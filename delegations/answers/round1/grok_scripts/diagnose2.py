"""Deeper per-head tests and candidate ensemble simulations."""
import numpy as np
from safetensors.numpy import load_file
from scipy.optimize import linear_sum_assignment

PATH = "ensemble_brief/gpt2_model.safetensors"
wts = load_file(PATH)
N, n = 768, 64
rng = np.random.default_rng(1)

def pr(s):
    s2 = np.asarray(s, float) ** 2
    return float((s2.sum() ** 2) / np.sum(s2 ** 2))

def profile_and_W(Q, K):
    Uq, sq, Vqh = np.linalg.svd(Q, full_matrices=False)
    Uk, sk, Vkh = np.linalg.svd(K, full_matrices=False)
    Ho = Uk.T @ Uq
    C = Vkh @ Vqh.T
    M = (sk[:, None] * Ho) * sq[None, :]
    P, sl, Sh = np.linalg.svd(M, full_matrices=True)
    W = P.T @ C @ Sh.T
    # profile from L without forming L: use from_SW geometry on the nonzero part
    # Build L's action via the n-frame. For eigenvalues of S we need the N x N matrix
    # only through its restriction to span(U_left, U_right). Use the 2n representation.
    U = Vkh.T @ P          # N x n left
    V = Vqh.T @ Sh.T       # N x n right
    # Orthonormalize the combined 2n frame and express L there. Cheaper: form L on R^N
    # is 768^2 ~ fine once, but for many sims use the CS block.
    # L = U @ diag(sl) @ V.T
    # Represent in an orthonormal basis of span(columns of U and V).
    # Stack and QR.
    Z = np.concatenate([U, V], axis=1)  # N x 2n
    Qr, Rr = np.linalg.qr(Z, mode="reduced")  # R is 2n x 2n, L coords: 
    # U = Qr @ Rr[:, :n], V = Qr @ Rr[:, n:]
    Ru, Rv = Rr[:, :n], Rr[:, n:]
    Lsmall = Ru @ np.diag(sl) @ Rv.T  # 2n x 2n, same nonzero spectrum / profile
    return sq, sk, sl, W, Ho, C, Lsmall

def stats_from(sl, W, Lsmall):
    n = len(sl)
    t = np.diag(W).real
    ww = sl ** 2
    w = ww / ww.sum()
    off = W - np.diag(t)
    offrms = float(np.sqrt(np.sum(off ** 2) / (n * n - n)))
    diagfrac = float(np.sum(t ** 2) / np.sum(W ** 2))
    tbar = float(w @ t)
    tstd = float(np.sqrt(max(w @ (t - tbar) ** 2, 0)))
    S = 0.5 * (Lsmall + Lsmall.T)
    T = 0.5 * (Lsmall - Lsmall.T)
    ev = np.linalg.eigvalsh(S)
    lp = np.sort(ev[ev > 0])[::-1][:n]
    lm = np.sort(-ev[ev < 0])[::-1][:n]
    # pad if needed
    if len(lp) < n:
        lp = np.pad(lp, (0, n - len(lp)))
    if len(lm) < n:
        lm = np.pad(lm, (0, n - len(lm)))
    sv = np.linalg.svd(T, compute_uv=False)
    # singular values of antisymmetric: take the n independent ones (even multiplicity)
    sv = sv[: 2 * n : 2][:n]
    nL = np.sum(Lsmall * Lsmall)
    a = float(np.sum(T * T) / nL)
    b = float(2 * lp @ lm / nL)
    dif = lp - lm
    c = float(np.sum(np.maximum(dif, 0) ** 2) / nL)
    d = float(np.sum(np.maximum(-dif, 0) ** 2) / nL)
    e1 = float(np.linalg.norm(sv - np.sqrt(np.maximum(lp, 0) * np.maximum(lm, 0))) / (np.linalg.norm(sv) + 1e-15))
    coss = np.linalg.svd(W, compute_uv=False)
    return dict(a=a, b=b, c=c, d=d, err1=e1, a_minus_b=a - b, c_minus_d=c - d,
                tbar=tbar, tstd=tstd, offrms=offrms, diagfrac=diagfrac, PR=pr(sl),
                Wf2=float(np.sum(W * W)), cos_top=float(coss[0]), cos_med=float(np.median(coss)),
                symfrac=float(np.sum(((W + W.T) / 2) ** 2) / np.sum(W ** 2)))

# ---------- load all heads, Ho alignment, per-head residuals ----------
heads = []
for l in range(12):
    Wa = wts[f"h.{l}.attn.c_attn.weight"]
    for h in range(12):
        Q = Wa[:, h * n:(h + 1) * n].T.astype(np.float64)
        K = Wa[:, N + h * n:N + (h + 1) * n].T.astype(np.float64)
        sq, sk, sl, W, Ho, C, Lsmall = profile_and_W(Q, K)
        st = stats_from(sl, W, Lsmall)
        # Ho alignment: sum of squared diagonal (sign-invariant) and best assignment
        ho_diag = float(np.sum(np.diag(Ho) ** 2) / n)
        ri, ci = linear_sum_assignment(-np.abs(Ho))
        ho_assign = float(np.sum(np.abs(Ho[ri, ci])) / n)  # 1 = signed permutation
        Cdiag = float(np.sum(np.diag(C) ** 2) / np.sum(C ** 2))
        t = np.diag(W).real.copy()
        st.update(layer=l, head=h, ho_diag=ho_diag, ho_assign=ho_assign, Cdiag=Cdiag,
                  sum_t2=float(np.sum(t ** 2)), tstd_u=float(t.std()), tmean=float(t.mean()),
                  kurt=float(((t - t.mean()) ** 4).mean() / (t.std() ** 4 + 1e-12)))
        st["sq"] = sq
        st["sk"] = sk
        st["sl"] = sl
        st["t"] = t
        heads.append(st)

def col(k):
    return np.array([h[k] for h in heads])

def summarize(name, v):
    v = np.asarray(v, float)
    qs = np.percentile(v, [10, 50, 90])
    print(f"{name:22s} mean={v.mean():+.4f}  p10={qs[0]:+.4f}  med={qs[1]:+.4f}  p90={qs[2]:+.4f}")

print("=== alignment of head-space singular bases Ho = Uk.T Uq ===")
for k in ["ho_diag", "ho_assign", "Cdiag", "sum_t2", "Wf2", "err1", "a_minus_b", "c_minus_d", "PR", "diagfrac", "offrms"]:
    summarize(k, col(k))

print("\nHaar reference: ho_diag ~", 1 / n, " ho_assign for one Haar draw:")
Hrand = np.linalg.qr(rng.standard_normal((n, n)))[0]
ri, ci = linear_sum_assignment(-np.abs(Hrand))
print("  one Haar ho_diag", np.sum(np.diag(Hrand) ** 2) / n, "assign", np.sum(np.abs(Hrand[ri, ci])) / n)

print("\n=== correlations ===")
pairs = [("ho_diag", "diagfrac"), ("ho_assign", "diagfrac"), ("ho_diag", "PR"),
         ("diagfrac", "PR"), ("Cdiag", "diagfrac"), ("sum_t2", "Wf2"),
         ("offrms", "ho_diag"), ("err1", "tstd"), ("a_minus_b", "tstd"),
         ("diagfrac", "sl_cv")]
# sl cv
slcv = np.array([h["sl"].std() / h["sl"].mean() for h in heads])
data = {k: col(k) for k in ["ho_diag", "ho_assign", "diagfrac", "PR", "Cdiag", "sum_t2", "Wf2", "offrms", "err1", "a_minus_b", "tstd"]}
data["sl_cv"] = slcv
data["tstd"] = col("tstd")
for a, b in pairs:
    print(f"  corr({a},{b})={np.corrcoef(data[a], data[b])[0,1]:+.3f}")

# excess off-diagonal variance over 1/N
ex = []
for h in heads:
    off_mass = h["Wf2"] - h["sum_t2"]
    base = n * (n - 1) / N
    ex.append(off_mass / base)
print("\noff-diagonal mass / (n(n-1)/N):")
summarize("off_excess", ex)

# ---------- simulations ----------
def row_model(alpha, t, rng):
    Gq = rng.standard_normal((n, N))
    Gg = rng.standard_normal((n, N))
    qn = np.linalg.norm(Gq, axis=1, keepdims=True)
    gn = np.linalg.norm(Gg, axis=1, keepdims=True)
    qhat = Gq / qn
    ghat = Gg / gn
    s = np.sqrt(np.clip(1 - t ** 2, 0, None))
    Q = qhat * alpha[:, None]
    K = (t[:, None] * qhat + s[:, None] * ghat) * alpha[:, None]
    return Q, K

def collect(name, fn, trials=8):
    recs = [stats_from(*profile_and_W(*fn())[2:5], ) for _ in range(trials)]
    # fix call properly
    return recs

def run_model(fn, trials=6):
    out = []
    for _ in range(trials):
        Q, K = fn()
        sq, sk, sl, W, Ho, C, Lsmall = profile_and_W(Q, K)
        out.append(stats_from(sl, W, Lsmall))
    return out

def show(name, recs):
    print(f"\n-- {name} --")
    for k in ["err1", "a_minus_b", "c_minus_d", "tbar", "tstd", "offrms", "diagfrac", "PR", "Wf2", "cos_top", "cos_med", "symfrac"]:
        summarize(k, [r[k] for r in recs])

# A. equal scale, t_i ~ N(0, 0.15^2) truncated
def clip_t(z):
    return np.clip(z, -0.98, 0.98)

print("\n\n######## SIMULATIONS ########")
show("row equal-alpha t~N(0,0.15)", run_model(lambda: row_model(np.ones(n), clip_t(rng.normal(0, 0.15, n)), rng)))
show("row equal-alpha t~N(0,0.40)", run_model(lambda: row_model(np.ones(n), clip_t(rng.normal(0, 0.40, n)), rng)))
show("row equal-alpha t~N(0.8,0.1)", run_model(lambda: row_model(np.ones(n), clip_t(rng.normal(0.8, 0.10, n)), rng)))

# power-law scales
def power_alpha(beta):
    idx = np.arange(1, n + 1)
    a = idx ** (-beta)
    a = a / np.sqrt(np.mean(a ** 2))
    return a

show("row power beta=0.3 t~N(0,0.2)", run_model(lambda: row_model(power_alpha(0.3), clip_t(rng.normal(0, 0.2, n)), rng)))
show("row power beta=0.6 t~N(0,0.2)", run_model(lambda: row_model(power_alpha(0.6), clip_t(rng.normal(0, 0.2, n)), rng)))

# oracle: regenerate 8 diverse heads from their own (sqrt(sl), t)
print("\n\n######## ORACLE ROW REGENERATION (input alpha=sqrt(sl), t=measured) ########")
# pick heads spanning diagfrac
order = np.argsort(col("diagfrac"))
pick = [heads[i] for i in [order[0], order[len(order)//5], order[len(order)//2], order[3*len(order)//4], order[-1]]]
print(f"{'head':8s} {'':8s} {'err1':7s} {'a-b':8s} {'c-d':8s} {'tbar':8s} {'tstd':7s} {'off':7s} {'diag':7s} {'PR':7s} {'Wf2':7s}")
for h in pick:
    tag = f"L{h['layer']}H{h['head']}"
    def fmt(r):
        return f"{r['err1']:.3f}  {r['a_minus_b']:+.3f}  {r['c_minus_d']:+.3f}  {r['tbar']:+.3f}  {r['tstd']:.3f}  {r['offrms']:.3f}  {r['diagfrac']:.3f}  {r['PR']:.1f}  {r['Wf2']:.1f}"
    print(f"{tag:8s} {'meas':8s} {fmt(h)}")
    alpha = np.sqrt(np.maximum(h["sl"], 1e-8))
    recs = run_model(lambda: row_model(alpha, np.clip(h["t"], -0.98, 0.98), rng), trials=4)
    avg = {k: np.mean([r[k] for r in recs]) for k in recs[0]}
    print(f"{'':8s} {'regen':8s} {fmt(avg)}")

# ---------- additive W model realized by from_SW, compared on profile only ----------
print("\n\n######## ADDITIVE W = diag(t)+sigma Z , Sigma from trained head, profile via 2n embedding ########")

def from_SW(sig, W):
    # returns Lsmall 2n x 2n with this Sigma, W. Requires ||W||_op <= 1.
    R2 = np.eye(n) - W.T @ W
    # numerical PSD projection
    ev, E = np.linalg.eigh(0.5 * (R2 + R2.T))
    ev = np.clip(ev, 0, None)
    R = E * np.sqrt(ev) @ E.T
    U = np.concatenate([np.eye(n), np.zeros((n, n))], 0)
    V = np.concatenate([W, R], 0)
    return U @ np.diag(sig) @ V.T

def stats_L(Lsmall, sig_for_pr=None):
    # reuse stats_from by fabricating W from SVD of Lsmall? Lsmall may be 2n.
    # Compute profile directly and also W from SVD of Lsmall.
    U, s, Vt = np.linalg.svd(Lsmall, full_matrices=False)
    # rank n
    U, s, V = U[:, :n], s[:n], Vt[:n].T
    W = U.T @ V
    return stats_from(s, W, Lsmall)

# For a median-ish head and a high-diag head, take their (sl, t) but replace W by diag(t)+noise
# and also pure diag, and compare profile stats to measured.
for h in pick:
    tag = f"L{h['layer']}H{h['head']}"
    sig = h["sl"]
    t = h["t"]
    def fmt(r):
        return f"err1={r['err1']:.3f} a-b={r['a_minus_b']:+.3f} c-d={r['c_minus_d']:+.3f} diag={r['diagfrac']:.3f} off={r['offrms']:.3f} PR={r['PR']:.1f}"
    print(f"\n{tag} measured {fmt(h)}")
    # pure diagonal W
    W = np.diag(np.clip(t, -0.98, 0.98))
    r = stats_L(from_SW(sig, W))
    print(f"  pure diag(t)     {fmt(r)}")
    # additive noise at 1/sqrt(N), rescale to contraction
    acc = []
    for _ in range(4):
        Z = rng.standard_normal((n, n)) / np.sqrt(N)
        W = np.diag(np.clip(t, -0.98, 0.98)) + Z
        op = np.linalg.norm(W, 2)
        if op > 0.98:
            W *= 0.98 / op
        acc.append(stats_L(from_SW(sig, W)))
    avg = {k: np.mean([r[k] for r in acc]) for k in acc[0]}
    print(f"  diag+N(0,1/N)    {fmt(avg)}")
