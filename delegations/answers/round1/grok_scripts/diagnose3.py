"""Test additive and effective-dimension ensembles head by head."""
import numpy as np
from safetensors.numpy import load_file

PATH = "ensemble_brief/gpt2_model.safetensors"
wts = load_file(PATH)
N, n = 768, 64
rng = np.random.default_rng(2)

def pr_of(s):
    s2 = np.asarray(s, float) ** 2
    s2 = s2[s2 > 0]
    return float((s2.sum() ** 2) / np.sum(s2 ** 2))

def project_contraction(W, eps=1.0):
    U, s, Vt = np.linalg.svd(W, full_matrices=False)
    s = np.minimum(s, eps)
    return U * s @ Vt

def from_SW(sig, W):
    R2 = np.eye(n) - W.T @ W
    ev, E = np.linalg.eigh(0.5 * (R2 + R2.T))
    ev = np.clip(ev, 0, None)
    R = (E * np.sqrt(ev)) @ E.T
    U = np.concatenate([np.eye(n), np.zeros((n, n))], 0)
    V = np.concatenate([W, R], 0)
    return U @ np.diag(sig) @ V.T

def profile_of(L):
    S = 0.5 * (L + L.T)
    Tm = 0.5 * (L - L.T)
    ev = np.linalg.eigvalsh(S)
    lp = np.sort(ev[ev > 0])[::-1]
    lm = np.sort(-ev[ev < 0])[::-1]
    if len(lp) < n:
        lp = np.pad(lp, (0, n - len(lp)))
    else:
        lp = lp[:n]
    if len(lm) < n:
        lm = np.pad(lm, (0, n - len(lm)))
    else:
        lm = lm[:n]
    sv = np.linalg.svd(Tm, compute_uv=False)[: 2 * n : 2][:n]
    nL = np.sum(L * L) + 1e-30
    a = float(np.sum(Tm * Tm) / nL)
    b = float(2 * np.dot(lp, lm) / nL)
    dif = lp - lm
    c = float(np.sum(np.maximum(dif, 0) ** 2) / nL)
    d = float(np.sum(np.maximum(-dif, 0) ** 2) / nL)
    e1 = float(np.linalg.norm(sv - np.sqrt(np.maximum(lp, 0) * np.maximum(lm, 0))) / (np.linalg.norm(sv) + 1e-15))
    return a, b, c, d, e1

def wstats(W, sig):
    t = np.diag(W).real
    ww = sig ** 2
    w = ww / ww.sum()
    off = W - np.diag(np.diag(W))
    offrms = float(np.sqrt(np.sum(off ** 2) / (n * (n - 1))))
    diagfrac = float(np.sum(t ** 2) / np.sum(W ** 2))
    tbar = float(w @ t)
    tstd = float(np.sqrt(max(w @ (t - tbar) ** 2, 0.0)))
    return dict(offrms=offrms, diagfrac=diagfrac, tbar=tbar, tstd=tstd, Wf2=float(np.sum(W ** 2)),
                op=float(np.linalg.norm(W, 2)))

def fullstats(sig, W):
    L = from_SW(sig, W)
    a, b, c, d, e1 = profile_of(L)
    st = wstats(W, sig)
    st.update(a=a, b=b, c=c, d=d, err1=e1, a_minus_b=a - b, c_minus_d=c - d, PR=pr_of(sig))
    return st

# load heads via compact SVD route
heads = []
for l in range(12):
    Wa = wts[f"h.{l}.attn.c_attn.weight"]
    for h in range(12):
        Q = Wa[:, h * n:(h + 1) * n].T.astype(np.float64)
        K = Wa[:, N + h * n:N + (h + 1) * n].T.astype(np.float64)
        Uq, sq, Vqh = np.linalg.svd(Q, full_matrices=False)
        Uk, sk, Vkh = np.linalg.svd(K, full_matrices=False)
        Ho = Uk.T @ Uq
        C = Vkh @ Vqh.T
        M = (sk[:, None] * Ho) * sq[None, :]
        P, sl, Sh = np.linalg.svd(M, full_matrices=False)
        W = P.T @ C @ Sh.T
        # symmetrize numerical noise
        st = fullstats(sl, W)
        # residual off-diagonal spectrum
        off = W - np.diag(np.diag(W))
        osv = np.linalg.svd(off, compute_uv=False)
        ent = off[~np.eye(n, dtype=bool)]
        st.update(layer=l, head=h, sl=sl, t=np.diag(W).real.copy(), W=W,
                  off_pr=pr_of(osv), off_kurt=float(((ent - ent.mean()) ** 4).mean() / (ent.var() ** 2 + 1e-30)),
                  off_top=float(osv[0]), off_med=float(np.median(osv)))
        heads.append(st)
        if (l, h) == (0, 0):
            # save one off singular spectrum normalized
            np.save("/tmp/off_sv_L0H0.npy", osv)

def summarize(name, v):
    v = np.asarray(v, float)
    qs = np.percentile(v, [10, 50, 90])
    print(f"{name:20s} mean={v.mean():+.4f}  p10={qs[0]:+.4f}  med={qs[1]:+.4f}  p90={qs[2]:+.4f}")

print("=== off-diagonal residual of W ===")
for k in ["off_pr", "off_kurt", "off_top", "off_med", "offrms", "op"]:
    summarize(k, [h[k] for h in heads])

# quarter-circle prediction at sigma=median offrms
sig_e = np.median([h["offrms"] for h in heads])
print(f"median offrms={sig_e:.4f}  quarter-circle edge={2*sig_e*np.sqrt(n):.3f}  N_eff={1/sig_e**2:.1f}")

# ---------- per-head additive reconstructions ----------
keys = ["err1", "a_minus_b", "c_minus_d", "diagfrac", "offrms", "tbar", "tstd", "Wf2"]

def eval_model(maker, trials=3):
    """maker(head, rng) -> W model. Returns list of dicts of absolute errors and signed biases, per head averaged."""
    errs = {k: [] for k in keys}
    for h in heads:
        acc = {k: [] for k in keys}
        for _ in range(trials):
            Wm = maker(h, rng)
            # numerical guard
            if np.linalg.norm(Wm, 2) > 1.001:
                Wm = project_contraction(Wm, 1.0)
            st = fullstats(h["sl"], Wm)
            for k in keys:
                acc[k].append(st[k])
        for k in keys:
            pred = np.mean(acc[k])
            errs[k].append(pred - h[k])
    return {k: np.array(v) for k, v in errs.items()}

def report(name, errs):
    print(f"\n== {name}: predicted - measured ==")
    for k in keys:
        v = errs[k]
        print(f"  {k:12s} bias={v.mean():+.4f}  mae={np.mean(np.abs(v)):.4f}  med|e|={np.median(np.abs(v)):.4f}")

# Model A: diag(t) + sigma Z, sigma = global
def make_global(sigma):
    def maker(h, rng):
        Z = rng.standard_normal((n, n)) * sigma
        np.fill_diagonal(Z, 0.0)
        return np.diag(h["t"]) + Z
    return maker

print("\n#### oracle diagonal + off-diagonal Ginibre (uses measured t and Sigma) ####")
for sigma, name in [(1 / np.sqrt(N), "sigma=1/sqrt(N)"),
                    (sig_e, "sigma=median offrms"),
                    (0.053, "sigma=0.053")]:
    report(name, eval_model(make_global(sigma), trials=2))

# Model B: sigma chosen per head so E[offrms]=measured offrms (oracle noise level)
def maker_matched(h, rng):
    Z = rng.standard_normal((n, n)) * h["offrms"]
    np.fill_diagonal(Z, 0.0)
    return np.diag(h["t"]) + Z

report("sigma = head offrms", eval_model(maker_matched, trials=2))

# Model C: pure diagonal
report("pure diag", eval_model(lambda h, rng: np.diag(np.clip(h["t"], -0.999, 0.999)), trials=1))

# Model D: full resample of t ~ N(mu, s^2) with mu, s fit per head (unweighted), sigma global = sig_e
# AND use measured Sigma. This is the 2-param ensemble.
def maker_gauss_t(h, rng):
    mu, s = h["t"].mean(), h["t"].std()
    t = np.clip(rng.normal(mu, s, n), -0.999, 0.999)
    Z = rng.standard_normal((n, n)) * sig_e
    np.fill_diagonal(Z, 0.0)
    return np.diag(t) + Z

report("t~N(mu,s) per head, sigma global", eval_model(maker_gauss_t, trials=3))

# Model E: t from a Laplace distribution (heavier tails), same mu, same std
def maker_lap(h, rng):
    mu, s = h["t"].mean(), h["t"].std()
    # Laplace scale b with variance 2 b^2 = s^2
    b = s / np.sqrt(2)
    t = np.clip(mu + rng.laplace(0, b, n), -0.999, 0.999)
    Z = rng.standard_normal((n, n)) * sig_e
    np.fill_diagonal(Z, 0.0)
    return np.diag(t) + Z

report("t~Laplace(mu,s), sigma global", eval_model(maker_lap, trials=3))

# Model F: mixture — with prob p, t=mu_big, else small noise. Fit two parameters to mean and std.
# Skip; instead student-t with nu=4 to match kurtosis ~4? 
# excess kurtosis of t is about 1 (kurt 4). Student-t nu=5? We'll do a two-point? 
# Gaussian scale mixture: t = mu + s * g * sqrt(v) with v~something.

print("\n#### spectrum of off-diagonal vs quarter circle, one median head and aggregate ####")
# Compare sorted singular values of off-diagonal, normalized by offrms*sqrt(n), to quarter circle quantiles
offs = []
for h in heads:
    off = h["W"] - np.diag(np.diag(h["W"]))
    osv = np.linalg.svd(off, compute_uv=False)
    offs.append(osv / (h["offrms"] * np.sqrt(n)))
A = np.stack(offs, 0)
med = np.median(A, 0)
# quarter-circle quantiles: density (1/pi) sqrt(4-x^2) on [0,2], but that's the LIMIT of singular values
# of a matrix with entry variance 1/n, whose typical SV is order 1, and we divided by offrms*sqrt(n) = (std)*sqrt(n)
# which is exactly the scaling that puts bulk edge at 2. Good.
def qc_quantile(ps):
    # numerical inversion of CDF
    xs = np.linspace(0, 2, 2000)
    # integrand
    dens = np.sqrt(np.maximum(4 - xs ** 2, 0)) / np.pi
    cdf = np.cumsum(dens) * (xs[1] - xs[0])
    cdf /= cdf[-1]
    return np.interp(ps, cdf, xs)

ps = (np.arange(n) + 0.5) / n
# med is sorted descending; quarter circle quantiles descending
qc = qc_quantile(1 - ps)
print("idx  model_med  quartercircle")
for i in [0, 1, 2, 5, 10, 20, 31, 40, 50, 63]:
    print(f"{i:4d}  {med[i]:.3f}      {qc[i]:.3f}")

# effective dim of weight row-covariance
print("\n#### effective dimension of Q,K rows ####")
cov = np.zeros((N, N))
for l in range(12):
    Wa = wts[f"h.{l}.attn.c_attn.weight"]  # N x 2304, columns are input directions? 
    # weight is (out, in) in HF gpt2? safetensors gpt2 Conv1D is (in, out) = (768, 2304)
    # We stored Q = Wa[:, h*n:(h+1)*n].T so Wa rows are residual coordinates.
    # Row-covariance of Q and K: each row of Q is length N? Q is n x N, rows live in R^N.
    for h in range(12):
        Q = Wa[:, h * n:(h + 1) * n].T.astype(np.float64)
        K = Wa[:, N + h * n:N + (h + 1) * n].T.astype(np.float64)
        cov += Q.T @ Q + K.T @ K
ev = np.linalg.eigvalsh(cov)
ev = np.sort(ev)[::-1]
ev = np.clip(ev, 0, None)
print("PR of Q/K row-covariance", pr_of(np.sqrt(ev)), "top10 share", ev[:10].sum() / ev.sum())
print("eigenvalue quantiles", [f"{ev[i]/ev[0]:.3f}" for i in [0, 10, 50, 100, 200, 400, 600, 767]])
