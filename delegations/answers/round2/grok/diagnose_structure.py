"""Structure of off-diagonal pairs of W on raw GPT-2 heads.

Questions:
- Where does q come from (symmetric pairs vs skew pairs, top pairs vs bulk)?
- Are large pairs local in singular-value index?
- How much of err(1) sits in the largest symmetric pairs?
"""
import numpy as np
from safetensors.numpy import load_file

PATH = "/private/tmp/claude-501/-Users-andrew-maisi-questions-2026-11-20-odesky/8a345037-c99c-4fe5-98da-2190c1ebad66/scratchpad/dl_gpt2/model.safetensors"
N, n = 768, 64

def profile_from_L(L):
    S = (L + L.T) / 2
    Tm = (L - L.T) / 2
    ev = np.linalg.eigvalsh(S)
    lp = np.sort(ev[ev > 0])[::-1][:n]
    lm = np.sort(-ev[ev < 0])[::-1][:n]
    if len(lp) < n:
        lp = np.pad(lp, (0, n - len(lp)))
    if len(lm) < n:
        lm = np.pad(lm, (0, n - len(lm)))
    sv = np.linalg.svd(Tm, compute_uv=False)[: 2 * n : 2][:n]
    nL = np.sum(L * L)
    a = np.sum(Tm * Tm) / nL
    b = 2 * np.dot(lp, lm) / nL
    dif = lp - lm
    c = np.sum(np.maximum(dif, 0) ** 2) / nL
    d = np.sum(np.maximum(-dif, 0) ** 2) / nL
    e1 = np.linalg.norm(sv - np.sqrt(np.maximum(lp, 0) * np.maximum(lm, 0))) / (np.linalg.norm(sv) + 1e-30)
    return a, b, c, d, e1

def realize(sig, W):
    # L up to orthogonal congruence from (Sigma, W), in R^{2n}
    R2 = np.eye(n) - W.T @ W
    R2 = 0.5 * (R2 + R2.T)
    ev, E = np.linalg.eigh(R2)
    R = (E * np.sqrt(np.clip(ev, 0, None))) @ E.T
    V = np.vstack([W, R])
    U = np.vstack([np.eye(n), np.zeros((n, n))])
    return U @ (sig[:, None] * V.T)

def pack(sig, W):
    a, b, c, d, e1 = profile_from_L(realize(sig, W))
    return e1, a - b

wts = load_file(PATH)
iu = np.triu_indices(n, 1)
# band accumulators
bands = [1, 2, 3, 5, 10, 20, 63]
band_sq = {b: [] for b in bands}
band_prod = {b: [] for b in bands}

rows = []
# also collect |i-j| histogram of top 5% pairs, split by symmetry
hist_sym = np.zeros(n)
hist_skew = np.zeros(n)
hist_alltop = np.zeros(n)
deg_top = []

for l in range(12):
    Wa = wts[f"h.{l}.attn.c_attn.weight"].astype(np.float64)
    for h in range(12):
        Q = Wa[:, h * n : (h + 1) * n].T
        K = Wa[:, N + h * n : N + (h + 1) * n].T
        U, sig, Vt = np.linalg.svd(K.T @ Q, full_matrices=False)
        sig = sig[:n]
        W = U[:, :n].T @ Vt[:n].T
        # sign-fix so diagonal of W is positive? no, t_i can be negative. Leave SVD signs.
        t = np.diag(W).copy()
        x = W[iu]
        y = W.T[iu]
        prod = x * y
        mag = np.maximum(np.abs(x), np.abs(y))
        F = np.sum(sig ** 2)
        q = np.sum(sig[iu[0]] * sig[iu[1]] * prod) * 2 / F  # each unordered pair once, times 2? 
        # q = sum_{i≠j} σ_i σ_j E_ij E_ji / F. Each unordered pair {i,j} contributes
        # σ_i σ_j E_ij E_ji + σ_j σ_i E_ji E_ij = 2 σ_i σ_j x y.
        # Yes q = 2 * sum_{i<j} σ_i σ_j x y / F.
        m2 = np.sum(sig ** 2 * t ** 2) / F
        a, b, c, d, e1 = profile_from_L(K.T @ Q)
        # symmetry split of q
        sym_mask = np.abs(x + y) >= np.abs(x - y)  # |sum| >= |diff| means closer to symmetric
        q_sym = 2 * np.sum(sig[iu[0]][sym_mask] * sig[iu[1]][sym_mask] * prod[sym_mask]) / F
        q_skew = 2 * np.sum(sig[iu[0]][~sym_mask] * sig[iu[1]][~sym_mask] * prod[~sym_mask]) / F
        # top 5% by mag
        thr = np.quantile(mag, 0.95)
        top = mag >= thr
        q_top = 2 * np.sum(sig[iu[0]][top] * sig[iu[1]][top] * prod[top]) / F
        q_bulk = q - q_top
        sym_top = np.mean(np.abs(x[top] + y[top]) / (np.abs(x[top]) + np.abs(y[top]) + 1e-30))
        # locality of top pairs
        dij = np.abs(iu[0] - iu[1])
        hist_alltop[dij[top]] += 1
        symscore = np.abs(x + y) / (np.abs(x) + np.abs(y) + 1e-30)
        hist_sym[dij[top & (symscore > 0.7)]] += 1
        hist_skew[dij[top & (symscore < 0.3)]] += 1
        # degree of top graph
        deg = np.zeros(n)
        for i, j in zip(iu[0][top], iu[1][top]):
            deg[i] += 1
            deg[j] += 1
        deg_top.append(deg)
        # |t_i - t_j| for top symmetric vs random
        dt = np.abs(t[iu[0]] - t[iu[1]])
        dsig = np.abs(np.log(sig[iu[0]] + 1e-30) - np.log(sig[iu[1]] + 1e-30))
        # correlation of |prod| or mag with locality, already via hist
        # band energy
        for b in bands:
            msk = dij <= b
            band_sq[b].append(np.mean(x[msk] ** 2 + y[msk] ** 2) / 2)
            band_prod[b].append(np.mean(prod[msk]))
        # ablation: zero all but diagonal + top symmetric pairs, recompute err
        Ws = np.diag(t)
        for i, j, xs, ys, sc in zip(iu[0][top], iu[1][top], x[top], y[top], symscore[top]):
            if sc > 0.7:
                Ws[i, j] = xs
                Ws[j, i] = ys
        # project to contraction
        op = np.linalg.norm(Ws, 2)
        if op > 0.999:
            Uu, ss, Vv = np.linalg.svd(Ws, full_matrices=False)
            Ws = (Uu * np.minimum(ss, 0.999)) @ Vv
        e_keep, ab_keep = pack(sig, Ws)
        # zero only top symmetric
        Wz = W.copy()
        for i, j, sc in zip(iu[0][top], iu[1][top], symscore[top]):
            if sc > 0.7:
                Wz[i, j] = 0
                Wz[j, i] = 0
        op = np.linalg.norm(Wz, 2)
        if op > 0.999:
            Uu, ss, Vv = np.linalg.svd(Wz, full_matrices=False)
            Wz = (Uu * np.minimum(ss, 0.999)) @ Vv
        e_zero, ab_zero = pack(sig, Wz)
        # kurtosis
        off = np.concatenate([x, y])
        kurt = np.mean(off ** 4) / (np.mean(off ** 2) ** 2)
        offrms = np.sqrt(np.mean(off ** 2))
        # fraction of off Frobenius in top 5%
        mass_top = np.sum(x[top] ** 2 + y[top] ** 2) / np.sum(x ** 2 + y ** 2)
        # median |i-j| of top
        med_dij = np.median(dij[top])
        # nearest-neighbor fraction of top
        nn_frac = np.mean(dij[top] <= 3)
        rows.append(dict(
            layer=l, head=h, a=a, b=b, amb=a - b, err1=e1, q=q, m2=m2,
            q_sym=q_sym, q_skew=q_skew, q_top=q_top, q_bulk=q_bulk,
            sym_top=sym_top, kurt=kurt, offrms=offrms, mass_top=mass_top,
            med_dij=med_dij, nn_frac=nn_frac,
            e_keep=e_keep, e_zero=e_zero, ab_keep=ab_keep, ab_zero=ab_zero,
            dt_top=np.mean(dt[top]), dt_all=np.mean(dt),
            dsig_top=np.mean(dsig[top]), dsig_all=np.mean(dsig),
            mean_prod=np.mean(prod), mean_prod_top=np.mean(prod[top]),
        ))

R = rows
def col(k):
    return np.array([r[k] for r in R])

def summ(k):
    v = col(k)
    return f"{np.median(v):+.4f} [{np.percentile(v,10):+.4f}, {np.percentile(v,90):+.4f}]"

print("n heads", len(R), "n with a>b", int(np.sum(col("amb") > 0)))
for k in ["amb", "q", "q_sym", "q_skew", "q_top", "q_bulk", "err1", "e_keep", "e_zero",
          "sym_top", "kurt", "mass_top", "med_dij", "nn_frac", "dt_top", "dt_all",
          "dsig_top", "dsig_all", "mean_prod", "mean_prod_top", "offrms"]:
    print(f"{k:16s} {summ(k)}")

amb = col("amb")
print("corr(q, amb)", np.corrcoef(col("q"), amb)[0, 1])
print("corr(q_sym, amb)", np.corrcoef(col("q_sym"), amb)[0, 1])
print("corr(q_skew, amb)", np.corrcoef(col("q_skew"), amb)[0, 1])
print("corr(q_top, amb)", np.corrcoef(col("q_top"), amb)[0, 1])
print("corr(q_bulk, amb)", np.corrcoef(col("q_bulk"), amb)[0, 1])
print("corr(err, e_keep)", np.corrcoef(col("err1"), col("e_keep"))[0, 1])
print("corr(err, e_zero)", np.corrcoef(col("err1"), col("e_zero"))[0, 1])

# split a>b vs a<b
for name, msk in [("a>b", amb > 0), ("a<b", amb <= 0)]:
    print(f"\n== {name} n={msk.sum()} ==")
    for k in ["q", "q_sym", "q_skew", "q_top", "q_bulk", "sym_top", "nn_frac", "med_dij", "err1", "mass_top", "mean_prod_top"]:
        v = col(k)[msk]
        print(f"  {k:16s} {np.median(v):+.4f} [{np.percentile(v,10):+.4f}, {np.percentile(v,90):+.4f}]")

print("\n|i-j| hist of top 5% pairs (normalized)")
h = hist_alltop / hist_alltop.sum()
print("P(|i-j|<=1)", h[1])
print("P(|i-j|<=2)", h[1:3].sum())
print("P(|i-j|<=3)", h[1:4].sum())
print("P(|i-j|<=5)", h[1:6].sum())
print("P(|i-j|<=10)", h[1:11].sum())
# uniform null: number of pairs at distance d is (n-d), total pairs n(n-1)/2
null = np.array([n - d for d in range(n)], dtype=float)
null[0] = 0
null /= null.sum()
print("null P(<=1)", null[1], "<=3", null[1:4].sum(), "<=5", null[1:6].sum(), "<=10", null[1:11].sum())
print("sym top P(<=3)", (hist_sym[1:4].sum() / max(hist_sym.sum(), 1)))
print("skew top P(<=3)", (hist_skew[1:4].sum() / max(hist_skew.sum(), 1)))
print("counts sym-top", hist_sym.sum(), "skew-top", hist_skew.sum(), "all-top", hist_alltop.sum())

deg = np.concatenate(deg_top)
print("degree of top-5% graph: median", np.median(deg), "p90", np.percentile(deg, 90), "max", deg.max(),
      "frac isolated", np.mean(deg == 0), "frac deg>=3", np.mean(deg >= 3))

print("\nband mean square and mean product (median over heads)")
for b in bands:
    print(f"  |i-j|<={b:2d}  meansq {np.median(band_sq[b]):.6f}  meanprod {np.median(band_prod[b]):+.6f}")
