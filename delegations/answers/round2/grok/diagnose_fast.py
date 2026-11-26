"""Fast structure diagnostic using the n x n overlap W."""
import os
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["VECLIB_MAXIMUM_THREADS"] = "1"
import numpy as np
from safetensors.numpy import load_file

PATH = "/private/tmp/claude-501/-Users-andrew-maisi-questions-2026-11-20-odesky/8a345037-c99c-4fe5-98da-2190c1ebad66/scratchpad/dl_gpt2/model.safetensors"
N, n = 768, 64

def extract_sW(Q, K):
    # Q, K are n x N
    uq, rq = np.linalg.qr(Q.T)
    uk, rk = np.linalg.qr(K.T)
    x, s, yt = np.linalg.svd(rk @ rq.T, full_matrices=False)
    W = (uk @ x).T @ (uq @ yt.T)
    return s, W

def profile(s, W):
    e, B = np.linalg.eigh(np.eye(n) - W.T @ W)
    R = (B * np.sqrt(np.maximum(e, 0))) @ B.T
    L = np.zeros((2 * n, 2 * n))
    L[:n, :n] = s[:, None] * W.T
    L[:n, n:] = s[:, None] * R
    ev = np.linalg.eigvalsh((L + L.T) / 2)
    lp = ev[-n:][::-1]
    lm = -ev[:n]
    # singular values of T, multiplicity two, take the positive half via |eig of iT|
    sv = np.linalg.eigvalsh(1j * (L - L.T) / 2)
    sv = np.sort(np.abs(sv))[::-1][:n]
    norm = float(s @ s)
    a = np.sum((L - L.T) ** 2) / 4 / norm
    b = 2 * float(lp @ lm) / norm
    diff = lp - lm
    c = float(np.maximum(diff, 0) @ np.maximum(diff, 0)) / norm
    d = float(np.minimum(diff, 0) @ np.minimum(diff, 0)) / norm
    err1 = np.linalg.norm(sv - np.sqrt(np.maximum(lp * lm, 0))) / (np.linalg.norm(sv) + 1e-30)
    return a, b, c, d, err1

wts = load_file(PATH)
iu = np.triu_indices(n, 1)
all_s = np.zeros((144, n))
all_W = np.zeros((144, n, n))
idx = 0
# magnitude-decile symmetry and product
dec_sym = np.zeros(10)
dec_prod = np.zeros(10)
dec_cnt = np.zeros(10)
rows = []
for l in range(12):
    A = wts[f"h.{l}.attn.c_attn.weight"].astype(np.float64)
    for h in range(12):
        Q = A[:, 64 * h:64 * (h + 1)].T
        K = A[:, N + 64 * h:N + 64 * (h + 1)].T
        s, W = extract_sW(Q, K)
        all_s[idx] = s
        all_W[idx] = W
        idx += 1
        a, b, c, d, err1 = profile(s, W)
        t = np.diag(W).copy()
        x = W[iu].copy()
        y = W.T[iu].copy()
        prod = x * y
        mag = np.maximum(np.abs(x), np.abs(y))
        F = float(s @ s)
        q = 2 * float(np.sum(s[iu[0]] * s[iu[1]] * prod)) / F
        m2 = float(np.sum(s ** 2 * t ** 2)) / F
        off = np.concatenate([x, y])
        kurt = float(np.mean(off ** 4) / np.mean(off ** 2) ** 2)
        sym = np.abs(x + y) / (np.abs(x) + np.abs(y) + 1e-30)
        # deciles of mag
        order = np.argsort(mag)
        bins = np.array_split(order, 10)
        dec_s = []
        dec_p = []
        for bi, bidx in enumerate(bins):
            dec_s.append(float(np.mean(sym[bidx])))
            dec_p.append(float(np.mean(prod[bidx])))
            dec_sym[bi] += dec_s[-1]
            dec_prod[bi] += dec_p[-1]
            dec_cnt[bi] += 1
        top = mag >= np.quantile(mag, 0.95)
        # weighted symmetry: share of off Frobenius that is symmetric
        Spart = 0.5 * (W + W.T)
        Apart = 0.5 * (W - W.T)
        symfrac = float(np.sum(Spart ** 2) / np.sum(W ** 2))
        # q from pairs with sym>0.7 vs <0.3
        q_hi = 2 * float(np.sum(s[iu[0]][sym > 0.7] * s[iu[1]][sym > 0.7] * prod[sym > 0.7])) / F
        q_lo = 2 * float(np.sum(s[iu[0]][sym < 0.3] * s[iu[1]][sym < 0.3] * prod[sym < 0.3])) / F
        rows.append(dict(
            layer=l, head=h, a=a, b=b, amb=a - b, cd=c - d, mincd=min(c, d),
            err1=err1, q=q, m2=m2, kurt=kurt,
            sym_top=float(np.mean(sym[top])),
            symfrac=symfrac,
            diag=float(np.sum(t ** 2) / np.sum(W ** 2)),
            offrms=float(np.sqrt(np.mean(off ** 2))),
            PR=float((s @ s) ** 2 / np.sum(s ** 4)),
            q_hi=q_hi, q_lo=q_lo,
            dec_sym_hi=dec_s[-1], dec_sym_lo=dec_s[0],
            dec_prod_hi=dec_p[-1], dec_prod_lo=dec_p[0],
            c=c, d=d,
        ))
    print("layer", l, flush=True)

def col(k):
    return np.array([r[k] for r in rows])

def summ(v):
    return f"{np.median(v):+.4f} [{np.percentile(v,10):+.4f}, {np.percentile(v,90):+.4f}]"

print("n", len(rows), "a>b", int(np.sum(col("amb") > 0)))
for k in ["amb", "q", "err1", "kurt", "sym_top", "symfrac", "diag", "offrms", "PR", "cd", "mincd", "q_hi", "q_lo", "m2"]:
    print(f"{k:12s} {summ(col(k))}")
print("corr q,amb", np.corrcoef(col("q"), col("amb"))[0, 1])
print("corr q_hi,amb", np.corrcoef(col("q_hi"), col("amb"))[0, 1])
print("corr q_lo,amb", np.corrcoef(col("q_lo"), col("amb"))[0, 1])
print("identity a-b vs c+d-m2-q", np.max(np.abs(col("amb") - (col("c") + col("d") - col("m2") - col("q")))))
print("\nsymmetry by magnitude decile (0=smallest):")
for i in range(10):
    print(f"  dec {i}: sym {dec_sym[i]/dec_cnt[i]:.3f}  meanprod {dec_prod[i]/dec_cnt[i]:+.6f}")

amb = col("amb")
for name, msk in [("a>b", amb > 0), ("a<b", amb <= 0)]:
    print(f"\n== {name} n={int(msk.sum())} ==")
    for k in ["q", "q_hi", "q_lo", "sym_top", "kurt", "err1", "diag", "m2", "offrms"]:
        v = col(k)[msk]
        print(f"  {k:12s} {summ(v)}")

# save per-head arrays for the fitter
np.savez(
    "gpt2_raw_stats.npz",
    s=all_s, W=all_W,
    **{k: col(k) for k in rows[0] if k not in ("layer", "head")},
    layer=col("layer"), head=col("head"),
)
print("saved gpt2_raw_stats.npz")
