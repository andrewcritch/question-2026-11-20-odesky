"""Diagnostics of GPT-2 Q/K bilinear forms: invariants of (Sigma, W) and the Q,K factorization."""
import numpy as np
from safetensors.numpy import load_file

PATH = "ensemble_brief/gpt2_model.safetensors"
wts = load_file(PATH)
N, n, H = 768, 64, 12
rng = np.random.default_rng(0)

def summarize(name, v):
    v = np.asarray(v, float)
    qs = np.percentile(v, [10, 50, 90])
    print(f"{name:28s} mean={v.mean():+.4f}  p10={qs[0]:+.4f}  med={qs[1]:+.4f}  p90={qs[2]:+.4f}")

def pr(s):
    s2 = np.asarray(s, float) ** 2
    return float((s2.sum() ** 2) / np.sum(s2 ** 2))

rows = []
# store spectra for shape comparison
sig_L = []
sig_Q = []
sig_K = []
cos2 = []
t_all = []
# a few full W's and t-vectors
examples = {}

for l in range(12):
    Wa = wts[f"h.{l}.attn.c_attn.weight"]
    for h in range(12):
        Q = Wa[:, h * n:(h + 1) * n].T.astype(np.float64)  # n x N
        K = Wa[:, N + h * n:N + (h + 1) * n].T.astype(np.float64)
        Uq, sq, Vqh = np.linalg.svd(Q, full_matrices=False)
        Uk, sk, Vkh = np.linalg.svd(K, full_matrices=False)
        # head-space overlap of left singular vectors (output bases)
        Ho = Uk.T @ Uq  # n x n
        # row-space overlap
        C = Vkh @ Vqh.T  # n x n
        M = (sk[:, None] * Ho) * sq[None, :]  # diag(sk) @ Ho @ diag(sq)
        P, sl, Sh = np.linalg.svd(M, full_matrices=False)
        W = P.T @ C @ Sh.T
        t = np.diag(W)
        wts2 = sl ** 2
        w = wts2 / wts2.sum()
        off = W - np.diag(t)
        offrms = np.sqrt(np.sum(off ** 2) / (n * n - n))
        diagfrac = np.sum(t ** 2) / np.sum(W ** 2)
        tbar = float(w @ t)
        tstd = float(np.sqrt(w @ (t - tbar) ** 2))
        # principal cosines
        coss = np.linalg.svd(C, compute_uv=False)
        # symmetry of W
        Ws = 0.5 * (W + W.T)
        Wa_ = 0.5 * (W - W.T)
        # head-overlap diagonal dominance in its SVD basis is trivial;
        # Frobenius of Ho and its diagonal in the given basis (gauge)
        # Better: singular values of Ho already are canonical.
        ho_sv = np.linalg.svd(Ho, compute_uv=False)
        # How aligned is L's singular basis with the principal basis of C?
        # In principal basis C = F diag(coss) G.T, and W = P.T F diag G.T S
        # diagonal share we have. Also ||W||_F^2 = ||C||_F^2.
        # correlation |t| vs sigma
        corr_t_sig = np.corrcoef(t, sl)[0, 1]
        corr_abs_t_sig = np.corrcoef(np.abs(t), sl)[0, 1]
        corr_t_idx = np.corrcoef(t, np.arange(n))[0, 1]
        # unweighted moments of t
        rec = dict(
            layer=l, head=h,
            prL=pr(sl), prQ=pr(sq), prK=pr(sk),
            offrms=offrms, diagfrac=diagfrac,
            tbar=tbar, tstd=tstd,
            tmean=float(t.mean()), tstd_u=float(t.std()),
            tmin=float(t.min()), tmax=float(t.max()),
            skew=float(((t - t.mean()) ** 3).mean() / (t.std() ** 3 + 1e-15)),
            kurt=float(((t - t.mean()) ** 4).mean() / (t.std() ** 4 + 1e-15)),
            Wf2=float(np.sum(W ** 2)),
            Cf2=float(np.sum(C ** 2)),
            symfrac=float(np.sum(Ws ** 2) / np.sum(W ** 2)),
            ho_f2=float(np.sum(Ho ** 2)),
            ho_sv_top=float(ho_sv[0]),
            ho_sv_med=float(np.median(ho_sv)),
            cos_top=float(coss[0]),
            cos_med=float(np.median(coss)),
            cos_p10=float(np.percentile(coss, 10)),
            n_cos_gt_05=int(np.sum(coss > 0.5)),
            n_cos_gt_08=int(np.sum(coss > 0.8)),
            corr_t_sig=float(corr_t_sig),
            corr_abs_t_sig=float(corr_abs_t_sig),
            corr_t_idx=float(corr_t_idx),
            # scale alignment: corr of log sq and log sk after optimal permutation? use sorted
            corr_sq_sk=float(np.corrcoef(sq, sk)[0, 1]),
            sq_cv=float(sq.std() / sq.mean()),
            sk_cv=float(sk.std() / sk.mean()),
            sl_cv=float(sl.std() / sl.mean()),
        )
        rows.append(rec)
        sig_L.append(sl / np.sqrt(np.mean(sl ** 2)))
        sig_Q.append(sq / np.sqrt(np.mean(sq ** 2)))
        sig_K.append(sk / np.sqrt(np.mean(sk ** 2)))
        cos2.append(coss ** 2)
        t_all.append(t)
        if (l, h) in [(0, 5), (5, 9), (0, 0), (11, 0)]:
            examples[(l, h)] = dict(t=t.copy(), sl=sl.copy(), coss=coss.copy(), sq=sq.copy(), sk=sk.copy(), W=W.copy())

print("=== per-head summaries (raw) ===")
keys = ["prL","prQ","prK","offrms","diagfrac","tbar","tstd","tmean","tstd_u","Wf2","symfrac",
        "ho_f2","ho_sv_top","ho_sv_med","cos_top","cos_med","cos_p10","n_cos_gt_05","n_cos_gt_08",
        "corr_t_sig","corr_abs_t_sig","corr_t_idx","corr_sq_sk","sq_cv","sk_cv","sl_cv","skew","kurt"]
for k in keys:
    summarize(k, [r[k] for r in rows])

# correlations
def col(k):
    return np.array([r[k] for r in rows])

print("\n=== correlations ===")
pairs = [("diagfrac","abs_tbar"), ("offrms","diagfrac"), ("offrms","tstd"), ("offrms","Wf2"),
         ("prL","prQ"), ("prL","prK"), ("tstd","diagfrac"), ("cos_top","diagfrac"),
         ("n_cos_gt_05","diagfrac"), ("symfrac","diagfrac"), ("ho_f2","diagfrac"),
         ("corr_abs_t_sig","diagfrac"), ("tstd_u","tstd"), ("prL","sl_cv")]
# abs tbar
abs_tbar = np.abs(col("tbar"))
data = {k: col(k) for k in keys}
data["abs_tbar"] = abs_tbar
for a, b in pairs:
    print(f"  corr({a},{b})={np.corrcoef(data[a], data[b])[0,1]:+.3f}")

print("\n=== normalized singular-value quantiles (median over heads) ===")
for name, arr in [("L", sig_L), ("Q", sig_Q), ("K", sig_K)]:
    A = np.stack(arr, 0)
    med = np.median(A, 0)
    p10 = np.percentile(A, 10, 0)
    p90 = np.percentile(A, 90, 0)
    # print a decimated curve
    idx = [0, 1, 3, 7, 15, 31, 47, 55, 63]
    print(name, " ".join(f"{med[i]:.3f}" for i in idx))

print("\n=== cos^2 quantiles (median spectrum of principal cos^2, sorted desc) ===")
C2 = np.sort(np.stack(cos2, 0), axis=1)[:, ::-1]
med = np.median(C2, 0)
print(" ".join(f"{med[i]:.3f}" for i in [0, 1, 2, 3, 5, 10, 20, 40, 63]))
print("median sum cos^2", np.median(C2.sum(1)))

print("\n=== pooled t moments ===")
T = np.concatenate(t_all)
print(f"pooled mean {T.mean():+.4f} std {T.std():.4f} skew {((T-T.mean())**3).mean()/T.std()**3:.3f} kurt {((T-T.mean())**4).mean()/T.std()**4:.3f}")
# fraction |t|<0.05, >0.3, >0.5
for thr in [0.05, 0.1, 0.2, 0.3, 0.5, 0.8]:
    print(f"  P(|t|>{thr})={np.mean(np.abs(T)>thr):.3f}")

print("\n=== examples ===")
for k, e in examples.items():
    t = e["t"]
    print(f"L{k[0]}H{k[1]} tbar={t.mean():+.3f} std={t.std():.3f} min={t.min():+.3f} max={t.max():+.3f} "
          f"top|t|={np.sort(np.abs(t))[::-1][:6].round(3)} cos_top={e['coss'][:6].round(3)} "
          f"sl/sl[0]={ (e['sl']/e['sl'][0])[:6].round(3) }")

# Gaussian null reference for the same factorization stats, 30 draws matched to one head's norms
print("\n=== gaussian null (30 draws) factorization ===")
Q0 = rows[0]
# use shape only
gn = []
for i in range(30):
    Q = rng.standard_normal((n, N))
    K = rng.standard_normal((n, N))
    Uq, sq, Vqh = np.linalg.svd(Q, full_matrices=False)
    Uk, sk, Vkh = np.linalg.svd(K, full_matrices=False)
    Ho = Uk.T @ Uq
    C = Vkh @ Vqh.T
    M = (sk[:, None] * Ho) * sq[None, :]
    P, sl, Sh = np.linalg.svd(M, full_matrices=False)
    W = P.T @ C @ Sh.T
    t = np.diag(W)
    coss = np.linalg.svd(C, compute_uv=False)
    gn.append(dict(prL=pr(sl), prQ=pr(sq), offrms=np.sqrt(np.sum((W-np.diag(t))**2)/(n*n-n)),
                   diagfrac=np.sum(t**2)/np.sum(W**2), Wf2=np.sum(W**2),
                   symfrac=np.sum(((W+W.T)/2)**2)/np.sum(W**2),
                   cos_top=coss[0], tstd_u=t.std(), ho_f2=np.sum(Ho**2)))
for k in ["prL","prQ","offrms","diagfrac","Wf2","symfrac","cos_top","tstd_u","ho_f2"]:
    summarize("null "+k, [g[k] for g in gn])

# save spectra medians for later
np.savez("/tmp/gpt2_diag.npz",
         sigL=np.stack(sig_L, 0), sigQ=np.stack(sig_Q, 0), sigK=np.stack(sig_K, 0),
         cos2=C2, t=np.stack(t_all, 0),
         **{k: col(k) for k in ["prL","diagfrac","tbar","tstd","offrms","Wf2","layer","head"]})
print("saved /tmp/gpt2_diag.npz")
