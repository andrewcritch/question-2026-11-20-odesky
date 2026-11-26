import sys
sys.path.insert(0, './ensemble_brief')
import numpy as np
import common

w_all, heads = common.load()
N, n, H = common.N, common.n, common.H

print(f"Loaded {len(heads)} heads, N={N}, n={n}")

# Collect detailed diagnostics per head
diag_sym_ratios = []
off_sym_corrs = []
qq_kk_diffs = []
pr_Q = []
pr_K = []
pr_L = []
w_sv_means = []
t_stds = []
t_bars = []
off_rmss = []
diag_fracs = []
rank_corrs_s_t = []
rank_corrs_s_abst = []
kurt_t = []
skew_t = []
err1_full = []
err1_diagW = []
amb_full = []
amb_diagW = []

# Also check residual stream covariance across all Q, K
cov_all = np.zeros((N, N))

for l, h, Q, K in heads:
    L = K.T @ Q
    U, s, Vt = np.linalg.svd(L, full_matrices=False)
    U, s, V = U[:, :n], s[:n], Vt[:n].T
    W = U.T @ V
    t = np.diag(W)
    off = W - np.diag(t)
    
    # Check symmetry of off-diagonal W: corr(W_ij, W_ji)
    iu = np.triu_indices(n, 1)
    w_up = W[iu]
    w_lo = W.T[iu]
    c_sym = np.corrcoef(w_up, w_lo)[0, 1]
    off_sym_corrs.append(c_sym)
    
    # Balance between Q Q^T and K K^T
    G_Q = Q @ Q.T
    G_K = K @ K.T
    qq_kk_diffs.append(np.linalg.norm(G_Q / np.trace(G_Q) - G_K / np.trace(G_K), 'fro') / np.linalg.norm(G_Q / np.trace(G_Q), 'fro'))
    
    sq = np.linalg.svd(Q, compute_uv=False)
    sk = np.linalg.svd(K, compute_uv=False)
    pr_Q.append(np.sum(sq**2)**2 / np.sum(sq**4))
    pr_K.append(np.sum(sk**2)**2 / np.sum(sk**4))
    pr_L.append(np.sum(s**2)**2 / np.sum(s**4))
    
    w_sv = np.linalg.svd(W, compute_uv=False)
    w_sv_means.append(np.mean(w_sv))
    
    wt = s**2 / np.sum(s**2)
    tb = wt @ t
    ts = np.sqrt(wt @ (t - tb)**2)
    t_bars.append(tb)
    t_stds.append(ts)
    off_rmss.append(np.sqrt(np.sum(off**2) / (n*n - n)))
    diag_fracs.append(np.sum(t**2) / np.sum(W**2))
    
    # Correlation of s_i (or i) with t_i and |t_i|
    idx = np.arange(n, dtype=float)
    rank_corrs_s_t.append(np.corrcoef(idx, t * np.sign(tb if tb != 0 else 1.0))[0, 1])
    rank_corrs_s_abst.append(np.corrcoef(idx, np.abs(t))[0, 1])
    
    # Surrogate with diagonal W only: L_diag includes exact same s and t, zero off-diag
    # For block model: lambda_+,i = s_i (1 + t_i)/2, lambda_-,i = s_i (1 - t_i)/2, sv_i = s_i sqrt(1 - t_i^2)/2
    lp_d = np.sort(s * (1 + t) / 2)[::-1]
    lm_d = np.sort(s * (1 - t) / 2)[::-1]
    sv_d = np.sort(s * np.sqrt(np.maximum(0, 1 - t**2)) / 2)[::-1]
    e1_d = np.linalg.norm(sv_d - np.sqrt(lp_d * lm_d)) / np.linalg.norm(sv_d)
    nL_d = np.sum(s**2)
    a_d = 2 * np.sum(sv_d**2) / nL_d
    b_d = 2 * (lp_d @ lm_d) / nL_d
    
    st = common.stats(L)
    err1_full.append(st['err1'])
    err1_diagW.append(e1_d)
    amb_full.append(st['amb'])
    amb_diagW.append(a_d - b_d)
    
    cov_all += (Q.T @ Q / np.sum(Q**2) + K.T @ K / np.sum(K**2)) / (2 * len(heads))

def qstr(arr):
    arr = np.array(arr)
    return f"{np.median(arr):+.4f} [{np.percentile(arr, 10):+.4f}, {np.percentile(arr, 90):+.4f}]"

print("off_sym_corr (corr(W_ij, W_ji)):", qstr(off_sym_corrs))
print("rel diff G_Q vs G_K:            ", qstr(qq_kk_diffs))
print("PR(Q):                          ", qstr(pr_Q))
print("PR(K):                          ", qstr(pr_K))
print("PR(L):                          ", qstr(pr_L))
print("mean SV of W (principal cos):   ", qstr(w_sv_means))
print("corr(index, signed t_i):        ", qstr(rank_corrs_s_t))
print("corr(index, |t_i|):             ", qstr(rank_corrs_s_abst))
print("err1 full W:                    ", qstr(err1_full))
print("err1 diag(t) surrogate:         ", qstr(err1_diagW))
print("corr(err1_full, err1_diagW):    ", f"{np.corrcoef(err1_full, err1_diagW)[0,1]:.4f}")
print("a-b full W:                     ", qstr(amb_full))
print("a-b diag(t) surrogate:          ", qstr(amb_diagW))
print("corr(amb_full, amb_diagW):      ", f"{np.corrcoef(amb_full, amb_diagW)[0,1]:.4f}")

# Global cov_all PR
ev_cov = np.linalg.eigvalsh(cov_all)[::-1]
pr_cov = np.sum(ev_cov)**2 / np.sum(ev_cov**2)
print(f"Global residual cov PR (out of {N}): {pr_cov:.1f}, top 5 eigvals*N: {ev_cov[:5]*N}")

# Inspect specific heads mentioned in brief.md + diverse heads
for (l, h) in [(0, 0), (0, 1), (0, 5), (0, 9), (1, 1), (2, 2), (5, 9), (7, 4), (10, 7), (11, 3)]:
    _, _, Q, K = heads[l*12 + h]
    L = K.T @ Q
    U, s, Vt = np.linalg.svd(L, full_matrices=False)
    U, s, V = U[:, :n], s[:n], Vt[:n].T
    W = U.T @ V
    t = np.diag(W)
    off = W - np.diag(t)
    w_sv = np.linalg.svd(W, compute_uv=False)
    # Check row-by-row cosine in raw head coordinates!
    row_cos = np.sum(Q * K, axis=1) / (np.linalg.norm(Q, axis=1) * np.linalg.norm(K, axis=1))
    print(f"\nHead L{l}H{h}: PR(L)={np.sum(s**2)**2/np.sum(s**4):.1f}, diagfrac={np.sum(t**2)/np.sum(W**2):.3f}, offrms={np.sqrt(np.sum(off**2)/(n*n-n)):.4f}")
    print(f"  t quantiles [0,10,25,50,75,90,100]: {np.round(np.percentile(t, [0,10,25,50,75,90,100]), 3)}")
    print(f"  W sv quantiles [0,25,50,75,100]:    {np.round(np.percentile(w_sv, [0,25,50,75,100]), 3)}")
    print(f"  raw Q_i . K_i cos [0,25,50,75,100]: {np.round(np.percentile(row_cos, [0,25,50,75,100]), 3)}")
    # Check if W_{ij} is larger near the diagonal |i-j| <= 3 vs far |i-j| > 10!
    idx_diff = np.abs(np.arange(n)[:, None] - np.arange(n)[None, :])
    near_rms = np.sqrt(np.mean(W[(idx_diff >= 1) & (idx_diff <= 3)]**2))
    far_rms = np.sqrt(np.mean(W[idx_diff > 10]**2))
    print(f"  offdiag RMS near (1<=|i-j|<=3)={near_rms:.4f} vs far (|i-j|>10)={far_rms:.4f}")
