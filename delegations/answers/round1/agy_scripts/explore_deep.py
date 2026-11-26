import sys
sys.path.insert(0, './ensemble_brief')
import numpy as np
import common

w_all, heads = common.load()
N, n, H = common.N, common.n, common.H

def fast_stats(Q, K):
    # Q, K: (n, N)
    M = np.vstack([K, Q])  # (2n, N)
    # QR of M.T: (N, 2n) -> R is (2n, 2n)
    R = np.linalg.qr(M.T, mode='r')  # (2n, 2n)
    Kh = R[:, :n].T   # (n, 2n)
    Qh = R[:, n:].T   # (n, 2n)
    Lh = Kh.T @ Qh    # (2n, 2n)
    S = (Lh + Lh.T) / 2
    T = (Lh - Lh.T) / 2
    ev = np.linalg.eigvalsh(S)
    lp = np.sort(ev[ev > 1e-14])[::-1][:n]
    lm = np.sort(-ev[ev < -1e-14])[::-1][:n]
    k = min(len(lp), len(lm))
    lp, lm = lp[:k], lm[:k]
    sv = np.linalg.svd(T, compute_uv=False)[:2*n:2][:k]
    nL = np.sum(Lh * Lh)
    a = np.sum(T * T) / nL
    b = 2 * (lp @ lm) / nL
    dif = lp - lm
    c = np.sum(np.maximum(dif, 0)**2) / nL
    d = np.sum(np.maximum(-dif, 0)**2) / nL
    e1 = np.linalg.norm(sv - np.sqrt(lp * lm)) / np.linalg.norm(sv)
    U, s, Vt = np.linalg.svd(Lh)
    U, s, V = U[:, :n], s[:n], Vt[:n].T
    W = U.T @ V
    t = np.diag(W)
    wt = s**2 / np.sum(s**2)
    tbar = wt @ t
    tstd = np.sqrt(wt @ (t - tbar)**2)
    off = W - np.diag(t)
    offrms = np.sqrt(np.sum(off**2) / (n*n - n))
    return dict(a=a, b=b, c=c, d=d, err1=e1, amb=a-b, cmd=c-d, tbar=tbar, tstd=tstd,
                offrms=offrms, diag=np.sum(t**2)/np.sum(W**2), PR=np.sum(s**2)**2/np.sum(s**4),
                W=W, s=s, t=t)

# Verify fast_stats matches common.stats to machine precision on head 0
st0_exact = common.stats(heads[0][3].T @ heads[0][2])
st0_fast = fast_stats(heads[0][2], heads[0][3])
print("Max diff fast vs exact:", max(abs(st0_exact[k] - st0_fast[k]) for k in ['err1', 'amb', 'cmd', 'tbar', 'tstd', 'offrms', 'diag', 'PR']))

all_st = [fast_stats(Q, K) for _, _, Q, K in heads]

# 1. Check raw head-space matrices Q Q^T, K K^T, K Q^T
diag_share_KQ = []
diag_share_QQ = []
diag_share_KK = []
for (_, _, Q, K), st in zip(heads, all_st):
    KQ = K @ Q.T
    QQ = Q @ Q.T
    KK = K @ K.T
    diag_share_KQ.append(np.sum(np.diag(KQ)**2) / np.sum(KQ**2))
    diag_share_QQ.append(np.sum(np.diag(QQ)**2) / np.sum(QQ**2))
    diag_share_KK.append(np.sum(np.diag(KK)**2) / np.sum(KK**2))

print(f"Raw head-space diag share (null=1/64=0.0156):")
print(f"  K Q^T: {np.median(diag_share_KQ):.4f} [{np.percentile(diag_share_KQ,10):.4f}, {np.percentile(diag_share_KQ,90):.4f}]")
print(f"  Q Q^T: {np.median(diag_share_QQ):.4f} [{np.percentile(diag_share_QQ,10):.4f}, {np.percentile(diag_share_QQ,90):.4f}]")
print(f"  K K^T: {np.median(diag_share_KK):.4f} [{np.percentile(diag_share_KK,10):.4f}, {np.percentile(diag_share_KK,90):.4f}]")

# 2. Understand heads with positive a-b vs negative a-b!
ambs = np.array([st['amb'] for st in all_st])
prs = np.array([st['PR'] for st in all_st])
tstds = np.array([st['tstd'] for st in all_st])
tbars = np.array([st['tbar'] for st in all_st])
offrmss = np.array([st['offrms'] for st in all_st])
err1s = np.array([st['err1'] for st in all_st])

# Compute tr(L^2)/||L||^2 decomposition: diag term sum w_i t_i^2 vs off-diag term sum_{i!=j} (s_i s_j / ||L||^2) W_ij W_ji
diag_tr2 = []
off_tr2 = []
for st in all_st:
    s = st['s']; W = st['W']; t = st['t']
    nL = np.sum(s**2)
    d_term = np.sum(s**2 * t**2) / nL
    # total tr(L^2)/nL = tr(diag(s) W diag(s) W) / nL
    SW = s[:, None] * W
    tot = np.sum(SW * SW.T) / nL
    diag_tr2.append(d_term)
    off_tr2.append(tot - d_term)
diag_tr2 = np.array(diag_tr2)
off_tr2 = np.array(off_tr2)

print("\ntr(L^2)/||L||^2 decomposition:")
print(f"  diag sum w_i t_i^2:             {np.median(diag_tr2):+.4f} [{np.percentile(diag_tr2,10):+.4f}, {np.percentile(diag_tr2,90):+.4f}]")
print(f"  offdiag sum s_i s_j W_ij W_ji:  {np.median(off_tr2):+.4f} [{np.percentile(off_tr2,10):+.4f}, {np.percentile(off_tr2,90):+.4f}]")
print(f"  corr(a-b, -off_tr2):            {np.corrcoef(ambs, -off_tr2)[0,1]:.4f}")
print(f"  corr(a-b, PR):                  {np.corrcoef(ambs, prs)[0,1]:.4f}")
print(f"  corr(off_tr2, PR):              {np.corrcoef(off_tr2, prs)[0,1]:.4f}")

print("\nTop 8 heads with MOST POSITIVE a-b:")
for idx in np.argsort(-ambs)[:8]:
    l, h = idx // 12, idx % 12
    st = all_st[idx]
    W = st['W']; s = st['s']
    print(f"  L{l}H{h}: a-b={st['amb']:+.4f}, err1={st['err1']:.4f}, PR={st['PR']:.1f}, tbar={st['tbar']:+.3f}, tstd={st['tstd']:.3f}, off_tr2={off_tr2[idx]:+.4f}")
    print(f"    top 6 s/s[0]: {np.round(s[:6]/s[0], 3)}")
    print(f"    top 4x4 of W:\n{np.round(W[:4,:4], 3)}")

print("\nTop 8 heads with MOST NEGATIVE a-b:")
for idx in np.argsort(ambs)[:8]:
    l, h = idx // 12, idx % 12
    st = all_st[idx]
    W = st['W']; s = st['s']
    print(f"  L{l}H{h}: a-b={st['amb']:+.4f}, err1={st['err1']:.4f}, PR={st['PR']:.1f}, tbar={st['tbar']:+.3f}, tstd={st['tstd']:.3f}, off_tr2={off_tr2[idx]:+.4f}")

# 3. Check residual stream subspace sharing between Q and K of the SAME head vs DIFFERENT heads!
# Specifically: let M_head = (Q^T Q / ||Q||^2 + K^T K / ||K||^2)/2 in R^{N x N} (rank <= 2n).
# What are the eigenvalues of (Q_orth_Q^T Q_orth_K), i.e., principal cosines between row(Q) and row(K)?
pcos_means = []
pcos_maxs = []
pcos_prs = []
for _, _, Q, K in heads:
    Uq = np.linalg.svd(Q, full_matrices=False)[2]  # (n, N)
    Uk = np.linalg.svd(K, full_matrices=False)[2]  # (n, N)
    pc = np.linalg.svd(Uk @ Uq.T, compute_uv=False) # principal cosines! Note Uk @ Uq.T has SAME singular values as W = U^T V!
    pcos_means.append(np.mean(pc))
    pcos_maxs.append(np.max(pc))
    pcos_prs.append(np.sum(pc**2)) # sum of cos^2 = ||W||_F^2!

w_fro2 = np.array([np.sum(st['W']**2) for st in all_st])
t_fro2 = np.array([np.sum(st['t']**2) for st in all_st])
off_fro2 = w_fro2 - t_fro2
print(f"\n||W||_F^2 decomposition (null: ||W||_F^2 = n^2/N = 5.333, sum t_i^2 = n/N = 0.083, off = 5.250):")
print(f"  ||W||_F^2:      {np.median(w_fro2):.3f} [{np.percentile(w_fro2,10):.3f}, {np.percentile(w_fro2,90):.3f}]")
print(f"  sum t_i^2:      {np.median(t_fro2):.3f} [{np.percentile(t_fro2,10):.3f}, {np.percentile(t_fro2,90):.3f}]")
print(f"  ||W_off||_F^2:  {np.median(off_fro2):.3f} [{np.percentile(off_fro2,10):.3f}, {np.percentile(off_fro2,90):.3f}]")
