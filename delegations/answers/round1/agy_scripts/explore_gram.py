import sys
sys.path.insert(0, '.')
sys.path.insert(0, './ensemble_brief')
import numpy as np
from scipy import stats as sp_stats
import common

w_all, heads = common.load()
N, n, H = common.N, common.n, common.H

# Let's inspect:
# 1. Distribution shape of t_i within heads (is it Gaussian, Beta/tanh-Gaussian, Uniform, bimodal, skewed?)
# 2. Relationship between tbar, tstd, diagfrac, offrms, PR across the 144 heads
# 3. Regression K = M Q + E: eigenvalues/singular values of M, symmetry of M
# 4. Per-layer residual covariance vs per-head Q^T Q + K^T K
# 5. Correlation between s_i and t_i, s_i and |t_i|, s_i and t_i^2 within heads

from explore_deep import fast_stats
all_st = [fast_stats(Q, K) for _, _, Q, K in heads]

tbars = np.array([r['tbar'] for r in all_st])
tstds = np.array([r['tstd'] for r in all_st])
diags = np.array([r['diag'] for r in all_st])
offs = np.array([r['offrms'] for r in all_st])
err1s = np.array([r['err1'] for r in all_st])
ambs = np.array([r['amb'] for r in all_st])
cmds = np.array([r['cmd'] for r in all_st])
prs = np.array([r['PR'] for r in all_st])

print("=== Cross-head correlations (144 heads) ===")
names = ['tbar', 'abs_tbar', 'tstd', 'diag', 'offrms', 'err1', 'amb', 'abs_amb', 'cmd', 'PR']
vecs = [tbars, np.abs(tbars), tstds, diags, offs, err1s, ambs, np.abs(ambs), cmds, prs]
header = "          " + "".join(f"{nm:>9s}" for nm in names)
print(header)
for nm, v1 in zip(names, vecs):
    row = f"{nm:10s}" + "".join(f"{np.corrcoef(v1, v2)[0,1]:+9.3f}" for v2 in vecs)
    print(row)

# Check unweighted mean and std of t_i vs sigma^2-weighted tbar and tstd
t_mean_unw = np.array([np.mean(r['t']) for r in all_st])
t_std_unw = np.array([np.std(r['t']) for r in all_st])
print(f"\nt_mean unweighted: {np.median(t_mean_unw):+.4f} [{np.percentile(t_mean_unw,10):+.4f}, {np.percentile(t_mean_unw,90):+.4f}]")
print(f"t_std unweighted:  {np.median(t_std_unw):+.4f} [{np.percentile(t_std_unw,10):+.4f}, {np.percentile(t_std_unw,90):+.4f}]")
print(f"tbar (weighted):   {np.median(tbars):+.4f} [{np.percentile(tbars,10):+.4f}, {np.percentile(tbars,90):+.4f}]")
print(f"tstd (weighted):   {np.median(tstds):+.4f} [{np.percentile(tstds,10):+.4f}, {np.percentile(tstds,90):+.4f}]")
print(f"corr(tbar, t_mean_unw) = {np.corrcoef(tbars, t_mean_unw)[0,1]:.4f}, median(|tbar| - |t_mean_unw|) = {np.median(np.abs(tbars) - np.abs(t_mean_unw)):+.4f}")
print(f"corr(tstd, t_std_unw)  = {np.corrcoef(tstds, t_std_unw)[0,1]:.4f}, median(tstd - t_std_unw) = {np.median(tstds - t_std_unw):+.4f}")

# Check brief.md observation: "Across heads with |tbar|>0.05, median corr between singular-value index and signed t_i is -0.11"
mask05 = np.abs(tbars) > 0.05
idx = np.arange(n, dtype=float)
corrs_idx_signed = [np.corrcoef(idx, r['t'] * np.sign(r['tbar']))[0, 1] for r, m in zip(all_st, mask05) if m]
corrs_s_t2 = [np.corrcoef(r['s'], r['t']**2)[0, 1] for r in all_st]
print(f"\nFor |tbar|>0.05 ({np.sum(mask05)} heads): median corr(index, sign(tbar)*t_i) = {np.median(corrs_idx_signed):+.4f}")
print(f"All 144 heads: median corr(s_i, t_i^2) = {np.median(corrs_s_t2):+.4f} [{np.percentile(corrs_s_t2,10):+.4f}, {np.percentile(corrs_s_t2,90):+.4f}]")

# Check distribution of Fisher z = arctanh(t_i) within heads!
ks_norm_t = []
ks_norm_z = []
kurt_z = []
skew_z_signed = []
for r in all_st:
    t = np.clip(r['t'], -0.999, 0.999)
    z = np.arctanh(t)
    t_stdz = (t - np.mean(t)) / (np.std(t) + 1e-12)
    z_stdz = (z - np.mean(z)) / (np.std(z) + 1e-12)
    ks_norm_t.append(sp_stats.kstest(t_stdz, 'norm').statistic)
    ks_norm_z.append(sp_stats.kstest(z_stdz, 'norm').statistic)
    kurt_z.append(sp_stats.kurtosis(z))
    sgn = np.sign(r['tbar']) if abs(r['tbar']) > 1e-6 else 1.0
    skew_z_signed.append(sp_stats.skew(z * sgn))

print(f"\nWithin-head normality KS stat (n=64, expected for true normal ~0.075):")
print(f"  t_i:          {np.median(ks_norm_t):.4f} [{np.percentile(ks_norm_t,10):.4f}, {np.percentile(ks_norm_t,90):.4f}]")
print(f"  z=arctanh(t): {np.median(ks_norm_z):.4f} [{np.percentile(ks_norm_z,10):.4f}, {np.percentile(ks_norm_z,90):.4f}]")
print(f"  excess kurtosis of z=arctanh(t): {np.median(kurt_z):+.4f} [{np.percentile(kurt_z,10):+.4f}, {np.percentile(kurt_z,90):+.4f}]")
print(f"  signed skew of z=arctanh(t):     {np.median(skew_z_signed):+.4f} [{np.percentile(skew_z_signed,10):+.4f}, {np.percentile(skew_z_signed,90):+.4f}]")

# Check M = K Q^T (Q Q^T)^{-1}: how much of K is explained by M Q?
r2_K_from_Q = []
sym_frac_M = []
for _, _, Q, K in heads:
    M = (K @ Q.T) @ np.linalg.inv(Q @ Q.T)
    K_hat = M @ Q
    r2_K_from_Q.append(np.sum(K_hat**2) / np.sum(K**2))
    Ms = (M + M.T) / 2
    sym_frac_M.append(np.sum(Ms**2) / np.sum(M**2))
print(f"\nLinear regression K = M Q + E in head space:")
print(f"  ||M Q||^2 / ||K||^2 (null=n/N=0.0833): {np.median(r2_K_from_Q):.4f} [{np.percentile(r2_K_from_Q,10):.4f}, {np.percentile(r2_K_from_Q,90):.4f}]")
print(f"  symmetric energy of M (null ~0.508):   {np.median(sym_frac_M):.4f} [{np.percentile(sym_frac_M,10):.4f}, {np.percentile(sym_frac_M,90):.4f}]")

# Check per-layer residual covariance PR (using all 12 heads in layer l)
for l in range(12):
    cov_l = np.zeros((N, N))
    for h in range(12):
        _, _, Q, K = heads[l*12 + h]
        cov_l += (Q.T @ Q / np.sum(Q**2) + K.T @ K / np.sum(K**2)) / 24.0
    ev = np.linalg.eigvalsh(cov_l)
    pr_l = np.sum(ev)**2 / np.sum(ev**2)
    off_l = np.median([all_st[l*12+h]['offrms'] for h in range(12)])
    print(f"  Layer {l:2d}: layer-cov PR={pr_l:5.1f} (1/sqrt(PR)={1/np.sqrt(pr_l):.4f}), median head offrms={off_l:.4f}")
