import sys
sys.path.insert(0, '.')
sys.path.insert(0, './ensemble_brief')
import numpy as np
import common
from explore_deep import fast_stats

w_all, heads = common.load()
all_st = [fast_stats(Q, K) for _, _, Q, K in heads]

# Check exact sign of brief.md's correlation observation!
tbars = np.array([r['tbar'] for r in all_st])
mask = np.abs(tbars) > 0.05
idx1 = np.arange(1, 65, dtype=float)
c_idx_t = [np.corrcoef(idx1, r['t'])[0, 1] for r, m in zip(all_st, mask) if m]
c_idx_st = [np.corrcoef(idx1, r['t'] * np.sign(r['tbar']))[0, 1] for r, m in zip(all_st, mask) if m]
c_s_st = [np.corrcoef(r['s'], r['t'] * np.sign(r['tbar']))[0, 1] for r, m in zip(all_st, mask) if m]
c_idx_abs = [np.corrcoef(idx1, np.abs(r['t']))[0, 1] for r in all_st]
print("Median corr(idx 1..64, t_i) on |tbar|>0.05:             ", np.median(c_idx_t))
print("Median corr(idx 1..64, sign(tbar)*t_i) on |tbar|>0.05:  ", np.median(c_idx_st))
print("Median corr(s_i, sign(tbar)*t_i) on |tbar|>0.05:        ", np.median(c_s_st))
print("Median corr(idx 1..64, |t_i|) on all 144:               ", np.median(c_idx_abs))

# Print detailed (s_i, t_i) profiles for 12 diverse heads
sample_heads = [(0,0), (0,1), (0,3), (0,5), (0,9), (1,1), (1,8), (2,2), (3,6), (5,9), (7,4), (10,7)]
for l, h in sample_heads:
    r = all_st[l*12 + h]
    s, t = r['s'], r['t']
    print(f"\n=== L{l}H{h}: tbar={r['tbar']:+.3f}, tstd={r['tstd']:.3f}, diag={r['diag']:.3f}, off={r['offrms']:.3f}, PR={r['PR']:.1f}, err1={r['err1']:.3f}, a-b={r['amb']:+.3f} ===")
    print("  s_i (every 4th):", np.round(s[::4], 3))
    print("  t_i (first 16): ", np.round(t[:16], 3))
    print("  t_i (mid 16):   ", np.round(t[24:40], 3))
    print("  t_i (last 16):  ", np.round(t[48:], 3))
