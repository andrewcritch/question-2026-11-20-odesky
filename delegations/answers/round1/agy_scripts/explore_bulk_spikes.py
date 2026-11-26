import sys
sys.path.insert(0, '.')
sys.path.insert(0, './ensemble_brief')
import numpy as np
import common
from explore_deep import fast_stats

w_all, heads = common.load()
N, n, H = common.N, common.n, common.H
all_st = [fast_stats(Q, K) for _, _, Q, K in heads]

# Also compute lnfold stats
P = np.eye(N) - np.ones((N, N)) / N
ln_st = []
pre = '' if 'h.0.attn.c_attn.weight' in w_all else 'transformer.'
for l, h, Q, K in heads:
    g = w_all[f'{pre}h.{l}.ln_1.weight'].astype(np.float64)
    Q_ln = (Q * g[None, :]) @ P
    K_ln = (K * g[None, :]) @ P
    ln_st.append(fast_stats(Q_ln, K_ln))

for label, st_list in [('RAW', all_st), ('LNFOLD', ln_st)]:
    tstd_all = np.array([r['tstd'] for r in st_list])
    std_unw = np.array([np.std(r['t']) for r in st_list])
    std_skip4 = np.array([np.std(r['t'][4:]) for r in st_list])
    std_skip8 = np.array([np.std(r['t'][8:]) for r in st_list])
    std_skip16 = np.array([np.std(r['t'][16:]) for r in st_list])
    gap_top4_bulk = np.array([np.mean(r['t'][:4]) - np.mean(r['t'][16:]) for r in st_list])
    abs_gap_top4 = np.array([np.abs(np.mean(r['t'][:4]) - np.mean(r['t'][16:])) for r in st_list])
    
    def q(x):
        return f"{np.median(x):.4f} [{np.percentile(x,10):.4f}, {np.percentile(x,90):.4f}]"
    print(f"=== {label} (144 heads) ===")
    print(f"  sigma^2-weighted tstd: {q(tstd_all)}")
    print(f"  unweighted std(t):     {q(std_unw)}")
    print(f"  std(t[4:]):            {q(std_skip4)}")
    print(f"  std(t[8:]):            {q(std_skip8)}")
    print(f"  std(t[16:]):           {q(std_skip16)}")
    print(f"  |mean(t[:4])-mean(t[16:])|: {q(abs_gap_top4)}")
    print(f"  mean(t[:4])-mean(t[16:]):   {np.median(gap_top4_bulk):+.4f} [{np.percentile(gap_top4_bulk,10):+.4f}, {np.percentile(gap_top4_bulk,90):+.4f}]")

# Also check if top singular vectors of different heads in the SAME layer share directions in R^N!
print("\n=== Alignment of top singular vectors u_1, v_1 with residual-stream outlier / all-ones direction ===")
ones_u = np.ones(N) / np.sqrt(N)
u1_ones = []
v1_ones = []
u1_pc1 = []
# Compute top PC of all Q, K rows in GPT-2
all_rows = np.vstack([np.vstack([Q, K]) for _, _, Q, K in heads])
_, sv_glob, vt_glob = np.linalg.svd(all_rows, full_matrices=False)
print("Top 10 singular values of stacked (Q,K) across all 144 heads:", np.round(sv_glob[:10], 2))
print("|cos(global PC1, all-ones)|:", abs(vt_glob[0] @ ones_u))

for l, h, Q, K in heads:
    L = K.T @ Q
    # top singular vectors via power / svd on reduced
    U, s, Vt = np.linalg.svd(L, full_matrices=False)
    u1, v1 = U[:, 0], Vt[0]
    u1_ones.append(abs(u1 @ ones_u))
    v1_ones.append(abs(v1 @ ones_u))
    u1_pc1.append(np.linalg.norm(vt_glob[:4] @ u1))
print(f"median |<u_1, 1/sqrt(N)>|: {np.median(u1_ones):.4f} [{np.percentile(u1_ones,10):.4f}, {np.percentile(u1_ones,90):.4f}]")
print(f"median ||P_top4_global u_1||: {np.median(u1_pc1):.4f} [{np.percentile(u1_pc1,10):.4f}, {np.percentile(u1_pc1,90):.4f}]")
