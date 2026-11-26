import sys
sys.path.insert(0, '.')
sys.path.insert(0, './ensemble_brief')
import numpy as np
import common
from fit_and_evaluate import fast_stats, make_gamma_sqrt, STATS_KEYS, fmt_dist

N, n, H = common.N, common.n, common.H
w_all, heads = common.load()
gpt_raw = [fast_stats(Q, K) for _, _, Q, K in heads]
gam_430 = make_gamma_sqrt(N, 430.0)

def sample_signed_spike(r0, gamma, nu=0.0, gam=gam_430, rng=None):
    # 2 parameters per head when nu=0: r0 in (-1, 1), gamma in R!
    # Q = X0 + |gamma| diag(g) F
    # K = (r0 X0 + sqrt(1 - r0^2) Y0) + gamma diag(g) F
    # Optional 3rd parameter nu >= 0: rotary 2x2 skew pairs!
    X0 = rng.standard_normal((n, N)) * gam[None, :]
    Y0 = rng.standard_normal((n, N)) * gam[None, :]
    F = rng.standard_normal((n, N)) * gam[None, :]
    g = rng.standard_normal((n, 1))
    Q = X0 + np.abs(gamma) * g * F
    K = (r0 * X0 + np.sqrt(1.0 - r0**2) * Y0) + gamma * g * F
    if nu > 0:
        F_rot = rng.standard_normal((n, N)) * gam[None, :]
        w_half = nu * rng.standard_normal(n // 2)
        w_pair = np.repeat(w_half, 2)[:, None]
        JF_rot = np.empty_like(F_rot)
        JF_rot[0::2] = F_rot[1::2]
        JF_rot[1::2] = -F_rot[0::2]
        Q = Q + w_pair * F_rot
        K = K + w_pair * JF_rot
    return Q, K

# Fast analytical + simulated grid fit for (r0, gamma) in (-1, 1) x R!
# Notice we can fit (r0, gamma) NOT ONLY to (tbar, tstd), OR even check fitting to (tbar, tstd, sign(corr(idx, t)))!
# Wait: with ONLY (tbar, tstd), note +gamma and -gamma can sometimes give similar tstd when r0=0;
# if we also match the sign of (t[:8].mean() - t[16:].mean()) — OR just include signed top-vs-bulk tilt or fit (tbar, tstd) with mild positive prior on gamma!
# Let's check BOTH: (A) fitting ONLY (tbar, tstd) with positive gamma>=0 vs (B) fitting (r0, gamma in R) to (tbar, tstd, c_idx_t)!
rng_grid = np.random.default_rng(777)
r0_grid = np.concatenate([
    np.linspace(-0.96, -0.40, 15),
    np.linspace(-0.36, 0.36, 25),
    np.linspace(0.40, 0.96, 15)
])
gam_grid = np.linspace(-1.1, 1.1, 35)

# Fast analytical moment approximation first to see how accurate it is, OR 55 x 35 x 3 = 5775 fast_stats (~1.8 sec!)
G_tb = np.zeros((len(r0_grid), len(gam_grid)))
G_ts = np.zeros((len(r0_grid), len(gam_grid)))
G_ab = np.zeros((len(r0_grid), len(gam_grid)))
G_ci = np.zeros((len(r0_grid), len(gam_grid)))

for i, r0 in enumerate(r0_grid):
    for j, gm in enumerate(gam_grid):
        sts = [fast_stats(*sample_signed_spike(r0, gm, rng=rng_grid)) for _ in range(4)]
        G_tb[i, j] = np.mean([x['tbar'] for x in sts])
        G_ts[i, j] = np.mean([x['tstd'] for x in sts])
        G_ab[i, j] = np.mean([x['amb'] for x in sts])
        G_ci[i, j] = np.mean([x['c_idx_t'] for x in sts])

rng_eval = np.random.default_rng(20261124)

for mode_name, use_sign in [("Signed-Spike 2p (fit tbar,tstd + tilt sign)", True), ("Pos-Spike 2p (gamma>=0, fit tbar,tstd only)", False)]:
    s_single, s_mean = [], []
    s3_single, s3_mean = [], []
    fitted_p = []
    for gt in gpt_raw:
        tb, ts, ab, ci = gt['tbar'], gt['tstd'], gt['amb'], gt['c_idx_t']
        if use_sign:
            # 2 continuous parameters (r0, gamma in R) per head!
            loss = (G_tb - tb)**2 + (G_ts - ts)**2 + 0.002 * (G_ci - ci)**2
        else:
            loss = (G_tb - tb)**2 + (G_ts - ts)**2
            loss[:, gam_grid < 0] = 1e9
        i, j = np.unravel_index(np.argmin(loss), loss.shape)
        r0_h, gm_h = r0_grid[i], gam_grid[j]
        fitted_p.append((r0_h, gm_h))
        draws = [fast_stats(*sample_signed_spike(r0_h, gm_h, rng=rng_eval)) for _ in range(6)]
        s_single.append(draws[0])
        s_mean.append({k: np.mean([d[k] for d in draws]) for k in draws[0]})
        
        if use_sign:
            # Also evaluate 3p (+nu for positive a-b heads)
            if ab > G_ab[i, j] + 0.012:
                best_nu, best_r0, best_l = 0.0, r0_h, 1e9
                for nu_try in [0.20, 0.35, 0.55, 0.75, 0.95]:
                    r0_try = np.clip(r0_h * (1.0 + 0.45 * nu_try**2), -0.97, 0.97)
                    sts3 = [fast_stats(*sample_signed_spike(r0_try, gm_h, nu=nu_try, rng=rng_grid)) for _ in range(3)]
                    l3 = (np.mean([x['tbar'] for x in sts3]) - tb)**2 + (np.mean([x['tstd'] for x in sts3]) - ts)**2 + 0.5*(np.mean([x['amb'] for x in sts3]) - ab)**2
                    if l3 < best_l:
                        best_l, best_nu, best_r0 = l3, nu_try, r0_try
                draws3 = [fast_stats(*sample_signed_spike(best_r0, gm_h, nu=best_nu, rng=rng_eval)) for _ in range(6)]
            else:
                draws3 = draws
            s3_single.append(draws3[0])
            s3_mean.append({k: np.mean([d[k] for d in draws3]) for k in draws3[0]})

    print(f"\n=== {mode_name} ===")
    d_g = fmt_dist(gpt_raw)
    d_s = fmt_dist(s_single)
    for k in STATS_KEYS:
        y_t = np.array([r[k] for r in gpt_raw])
        y_p = np.array([r[k] for r in s_mean])
        print(f"  {k:8s} | GPT-2: {d_g[k]:24s} | Pred: {d_s[k]:24s} | r={np.corrcoef(y_t,y_p)[0,1]:+.3f} MAE={np.mean(np.abs(y_t-y_p)):.3f}")
    tb = np.array([r['tbar'] for r in s_single]); ts = np.array([r['tstd'] for r in s_single])
    dg = np.array([r['diag'] for r in s_single]); of = np.array([r['offrms'] for r in s_single])
    e1 = np.array([r['err1'] for r in s_single]); pr = np.array([r['PR'] for r in s_single])
    mask05 = np.abs(tb) > 0.05
    med_ci = np.median([r['c_idx_t'] for r, m in zip(s_single, mask05) if m])
    print(f"  Extra: corr(|tbar|,diag)={np.corrcoef(np.abs(tb),dg)[0,1]:.3f}, corr(err1,tstd)={np.corrcoef(e1,ts)[0,1]:.3f}, corr(off,|tbar|)={np.corrcoef(of,np.abs(tb))[0,1]:.3f}, corr(PR,tstd)={np.corrcoef(pr,ts)[0,1]:.3f}, %(tbar>2std)={100*np.mean(np.abs(tb)>2*ts):.1f}%, med_corr(idx,t)={med_ci:+.3f}")

    if use_sign:
        print(f"\n=== Signed-Spike + Rotary Skew 3p (r0, gamma, nu) ===")
        d_s3 = fmt_dist(s3_single)
        for k in STATS_KEYS:
            y_t = np.array([r[k] for r in gpt_raw])
            y_p = np.array([r[k] for r in s3_mean])
            print(f"  {k:8s} | GPT-2: {d_g[k]:24s} | Pred: {d_s3[k]:24s} | r={np.corrcoef(y_t,y_p)[0,1]:+.3f} MAE={np.mean(np.abs(y_t-y_p)):.3f}")
        tb3 = np.array([r['tbar'] for r in s3_single]); ts3 = np.array([r['tstd'] for r in s3_single])
        dg3 = np.array([r['diag'] for r in s3_single]); of3 = np.array([r['offrms'] for r in s3_single])
        e13 = np.array([r['err1'] for r in s3_single]); pr3 = np.array([r['PR'] for r in s3_single])
        mask05_3 = np.abs(tb3) > 0.05
        med_ci3 = np.median([r['c_idx_t'] for r, m in zip(s3_single, mask05_3) if m])
        print(f"  Extra: corr(|tbar|,diag)={np.corrcoef(np.abs(tb3),dg3)[0,1]:.3f}, corr(err1,tstd)={np.corrcoef(e13,ts3)[0,1]:.3f}, corr(off,|tbar|)={np.corrcoef(of3,np.abs(tb3))[0,1]:.3f}, corr(PR,tstd)={np.corrcoef(pr3,ts3)[0,1]:.3f}, %(tbar>2std)={100*np.mean(np.abs(tb3)>2*ts3):.1f}%, med_corr(idx,t)={med_ci3:+.3f}")
