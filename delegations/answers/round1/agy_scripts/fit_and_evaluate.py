import sys
sys.path.insert(0, '.')
sys.path.insert(0, './ensemble_brief')
import numpy as np
import common

N, n, H = common.N, common.n, common.H
w_all, heads = common.load()

def fast_stats(Q, K):
    M = np.vstack([K, Q])
    R = np.linalg.qr(M.T, mode='r')
    Kh = R[:, :n].T
    Qh = R[:, n:].T
    Lh = Kh.T @ Qh
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
    pred_cd = wt @ (t * np.abs(t))
    idx1 = np.arange(1, n + 1, dtype=float)
    c_idx_t = np.corrcoef(idx1, t)[0, 1]
    return dict(
        diag=np.sum(t**2)/np.sum(W**2),
        tbar=tbar,
        tstd=tstd,
        offrms=offrms,
        err1=e1,
        amb=a-b,
        cmd=c-d,
        PR=np.sum(s**2)**2/np.sum(s**4),
        pred_cd=pred_cd,
        tmin=np.min(t),
        tmax=np.max(t),
        c_idx_t=c_idx_t,
    )

def make_gamma_sqrt(N, N_eff):
    if N_eff >= N - 1:
        return np.ones(N) / np.sqrt(N)
    lo, hi = 0.0, 20.0
    x = np.linspace(0, 1, N)
    for _ in range(50):
        mid = (lo + hi) / 2
        g = np.exp(-mid * x)
        pr = np.sum(g)**2 / np.sum(g**2)
        if pr > N_eff:
            lo = mid
        else:
            hi = mid
    g = np.exp(-((lo + hi) / 2) * x)
    g /= np.sum(g)
    return np.sqrt(g)

gam_430 = make_gamma_sqrt(N, 430.0)

# True GPT-2 raw stats
gpt_raw = [fast_stats(Q, K) for _, _, Q, K in heads]

# Analytical moment map for fast parameter inversion!
# Candidate 1: s_i ~ Gamma(kappa, 1/kappa), z_i ~ N(mu, tau^2), r_i = tanh(z_i).
# Note finite-N_eff adds variance ~(1 - r_i^2)^2 / N_eff to t_i^2!
# Let's include finite-N_eff baseline variance sigma_0^2(r) = (1 - r^2) / N_eff in the analytical moment solver,
# then refine with 1-step stochastic/deterministic check!

rng_fit = np.random.default_rng(2026)
Z_STD = rng_fit.standard_normal(4000)
U1_STD = rng_fit.standard_normal(4000)
U2_STD = rng_fit.standard_normal(4000)
N_EFF = 430.0

def fit_cand1_head(target_tbar, target_tstd):
    # r = tanh(mu + tau * Z), plus finite-N fluctuation ~ sqrt((1-r^2)/N_eff) * eps
    # Grid search over (mu, tau) in vectorized form -> instant!
    mus = np.linspace(-2.4, 2.4, 97)
    taus = np.linspace(0.0, 1.2, 49)
    best_loss = 1e9
    best_p = (0.0, 0.0)
    # Coarse then fine
    z_sub = Z_STD[:500]
    for mu in mus:
        r = np.tanh(mu + taus[:, None] * z_sub[None, :]) # (49, 500)
        m_r = np.mean(r, axis=1)
        # finite N variance contribution (approx (1 - r^2)^1.5 / N_eff; empirically null tstd = 0.036 at N=768, ~0.048 at N_eff=430)
        v_fin = np.mean((1.0 - r**2)**2, axis=1) / N_EFF
        s_r = np.sqrt(np.var(r, axis=1) + v_fin)
        loss = (m_r - target_tbar)**2 + (s_r - target_tstd)**2
        j = int(np.argmin(loss))
        if loss[j] < best_loss:
            best_loss = loss[j]
            best_p = (mu, taus[j])
    return best_p

def pred_moments_cand2(r0_arr, gam_arr, rho_f=0.12):
    # Vectorized prediction of (tbar, tstd) for Candidate 2!
    # Channel i has s_i = sqrt((1 + a_i^2)(1 + b_i^2)), r_i = (r0 + a_i b_i) / s_i
    # Weight w_i propto s_i^2 = (1 + a_i^2)(1 + b_i^2)!
    # Wait: in finite N_eff, channel mixing dampens extreme r_i slightly, let's check both asymptotic and simulated grid!
    pass

# Even better: build an ACTUAL simulated lookup table on a 2D grid of (r0, gamma) for Candidate 2 (and (mu, tau) for Candidate 1)!
# Because fast_stats takes 0.3 ms per matrix, a 25 x 20 grid x 6 trials = 3000 matrices = 0.9 seconds!!
# That accounts for ALL exact finite-(n, N) SVD / channel-mixing effects with ZERO approximation error!

def sample_cand1(mu, tau, kappa=16.0, gam=gam_430, rng=rng_fit):
    s = np.sqrt(rng.gamma(kappa, 1.0 / kappa, size=(n, 1)))
    r = np.tanh(rng.normal(mu, tau, size=(n, 1)))
    X = rng.standard_normal((n, N)) * gam[None, :]
    Y = rng.standard_normal((n, N)) * gam[None, :]
    return s * X, s * (r * X + np.sqrt(1.0 - r**2) * Y)

def sample_cand2(r0, gamma, rho_f=0.12, kappa_bulk=22.0, gam=gam_430, rng=rng_fit):
    # Wait: test BOTH kappa_bulk = inf (pure isotropic X0) and mild kappa_bulk!
    if kappa_bulk is None:
        s0 = 1.0
    else:
        s0 = np.sqrt(rng.gamma(kappa_bulk, 1.0 / kappa_bulk, size=(n, 1)))
    X0 = s0 * (rng.standard_normal((n, N)) * gam[None, :])
    Y0 = s0 * (rng.standard_normal((n, N)) * gam[None, :])
    F = rng.standard_normal((n, N)) * gam[None, :]
    u1 = rng.standard_normal((n, 1))
    u2 = rng.standard_normal((n, 1))
    alpha = gamma * u1
    beta = gamma * (rho_f * u1 + np.sqrt(1.0 - rho_f**2) * u2)
    Q = X0 + alpha * F
    K = (r0 * X0 + np.sqrt(1.0 - r0**2) * Y0) + beta * F
    return Q, K

def sample_cand3(r0, gamma, nu, rho_f=0.12, kappa_bulk=None, gam=gam_430, rng=rng_fit):
    Q, K = sample_cand2(r0, gamma, rho_f=rho_f, kappa_bulk=kappa_bulk, gam=gam, rng=rng)
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

print("Building simulation grid for Candidate 1 (25 x 18 x 5)...")
c1_mus = np.linspace(-2.0, 2.0, 25)
c1_taus = np.linspace(0.0, 0.85, 18)
c1_grid_tbar = np.zeros((len(c1_mus), len(c1_taus)))
c1_grid_tstd = np.zeros((len(c1_mus), len(c1_taus)))
for i, mu in enumerate(c1_mus):
    for j, tau in enumerate(c1_taus):
        sts = [fast_stats(*sample_cand1(mu, tau)) for _ in range(5)]
        c1_grid_tbar[i, j] = np.mean([x['tbar'] for x in sts])
        c1_grid_tstd[i, j] = np.mean([x['tstd'] for x in sts])

print("Building simulation grid for Candidate 2 (pure iso bulk kappa_bulk=None, 27 x 18 x 5)...")
c2_r0s = np.concatenate([[-0.97, -0.92, -0.85], np.linspace(-0.75, 0.75, 21), [0.85, 0.92, 0.97]])
c2_gams = np.linspace(0.0, 1.5, 19)
c2_grid_tbar = np.zeros((len(c2_r0s), len(c2_gams)))
c2_grid_tstd = np.zeros((len(c2_r0s), len(c2_gams)))
c2_grid_amb = np.zeros((len(c2_r0s), len(c2_gams)))
for i, r0 in enumerate(c2_r0s):
    for j, gm in enumerate(c2_gams):
        sts = [fast_stats(*sample_cand2(r0, gm, rho_f=0.12, kappa_bulk=None)) for _ in range(5)]
        c2_grid_tbar[i, j] = np.mean([x['tbar'] for x in sts])
        c2_grid_tstd[i, j] = np.mean([x['tstd'] for x in sts])
        c2_grid_amb[i, j] = np.mean([x['amb'] for x in sts])

# Fit each of the 144 heads and evaluate on FRESH random draws (separate RNG seed!)
rng_eval = np.random.default_rng(9999)
N_MC = 8  # average per-head predictions AND keep 1 single realization per head to mimic a 144-head synthetic model!

c1_single, c1_mean = [], []
c2_single, c2_mean = [], []
c3_single, c3_mean = [], []
c1_params, c2_params, c3_params = [], [], []

for h_idx, gt in enumerate(gpt_raw):
    tb, ts, ab = gt['tbar'], gt['tstd'], gt['amb']
    
    # Fit C1 on (tbar, tstd)
    loss1 = (c1_grid_tbar - tb)**2 + (c1_grid_tstd - ts)**2
    i1, j1 = np.unravel_index(np.argmin(loss1), loss1.shape)
    mu_hat, tau_hat = c1_mus[i1], c1_taus[j1]
    c1_params.append((mu_hat, tau_hat))
    draws1 = [fast_stats(*sample_cand1(mu_hat, tau_hat, rng=rng_eval)) for _ in range(N_MC)]
    c1_single.append(draws1[0])
    c1_mean.append({k: np.mean([d[k] for d in draws1]) for k in draws1[0]})
    
    # Fit C2 on (tbar, tstd) ONLY!
    loss2 = (c2_grid_tbar - tb)**2 + (c2_grid_tstd - ts)**2
    i2, j2 = np.unravel_index(np.argmin(loss2), loss2.shape)
    r0_hat, gm_hat = c2_r0s[i2], c2_gams[j2]
    c2_params.append((r0_hat, gm_hat))
    draws2 = [fast_stats(*sample_cand2(r0_hat, gm_hat, rho_f=0.12, kappa_bulk=None, rng=rng_eval)) for _ in range(N_MC)]
    c2_single.append(draws2[0])
    c2_mean.append({k: np.mean([d[k] for d in draws2]) for k in draws2[0]})
    
    # Fit C3: if head has positive excess (a - b) > c2_pred + 0.015, optimize nu > 0 over small 1D line search
    pred_ab2 = c2_grid_amb[i2, j2]
    if ab > pred_ab2 + 0.015:
        best_nu = 0.0
        best_l3 = 1e9
        best_r03, best_gm3 = r0_hat, gm_hat
        for nu_try in [0.25, 0.45, 0.65, 0.85, 1.05]:
            # Note nu > 0 slightly shrinks tbar toward 0, so allow slight r0 adjustment
            scale = 1.0 + 0.5 * nu_try**2
            r0_try = np.clip(r0_hat * scale, -0.97, 0.97)
            sts3 = [fast_stats(*sample_cand3(r0_try, gm_hat, nu_try, rho_f=0.12, kappa_bulk=None, rng=rng_fit)) for _ in range(3)]
            m_tb = np.mean([x['tbar'] for x in sts3])
            m_ts = np.mean([x['tstd'] for x in sts3])
            m_ab = np.mean([x['amb'] for x in sts3])
            l3 = (m_tb - tb)**2 + (m_ts - ts)**2 + 0.5 * (m_ab - ab)**2
            if l3 < best_l3:
                best_l3 = l3
                best_nu, best_r03, best_gm3 = nu_try, r0_try, gm_hat
        c3_params.append((best_r03, best_gm3, best_nu))
        draws3 = [fast_stats(*sample_cand3(best_r03, best_gm3, best_nu, rho_f=0.12, kappa_bulk=None, rng=rng_eval)) for _ in range(N_MC)]
    else:
        c3_params.append((r0_hat, gm_hat, 0.0))
        draws3 = draws2
    c3_single.append(draws3[0])
    c3_mean.append({k: np.mean([d[k] for d in draws3]) for k in draws3[0]})

STATS_KEYS = ['diag', 'tbar', 'tstd', 'offrms', 'err1', 'amb', 'cmd', 'PR']

def fmt_dist(rows):
    out = {}
    for k in STATS_KEYS:
        v = np.array([r[k] for r in rows])
        out[k] = f"{np.median(v):+.3f} [{np.percentile(v,10):+.3f}, {np.percentile(v,90):+.3f}]"
    return out

print("\n=== DISTRIBUTION COMPARISON ACROSS 144 HEADS (1 single synthetic draw per head vs GPT-2) ===")
d_gpt = fmt_dist(gpt_raw)
d_c1 = fmt_dist(c1_single)
d_c2 = fmt_dist(c2_single)
d_c3 = fmt_dist(c3_single)

print(f"{'stat':8s} | {'GPT-2 trained':24s} | {'Cand 1 (2p: mu,tau)':24s} | {'Cand 2 (2p: r0,gamma)':24s} | {'Cand 3 (3p: +skew nu)':24s}")
print("-" * 116)
for k in STATS_KEYS:
    print(f"{k:8s} | {d_gpt[k]:24s} | {d_c1[k]:24s} | {d_c2[k]:24s} | {d_c3[k]:24s}")

print("\n=== EXTRA OBSERVATIONS FROM BRIEF.MD ===")
for name, rows in [("GPT-2", gpt_raw), ("Cand 1", c1_single), ("Cand 2", c2_single), ("Cand 3", c3_single)]:
    tb = np.array([r['tbar'] for r in rows])
    ts = np.array([r['tstd'] for r in rows])
    dg = np.array([r['diag'] for r in rows])
    of = np.array([r['offrms'] for r in rows])
    e1 = np.array([r['err1'] for r in rows])
    cd = np.array([r['cmd'] for r in rows])
    pcd = np.array([r['pred_cd'] for r in rows])
    pr = np.array([r['PR'] for r in rows])
    frac_strong = np.mean(np.abs(tb) > 2 * ts)
    mask05 = np.abs(tb) > 0.05
    med_c_idx = np.median([r['c_idx_t'] for r, m in zip(rows, mask05) if m])
    print(f"{name:7s}: corr(c-d,pred)={np.corrcoef(cd,pcd)[0,1]:.4f} | corr(|tbar|,diag)={np.corrcoef(np.abs(tb),dg)[0,1]:.3f} | corr(err1,tstd)={np.corrcoef(e1,ts)[0,1]:.3f} | corr(off,|tbar|)={np.corrcoef(of,np.abs(tb))[0,1]:.3f} | corr(PR,tstd)={np.corrcoef(pr,ts)[0,1]:.3f} | %(tbar>2std)={100*frac_strong:.1f}% | med_corr(idx,t)={med_c_idx:+.3f}")

print("\n=== HEAD-BY-HEAD PREDICTION CORRELATION & MAE (MC mean vs GPT-2 across 144 heads) ===")
for k in STATS_KEYS:
    y_true = np.array([r[k] for r in gpt_raw])
    out_str = f"{k:8s}: "
    for nm, pred_rows in [("C1", c1_mean), ("C2", c2_mean), ("C3", c3_mean)]:
        y_pred = np.array([r[k] for r in pred_rows])
        corr = np.corrcoef(y_true, y_pred)[0, 1]
        mae = np.mean(np.abs(y_true - y_pred))
        out_str += f"{nm} r={corr:+.3f} (MAE={mae:.3f})  |  "
    print(out_str)
