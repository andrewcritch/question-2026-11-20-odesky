import sys
sys.path.insert(0, './ensemble_brief')
import numpy as np
import common

N, n, H = common.N, common.n, common.H

def fast_stats(Q, K):
    """Exact spectral and W=U^T V statistics via thin QR reduction to 2n x 2n."""
    M = np.vstack([K, Q])
    R = np.linalg.qr(M.T, mode='r')
    Kh = R[:, :n].T
    Qh = R[:, n:].T
    Lh = Kh.T @ Qh
    S = (Lh + Lh.T) / 2.0
    T = (Lh - Lh.T) / 2.0
    ev = np.linalg.eigvalsh(S)
    lp = np.sort(ev[ev > 1e-14])[::-1][:n]
    lm = np.sort(-ev[ev < -1e-14])[::-1][:n]
    k = min(len(lp), len(lm))
    lp, lm = lp[:k], lm[:k]
    sv = np.linalg.svd(T, compute_uv=False)[:2*n:2][:k]
    nL = np.sum(Lh * Lh)
    a = np.sum(T * T) / nL
    b = 2.0 * (lp @ lm) / nL
    dif = lp - lm
    c = np.sum(np.maximum(dif, 0.0)**2) / nL
    d = np.sum(np.maximum(-dif, 0.0)**2) / nL
    e1 = np.linalg.norm(sv - np.sqrt(lp * lm)) / np.linalg.norm(sv)
    U, s, Vt = np.linalg.svd(Lh)
    U, s, V = U[:, :n], s[:n], Vt[:n].T
    W = U.T @ V
    t = np.diag(W)
    wt = s**2 / np.sum(s**2)
    tbar = wt @ t
    tstd = np.sqrt(wt @ (t - tbar)**2)
    off = W - np.diag(t)
    offrms = np.sqrt(np.sum(off**2) / (n * n - n))
    pred_cd = wt @ (t * np.abs(t))
    idx1 = np.arange(1, n + 1, dtype=float)
    c_idx_t = np.corrcoef(idx1, t)[0, 1]
    return dict(
        a=a, b=b, c=c, d=d,
        diag=np.sum(t**2) / np.sum(W**2),
        tbar=tbar,
        tmean_unw=float(np.mean(t)),
        tstd=tstd,
        offrms=offrms,
        err1=e1,
        amb=a - b,
        cmd=c - d,
        PR=np.sum(s**2)**2 / np.sum(s**4),
        pred_cd=pred_cd,
        tmin=float(np.min(t)),
        tmax=float(np.max(t)),
        c_idx_t=c_idx_t,
    )

def make_gamma_sqrt(N_dim, N_eff):
    if N_eff >= N_dim - 1:
        return np.ones(N_dim) / np.sqrt(N_dim)
    lo, hi = 0.0, 20.0
    x = np.linspace(0.0, 1.0, N_dim)
    for _ in range(50):
        mid = 0.5 * (lo + hi)
        g = np.exp(-mid * x)
        pr = np.sum(g)**2 / np.sum(g**2)
        if pr > N_eff:
            lo = mid
        else:
            hi = mid
    g = np.exp(-0.5 * (lo + hi) * x)
    g /= np.sum(g)
    return np.sqrt(g)

def sample_cand1(mu, tau, kappa=20.0, gam_sqrt=None, rng=None):
    """Candidate 1: Heterogeneously Correlated Channel Ensemble (2 per-head params: mu, tau)."""
    if gam_sqrt is None:
        gam_sqrt = np.ones(N) / np.sqrt(N)
    s = np.sqrt(rng.gamma(kappa, 1.0 / kappa, size=(n, 1)))
    r = np.tanh(rng.normal(mu, tau, size=(n, 1)))
    X = rng.standard_normal((n, N)) * gam_sqrt[None, :]
    Y = rng.standard_normal((n, N)) * gam_sqrt[None, :]
    Q = s * X
    K = s * (r * X + np.sqrt(1.0 - r**2) * Y)
    return Q, K

def sample_cand2(r0, gamma, gam_sqrt=None, rng=None):
    """Candidate 2: Signed-Spike Correlated Ensemble (2 per-head params: r0 in (-1,1), gamma in R)."""
    if gam_sqrt is None:
        gam_sqrt = np.ones(N) / np.sqrt(N)
    X0 = rng.standard_normal((n, N)) * gam_sqrt[None, :]
    Y0 = rng.standard_normal((n, N)) * gam_sqrt[None, :]
    F = rng.standard_normal((n, N)) * gam_sqrt[None, :]
    g = rng.standard_normal((n, 1))
    Q = X0 + np.abs(gamma) * g * F
    K = (r0 * X0 + np.sqrt(1.0 - r0**2) * Y0) + gamma * g * F
    return Q, K

def sample_cand3(r0, gamma, nu, gam_sqrt=None, rng=None):
    """Candidate 3: Symplectic/Rotary-Augmented Signed-Spike Ensemble (3 per-head params: r0, gamma, nu>=0)."""
    Q, K = sample_cand2(r0, gamma, gam_sqrt=gam_sqrt, rng=rng)
    if nu > 0.0:
        F_rot = rng.standard_normal((n, N)) * gam_sqrt[None, :]
        w_half = nu * rng.standard_normal(n // 2)
        w_pair = np.repeat(w_half, 2)[:, None]
        JF_rot = np.empty_like(F_rot)
        JF_rot[0::2] = F_rot[1::2]
        JF_rot[1::2] = -F_rot[0::2]
        Q = Q + w_pair * F_rot
        K = K + w_pair * JF_rot
    return Q, K

if __name__ == '__main__':
    w_all, heads = common.load()
    pre = '' if 'h.0.attn.c_attn.weight' in w_all else 'transformer.'
    gam_430 = make_gamma_sqrt(N, 430.0)

    gpt_raw = []
    gpt_ln = []
    for l, h, Q, K in heads:
        gpt_raw.append(fast_stats(Q, K))
        g_ln = w_all[f'{pre}h.{l}.ln_1.weight'].astype(np.float64)
        Qg = Q * g_ln[None, :]; Kg = K * g_ln[None, :]
        Qg -= Qg.mean(axis=1, keepdims=True); Kg -= Kg.mean(axis=1, keepdims=True)
        gpt_ln.append(fast_stats(Qg, Kg))

    # Fast analytical pre-grids (instantaneous, 0.02s!) + small simulated calibration
    rng_grid = np.random.default_rng(101)
    Z_MC = rng_grid.standard_normal(2000)
    G2_MC = Z_MC**2

    # Cand 1 analytical grid (101 x 61)
    c1_mus = np.linspace(-2.0, 2.0, 101)
    c1_taus = np.linspace(0.0, 0.90, 61)
    # Account for finite-N_eff channel-mixing damping of tau (~0.62 factor on observed tstd above floor 0.046)
    C1_tb = np.zeros((len(c1_mus), len(c1_taus)))
    C1_ts = np.zeros((len(c1_mus), len(c1_taus)))
    for i, mu in enumerate(c1_mus):
        r = np.tanh(mu + c1_taus[:, None] * Z_MC[None, :])
        C1_tb[i] = np.mean(r, axis=1)
        v_fin = np.mean((1.0 - r**2)**2, axis=1) / 430.0
        C1_ts[i] = np.sqrt(0.45 * np.var(r, axis=1) + v_fin)

    # Cand 2 compact simulated grid: 33 x 25 x 2 = 1650 fast_stats (~0.8s!)
    r0_grid = np.concatenate([np.linspace(-0.96, -0.40, 9), np.linspace(-0.35, 0.35, 15), np.linspace(0.40, 0.96, 9)])
    gam_grid = np.linspace(-1.50, 1.50, 25)
    C2_tb = np.zeros((len(r0_grid), len(gam_grid)))
    C2_tm = np.zeros((len(r0_grid), len(gam_grid)))
    C2_ts = np.zeros((len(r0_grid), len(gam_grid)))
    C2_ab = np.zeros((len(r0_grid), len(gam_grid)))
    for i, r0 in enumerate(r0_grid):
        for j, gm in enumerate(gam_grid):
            sts = [fast_stats(*sample_cand2(r0, gm, gam_sqrt=gam_430, rng=rng_grid)) for _ in range(2)]
            C2_tb[i, j] = 0.5 * (sts[0]['tbar'] + sts[1]['tbar'])
            C2_tm[i, j] = 0.5 * (sts[0]['tmean_unw'] + sts[1]['tmean_unw'])
            C2_ts[i, j] = 0.5 * (sts[0]['tstd'] + sts[1]['tstd'])
            C2_ab[i, j] = 0.5 * (sts[0]['amb'] + sts[1]['amb'])

    rng_eval = np.random.default_rng(20261125)
    N_MC = 5
    c1_one, c1_avg, c1_fit = [], [], []
    c2_one, c2_avg, c2_fit = [], [], []
    c3_one, c3_avg, c3_fit = [], [], []

    for h_idx, gt in enumerate(gpt_raw):
        tb, tm, ts, ab = gt['tbar'], gt['tmean_unw'], gt['tstd'], gt['amb']

        # Cand 1 fit
        l1 = (C1_tb - tb)**2 + (C1_ts - ts)**2
        i1, j1 = np.unravel_index(np.argmin(l1), l1.shape)
        mu_h, tau_h = float(c1_mus[i1]), float(c1_taus[j1])
        c1_fit.append((mu_h, tau_h))
        d1 = [fast_stats(*sample_cand1(mu_h, tau_h, kappa=20.0, gam_sqrt=gam_430, rng=rng_eval)) for _ in range(N_MC)]
        c1_one.append(d1[0])
        c1_avg.append({k: float(np.mean([x[k] for x in d1])) for k in d1[0]})

        # Cand 2 fit (only t_i moments!)
        l2 = (C2_tb - tb)**2 + 0.5 * (C2_tm - tm)**2 + (C2_ts - ts)**2
        i2, j2 = np.unravel_index(np.argmin(l2), l2.shape)
        r0_h, gm_h = float(r0_grid[i2]), float(gam_grid[j2])
        c2_fit.append((r0_h, gm_h))
        d2 = [fast_stats(*sample_cand2(r0_h, gm_h, gam_sqrt=gam_430, rng=rng_eval)) for _ in range(N_MC)]
        c2_one.append(d2[0])
        c2_avg.append({k: float(np.mean([x[k] for x in d2])) for k in d2[0]})

        # Cand 3 fit
        if ab > C2_ab[i2, j2] + 0.012:
            best_l3, best_nu, best_r0 = 1e9, 0.0, r0_h
            for nu_try in [0.22, 0.38, 0.58, 0.80, 1.05]:
                r0_try = float(np.clip(r0_h * (1.0 + 0.45 * nu_try**2), -0.97, 0.97))
                st_try = fast_stats(*sample_cand3(r0_try, gm_h, nu_try, gam_sqrt=gam_430, rng=rng_grid))
                l3 = (st_try['tbar'] - tb)**2 + (st_try['tstd'] - ts)**2 + 0.6 * (st_try['amb'] - ab)**2
                if l3 < best_l3:
                    best_l3, best_nu, best_r0 = l3, nu_try, r0_try
            c3_fit.append((best_r0, gm_h, best_nu))
            d3 = [fast_stats(*sample_cand3(best_r0, gm_h, best_nu, gam_sqrt=gam_430, rng=rng_eval)) for _ in range(N_MC)]
        else:
            c3_fit.append((r0_h, gm_h, 0.0))
            d3 = d2
        c3_one.append(d3[0])
        c3_avg.append({k: float(np.mean([x[k] for x in d3])) for k in d3[0]})

    r0_arr = np.array([p[0] for p in c3_fit])
    gm_arr = np.array([p[1] for p in c3_fit])
    nu_arr = np.array([p[2] for p in c3_fit])
    print(f"=== Fitted Parameters Summary (144 heads) ===")
    print(f"  r0:    med={np.median(r0_arr):+.3f}, [p10,p90]=[{np.percentile(r0_arr,10):+.3f}, {np.percentile(r0_arr,90):+.3f}]")
    print(f"  gamma: med={np.median(gm_arr):+.3f}, [p10,p90]=[{np.percentile(gm_arr,10):+.3f}, {np.percentile(gm_arr,90):+.3f}], %(gamma>0)={100*np.mean(gm_arr>0):.1f}%")
    print(f"  nu>0:  {np.sum(nu_arr>0)}/144 heads ({100*np.mean(nu_arr>0):.1f}%), mean active nu={np.mean(nu_arr[nu_arr>0]):.3f}")

    # Population draw (0 per-head parameters!)
    rng_pop = np.random.default_rng(31415)
    pop_c2, pop_c3 = [], []
    for _ in range(144):
        r0_p = float(np.tanh(rng_pop.laplace(-0.04, 0.28)))
        gm_p = float(rng_pop.normal(0.12, 0.55))
        nu_p = float(abs(rng_pop.normal(0.0, 0.42))) if rng_pop.random() < 0.28 else 0.0
        pop_c2.append(fast_stats(*sample_cand2(r0_p, gm_p, gam_sqrt=gam_430, rng=rng_pop)))
        pop_c3.append(fast_stats(*sample_cand3(r0_p, gm_p, nu_p, gam_sqrt=gam_430, rng=rng_pop)))

    KEYS = ['diag', 'tbar', 'tstd', 'offrms', 'err1', 'amb', 'cmd', 'PR']
    def fdist(rows):
        return {k: f"{np.median([r[k] for r in rows]):+.3f} [{np.percentile([r[k] for r in rows],10):+.3f}, {np.percentile([r[k] for r in rows],90):+.3f}]" for k in KEYS}

    dg, dc1, dc2, dc3, dp2, dp3 = map(fdist, [gpt_raw, c1_one, c2_one, c3_one, pop_c2, pop_c3])
    print("\n=== TABLE 1: PER-HEAD FITTED ENSEMBLES (1 synthetic draw per head) ===")
    print(f"{'Stat':8s} | {'GPT-2 Raw':24s} | {'Cand 1 (2p)':24s} | {'Cand 2 (2p)':24s} | {'Cand 3 (3p)':24s}")
    print("-" * 116)
    for k in KEYS:
        print(f"{k:8s} | {dg[k]:24s} | {dc1[k]:24s} | {dc2[k]:24s} | {dc3[k]:24s}")

    print("\n=== TABLE 2: UNCONDITIONAL POPULATION DRAW (0 per-head params, 144 heads) ===")
    for k in KEYS:
        print(f"{k:8s} | GPT-2: {dg[k]:24s} | Pop C2: {dp2[k]:24s} | Pop C3: {dp3[k]:24s}")

    print("\n=== TABLE 3: HEAD-BY-HEAD CORRELATION & MAE (MC mean vs GPT-2) ===")
    for k in KEYS:
        yt = np.array([r[k] for r in gpt_raw])
        line = f"  {k:8s} | "
        for nm, pr_rows in [("Cand 1", c1_avg), ("Cand 2", c2_avg), ("Cand 3", c3_avg)]:
            yp = np.array([r[k] for r in pr_rows])
            line += f"{nm}: r={np.corrcoef(yt, yp)[0,1]:+.3f}, MAE={np.mean(np.abs(yt - yp)):.3f} | "
        print(line)

    print("\n=== TABLE 4: SECONDARY OBSERVATIONS ===")
    for nm, rows in [("GPT-2", gpt_raw), ("Cand 1", c1_one), ("Cand 2", c2_one), ("Cand 3", c3_one), ("Pop C3", pop_c3)]:
        tb = np.array([r['tbar'] for r in rows]); ts = np.array([r['tstd'] for r in rows])
        d_arr = np.array([r['diag'] for r in rows]); of = np.array([r['offrms'] for r in rows])
        e1 = np.array([r['err1'] for r in rows]); cd = np.array([r['cmd'] for r in rows])
        pcd = np.array([r['pred_cd'] for r in rows]); pr = np.array([r['PR'] for r in rows])
        m05 = np.abs(tb) > 0.05
        ci = np.median([r['c_idx_t'] for r, m in zip(rows, m05) if m])
        print(f"  {nm:7s} | corr(c-d,pred)={np.corrcoef(cd,pcd)[0,1]:.4f} | corr(|tbar|,diag)={np.corrcoef(np.abs(tb),d_arr)[0,1]:.3f} | corr(err1,tstd)={np.corrcoef(e1,ts)[0,1]:.3f} | corr(off,|tbar|)={np.corrcoef(of,np.abs(tb))[0,1]:.3f} | corr(PR,tstd)={np.corrcoef(pr,ts)[0,1]:.3f} | %(>2std)={100*np.mean(np.abs(tb)>2*ts):.1f}% | corr(idx,t)={ci:+.3f}")

    print("\n=== CASE STUDIES ===")
    for (l, h) in [(0, 5), (5, 9), (0, 3), (1, 1), (0, 0)]:
        idx = l * 12 + h
        gt = gpt_raw[idx]
        p2 = c2_fit[idx]; s2 = c2_one[idx]
        p3 = c3_fit[idx]; s3 = c3_one[idx]
        print(f"  L{l}H{h} GPT-2 : tbar={gt['tbar']:+.3f}, tstd={gt['tstd']:.3f}, t in [{gt['tmin']:+.2f},{gt['tmax']:+.2f}], diag={gt['diag']:.3f}, off={gt['offrms']:.3f}, err1={gt['err1']:.3f}, a-b={gt['amb']:+.3f}, PR={gt['PR']:.1f}")
        print(f"    Cand2 (r0={p2[0]:+.2f}, g={p2[1]:+.2f})       : tbar={s2['tbar']:+.3f}, tstd={s2['tstd']:.3f}, t in [{s2['tmin']:+.2f},{s2['tmax']:+.2f}], diag={s2['diag']:.3f}, off={s2['offrms']:.3f}, err1={s2['err1']:.3f}, a-b={s2['amb']:+.3f}, PR={s2['PR']:.1f}")
        if p3[2] > 0:
            print(f"    Cand3 (r0={p3[0]:+.2f}, g={p3[1]:+.2f}, nu={p3[2]:.2f}): tbar={s3['tbar']:+.3f}, tstd={s3['tstd']:.3f}, t in [{s3['tmin']:+.2f},{s3['tmax']:+.2f}], diag={s3['diag']:.3f}, off={s3['offrms']:.3f}, err1={s3['err1']:.3f}, a-b={s3['amb']:+.3f}, PR={s3['PR']:.1f}")
