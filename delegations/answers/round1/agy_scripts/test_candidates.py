import sys
sys.path.insert(0, '.')
sys.path.insert(0, './ensemble_brief')
import numpy as np
import common
from explore_deep import fast_stats

rng = np.random.default_rng(42)
N, n = 768, 64

# Helper: anisotropic residual covariance Gamma with PR = N_eff
def make_gamma_sqrt(N, N_eff):
    # Power-law / exponential decay calibrated to PR = N_eff
    if N_eff >= N - 1:
        return np.ones(N) / np.sqrt(N)
    # Solve for exponential decay exp(-alpha * j / N) so (sum g)^2 / sum g^2 = N_eff
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
gam_768 = np.ones(N) / np.sqrt(N)

def run_trials(name, gen_fn, trials=30):
    rows = [fast_stats(*gen_fn()) for _ in range(trials)]
    def m(k):
        v = np.array([r[k] for r in rows])
        return f"{np.median(v):+.3f}"
    print(f"{name:54s} | diag={m('diag')} tbar={m('tbar')} tstd={m('tstd')} off={m('offrms')} err1={m('err1')} a-b={m('amb')} c-d={m('cmd')} PR={m('PR')}")

print("=== Testing M1: Q = Z1 + B^T Z2, K = Z2 + B Z1 ===")
for mu, tau_s, tau_a in [(0.0, 0.3, 0.0), (-0.15, 0.35, 0.0), (0.6, 0.25, 0.0), (0.0, 0.3, 0.2)]:
    def gen(mu=mu, ts=tau_s, ta=tau_a):
        Z1 = rng.standard_normal((n, N)) * gam_430[None, :]
        Z2 = rng.standard_normal((n, N)) * gam_430[None, :]
        X = rng.standard_normal((n, n)) / np.sqrt(n)
        Hs = (X + X.T) / np.sqrt(2)
        Ha = (X - X.T) / np.sqrt(2)
        B = mu * np.eye(n) + ts * Hs + ta * Ha
        return Z1 + B.T @ Z2, Z2 + B @ Z1
    run_trials(f"M1 (iso Q): mu={mu:+.2f}, ts={tau_s:.2f}, ta={tau_a:.2f}", gen)

print("\n=== Testing M1b: Same with Gamma(shape=3) channel weights S0^{1/2} breaking +/-beta degeneracy ===")
for mu, tau_s, tau_a in [(0.0, 0.3, 0.0), (-0.15, 0.35, 0.0), (0.6, 0.25, 0.0), (0.2, 0.1, 0.35)]:
    def gen(mu=mu, ts=tau_s, ta=tau_a):
        s0 = np.sqrt(rng.gamma(3.0, 1.0/3.0, size=(n, 1)))
        Z1 = rng.standard_normal((n, N)) * gam_430[None, :]
        Z2 = rng.standard_normal((n, N)) * gam_430[None, :]
        X = rng.standard_normal((n, n)) / np.sqrt(n)
        Hs = (X + X.T) / np.sqrt(2)
        Ha = (X - X.T) / np.sqrt(2)
        B = mu * np.eye(n) + ts * Hs + ta * Ha
        return s0 * (Z1 + B.T @ Z2), s0 * (Z2 + B @ Z1)
    run_trials(f"M1b (Gamma s0): mu={mu:+.2f}, ts={tau_s:.2f}, ta={tau_a:.2f}", gen)

print("\n=== Testing M2: Channel-Factored Random-Correlation (r_i = tanh(z_i), z_i ~ N(mu, tau^2), s_i ~ Gamma(kappa)) ===")
for mu, tau, kap in [(0.0, 0.15, 6.0), (-0.12, 0.10, 8.0), (-0.30, 0.35, 4.0), (1.5, 0.35, 8.0), (0.0, 0.35, 3.0)]:
    def gen(mu=mu, tau=tau, kap=kap):
        s = np.sqrt(rng.gamma(kap, 1.0/kap, size=(n, 1)))
        r = np.tanh(rng.normal(mu, tau, size=(n, 1)))
        X = rng.standard_normal((n, N)) * gam_430[None, :]
        Y = rng.standard_normal((n, N)) * gam_430[None, :]
        Q = s * X
        K = s * (r * X + np.sqrt(1 - r**2) * Y)
        return Q, K
    run_trials(f"M2: mu={mu:+.2f}, tau={tau:.2f}, kap={kap:.1f}", gen)

print("\n=== Testing M3: Spiked Correlated Gaussian (bulk r0 + rank-k Ginibre/GOE feature spike) ===")
for r0, k, g_str, sym_bias in [(-0.15, 4, 1.5, 0.5), (-0.55, 4, 2.2, 0.6), (0.92, 2, 1.8, -0.1), (0.40, 2, 3.0, -0.8)]:
    # sym_bias in [-1, 1]: +1 = pure GOE symmetric spike, -1 = pure skew spike, 0 = Ginibre
    def gen(r0=r0, k=k, g_str=g_str, sb=sym_bias):
        Z1 = rng.standard_normal((n, N)) * gam_430[None, :]
        Z2 = rng.standard_normal((n, N)) * gam_430[None, :]
        Qb = Z1
        Kb = r0 * Z1 + np.sqrt(1 - r0**2) * Z2
        # Low-rank feature spike in R^N: k shared feature vectors F in R^{k x N}
        # Q adds U_q F, K adds U_k M_k F where M_k is k x k coupling!
        F = rng.standard_normal((k, N)) * gam_430[None, :]
        # Embed in top k head channels (equivalent up to O_n gauge)
        X = rng.standard_normal((k, k)) / np.sqrt(k)
        Hs = (X + X.T) / np.sqrt(2)
        Ha = (X - X.T) / np.sqrt(2)
        ws = np.sqrt(max(0.0, (1 + sb)/2))
        wa = np.sqrt(max(0.0, (1 - sb)/2))
        Mk = ws * Hs + wa * Ha
        dQ = np.zeros((n, N)); dK = np.zeros((n, N))
        dQ[:k] = g_str * F
        dK[:k] = g_str * (Mk @ F)
        return Qb + dQ, Kb + dK
    run_trials(f"M3: r0={r0:+.2f}, k={k}, g={g_str:.1f}, sb={sym_bias:+.1f}", gen)
