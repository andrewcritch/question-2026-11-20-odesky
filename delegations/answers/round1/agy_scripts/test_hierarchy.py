import sys
sys.path.insert(0, '.')
sys.path.insert(0, './ensemble_brief')
import numpy as np
import common
from explore_deep import fast_stats
from test_candidates import make_gamma_sqrt

rng = np.random.default_rng(123)
N, n = 768, 64
gam_430 = make_gamma_sqrt(N, 430.0)

def sample_cand1(mu, tau, kappa=14.0, gam=gam_430, rng=rng):
    s = np.sqrt(rng.gamma(kappa, 1.0 / kappa, size=(n, 1)))
    r = np.tanh(rng.normal(mu, tau, size=(n, 1)))
    X = rng.standard_normal((n, N)) * gam[None, :]
    Y = rng.standard_normal((n, N)) * gam[None, :]
    Q = s * X
    K = s * (r * X + np.sqrt(1.0 - r**2) * Y)
    return Q, K

def sample_cand2(r0, gamma, rho_f=0.25, gam=gam_430, rng=rng):
    X0 = rng.standard_normal((n, N)) * gam[None, :]
    Y0 = rng.standard_normal((n, N)) * gam[None, :]
    F = rng.standard_normal((n, N)) * gam[None, :]
    u1 = rng.standard_normal((n, 1))
    u2 = rng.standard_normal((n, 1))
    alpha = gamma * u1
    beta = gamma * (rho_f * u1 + np.sqrt(1.0 - rho_f**2) * u2)
    Q = X0 + alpha * F
    K = (r0 * X0 + np.sqrt(1.0 - r0**2) * Y0) + beta * F
    return Q, K

def sample_cand3(r0, gamma, nu, rho_f=0.25, gam=gam_430, rng=rng):
    # Each of n/2 pairs can carry symmetric channel loadings (alpha, beta) PLUS a 2x2 skew-rotation coupling!
    # Specifically, on pair j, adding a rotary feature pair F_rot: Q adds sqrt(|w_j|) F_rot, K adds sqrt(|w_j|) J F_rot
    # Wait: even simpler! Let J = kron(I_{n/2}, [[0, 1], [-1, 0]]).
    # If Q = X0 + diag(alpha) F + diag(omega_pair) F_rot, K = Kb + diag(beta) F + diag(omega_pair) (J F_rot),
    # where omega_pair repeats w_j ~ N(0, nu^2) on (2j, 2j+1)!
    # Notice: when nu=0, F_rot disappears and this is IDENTICAL to Candidate 2!
    # And no matrix square roots needed: w_j in R, Q gets w_j F_rot, K gets w_j J F_rot -> L gets w_j^2 F_rot^T J^T F_rot (purely skew-symmetric of equal singular values w_j^2)!
    X0 = rng.standard_normal((n, N)) * gam[None, :]
    Y0 = rng.standard_normal((n, N)) * gam[None, :]
    F = rng.standard_normal((n, N)) * gam[None, :]
    u1 = rng.standard_normal((n, 1))
    u2 = rng.standard_normal((n, 1))
    alpha = gamma * u1
    beta = gamma * (rho_f * u1 + np.sqrt(1.0 - rho_f**2) * u2)
    Q = X0 + alpha * F
    K = (r0 * X0 + np.sqrt(1.0 - r0**2) * Y0) + beta * F
    if nu > 0:
        F_rot = rng.standard_normal((n, N)) * gam[None, :]
        w_half = nu * rng.standard_normal(n // 2)
        w_pair = np.repeat(w_half, 2)[:, None]
        # J acts on pairs (2j, 2j+1): (x0, x1) -> (x1, -x0)
        JF_rot = np.empty_like(F_rot)
        JF_rot[0::2] = F_rot[1::2]
        JF_rot[1::2] = -F_rot[0::2]
        Q = Q + w_pair * F_rot
        K = K + w_pair * JF_rot
    return Q, K

print("=== Testing Candidate 2 across GPT-2-like regimes ===")
for name, (r0, gam_p) in [
    ("Near-null / typical head", (-0.05, 0.45)),
    ("L0H5-like (strong +align)", (+0.93, 0.70)),
    ("L5H9-like (neg bulk + wide)", (-0.45, 0.95)),
    ("L1H1-like (small tbar, huge std)", (-0.45, 1.35)),
    ("L10H7-like (mild +align, high PR)", (+0.22, 0.35)),
]:
    rows = [fast_stats(*sample_cand2(r0, gam_p)) for _ in range(30)]
    def m(k): return f"{np.median([r[k] for r in rows]):+.3f}"
    tmin_m = np.median([np.min(r['t']) for r in rows])
    tmax_m = np.median([np.max(r['t']) for r in rows])
    idx1 = np.arange(1, 65, dtype=float)
    c_idx = np.median([np.corrcoef(idx1, r['t'])[0, 1] for r in rows])
    print(f"{name:34s} (r0={r0:+.2f}, g={gam_p:.2f}): diag={m('diag')} tbar={m('tbar')} tstd={m('tstd')} [{tmin_m:+.2f},{tmax_m:+.2f}] off={m('offrms')} err1={m('err1')} a-b={m('amb')} PR={m('PR')} c_idx={c_idx:+.2f}")

print("\n=== Testing Candidate 3 on Rotary / Positive (a-b) heads ===")
for name, (r0, gam_p, nu_p) in [
    ("L0H3-like (+align + rotary)", (+0.52, 0.30, 0.95)),
    ("L0H7-like (mixed + rotary)", (-0.10, 0.85, 1.10)),
    ("LN-collapsed rotary head", (+0.10, 0.40, 1.60)),
]:
    rows = [fast_stats(*sample_cand3(r0, gam_p, nu_p)) for _ in range(30)]
    def m(k): return f"{np.median([r[k] for r in rows]):+.3f}"
    print(f"{name:34s} (r0={r0:+.2f}, g={gam_p:.2f}, nu={nu_p:.2f}): diag={m('diag')} tbar={m('tbar')} tstd={m('tstd')} off={m('offrms')} err1={m('err1')} a-b={m('amb')} c-d={m('cmd')} PR={m('PR')}")
    # Print top 4x4 of W for one sample!
    st1 = rows[0]
    print("  sample top 4 s/s[0]:", np.round(st1['s'][:4]/st1['s'][0], 3))
    print("  sample W[:3,:3]:\n", np.round(st1['W'][:3,:3], 3))
