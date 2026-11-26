"""Fit the lognormal tilt ensemble (candidate A) per head and test its predictions.

Candidate A, per head, parameters (mu, s, v):
    rho_k = exp(sqrt(v) xi_k),  y_k = mu + s eta_k,      k = 1..n,  xi, eta iid N(0,1)
    P, M  : n x N, iid N(0,1) entries  (optionally rows ~ N(0, Gamma))
    Pi    = diag(sqrt(rho/2) e^{+y/2}) P ,  Delta = diag(sqrt(rho/2) e^{-y/2}) M
    Q = Pi - Delta ,  K = Pi + Delta
Then exactly S = Pi^T Pi - Delta^T Delta and T = Delta^T Pi - Pi^T Delta.

Asymptotic (n -> inf, N >> n) predictions, with r = exp(-2|mu|), eps = exp(-2 s^2):
    b = 1/(1 + eps + (1-r)^2/(2r)),  a = eps*b,  |c-d| = c+d = b(1-r)^2/(2r),  min(c,d) = 0
    err1 ~= sqrt(1+4 v)*(sqrt(v+s^2) - sqrt(v))
Fitting uses only gauge-free S/T spectral statistics: s from a/b, mu from (c+d)/b, v from PR.
The SVD-diagonal statistics (diag share, tbar, tstd, offrms) and err1 are then PREDICTED, by simulation.

usage: python -I fit_tilt.py [nsim]
"""
import sys, os, csv
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from common import load, stats, N, n

NSIM = int(sys.argv[1]) if len(sys.argv) > 1 else 2
rng = np.random.default_rng(7)
HERE = os.path.dirname(os.path.abspath(__file__))


def spectra(L):
    S = (L + L.T) / 2; T = (L - L.T) / 2
    ev = np.linalg.eigvalsh(S)
    lp = np.sort(ev[ev > 0])[::-1][:n]; lm = np.sort(-ev[ev < 0])[::-1][:n]
    sv = np.linalg.svd(T, compute_uv=False)[:2 * n:2]
    return lp, lm, sv


def profile(L):
    lp, lm, sv = spectra(L)
    T = (L - L.T) / 2; nL = np.sum(L * L)
    a = np.sum(T * T) / nL; b = 2 * lp @ lm / nL; dif = lp - lm
    c = np.sum(np.maximum(dif, 0) ** 2) / nL; d = np.sum(np.maximum(-dif, 0) ** 2) / nL
    return a, b, c, d, lp, lm, sv


def sample_A(mu, s, v, R=None):
    rho = np.exp(np.sqrt(v) * rng.standard_normal(n)); y = mu + s * rng.standard_normal(n)
    P = rng.standard_normal((n, N)); M = rng.standard_normal((n, N))
    if R is not None:
        P = P @ R.T; M = M @ R.T
    Pi = (np.sqrt(rho / 2) * np.exp(y / 2))[:, None] * P
    De = (np.sqrt(rho / 2) * np.exp(-y / 2))[:, None] * M
    Q = Pi - De; K = Pi + De
    return K.T @ Q


def Ecosh_moments(mu, s):
    # y ~ N(mu, s^2): E cosh^2 y, E cosh^4 y
    Ec2 = np.cosh(2 * mu) * np.exp(2 * s * s); Ec4 = np.cosh(4 * mu) * np.exp(8 * s * s)
    return (1 + Ec2) / 2, (3 + 4 * Ec2 + Ec4) / 8


V_NULL = np.log(64 / 54.8) / 4   # dispersion of sigma already produced by Wishart noise at N=768


def fit(a, b, c, d, PR):
    s2 = max(-0.5 * np.log(a / b), 0.0) if a < b else 0.0
    x = (c + d) / b
    r = (1 + x) - np.sqrt((1 + x) ** 2 - 1)
    mu = -0.5 * np.log(r) * (1 if c >= d else -1)
    C2, C4 = Ecosh_moments(mu, np.sqrt(s2))
    v_tot = max(np.log(n * C2 ** 2 / (PR * C4)) / 4, 1e-4)
    return mu, np.sqrt(s2), v_tot


def err1_asym(s, v):
    return np.sqrt(1 + 4 * v) * (np.sqrt(v + s * s) - np.sqrt(v))


w, heads = load()
pre = '' if 'h.0.ln_1.weight' in w else 'transformer.'
Pc = None
rows = []
SIMKEYS = ['diag', 'tbar', 'tstd', 'offrms', 'err1', 'amb', 'cmd', 'PR']
layerR = {}
for l in range(12):
    C = sum(Q.T @ Q + K.T @ K for (ll, hh, Q, K) in heads if ll == l)
    ev, E = np.linalg.eigh(C / np.trace(C) * N)
    layerR[l] = E * np.sqrt(np.maximum(ev, 0))
    print(f'layer {l}: ambient effective dim (tr C)^2/tr C^2 = {np.sum(ev)**2/np.sum(ev**2):.0f}', flush=True)

for var in ['raw', 'lnfold']:
    for (l, h, Q, K) in heads:
        L = K.T @ Q
        if var == 'lnfold':
            g = w[f'{pre}h.{l}.ln_1.weight'].astype(np.float64)
            L = g[:, None] * L * g[None, :]
            L = L - L.mean(0, keepdims=True); L = L - L.mean(1, keepdims=True)
        m = stats(L); m.pop('t'); m.pop('s')
        a, b, c, d, lp, lm, sv = profile(L)
        mu, s, v_tot = fit(a, b, c, d, m['PR'])
        v = max(v_tot - V_NULL, 1e-4)
        # second, independent estimate of s^2 from log-variances of the three spectra
        s2_spec = 0.5 * (np.var(np.log(lp)) + np.var(np.log(lm))) - np.var(np.log(sv))
        row = dict(var=var, layer=l, head=h, a=a, b=b, mincd=min(c, d), mu=mu, s=s, v=v,
                   s2_ab=s * s, s2_spec=s2_spec, err1_asym=err1_asym(s, v_tot), rotation_type=int(a > b))
        for k in SIMKEYS:
            row['meas_' + k] = m[k]
        for tag, R in [('iso', None), ('gam', layerR[l])]:
            sims = [stats(sample_A(mu, s, v, R)) for _ in range(NSIM)]
            for k in SIMKEYS + ['absamb']:
                row[f'{tag}_{k}'] = float(np.mean([x[k] for x in sims]))
            row[f'{tag}_mincd'] = float(np.mean([min(profile(sample_A(mu, s, v, R))[2:4]) for _ in range(1)]))
        rows.append(row)
        if h == 0:
            print(var, 'layer', l, 'done', flush=True)

with open(os.path.join(HERE, 'fit_tilt_out.csv'), 'w', newline='') as f:
    wr = csv.DictWriter(f, fieldnames=list(rows[0].keys())); wr.writeheader(); wr.writerows(rows)


def q(v):
    v = np.asarray(v); return f'{np.median(v):+.3f} [{np.percentile(v,10):+.3f},{np.percentile(v,90):+.3f}]'


for var in ['raw', 'lnfold']:
    R = [r for r in rows if r['var'] == var]
    B = [r for r in R if not r['rotation_type']]
    print(f'\n===== {var}: {len(R)} heads, {len(R)-len(B)} with a>b (rotation-type, outside candidate A) =====')
    print(f'fitted mu {q([r["mu"] for r in R])}  s {q([r["s"] for r in R])}  v {q([r["v"] for r in R])}')
    print(f'{"stat":8s} {"measured":28s} {"pred (iso)":28s} {"pred (layer Gamma)":28s} corr_iso corr_gam   [heads with a<b]')
    for k in SIMKEYS:
        me = [r['meas_' + k] for r in B]; pi = [r['iso_' + k] for r in B]; pg = [r['gam_' + k] for r in B]
        print(f'{k:8s} {q(me):28s} {q(pi):28s} {q(pg):28s} {np.corrcoef(me,pi)[0,1]:+.2f}     {np.corrcoef(me,pg)[0,1]:+.2f}')
    me = [r['meas_err1'] for r in B]; pa = [r['err1_asym'] for r in B]
    print(f'err1 asymptotic formula: corr {np.corrcoef(me,pa)[0,1]:+.3f}, median ratio pred/meas {np.median(np.array(pa)/np.array(me)):.2f}')
    s_ab = [r['s2_ab'] for r in B]; s_sp = [r['s2_spec'] for r in B]
    print(f's^2 from a/b {q(s_ab)}   s^2 from log-variances {q(s_sp)}   corr {np.corrcoef(s_ab,s_sp)[0,1]:+.3f}')
    print(f'min(c,d) measured {q([r["mincd"] for r in B])}  predicted(gam) {q([r["gam_mincd"] for r in B])}')
