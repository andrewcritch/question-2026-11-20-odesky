"""Which part of (Q,K) carries the statistics?  Structure-preserving nulls on GPT-2 small."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from common import load, stats, summarize, haar, N, n

rng = np.random.default_rng(1)
w, heads = load()
res = {k: [] for k in ['trained', 'headrot', 'ambrotK', 'colscale', 'layercov']}

# column (ambient-coordinate) energy profile per layer
for l in range(12):
    Qs = [Q for (ll, h, Q, K) in heads if ll == l]; Ks = [K for (ll, h, Q, K) in heads if ll == l]
    ce = sum((Q ** 2).sum(0) + (K ** 2).sum(0) for Q, K in zip(Qs, Ks))
    ce = ce / ce.sum()
    top = np.argsort(ce)[::-1][:5]
    print(f'layer {l}: ambient energy PR={1/np.sum(ce**2):6.1f}  top dims {top.tolist()} share {ce[top].round(3).tolist()}')

for (l, h, Q, K) in heads:
    res['trained'].append(stats(K.T @ Q))
    # head-space rotation: keep both row spaces of Q and K, randomise the pairing
    res['headrot'].append(stats((haar(n, rng) @ K).T @ Q))
    # ambient rotation of K: keep head-space wiring, destroy Q/K subspace overlap
    res['ambrotK'].append(stats((K @ haar(N, rng)).T @ Q))
    # independent Gaussian with the trained per-coordinate column norms
    cq = np.linalg.norm(Q, axis=0) / np.sqrt(n); ck = np.linalg.norm(K, axis=0) / np.sqrt(n)
    res['colscale'].append(stats((rng.standard_normal((n, N)) * ck).T @ (rng.standard_normal((n, N)) * cq)))
    # independent Gaussian with the layer's pooled ambient covariance (no per-head info)
    if h == 0:
        C = sum(QQ.T @ QQ + KK.T @ KK for (ll, hh, QQ, KK) in heads if ll == l) / (2 * 12 * n)
        ev, E = np.linalg.eigh(C); R = E * np.sqrt(np.maximum(ev, 0))
    res['layercov'].append(stats((rng.standard_normal((n, N)) @ R.T).T @ (rng.standard_normal((n, N)) @ R.T)))

for k, v in res.items():
    print(summarize(v, k))
