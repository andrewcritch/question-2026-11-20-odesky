"""Diagnostics for candidate B (rotation channels) and for balancedness.

Per head (raw L = K^T Q):
  tau2   = Re tr(L^2)/||L||^2 = sum Re(mu_k^2)/sum sigma_k^2      (mu = eig(Q K^T));  a = (1 - tau2)/2 exactly
  iota   = sum Im(mu_k)^2 / sum sigma_k^2                         (rotation content; candidate A predicts ~ null)
  ovl    = mean cos^2 of principal angles between rowspaces of Q+K and K-Q
           (candidate A: ~ n/N; rotation channels raise it, and only then can a > b)
  pos    = ||P L P||^2/||L||^2, P = projector on top-k PCs of the positional embedding wpe
  bal    = ||QQ^T - KK^T||_F / ||QQ^T + KK^T||_F (gradient flow from small init keeps this small)
Each is compared with an independent Gaussian null of the same shape.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from common import load, N, n

rng = np.random.default_rng(3)
w, heads = load()
pre = '' if 'wpe.weight' in w else 'transformer.'
wpe = w[pre + 'wpe.weight'].astype(np.float64)
wpe = wpe - wpe.mean(0)
_, sp, Vt = np.linalg.svd(wpe, full_matrices=False)
KPOS = 10
Vp = Vt[:KPOS].T
print(f'wpe: top-{KPOS} PCs carry {np.sum(sp[:KPOS]**2)/np.sum(sp**2):.3f} of its variance')


def diag(Q, K):
    L = K.T @ Q
    s = np.linalg.svd(L, compute_uv=False)[:n]
    mu = np.linalg.eigvals(Q @ K.T)
    S2 = np.sum(s ** 2)
    tau2 = np.sum((mu ** 2).real) / S2; iota = np.sum(mu.imag ** 2) / S2
    A = np.linalg.qr((Q + K).T)[0]; B = np.linalg.qr((K - Q).T)[0]
    ovl = np.sum(np.linalg.svd(A.T @ B, compute_uv=False) ** 2) / n
    Lp = Vp.T @ L @ Vp; pos = np.sum(Lp ** 2) / np.sum(L ** 2)
    G1 = Q @ Q.T; G2 = K @ K.T
    bal = np.linalg.norm(G1 - G2) / np.linalg.norm(G1 + G2)
    # commutator of the centred Gram matrices of Pi=(Q+K)/2 and Delta=(K-Q)/2 (candidate A: they commute)
    Gp = (Q + K) @ (Q + K).T / 4; Gm = (K - Q) @ (K - Q).T / 4
    Gp = Gp - np.trace(Gp) / n * np.eye(n); Gm = Gm - np.trace(Gm) / n * np.eye(n)
    comm = np.linalg.norm(Gp @ Gm - Gm @ Gp) / (np.linalg.norm(Gp) * np.linalg.norm(Gm))
    T = (L - L.T) / 2; a = np.sum(T * T) / np.sum(L * L)
    ev = np.linalg.eigvalsh((L + L.T) / 2)
    lp = np.sort(ev[ev > 0])[::-1][:n]; lm = np.sort(-ev[ev < 0])[::-1][:n]
    b = 2 * lp @ lm / np.sum(L * L)
    sT = np.linalg.svd(T, compute_uv=False)[:2 * n:2]
    detgap = np.sum(np.log(sT)) - 0.5 * np.sum(np.log(lp) + np.log(lm))   # = 0 exactly (determinant identity)
    return dict(tau2=tau2, iota=iota, ovl=ovl, pos=pos, bal=bal, comm=comm, amb=a - b, PR=S2 ** 2 / np.sum(s ** 4),
                a_check=a - (1 - tau2) / 2, detgap=detgap)


R = []; G = []
for (l, h, Q, K) in heads:
    r = diag(Q, K); r.update(layer=l, head=h); R.append(r)
    sq = np.linalg.norm(Q) / np.sqrt(n * N); sk = np.linalg.norm(K) / np.sqrt(n * N)
    G.append(diag(rng.standard_normal((n, N)) * sq, rng.standard_normal((n, N)) * sk))


def q(v):
    v = np.asarray(v); return f'{np.median(v):+.4f} [{np.percentile(v,10):+.4f},{np.percentile(v,90):+.4f}]'


print('max |a - (1-tau2)/2| =', max(abs(r['a_check']) for r in R))
print('max |sum log sigma(T) - 1/2 sum log(lam+ lam-)| =', max(abs(r['detgap']) for r in R))
for k in ['tau2', 'iota', 'ovl', 'pos', 'bal', 'comm']:
    x = np.array([r[k] for r in R]); amb = np.array([r['amb'] for r in R])
    print(f'{k:5s} trained {q(x)}  null {q([g[k] for g in G])}  corr with (a-b) {np.corrcoef(x, amb)[0,1]:+.2f}  '
          f'Spearman {np.corrcoef(np.argsort(np.argsort(x)), np.argsort(np.argsort(amb)))[0,1]:+.2f}')
print('\nheads with a-b > 0.03 (candidate-B heads):')
for r in sorted(R, key=lambda r: -r['amb']):
    if r['amb'] > 0.03:
        print(f"  L{r['layer']}H{r['head']}: a-b={r['amb']:+.3f} PR={r['PR']:5.1f} iota={r['iota']:.3f} ovl={r['ovl']:.3f} pos={r['pos']:.3f}")
