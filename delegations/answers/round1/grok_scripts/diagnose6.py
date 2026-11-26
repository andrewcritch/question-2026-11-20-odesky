"""Sign coherence of large W entries, and spike/Givens models for err1."""
import numpy as np
from safetensors.numpy import load_file

PATH = "ensemble_brief/gpt2_model.safetensors"
N, n = 768, 64
rng = np.random.default_rng(5)
wts = load_file(PATH)

def err1_profile(sig, W):
    op = np.linalg.norm(W, 2)
    if op > 0.999:
        U, s, Vt = np.linalg.svd(W, full_matrices=False)
        W = (U * np.minimum(s, 0.999)) @ Vt
    R2 = np.eye(n) - W.T @ W
    ev, E = np.linalg.eigh(0.5 * (R2 + R2.T))
    ev = np.clip(ev, 0, None)
    R = (E * np.sqrt(ev)) @ E.T
    L = np.concatenate([np.eye(n), np.zeros((n, n))], 0) @ np.diag(sig) @ np.concatenate([W, R], 0).T
    S = 0.5 * (L + L.T)
    Tm = 0.5 * (L - L.T)
    evs = np.linalg.eigvalsh(S)
    lp = np.sort(evs[evs > 0])[::-1][:n]
    lm = np.sort(-evs[evs < 0])[::-1][:n]
    if len(lp) < n: lp = np.pad(lp, (0, n - len(lp)))
    if len(lm) < n: lm = np.pad(lm, (0, n - len(lm)))
    sv = np.linalg.svd(Tm, compute_uv=False)[: 2 * n : 2][:n]
    nL = np.sum(L * L) + 1e-30
    e1 = np.linalg.norm(sv - np.sqrt(np.maximum(lp, 0) * np.maximum(lm, 0))) / (np.linalg.norm(sv) + 1e-15)
    a = np.sum(Tm * Tm) / nL
    b = 2 * np.dot(lp, lm) / nL
    dif = lp - lm
    c = np.sum(np.maximum(dif, 0) ** 2) / nL
    d = np.sum(np.maximum(-dif, 0) ** 2) / nL
    return float(e1), float(a - b), float(c - d)

heads = []
for l in range(12):
    Wa = wts[f"h.{l}.attn.c_attn.weight"]
    for h in range(12):
        Q = Wa[:, h * n:(h + 1) * n].T.astype(np.float64)
        K = Wa[:, N + h * n:N + (h + 1) * n].T.astype(np.float64)
        Uq, sq, Vqh = np.linalg.svd(Q, full_matrices=False)
        Uk, sk, Vkh = np.linalg.svd(K, full_matrices=False)
        M = (sk[:, None] * (Uk.T @ Uq)) * sq[None, :]
        P, sl, Sh = np.linalg.svd(M, full_matrices=False)
        W = P.T @ (Vkh @ Vqh.T) @ Sh.T
        heads.append((sl, W))

# symmetry of large entries
sym_ratio_large = []
corr_ji = []
for sl, W in heads:
    offmask = ~np.eye(n, dtype=bool)
    rms = np.sqrt(np.mean((W - np.diag(np.diag(W))) ** 2))
    # upper triangle
    iu = np.triu_indices(n, 1)
    mag = 0.5 * (np.abs(W[iu]) + np.abs(W.T[iu]))
    thr = np.quantile(mag, 0.95)
    big = mag >= thr
    if big.sum() < 5:
        continue
    wp, wm = W[iu][big], W.T[iu][big]
    # symmetry score in [0,1]: 1 if symmetric, 0 if skew
    sym_ratio_large.append(np.mean(np.abs(wp + wm) / (np.abs(wp) + np.abs(wm) + 1e-15)))
    corr_ji.append(np.corrcoef(W[iu], W.T[iu])[0, 1])

print(f"corr(W_ij, W_ji) all upper med={np.median(corr_ji):+.3f}")
print(f"symmetry ratio of top-5% pairs med={np.median(sym_ratio_large):.3f}  (1=symmetric, 0.5=neither, 0=skew)")

# sign-randomization test
def rand_signs(sl, W, rng):
    A = W.copy()
    iu = np.triu_indices(n, 1)
    signs = rng.choice([-1.0, 1.0], size=len(iu[0]))
    A[iu] *= signs
    A[(iu[1], iu[0])] *= signs  # same sign flip on both? or independent
    return A

def rand_signs_indep(sl, W, rng):
    A = np.diag(np.diag(W)).astype(float)
    mask = ~np.eye(n, dtype=bool)
    A[mask] = np.abs(W[mask]) * rng.choice([-1.0, 1.0], size=int(mask.sum()))
    return A

def median_err(fn, trials=1):
    vals = []
    for sl, W in heads:
        acc = [fn(sl, W, rng) for _ in range(trials)]
        # fn returns W
        es = [err1_profile(sl, A)[0] for A in acc]
        vals.append(np.mean(es))
    return np.median(vals)

print("original", np.median([err1_profile(sl, W)[0] for sl, W in heads]))
print("flip signs of pairs together", median_err(lambda sl, W, rng: rand_signs(sl, W, rng), 1))
print("independent random signs on |W|", median_err(lambda sl, W, rng: rand_signs_indep(sl, W, rng), 1))

# rank-1 spike on top of measured diagonal: sweep c
print("\n== rank-one spikes added to measured diag(t), median err1 ==")
base = []
for c in [0.0, 0.3, 0.6, 1.0, 1.5]:
    vals = []
    for sl, W in heads:
        t = np.diag(W).real
        u = rng.standard_normal(n); u /= np.linalg.norm(u)
        v = rng.standard_normal(n); v /= np.linalg.norm(v)
        Wm = np.diag(t) + c * np.outer(u, v)
        vals.append(err1_profile(sl, Wm)[0])
    print(f"  c={c:.1f} random uv^T   err1 med={np.median(vals):.3f}")

# spike along coordinate directions: a few random big entries
print("\n== k random big entries of size c, on measured diag ==")
for k, c in [(8, 0.3), (16, 0.3), (32, 0.25), (64, 0.2), (8, 0.5), (16, 0.5)]:
    vals = []
    for sl, W in heads:
        t = np.diag(W).real
        Wm = np.diag(t).astype(float)
        for _ in range(k):
            i, j = rng.integers(0, n, size=2)
            if i == j:
                continue
            Wm[i, j] += c * rng.choice([-1.0, 1.0])
        vals.append(err1_profile(sl, Wm)[0])
    print(f"  k={k:3d} c={c:.2f}  err1 med={np.median(vals):.3f}")

# Student-t bulk
print("\n== student-t off-diagonal (df=4) scale matched to offrms, median err1 ==")
vals = []
for sl, W in heads:
    t = np.diag(W).real
    offrms = np.sqrt(np.sum((W - np.diag(t)) ** 2) / (n * (n - 1)))
    Z = rng.standard_t(4, size=(n, n))
    Z = Z / np.std(Z) * offrms
    np.fill_diagonal(Z, 0)
    vals.append(err1_profile(sl, np.diag(t) + Z)[0])
print(f"  student err1 med={np.median(vals):.3f}")

# Givens: conjugate diag by a product of k plane rotations with angle theta, independently left and right
print("\n== Givens dressing of a LARGER latent diagonal, then measure err1 ==")
def givens_ortho(k, theta, rng):
    R = np.eye(n)
    for _ in range(k):
        i, j = rng.choice(n, size=2, replace=False)
        c, s = np.cos(theta), np.sin(theta)
        Ri = np.eye(n)
        Ri[i, i] = c; Ri[j, j] = c; Ri[i, j] = s; Ri[j, i] = -s
        R = Ri @ R
    return R

for k, theta, scale in [(8, 0.4, 0.5), (16, 0.3, 0.45), (32, 0.25, 0.4), (8, 0.8, 0.6), (4, 1.0, 0.7)]:
    vals_e, vals_df, vals_off, vals_kurt = [], [], [], []
    for sl, W in heads:
        # latent c chosen so that after dressing, we don't use measured t
        # use measured |spectrum of W| as latent singular values? use measured t scaled
        cvec = np.clip(np.diag(W).real * scale / 0.3, -0.95, 0.95)  # nonsense
    # better: plant c from measured t inflated, dress, compare err1 to original
    for sl, W in heads:
        cvec = np.clip(np.diag(W).real, -0.95, 0.95)
        Rl = givens_ortho(k, theta, rng)
        Rr = givens_ortho(k, theta, rng)
        Wm = Rl.T @ np.diag(cvec) @ Rr
        e, amb, cd = err1_profile(sl, Wm)
        vals_e.append(e)
        off = Wm - np.diag(np.diag(Wm))
        ent = off[~np.eye(n, dtype=bool)]
        vals_kurt.append(((ent - ent.mean()) ** 4).mean() / (ent.var() ** 2 + 1e-30))
        vals_df.append(np.sum(np.diag(Wm) ** 2) / np.sum(Wm ** 2))
        vals_off.append(np.sqrt(np.mean(ent ** 2)))
    print(f"  k={k:3d} th={theta:.2f} err1={np.median(vals_e):.3f} diagfrac={np.median(vals_df):.3f} off={np.median(vals_off):.3f} kurt={np.median(vals_kurt):.1f}")
