"""Perturbed orthogonal-block ensemble, and |W_ij| vs spectral gap."""
import numpy as np
from safetensors.numpy import load_file

PATH = "ensemble_brief/gpt2_model.safetensors"
N, n = 768, 64
rng = np.random.default_rng(4)
wts = load_file(PATH)

def stats_QK(Q, K):
    Uq, sq, Vqh = np.linalg.svd(Q, full_matrices=False)
    Uk, sk, Vkh = np.linalg.svd(K, full_matrices=False)
    Ho = Uk.T @ Uq
    C = Vkh @ Vqh.T
    M = (sk[:, None] * Ho) * sq[None, :]
    P, sl, Sh = np.linalg.svd(M, full_matrices=False)
    W = P.T @ C @ Sh.T
    # profile via 2n embedding of the EXACT L = U sl V
    U = Vkh.T @ P
    V = Vqh.T @ Sh.T
    # build L densely? N=768 is ok but eig of 768 is slower. Use QR embedding.
    Z = np.concatenate([U, V], 1)
    Qr, R = np.linalg.qr(Z, mode="reduced")
    L = R[:, :n] @ np.diag(sl) @ R[:, n:].T
    S = 0.5 * (L + L.T)
    Tm = 0.5 * (L - L.T)
    ev = np.linalg.eigvalsh(S)
    lp = np.sort(ev[ev > 0])[::-1][:n]
    lm = np.sort(-ev[ev < 0])[::-1][:n]
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
    t = np.diag(W)
    ww = sl ** 2
    w = ww / ww.sum()
    off = W - np.diag(t)
    ent = off[~np.eye(n, dtype=bool)]
    return dict(err1=float(e1), amb=float(a - b), cd=float(c - d),
                tbar=float(w @ t), tstd=float(np.sqrt(w @ (t - w @ t) ** 2)),
                offrms=float(np.sqrt(np.mean(off ** 2) * n / (n - 1))),  # rms over off entries
                diagfrac=float(np.sum(t ** 2) / np.sum(W ** 2)),
                PR=float((ww.sum() ** 2) / np.sum(ww ** 2)),
                kurt=float(((ent - ent.mean()) ** 4).mean() / (ent.var() ** 2 + 1e-30)),
                Wf2=float(np.sum(W ** 2)))

def block_QK(alpha, t, rng):
    """Exact nearly-orthogonal planes: q, g random gaussians, row-normalized."""
    Gq = rng.standard_normal((n, N))
    Gg = rng.standard_normal((n, N))
    qn = np.linalg.norm(Gq, axis=1, keepdims=True)
    gn = np.linalg.norm(Gg, axis=1, keepdims=True)
    qhat, ghat = Gq / qn, Gg / gn
    s = np.sqrt(np.clip(1 - t ** 2, 0, None))
    Q = qhat * alpha[:, None]
    K = (t[:, None] * qhat + s[:, None] * ghat) * alpha[:, None]
    return Q, K

def show(name, recs):
    print(f"\n{name}")
    for k in ["err1", "amb", "cd", "tbar", "tstd", "offrms", "diagfrac", "PR", "kurt", "Wf2"]:
        v = np.array([r[k] for r in recs])
        print(f"  {k:10s} med={np.median(v):+.3f}  mean={v.mean():+.3f}")

# spectrum shape taken from a real median-ish head: load one Q spectrum later; use mild power
idx = np.arange(1, n + 1)
# fit later; first use flat and a weakly decaying spectrum matching PR~46
def alpha_for_pr(beta):
    a = idx ** (-beta)
    return a / np.sqrt(np.mean(a ** 2))

def tdraw(mu, s):
    return np.clip(rng.normal(mu, s, n), -0.95, 0.95)

print("==== perturbed block model ====")
for eps in [0.0, 0.05, 0.1, 0.2, 0.4]:
    def trial(eps=eps):
        t = tdraw(0.0, 0.25)
        a = np.ones(n)
        Q, K = block_QK(a, t, rng)
        if eps > 0:
            Q = Q + eps * rng.standard_normal((n, N)) * (np.linalg.norm(Q) / np.sqrt(n * N))
            K = K + eps * rng.standard_normal((n, N)) * (np.linalg.norm(K) / np.sqrt(n * N))
        return stats_QK(Q, K)
    show(f"eps={eps} flat alpha t~N(0,0.25)", [trial() for _ in range(6)])

for eps in [0.0, 0.1, 0.2]:
    def trial(eps=eps):
        t = tdraw(0.0, 0.25)
        a = alpha_for_pr(0.08)
        Q, K = block_QK(a, t, rng)
        if eps > 0:
            nQ = np.linalg.norm(Q); nK = np.linalg.norm(K)
            Q = Q + eps * rng.standard_normal((n, N)) * (nQ / np.sqrt(n * N))
            K = K + eps * rng.standard_normal((n, N)) * (nK / np.sqrt(n * N))
        return stats_QK(Q, K)
    show(f"eps={eps} beta=0.08 t~N(0,0.25)", [trial() for _ in range(5)])

# aligned head
def trial():
    t = tdraw(0.85, 0.08)
    Q, K = block_QK(np.ones(n), t, rng)
    eps = 0.1
    Q = Q + eps * rng.standard_normal((n, N)) * (np.linalg.norm(Q) / np.sqrt(n * N))
    K = K + eps * rng.standard_normal((n, N)) * (np.linalg.norm(K) / np.sqrt(n * N))
    return stats_QK(Q, K)
show("aligned mu=0.85 s=0.08 eps=0.1", [trial() for _ in range(5)])

print("\n==== |W_ij| vs |i-j| and vs |log sig_i - log sig_j| on real heads ====")
# bin mean |W|/offrms by |i-j| and by relative gap
gap_bins = np.zeros(10)
gap_w = np.zeros(10)
dist_bins = np.zeros(16)
dist_w = np.zeros(16)
# also correlation of log|W_ij| with -|i-j|
corrs_dist = []
corrs_gap = []
for l in range(12):
    Wa = wts[f"h.{l}.attn.c_attn.weight"]
    for h in range(12):
        Q = Wa[:, h * n:(h + 1) * n].T.astype(np.float64)
        K = Wa[:, N + h * n:N + (h + 1) * n].T.astype(np.float64)
        # only need W and sl; reuse stats path partially
        Uq, sq, Vqh = np.linalg.svd(Q, full_matrices=False)
        Uk, sk, Vkh = np.linalg.svd(K, full_matrices=False)
        M = (sk[:, None] * (Uk.T @ Uq)) * sq[None, :]
        P, sl, Sh = np.linalg.svd(M, full_matrices=False)
        W = P.T @ (Vkh @ Vqh.T) @ Sh.T
        off = np.abs(W - np.diag(np.diag(W)))
        rms = np.sqrt(np.mean((W - np.diag(np.diag(W))) ** 2))
        ii, jj = np.triu_indices(n, k=1)
        dij = np.abs(ii - jj)
        # relative gap
        g = np.abs(sl[ii] - sl[jj]) / (np.median(sl) + 1e-15)
        a = off[ii, jj] / (rms + 1e-15)
        # distance bins of width 4
        for b in range(16):
            m = (dij > b * 4) & (dij <= (b + 1) * 4)
            if m.any():
                dist_bins[b] += a[m].mean()
                dist_w[b] += 1
        gb = np.clip((g / 0.15).astype(int), 0, 9)
        for b in range(10):
            m = gb == b
            if m.any():
                gap_bins[b] += a[m].mean()
                gap_w[b] += 1
        corrs_dist.append(np.corrcoef(dij, a)[0, 1])
        corrs_gap.append(np.corrcoef(g, a)[0, 1])

print("mean |W|/rms by |i-j| bins of 4:")
print(np.round(dist_bins / np.maximum(dist_w, 1), 3))
print("mean |W|/rms by |si-sj|/median(s) bins of 0.15:")
print(np.round(gap_bins / np.maximum(gap_w, 1), 3))
print(f"corr(|W|,|i-j|) med={np.median(corrs_dist):+.3f}")
print(f"corr(|W|, spectral gap) med={np.median(corrs_gap):+.3f}")
