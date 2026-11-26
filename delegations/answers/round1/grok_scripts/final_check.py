"""One operating point: architectural bulk 1/sqrt(N) plus 8 symmetric defects."""
import numpy as np
from safetensors.numpy import load_file

PATH = "ensemble_brief/gpt2_model.safetensors"
N, n = 768, 64
rng = np.random.default_rng(8)
wts = load_file(PATH)
SIG = 1 / np.sqrt(N)

def project(W):
    if np.linalg.norm(W, 2) > 0.999:
        U, s, Vt = np.linalg.svd(W, full_matrices=False)
        W = (U * np.minimum(s, 0.999)) @ Vt
    return W

def fullstats(sig, W):
    W = project(W)
    R2 = np.eye(n) - W.T @ W
    ev, E = np.linalg.eigh(0.5 * (R2 + R2.T))
    R = (E * np.sqrt(np.clip(ev, 0, None))) @ E.T
    L = np.vstack([np.eye(n), np.zeros((n, n))]) @ (sig[:, None] * np.vstack([W, R]).T)
    S = 0.5 * (L + L.T); Tm = 0.5 * (L - L.T)
    evs = np.linalg.eigvalsh(S)
    lp = np.sort(evs[evs > 0])[::-1][:n]
    lm = np.sort(-evs[evs < 0])[::-1][:n]
    if len(lp) < n: lp = np.pad(lp, (0, n - len(lp)))
    if len(lm) < n: lm = np.pad(lm, (0, n - len(lm)))
    sv = np.linalg.svd(Tm, compute_uv=False)[:2 * n:2][:n]
    nL = np.sum(L * L) + 1e-30
    a = np.sum(Tm * Tm) / nL
    b = 2 * np.dot(lp, lm) / nL
    dif = lp - lm
    c = np.sum(np.maximum(dif, 0) ** 2) / nL
    d = np.sum(np.maximum(-dif, 0) ** 2) / nL
    e1 = np.linalg.norm(sv - np.sqrt(np.maximum(lp, 0) * np.maximum(lm, 0))) / (np.linalg.norm(sv) + 1e-15)
    t = np.diag(W)
    ww = sig ** 2; w = ww / ww.sum()
    off = W - np.diag(t)
    ent = off[~np.eye(n, dtype=bool)]
    return dict(err1=float(e1), a_minus_b=float(a - b), c_minus_d=float(c - d),
                tbar=float(w @ t), tstd=float(np.sqrt(max(w @ (t - w @ t) ** 2, 0))),
                offrms=float(np.sqrt(np.sum(off ** 2) / (n * (n - 1)))),
                diagfrac=float(np.sum(np.diag(W) ** 2) / np.sum(W ** 2)),
                Wf2=float(np.sum(W ** 2)),
                kurt=float(((ent - ent.mean()) ** 4).mean() / (ent.var() ** 2 + 1e-30)),
                symfrac=float(np.sum(((W + W.T) / 2) ** 2) / (np.sum(W ** 2) + 1e-30)))

def load_heads():
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
            st = fullstats(sl, W)
            st.update(sl=sl, t=np.diag(W).real.copy())
            heads.append(st)
    return heads

def sample_W(t, k, c, rng):
    G = rng.standard_normal((n, n)) * SIG
    Kskew = 0.5 * (G - G.T)
    np.fill_diagonal(Kskew, 0.0)
    W = np.diag(t).astype(float) + Kskew
    for _ in range(k):
        i, j = rng.choice(n, 2, replace=False)
        val = c * rng.choice([-1.0, 1.0])
        W[i, j] += val
        W[j, i] += val
    return W

heads = load_heads()
KEYS = ["err1", "a_minus_b", "c_minus_d", "tbar", "tstd", "offrms", "diagfrac", "Wf2", "kurt", "symfrac"]
# oracle t
for label, k, c, resample in [("oracle t k=8 c=0.50", 8, 0.50, False),
                              ("oracle t k=8 c=0.45", 8, 0.45, False),
                              ("gauss t k=8 c=0.50", 8, 0.50, True)]:
    err = {kk: [] for kk in KEYS}
    pred = {kk: [] for kk in KEYS}
    for h in heads:
        acc = {kk: [] for kk in KEYS}
        for _ in range(2):
            t = h["t"]
            if resample:
                t = np.clip(rng.normal(h["t"].mean(), max(h["t"].std(), 1e-3), n), -0.98, 0.98)
            st = fullstats(h["sl"], sample_W(t, k, c, rng))
            for kk in KEYS:
                acc[kk].append(st[kk])
        for kk in KEYS:
            m = np.mean(acc[kk])
            pred[kk].append(m)
            err[kk].append(m - h[kk])
    print(f"\n== {label} ==")
    print(f"{'stat':12s} {'bias':>8s} {'mae':>8s} {'dataMed':>8s} {'modMed':>8s}")
    for kk in KEYS:
        e = np.array(err[kk]); d = np.array([h[kk] for h in heads]); m = np.array(pred[kk])
        print(f"{kk:12s} {e.mean():+8.3f} {np.mean(np.abs(e)):8.3f} {np.median(d):8.3f} {np.median(m):8.3f}")
