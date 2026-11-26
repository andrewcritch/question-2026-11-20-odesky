"""Ginibre bulk at the measured scale, with the largest pairs symmetrized."""
import numpy as np
from safetensors.numpy import load_file

PATH = "ensemble_brief/gpt2_model.safetensors"
N, n = 768, 64
rng = np.random.default_rng(9)
wts = load_file(PATH)
SIG = 0.0483

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
                offrms=float(np.sqrt(np.sum(off ** 2) / (n * (n - 1)))),
                diagfrac=float(np.sum(t ** 2) / np.sum(W ** 2)),
                Wf2=float(np.sum(W ** 2)),
                kurt=float(((ent - ent.mean()) ** 4).mean() / (ent.var() ** 2 + 1e-30)),
                symfrac=float(np.sum(((W + W.T) / 2) ** 2) / (np.sum(W ** 2) + 1e-30)),
                tstd=float(np.sqrt(max(w @ (t - w @ t) ** 2, 0))),
                tbar=float(w @ t))

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

def make(t, m_pairs, how, rng):
    Z = rng.standard_normal((n, n)) * SIG
    np.fill_diagonal(Z, 0.0)
    iu = np.triu_indices(n, 1)
    mag = np.maximum(np.abs(Z[iu]), np.abs(Z.T[iu]))
    if m_pairs > 0:
        pick = np.argpartition(mag, -m_pairs)[-m_pairs:]
        for p in pick:
            i, j = iu[0][p], iu[1][p]
            if how == "avg":
                v = 0.5 * (Z[i, j] + Z[j, i])
                Z[i, j] = Z[j, i] = v
            elif how == "copy":
                # copy the larger-magnitude value onto both, with the sign of Z_ij
                if abs(Z[i, j]) >= abs(Z[j, i]):
                    Z[j, i] = Z[i, j]
                else:
                    Z[i, j] = Z[j, i]
    return np.diag(t) + Z

KEYS = ["err1", "a_minus_b", "c_minus_d", "offrms", "diagfrac", "Wf2", "kurt", "symfrac", "tstd", "tbar"]
for m, how in [(0, "avg"), (20, "copy"), (50, "copy"), (100, "copy"), (200, "copy"),
               (50, "avg"), (100, "avg"), (200, "avg"), (400, "avg")]:
    err = {k: [] for k in KEYS}
    pred = {k: [] for k in KEYS}
    for h in heads:
        acc = {k: [] for k in KEYS}
        for _ in range(1):
            st = fullstats(h["sl"], make(h["t"], m, how, rng))
            for k in KEYS:
                acc[k].append(st[k])
        for k in KEYS:
            val = acc[k][0]
            pred[k].append(val)
            err[k].append(val - h[k])
    e1 = np.array(err["err1"]); ab = np.array(err["a_minus_b"])
    print(f"m={m:3d} {how:4s}  err1 medPred={np.median(pred['err1']):.3f} bias={e1.mean():+.3f}  "
          f"a-b medPred={np.median(pred['a_minus_b']):+.3f}  off={np.median(pred['offrms']):.3f}  "
          f"diag={np.median(pred['diagfrac']):.3f}  kurt={np.median(pred['kurt']):.1f}  "
          f"sym={np.median(pred['symfrac']):.3f}  Wf2={np.median(pred['Wf2']):.1f}")
