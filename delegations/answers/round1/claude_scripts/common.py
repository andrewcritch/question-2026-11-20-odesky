import numpy as np
from safetensors.numpy import load_file

N, n, H = 768, 64, 12
WPATH = '/private/tmp/claude-501/-Users-andrew-maisi-questions-2026-11-20-odesky/8a345037-c99c-4fe5-98da-2190c1ebad66/scratchpad/ensemble_brief/gpt2_model.safetensors'


def load():
    w = load_file(WPATH)
    pre = '' if 'h.0.attn.c_attn.weight' in w else 'transformer.'
    heads = []
    for l in range(12):
        Wa = w[f'{pre}h.{l}.attn.c_attn.weight'].astype(np.float64)
        for h in range(H):
            Q = Wa[:, h * n:(h + 1) * n].T
            K = Wa[:, N + h * n:N + (h + 1) * n].T
            heads.append((l, h, Q, K))
    return w, heads


def stats(L):
    """Same definitions as gpt2_W.py."""
    S = (L + L.T) / 2; T = (L - L.T) / 2
    ev = np.linalg.eigvalsh(S)
    lp = np.sort(ev[ev > 0])[::-1][:n]; lm = np.sort(-ev[ev < 0])[::-1][:n]
    k = min(len(lp), len(lm)); lp, lm = lp[:k], lm[:k]
    sv = np.linalg.svd(T, compute_uv=False)[:2 * n:2][:k]
    nL = np.sum(L * L); a = np.sum(T * T) / nL; b = 2 * lp @ lm / nL; dif = lp - lm
    c = np.sum(np.maximum(dif, 0) ** 2) / nL; d = np.sum(np.maximum(-dif, 0) ** 2) / nL
    e1 = np.linalg.norm(sv - np.sqrt(lp * lm)) / np.linalg.norm(sv)
    U, s, Vt = np.linalg.svd(L); U, s, V = U[:, :n], s[:n], Vt[:n].T
    W = U.T @ V; t = np.diag(W); wt = s ** 2 / np.sum(s ** 2)
    tbar = wt @ t; tstd = np.sqrt(wt @ (t - tbar) ** 2)
    off = W - np.diag(t); offrms = np.sqrt(np.sum(off ** 2) / (n * n - n))
    return dict(err1=e1, amb=a - b, cmd=c - d, tbar=tbar, tstd=tstd, offrms=offrms,
                diag=np.sum(t ** 2) / np.sum(W ** 2), PR=np.sum(s ** 2) ** 2 / np.sum(s ** 4),
                absamb=abs(a - b), abstbar=abs(tbar), t=t, s=s)


KEYS = ['diag', 'tbar', 'abstbar', 'tstd', 'offrms', 'err1', 'amb', 'cmd', 'PR']


def summarize(rows, name):
    out = f'{name}\n'
    for k in KEYS:
        v = np.array([r[k] for r in rows])
        out += f'   {k:8s} {np.median(v):+.3f} [{np.percentile(v,10):+.3f}, {np.percentile(v,90):+.3f}]\n'
    return out


def haar(m, rng):
    A = rng.standard_normal((m, m)); Qm, R = np.linalg.qr(A)
    return Qm * np.sign(np.diag(R))
