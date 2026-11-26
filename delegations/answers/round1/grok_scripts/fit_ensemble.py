"""Per-head score of the mode-alignment ensemble with a symmetric sparse defect."""
import numpy as np
from safetensors.numpy import load_file

PATH = "ensemble_brief/gpt2_model.safetensors"
N, n = 768, 64
rng = np.random.default_rng(7)
wts = load_file(PATH)

def project(W):
    op = np.linalg.norm(W, 2)
    if op > 0.999:
        U, s, Vt = np.linalg.svd(W, full_matrices=False)
        W = (U * np.minimum(s, 0.999)) @ Vt
    return W

def fullstats(sig, W):
    W = project(W)
    R2 = np.eye(n) - W.T @ W
    ev, E = np.linalg.eigh(0.5 * (R2 + R2.T))
    R = (E * np.sqrt(np.clip(ev, 0, None))) @ E.T
    L = np.vstack([np.eye(n), np.zeros((n, n))]) @ (sig[:, None] * np.vstack([W, R]).T)
    S = 0.5 * (L + L.T)
    Tm = 0.5 * (L - L.T)
    evs = np.linalg.eigvalsh(S)
    lp = np.sort(evs[evs > 0])[::-1][:n]
    lm = np.sort(-evs[evs < 0])[::-1][:n]
    if len(lp) < n: lp = np.pad(lp, (0, n - len(lp)))
    if len(lm) < n: lm = np.pad(lm, (0, n - len(lm)))
    sv = np.linalg.svd(Tm, compute_uv=False)[: 2 * n : 2][:n]
    nL = np.sum(L * L) + 1e-30
    a = np.sum(Tm * Tm) / nL
    b = 2 * np.dot(lp, lm) / nL
    dif = lp - lm
    c = np.sum(np.maximum(dif, 0) ** 2) / nL
    d = np.sum(np.maximum(-dif, 0) ** 2) / nL
    e1 = np.linalg.norm(sv - np.sqrt(np.maximum(lp, 0) * np.maximum(lm, 0))) / (np.linalg.norm(sv) + 1e-15)
    t = np.diag(W)
    ww = sig ** 2
    w = ww / ww.sum()
    off = W - np.diag(t)
    ent = off[~np.eye(n, dtype=bool)]
    return dict(
        err1=float(e1), a_minus_b=float(a - b), c_minus_d=float(c - d),
        tbar=float(w @ t), tstd=float(np.sqrt(max(w @ (t - w @ t) ** 2, 0))),
        offrms=float(np.sqrt(np.sum(off ** 2) / (n * (n - 1)))),
        diagfrac=float(np.sum(t ** 2) / np.sum(W ** 2)),
        Wf2=float(np.sum(W ** 2)),
        kurt=float(((ent - ent.mean()) ** 4).mean() / (ent.var() ** 2 + 1e-30)),
        symfrac=float(np.sum(((W + W.T) / 2) ** 2) / np.sum(W ** 2)),
        PR=float((ww.sum() ** 2) / np.sum(ww ** 2)),
    )

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
        st.update(sl=sl, t=np.diag(W).real.copy(), layer=l, head=h)
        heads.append(st)

KEYS = ["err1", "a_minus_b", "c_minus_d", "tbar", "tstd", "offrms", "diagfrac", "Wf2", "kurt", "symfrac"]

def sample_W(t, sigma_skew, k, c, rng, sigma_sym_bulk=0.0):
    W = np.diag(t).astype(float)
    if sigma_skew > 0:
        G = rng.standard_normal((n, n)) * sigma_skew
        K = 0.5 * (G - G.T)
        np.fill_diagonal(K, 0.0)
        W += K
    if sigma_sym_bulk > 0:
        G = rng.standard_normal((n, n)) * sigma_sym_bulk
        S = 0.5 * (G + G.T)
        np.fill_diagonal(S, 0.0)
        W += S
    for _ in range(k):
        i, j = rng.choice(n, 2, replace=False)
        val = c * rng.choice([-1.0, 1.0])
        W[i, j] += val
        W[j, i] += val
    return W

def evaluate(name, maker, trials=2):
    err = {k: [] for k in KEYS}
    for h in heads:
        acc = {k: [] for k in KEYS}
        for _ in range(trials):
            Wm = maker(h, rng)
            st = fullstats(h["sl"], Wm)
            for k in KEYS:
                acc[k].append(st[k])
        for k in KEYS:
            err[k].append(np.mean(acc[k]) - h[k])
    print(f"\n== {name} ==")
    for k in KEYS:
        v = np.array(err[k])
        print(f"  {k:12s} bias={v.mean():+.4f}  mae={np.mean(np.abs(v)):.4f}  med={np.median(v):+.4f}")

# Oracle t, several spike settings. sigma_skew so skew mass ~ half of typical off mass.
# n(n-1)*sigma^2 = mass. For sigma=0.034, mass=n(n-1)*0.001156=4.66
configs = [
    ("ginibre only s=0.048", dict(sigma_skew=0.048, sigma_sym_bulk=0.048, k=0, c=0.0)),
    ("skew0.034 + 16 sym spikes c=0.38", dict(sigma_skew=0.034, k=16, c=0.38)),
    ("skew0.030 + 24 sym spikes c=0.30", dict(sigma_skew=0.030, k=24, c=0.30)),
    ("skew0.040 + 8 sym spikes c=0.45", dict(sigma_skew=0.040, k=8, c=0.45)),
    ("balanced bulk 0.040 + 12 spikes 0.35", dict(sigma_skew=0.040, sigma_sym_bulk=0.020, k=12, c=0.35)),
    ("skew0.036 + 16 spikes 0.30", dict(sigma_skew=0.036, k=16, c=0.30)),
]
for name, cfg in configs:
    def maker(h, rng, cfg=cfg):
        return sample_W(h["t"], cfg["sigma_skew"], cfg["k"], cfg["c"], rng, cfg.get("sigma_sym_bulk", 0.0))
    evaluate(name, maker, trials=2)

# Resampled t ~ N(mu, s) with the best-looking config, oracle Sigma
def maker_resamp(h, rng):
    mu, s = float(h["t"].mean()), float(h["t"].std())
    t = np.clip(rng.normal(mu, max(s, 1e-3), n), -0.98, 0.98)
    return sample_W(t, 0.034, 16, 0.38, rng)

evaluate("resampled Gaussian t, skew0.034+16*0.38, oracle Sigma", maker_resamp, trials=2)

# population medians of the resampled model vs data, absolute levels
print("\n== absolute medians, resampled model vs data ==")
pred = {k: [] for k in KEYS}
for h in heads:
    acc = {k: [] for k in KEYS}
    for _ in range(2):
        st = fullstats(h["sl"], maker_resamp(h, rng))
        for k in KEYS:
            acc[k].append(st[k])
    for k in KEYS:
        pred[k].append(np.mean(acc[k]))
print(f"{'stat':12s} {'data med':>10s} {'model med':>10s} {'data p10':>10s} {'model p10':>10s} {'data p90':>10s} {'model p90':>10s}")
for k in KEYS:
    d = np.array([h[k] for h in heads])
    m = np.array(pred[k])
    print(f"{k:12s} {np.median(d):10.3f} {np.median(m):10.3f} {np.percentile(d,10):10.3f} {np.percentile(m,10):10.3f} {np.percentile(d,90):10.3f} {np.percentile(m,90):10.3f}")
