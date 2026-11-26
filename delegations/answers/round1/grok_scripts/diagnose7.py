"""Does a symmetric sparse spike on top of diag(t) create err1?"""
import numpy as np
from safetensors.numpy import load_file

PATH = "ensemble_brief/gpt2_model.safetensors"
N, n = 768, 64
rng = np.random.default_rng(6)
wts = load_file(PATH)

def err1_only(sig, W):
    op = np.linalg.norm(W, 2)
    if not np.isfinite(op) or op > 0.999:
        U, s, Vt = np.linalg.svd(W, full_matrices=False)
        W = (U * np.minimum(s, 0.999)) @ Vt
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
    return float(np.linalg.norm(sv - np.sqrt(np.maximum(lp, 0) * np.maximum(lm, 0))) / (np.linalg.norm(sv) + 1e-15))

sigs, diags, offs = [], [], []
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
        sigs.append(sl)
        diags.append(np.diag(W).real.copy())
        offs.append(np.sqrt(np.sum((W - np.diag(np.diag(W))) ** 2) / (n * (n - 1))))

def trial(builder):
    vals = [err1_only(sl, builder(t, off, sl)) for sl, t, off in zip(sigs, diags, offs)]
    return np.median(vals)

def sym_spike(k, c, bulk):
    def build(t, off, sl):
        W = np.diag(t).astype(float)
        if bulk:
            Z = rng.standard_normal((n, n)) * off
            Z = 0.5 * (Z - Z.T)  # pure skew bulk
            np.fill_diagonal(Z, 0)
            W = W + Z
        for _ in range(k):
            i, j = rng.choice(n, 2, replace=False)
            val = c * rng.choice([-1.0, 1.0])
            W[i, j] += val
            W[j, i] += val
        return W
    return build

for k, c, bulk in [
    (0, 0.0, True),
    (8, 0.25, False), (16, 0.25, False), (32, 0.20, False),
    (8, 0.40, False), (16, 0.35, False), (32, 0.30, False),
    (8, 0.40, True), (16, 0.35, True), (32, 0.25, True),
    (64, 0.15, True), (128, 0.10, True),
]:
    print(f"k={k:3d} c={c:.2f} bulk={bulk}  err1={trial(sym_spike(k, c, bulk)):.3f}")

# localized on nearby indices only
def band_sym(k, c, bandwidth):
    def build(t, off, sl):
        W = np.diag(t).astype(float)
        Z = rng.standard_normal((n, n)) * (off * 0.7)
        Z = 0.5 * (Z - Z.T)
        np.fill_diagonal(Z, 0)
        W = W + Z
        for _ in range(k):
            i = rng.integers(0, n)
            j = int(np.clip(i + rng.integers(-bandwidth, bandwidth + 1), 0, n - 1))
            if i == j:
                continue
            val = c * rng.choice([-1.0, 1.0])
            W[i, j] += val
            W[j, i] += val
        return W
    return build

print("--- banded symmetric spikes ---")
for k, c, bw in [(16, 0.35, 4), (32, 0.3, 4), (32, 0.3, 8), (64, 0.2, 8), (16, 0.5, 2)]:
    print(f"k={k:3d} c={c:.2f} bw={bw}  err1={trial(band_sym(k, c, bw)):.3f}")
