"""Surgical tests: which structure in W drives relation (1)?"""
import numpy as np
from safetensors.numpy import load_file

PATH = "ensemble_brief/gpt2_model.safetensors"
wts = load_file(PATH)
N, n = 768, 64
rng = np.random.default_rng(3)

def from_SW(sig, W):
    R2 = np.eye(n) - W.T @ W
    ev, E = np.linalg.eigh(0.5 * (R2 + R2.T))
    ev = np.clip(ev, 1e-15, None)
    R = (E * np.sqrt(ev)) @ E.T
    U = np.concatenate([np.eye(n), np.zeros((n, n))], 0)
    V = np.concatenate([W, R], 0)
    return U @ np.diag(sig) @ V.T

def err1_of(sig, W):
    # guard contraction
    op = np.linalg.norm(W, 2)
    if op > 0.999:
        U, s, Vt = np.linalg.svd(W, full_matrices=False)
        W = (U * np.minimum(s, 0.999)) @ Vt
    L = from_SW(sig, W)
    S = 0.5 * (L + L.T)
    Tm = 0.5 * (L - L.T)
    ev = np.linalg.eigvalsh(S)
    lp = np.sort(ev[ev > 0])[::-1][:n]
    lm = np.sort(-ev[ev < 0])[::-1][:n]
    if len(lp) < n: lp = np.pad(lp, (0, n - len(lp)))
    if len(lm) < n: lm = np.pad(lm, (0, n - len(lm)))
    sv = np.linalg.svd(Tm, compute_uv=False)[: 2 * n : 2][:n]
    return float(np.linalg.norm(sv - np.sqrt(np.maximum(lp, 0) * np.maximum(lm, 0))) / (np.linalg.norm(sv) + 1e-15))

heads = []
for l in range(12):
    Wa = wts[f"h.{l}.attn.c_attn.weight"]
    for h_i in range(12):
        Q = Wa[:, h_i * n:(h_i + 1) * n].T.astype(np.float64)
        K = Wa[:, N + h_i * n:N + (h_i + 1) * n].T.astype(np.float64)
        Uq, sq, Vqh = np.linalg.svd(Q, full_matrices=False)
        Uk, sk, Vkh = np.linalg.svd(K, full_matrices=False)
        Ho = Uk.T @ Uq
        C = Vkh @ Vqh.T
        M = (sk[:, None] * Ho) * sq[None, :]
        P, sl, Sh = np.linalg.svd(M, full_matrices=False)
        W = P.T @ C @ Sh.T
        heads.append((sl, W))

# verify a couple err1 against csv quickly
print("sanity L0H0 err1", err1_of(*heads[0]))

def median_err(transform, trials=1):
    vals = []
    for sl, W in heads:
        acc = []
        for _ in range(trials):
            Wt = transform(sl, W)
            acc.append(err1_of(sl, Wt))
        vals.append(np.mean(acc))
    return np.median(vals), np.percentile(vals, 10), np.percentile(vals, 90)

tests = []

def add(name, fn, trials=1):
    med, p10, p90 = median_err(fn, trials)
    print(f"{name:48s} err1 med={med:.3f}  [{p10:.3f}, {p90:.3f}]")

add("original W", lambda sl, W: W)
add("zero off-diagonal", lambda sl, W: np.diag(np.diag(W)))
add("symmetrize W", lambda sl, W: 0.5 * (W + W.T))
add("skew-symmetrize off + keep diag", lambda sl, W: np.diag(np.diag(W)) + 0.5 * ((W - np.diag(np.diag(W))) - (W - np.diag(np.diag(W))).T))
add("keep symmetric off + diag", lambda sl, W: np.diag(np.diag(W)) + 0.5 * ((W - np.diag(np.diag(W))) + (W - np.diag(np.diag(W))).T))

def shuffle_off(sl, W):
    D = np.diag(W).copy()
    off = W.copy()
    mask = ~np.eye(n, dtype=bool)
    vals = off[mask].copy()
    rng.shuffle(vals)
    off[mask] = vals
    np.fill_diagonal(off, D)
    return off
add("shuffle off-diag entries", shuffle_off, trials=2)

def shuffle_within_band(sl, W, band=8):
    D = np.diag(W).copy()
    out = np.zeros_like(W)
    np.fill_diagonal(out, D)
    mask = ~np.eye(n, dtype=bool)
    # permute among pairs with |i-j|<=band and among the rest separately
    close = mask & (np.abs(np.subtract.outer(np.arange(n), np.arange(n))) <= band)
    far = mask & ~close
    for m in (close, far):
        vals = W[m].copy()
        rng.shuffle(vals)
        out[m] = vals
    return out
add("shuffle near/far separately band=4", lambda sl, W: shuffle_within_band(sl, W, 4), trials=2)
add("shuffle near/far separately band=8", lambda sl, W: shuffle_within_band(sl, W, 8), trials=2)

def keep_topk_off(k):
    def fn(sl, W):
        D = np.diag(W).copy()
        off = W - np.diag(D)
        U, s, Vt = np.linalg.svd(off, full_matrices=False)
        s2 = np.zeros_like(s)
        s2[:k] = s[:k]
        off2 = (U * s2) @ Vt
        return np.diag(D) + off2
    return fn
for k in [1, 2, 4, 8, 16]:
    add(f"diag + top-{k} SVs of off", keep_topk_off(k))

def keep_large_entries(thr_mult):
    def fn(sl, W):
        D = np.diag(W).copy()
        off = W - np.diag(D)
        rms = np.sqrt(np.mean(off ** 2))
        out = off.copy()
        out[np.abs(out) < thr_mult * rms] = 0
        np.fill_diagonal(out, D)
        return out
    return fn
for thr in [1.5, 2.0, 3.0, 4.0]:
    add(f"keep |off| > {thr} * rms", keep_large_entries(thr))

# magnitude pattern: mean |W_ij| by index bin
print("\n=== mean |W_ij|/offrms on a 8x8 index grid (singular-value order) ===")
grid = np.zeros((8, 8))
counts = np.zeros((8, 8))
b = n // 8
sparsity = []
row_pr = []
max_over_rms = []
near_frac = []  # fraction of off mass with |i-j|<=4
for sl, W in heads:
    off = W - np.diag(np.diag(W))
    rms = np.sqrt(np.mean(off ** 2))
    A = np.abs(off) / (rms + 1e-15)
    for i in range(8):
        for j in range(8):
            block = A[i * b:(i + 1) * b, j * b:(j + 1) * b]
            # exclude diagonal block's diagonal? keep it simple, include all
            grid[i, j] += block.mean()
    ent = np.abs(off[~np.eye(n, dtype=bool)])
    ent2 = ent ** 2
    sparsity.append(np.sum(np.sort(ent2)[::-1][: max(1, int(0.05 * ent2.size))]) / ent2.sum())
    # row energy participation
    rn = np.sum(off ** 2, axis=1)
    row_pr.append((rn.sum() ** 2) / (np.sum(rn ** 2) + 1e-30))
    max_over_rms.append(ent.max() / (rms + 1e-15))
    ii, jj = np.indices((n, n))
    mask = np.abs(ii - jj) >= 1
    near = mask & (np.abs(ii - jj) <= 4)
    near_frac.append(np.sum(off[near] ** 2) / np.sum(off[mask] ** 2))

grid /= len(heads)
np.set_printoptions(precision=2, suppress=True, linewidth=120)
print(grid)
print(f"mass in top 5% |entries|: med={np.median(sparsity):.3f}")
print(f"row-energy PR (64=flat): med={np.median(row_pr):.1f}")
print(f"max|off|/rms: med={np.median(max_over_rms):.2f}  p90={np.percentile(max_over_rms,90):.2f}")
print(f"fraction off-mass with |i-j|<=4: med={np.median(near_frac):.3f}")
# baseline: number of pairs with 1<=|i-j|<=4 over n(n-1)
nb_near = np.sum((np.abs(np.subtract.outer(np.arange(n), np.arange(n))) <= 4) & (np.abs(np.subtract.outer(np.arange(n), np.arange(n))) >= 1))
print(f"  random baseline fraction {nb_near / (n * (n - 1)):.3f}")

# Also: correlation of W_ij with (t_i - t_j) etc, and whether W is close to normal (WW* vs W*W)
comms = []
for sl, W in heads:
    comms.append(np.linalg.norm(W @ W.T - W.T @ W) / (np.linalg.norm(W) ** 2 + 1e-15))
print(f"non-normality ||WW*-W*W||/||W||^2 med={np.median(comms):.3f}")
