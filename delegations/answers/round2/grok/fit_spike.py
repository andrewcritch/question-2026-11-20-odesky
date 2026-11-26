"""One-spike-per-end-block ensemble. Kurtosis and profile, 4 draws."""
import os
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["VECLIB_MAXIMUM_THREADS"] = "1"
import json
import numpy as np

n, M_TOP, M_BOT = 64, 8, 8
N_DRAWS, SEED = 4, 11
z = np.load("gpt2_raw_stats.npz")
S, W = z["s"], z["W"]
layer, head = z["layer"], z["head"]
H = len(S)
iu = np.triu_indices(n, 1)
ii, jj = iu

def which(i, j):
    a, b = min(i, j), max(i, j)
    if b < M_TOP: return 0
    if a >= n - M_BOT: return 1
    if a >= M_TOP and b < n - M_BOT: return 2
    return 3
reg = np.array([which(int(i), int(j)) for i, j in zip(ii, jj)])
is_bot, is_top = reg == 1, reg == 0

eta_top = np.zeros(H); eta_bot = np.zeros(H)
rho_rest = np.zeros(H); q_meas = np.zeros(H)
tbar = np.zeros(H); tvar = np.zeros(H); pr = np.zeros(H)
for hi in range(H):
    WW, sig = W[hi], S[hi]
    x, y = WW[ii, jj], WW[jj, ii]
    F = float(sig @ sig)
    w = sig ** 2 / F
    t = np.diag(WW)
    tbar[hi] = float(w @ t)
    tvar[hi] = float(w @ (t - tbar[hi]) ** 2)
    pr[hi] = F ** 2 / np.sum(sig ** 4)
    q_meas[hi] = 2 * float(np.sum(sig[ii] * sig[jj] * x * y)) / F
    def rms(mask):
        return float(np.sqrt(np.mean(0.5 * (x[mask] ** 2 + y[mask] ** 2))))
    eta_top[hi] = rms(is_top); eta_bot[hi] = rms(is_bot)
    xx, yy = x[~is_bot], y[~is_bot]
    rho_rest[hi] = float(np.sum(xx * yy) / np.sqrt(np.sum(xx ** 2) * np.sum(yy ** 2) + 1e-30))

ETA_MID = 0.04381
ETA_X = 0.04252
# background inside an end block sits at the mid scale; excess RMS becomes one pair
def amp(eta_block, n_ent=56):
    # two entries of size A, the rest at ETA_MID
    excess = n_ent * eta_block ** 2 - (n_ent - 2) * ETA_MID ** 2
    return float(np.sqrt(max(excess, 0.0) / 2))

def project(M):
    op = np.linalg.norm(M, 2)
    if op > 0.999:
        U, s, Vt = np.linalg.svd(M, full_matrices=False)
        return (U * np.minimum(s, 0.999)) @ Vt, True
    return M, False

def sample_W(mu, st, rho, A_top, A_bot, sig, rng):
    t = np.clip(mu + st * rng.standard_normal(n), -0.999, 0.999)
    z1 = rng.standard_normal(len(ii))
    z2 = rng.standard_normal(len(ii))
    eta = np.where(is_top | is_bot, ETA_MID, np.where(reg == 2, ETA_MID, ETA_X))
    # end-block background is mid; cross is ETA_X; mid is ETA_MID
    rho_p = np.full(len(ii), rho)
    E = np.zeros((n, n))
    E[ii, jj] = eta * z1
    E[jj, ii] = eta * (rho * z1 + np.sqrt(max(1 - rho * rho, 0)) * z2)
    # one spike on the strongest top pair (0,1), sign of rho; one skew spike on a random bottom pair
    if A_top > 0:
        sgn = 1.0 if rho >= 0 else -1.0
        # random common sign
        g = 1.0 if rng.random() < 0.5 else -1.0
        E[0, 1] = g * A_top
        E[1, 0] = g * sgn * A_top
    if A_bot > 0:
        a = int(rng.integers(n - M_BOT, n - 1))
        b = int(rng.integers(a + 1, n))
        g = 1.0 if rng.random() < 0.5 else -1.0
        E[a, b] = g * A_bot
        E[b, a] = -g * A_bot  # skew, rho_bot ~ -1
    M, clipped = project(np.diag(t) + E)
    return M, clipped

def metrics(sig, M):
    e, B = np.linalg.eigh(np.eye(n) - M.T @ M)
    R = (B * np.sqrt(np.maximum(e, 0.0))) @ B.T
    L = np.zeros((2 * n, 2 * n))
    L[:n, :n] = sig[:, None] * M.T
    L[:n, n:] = sig[:, None] * R
    T = (L - L.T) / 2
    Sm = (L + L.T) / 2
    ev = np.linalg.eigvalsh(Sm)
    lp = np.sort(ev[ev > 0])[::-1][:n]
    lm = np.sort(-ev[ev < 0])[::-1][:n]
    if len(lp) < n: lp = np.pad(lp, (0, n - len(lp)))
    if len(lm) < n: lm = np.pad(lm, (0, n - len(lm)))
    sv = np.linalg.svd(T, compute_uv=False)[:2 * n:2][:n]
    norm = float(sig @ sig)
    a = float(np.sum(T * T) / norm)
    b = 2 * float(lp @ lm) / norm
    diff = lp - lm
    c = float(np.maximum(diff, 0) @ np.maximum(diff, 0) / norm)
    d = float(np.minimum(diff, 0) @ np.minimum(diff, 0) / norm)
    err = float(np.linalg.norm(sv - np.sqrt(np.maximum(lp * lm, 0))) / (np.linalg.norm(sv) + 1e-30))
    off = M.copy(); np.fill_diagonal(off, 0)
    ent = off[~np.eye(n, dtype=bool)]
    kurt = float(np.mean(ent ** 4) / (np.mean(ent ** 2) ** 2 + 1e-30))
    t = np.diag(M)
    return dict(err1=err, amb=a - b, cd=c - d, mincd=min(c, d),
                diag=float(np.sum(t ** 2) / (np.sum(M ** 2) + 1e-30)),
                offrms=float(np.sqrt(np.mean(ent ** 2))), kurt=kurt,
                pr=float(norm ** 2 / np.sum(sig ** 4)))

# measured with same metric
meas = [metrics(S[hi], W[hi]) for hi in range(H)]
KEYS = ["err1", "amb", "cd", "mincd", "diag", "offrms", "kurt", "pr"]
rng = np.random.default_rng(SEED)
pred = []
nclip = 0
for hi in range(H):
    sig = S[hi]
    mu = float(tbar[hi])
    st = float(np.sqrt(max(tvar[hi] / max(1.0 - 1.0 / pr[hi], 1e-6), 0.0)))
    rho = float(np.clip(rho_rest[hi], -0.999, 0.999))
    At, Ab = amp(eta_top[hi]), amp(eta_bot[hi])
    acc = []
    for _ in range(N_DRAWS):
        M, cl = sample_W(mu, st, rho, At, Ab, sig, rng)
        nclip += int(cl)
        acc.append(metrics(sig, M))
    pred.append({k: float(np.mean([r[k] for r in acc])) for k in KEYS})
    if hi % 48 == 0:
        print("fit", hi, "A", round(At, 3), round(Ab, 3), flush=True)

def corr(a, b):
    a, b = np.asarray(a, float), np.asarray(b, float)
    if np.std(a) < 1e-12 or np.std(b) < 1e-12: return float("nan")
    return float(np.corrcoef(a, b)[0, 1])

print("clip fraction", nclip / (H * N_DRAWS))
out = {}
print(f"{'stat':8s} {'meas':>8} {'pred':>8} {'mp10':>8} {'pp10':>8} {'mp90':>8} {'pp90':>8} {'corr':>7}")
for k in KEYS:
    m = np.array([r[k] for r in meas]); p = np.array([r[k] for r in pred])
    c = corr(m, p)
    print(f"{k:8s} {np.median(m):8.4f} {np.median(p):8.4f} {np.percentile(m,10):8.4f} {np.percentile(p,10):8.4f} {np.percentile(m,90):8.4f} {np.percentile(p,90):8.4f} {c:7.3f}")
    out[k] = dict(meas_med=float(np.median(m)), pred_med=float(np.median(p)),
                  meas_p10=float(np.percentile(m,10)), pred_p10=float(np.percentile(p,10)),
                  meas_p90=float(np.percentile(m,90)), pred_p90=float(np.percentile(p,90)), corr=None if c != c else c)
Ma = np.array([r["amb"] for r in meas]); Pa = np.array([r["amb"] for r in pred])
Me = np.array([r["err1"] for r in meas]); Pe = np.array([r["err1"] for r in pred])
print("a>b", int((Ma>0).sum()), "pred", int((Pa>0).sum()), "sign", float(np.mean(np.sign(Ma)==np.sign(Pa))))
order = np.argsort(-np.abs(Me-Pe))[:6]
for hi in order:
    print(f"  L{int(layer[hi])}H{int(head[hi])} err {Me[hi]:.3f}->{Pe[hi]:.3f} amb {Ma[hi]:+.3f}->{Pa[hi]:+.3f}")
json.dump(out, open("fit_spike_summary.json","w"), indent=2)
print("done")
