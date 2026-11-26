"""Refit: per-head scales on the two end blocks, Student-t there, Gaussian middle.

Parameters per head: mu, s_t, rho (non-bottom), eta_top, eta_bot.
Global: rho_bot median, nu=5, eta_mid, eta_cross, block sizes 8.
Sigma is the measured spectrum (a covariate).
"""
import os
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["VECLIB_MAXIMUM_THREADS"] = "1"
import json
import numpy as np

n = 64
M_TOP, M_BOT = 8, 8
NU = 5.0
T_SCALE = np.sqrt(NU / (NU - 2.0))
N_DRAWS = 6
SEED = 7

z = np.load("gpt2_raw_stats.npz")
S, W = z["s"], z["W"]
layer, head = z["layer"], z["head"]
H = S.shape[0]
iu = np.triu_indices(n, 1)
ii, jj = iu

def which(i, j):
    a, b = (i, j) if i < j else (j, i)
    if b < M_TOP:
        return 0  # TT
    if a >= n - M_BOT:
        return 1  # BB
    if a >= M_TOP and b < n - M_BOT:
        return 2  # MM
    return 3  # X

reg = np.array([which(int(i), int(j)) for i, j in zip(ii, jj)])
is_bot = reg == 1
is_top = reg == 0
is_mid = reg == 2
is_x = reg == 3

# measured per-head quantities
eta_top = np.zeros(H)
eta_bot = np.zeros(H)
rho_rest = np.zeros(H)
rho_bot_h = np.zeros(H)
q_meas = np.zeros(H)
tbar = np.zeros(H)
tvar = np.zeros(H)
pr = np.zeros(H)
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
    def corr(mask):
        xx, yy = x[mask], y[mask]
        return float(np.sum(xx * yy) / np.sqrt(np.sum(xx ** 2) * np.sum(yy ** 2) + 1e-30))
    eta_top[hi] = rms(is_top)
    eta_bot[hi] = rms(is_bot)
    rho_rest[hi] = corr(~is_bot)
    rho_bot_h[hi] = corr(is_bot)

ETA_MID = float(np.median([
    np.sqrt(np.mean(0.5 * (W[hi][ii, jj][is_mid] ** 2 + W[hi][jj, ii][is_mid] ** 2))) for hi in range(H)]))
ETA_X = float(np.median([
    np.sqrt(np.mean(0.5 * (W[hi][ii, jj][is_x] ** 2 + W[hi][jj, ii][is_x] ** 2))) for hi in range(H)]))
# use each head's own bottom correlation? it's stably near -0.8 except a tail.
# Per-head rho_bot is a 6th parameter. Keep global median for the generator,
# but the head's rho_rest is the predictive parameter.
RHO_BOT = float(np.median(rho_bot_h))
print("eta mid", ETA_MID, "eta x", ETA_X, "rho_bot", RHO_BOT)
print("eta_top med", np.median(eta_top), "eta_bot med", np.median(eta_bot))


def project(M):
    op = np.linalg.norm(M, 2)
    if op > 0.999:
        U, s, Vt = np.linalg.svd(M, full_matrices=False)
        return (U * np.minimum(s, 0.999)) @ Vt
    return M


def sample_W(mu, st, rho, et, eb, rng):
    t = np.clip(mu + st * rng.standard_normal(n), -0.999, 0.999)
    z1 = rng.standard_normal(len(ii))
    z2 = rng.standard_normal(len(ii))
    # student-t scale on the two end blocks, shared within the pair
    chi = rng.chisquare(NU, size=len(ii)) / NU
    scale = np.ones(len(ii))
    end = is_top | is_bot
    scale[end] = (1.0 / np.sqrt(chi[end])) / T_SCALE
    z1 = z1 * scale
    z2 = z2 * scale
    eta = np.empty(len(ii))
    eta[is_top] = et
    eta[is_bot] = eb
    eta[is_mid] = ETA_MID
    eta[is_x] = ETA_X
    rho_p = np.full(len(ii), rho)
    rho_p[is_bot] = RHO_BOT
    E = np.zeros((n, n))
    E[ii, jj] = eta * z1
    E[jj, ii] = eta * (rho_p * z1 + np.sqrt(np.maximum(1 - rho_p ** 2, 0)) * z2)
    return project(np.diag(t) + E)


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
    if len(lp) < n:
        lp = np.pad(lp, (0, n - len(lp)))
    if len(lm) < n:
        lm = np.pad(lm, (0, n - len(lm)))
    sv = np.linalg.svd(T, compute_uv=False)[: 2 * n : 2][:n]
    norm = float(sig @ sig)
    a = float(np.sum(T * T) / norm)
    b = 2 * float(lp @ lm) / norm
    diff = lp - lm
    c = float(np.maximum(diff, 0) @ np.maximum(diff, 0) / norm)
    d = float(np.minimum(diff, 0) @ np.minimum(diff, 0) / norm)
    err = float(np.linalg.norm(sv - np.sqrt(np.maximum(lp * lm, 0))) / (np.linalg.norm(sv) + 1e-30))
    t = np.diag(M)
    off = M.copy()
    np.fill_diagonal(off, 0)
    ent = off[~np.eye(n, dtype=bool)]
    kurt = float(np.mean(ent ** 4) / (np.mean(ent ** 2) ** 2 + 1e-30))
    return dict(err1=err, amb=a - b, cd=c - d, mincd=min(c, d),
                diag=float(np.sum(t ** 2) / (np.sum(M ** 2) + 1e-30)),
                offrms=float(np.sqrt(np.mean(ent ** 2))),
                kurt=kurt,
                pr=float(norm ** 2 / np.sum(sig ** 4)))


KEYS = ["err1", "amb", "cd", "mincd", "diag", "offrms", "kurt", "pr"]
meas = [metrics(S[hi], W[hi]) for hi in range(H)]

def col(rows, k):
    return np.array([r[k] for r in rows])

rng = np.random.default_rng(SEED)
pred = []
rho_f = np.zeros(H)
clip = np.zeros(H)
for hi in range(H):
    sig = S[hi]
    mu = float(tbar[hi])
    st = float(np.sqrt(max(tvar[hi] / max(1 - 1 / pr[hi], 1e-6), 0.0)))
    # rho matched to q, with this head's end scales. Analytic E[q].
    F = float(sig @ sig)
    wgt = 2 * sig[ii] * sig[jj] / F
    eta = np.empty(len(ii))
    eta[is_top] = eta_top[hi]
    eta[is_bot] = eta_bot[hi]
    eta[is_mid] = ETA_MID
    eta[is_x] = ETA_X
    # E[prod] = rho * eta^2 for gaussian; for t, variance is 1 after scaling so same.
    s_bot = float(np.sum(wgt[is_bot] * eta[is_bot] ** 2))
    s_rest = float(np.sum(wgt[~is_bot] * eta[~is_bot] ** 2))
    rho = float(np.clip((q_meas[hi] - RHO_BOT * s_bot) / (s_rest + 1e-15), -0.999, 0.999))
    rho_f[hi] = rho
    clip[hi] = abs(rho) >= 0.999
    acc = []
    for _ in range(N_DRAWS):
        acc.append(metrics(sig, sample_W(mu, st, rho, eta_top[hi], eta_bot[hi], rng)))
    pred.append({k: float(np.mean([r[k] for r in acc])) for k in KEYS})
    if hi % 36 == 0:
        print("fit", hi, flush=True)

def corr(a, b):
    a, b = np.asarray(a, float), np.asarray(b, float)
    if np.std(a) < 1e-12 or np.std(b) < 1e-12:
        return float("nan")
    return float(np.corrcoef(a, b)[0, 1])

print("frac rho clipped", clip.mean())
print(f"{'stat':8s} {'meas med':>10} {'pred med':>10} {'m p10':>10} {'p p10':>10} {'m p90':>10} {'p p90':>10} {'corr':>8}")
out = {}
for k in KEYS:
    m, p = col(meas, k), col(pred, k)
    c = corr(m, p)
    print(f"{k:8s} {np.median(m):10.4f} {np.median(p):10.4f} {np.percentile(m,10):10.4f} {np.percentile(p,10):10.4f} {np.percentile(m,90):10.4f} {np.percentile(p,90):10.4f} {c:8.3f}")
    out[k] = dict(meas_med=float(np.median(m)), pred_med=float(np.median(p)),
                  meas_p10=float(np.percentile(m, 10)), pred_p10=float(np.percentile(p, 10)),
                  meas_p90=float(np.percentile(m, 90)), pred_p90=float(np.percentile(p, 90)), corr=c)

Me, Pe = col(meas, "err1"), col(pred, "err1")
Ma, Pa = col(meas, "amb"), col(pred, "amb")
print("a>b meas", int(np.sum(Ma > 0)), "pred", int(np.sum(Pa > 0)), "sign", float(np.mean(np.sign(Ma) == np.sign(Pa))))
order = np.argsort(-np.abs(Me - Pe))
print("worst err:")
for hi in order[:8]:
    print(f"  L{int(layer[hi])}H{int(head[hi])} meas {Me[hi]:.3f} pred {Pe[hi]:.3f} amb {Ma[hi]:+.3f}/{Pa[hi]:+.3f} et {eta_top[hi]:.3f} eb {eta_bot[hi]:.3f} rho {rho_f[hi]:+.3f}")
json.dump({"out": out, "frac_clip": float(clip.mean()), "eta_mid": ETA_MID, "eta_x": ETA_X,
           "rho_bot": RHO_BOT, "n_pos_pred": int(np.sum(Pa > 0))}, open("fit2_summary.json", "w"), indent=2)
np.savez("fit2_preds.npz", err_m=Me, err_p=Pe, amb_m=Ma, amb_p=Pa, kurt_m=col(meas, "kurt"), kurt_p=col(pred, "kurt"),
         layer=layer, head=head, rho=rho_f, eta_top=eta_top, eta_bot=eta_bot)
print("done")
