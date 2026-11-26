"""Spectral-block ensemble: fit and predict on all 144 raw GPT-2 heads.

Ensemble (conditional on the measured singular values Sigma):
  t_i = clip(mu + s_t * g_i, -0.999, 0.999), g_i iid N(0,1)
  Off-diagonal pairs are independent.
  Non-bottom pairs: Gaussian, correlation rho (per head),
      scale eta_TT, eta_MM, or eta_X by index region.
  Bottom block (last m=8 modes): variance-mixture (Student-t, nu=5) elliptic
      pairs with a global correlation rho_bot.

Two fits:
  P  rho from the unweighted correlation of non-bottom pairs (predicts q and a-b)
  F  rho chosen so E[q] equals the measured q (a-b partly fitted)
"""
import os
os.environ["OPENBLAS_NUM_THREADS"] = "1"
os.environ["VECLIB_MAXIMUM_THREADS"] = "1"
import json
import numpy as np

n = 64
M_TOP = 8
M_BOT = 8
NU = 5.0
T_SCALE = np.sqrt(NU / (NU - 2.0))  # std of standard_t(nu)
N_DRAWS = 8
SEED = 20261124

z = np.load("gpt2_raw_stats.npz")
S = z["s"]
W = z["W"]
layer = z["layer"]
head = z["head"]
n_heads = S.shape[0]


def region(i, j):
    a, b = (i, j) if i < j else (j, i)
    if b < M_TOP:
        return "TT"
    if a >= n - M_BOT:
        return "BB"
    if a >= M_TOP and b < n - M_BOT:
        return "MM"
    return "X"


# Global scales: median RMS of each region, pooled over heads.
buckets = {k: [] for k in ("TT", "MM", "BB", "X")}
bot_rms = np.zeros(n_heads)
top_rho = np.zeros(n_heads)
rest_rho = np.zeros(n_heads)
bot_rho = np.zeros(n_heads)
q_meas = np.zeros(n_heads)
tbar = np.zeros(n_heads)
tvar = np.zeros(n_heads)
pr = np.zeros(n_heads)
iu = np.triu_indices(n, 1)
for hi in range(n_heads):
    WW = W[hi]
    sig = S[hi]
    x = WW[iu]
    y = WW.T[iu]
    F = float(sig @ sig)
    q_meas[hi] = 2 * float(np.sum(sig[iu[0]] * sig[iu[1]] * x * y)) / F
    w = sig ** 2 / F
    t = np.diag(WW)
    tbar[hi] = float(w @ t)
    tvar[hi] = float(w @ (t - tbar[hi]) ** 2)
    pr[hi] = float(F ** 2 / np.sum(sig ** 4))
    # region lists for this head
    reg = {}
    for k in buckets:
        reg[k] = []
    for p, (i, j) in enumerate(zip(iu[0], iu[1])):
        reg[region(i, j)].append(p)
    for k, idxs in reg.items():
        idxs = np.array(idxs)
        buckets[k].append(np.sqrt(np.mean(0.5 * (x[idxs] ** 2 + y[idxs] ** 2))))
    bb = np.array(reg["BB"])
    bot_rms[hi] = np.sqrt(np.mean(0.5 * (x[bb] ** 2 + y[bb] ** 2)))
    def corr(idxs):
        idxs = np.array(idxs)
        xx, yy = x[idxs], y[idxs]
        return float(np.sum(xx * yy) / np.sqrt(np.sum(xx ** 2) * np.sum(yy ** 2) + 1e-30))
    top_rho[hi] = corr(reg["TT"])
    rest_idx = list(reg["TT"]) + list(reg["MM"]) + list(reg["X"])
    rest_rho[hi] = corr(rest_idx)
    bot_rho[hi] = corr(reg["BB"])

ETA = {k: float(np.median(v)) for k, v in buckets.items()}
RHO_BOT = float(np.median(bot_rho))
print("global eta", {k: round(v, 4) for k, v in ETA.items()})
print("rho_bot median", round(RHO_BOT, 3), "p10-p90", np.percentile(bot_rho, [10, 90]))
print("corr(rest_rho, q)", np.corrcoef(rest_rho, q_meas)[0, 1])
print("corr(top_rho, q)", np.corrcoef(top_rho, q_meas)[0, 1])
print("corr(bot_rms, kurt) will be after")

# eta lookup matrix
eta = np.empty((n, n))
for i in range(n):
    for j in range(n):
        if i == j:
            eta[i, j] = 0.0
        else:
            eta[i, j] = ETA[region(i, j)]

# analytic S_region = sum_{i!=j in region} sig_i sig_j eta^2 / F   (each ordered pair)
def q_coeffs(sig):
    F = float(sig @ sig)
    s_rest = 0.0
    s_bot = 0.0
    for i, j in zip(iu[0], iu[1]):
        term = 2 * sig[i] * sig[j] * eta[i, j] ** 2 / F  # both ordered pairs
        if i >= n - M_BOT:
            s_bot += term
        else:
            s_rest += term
    return s_rest, s_bot


def project(W):
    op = np.linalg.norm(W, 2)
    if op > 0.999:
        U, s, Vt = np.linalg.svd(W, full_matrices=False)
        W = (U * np.minimum(s, 0.999)) @ Vt
    return W


def sample_W(sig, mu, st, rho, rng):
    t = np.clip(mu + st * rng.standard_normal(n), -0.999, 0.999)
    E = np.zeros((n, n))
    # non-bottom gaussian pairs, then bottom t pairs
    for i, j in zip(iu[0], iu[1]):
        if i >= n - M_BOT:
            continue
        z1 = rng.standard_normal()
        z2 = rng.standard_normal()
        E[i, j] = eta[i, j] * z1
        E[j, i] = eta[i, j] * (rho * z1 + np.sqrt(max(1 - rho ** 2, 0)) * z2)
    # bottom block, shared scale mixture so spikes hit both entries
    ii = np.arange(n - M_BOT, n)
    for a in range(len(ii)):
        for b in range(a + 1, len(ii)):
            i, j = int(ii[a]), int(ii[b])
            chi = rng.chisquare(NU) / NU
            scale = 1.0 / np.sqrt(chi) / T_SCALE
            z1 = rng.standard_normal() * scale
            z2 = rng.standard_normal() * scale
            E[i, j] = eta[i, j] * z1
            E[j, i] = eta[i, j] * (RHO_BOT * z1 + np.sqrt(max(1 - RHO_BOT ** 2, 0)) * z2)
    W = np.diag(t) + E
    return project(W)


def metrics(sig, W):
    e, B = np.linalg.eigh(np.eye(n) - W.T @ W)
    R = (B * np.sqrt(np.maximum(e, 0.0))) @ B.T
    L = np.zeros((2 * n, 2 * n))
    L[:n, :n] = sig[:, None] * W.T
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
    t = np.diag(W)
    off = W.copy()
    np.fill_diagonal(off, 0.0)
    ent = off[~np.eye(n, dtype=bool)]
    kurt = float(np.mean(ent ** 4) / (np.mean(ent ** 2) ** 2 + 1e-30))
    offrms = float(np.sqrt(np.mean(ent ** 2)))
    diag = float(np.sum(t ** 2) / (np.sum(W ** 2) + 1e-30))
    pr = float(norm ** 2 / np.sum(sig ** 4))
    x = W[iu]
    y = W.T[iu]
    mag = np.maximum(np.abs(x), np.abs(y))
    top = mag >= np.quantile(mag, 0.95)
    sym = np.abs(x + y) / (np.abs(x) + np.abs(y) + 1e-30)
    return dict(err1=err, amb=a - b, cd=c - d, mincd=min(c, d),
                diag=diag, offrms=offrms, kurt=kurt, pr=pr,
                sym_top=float(np.mean(sym[top])))


# measured metrics for comparison, recomputed with the same function
meas = [metrics(S[hi], W[hi]) for hi in range(n_heads)]
KEYS = ["err1", "amb", "cd", "mincd", "diag", "offrms", "kurt", "pr", "sym_top"]


def corr(a, b):
    a = np.asarray(a, float)
    b = np.asarray(b, float)
    if np.std(a) < 1e-12 or np.std(b) < 1e-12:
        return float("nan")
    return float(np.corrcoef(a, b)[0, 1])


def pack(rows):
    return {k: np.array([r[k] for r in rows]) for k in KEYS}


M = pack(meas)
print("measured err", np.median(M["err1"]), "kurt", np.median(M["kurt"]), "amb", np.median(M["amb"]))
print("corr bot_rms kurt", corr(bot_rms, M["kurt"]))
print("corr rest_rho amb", corr(rest_rho, M["amb"]), "corr top_rho amb", corr(top_rho, M["amb"]))

rng = np.random.default_rng(SEED)
pred_P = []
pred_F = []
rho_P = np.zeros(n_heads)
rho_F = np.zeros(n_heads)
for hi in range(n_heads):
    sig = S[hi]
    mu = float(tbar[hi])
    st = np.sqrt(max(tvar[hi] / max(1 - 1 / pr[hi], 1e-6), 0.0))
    s_rest, s_bot = q_coeffs(sig)
    rho_p = float(np.clip(rest_rho[hi], -0.999, 0.999))
    rho_f = float(np.clip((q_meas[hi] - RHO_BOT * s_bot) / (s_rest + 1e-15), -0.999, 0.999))
    rho_P[hi] = rho_p
    rho_F[hi] = rho_f
    acc_p = []
    acc_f = []
    for d in range(N_DRAWS):
        acc_p.append(metrics(sig, sample_W(sig, mu, st, rho_p, rng)))
        acc_f.append(metrics(sig, sample_W(sig, mu, st, rho_f, rng)))
    pred_P.append({k: float(np.mean([r[k] for r in acc_p])) for k in KEYS})
    pred_F.append({k: float(np.mean([r[k] for r in acc_f])) for k in KEYS})
    if hi % 24 == 0:
        print("fit", hi, flush=True)

PP = pack(pred_P)
FF = pack(pred_F)


def report(name, P):
    print(f"\n== {name} ==")
    print(f"{'stat':8s} {'meas med':>10s} {'pred med':>10s} {'meas p10':>10s} {'pred p10':>10s} {'meas p90':>10s} {'pred p90':>10s} {'corr':>8s}")
    out = {}
    for k in KEYS:
        m, p = M[k], P[k]
        c = corr(m, p)
        print(f"{k:8s} {np.median(m):10.4f} {np.median(p):10.4f} {np.percentile(m,10):10.4f} {np.percentile(p,10):10.4f} {np.percentile(m,90):10.4f} {np.percentile(p,90):10.4f} {c:8.3f}")
        out[k] = dict(meas_med=float(np.median(m)), pred_med=float(np.median(p)),
                      meas_p10=float(np.percentile(m, 10)), pred_p10=float(np.percentile(p, 10)),
                      meas_p90=float(np.percentile(m, 90)), pred_p90=float(np.percentile(p, 90)),
                      corr=c)
    return out

rP = report("P predictive rho from non-bottom pair correlation", PP)
rF = report("F rho matched to q", FF)

# worst heads by err relative error under F and by amb under P
err_abs = np.abs(PP["err1"] - M["err1"])
amb_abs = np.abs(PP["amb"] - M["amb"])
order = np.argsort(-err_abs)
print("\nworst err under P:")
for hi in order[:8]:
    print(f"  L{int(layer[hi])}H{int(head[hi])} meas {M['err1'][hi]:.3f} pred {PP['err1'][hi]:.3f} amb {M['amb'][hi]:+.3f} predamb {PP['amb'][hi]:+.3f} rhoP {rho_P[hi]:+.3f} rhoF {rho_F[hi]:+.3f}")
print("rhoP median", np.median(rho_P), "frac |rhoF| clipped", np.mean(np.abs(rho_F) > 0.99))
print("frac rhoF at clip", np.mean(np.abs(rho_F) >= 0.999))
print("a>b meas", int(np.sum(M["amb"] > 0)), "pred P", int(np.sum(PP["amb"] > 0)), "pred F", int(np.sum(FF["amb"] > 0)))

# how well does P predict the sign of amb
sign_ok = np.mean(np.sign(PP["amb"]) == np.sign(M["amb"]))
print("sign agreement amb P", sign_ok, "F", np.mean(np.sign(FF["amb"]) == np.sign(M["amb"])))

json.dump({"eta": ETA, "rho_bot": RHO_BOT, "nu": NU, "m_top": M_TOP, "m_bot": M_BOT,
           "n_draws": N_DRAWS, "P": rP, "F": rF,
           "rhoP_med": float(np.median(rho_P)),
           "frac_rhoF_clip": float(np.mean(np.abs(rho_F) >= 0.999)),
           "n_pos_meas": int(np.sum(M["amb"] > 0)),
           "n_pos_P": int(np.sum(PP["amb"] > 0)),
           "n_pos_F": int(np.sum(FF["amb"] > 0))},
          open("fit_summary.json", "w"), indent=2)
np.savez("fit_preds.npz", meas=M["err1"], **{f"P_{k}": PP[k] for k in KEYS}, **{f"F_{k}": FF[k] for k in KEYS},
         **{f"M_{k}": M[k] for k in KEYS}, rho_P=rho_P, rho_F=rho_F, layer=layer, head=head)
print("wrote fit_summary.json")
