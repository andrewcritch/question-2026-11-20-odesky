"""Independent checks of R13 and the fixed-n limit in R14."""
import itertools
import numpy as np


def block_profile(alpha, beta):
    denominator = np.sum((alpha + beta) ** 2)
    ap, bp = np.sort(alpha)[::-1], np.sort(beta)[::-1]
    return np.array([
        2 * np.dot(alpha, beta),
        2 * np.dot(ap, bp),
        np.sum(np.maximum(ap - bp, 0) ** 2),
        np.sum(np.maximum(bp - ap, 0) ** 2),
    ]) / denominator


count = 0
for values in itertools.product((1., 2., 3.), repeat=6):
    alpha, beta = np.array(values[:3]), np.array(values[3:])
    comonotone = np.all(
        (alpha[:, None] - alpha) * (beta[:, None] - beta) >= 0
    )
    same_dot = np.dot(alpha, beta) == np.dot(np.sort(alpha), np.sort(beta))
    assert same_dot == comonotone
    if comonotone:
        assert np.allclose(
            np.sort(np.sqrt(alpha * beta)),
            np.sqrt(np.sort(alpha) * np.sort(beta)),
        )
        profile = block_profile(alpha, beta)
        assert (profile[3] == 0) == np.all(alpha >= beta)
        assert (profile[2] == 0) == np.all(alpha <= beta)
    count += 1
print(f"R13: {count} positive integer block cases passed, including ties.")


rng = np.random.default_rng(20261124)
n, max_N = 4, 131072
f = np.array([1., 1., 3., 3.])
g = np.array([.5, 1., 1., 2.])
P, M = rng.normal(size=(2, n, max_N))
C = np.block([[np.eye(n), -np.eye(n)], [np.eye(n), -np.eye(n)]])
target = block_profile(f, g)
print("R14 target:", target)
for N in (128, 2048, 32768, max_N):
    rows = np.vstack((np.sqrt(f)[:, None] * P[:, :N],
                      np.sqrt(g)[:, None] * M[:, :N])) / np.sqrt(N)
    H = rows @ rows.T
    eigenvalues, eigenvectors = np.linalg.eigh(H)
    root = (eigenvectors * np.sqrt(eigenvalues)) @ eigenvectors.T
    L = root @ C @ root
    S, T = (L + L.T) / 2, (L - L.T) / 2
    se = np.linalg.eigvalsh(S)
    alpha = se[-n:][::-1]
    beta = -se[:n]
    tau = np.linalg.svd(T, compute_uv=False)[::2]
    norm2 = np.sum(L * L)
    profile = np.array([
        np.sum(T * T), 2 * np.dot(alpha, beta),
        np.sum(np.maximum(alpha - beta, 0) ** 2),
        np.sum(np.maximum(beta - alpha, 0) ** 2),
    ]) / norm2
    error = np.max(np.abs(tau / np.sqrt(alpha * beta) - 1))
    print(f"N={N}: profile max error={max(abs(profile-target)):.7g}, "
          f"relation-(1) max relative error={error:.7g}")


for name, f, g in (
    ("A", np.array([1., 3.]), np.array([1., 1.])),
    ("B", np.array([1., 6.]), np.array([1., 2.])),
):
    print(name, "t:", (f-g)/(f+g), "profile:", block_profile(f, g))
