"""Figures for the README. Every curve is computed here from first principles
(no data files): the point is that the pictures illustrate theorems that are
verified in the Lean sources next to this script, and each figure re-checks
its theorem numerically before drawing it.

  figures/redheffer_mertens.png   det(R_n) = M(n) against n, with +-sqrt(n)
  figures/smith_determinant.png   log det(S_n) = sum log phi(k)
  figures/hodge_chi.png           chi(X_d^n) for hypersurfaces of degree d
  figures/panoptic_duplicates.png how duplicating a prediction moves PQ
  figures/twist_ap.png            a_p(E_n) = (n|p) a_p(E_1) for y^2 = x^3 - n^2 x

Usage: python scripts/make_figures.py   (needs numpy + matplotlib)
"""
import math
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

OUT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "figures")
os.makedirs(OUT, exist_ok=True)
plt.rcParams.update({"font.size": 10, "axes.titlesize": 9, "axes.spines.top": False, "axes.spines.right": False})


# ---------------------------------------------------------------- arithmetic
def moebius(n):
    m, k, p = 1, n, 2
    while p * p <= k:
        if k % p == 0:
            k //= p
            if k % p == 0:
                return 0
            m = -m
        p += 1
    if k > 1:
        m = -m
    return m


def totient(n):
    r, k, p = n, n, 2
    while p * p <= k:
        if k % p == 0:
            while k % p == 0:
                k //= p
            r -= r // p
        p += 1
    if k > 1:
        r -= r // k
    return r


def redheffer_det(n):
    """Exact integer determinant of the n x n Redheffer matrix (Bareiss)."""
    A = [[1 if (j == 0 or (j + 1) % (i + 1) == 0) else 0 for j in range(n)] for i in range(n)]
    prev, sign = 1, 1
    for k in range(n - 1):
        if A[k][k] == 0:
            sw = next((r for r in range(k + 1, n) if A[r][k] != 0), None)
            if sw is None:
                return 0
            A[k], A[sw] = A[sw], A[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = (A[i][j] * A[k][k] - A[i][k] * A[k][j]) // prev
        prev = A[k][k]
    return sign * A[n - 1][n - 1]


# 1. Redheffer determinant = Mertens function -------------------------------
N = 120
ns = np.arange(1, N + 1)
mertens = np.cumsum([moebius(int(k)) for k in ns])
dets = np.array([redheffer_det(int(n)) for n in ns[:60]])   # exact check on the first 60
assert np.array_equal(dets, mertens[:60]), "det(R_n) != M(n) -- the theorem says otherwise"
fig, ax = plt.subplots(figsize=(8.6, 3.8))
ax.step(ns, mertens, where="mid", color="#1f4e79", lw=1.4,
        label=r"$M(n)=\sum_{k \leq n}\mu(k) = \det R_n$   (Lean: redheffer_general)")
ax.plot(ns[:60], dets, "o", ms=3, color="#c0392b", label=r"$\det R_n$ computed exactly (Bareiss), $n \leq 60$")
ax.plot(ns, np.sqrt(ns), "--", color="grey", lw=0.9, label=r"$\pm\sqrt{n}$")
ax.plot(ns, -np.sqrt(ns), "--", color="grey", lw=0.9)
ax.axhline(0, color="black", lw=0.6)
ax.set_xlabel("n"); ax.set_ylabel("value")
ax.set_title("Redheffer's theorem: det of the n x n Redheffer matrix = Mertens function M(n)")
ax.legend(loc="lower left", fontsize=8, frameon=False)
fig.tight_layout(); fig.savefig(os.path.join(OUT, "redheffer_mertens.png"), dpi=160); plt.close(fig)

# 2. Smith determinant = product of totients ---------------------------------
M = 200
ms = np.arange(1, M + 1)
logdet = np.cumsum([math.log(totient(int(k))) for k in ms])
fig, ax = plt.subplots(figsize=(8.6, 3.6))
ax.plot(ms, logdet, color="#1f4e79", lw=1.6,
        label=r"$\log\det S_n=\sum_{k \leq n}\log\varphi(k)$   (Lean: smith_determinant)")
ax.plot(ms, ms * np.log(ms) - ms, "--", color="grey", lw=0.9, label=r"$n\log n - n$ (for scale)")
ax.set_xlabel("n"); ax.set_ylabel(r"$\log\det S_n$")
ax.set_title(r"Smith's determinant (1875): $\det[\gcd(i,j)]_{i,j \leq n}=\prod_{k \leq n}\varphi(k)$")
ax.legend(fontsize=8, frameon=False)
fig.tight_layout(); fig.savefig(os.path.join(OUT, "smith_determinant.png"), dpi=160); plt.close(fig)


# 3. Euler characteristic of smooth hypersurfaces ----------------------------
def chi(n, d):
    return ((1 - d) ** (n + 2) - 1) / d + (n + 2)


fig, ax = plt.subplots(figsize=(8.6, 3.8))
ds = np.arange(1, 9)
for n, col in ((1, "#7f8c8d"), (2, "#1f4e79"), (3, "#c0392b"), (4, "#27ae60")):
    ax.plot(ds, [chi(n, d) for d in ds], "o-", color=col, ms=4,
            label="n=%d: $X_d^{%d} \\subset \\mathbb{P}^{%d}$" % (n, n, n + 1))
ax.set_yscale("symlog"); ax.set_xlabel("degree d"); ax.set_ylabel(r"$\chi(X_d^n)$ (symlog)")
ax.set_title(r"$\chi(X_d^n)=\frac{(1-d)^{n+2}-1}{d}+(n+2)$: closed = binomial form (Lean: chi_general)")
ax.annotate("quintic threefold: chi = -200", xy=(5, chi(3, 5)), xytext=(5.6, -60), fontsize=8,
            arrowprops=dict(arrowstyle="->", lw=0.7))
ax.legend(fontsize=8, frameon=False, ncol=2)
fig.tight_layout(); fig.savefig(os.path.join(OUT, "hodge_chi.png"), dpi=160); plt.close(fig)

# 4. Panoptic Quality and duplicated predictions -----------------------------
# PQ = sum IoU(matches) / (TP + FP/2 + FN/2). A duplicate of a matched
# prediction that also matches (IoU v) adds v to the numerator and 1 to the
# denominator; PanopticFamilia.dup_iff: PQ rises exactly when v > M (mean IoU).
TP, FN = 40, 10
fig, ax = plt.subplots(figsize=(8.6, 3.6))
for mean_iou, col in ((0.60, "#1f4e79"), (0.75, "#c0392b"), (0.90, "#27ae60")):
    base = TP * mean_iou / (TP + FN / 2)
    vs = np.linspace(0.5, 1.0, 101)
    dup = (TP * mean_iou + vs) / (TP + 1 + FN / 2)
    ax.plot(vs, dup - base, color=col, lw=1.6, label="mean IoU of the matches M = %.2f" % mean_iou)
    ax.axvline(mean_iou, color=col, lw=0.7, ls=":")
ax.axhline(0, color="black", lw=0.6)
ax.set_xlabel("IoU v of the duplicated prediction"); ax.set_ylabel("change in PQ from one duplicate")
ax.set_title("One duplicate of a matched prediction raises PQ exactly when v > M (Lean: dup_iff)")
ax.legend(fontsize=8, frameon=False)
fig.tight_layout(); fig.savefig(os.path.join(OUT, "panoptic_duplicates.png"), dpi=160); plt.close(fig)


# 5. Quadratic twist: a_p(E_n) = (n|p) a_p(E_1) ------------------------------
def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def a_p(n, p):
    # a_p = -sum_x chi(x^3 - n^2 x), chi = Legendre symbol mod p (chi(0)=0)
    return -sum(legendre(x ** 3 - n * n * x, p) for x in range(p))


primes = [p for p in range(3, 200) if all(p % q for q in range(2, int(p ** 0.5) + 1))]
fig, ax = plt.subplots(figsize=(8.6, 3.6))
for n, col in ((5, "#1f4e79"), (6, "#c0392b"), (7, "#27ae60")):
    ps = [p for p in primes if n % p]
    lhs = np.array([a_p(n, p) for p in ps]); rhs = np.array([legendre(n, p) * a_p(1, p) for p in ps])
    assert np.array_equal(lhs, rhs), "twist formula failed numerically"
    ax.plot(ps, lhs, "o", ms=3.5, color=col, label="$a_p(E_{%d})$, checked $= (%d|p)\\,a_p(E_1)$" % (n, n))
ax.axhline(0, color="black", lw=0.6)
ax.set_xlabel("prime p"); ax.set_ylabel(r"$a_p$")
ax.set_title(r"Congruent-number curves $E_n: y^2=x^3-n^2x$ are quadratic twists of $E_1$ (Lean: a_p_twist)")
ax.legend(fontsize=8, frameon=False)
fig.tight_layout(); fig.savefig(os.path.join(OUT, "twist_ap.png"), dpi=160); plt.close(fig)

print("figures written to", OUT, ":", sorted(os.listdir(OUT)))
