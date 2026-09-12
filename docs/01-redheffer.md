# Redheffer's theorem: `det R_n = M(n)`

**File:** `RiemannRedheffer.lean` (main theorem `Redheffer.redheffer_general`).
**Mathlib version:** `mathlib-pr/Redheffer.lean`, submitted as
[mathlib4#43758](https://github.com/leanprover-community/mathlib4/pull/43758).

## Statement

Let `R_n` be the `n × n` matrix with `R_n[i][j] = 1` if `j = 1` or `i ∣ j`, and `0`
otherwise (indices `1..n`). Let `M(n) = Σ_{k ≤ n} μ(k)` be the Mertens function. Then

```
det R_n = M(n)        for every n ≥ 1.
```

In Lean the matrix is `0`-indexed over `Fin n`, so "`i ∣ j`" reads `i + 1 ∣ j + 1`:

```lean
theorem redheffer_general (N : ℕ) : (redheffer (N + 1)).det = mertens (N + 1)
```

## Why it matters, and what it does not say

The Riemann Hypothesis is equivalent to `M(n) = O(n^{1/2+ε})`. Redheffer's identity
turns that growth statement into a statement about the growth of a determinant of a
`0/1` matrix, which is why the matrix appears in the literature on RH (Redheffer 1977;
Barrett–Forcade–Pollington 1988 on its eigenvalues; Vaughan 1993). **The identity itself is
elementary and unconditional.** Nothing here touches the growth of `M(n)`; the figure
below shows `M(n)` staying well inside `±√n` for `n ≤ 120`, which is an observation,
not a theorem.

![det R_n = M(n)](../figures/redheffer_mertens.png)

## Proof, as formalized

The proof follows the classical route through the *zeta matrix* `ζ_n` (entry `1` iff
`i ∣ j`), but avoids computing its inverse:

1. **`det ζ_n = 1`** (`det_zeta`). `i ∣ j` forces `i ≤ j`, so `ζ_n` is upper triangular with
   ones on the diagonal (`zeta_blockTriangular`, then `Matrix.det_of_upperTriangular`).
2. **`R_n` is `ζ_n` with its first column replaced by ones** (`redheffer_eq`). Writing that
   column as `e_1 + (0, 1, …, 1)` and using linearity of the determinant in one column
   (`Matrix.det_updateCol_add`):
   `det R_n = det ζ_n + det ζ'_n = 1 + det ζ'_n`, where `ζ'_n` has first column `(0,1,…,1)`
   (`redheffer_reduccion`).
3. **The crux, `det ζ'_n = M(n) − 1`.** By Cramer's rule (`Matrix.det_smul_inv_mulVec_eq_cramer`),
   replacing the first column of an invertible matrix by `u` gives a determinant equal to
   `(first row of ζ_n⁻¹) · u`. The first row of `ζ_n⁻¹` is `(μ(1), …, μ(n))`: this is the
   matrix form of `Σ_{d ∣ k} μ(d) = [k = 1]`, i.e. `μ * ζ = 1` in the Dirichlet ring, which
   Mathlib provides as `ArithmeticFunction.moebius_mul_coe_zeta` (`vecMul_mu_zeta`,
   `fila_inversa`, `crux_general`). Dotting with `(0, 1, …, 1)` leaves `μ(2) + ⋯ + μ(n) = M(n) − 1`
   (`suma_a_mertens`).

The only bridge lemma of any length is `fin_sum_eq_divisors_sum`: a sum over `Fin n`
with a divisibility indicator equals a sum over `Nat.divisors m` when `1 ≤ m ≤ n`, so
that no divisor escapes the index range.

## Also in the file

* `redheffer_pesada`: the weighted variant with first column `(1, 2, …, n)` has determinant
  `Σ_{k ≤ n} k·μ(k)` (same Cramer argument).
* Concrete instances `redheffer_1/2/3` and `mertens_1/2/3` as anchors (`M(1)=1, M(2)=0, M(3)=−1`).

## Status in the literature

The identity is classical. As far as we could determine (Mathlib search at the time of
writing, and the absence of `mertens`/`redheffer` in Mathlib master), this is the first
formalization in a proof assistant; the Mathlib pull request is under review.

## References

* R. M. Redheffer, *Eine explizit lösbare Optimierungsaufgabe*, ISNM 36 (1977), 213–216.
* W. Barrett, R. Forcade, A. Pollington, *On the spectral radius of a (0,1) matrix related to Mertens' function*, Linear Algebra Appl. 107 (1988).
* R. C. Vaughan, *On the eigenvalues of Redheffer's matrix I*, in *Number Theory with an Emphasis on the Markoff Spectrum* (1993).
