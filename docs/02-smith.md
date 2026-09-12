# Smith's determinant and its general form

**Files:** `SmithDeterminant.lean` (over `ℤ`), `SmithLCM.lean` (over any commutative ring,
plus the `lcm` matrix), `SmithLCMForma.lean` (closed form of the `lcm` determinant).

## Statement (Smith, 1875)

For the `n × n` matrix `S_n[i][j] = gcd(i, j)`,

```
det S_n = φ(1) · φ(2) · ⋯ · φ(n),
```

with `φ` Euler's totient.

```lean
theorem smith_determinant (N : ℕ) :
    (smith N).det = ∏ i : Fin N, (Nat.totient ((i : ℕ) + 1) : ℤ)
```

![Smith determinant](../figures/smith_determinant.png)

## The general form

Smith's argument works for any `f` applied to `gcd(i, j)`, provided `f` is the divisor sum
of some `g` (that is, `f = g * 1` in the Dirichlet ring, `g = f * μ`):

```lean
theorem smithF_determinant (N : ℕ) (f g : ℕ → ℤ)
    (hyp : ∀ m, 1 ≤ m → f m = ∑ d ∈ Nat.divisors m, g d) :
    (smithF N f).det = ∏ i : Fin N, g ((i : ℕ) + 1)
```

Corollaries recovered from it in the file:

| `f(gcd(i,j))` | `g` | `det` | theorem |
|---|---|---|---|
| `gcd(i,j)` | `φ` | `∏ φ(k)` | `smith_clasico_de_general` |
| `σ(gcd(i,j))` (sum of divisors) | `id` | `n!` | `smith_sigma_de_general` |
| `τ(gcd(i,j))` (number of divisors) | `1` | `1` | `smith_tau_de_general` |
| `σ_k(gcd(i,j))` | `id^k` | `(n!)^k` | `smith_sigmaK_de_general` |

`SmithLCM.lean` proves the same factorization over an arbitrary commutative ring `R`
(`smithR_determinant`) and applies it to the **lcm matrix** `L_n[i][j] = lcm(i, j)` via
`lcm(i,j) = i · j / gcd(i,j)`: `L_n = D · S(1/m) · D` with `D = diag(1, …, n)`, so

```lean
theorem det_lcm (N : ℕ) :
    (lcmMat N).det = (∏ i : Fin N, ((i : ℕ) + 1 : ℚ)) * (∏ i : Fin N, ((i : ℕ) + 1 : ℚ))
                     * ∏ i : Fin N, gLcm ((i : ℕ) + 1)
```

that is, `det L_n = (n!)² · ∏_{k ≤ n} g(k)` with `g = (1/m) * μ`, i.e. `g(k) = Σ_{d ∣ k} μ(d)/d`
(`gLcm_spec`).

## The closed form, and where Mathlib came in

The factor `g(k) = Σ_{d ∣ k} μ(d)/d` for the `lcm` matrix has the closed form
`∏_{p ∣ k} (1 − 1/p)`. This is the identity

```
Σ_{d ∣ n} μ(d) f(d) = ∏_{p ∣ n} (1 − f(p))        (f multiplicative, n ≠ 0)
```

which Mathlib had only for **squarefree** `n`
(`IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree`). `SmithLCMForma.lean` proves it
for every `n ≠ 0` (`sum_moebius_mul_eq_prod_one_sub`): the summands with `d` not squarefree
vanish because `μ(d) = 0`, and the squarefree divisors of `n` are exactly the divisors of
`rad(n)`, which is squarefree with the same prime factors. The Mathlib-ready version, written
without `radical` so that it adds no imports to `Moebius.lean`, is `mathlib-pr/MoebiusProdPR.lean`
and was submitted as [mathlib4#43749](https://github.com/leanprover-community/mathlib4/pull/43749).

## Proof structure (all three files share it)

1. `ζ_n` (divisibility matrix) has `det ζ_n = 1` — reused from `RiemannRedheffer.lean` over `ℤ`,
   reproved over `R` in `SmithLCM.lean` (`det_zetaR`).
2. `S(f) = ζ_nᵀ · diag(g(1), …, g(n)) · ζ_n` entrywise: the `(i, j)` entry of the right-hand side is
   `Σ_{d ∣ i, d ∣ j} g(d) = Σ_{d ∣ gcd(i,j)} g(d) = f(gcd(i,j))` (`entrada_factorizacion`,
   with the same `Fin`-to-`divisors` bridge as in Redheffer).
3. `det` is multiplicative and `det ζ_nᵀ = det ζ_n = 1`, so `det S(f) = ∏ g(k)`.

## References

* H. J. S. Smith, *On the value of a certain arithmetical determinant*, Proc. London Math. Soc. 7 (1875–76), 208–212.
* P. Haukkanen, J. Wang, J. Sillanpää, *On Smith's determinant*, Linear Algebra Appl. 258 (1997) — survey of the `f(gcd)` and `lcm` generalizations.
