# Congruent numbers: a parity lemma for Tunnell's counts, and the quadratic-twist formula

**Files:** `BSDParidad.lean`, `BSDTwist.lean`.

These two results sit next to the Birch and Swinnerton-Dyer conjecture through the
congruent number problem — which squarefree `n` are areas of rational right triangles,
equivalently which curves `E_n : y² = x³ − n²x` have positive rank. **Neither result touches
BSD itself**; both are unconditional statements about the objects that Tunnell's theorem uses.

## 1. Tunnell's counts are always even (`BSDParidad.lean`)

Tunnell's theorem (1983) expresses the parity condition through the number of integer
solutions of `a x² + y² + c z² = n` for `(a, c) ∈ {(2, 32), (2, 8), (4, 32), (4, 8)}`
(with `y` ranging over all integers, and `n` or `n/2` odd and squarefree).

**Lemma (abstract).** A finite set with a fixed-point-free involution has even cardinality.

```lean
theorem even_card_of_fixedPointFree_involution ...
```

**Theorem.** Each of the four Tunnell counts is even (`tunnell_par`).

*Proof.* The map `σ(x, y, z) = (x, −y, z)` preserves the equation (no cross terms) and is an
involution. A fixed point would have `y = 0`, i.e. `n = a x² + c z²`; but in all four cases `a`
and `c` are even, so the right-hand side is even while `n` is odd by hypothesis. Hence `σ` has no
fixed points and the solutions pair off. ∎

This is the kind of fact one usually reads off in a sentence; formalizing it needed the
involution lemma, which we could not find in Mathlib in this form.

## 2. `E_n` is the quadratic twist of `E_1` by `n` (`BSDTwist.lean`)

For a prime `p ∤ 2n`, with `a_p(E) = p + 1 − #E(𝔽_p)`:

```
a_p(E_n) = (n / p) · a_p(E_1)        ((·/p) the Legendre symbol)
```

```lean
theorem a_p_twist ...   -- stated through the character sum a_p = −Σ_x χ(x³ − n²x)
```

*Proof.* Write `a_p(E_n) = −Σ_{x ∈ 𝔽_p} χ(x³ − n² x)` with `χ` the quadratic character
(`χ(0) = 0`, which matches the point count exactly). Substituting `x = n t` — a bijection of
`𝔽_p` since `p ∤ n` — gives `Σ_t χ(n³(t³ − t)) = χ(n)³ Σ_t χ(t³ − t) = χ(n) · Σ_t χ(t³ − t)`,
using `χ(n)² = 1` for `n ≠ 0`. ∎

The formalization uses Mathlib's `quadraticChar (ZMod p)` (with `quadraticChar_dichotomy`
for `χ(n)² = 1`) and reindexes the character sum by the bijection `t ↦ n·t` of `ZMod p`.

![a_p of the twists](../figures/twist_ap.png)

The figure computes `a_p(E_n)` directly by counting for `n = 5, 6, 7` and every prime `p < 200`
and asserts the identity numerically before drawing (the `a_p = 0` at `p ≡ 3 (mod 4)` is the
familiar CM behaviour of `y² = x³ − x`).

## What these give you

Together they are the two ingredients that make Tunnell's criterion computable and
well-defined in a formal setting: the counts have the parity the criterion needs, and the
whole family `E_n` is governed by one curve and one character. The rank statement (BSD) is
untouched.

## References

* J. B. Tunnell, *A classical Diophantine problem and modular forms of weight 3/2*, Invent. Math. 72 (1983), 323–334.
* N. Koblitz, *Introduction to Elliptic Curves and Modular Forms*, Springer GTM 97, Ch. I–II.
