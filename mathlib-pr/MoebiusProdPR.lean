import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Borrador del PR a Mathlib: `prodPrimeFactors_one_sub` para todo `n`

Mathlib tiene `IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree`:

    ∏ p ∈ n.primeFactors, (1 - f p) = ∑ d ∈ n.divisors, μ d * f d      (n libre de cuadrados)

La hipótesis de libre de cuadrados sobra: `μ d = 0` fuera de los divisores
libres de cuadrados, y esos son exactamente los divisores de
`∏ p ∈ n.primeFactors, p` (el radical, sin importar `RingTheory.Radical`).

Este fichero importa **exactamente lo que importa `Moebius.lean`** para
comprobar que el teorema entraría en ese fichero sin añadir ninguna dependencia.
Enunciado con la orientación y el nombre que usa Mathlib.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

namespace ArithmeticFunction

variable {R : Type*} [CommRing R]

/-- Un divisor libre de cuadrados de `n` divide al producto de los primos de `n`. -/
theorem _root_.Nat.Squarefree.dvd_prod_primeFactors {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n)
    (hsq : Squarefree d) : d ∣ ∏ p ∈ n.primeFactors, p := by
  calc d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
    _ ∣ ∏ p ∈ n.primeFactors, p :=
        Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono hd hn)

/-- `∏ p ∈ n.primeFactors, (1 - f p) = ∑ d ∈ n.divisors, μ d * f d` for every `n ≠ 0`.

This generalises `prodPrimeFactors_one_sub_of_squarefree`: the summands with
`d` not squarefree vanish, and the squarefree divisors of `n` are exactly the
divisors of `∏ p ∈ n.primeFactors, p`, which is squarefree with the same prime
factors. -/
theorem IsMultiplicative.prodPrimeFactors_one_sub (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, (1 - f p) = ∑ d ∈ n.divisors, μ d * f d := by
  set P := ∏ p ∈ n.primeFactors, p with hP
  have hPsq : Squarefree P := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ fun p hp ↦
      (Nat.mem_primeFactors.mp hp).1.prime.squarefree
    intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hq).1).mpr hpq)
  have hP0 : P ≠ 0 := hPsq.ne_zero
  have hsum : ∑ d ∈ n.divisors, (μ d : R) * f d = ∑ d ∈ P.divisors, (μ d : R) * f d := by
    refine (Finset.sum_subset (Nat.divisors_subset_of_dvd hn (Nat.prod_primeFactors_dvd n))
      fun d hd hno ↦ ?_).symm
    have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
    have : ¬ Squarefree d := fun hsq ↦
      hno (Nat.mem_divisors.mpr ⟨Nat.Squarefree.dvd_prod_primeFactors hn hdn hsq, hP0⟩)
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree this]
  rw [hsum, ← hf.prodPrimeFactors_one_sub_of_squarefree f hPsq, hP,
    Nat.primeFactors_prod_primeFactors]

end ArithmeticFunction
