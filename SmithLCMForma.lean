import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic

/-!
# La forma cerrada que le faltaba al determinante del lcm

`SmithLCM.lean` cerró `det(lcm(i,j)) = (Π k)² · Π gLcm(k)` sin premisas, con
`gLcm n = Σ_{ab=n} μ(a)/b` --- la función que la inversión de Möbius obliga.
Lo que quedó abierto es la **forma cerrada** de esa `g`, que es lo que convierte
el resultado en el clásico de Smith (1875):

    det(lcm(i,j))_{i,j=1}^N = N! · Π_{k≤N} Π_{p|k} (1-p).

Todo se reduce a una identidad: `Σ_{d|n} μ(d)·f(d) = Π_{p|n} (1 - f p)`.

Mathlib la trae en `IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree`
**pero solo para `n` libre de cuadrados**. La grieta se cierra sin maquinaria
nueva, con una observación: `μ d = 0` salvo que `d` sea libre de cuadrados, así
que la suma sobre los divisores de `n` solo ve los divisores libres de cuadrados
--- y esos son exactamente los divisores del **radical** de `n`, que tiene los
mismos primos y sí es libre de cuadrados. `Nat.radical` ya existe en Mathlib con
esa API, así que no hay que definir nada.
-/

open ArithmeticFunction Finset UniqueFactorizationMonoid
open scoped ArithmeticFunction.Moebius

namespace SmithLCMForma

variable {R : Type*} [CommRing R]

/-- Los divisores del radical son exactamente los divisores libres de cuadrados:
    un `d` libre de cuadrados que divide a `n` tiene los mismos primos dentro de
    los de `n`, y por eso divide al producto de todos ellos. -/
theorem dvd_radical_of_squarefree {d n : ℕ} (hn : n ≠ 0) (hd : d ∣ n) (hsq : Squarefree d) :
    d ∣ radical n := by
  rw [Nat.radical_eq_prod_primeFactors]
  have : d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
  rw [this]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono hd hn)

/-- **La identidad, ahora para TODO `n ≥ 1`.**

    `Σ_{d|n} μ(d)·f(d) = Π_{p|n} (1 - f p)`

    Se reduce al radical: los sumandos con `d` no libre de cuadrados valen cero,
    y los que quedan son justo los divisores del radical. -/
theorem sum_moebius_mul_eq_prod_one_sub (f : ArithmeticFunction R)
    (hf : f.IsMultiplicative) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (μ d : R) * f d = ∏ p ∈ n.primeFactors, (1 - f p) := by
  have hrad : radical n ≠ 0 := (Nat.radical_pos n).ne'
  -- (1) la suma sobre n es la suma sobre su radical: lo que sobra tiene mu = 0
  have paso : ∑ d ∈ n.divisors, (μ d : R) * f d
      = ∑ d ∈ (radical n).divisors, (μ d : R) * f d := by
    refine (Finset.sum_subset ?_ ?_).symm
    · exact Nat.divisors_subset_of_dvd hn radical_dvd_self
    · intro d hd hno
      have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
      have : ¬ Squarefree d := by
        intro hsq
        exact hno (Nat.mem_divisors.mpr ⟨dvd_radical_of_squarefree hn hdn hsq, hrad⟩)
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree this]
      simp
  -- (2) sobre el radical, que SI es libre de cuadrados, vale el lema de Mathlib
  rw [paso, ← hf.prodPrimeFactors_one_sub_of_squarefree f squarefree_radical,
      Nat.primeFactors_radical]

/-- La instancia que necesita el determinante del lcm: `f = id` sobre ℚ, es
    decir `Σ_{d|n} μ(d)·d = Π_{p|n} (1-p)`. -/
theorem sum_moebius_mul_id {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (μ d : ℚ) * (d : ℚ)
      = ∏ p ∈ n.primeFactors, (1 - (p : ℚ)) := by
  -- `id` como funcion aritmetica sobre Q es la coercion natCast de la de N.
  have := sum_moebius_mul_eq_prod_one_sub
    (R := ℚ) ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℚ)
    ArithmeticFunction.isMultiplicative_id.natCast hn
  simpa using this

end SmithLCMForma
