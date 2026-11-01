/-
  BSDDeuring.lean — Deuring's vanishing: a_p(E_n) = 0 for every p ≡ 3 (mod 4)

  The congruent-number curves E_n : y² = x³ − n²x are supersingular at every prime
  p ≡ 3 (mod 4) of good reduction. With the character-sum definition of a_p already
  used in BSDTwist.lean (a_p = −Σ_x χ(x³ − n²x), which for p ∤ 2n is exactly the point
  count #E_n(F_p) = p + 1 + Σ_x χ(x³ − n²x)), the whole statement is that the sum
  vanishes, and the proof is elementary:

      x ↦ −x is a bijection of F_p, so  S = Σ_x χ(f(−x));
      f(x) = x³ − n²x is ODD, so  χ(f(−x)) = χ(−1)·χ(f(x));
      for p ≡ 3 (mod 4), −1 is a non-residue, so  χ(−1) = −1;
      hence  S = −S,  2S = 0,  S = 0  and  a_p = 0.

  Nothing is assumed: the bijection is `Equiv.neg`, and χ(−1) = −1 is Mathlib's
  `quadraticChar_neg_one` together with `ZMod.χ₄_nat_three_mod_four`.

  The argument has nothing to do with the curve, so it is stated where it lives: over
  ANY finite field in which −1 is a non-square, the quadratic character sum of ANY odd
  function vanishes (`sum_quadraticChar_comp_eq_zero_of_odd`). The curve family is one
  instance of it, and `p ≡ 3 (mod 4)` is one way to have −1 a non-square.

  Together with `BSDTwist.a_p_twist` this closes the supersingular half of the
  congruent-number curves: half of all primes contribute nothing to the trace.
-/
import Mathlib.Tactic
import Mathlib.Algebra.Group.EvenFunction
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import BSDTwist

namespace BSDDeuring

section Field

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem sum_quadraticChar_comp_eq_mul_of_odd {f : F → F} (hf : Function.Odd f) :
    ∑ x : F, quadraticChar F (f x) = quadraticChar F (-1) * ∑ x : F, quadraticChar F (f x) :=
  calc ∑ x : F, quadraticChar F (f x)
    _ = ∑ x : F, quadraticChar F (f (-x)) :=
        (Fintype.sum_equiv (Equiv.neg F) _ _ fun _ => rfl).symm
    _ = ∑ x : F, quadraticChar F (-1) * quadraticChar F (f x) :=
        Finset.sum_congr rfl fun x _ => by
          rw [hf x, show -f x = (-1) * f x by ring, map_mul]
    _ = quadraticChar F (-1) * ∑ x : F, quadraticChar F (f x) := (Finset.mul_sum ..).symm

/-- If `−1` is a non-square in a finite field `F`, the quadratic character sum of an
**odd** function vanishes: reindexing by `x ↦ −x` pairs each value with its negative. -/
theorem sum_quadraticChar_comp_eq_zero_of_odd (hF : quadraticChar F (-1) = -1) {f : F → F}
    (hf : Function.Odd f) : ∑ x : F, quadraticChar F (f x) = 0 := by
  have h := sum_quadraticChar_comp_eq_mul_of_odd hf
  rw [hF] at h
  linarith

end Field

variable (p : ℕ) [Fact p.Prime]

theorem quadraticChar_neg_one_of_three_mod_four (hp : p % 4 = 3) :
    quadraticChar (ZMod p) (-1) = -1 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  rw [quadraticChar_neg_one hF, ZMod.card p, ZMod.χ₄_nat_three_mod_four hp]

/-- **Deuring's vanishing** for the congruent-number curves: for every integer `n` and
every prime `p ≡ 3 (mod 4)`, the character sum of `E_n : y² = x³ − n²x` is zero.

For `p ∤ 2n` that sum is `−a_p`, so the trace of Frobenius vanishes, `#E_n(F_p) = p + 1`
and `E_n` is supersingular at `p`. For `p ∣ n` the statement is still true but says
nothing about a curve: `E_n` reduces to the singular `y² = x³`, and there the sum
vanishes for every odd `p`, since `χ(x³) = χ(x)` and `∑ χ = 0`. -/
theorem a_p_eq_zero (n : ℤ) (hp : p % 4 = 3) : BSDTwist.a_p n p = 0 := by
  rw [BSDTwist.a_p,
    sum_quadraticChar_comp_eq_zero_of_odd (quadraticChar_neg_one_of_three_mod_four p hp)
      fun x => by ring,
    neg_zero]

theorem a_p_one_eq_zero (hp : p % 4 = 3) : BSDTwist.a_p 1 p = 0 := a_p_eq_zero p 1 hp

end BSDDeuring
