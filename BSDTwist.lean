/-
  BSDTwist.lean — la fórmula del twist cuadrático a_p(E_n) = (n|p)·a_p(E_1)

  B-familia-torsion (nivel P, nunca formalizado): cada E_n : y²=x³−n²x es la
  torsión cuadrática de E_1 : y²=x³−x por n, y por tanto

      a_p(E_n) = (n|p) · a_p(E_1)          (símbolo de Legendre, p∤2n)

  DEMOSTRACIÓN (sustitución x=n·t en la suma de caracteres): con
  a_p = −Σ_x χ(x³−n²x) (χ = carácter cuadrático de F_p, χ(0)=0 por
  convención — coincide exactamente con la fórmula de conteo de puntos
  #E(F_p) = p+1+Σχ(f(x))), sustituyendo x=n·t (biyección de F_p porque
  p∤n hace n invertible):

      Σ_x χ(x³−n²x) = Σ_t χ(n³t³−n³t) = Σ_t χ(n³)·χ(t³−t)
                     = χ(n)³ · Σ_t χ(t³−t) = χ(n) · Σ_t χ(t³−t)

  (χ(n)³=χ(n) porque χ(n)∈{−1,1} para n≠0, vía χ(n)²=1). De ahí
  a_p(E_n) = χ(n)·a_p(E_1) directamente.
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

namespace BSDTwist

/-- a_p(E_n) vía la suma de caracteres, coincide con la definición usual
    p+1−#E_n(F_p) (χ(0)=0 hace que cada punto y=0 cuente una vez, cada
    residuo cuadrático no nulo cuenta dos veces — exactamente el conteo). -/
noncomputable def a_p (n : ℤ) (p : ℕ) [Fact p.Prime] : ℤ :=
  -∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - (n : ZMod p) ^ 2 * x)

/-- EL TWIST CUADRÁTICO: a_p(E_n) = χ(n)·a_p(E_1), para todo primo p que no
    divide a n (buena reducción, salvo p=2 que queda fuera por la
    característica de `quadraticChar`). -/
theorem a_p_twist (n : ℤ) (p : ℕ) [Fact p.Prime] (hn : (n : ZMod p) ≠ 0) :
    a_p n p = quadraticChar (ZMod p) (n : ZMod p) * a_p 1 p := by
  have hcube : quadraticChar (ZMod p) ((n : ZMod p) ^ 3) = quadraticChar (ZMod p) (n : ZMod p) := by
    have h3 : (n : ZMod p) ^ 3 = (n : ZMod p) * (n : ZMod p) * (n : ZMod p) := by ring
    rw [h3, map_mul, map_mul]
    rcases quadraticChar_dichotomy hn with h | h <;> rw [h] <;> ring
  unfold a_p
  have hbij : ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - (n : ZMod p) ^ 2 * x)
      = ∑ t : ZMod p, quadraticChar (ZMod p)
          (((n : ZMod p) * t) ^ 3 - (n : ZMod p) ^ 2 * ((n : ZMod p) * t)) :=
    (Equiv.sum_comp (Equiv.mulLeft₀ (n : ZMod p) hn)
      (fun x => quadraticChar (ZMod p) (x ^ 3 - (n : ZMod p) ^ 2 * x))).symm
  rw [hbij]
  have hstep : ∀ t : ZMod p,
      quadraticChar (ZMod p) (((n : ZMod p) * t) ^ 3 - (n : ZMod p) ^ 2 * ((n : ZMod p) * t))
        = quadraticChar (ZMod p) (n : ZMod p) * quadraticChar (ZMod p) (t ^ 3 - t) := by
    intro t
    have heq : ((n : ZMod p) * t) ^ 3 - (n : ZMod p) ^ 2 * ((n : ZMod p) * t)
        = (n : ZMod p) ^ 3 * (t ^ 3 - t) := by ring
    rw [heq, map_mul, hcube]
  simp_rw [hstep]
  rw [← Finset.mul_sum]
  ring

end BSDTwist
