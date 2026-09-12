/-
  SmithDeterminant.lean — el determinante de Smith, CERRADO

  TEOREMA (H.J.S. Smith, 1875, "On the value of a certain arithmetical
  determinant"): para la matriz S_N con S[i][j] = gcd(i,j), 1 ≤ i,j ≤ N,

      det(S_N) = φ(1) · φ(2) · ··· · φ(N)

  donde φ es la función de Euler. Es un teorema REAL, clásico, citable — y,
  hasta donde sabe TRINITY, no está en Mathlib.

  Segundo teorema cerrado de la sesión (el primero fue Redheffer,
  RiemannRedheffer.lean) usando la MISMA maquinaria: reutiliza literalmente
  `Redheffer.zeta` y `Redheffer.det_zeta` (det(ζ)=1) de ese módulo.

  LA DEMOSTRACIÓN (factorización matricial clásica, más corta que Redheffer):
    1. `gcd(i,j) = Σ_{d∣gcd(i,j)} φ(d)` — identidad clásica de Gauss,
       YA EN MATHLIB (`Nat.sum_totient : n.divisors.sum φ = n`).
    2. Traduciendo la suma sobre divisores a una suma sobre Fin N (mismo
       puente que en Redheffer): S[i][j] = Σ_d ζ[d][i]·φ(d)·ζ[d][j], es decir
       S = ζᵀ · diag(φ) · ζ  (`entrada_factorizacion`, `smith_eq_factorizacion`).
    3. Determinante multiplicativo: det(S) = det(ζ)·det(diag φ)·det(ζ)
       = 1·∏φ(i)·1 = ∏φ(i)  (`smith_determinant`).

  #print axioms de cada teorema ⊆ [propext, Classical.choice, Quot.sound].
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic
import RiemannRedheffer
open Matrix Redheffer

namespace Smith

/-- La matriz S_N: S[i][j] = gcd(i+1, j+1) (1-indexado vía Redheffer.zeta). -/
def smith (N : ℕ) : Matrix (Fin N) (Fin N) ℤ :=
  fun i j => (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) : ℤ)

/-- diag(φ(1), φ(2), …, φ(N)). -/
def diagPhi (N : ℕ) : Matrix (Fin N) (Fin N) ℤ :=
  Matrix.diagonal (fun i => (Nat.totient ((i : ℕ) + 1) : ℤ))

/-- diagPhi · ζ escala cada fila d por φ(d+1) — solo la escala si d+1 divide j+1
    (herencia de la estructura de ζ). -/
theorem diagPhi_mul_zeta (N : ℕ) (d j : Fin N) :
    (diagPhi N * zeta N) d j
      = if (d : ℕ) + 1 ∣ (j : ℕ) + 1 then (Nat.totient ((d : ℕ) + 1) : ℤ) else 0 := by
  simp only [Matrix.mul_apply, diagPhi, Matrix.diagonal_apply, zeta]
  have step : (∑ x : Fin N, (if d = x then (Nat.totient ((d : ℕ) + 1) : ℤ) else 0)
        * (if (x : ℕ) + 1 ∣ (j : ℕ) + 1 then (1 : ℤ) else 0))
      = ∑ x : Fin N, (if x = d then
          (if (x : ℕ) + 1 ∣ (j : ℕ) + 1 then (Nat.totient ((d : ℕ) + 1) : ℤ) else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : x = d
    · simp [h]
    · rw [if_neg h, if_neg (fun hh => h hh.symm), zero_mul]
  rw [step, Finset.sum_ite_eq' Finset.univ d]
  simp

/-- Puente Fin N ↔ Nat.divisors para φ (mismo patrón que en Redheffer para μ). -/
theorem fin_sum_eq_divisors_sum_phi (N : ℕ) (m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    (∑ x : Fin N, if (x : ℕ) + 1 ∣ m then (Nat.totient ((x : ℕ) + 1) : ℤ) else 0)
      = ∑ d ∈ Nat.divisors m, (Nat.totient d : ℤ) := by
  rw [Fin.sum_univ_eq_sum_range (fun x => if x + 1 ∣ m then (Nat.totient (x + 1) : ℤ) else 0)]
  rw [← Finset.sum_filter]
  have hset : (Finset.range N).filter (fun i => i + 1 ∣ m) = (Nat.divisors m).image (· - 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨hiN, hdvd⟩
      refine ⟨i + 1, ⟨hdvd, by omega⟩, by omega⟩
    · rintro ⟨d, ⟨hdvd, hmne⟩, hd⟩
      have hdle : d ≤ m := Nat.le_of_dvd (by omega) hdvd
      have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      constructor
      · omega
      · have heq1 : i = d - 1 := hd.symm
        rw [heq1]
        have heq2 : d - 1 + 1 = d := by omega
        rw [heq2]; exact hdvd
  rw [hset, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro d hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    have hmpos : 0 < m := by omega
    have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd hmpos
    have hde : d - 1 + 1 = d := by omega
    rw [hde]
  · intro a ha b hb hab
    simp only at hab
    have hapos : 1 ≤ a := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 (by omega)
    have hbpos : 1 ≤ b := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hb).1 (by omega)
    omega

/-- LA IDENTIDAD ENTRADA A ENTRADA: (ζᵀ · diagPhi · ζ)[i][j] = gcd(i+1,j+1). -/
theorem entrada_factorizacion (N : ℕ) (i j : Fin N) :
    ((zeta N)ᵀ * (diagPhi N * zeta N)) i j = smith N i j := by
  rw [Matrix.mul_apply]
  simp_rw [Matrix.transpose_apply, diagPhi_mul_zeta, zeta]
  have key : (∑ x : Fin N, (if (x : ℕ) + 1 ∣ (i : ℕ) + 1 then (1 : ℤ) else 0)
        * (if (x : ℕ) + 1 ∣ (j : ℕ) + 1 then (Nat.totient ((x : ℕ) + 1) : ℤ) else 0))
      = ∑ x : Fin N,
          (if (x : ℕ) + 1 ∣ Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1)
           then (Nat.totient ((x : ℕ) + 1) : ℤ) else 0) := by
    apply Finset.sum_congr rfl; intro x _
    by_cases h1 : (x : ℕ) + 1 ∣ (i : ℕ) + 1 <;> by_cases h2 : (x : ℕ) + 1 ∣ (j : ℕ) + 1 <;>
      simp [h1, h2, Nat.dvd_gcd_iff]
  rw [key]
  have hgcdpos : 1 ≤ Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hgcdle : Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) ≤ N := by
    have := Nat.gcd_le_left ((j : ℕ) + 1) (show 0 < (i : ℕ) + 1 by omega)
    omega
  rw [fin_sum_eq_divisors_sum_phi N (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1)) hgcdpos hgcdle]
  rw [← Nat.cast_sum, Nat.sum_totient]
  rfl

/-- LA FACTORIZACIÓN MATRICIAL: S = ζᵀ · diag(φ) · ζ. El corazón de la prueba
    clásica de Smith, para TODO N. -/
theorem smith_eq_factorizacion (N : ℕ) :
    smith N = (zeta N)ᵀ * (diagPhi N * zeta N) := by
  ext i j; exact (entrada_factorizacion N i j).symm

theorem det_diagPhi (N : ℕ) :
    (diagPhi N).det = ∏ i : Fin N, (Nat.totient ((i : ℕ) + 1) : ℤ) := by
  unfold diagPhi; exact Matrix.det_diagonal

/-- EL TEOREMA DE SMITH (1875), CERRADO, para TODO N≥1, sin hipótesis:
    det(gcd(i,j))_{i,j=1}^N = φ(1)·φ(2)···φ(N). -/
theorem smith_determinant (N : ℕ) :
    (smith N).det = ∏ i : Fin N, (Nat.totient ((i : ℕ) + 1) : ℤ) := by
  rw [smith_eq_factorizacion, Matrix.det_mul, Matrix.det_transpose, Matrix.det_mul,
      det_zeta, det_diagPhi]
  ring

/-  ── LA GENERALIZACIÓN: Smith no es solo sobre gcd y φ ──

    Smith 1875 es la instancia f=id, g=φ de un hecho más general: si f(n) =
    Σ_{d∣n} g(d) para todo n≥1 (f es la "transformada de sumas de divisores"
    de g — la propiedad que define a φ vía la identidad de Gauss, pero vale
    para cualquier par f,g relacionado así), entonces

        det(f(gcd(i,j)))_{i,j=1}^N = g(1)·g(2)···g(N).

    La prueba es LA MISMA factorización S_f = ζᵀ·diag(g)·ζ, genérica en g —
    ni siquiera hace falta volver a probar nada sobre φ en particular.        -/

/-- Matriz generalizada: S_f[i][j] = f(gcd(i+1,j+1)) para cualquier f : ℕ → ℤ. -/
def smithF (N : ℕ) (f : ℕ → ℤ) : Matrix (Fin N) (Fin N) ℤ :=
  fun i j => f (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1))

def diagG (N : ℕ) (g : ℕ → ℤ) : Matrix (Fin N) (Fin N) ℤ :=
  Matrix.diagonal (fun i => g ((i : ℕ) + 1))

theorem diagG_mul_zeta (N : ℕ) (g : ℕ → ℤ) (d j : Fin N) :
    (diagG N g * zeta N) d j = if (d : ℕ) + 1 ∣ (j : ℕ) + 1 then g ((d : ℕ) + 1) else 0 := by
  simp only [Matrix.mul_apply, diagG, Matrix.diagonal_apply, zeta]
  have step : (∑ x : Fin N, (if d = x then g ((d : ℕ) + 1) else 0)
        * (if (x : ℕ) + 1 ∣ (j : ℕ) + 1 then (1 : ℤ) else 0))
      = ∑ x : Fin N, (if x = d then
          (if (x : ℕ) + 1 ∣ (j : ℕ) + 1 then g ((d : ℕ) + 1) else 0) else 0) := by
    apply Finset.sum_congr rfl; intro x _
    by_cases h : x = d
    · simp [h]
    · rw [if_neg h, if_neg (fun hh => h hh.symm), zero_mul]
  rw [step, Finset.sum_ite_eq' Finset.univ d]
  simp

theorem entrada_factorizacion_general (N : ℕ) (f g : ℕ → ℤ)
    (hyp : ∀ m, 1 ≤ m → f m = ∑ d ∈ Nat.divisors m, g d) (i j : Fin N) :
    ((zeta N)ᵀ * (diagG N g * zeta N)) i j = smithF N f i j := by
  rw [Matrix.mul_apply]
  simp_rw [Matrix.transpose_apply, diagG_mul_zeta N g, zeta]
  have key : (∑ x : Fin N, (if (x : ℕ) + 1 ∣ (i : ℕ) + 1 then (1 : ℤ) else 0)
        * (if (x : ℕ) + 1 ∣ (j : ℕ) + 1 then g ((x : ℕ) + 1) else 0))
      = ∑ x : Fin N,
          (if (x : ℕ) + 1 ∣ Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) then g ((x : ℕ) + 1) else 0) := by
    apply Finset.sum_congr rfl; intro x _
    by_cases h1 : (x : ℕ) + 1 ∣ (i : ℕ) + 1 <;> by_cases h2 : (x : ℕ) + 1 ∣ (j : ℕ) + 1 <;>
      simp [h1, h2, Nat.dvd_gcd_iff]
  rw [key]
  have hgcdpos : 1 ≤ Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hgcdle : Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) ≤ N := by
    have := Nat.gcd_le_left ((j : ℕ) + 1) (show 0 < (i : ℕ) + 1 by omega)
    omega
  have hbridge : (∑ x : Fin N,
        if (x : ℕ) + 1 ∣ Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) then g ((x : ℕ) + 1) else 0)
      = ∑ d ∈ Nat.divisors (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1)), g d := by
    rw [Fin.sum_univ_eq_sum_range
      (fun x => if x + 1 ∣ Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) then g (x + 1) else 0)]
    rw [← Finset.sum_filter]
    set m := Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1)
    have hset : (Finset.range N).filter (fun x => x + 1 ∣ m) = (Nat.divisors m).image (· - 1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Nat.mem_divisors]
      constructor
      · rintro ⟨hxN, hdvd⟩
        refine ⟨x + 1, ⟨hdvd, by omega⟩, by omega⟩
      · rintro ⟨d, ⟨hdvd, hmne⟩, hd⟩
        have hdle : d ≤ m := Nat.le_of_dvd (by omega) hdvd
        have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
        refine ⟨by omega, ?_⟩
        have heq2 : d - 1 + 1 = d := by omega
        rw [hd.symm, heq2]; exact hdvd
    rw [hset, Finset.sum_image]
    · apply Finset.sum_congr rfl; intro d hd
      have hdvd := (Nat.mem_divisors.mp hd).1
      have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hde : d - 1 + 1 = d := by omega
      rw [hde]
    · intro a ha b hb hab
      simp only at hab
      have hapos : 1 ≤ a := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 (by omega)
      have hbpos : 1 ≤ b := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hb).1 (by omega)
      omega
  rw [hbridge, ← hyp _ hgcdpos]
  rfl

theorem smithF_eq_factorizacion (N : ℕ) (f g : ℕ → ℤ)
    (hyp : ∀ m, 1 ≤ m → f m = ∑ d ∈ Nat.divisors m, g d) :
    smithF N f = (zeta N)ᵀ * (diagG N g * zeta N) := by
  ext i j; exact (entrada_factorizacion_general N f g hyp i j).symm

/-- SMITH GENERALIZADO, CERRADO: si f(n) = Σ_{d∣n} g(d) para todo n≥1, entonces
    det(f(gcd(i,j)))_{i,j=1}^N = g(1)·g(2)···g(N). Smith 1875 es el caso f=id,
    g=φ; hay muchos más (ver los corolarios abajo). -/
theorem smithF_determinant (N : ℕ) (f g : ℕ → ℤ)
    (hyp : ∀ m, 1 ≤ m → f m = ∑ d ∈ Nat.divisors m, g d) :
    (smithF N f).det = ∏ i : Fin N, g ((i : ℕ) + 1) := by
  rw [smithF_eq_factorizacion N f g hyp, Matrix.det_mul, Matrix.det_transpose, Matrix.det_mul,
      det_zeta]
  have hdiag : (diagG N g).det = ∏ i : Fin N, g ((i : ℕ) + 1) := by
    unfold diagG; exact Matrix.det_diagonal
  rw [hdiag]; ring

/-- Corolario: Smith clásico, reobtenido del teorema general (no una prueba
    aparte — es la instancia f=id, g=φ, vía la identidad de Gauss). -/
theorem smith_clasico_de_general (N : ℕ) :
    (smithF N (fun n => (n : ℤ))).det = ∏ i : Fin N, (Nat.totient ((i : ℕ) + 1) : ℤ) := by
  apply smithF_determinant N (fun n => (n : ℤ)) (fun n => (Nat.totient n : ℤ))
  intro m hm
  rw [← Nat.cast_sum, Nat.sum_totient]

/-- Corolario, instancia NUEVA: f = σ (suma de divisores), g = id ⟹
    det(σ(gcd(i,j)))_{i,j=1}^N = N!. Verificado en Python (eliminación exacta
    con Fraction) antes de formalizar: N=1..7 da 1,2,6,24,120,720,5040. -/
theorem smith_sigma_de_general (N : ℕ) :
    (smithF N (fun n => (∑ d ∈ Nat.divisors n, d : ℤ))).det
      = ∏ i : Fin N, ((i : ℕ) + 1 : ℤ) := by
  apply smithF_determinant
  intro m hm
  apply Finset.sum_congr rfl
  intro d hd; rfl

/-- Corolario, instancia NUEVA: f = τ (número de divisores), g = 1 (constante)
    ⟹ det(τ(gcd(i,j)))_{i,j=1}^N = 1, para TODO N. g=1 es el caso más simple
    posible de la hipótesis (τ(n) = Σ_{d∣n} 1 es la propia definición de τ vía
    cardinalidad), y el producto ∏ g(i) = ∏ 1 = 1 no depende de N. Verificado
    en Python (eliminación exacta con Fraction) antes de formalizar: N=1..9
    dan todos 1. -/
theorem smith_tau_de_general (N : ℕ) :
    (smithF N (fun n => (n.divisors.card : ℤ))).det = 1 := by
  have h := smithF_determinant N (fun n => (n.divisors.card : ℤ)) (fun _ => (1 : ℤ))
    (by intro m hm; rw [Finset.card_eq_sum_ones]; push_cast; rfl)
  simpa using h

/-  ── σ_k DE MATHLIB: LA FAMILIA COMPLETA, NO SOLO k=1 ──

    σ = suma de divisores es la instancia k=1 de σ_k = suma de k-ésimas
    potencias de divisores (Mathlib: `ArithmeticFunction.sigma`, ya con la
    identidad σ_k(n) = Σ_{d∣n} d^k probada como `sigma_apply` — no hace
    falta reprobarla). Con g(d) = d^k, f = σ_k, el teorema general da

        det(σ_k(gcd(i,j)))_{i,j=1}^N = 1^k · 2^k · ··· · N^k = (N!)^k

    para TODO k, de un tiro — generaliza smith_sigma_de_general (que era la
    instancia k=1, con una suma escrita a mano) citando la σ_k OFICIAL de
    Mathlib en vez de reinventarla.                                        -/

/-- La familia COMPLETA, para todo k: det(σ_k(gcd(i,j)))_{i,j=1}^N = (N!)^k.
    k=1 recupera smith_sigma_de_general (con la σ de Mathlib en vez de la
    suma escrita a mano). Verificado en Python (Fraction exacto) para
    k=0,1,2,3, N=1..6 antes de formalizar. -/
theorem smith_sigmaK_de_general (N k : ℕ) :
    (smithF N (fun n => (ArithmeticFunction.sigma k n : ℤ))).det
      = (∏ i : Fin N, ((i : ℕ) + 1 : ℤ)) ^ k := by
  have h := smithF_determinant N (fun n => (ArithmeticFunction.sigma k n : ℤ))
    (fun d => (d : ℤ) ^ k) (by
      intro m hm
      rw [ArithmeticFunction.sigma_apply]
      push_cast
      rfl)
  rw [h, ← Finset.prod_pow]
  push_cast
  ring

end Smith
