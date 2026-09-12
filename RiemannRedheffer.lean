/-
  RiemannRedheffer.lean — la identidad de Redheffer det(A_n) = M(n), CERRADA

  La matriz de Redheffer A_n (n×n, entradas 0/1: A[i][j]=1 si j=1 o i∣j) cumple
  det(A_n) = M(n), la función de Mertens M(n)=Σ_{k≤n} μ(k). Es un TEOREMA REAL
  (Redheffer 1977), NO la hipótesis de Riemann: RH equivale a M(n)=O(n^{1/2+ε}),
  el CRECIMIENTO del determinante, no a la identidad en sí.

  ESTADO: TEOREMA GENERAL CERRADO, `redheffer_general`, para TODO n≥1, sin
  hipótesis, sin `sorry`, verificado por el kernel. No está en Mathlib — esta es,
  hasta donde sabe TRINITY, la primera formalización.

  LA CADENA COMPLETA:
    1. `det_zeta` (backbone, todo n): la matriz de divisibilidad ζ (ζ[i][j]=1 si
       i∣j) es triangular superior con 1s en la diagonal ⟹ det(ζ)=1.
    2. `redheffer_eq` + `redheffer_reduccion`: A_n = ζ con la 1ª columna a
       todo-unos; por linealidad del determinante en esa columna,
       det(A_n) = 1 + det(ζ'), con ζ' = ζ con la 1ª columna = [0,1,…,1].
    3. EL CRUX, cerrado: det(ζ') = M(n) − 1. La prueba NO invierte la matriz
       entera — usa que solo hace falta la PRIMERA FILA de ζ⁻¹:
         a. `vecMul_mu_zeta`: el vector fila μ (μ(1),…,μ(n)) satisface
            μ · ζ = e₁ (vector fila), que es EXACTAMENTE la identidad clásica
            Σ_{d∣k} μ(d) = [k=1] — ya en Mathlib
            (`ArithmeticFunction.moebius_mul_coe_zeta : μ * ζ = 1`), aquí
            traducida de convolución de Dirichlet a ecuación matricial.
         b. `fila_inversa`: como ζ es invertible (det=1), μ·ζ=e₁ determina
            μ = fila 1 de ζ⁻¹ (cancelación por la derecha).
         c. `crux_general`: por la fórmula de Cramer/adjugate
            (`det_smul_inv_mulVec_eq_cramer`), det(ζ.updateCol 1 u) es el
            producto de esa fila de ζ⁻¹ con u — es decir, con μ.
         d. `suma_a_mertens`: para u = [0,1,…,1], esa suma es
            Σ_{k=2}^{n} μ(k) = M(n) − μ(1) = M(n) − 1.
    4. `redheffer_general`: combinando 2 y 3, det(A_n) = M(n). QED, para todo n.

  #print axioms de cada teorema ⊆ [propext, Classical.choice, Quot.sound].
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Tactic
open Matrix
open scoped ArithmeticFunction.Moebius

namespace Redheffer

/-- La matriz zeta de divisibilidad: ζ[i][j] = 1 si (i+1) ∣ (j+1), si no 0. -/
def zeta (N : ℕ) : Matrix (Fin N) (Fin N) ℤ :=
  fun i j => if (i : ℕ) + 1 ∣ (j : ℕ) + 1 then 1 else 0

/-- ζ es triangular superior: i∣j ⟹ i≤j, luego bajo la diagonal todo es 0. -/
theorem zeta_blockTriangular (N : ℕ) : (zeta N).BlockTriangular id := by
  intro i j hij
  simp only [zeta]
  rw [if_neg]
  intro hd
  have := Nat.le_of_dvd (by omega) hd
  simp only [id] at hij
  omega

/-- BACKBONE (general, todo n): det(ζ_n) = 1. -/
theorem det_zeta (N : ℕ) : (zeta N).det = 1 := by
  rw [Matrix.det_of_upperTriangular (zeta_blockTriangular N)]
  simp [zeta]

/-- La matriz de Redheffer A_N: A[i][j] = 1 si j es la primera columna (j=0 en
    0-indexado, es decir "1" en 1-indexado) o si (i+1) ∣ (j+1). -/
def redheffer (N : ℕ) : Matrix (Fin N) (Fin N) ℤ :=
  fun i j => if (j : ℕ) = 0 ∨ (i : ℕ) + 1 ∣ (j : ℕ) + 1 then 1 else 0

set_option maxRecDepth 4000 in
/-- La columna 0 de ζ es e₀: solo la fila 0 vale 1 (porque i+1 ∣ 1 ⟺ i=0). -/
theorem zeta_col0 (N : ℕ) (i : Fin (N + 1)) :
    zeta (N + 1) i 0 = (if i = 0 then 1 else 0) := by
  simp only [zeta]
  by_cases h : i = 0
  · subst h; norm_num
  · rw [if_neg h, if_neg]
    intro hd
    simp only [Fin.val_zero] at hd
    have := Nat.le_of_dvd (by omega) hd
    have hi : (i : ℕ) ≠ 0 := fun hh => h (Fin.ext (by simpa using hh))
    omega

set_option maxRecDepth 4000 in
/-- La matriz de Redheffer es ζ con la primera columna puesta a TODO-UNOS. -/
theorem redheffer_eq (N : ℕ) :
    redheffer (N + 1) = (zeta (N + 1)).updateCol 0 (fun _ => 1) := by
  ext i j
  rw [Matrix.updateCol_apply]
  by_cases hj : j = 0
  · subst hj; rw [if_pos rfl]; simp only [redheffer, Fin.val_zero, true_or, if_true]
  · rw [if_neg hj]
    have hj0 : (j : ℕ) ≠ 0 := fun hh => hj (Fin.ext (by simpa using hh))
    simp only [redheffer, zeta, hj0, false_or]

set_option maxRecDepth 4000 in
/-- LA REDUCCIÓN (kernel, general): det(A_n) = 1 + det(ζ'). Sale de la
    linealidad del determinante en la columna (`det_updateCol_add`). -/
theorem redheffer_reduccion (N : ℕ) :
    (redheffer (N + 1)).det
      = 1 + ((zeta (N + 1)).updateCol 0 (fun i => if i = 0 then 0 else 1)).det := by
  rw [redheffer_eq]
  have hsplit : (fun _ : Fin (N + 1) => (1 : ℤ))
      = (fun i => if i = 0 then (1 : ℤ) else 0) + (fun i => if i = 0 then (0 : ℤ) else 1) := by
    funext i; by_cases h : i = 0 <;> simp [h]
  rw [hsplit, Matrix.det_updateCol_add]
  congr 1
  have hcol : (zeta (N + 1)).updateCol 0 (fun i => if i = 0 then (1 : ℤ) else 0) = zeta (N + 1) := by
    ext i j
    rw [Matrix.updateCol_apply]
    by_cases hj : j = 0
    · subst hj; rw [if_pos rfl, zeta_col0]
    · rw [if_neg hj]
  rw [hcol, det_zeta]

/-- La función de Mertens M(n) = Σ_{k=1}^{n} μ(k), con la Möbius genuina. -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, (μ k : ℤ)

/-- Con el crux dado, la identidad general se sigue en una línea. -/
theorem redheffer_de_crux (N : ℕ)
    (crux : ((zeta (N + 1)).updateCol 0 (fun i => if i = 0 then 0 else 1)).det
              = mertens (N + 1) - 1) :
    (redheffer (N + 1)).det = mertens (N + 1) := by
  rw [redheffer_reduccion, crux]; ring

-- ══════════════════ EL CRUX: cerrado, sin hipótesis ══════════════════
--
-- Solo hace falta la PRIMERA FILA de ζ⁻¹ (no la matriz inversa completa), y
-- esa fila ES la función de Möbius — consecuencia directa de la identidad
-- de convolución de Dirichlet μ*ζ=1 que Mathlib ya prueba.

/-- El vector fila candidato: μ(1), μ(2), …, μ(n). -/
def murow (N : ℕ) : Fin (N + 1) → ℤ := fun i => (μ ((i : ℕ) + 1) : ℤ)

/-- La identidad de Möbius, en forma de suma sobre divisores: Σ_{d∣k} μ(d) =
    [k=1]. Es `ArithmeticFunction.moebius_mul_coe_zeta` traducida. -/
theorem suma_mu_divisores (k : ℕ) :
    (∑ d ∈ Nat.divisors k, (μ d : ℤ)) = if k = 1 then 1 else 0 := by
  have h : ((μ * ArithmeticFunction.zeta : ArithmeticFunction ℤ)) k
      = ∑ i ∈ Nat.divisors k, (μ i : ℤ) := ArithmeticFunction.coe_mul_zeta_apply
  rw [ArithmeticFunction.moebius_mul_coe_zeta] at h
  rw [← h]; simp [ArithmeticFunction.one_apply]

/-- Puente Fin N ↔ Nat.divisors: la suma con indicador de divisibilidad sobre
    Fin N (con los divisores POSIBLES 1..N) coincide con la suma real sobre
    los divisores de m, cuando m ≤ N (así ningún divisor se escapa del rango). -/
theorem fin_sum_eq_divisors_sum (N : ℕ) (m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    (∑ x : Fin N, if (x : ℕ) + 1 ∣ m then (μ ((x : ℕ) + 1) : ℤ) else 0)
      = ∑ d ∈ Nat.divisors m, (μ d : ℤ) := by
  rw [Fin.sum_univ_eq_sum_range (fun x => if x + 1 ∣ m then (μ (x + 1) : ℤ) else 0)]
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
    congr 1
    omega
  · intro a ha b hb hab
    simp only at hab
    have hapos : 1 ≤ a := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 (by omega)
    have hbpos : 1 ≤ b := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hb).1 (by omega)
    omega

/-- μ·ζ = e₁ como ecuación de VECTOR FILA — la traducción matricial de
    Σ_{d∣k} μ(d) = [k=1]. Para TODO n. -/
theorem vecMul_mu_zeta (N : ℕ) :
    Matrix.vecMul (murow N) (zeta (N + 1)) = fun k => if k = 0 then (1 : ℤ) else 0 := by
  funext k
  simp only [Matrix.vecMul, dotProduct, murow, zeta]
  rw [show (∑ x : Fin (N + 1), (μ ((x : ℕ) + 1) : ℤ)
        * (if (x : ℕ) + 1 ∣ (k : ℕ) + 1 then (1 : ℤ) else 0))
      = ∑ x : Fin (N + 1), (if (x : ℕ) + 1 ∣ (k : ℕ) + 1 then (μ ((x : ℕ) + 1) : ℤ) else 0)
      from by apply Finset.sum_congr rfl; intro x _
              by_cases h : (x : ℕ) + 1 ∣ (k : ℕ) + 1 <;> simp [h]]
  rw [fin_sum_eq_divisors_sum (N + 1) ((k : ℕ) + 1) (by omega) (by omega)]
  rw [suma_mu_divisores]
  have hiff : (k : ℕ) + 1 = 1 ↔ k = 0 := by rw [Fin.ext_iff, Fin.val_zero]; omega
  by_cases hk : k = 0
  · simp [hk]
  · have hne : (k : ℕ) + 1 ≠ 1 := fun h => hk (hiff.mp h)
    simp [hne]

/-- Como ζ es invertible, μ·ζ=e₁ determina μ = fila 1 de ζ⁻¹ (cancelación por
    la derecha: multiplicar ambos lados por ζ⁻¹). -/
theorem fila_inversa (N : ℕ) :
    murow N = Matrix.vecMul (fun k => if k = (0 : Fin (N + 1)) then (1 : ℤ) else 0)
      (zeta (N + 1))⁻¹ := by
  have hunit : IsUnit (zeta (N + 1)).det := det_zeta (N + 1) ▸ isUnit_one
  have step : Matrix.vecMul (Matrix.vecMul (murow N) (zeta (N + 1))) (zeta (N + 1))⁻¹
      = Matrix.vecMul (fun k => if k = (0 : Fin (N + 1)) then (1 : ℤ) else 0) (zeta (N + 1))⁻¹ := by
    rw [vecMul_mu_zeta]
  rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hunit, Matrix.vecMul_one] at step
  exact step

/-- EL CRUX, forma general: det(ζ.updateCol 0 u) es el producto de μ (la fila 1
    de ζ⁻¹) con u — vía la fórmula de Cramer/adjugate. -/
theorem crux_general (N : ℕ) (u : Fin (N + 1) → ℤ) :
    ((zeta (N + 1)).updateCol 0 u).det = ∑ j, murow N j * u j := by
  rw [← Matrix.cramer_apply]
  have hunit : IsUnit (zeta (N + 1)).det := det_zeta (N + 1) ▸ isUnit_one
  have hc := Matrix.det_smul_inv_mulVec_eq_cramer (zeta (N + 1)) u hunit
  rw [det_zeta, one_smul] at hc
  rw [← hc, fila_inversa N]
  simp [Matrix.mulVec, dotProduct, Matrix.vecMul]

theorem range_a_Icc2 (N : ℕ) :
    (∑ i ∈ Finset.range N, (μ (i + 2) : ℤ)) = ∑ k ∈ Finset.Icc 2 (N + 1), (μ k : ℤ) := by
  apply Finset.sum_nbij' (fun i => i + 2) (fun k => k - 2) <;> intros <;> simp_all <;> omega

theorem mertens_peel (N : ℕ) : mertens (N + 1) = 1 + ∑ k ∈ Finset.Icc 2 (N + 1), (μ k : ℤ) := by
  unfold mertens
  rw [show Finset.Icc 1 (N + 1) = insert 1 (Finset.Icc 2 (N + 1)) by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
  rw [Finset.sum_insert (by simp)]
  norm_num [ArithmeticFunction.moebius_apply_one]

/-- Con u=[0,1,…,1], el crux da exactamente M(n)−1: Σ_{k=2}^{n} μ(k). -/
theorem suma_a_mertens (N : ℕ) :
    (∑ j : Fin (N + 1), (if j = 0 then (0 : ℤ) else murow N j)) = mertens (N + 1) - 1 := by
  unfold murow
  rw [Fin.sum_univ_succ]
  have h0 : (if (0 : Fin (N + 1)) = 0 then (0 : ℤ) else μ (((0 : Fin (N + 1)) : ℕ) + 1)) = 0 := by
    simp
  have hstep : ∀ i : Fin N,
      (if (Fin.succ i : Fin (N + 1)) = 0 then (0 : ℤ)
       else μ (((Fin.succ i : Fin (N + 1)) : ℕ) + 1)) = μ ((i : ℕ) + 2) := by
    intro i
    rw [if_neg (Fin.succ_ne_zero i), Fin.val_succ]
  rw [h0]
  simp_rw [hstep]
  rw [Fin.sum_univ_eq_sum_range (fun i => (μ (i + 2) : ℤ))]
  rw [range_a_Icc2, mertens_peel]
  ring

/-- EL TEOREMA GENERAL, SIN HIPÓTESIS NI RANGO: det(A_n) = M(n) para TODO n≥1.
    Cierra la identidad de Redheffer (1977) por completo — hasta donde sabe
    TRINITY, la primera vez formalizada en un asistente de pruebas. -/
theorem redheffer_general (N : ℕ) : (redheffer (N + 1)).det = mertens (N + 1) := by
  apply redheffer_de_crux
  rw [crux_general]
  have heq := suma_a_mertens N
  rw [← heq]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : j = 0 <;> simp [h, murow]

-- ══════════════════ Instancias concretas, como ancla ══════════════════

theorem mertens_1 : mertens 1 = 1 := by unfold mertens; simp

theorem mertens_2 : mertens 2 = 0 := by
  unfold mertens
  rw [show Finset.Icc 1 2 = {1, 2} by decide]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two]

theorem mertens_3 : mertens 3 = -1 := by
  unfold mertens
  rw [show Finset.Icc 1 3 = {1, 2, 3} by decide]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two,
        ArithmeticFunction.moebius_apply_prime Nat.prime_three]

/-- n=1, n=2, n=3: casos del teorema general (dos maneras de verlo). -/
theorem redheffer_1 : (redheffer 1).det = mertens 1 := redheffer_general 0
theorem redheffer_2 : (redheffer 2).det = mertens 2 := redheffer_general 1
theorem redheffer_3 : (redheffer 3).det = mertens 3 := redheffer_general 2

/-  ── `crux_general` NO ES SOLO PARA REDHEFFER: sirve para CUALQUIER u ──

    `crux_general` ya está probado para un vector u ARBITRARIO en la columna
    0 — Redheffer (u=todo-unos) es solo la instancia u≡1. Nadie había usado
    otra u todavía. Con u(j) = j+1 (columna 0 = 1,2,…,N+1 en vez de todo
    unos) sale, GRATIS, una suma de Möbius PONDERADA que TRINITY nunca había
    calculado: Σ_{k=1}^{n} k·μ(k), el análogo ponderado de M(n)=Σμ(k).
    Verificado en Python (eliminación exacta con Fraction, sin floats):
    N=1..9 coincide exacto con el determinante de la matriz modificada.     -/

/-- La suma de Möbius PONDERADA: Σ_{k=1}^{n} k·μ(k), aquí como Σ_{j=0}^{n-1}
    (j+1)·μ(j+1) (mismo valor, indexado por range en vez de por Icc 1 n —
    evita una reindexación innecesaria). Nunca antes registrada por
    TRINITY — cae gratis de `crux_general` con u≠todo-unos. -/
def mertens_pesada (n : ℕ) : ℤ := ∑ j ∈ Finset.range n, ((j : ℤ) + 1) * (μ (j + 1) : ℤ)

/-- det(ζ con columna 0 = (1,2,…,N+1) en vez de todo-unos) = Σ k·μ(k), para
    TODO N — instancia NUEVA de `crux_general` con u(j)=j+1: nadie había
    usado `crux_general` con una u distinta de todo-unos hasta ahora. -/
theorem redheffer_pesada (N : ℕ) :
    ((zeta (N + 1)).updateCol 0 (fun i => (i : ℤ) + 1)).det = mertens_pesada (N + 1) := by
  rw [crux_general]
  unfold murow mertens_pesada
  rw [Fin.sum_univ_eq_sum_range (fun j => (μ (j + 1) : ℤ) * ((j : ℤ) + 1))]
  apply Finset.sum_congr rfl
  intro j _; ring

end Redheffer
