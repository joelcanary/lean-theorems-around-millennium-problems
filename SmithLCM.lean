import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-!
# Smith sobre un anillo cualquiera, y el determinante del mínimo común múltiplo

`SmithDeterminant.lean` cerró `det(f(gcd(i,j))) = g(1)···g(N)` cuando
`f(m) = Σ_{d|m} g(d)`, sobre ℤ. Este fichero hace dos cosas:

1. **Sube esa prueba a un anillo conmutativo cualquiera.** No cuesta nada: la
   prueba nunca usa nada de ℤ, solo suma, producto y el 1 del anillo. Y es lo
   que hace falta, porque el determinante del lcm vive en ℚ.

2. **Reduce el determinante del lcm a ese teorema.** La identidad
   `lcm(i,j)·gcd(i,j) = i·j` dice que la matriz del lcm se factoriza como
   `D · S · D` con `D = diag(k)` y `S[i][j] = 1/gcd(i,j)`. Y `1/m` sí es de la
   forma `Σ_{d|m} g(d)`, con `g(n) = (1/n)·Π_{p|n}(1-p)`. De ahí

       det(lcm(i,j))_{i,j=1}^N = (N!)² · Π_k g(k) = N! · Π_k Π_{p|k} (1-p).

3. **Cierra la premisa, y con ella el teorema.** La hipótesis que hacía falta
   (`1/m = Σ_{d|m} g d`) no hay que demostrarla: la inversión de Möbius de
   Mathlib es un *si y solo si*, así que basta **definir** `g` por el otro lado
   —`g(n) = Σ_{ab=n} μ(a)/b`— y la hipótesis sale del `iff` sin trabajo. El
   resultado `det_lcm` es incondicional.

4. **La forma cerrada, cerrada tambien.** Lo que quedaba era
   `gLcm n = (1/n)·Π_{p|n}(1-p)`, que se reduce a la identidad
   `Σ_{d|n} μ(d)·d = Π_{p|n}(1-p)`. Mathlib solo la trae para `n` libre de
   cuadrados; la version general esta ahora en `SmithLCMForma.lean`, probada
   observando que `μ(d)=0` fuera de los libres de cuadrados y que esos divisores
   son exactamente los del **radical** de `n`. Con ella el determinante vale
   `N!·Π_k Π_{p|k}(1-p)`, el clasico de Smith (1875).

Nada queda abierto en este fichero.
-/
open Matrix

namespace SmithLCM

variable {R : Type*} [CommRing R]

/-! ## 1. La maquinaria de Smith sobre un anillo conmutativo cualquiera -/

/-- ζ de divisibilidad con coeficientes en `R`: ζ[i][j] = 1 si (i+1) ∣ (j+1). -/
def zetaR (N : ℕ) : Matrix (Fin N) (Fin N) R :=
  fun i j => if (i : ℕ) + 1 ∣ (j : ℕ) + 1 then 1 else 0

theorem zetaR_blockTriangular (N : ℕ) : (zetaR (R := R) N).BlockTriangular id := by
  intro i j hij
  simp only [zetaR]
  rw [if_neg]
  intro hd
  have := Nat.le_of_dvd (by omega) hd
  simp only [id] at hij
  omega

/-- det(ζ) = 1 en cualquier anillo: triangular superior con unos en la diagonal. -/
theorem det_zetaR (N : ℕ) : (zetaR (R := R) N).det = 1 := by
  rw [Matrix.det_of_upperTriangular (zetaR_blockTriangular N)]
  simp [zetaR]

/-- S_f[i][j] = f(gcd(i+1, j+1)). -/
def smithR (N : ℕ) (f : ℕ → R) : Matrix (Fin N) (Fin N) R :=
  fun i j => f (Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1))

/-- diag(g(1), …, g(N)). -/
def diagR (N : ℕ) (g : ℕ → R) : Matrix (Fin N) (Fin N) R :=
  Matrix.diagonal (fun i => g ((i : ℕ) + 1))

theorem diagR_mul_zetaR (N : ℕ) (g : ℕ → R) (d j : Fin N) :
    (diagR N g * zetaR (R := R) N) d j
      = if (d : ℕ) + 1 ∣ (j : ℕ) + 1 then g ((d : ℕ) + 1) else 0 := by
  simp only [Matrix.mul_apply, diagR, Matrix.diagonal_apply, zetaR]
  have step : (∑ x : Fin N, (if d = x then g ((d : ℕ) + 1) else 0)
        * (if (x : ℕ) + 1 ∣ (j : ℕ) + 1 then (1 : R) else 0))
      = ∑ x : Fin N, (if x = d then
          (if (x : ℕ) + 1 ∣ (j : ℕ) + 1 then g ((d : ℕ) + 1) else 0) else 0) := by
    apply Finset.sum_congr rfl; intro x _
    by_cases h : x = d
    · simp [h]
    · rw [if_neg h, if_neg (fun hh => h hh.symm), zero_mul]
  rw [step, Finset.sum_ite_eq' Finset.univ d]
  simp

/-- El puente `Fin N ↔ Nat.divisors m`, ahora genérico en el sumando.
    Es puro manejo de índices: no mira lo que hay dentro de `g`. -/
theorem fin_sum_eq_divisors_sum (N m : ℕ) (g : ℕ → R) (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    (∑ x : Fin N, if (x : ℕ) + 1 ∣ m then g ((x : ℕ) + 1) else 0)
      = ∑ d ∈ Nat.divisors m, g d := by
  rw [Fin.sum_univ_eq_sum_range (fun x => if x + 1 ∣ m then g (x + 1) else 0)]
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
      refine ⟨by omega, ?_⟩
      have heq1 : i = d - 1 := hd.symm
      rw [heq1]
      have heq2 : d - 1 + 1 = d := by omega
      rw [heq2]; exact hdvd
  rw [hset, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro d hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hde : d - 1 + 1 = d := by omega
    rw [hde]
  · intro a ha b hb hab
    simp only at hab
    have hapos : 1 ≤ a := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp ha).1 (by omega)
    have hbpos : 1 ≤ b := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hb).1 (by omega)
    omega

theorem entrada_factorizacion_R (N : ℕ) (f g : ℕ → R)
    (hyp : ∀ m, 1 ≤ m → f m = ∑ d ∈ Nat.divisors m, g d) (i j : Fin N) :
    ((zetaR (R := R) N)ᵀ * (diagR N g * zetaR (R := R) N)) i j = smithR N f i j := by
  rw [Matrix.mul_apply]
  simp_rw [Matrix.transpose_apply, diagR_mul_zetaR N g, zetaR]
  have key : (∑ x : Fin N, (if (x : ℕ) + 1 ∣ (i : ℕ) + 1 then (1 : R) else 0)
        * (if (x : ℕ) + 1 ∣ (j : ℕ) + 1 then g ((x : ℕ) + 1) else 0))
      = ∑ x : Fin N,
          (if (x : ℕ) + 1 ∣ Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) then g ((x : ℕ) + 1) else 0) := by
    apply Finset.sum_congr rfl; intro x _
    by_cases h1 : (x : ℕ) + 1 ∣ (i : ℕ) + 1 <;> by_cases h2 : (x : ℕ) + 1 ∣ (j : ℕ) + 1 <;>
      simp [h1, h2, Nat.dvd_gcd_iff]
  rw [key]
  have hgcdpos : 1 ≤ Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hgcdle : Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) ≤ N := by
    have := Nat.gcd_le_left (m := (i : ℕ) + 1) ((j : ℕ) + 1) (by omega)
    have hi := i.isLt
    omega
  rw [fin_sum_eq_divisors_sum N _ g hgcdpos hgcdle]
  exact (hyp _ hgcdpos).symm

theorem smithR_eq_factorizacion (N : ℕ) (f g : ℕ → R)
    (hyp : ∀ m, 1 ≤ m → f m = ∑ d ∈ Nat.divisors m, g d) :
    smithR N f = (zetaR (R := R) N)ᵀ * (diagR N g * zetaR (R := R) N) := by
  ext i j
  exact (entrada_factorizacion_R N f g hyp i j).symm

theorem det_diagR (N : ℕ) (g : ℕ → R) :
    (diagR N g).det = ∏ i : Fin N, g ((i : ℕ) + 1) := by
  simp [diagR, Matrix.det_diagonal]

/-- **Smith generalizado, sobre cualquier anillo conmutativo.**
    Si `f(m) = Σ_{d|m} g(d)` entonces `det(f(gcd(i,j))) = g(1)···g(N)`. -/
theorem smithR_determinant (N : ℕ) (f g : ℕ → R)
    (hyp : ∀ m, 1 ≤ m → f m = ∑ d ∈ Nat.divisors m, g d) :
    (smithR N f).det = ∏ i : Fin N, g ((i : ℕ) + 1) := by
  rw [smithR_eq_factorizacion N f g hyp, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, det_zetaR, det_diagR]
  ring

/-! ## 2. El determinante del mínimo común múltiplo -/

/-- L[i][j] = lcm(i+1, j+1), con coeficientes racionales. -/
def lcmMat (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => (Nat.lcm ((i : ℕ) + 1) ((j : ℕ) + 1) : ℚ)

/-- D = diag(1, 2, …, N). -/
def diagId (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.diagonal (fun i => (((i : ℕ) + 1 : ℕ) : ℚ))

/-- **La factorización que lo reduce todo a Smith**: `lcm(i,j) = i · (1/gcd(i,j)) · j`,
    que no es más que `lcm·gcd = i·j` dividido por el gcd. -/
theorem lcmMat_eq (N : ℕ) :
    lcmMat N = diagId N * smithR N (fun m => (1 : ℚ) / m) * diagId N := by
  ext i j
  -- `Matrix.diagonal_mul` / `Matrix.mul_diagonal` evitan tener que sumar a mano:
  -- multiplicar por una diagonal es escalar la fila y la columna, nada más.
  simp only [diagId, Matrix.mul_diagonal, Matrix.diagonal_mul, smithR, lcmMat]
  have hgpos : 0 < Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) :=
    Nat.gcd_pos_of_pos_left _ (by omega)
  have hgQ : ((Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast hgpos.ne'
  -- la única aritmética de verdad: lcm·gcd = i·j
  have hmulQ : ((Nat.gcd ((i : ℕ) + 1) ((j : ℕ) + 1) : ℕ) : ℚ)
        * ((Nat.lcm ((i : ℕ) + 1) ((j : ℕ) + 1) : ℕ) : ℚ)
      = (((i : ℕ) + 1 : ℕ) : ℚ) * (((j : ℕ) + 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.gcd_mul_lcm ((i : ℕ) + 1) ((j : ℕ) + 1)
  field_simp
  linear_combination hmulQ

theorem det_diagId (N : ℕ) :
    (diagId N).det = ∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ) := by
  simp [diagId, Matrix.det_diagonal]

/-- **El determinante del lcm, reducido a Smith.**
    Dada `g` con `1/m = Σ_{d|m} g(d)` (premisa abierta, ver la cabecera):

        det(lcm(i,j))_{i,j=1}^N = (Π k)² · Π_k g(k).

    Con `g(n) = (1/n)·Π_{p|n}(1-p)` el lado derecho es `N! · Π_k Π_{p|k}(1-p)`,
    verificado exactamente hasta N=12 en `verifica_lcm_det.py`. -/
theorem det_lcmMat (N : ℕ) (g : ℕ → ℚ)
    (hyp : ∀ m, 1 ≤ m → (1 : ℚ) / m = ∑ d ∈ Nat.divisors m, g d) :
    (lcmMat N).det
      = (∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ))
        * (∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ))
        * ∏ i : Fin N, g ((i : ℕ) + 1) := by
  rw [lcmMat_eq N, Matrix.det_mul, Matrix.det_mul, det_diagId,
      smithR_determinant N (fun m => (1 : ℚ) / m) g hyp]
  ring

/-! ## 3. Cerrando la premisa: la inversión de Möbius la da hecha -/

/-- `g(n) = Σ_{ab=n} μ(a)/b`. No es una elección: es **la** función que la
    inversión de Möbius obliga, y definirla así es lo que hace la hipótesis
    gratis en lugar de tener que demostrarla. -/
noncomputable def gLcm (n : ℕ) : ℚ :=
  ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℚ) * (1 / x.2)

/-- La hipótesis que `det_lcmMat` pedía, ahora demostrada.

    `sum_eq_iff_sum_mul_moebius_eq` es un *si y solo si*: el lado que dice
    `Σ_{ab=n} μ(a)·(1/b) = gLcm n` es cierto **por definición** de `gLcm`, así
    que el otro lado --- el que necesitamos --- se obtiene con `.mpr`. -/
theorem gLcm_spec (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℚ) / m = ∑ d ∈ Nat.divisors m, gLcm d := by
  have h : ∀ n, 0 < n →
      ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℚ) * (1 / x.2) = gLcm n :=
    fun _ _ => rfl
  exact ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℚ)
    (f := gLcm) (g := fun n => (1 : ℚ) / n)).mpr h m (by omega)).symm

/-- **El determinante del mínimo común múltiplo, incondicional.**

        det(lcm(i,j))_{i,j=1}^N = (Π_{k≤N} k)² · Π_{k≤N} gLcm(k).

    Sin premisas: la única que había la descarga `gLcm_spec`. -/
theorem det_lcm (N : ℕ) :
    (lcmMat N).det
      = (∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ))
        * (∏ i : Fin N, (((i : ℕ) + 1 : ℕ) : ℚ))
        * ∏ i : Fin N, gLcm ((i : ℕ) + 1) :=
  det_lcmMat N gLcm (fun m hm => gLcm_spec m hm)

end SmithLCM
