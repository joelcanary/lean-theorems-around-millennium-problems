/-
  HodgeMathlib.lean — la fórmula unificada de χ como identidad polinómica (Mathlib)

  Este módulo vive en un proyecto lake CON Mathlib (papers/mathlib_proj/), porque
  las identidades de χ son igualdades de POLINOMIOS en d que requieren `ring` — la
  táctica de normalización de anillos de Mathlib, que el Lean core no tiene.

  Es la parte que el hallazgo X-lean-sin-kernel dejó pendiente: subir
  HodgeChiUnificada de "fuente Mathlib" a verificada por el kernel de verdad.

  χ(X_d^n) = ((1−d)^{n+2} − 1)/d + (n+2)  (forma cerrada)
           = Σ_{k=1}^{n+1} (−1)^{k+1} C(n+2,k+1) d^k   (forma binomial)
  Las "cerrada = binomial" se multiplican por d para evitar la división.
-/
import Mathlib.Tactic

namespace HodgeChi

/-- n=2 (superficies): χ = d³ − 4d² + 6d, coincide con la binomial 6d − 4d² + d³. -/
theorem chi_n2 (d : ℚ) :
    d ^ 3 - 4 * d ^ 2 + 6 * d = 6 * d - 4 * d ^ 2 + d ^ 3 := by ring

/-- n=2, forma cerrada = binomial: ((1−d)⁴ − 1) + 4d = (d³ − 4d² + 6d)·d. -/
theorem chi_n2_cerrada (d : ℚ) :
    (1 - d) ^ 4 - 1 + 4 * d = (d ^ 3 - 4 * d ^ 2 + 6 * d) * d := by ring

/-- n=3 (3-folds): binomial 10d − 10d² + 5d³ − d⁴; cerrada ((1−d)⁵−1)+5d, ·d. -/
theorem chi_n3_cerrada (d : ℚ) :
    (1 - d) ^ 5 - 1 + 5 * d = (10 * d - 10 * d ^ 2 + 5 * d ^ 3 - d ^ 4) * d := by ring

/-- n=4 (4-folds): binomial 15d − 20d² + 15d³ − 6d⁴ + d⁵. -/
theorem chi_n4_cerrada (d : ℚ) :
    (1 - d) ^ 6 - 1 + 6 * d =
      (15 * d - 20 * d ^ 2 + 15 * d ^ 3 - 6 * d ^ 4 + d ^ 5) * d := by ring

/-- La quíntica 3-fold (d=5, n=3): χ = −200, de la fórmula. -/
theorem quintica_chi_menos_200 :
    (10 * 5 - 10 * 5 ^ 2 + 5 * 5 ^ 3 - 5 ^ 4 : ℤ) = -200 := by norm_num

/-- LA FÓRMULA UNIFICADA, GENERAL (para TODO n, no solo n=2,3,4). El polinomio de
    χ (multiplicado por d, es decir `(1−d)^{n+2} − 1 + (n+2)d`) es exactamente la
    cola binomial `∑_{k≥2} C(n+2,k)(−d)^k`. Los dos términos de orden bajo del
    binomio (el 1 y el −(n+2)d) se cancelan con el −1 y el +(n+2)d — por eso χ es
    un polinomio genuino sin término constante ni lineal. Demostrado con el teorema
    del binomio (`add_pow`) y pelando los dos primeros sumandos. Es la instancia
    n=2,3,4 (chi_n*_cerrada) elevada a teorema para todo n. -/
theorem chi_general (d : ℚ) (n : ℕ) :
    (1 - d) ^ (n + 2) - 1 + ((n : ℚ) + 2) * d
      = ∑ k ∈ Finset.range (n + 1), ((n + 2).choose (k + 2) : ℚ) * (-d) ^ (k + 2) := by
  have key : (1 - d) ^ (n + 2)
      = ∑ k ∈ Finset.range (n + 3), ((n + 2).choose k : ℚ) * (-d) ^ k := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro k _
    rw [one_pow, mul_one]
    ring
  rw [key, Finset.sum_range_succ', Finset.sum_range_succ']
  simp [Nat.choose_one_right]

/-  ── La tricotomía de Kodaira de una hipersuperficie, como hecho binomial ──

    El género geométrico (número de Hodge de arriba) de X_d^n es, por Griffiths,
    h^{n,0} = C(d−1, n+1). Con m = d−1, `pg m n = C(m, n+1)` clasifica la
    variedad por el signo del fibrado canónico:

        Fano         h^{n,0} = 0   ⟺  d ≤ n+1   (m < n+1)
        Calabi–Yau   h^{n,0} = 1   ⟺  d = n+2   (m = n+1)
        tipo general h^{n,0} ≥ 2   ⟸  d ≥ n+3   (m ≥ n+2)

    Griffiths entra como definición (`pg`); la CLASIFICACIÓN es un hecho puro de
    coeficientes binomiales, aquí verificado por el kernel. Generaliza el corolario
    "X_d es Calabi–Yau ⟺ d = n+2" a las tres clases de dimensión de Kodaira.        -/

/-- Género geométrico h^{n,0} de X_d^n, con m = d−1 (Griffiths: h^{n,0}=C(d−1,n+1)). -/
def pg (m n : ℕ) : ℕ := m.choose (n + 1)

/-- FANO: h^{n,0} = 0 ⟺ d ≤ n+1 (m < n+1). -/
theorem fano_iff (m n : ℕ) : pg m n = 0 ↔ m < n + 1 := by
  unfold pg; exact Nat.choose_eq_zero_iff

/-- CALABI–YAU: h^{n,0} = 1 ⟺ d = n+2 (m = n+1). El corolario, ahora demostrado. -/
theorem calabi_yau_iff (m n : ℕ) : pg m n = 1 ↔ m = n + 1 := by
  unfold pg
  constructor
  · intro h; rcases Nat.choose_eq_one_iff.mp h with h0 | h1 <;> omega
  · intro h; subst h; simp [Nat.choose_self]

/-- TIPO GENERAL: d ≥ n+3 (m ≥ n+2) ⟹ h^{n,0} ≥ 2. -/
theorem general_type (m n : ℕ) (h : n + 2 ≤ m) : 2 ≤ pg m n := by
  unfold pg
  have hval : (n + 2).choose (n + 1) = n + 2 := by
    have hs := (Nat.choose_symm (show n + 1 ≤ n + 2 by omega)).symm
    rw [show (n + 2) - (n + 1) = 1 by omega, Nat.choose_one_right] at hs
    exact hs
  have hmono := Nat.choose_le_choose (n + 1) h
  omega

/-- Anclas (m = d−1): quíntica 3-fold (d=5,n=3) es CY; K3 (d=4,n=2) es CY;
    superficie cúbica (d=3,n=2) es Fano; séxtica (d=6,n=3) es de tipo general. -/
theorem quintica_es_CY : pg 4 3 = 1 := by decide
theorem k3_es_CY : pg 3 2 = 1 := by decide
theorem cubica_es_Fano : pg 2 2 = 0 := by decide
theorem sextica_tipo_general : 2 ≤ pg 5 3 := by decide

/-  ── La fórmula GÉNERO–GRADO, como caso n=1 ──

    Para curvas planas (n=1), el género geométrico es h^{1,0} = C(d−1, 2), que es
    exactamente la fórmula clásica género–grado (Plücker):

        g(curva plana lisa de grado d) = (d−1)(d−2)/2.

    Es el mismo teorema de Griffiths especializado a n=1. Y la tricotomía de arriba
    dice, en n=1: recta/cónica (d≤2) son racionales (g=0, Fano P¹), la CÚBICA (d=3)
    es la única de género 1 — la curva elíptica, el Calabi–Yau de dimensión 1—, y
    d≥4 es de tipo general (g≥3).                                                  -/

/-- Fórmula género–grado: una curva plana lisa de grado d = m+1 tiene género
    g = C(m,2) = m(m−1)/2. (`Nat.choose_two_right`.) -/
theorem genus_degree (m : ℕ) : pg m 1 = m * (m - 1) / 2 := by
  unfold pg; exact Nat.choose_two_right m

/-- Géneros clásicos: cónica (d=2) g=0; cúbica (d=3) g=1 (elíptica); cuártica g=3;
    quíntica g=6. -/
theorem genero_conica : pg 1 1 = 0 := by decide
theorem genero_cubica_es_1 : pg 2 1 = 1 := by decide
theorem genero_cuartica : pg 3 1 = 3 := by decide
theorem genero_quintica : pg 4 1 = 6 := by decide

/-  ── SIMETRÍA ESPECULAR: h^{2,1} bien definido para TODO d, no solo la quíntica ──

    Para las 3-folds X_d^3, la simetría especular calcula h^{2,1} = b₃/2 − h^{3,0},
    con b₃ = 4 − χ(d) (χ+b₃=4 demostrado en HodgeThreefoldBetti). Que esta fórmula
    dé SIEMPRE un entero —para CUALQUIER grado d, no solo d=5— depende de un hecho
    NO trivial: χ(d) es par para todo d. Los coeficientes del polinomio de χ (10,
    −10, 5, −1) NO son todos pares, así que no es una identidad polinómica; es un
    hecho de PARIDAD: 5d³−d⁴ = d³(5−d) es par porque d³ tiene la paridad de d, y
    si d es par el factor d³ lo es, si d es impar 5−d es par. Demostrado por casos
    en la paridad de d (`Int.even_or_odd`), con el testigo exacto en cada caso.   -/

/-- χ de una 3-fold X_d, como función entera del grado (la forma binomial ×d,
    dividida por d — aquí ya sin el factor d, la fórmula usual de la literatura). -/
def chi3 (d : Int) : Int := 10 * d - 10 * d ^ 2 + 5 * d ^ 3 - d ^ 4

/-- χ(d) es PAR para TODO entero d — no una instancia, el hecho general que hace
    que h^{2,1} = (4−χ)/2 − h^{3,0} sea siempre un entero. -/
theorem chi3_par (d : Int) : Even (chi3 d) := by
  rcases Int.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨-8 * k ^ 4 + 20 * k ^ 3 - 20 * k ^ 2 + 10 * k, by subst hk; unfold chi3; ring⟩
  · exact ⟨-8 * k ^ 4 + 4 * k ^ 3 - 2 * k ^ 2 + k + 2, by subst hk; unfold chi3; ring⟩

/-- b₃(d) = 4 − χ(d): también par para todo d, consecuencia directa. -/
theorem b3_par (d : Int) : Even (4 - chi3 d) := by
  obtain ⟨r, hr⟩ := chi3_par d
  exact ⟨2 - r, by omega⟩

/-- h^{2,1}(d) = (4−χ(d))/2 − h^{3,0}(d), bien definido (entero) para todo d, con
    h^{3,0} = C(d−1,4) (m=d−1 como Nat, aquí ya como valor concreto por caso). La
    quíntica (d=5, m=4): (4−(−200))/2 − 1 = 102 − 1 = 101 — el 101 clásico de la
    simetría especular de Candelas et al. (1985). -/
theorem h21_quintica_de_formula_general :
    (4 - chi3 5) / 2 - (pg 4 3 : Int) = 101 := by
  unfold chi3 pg; decide

/-  ── LA GENERALIZACIÓN COMPLETA: χ es par para TODA dimensión impar n, no solo n=3 ──

    `chi3_par` de arriba era una prueba AD HOC del caso n=3 (testigo cuártico
    explícito, calculado con sympy). Aquí el mismo hecho pero para χ_N(n,d) —la
    forma binomial de χ, Σ_{j=1}^{n+1}(−1)^{j+1}C(n+2,j+1)d^j, la de chi_general—
    para TODO n impar y TODO entero d. El argumento, genuinamente distinto:

      1. En ZMod 2, x^j = x para j≥1 (idempotencia 0·0=0, 1·1=1 + inducción).
      2. Por eso χ_N(n,d) mod 2 = d · S(n) mod 2, con S(n)=Σ_{j=1}^{n+1}C(n+2,j+1)
         una CONSTANTE que no depende de d (el signo (−1)^{j+1} también es 1 en
         ZMod 2, así que desaparece).
      3. S(n) = 2^{n+2} − (n+3) (suma de coeficientes binomiales, `sum_range_choose`,
         menos los dos términos que `chi_general` ya pela).
      4. Para n IMPAR, n+3 es par y 2^{n+2} es par ⟹ S(n) es par ⟹ χ_N(n,d) es
         par para TODO d, sin importar la paridad de d — el caso n=3 (chi3_par)
         es la instancia n=3 de este teorema.                                    -/

noncomputable def chiN (n : ℕ) (d : Int) : Int :=
  ∑ j ∈ Finset.Icc 1 (n + 1), (-1 : Int) ^ (j + 1) * (n + 2).choose (j + 1) * d ^ j

private theorem idem2 : ∀ x : ZMod 2, x * x = x := by decide

private theorem pow_eq_self (x : ZMod 2) (j : ℕ) (hj : 1 ≤ j) : x ^ j = x := by
  induction j with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; ring
    · rw [pow_succ, ih hk, idem2]

private theorem neg_one_cast : (-1 : ZMod 2) = 1 := by decide

private theorem chiN_mod2 (n : ℕ) (d : Int) :
    ((chiN n d : Int) : ZMod 2)
      = (d : ZMod 2) * ∑ j ∈ Finset.Icc 1 (n + 1), ((n + 2).choose (j + 1) : ZMod 2) := by
  unfold chiN
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  rw [neg_one_cast, one_pow, one_mul, pow_eq_self (d : ZMod 2) j hj1]
  ring

private theorem S_formula (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 (n + 1), (n + 2).choose (j + 1) = 2 ^ (n + 2) - (n + 3) := by
  have hsum : ∑ i ∈ Finset.range (n + 3), (n + 2).choose i = 2 ^ (n + 2) :=
    Nat.sum_range_choose (n + 2)
  have hreindex : ∑ j ∈ Finset.Icc 1 (n + 1), (n + 2).choose (j + 1)
      = ∑ i ∈ Finset.Icc 2 (n + 2), (n + 2).choose i := by
    apply Finset.sum_nbij' (fun j => j + 1) (fun i => i - 1) <;> intros <;> simp_all <;> omega
  rw [hreindex]
  have hsplit : Finset.range (n + 3) = insert 0 (insert 1 (Finset.Icc 2 (n + 2))) := by
    ext x; simp [Finset.mem_range, Finset.mem_Icc]; omega
  rw [hsplit] at hsum
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp)] at hsum
  simp [Nat.choose_zero_right, Nat.choose_one_right] at hsum
  omega

private theorem S_par_si_n_impar (n : ℕ) (himpar : Odd n) :
    (∑ j ∈ Finset.Icc 1 (n + 1), ((n + 2).choose (j + 1) : ZMod 2)) = 0 := by
  rw [show (∑ j ∈ Finset.Icc 1 (n + 1), ((n + 2).choose (j + 1) : ZMod 2))
      = ((∑ j ∈ Finset.Icc 1 (n + 1), (n + 2).choose (j + 1) : ℕ) : ZMod 2) from by
    push_cast; ring]
  rw [ZMod.natCast_eq_zero_iff_even, S_formula]
  have hle : n + 3 ≤ 2 ^ (n + 2) := by
    have := Nat.lt_two_pow_self (n := n + 2)
    omega
  rw [Nat.even_sub hle]
  have hn3 : Even (n + 3) := by obtain ⟨k, hk⟩ := himpar; exact ⟨k + 2, by omega⟩
  constructor
  · intro _; exact hn3
  · intro _; exact ⟨2 ^ (n + 1), by ring⟩

/-- EL TEOREMA GENERAL: para TODO n impar y TODO entero d, χ_N(n,d) es par.
    Generaliza `chi3_par` (solo n=3) a TODA dimensión impar. -/
theorem chiN_par (n : ℕ) (himpar : Odd n) (d : Int) : (2 : Int) ∣ chiN n d := by
  have h2 : ((2 : ℕ) : Int) ∣ chiN n d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, chiN_mod2, S_par_si_n_impar n himpar, mul_zero]
  exact_mod_cast h2

/-- Instancia n=3 (subsume chi3_par): b₃ = 4−χ_N(3,d) es par para todo d,
    exactamente lo que hace falta para que h^{2,1} de una 3-fold esté bien
    definido — ahora como corolario del teorema general, no un caso ad hoc. -/
theorem b3_par_de_general (d : Int) : (2 : Int) ∣ (4 - chiN 3 d) := by
  obtain ⟨r, hr⟩ := chiN_par 3 ⟨1, rfl⟩ d
  exact ⟨2 - r, by omega⟩

/-  ── SUPERFICIES (n=2): h^{1,1} bien definido para TODO d, no solo d=1..12 ──

    H-medible (research/hallazgos/hodge/H-medible.json) da, para una superficie
    lisa X_d ⊂ P³, tres fórmulas verificadas SOLO en rango d=1..12:
      χ_top = d³−4d²+6d          (YA demostrada arriba: chi_n2, chi_general)
      h^{2,0} = C(d−1,3)         (YA demostrada: pg, es la instancia n=2)
      h^{1,1} = 2d³/3 − 2d² + 7d/3
    La tercera es la que faltaba cerrar. Dos cosas NO triviales, ninguna
    verificada hasta ahora más allá de d≤12:

    1. INTEGRALIDAD: h^{1,1}(d) es SIEMPRE un entero. Multiplicando por 3,
       equivale a 3 ∣ (2d³−6d²+7d). Mod 3, el término −6d² se anula y 7d≡d,
       quedando 2d³+d ≡ 2d³+d (mod 3). Por Fermat (x³≡x mod 3 para TODO x,
       chequeo finito sobre ZMod 3 — el mismo truco de `idem2`/`pow_eq_self`
       de arriba, aquí con cubos en vez de cuadrados), 2d³+d ≡ 2d+d = 3d ≡ 0.

    2. CONSISTENCIA DE BETTI: para una superficie simplemente conexa,
       b₂ = 2h^{2,0}+h^{1,1}, así que χ_top = 2+b₂ = 2+2h^{2,0}+h^{1,1}. Que
       las TRES fórmulas de TRINITY (obtenidas por identificación numérica
       independiente, no derivadas unas de otras) satisfagan esta relación
       clásica para TODO d —no solo los 12 valores donde se comprobó— es la
       identidad de polinomios (sin división, ×3 para despejarla):
         3·χ_top(d) = 6 + (d−1)(d−2)(d−3) + (2d³−6d²+7d)
       con (d−1)(d−2)(d−3) = 6·h^{2,0}(d) y (2d³−6d²+7d) = 3·h^{1,1}(d).     -/

/-- Numerador de 3·h^{1,1}(d), sin dividir (evita la división en ℤ). -/
def h11_num (d : Int) : Int := 2 * d ^ 3 - 6 * d ^ 2 + 7 * d

/-- Fermat finito, ya aplicado al numerador completo: 2x³−6x²+7x = 0 para TODO
    x en ZMod 3 (chequeo sobre los 3 elementos — el mismo truco de `idem2` de
    arriba, aquí `decide` evalúa la expresión entera en vez de solo x³=x, para
    no depender de que `ring` reduzca coeficientes numéricos mod 3 por su cuenta). -/
private theorem h11_num_mod3 : ∀ x : ZMod 3, 2 * x ^ 3 - 6 * x ^ 2 + 7 * x = 0 := by decide

/-- INTEGRALIDAD DE h^{1,1}: 3 ∣ (2d³−6d²+7d) para TODO entero d — no solo
    los d=1..12 verificados en H-medible. Generaliza a superficies (n=2) lo
    que `chiN_par`/`b3_par_de_general` ya hicieron para 3-folds (n=3, mod 2):
    aquí la divisibilidad relevante es mod 3, no mod 2. -/
theorem h11_integral (d : Int) : (3 : Int) ∣ h11_num d := by
  have h3 : ((h11_num d : Int) : ZMod 3) = 0 := by
    unfold h11_num; push_cast; exact h11_num_mod3 (d : ZMod 3)
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (h11_num d) 3).mp h3

/-- CONSISTENCIA DE BETTI para TODO d, identidad de polinomios sin división:
    3·χ_top(d) = 6 + (d−1)(d−2)(d−3) + (2d³−6d²+7d). Las tres fórmulas
    independientes de H-medible (χ_top, h^{2,0}=C(d−1,3), h^{1,1}) obedecen
    la relación clásica χ=2+2h^{2,0}+h^{1,1} para TODO d, no solo d=1..12. -/
theorem hodge_surface_betti (d : Int) :
    3 * (d ^ 3 - 4 * d ^ 2 + 6 * d) = 6 + (d - 1) * (d - 2) * (d - 3) + h11_num d := by
  unfold h11_num; ring

/-  ── LA VENTANA DE NOETHER–LEFSCHETZ: d−3 alcanza p_g EXACTAMENTE en d=3,4 ──

    H-cota-optima (Green–Voisin) da la cota INFERIOR d−3 para la codimensión
    de las componentes del locus de Noether–Lefschetz NL_d; p_g=C(d−1,3) es
    la cota SUPERIOR (ya `pg` arriba). Que ambas coincidan justo en d=3,4 y
    luego se separen —la "ventana de incertidumbre" que crece con d, ~d³/6—
    es la comparación NUMÉRICA de dos cantidades demostradas cada una por su
    lado. La geometría de Green–Voisin (por qué d−3 es la cota) NO se
    reproduce aquí — se cita como hecho externo, igual que B-tunnell-signo-
    funcional cita la conjetura de paridad. Lo que se demuestra es la
    ARITMÉTICA: la desigualdad de coeficientes binomiales y su caso de
    igualdad, con m=d−1 (mismo convenio que `pg`).                          -/

/-- d−3 ≤ p_g(d) para TODO d≥3 (m=d−1≥2): la cota se alcanza, nunca se
    excede. Inducción con la regla de Pascal (`choose_succ_succ'`). -/
theorem cota_le_pg (m : ℕ) (hm : 2 ≤ m) : m - 2 ≤ pg m 2 := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    unfold pg at ih ⊢
    rw [Nat.choose_succ_succ' n 2]
    have h2 : 1 ≤ n.choose 2 := Nat.choose_pos hn
    omega

/-- Para d≥5 (m≥4) la cota es ESTRICTA: la ventana de incertidumbre ya se
    abrió. Misma inducción, ahora arrancando en m=4 (d=5), donde 2 < 4. -/
theorem cota_lt_pg (m : ℕ) (hm : 4 ≤ m) : m - 2 < pg m 2 := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    unfold pg at ih ⊢
    rw [Nat.choose_succ_succ' n 2]
    have h2 : 1 ≤ n.choose 2 := Nat.choose_pos (by omega)
    omega

/-- CARACTERIZACIÓN COMPLETA: la cota d−3 iguala a p_g EXACTAMENTE en d=3,4
    (m=2,3) — el "hallazgo estructural" de H-noether-lefschetz, ahora un
    teorema, no una observación en un rango finito. -/
theorem cota_eq_pg_iff (m : ℕ) (hm : 2 ≤ m) : m - 2 = pg m 2 ↔ m = 2 ∨ m = 3 := by
  constructor
  · intro heq
    rcases Nat.lt_or_ge m 4 with h4 | h4
    · omega
    · exact absurd heq (by have := cota_lt_pg m h4; omega)
  · rintro (rfl | rfl) <;> decide

/-  ── LA VENTANA DE NOETHER–LEFSCHETZ ES EXACTAMENTE OEIS A005581 ──

    H-oeis-A005581 observaba (verificado con sympy, FUERA del kernel de
    TRINITY) que la ventana nl_ventana(d) = p_g(d) − (d−3) — la diferencia
    entre la cota superior (h^{2,0}=C(d−1,3), con 6·h^{2,0}=(d−1)(d−2)(d−3)
    de `hodge_surface_betti`) y la cota inferior (d−3, de `cota_le_pg`) —
    coincide, COMO POLINOMIO, con la fórmula cerrada de OEIS A005581(n) =
    (n−1)·n·(n+4)/6 evaluada en n=d−3. Identidad de polinomios sin división
    (×6 para despejarla): (d−1)(d−2)(d−3) − 6(d−3) = (d−4)(d−3)(d+1).       -/

/-- La ventana de Noether–Lefschetz (×6, sin división) es EXACTAMENTE OEIS
    A005581(d−3) (×6), para TODO entero d — sube H-oeis-A005581 de
    "verificado con sympy externo, d=4..200" a kernel-verificado, para
    todo d, sin excepción. -/
theorem ventana_es_oeis_A005581 (d : Int) :
    (d - 1) * (d - 2) * (d - 3) - 6 * (d - 3) = (d - 4) * (d - 3) * (d + 1) := by
  ring

/-  ── H-hodge-loci-dimension-n (P → P-Lean): la clase (m,m) NUEVA, para TODA
    dimensión par 2m, no solo superficies (m=1) ──

    Para una hipersuperficie lisa X_d^{2m} ⊂ P^{2m+1} que contiene un P^m
    (un "plano" L), H-hodge-loci-dimension-n da el argumento (Chern classes
    de N_{L/X}, CITADO, no re-derivado aquí) de que [L] es una clase (m,m)
    GENUINAMENTE NUEVA — no proporcional a la clase hiperplana h^m — para
    TODO d≥2, no solo el caso m=1 (rectas en superficies) ya conocido.

    LA PIEZA QUE FALTABA POR DEMOSTRAR: el argumento se apoya en dos hechos
    geométricos CITADOS (L·h^m=1, h^m·h^m=d) y UNA obstrucción aritmética
    que sí se demuestra aquí. Si [L]=c·h^m para algún c∈ℚ, entonces de
    L·h^m=1=c·d sale c=1/d, y L·L=c²·d=1/d — que debe ser un ENTERO (los
    números de intersección de ciclos algebraicos lo son, hecho citado).
    Pero 1/d NUNCA es entero para d≥2: es la obstrucción, para TODO d≥2 y
    TODO m≥1 (el argumento no depende de m, solo de d). -/

/-- LA OBSTRUCCIÓN ARITMÉTICA: no existe c∈ℚ con c·d=1 y c²·d entero, para
    NINGÚN entero d≥2. Es lo que hace imposible que [L]=c·h^m — la pieza
    aritmética, aislada, del argumento geométrico de H-hodge-loci-
    dimension-n (Chern classes citadas, no re-derivadas). -/
theorem no_proporcional_a_h_potencia_m (d : ℤ) (hd : 2 ≤ d) :
    ¬ ∃ c : ℚ, c * (d : ℚ) = 1 ∧ ∃ n : ℤ, c ^ 2 * (d : ℚ) = (n : ℚ) := by
  rintro ⟨c, hcd, n, hn⟩
  have hd0 : (d : ℚ) ≠ 0 := by
    have : (0 : ℤ) < d := by omega
    exact_mod_cast this.ne'
  have hc : c = 1 / d := by
    field_simp
    linarith [hcd]
  rw [hc] at hn
  have hn' : (n : ℚ) * d = 1 := by
    field_simp at hn
    linarith [hn]
  have hnd : n * d = 1 := by exact_mod_cast hn'
  have hddvd : d ∣ 1 := ⟨n, by linarith [hnd, mul_comm n d]⟩
  have := Int.le_of_dvd (by norm_num) hddvd
  omega

