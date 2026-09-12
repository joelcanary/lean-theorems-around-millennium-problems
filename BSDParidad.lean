/-
  BSDParidad.lean — paridad de conteos de Tunnell vía involución sin puntos fijos

  B-paridad-conteos (nivel P, demostrado en papel, nunca formalizado):
  los cuatro conteos de Tunnell A, B, A_par, B_par
  (symbolica/plugins/bsd_congruentes.py, `_representaciones(n,a,b,c)` con
  (a,b,c) ∈ {(2,1,32), (2,1,8), (4,1,32), (4,1,8)}) son SIEMPRE pares para
  n (o m=n/2) impar libre de cuadrados. Demostración por involución:
  σ(x,y,z)=(x,−y,z) preserva la ecuación a·x²+y²+c·z²=n (no hay término
  cruzado). Sus puntos fijos son las soluciones con y=0, es decir
  n=a·x²+c·z² — pero en LOS CUATRO CASOS a y c son PARES, así que esa suma
  es siempre PAR, mientras que n (o m) es IMPAR por hipótesis: nunca hay
  puntos fijos. Sin puntos fijos ⟹ las soluciones se emparejan (x,y,z)↔
  (x,−y,z) ⟹ cardinal PAR.

  Esta pieza se demuestra en DOS capas:
  1. El LEMA ABSTRACTO (no está en Mathlib, se busca y no aparece): un
     Finset con una involución SIN puntos fijos tiene cardinal par. Prueba
     propia por inducción fuerte, quitando un par {x, f x} cada vez.
  2. La APLICACIÓN a los cuatro conteos de Tunnell, con el conjunto de
     soluciones representado explícitamente como Finset (acotado, ya que
     a,c>0 fuerza |x|,|z| ≤ √n), y la prueba de "sin puntos fijos" que es
     PURA ARITMÉTICA de paridad (a,c pares, n impar ⟹ a·x²+c·z² par ≠ n).
-/
import Mathlib.Tactic

namespace BSDParidad

/-  ── CAPA 1: el lema abstracto de conteo por involución ──────────────── -/

/-- Un Finset con una involución SIN puntos fijos tiene cardinal PAR.
    No encontrado en Mathlib (se buscó `card_modEq_card_fixedPoints` y
    variantes de `MulAction`, ninguna aplica sin montar una acción de
    grupo completa) — demostrado aquí por inducción fuerte en `S.card`,
    quitando el par {x, f x} en cada paso. -/
theorem even_card_of_fixedPointFree_involution {α : Type*} [DecidableEq α] :
    ∀ S : Finset α, ∀ f : α → α, (∀ x ∈ S, f x ∈ S) → (∀ x ∈ S, f (f x) = x) →
      (∀ x ∈ S, f x ≠ x) → Even S.card := by
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro f hmaps hinv hfree
    rcases S.eq_empty_or_nonempty with hemp | ⟨x, hx⟩
    · simp [hemp]
    · set y := f x with hydef
      have hy : y ∈ S := hmaps x hx
      have hxy : x ≠ y := (hfree x hx).symm
      set S' := (S.erase x).erase y with hS'def
      have hxS' : x ∉ S' := by simp [hS'def]
      have hyS' : y ∉ S' := by simp [hS'def]
      have hss : S' ⊂ S := by
        apply Finset.ssubset_iff_of_subset (by
          intro a ha
          simp only [hS'def, Finset.mem_erase] at ha
          exact ha.2.2) |>.mpr
        exact ⟨x, hx, hxS'⟩
      have hcard : S.card = S'.card + 2 := by
        have h1 : (S.erase x).card = S.card - 1 := Finset.card_erase_of_mem hx
        have hyS_erase : y ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
        have h2 : S'.card = (S.erase x).card - 1 := Finset.card_erase_of_mem hyS_erase
        have hSpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨x, hx⟩
        have hSpos2 : 1 ≤ (S.erase x).card := Finset.card_pos.mpr ⟨y, hyS_erase⟩
        omega
      have hfinj : ∀ a ∈ S, ∀ b ∈ S, f a = f b → a = b := by
        intro a ha b hb hab
        have := hinv a ha
        rw [hab, hinv b hb] at this
        exact this.symm
      have hmaps' : ∀ z ∈ S', f z ∈ S' := by
        intro z hz
        have hzS : z ∈ S := by
          simp only [hS'def, Finset.mem_erase] at hz
          exact hz.2.2
        have hzx : z ≠ x := by
          simp only [hS'def, Finset.mem_erase] at hz
          exact hz.2.1
        have hzy : z ≠ y := by
          simp only [hS'def, Finset.mem_erase] at hz
          exact hz.1
        have hfz : f z ∈ S := hmaps z hzS
        have hfzx : f z ≠ x := by
          intro hcon
          apply hzy
          have hfyx : f y = x := by rw [hydef]; exact hinv x hx
          have heq : f z = f y := hcon.trans hfyx.symm
          exact hfinj z hzS y hy heq
        have hfzy : f z ≠ y := by
          intro hcon
          apply hzx
          have heq : f z = f x := hcon.trans hydef
          exact hfinj z hzS x hx heq
        simp only [hS'def, Finset.mem_erase]
        exact ⟨hfzy, hfzx, hfz⟩
      have hinv' : ∀ z ∈ S', f (f z) = z := by
        intro z hz
        have hzS : z ∈ S := by
          simp only [hS'def, Finset.mem_erase] at hz; exact hz.2.2
        exact hinv z hzS
      have hfree' : ∀ z ∈ S', f z ≠ z := by
        intro z hz
        have hzS : z ∈ S := by
          simp only [hS'def, Finset.mem_erase] at hz; exact hz.2.2
        exact hfree z hzS
      obtain ⟨k, hk⟩ := ih S' hss f hmaps' hinv' hfree'
      exact ⟨k + 1, by omega⟩

/-  ── CAPA 2: aplicación a los cuatro conteos de Tunnell ──────────────── -/

/-- El conjunto de soluciones de a·x²+y²+c·z²=n, como Finset explícito
    (acotado por Icc(-n,n) en las tres coordenadas — cota floja pero
    suficiente: a,c≥1 y n≥0 fuerzan x²,y²,z² ≤ n). Coincide con lo que
    cuenta `_representaciones(n,a,1,c)` en
    symbolica/plugins/bsd_congruentes.py (A, B, A_par, B_par son las
    cuatro instancias (a,c) ∈ {(2,32),(2,8),(4,32),(4,8)}). -/
noncomputable def solTunnell (a c n : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc (-n) n) ×ˢ (Finset.Icc (-n) n) ×ˢ (Finset.Icc (-n) n)).filter
    (fun p => a * p.1 ^ 2 + p.2.1 ^ 2 + c * p.2.2 ^ 2 = n)

/-- LOS CUATRO CONTEOS DE TUNNELL SON SIEMPRE PARES, para n impar y a,c
    PARES POSITIVOS (los cuatro casos reales: (a,c)∈{(2,32),(2,8),(4,32),
    (4,8)}, todos con a,c pares y positivos). B-paridad-conteos, ahora
    demostrado por el kernel: la involución σ(x,y,z)=(x,−y,z) no tiene
    puntos fijos porque un punto fijo exigiría y=0, es decir n=a·x²+c·z² —
    PAR, contradiciendo que n es impar. Sin puntos fijos,
    `even_card_of_fixedPointFree_involution` da la paridad directamente.
    LAS HIPÓTESIS 0<a, 0<c NO las usa la prueba de paridad en sí (el
    argumento de puntos fijos es puro, no necesita signo) — pero SÍ son
    necesarias para que `solTunnell` (acotado por Icc(-n,n), no por la
    ecuación) coincida de verdad con `_representaciones`: con a≤0, por
    ejemplo, la ecuación no acotaría x y el Finset estaría, silenciosamente,
    contando solo una FRACCIÓN de las soluciones reales. Se exigen aquí
    para que el teorema, tal como está enunciado, sea honesto sobre a qué
    corresponde exactamente. -/
theorem tunnell_par (a c n : ℤ) (ha : Even a) (hc : Even c) (hn : Odd n) (_hn0 : 0 ≤ n)
    (_ha_pos : 0 < a) (_hc_pos : 0 < c) :
    Even (solTunnell a c n).card := by
  apply even_card_of_fixedPointFree_involution (solTunnell a c n) (fun p => (p.1, -p.2.1, p.2.2))
  · intro p hp
    simp only [solTunnell, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
    obtain ⟨⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, ⟨hz1, hz2⟩⟩, heq⟩ := hp
    exact ⟨⟨⟨hx1, hx2⟩, ⟨by omega, by omega⟩, ⟨hz1, hz2⟩⟩, by rw [neg_sq]; exact heq⟩
  · intro p hp
    simp
  · intro p hp hcon
    simp only [solTunnell, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨_, heq⟩ := hp
    have hy0 : p.2.1 = 0 := by
      have heqp : (p.1, -p.2.1, p.2.2) = p := hcon
      have : -p.2.1 = p.2.1 := congrArg (fun q => q.2.1) heqp
      omega
    rw [hy0] at heq
    have heven : Even (a * p.1 ^ 2 + (0 : ℤ) ^ 2 + c * p.2.2 ^ 2) := by
      obtain ⟨k, hk⟩ := ha
      obtain ⟨j, hj⟩ := hc
      exact ⟨k * p.1 ^ 2 + 0 + j * p.2.2 ^ 2, by rw [hk, hj]; ring⟩
    rw [heq] at heven
    exact (Int.not_odd_iff_even.mpr heven) hn

end BSDParidad
