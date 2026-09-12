import PanopticDuplicados

/-!
# Cuándo compensa añadir una detección: `p · j > PQ / 2`

La sección 3 del informe deriva a mano la regla que decidió los dos umbrales de
la campaña: añadir un candidato al conjunto de predicciones sube el PQ esperado
exactamente cuando

    p · j  >  PQ / 2,

con `p` la probabilidad de que el candidato empareje con una anotación y `j` el
IoU que consigue cuando empareja. Aquí queda demostrada.

## Por qué la regla es exacta y no una aproximación

El paso que hace todo el trabajo es que **el denominador no depende de si el
candidato acierta**:

* si acierta, convierte un falso negativo en un verdadero positivo:
  `n → n+1`, `fn → fn-1`, y el denominador `n + (fp+fn)/2` sube `1 - ½ = ½`;
* si falla, añade un falso positivo: `fp → fp+1`, y el denominador sube `½`.

Es `den_acierto` y `den_fallo` abajo. Como el denominador vale `D + ½` en las
dos ramas, la esperanza del cociente **es** el cociente de la esperanza —no hay
que apelar a ninguna linealización— y el numerador esperado es `s + p·j`. De ahí
sale la regla con un `nlinarith`.

Esto es también la razón de que el umbral no dependa de qué error cometes: un
falso positivo cuesta ½ y una anotación perdida cuesta ½, exactamente lo mismo.
-/

namespace Panoptic

/-- Si el candidato **acierta**, un falso negativo pasa a verdadero positivo y el
denominador sube justo `½`. -/
lemma den_acierto (n fp m : ℕ) :
    den (n + 1) fp m = den n fp (m + 1) + 1 / 2 := by
  unfold den; push_cast; ring

/-- Si el candidato **falla**, aparece un falso positivo y el denominador sube
justo `½`: el mismo coste que acertar. -/
lemma den_fallo (n fp m : ℕ) :
    den n (fp + 1) (m + 1) = den n fp (m + 1) + 1 / 2 := by
  unfold den; push_cast; ring

/-- El PQ esperado tras añadir un candidato que empareja con probabilidad `p` y,
cuando empareja, con IoU `j`. El denominador es el mismo en las dos ramas
(`den_acierto`, `den_fallo`), así que esta expresión es exacta. -/
noncomputable def pqCandidato (s p j : ℝ) (n fp fn : ℕ) : ℝ :=
  (s + p * j) / (den n fp fn + 1 / 2)

/-- **La regla de la sección 3, demostrada.**

Añadir el candidato sube el PQ esperado **si y solo si** `p · j > PQ / 2`. -/
theorem pq_candidato_iff (s p j : ℝ) (n fp fn : ℕ) (hd : 0 < den n fp fn) :
    pq s n fp fn < pqCandidato s p j n fp fn ↔ pq s n fp fn / 2 < p * j := by
  have hd2 : (0 : ℝ) < den n fp fn + 1 / 2 := by linarith
  unfold pqCandidato
  rw [pq_def, div_lt_div_iff₀ hd hd2, div_div,
      div_lt_iff₀ (by positivity : (0:ℝ) < den n fp fn * 2)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- La forma en que se usa al decidir: si el candidato supera el umbral, entra. -/
theorem pq_lt_candidato (s p j : ℝ) (n fp fn : ℕ) (hd : 0 < den n fp fn)
    (h : pq s n fp fn / 2 < p * j) : pq s n fp fn < pqCandidato s p j n fp fn :=
  (pq_candidato_iff s p j n fp fn hd).mpr h

/-- Y el recíproco, que es el que de verdad usamos: por debajo del umbral el
candidato **baja** la nota, así que rechazarlo no es prudencia, es aritmética. -/
theorem candidato_le_pq (s p j : ℝ) (n fp fn : ℕ) (hd : 0 < den n fp fn)
    (h : p * j ≤ pq s n fp fn / 2) : pqCandidato s p j n fp fn ≤ pq s n fp fn := by
  rw [← not_lt]
  intro hc
  exact absurd ((pq_candidato_iff s p j n fp fn hd).mp hc) (not_lt.mpr h)

/-- El punto de equilibrio, despejado: con el PQ de operación de la campaña
(`≈ 0.35`) el umbral cae en `p·j ≈ 0.175`, y con `j ≈ 0.5` en `p ≈ 0.35`. Es el
rango `0.33–0.37` que el informe cita, y explica por qué los dos escalares
ajustados a mano ya estaban en el equilibrio del teorema: no había nada que
ganar moviéndolos. -/
theorem umbral_equilibrio (s p j : ℝ) (n fp fn : ℕ) (hd : 0 < den n fp fn)
    (hj : 0 < j) :
    pq s n fp fn < pqCandidato s p j n fp fn ↔ pq s n fp fn / (2 * j) < p := by
  rw [pq_candidato_iff s p j n fp fn hd,
      div_lt_iff₀ (by norm_num : (0:ℝ) < 2),
      div_lt_iff₀ (by positivity : (0:ℝ) < 2 * j)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

end Panoptic
