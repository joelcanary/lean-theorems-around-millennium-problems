import Mathlib.Tactic

/-!
# Por qué una métrica que cuenta todos los pares se puede inflar duplicando

La Panoptic Quality del reto de filamentos solares (IEEE BigData Cup 2026) es

    PQ = (Σ_{pares emparejados} IoU) / (|TP| + ½|FP| + ½|FN|),

y el evaluador oficial acumula **todos** los pares `(predicción, verdad)` con
IoU > ½, no un emparejamiento uno a uno. Al fundir dos tuberías nuestras con un
filtro laxo de duplicados medimos `PQ = 0.4852` con **458 aciertos sobre 456
instancias reales**: imposible, y la señal de que algo estaba mal en la métrica y
no en el modelo.

Este fichero demuestra que esa aritmética no era un accidente:

* `pq_dup_iff` — con acumulación de todos los pares, añadir un duplicado de una
  predicción ya emparejada, con IoU `v`, sube el PQ **exactamente cuando
  `v > PQ`**. No hace falta que el duplicado aporte información: basta con que
  sea mejor que la media ponderada que ya llevas.
* `pq_fp_lt` — con emparejamiento uno a uno el mismo duplicado no puede
  emparejar (su verdad ya está tomada), cuenta como falso positivo, y el PQ
  **baja siempre**.

Juntos dicen lo que el informe afirma con números: la métrica tal y como está
especificada es explotable, y exigir emparejamiento uno a uno la arregla.

La medida que motivó esto: en AFINA el campeón tiene PQ 0.4326 y sus aciertos
promedian IoU 0.687. Como `0.687 > 0.4326`, `pq_dup_iff` dice que **cada
duplicado subía la nota**, que es justo lo que observamos.
-/

namespace Panoptic

/-- Panoptic Quality: `s` es la suma de los IoU de los pares emparejados y `n`
cuántos son; `fp` y `fn` cuentan predicciones sin verdad y verdades sin
predicción, y pesan ½ cada una. -/
noncomputable def pq (s : ℝ) (n fp fn : ℕ) : ℝ :=
  s / (n + (fp + fn) / 2)

/-- El denominador de PQ. -/
noncomputable def den (n fp fn : ℕ) : ℝ := (n : ℝ) + (fp + fn) / 2

lemma pq_def (s : ℝ) (n fp fn : ℕ) : pq s n fp fn = s / den n fp fn := rfl

lemma den_nonneg (n fp fn : ℕ) : 0 ≤ den n fp fn := by
  unfold den
  positivity

/-- **Duplicar sube la nota exactamente cuando el duplicado supera al PQ.**

Añadir una predicción que empareja con una verdad ya emparejada, con IoU `v`,
suma `v` al numerador y `1` al denominador (un TP más), y no crea ningún falso
positivo, porque el evaluador acumula todos los pares por encima del umbral.
El PQ resultante es mayor si y solo si `v` es mayor que el PQ de partida. -/
theorem pq_dup_iff (s v : ℝ) (n fp fn : ℕ) (hd : 0 < den n fp fn) :
    pq s n fp fn < pq (s + v) (n + 1) fp fn ↔ pq s n fp fn < v := by
  have hd1 : (0 : ℝ) < den n fp fn + 1 := by linarith
  have hden : den (n + 1) fp fn = den n fp fn + 1 := by
    unfold den; push_cast; ring
  rw [pq_def, pq_def, hden]
  rw [div_lt_div_iff₀ hd hd1, div_lt_iff₀ hd]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- La misma cuenta, en la forma en que se usa: si el duplicado es mejor que el
PQ actual, la nota sube **estrictamente**. -/
theorem pq_lt_pq_dup (s v : ℝ) (n fp fn : ℕ) (hd : 0 < den n fp fn)
    (hv : pq s n fp fn < v) : pq s n fp fn < pq (s + v) (n + 1) fp fn :=
  (pq_dup_iff s v n fp fn hd).mpr hv

/-- **Con emparejamiento uno a uno, el duplicado baja la nota.**

Si cada verdad sólo puede emparejarse una vez, el duplicado no empareja: cuenta
como falso positivo. El numerador no cambia y el denominador crece en ½, así que
el PQ baja estrictamente siempre que hubiera algo que perder (`0 < s`). -/
theorem pq_fp_lt (s : ℝ) (n fp fn : ℕ) (hs : 0 < s) (hd : 0 < den n fp fn) :
    pq s n (fp + 1) fn < pq s n fp fn := by
  have hden : den n (fp + 1) fn = den n fp fn + 1 / 2 := by
    unfold den; push_cast; ring
  have hd2 : (0 : ℝ) < den n fp fn + 1 / 2 := by linarith
  rw [pq_def, pq_def, hden, div_lt_div_iff₀ hd2 hd]
  nlinarith

/-- La brecha entre las dos reglas, dicha de una vez: bajo acumulación de todos
los pares un duplicado suficientemente bueno sube la nota, mientras que bajo
emparejamiento uno a uno el mismo duplicado la baja. Una métrica que se puede
mover en direcciones opuestas según cómo se cuente no está midiendo calidad. -/
theorem duplicado_sube_pero_uno_a_uno_baja
    (s v : ℝ) (n fp fn : ℕ) (hs : 0 < s) (hd : 0 < den n fp fn)
    (hv : pq s n fp fn < v) :
    pq s n fp fn < pq (s + v) (n + 1) fp fn ∧ pq s n (fp + 1) fn < pq s n fp fn :=
  ⟨pq_lt_pq_dup s v n fp fn hd hv, pq_fp_lt s n fp fn hs hd⟩

/-- El caso medido en AFINA: PQ del campeón 0.4326 y IoU medio de sus aciertos
0.687. Como `0.4326 < 0.687`, duplicar subía la nota. Aquí se comprueba la
hipótesis con los números reales, para que el enunciado no dependa de creer la
tabla del informe. -/
example : (0.4326 : ℝ) < 0.687 := by norm_num

end Panoptic
