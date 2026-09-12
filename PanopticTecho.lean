import PanopticDuplicados

/-!
# El techo de los anotadores, y la asimetría que lo acompaña

La sección 6 del informe sostiene que el techo de la tarea está en las
etiquetas: un anotador no marca el 45,9 % de lo que marca otro, y puntuar a un
anotador contra otro con la métrica del reto da PQ 0,356 y 0,334. Aquí se
demuestra la parte que es matemática y no medición.

## Dos hechos, y la asimetría entre ellos

Con umbral IoU > 1/2 y anotaciones **disjuntas** entre sí:

* `empareja_a_lo_sumo_una` — una predicción empareja con **como mucho una**
  anotación. La prueba cabe en tres líneas: solapar más de la mitad obliga a
  ocupar más de la mitad de la predicción, y dos anotaciones disjuntas no caben
  las dos en más de la mitad.
* Las predicciones, en cambio, **no** tienen por qué ser disjuntas, así que
  varias pueden emparejar con la misma anotación. Esa es exactamente la puerta
  que `PanopticDuplicados.pq_dup_iff` demuestra que se puede empujar.

La métrica ya asume implícitamente el primer hecho; lo que le falta es exigir el
segundo. Enunciarlos juntos deja claro que el emparejamiento uno a uno no es una
restricción nueva: es la simetría que faltaba.

## El techo

Si dos anotadores marcan **distinto número** de instancias en una imagen,
ninguna predicción, por buena que sea, alcanza PQ 1 contra los dos a la vez
(`techo_dos_anotadores`). La cota es estricta y su holgura es la mitad del
desacuerdo. No es una limitación de nuestros modelos: es de la tarea.
-/

namespace Panoptic

open Finset

variable {α : Type*} [DecidableEq α]

/-- IoU de dos conjuntos finitos de píxeles. Con la convención de Lean `x/0 = 0`,
el IoU de dos conjuntos vacíos es `0`, que es lo que conviene: no hay nada que
emparejar. -/
noncomputable def iou (X Y : Finset α) : ℝ := ((X ∩ Y).card : ℝ) / ((X ∪ Y).card : ℝ)

/-- Solapar más de la mitad con `A` obliga a ocupar más de la mitad de `P`. -/
lemma card_inter_gt_of_iou (P A : Finset α) (h : (1 : ℝ) / 2 < iou P A) :
    (P.card : ℝ) < 2 * ((P ∩ A).card : ℝ) := by
  unfold iou at h
  have hu : (0 : ℝ) < ((P ∪ A).card : ℝ) := by
    rcases Nat.eq_zero_or_pos (P ∪ A).card with h0 | hpos
    · rw [h0] at h; norm_num at h
    · exact_mod_cast hpos
  have hle : (P.card : ℝ) ≤ ((P ∪ A).card : ℝ) := by
    exact_mod_cast card_le_card subset_union_left
  rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 2) hu] at h
  linarith

/-- **Una predicción empareja con como mucho una anotación.**

Si las anotaciones son disjuntas —lo son: son instancias distintas de la misma
imagen— ninguna predicción puede superar el umbral con dos a la vez. Es la razón
de que el evaluador pueda acumular pares sin ambigüedad por ese lado. -/
theorem empareja_a_lo_sumo_una (P A B : Finset α) (hAB : Disjoint A B)
    (hA : (1 : ℝ) / 2 < iou P A) (hB : (1 : ℝ) / 2 < iou P B) : False := by
  have hpa := card_inter_gt_of_iou P A hA
  have hpb := card_inter_gt_of_iou P B hB
  have hdis : Disjoint (P ∩ A) (P ∩ B) :=
    (hAB.mono inter_subset_right inter_subset_right)
  have hsub : (P ∩ A) ∪ (P ∩ B) ⊆ P := union_subset inter_subset_left inter_subset_left
  have hcard : ((P ∩ A).card : ℝ) + ((P ∩ B).card : ℝ) ≤ (P.card : ℝ) := by
    have : (P ∩ A).card + (P ∩ B).card = ((P ∩ A) ∪ (P ∩ B)).card :=
      (card_union_of_disjoint hdis).symm
    have h2 : ((P ∩ A) ∪ (P ∩ B)).card ≤ P.card := card_le_card hsub
    exact_mod_cast this ▸ h2
  linarith

/-- El denominador de PQ contra **un** anotador depende solo de cuántas
predicciones y cuántas anotaciones hay: `(m + a)/2`. Los aciertos se cancelan,
porque cada uno quita un falso positivo y un falso negativo, que valían ½ cada
uno. -/
lemma den_una_anotacion (tp m a : ℕ) (h1 : tp ≤ m) (h2 : tp ≤ a) :
    den tp (m - tp) (a - tp) = ((m : ℝ) + a) / 2 := by
  unfold den
  rw [Nat.cast_sub h1, Nat.cast_sub h2]
  ring

/-- **El techo del desacuerdo.**

Dos anotadores que marcan `a` y `b` instancias con `a < b`, y una predicción con
`m` instancias puntuada contra los dos. Como cada acierto contra el primero está
limitado por `a` y cada acierto contra el segundo por `m`, el numerador de PQ se
queda **estrictamente** por debajo del denominador: PQ < 1 es forzoso.

La holgura es `(b - a)/2`: exactamente la mitad del desacuerdo entre anotadores.
No hay predicción, ni modelo, que la salve. -/
theorem techo_dos_anotadores (m a b tpA tpB : ℕ)
    (hab : a < b) (hA : tpA ≤ a) (hB : tpB ≤ m) :
    ((tpA : ℝ) + tpB) < (m : ℝ) + ((a : ℝ) + b) / 2 := by
  have h1 : (tpA : ℝ) ≤ (a : ℝ) := by exact_mod_cast hA
  have h2 : (tpB : ℝ) ≤ (m : ℝ) := by exact_mod_cast hB
  have h3 : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  linarith

/-- La misma cota, escrita como PQ: el numerador (suma de IoU, cada uno ≤ 1, así
que a lo sumo el número de aciertos) sobre el denominador combinado de los dos
anotadores. Si discrepan en el recuento, **PQ < 1 pase lo que pase**. -/
theorem pq_lt_one_de_desacuerdo (sA sB : ℝ) (m a b tpA tpB : ℕ)
    (hab : a < b) (hA : tpA ≤ a) (hB : tpB ≤ m)
    (hsA : sA ≤ tpA) (hsB : sB ≤ tpB) (hm : 0 < m) :
    (sA + sB) / ((m : ℝ) + ((a : ℝ) + b) / 2) < 1 := by
  have hden : (0 : ℝ) < (m : ℝ) + ((a : ℝ) + b) / 2 := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    positivity
  rw [div_lt_one hden]
  have := techo_dos_anotadores m a b tpA tpB hab hA hB
  linarith

/-- El caso del informe, con sus números: en las imágenes con dos anotadores uno
marca 586 instancias y el otro 1083 (497 de diferencia, el 45,9 % que cita la
sección 6). Con `m = 700` predicciones perfectas contra el primero, el PQ
combinado no puede pasar de `(586 + 700) / (700 + 1669/2) = 0,8381`, y eso
suponiendo IoU 1 en todo lo que acierta: el techo no lo pone el modelo. -/
example : ((586 : ℝ) + 700) / (700 + ((586 : ℝ) + 1083) / 2) < 0.839 := by
  norm_num

end Panoptic
