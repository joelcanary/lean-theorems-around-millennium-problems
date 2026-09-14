# The Panoptic Quality metric, exactly

**Files:** `PanopticDuplicados.lean`, `PanopticFamilia.lean`, `PanopticCandidato.lean`,
`PanopticQuitar.lean`, `PanopticTecho.lean`, `PanopticUmbral.lean`.

These theorems came out of the IEEE BigData Cup 2026 solar-filament segmentation challenge,
whose score is the Panoptic Quality (Kirillov et al., CVPR 2019):

```
PQ = Σ_{matched pairs} IoU / (TP + ½·FP + ½·FN),      a pair is matched when IoU > ½.
```

In the Lean files `pq s n fp fn = s / den n fp fn` with `s` the sum of the matched IoUs,
`n = TP`, and `den n fp fn = n + fp/2 + fn/2`. Every statement below is an exact
algebraic fact about that formula; none depends on any model or data.

## 1. When a duplicate raises the score (`PanopticDuplicados.lean`)

If the evaluator accumulates matched pairs without enforcing that each ground-truth
instance is used at most once, a *second* prediction of an already-matched instance,
with IoU `v`, adds `v` to the numerator and `1` to the denominator. Then

```lean
theorem pq_dup_iff (s v : ℝ) (n fp fn : ℕ) (hd : 0 < den n fp fn) :
    pq s n fp fn < pq (s + v) (n + 1) fp fn ↔ pq s n fp fn < v
```

**a duplicate raises PQ exactly when its IoU exceeds the current PQ.** With a one-to-one
matching the same prediction would instead count as a false positive and lower the score
(`pq_fp_lt`, `duplicado_sube_pero_uno_a_uno_baja`): the sign of the effect depends only on how
pairs are counted (`sube_o_baja_segun_se_cuente`).

![duplicates and PQ](../figures/panoptic_duplicates.png)

## 2. No reweighting removes the defect (`PanopticFamilia.lean`)

One might hope that the `½` weights on FP and FN are the culprit. For the whole family
`m a b s n fp fn = s / (n + a·fp + b·fn)`:

```lean
theorem dup_iff ... :  m a b s n fp fn < m a b (s + v) (n + 1) fp fn ↔ m a b s n fp fn < v
theorem ningun_peso_lo_arregla (s v : ℝ) (n fp fn : ℕ) :
    ∀ a b : ℝ, 0 < den a b n fp fn → m a b s n fp fn < v → m a b s n fp fn < m a b (s + v) (n + 1) fp fn
```

The threshold `v > (current score)` is the same for every choice of weights. Only the
false-positive penalty depends on the weights (`fp_baja` for `a > 0`, `fp_no_baja` for `a = 0`).

## 3. When adding a candidate detection pays (`PanopticCandidato.lean`)

A candidate that is a true match with probability `p` and, when matched, has IoU `j`
(and otherwise is a false positive) improves the expected score exactly when

```lean
theorem pq_candidato_iff ... : pq s n fp fn < pqCandidato s p j n fp fn ↔ pq s n fp fn / 2 < p * j
```

i.e. **`p · j > PQ / 2`**. This is exact, not an approximation: both branches move the
denominator by the same `½` (`den_acierto`, `den_fallo`), which is what makes the rule
so simple. `umbral_equilibrio` restates it as a threshold on `p` given `j`. In the challenge this
rule fixed two confidence thresholds.

## 3b. When removing a detection pays (`PanopticQuitar.lean`)

The mirror of §3. A detection already on the list contributes `p · j` to the numerator and
exactly `½` to the denominator whichever way it turns out (a true positive removed becomes a
false negative, `den_quitar_acierto`; a false positive removed just disappears,
`den_quitar_fallo`). Removing it raises the score exactly when

```lean
theorem pq_quitar_iff ... : pq s n fp fn < pqQuitar s p j n fp fn ↔ p * j < pq s n fp fn / 2
```

i.e. **`p · j < PQ / 2`**, with `quitar_le_pq` for the direction actually used (at or above
the threshold, removing never helps) and `quitar_candidato` closing the circuit with §3
(adding then removing returns the original score). In the challenge this is the rule that
decides whether a band of detections (by size, by grouping, by confidence) stays: measured on
validation, no band of the final model falls below `PQ/2 ≈ 0.216`, so the annotators' rule
"ignore filaments too small or too faint" adds nothing on top of the operating point.

## 4. The two-annotator ceiling (`PanopticTecho.lean`)

If two annotators mark **different numbers** of instances, `a < b`, in the same image, no
prediction reaches `PQ = 1` against both (`techo_dos_anotadores`, `pq_lt_one_de_desacuerdo`).
The slack is half the disagreement. This is a property of the task, not of any model.

The same file proves the fact that makes the metric's pair accumulation well defined on the
ground-truth side: with disjoint annotations and threshold `> ½`, **a prediction matches at
most one annotation** (`empareja_a_lo_sumo_una`), by a three-line counting argument.

## 5. The threshold `½` is exact (`PanopticUmbral.lean`)

Is `½` the right constant, or would any threshold do? With `≥ ½` the uniqueness above is
**false**: `A = {1,2}`, `B = {3,4}`, `P = {1,2,3,4}` gives `IoU(P,A) = IoU(P,B) = ½`
(`empata_con_dos_en_un_medio`). Hence

```lean
theorem umbral_exacto :
    (∀ P A B, Disjoint A B → ½ < iou P A → ½ < iou P B → False)
    ∧ ¬ (∀ P A B, Disjoint A B → ½ ≤ iou P A → ½ ≤ iou P B → False)
```

`½` is the **infimum** of the thresholds for which "P matches A" is a well-defined partial
function; below it (and at it) the matching has to be *chosen* by an assignment, which the
published formula does not do. And it locates the duplicate defect of §1: uniqueness is
guaranteed by the annotations being disjoint, a hypothesis nobody imposes on predictions.

## References

* A. Kirillov, K. He, R. Girshick, C. Rother, P. Dollár, *Panoptic Segmentation*, CVPR 2019.
