# Verifying the results, and the Mathlib contributions

## What "verified" means here

Every theorem in this repository is checked by the Lean 4 kernel against Mathlib. There are
no `sorry`s, and the main theorems depend only on the three standard axioms of Lean's
mathematical library:

```
propext, Classical.choice, Quot.sound
```

You can reproduce this check yourself. After building (below), create a file

```lean
import RiemannRedheffer
import SmithDeterminant
import BSDParidad
import BSDTwist
import HodgeMathlib
import PanopticUmbral
import PanopticFamilia
#print axioms Redheffer.redheffer_general
#print axioms Smith.smith_determinant
#print axioms BSDParidad.tunnell_par
#print axioms BSDTwist.a_p_twist
#print axioms Panoptic.umbral_exacto
#print axioms PanopticFamilia.ningun_peso_lo_arregla
```

and run `lake env lean Axiomas.lean`. The GitHub workflow in `.github/workflows/lean.yml`
does exactly this on every push.

## Building

```bash
# toolchain is pinned in lean-toolchain (leanprover/lean4:v4.32.0); elan picks it up
lake exe cache get      # downloads Mathlib's compiled oleans for the pinned version
lake build              # builds the twelve libraries listed in lakefile.toml
```

A from-source Mathlib build is not needed; `cache get` takes a few minutes, the project
itself builds in under a minute.

## Reading the files

Each `.lean` file starts with a long comment that states the theorem, gives the proof idea,
cites the original reference, and says what was searched for in Mathlib before claiming
novelty. The comments are in Spanish (the language the campaign was run in); the theorem
names are a mix of Spanish and English. The English documents in `docs/` follow the same
order and translate the mathematics; the Mathlib-facing versions in `mathlib-pr/` are
fully in English.

## Mathlib contributions

Two pieces were judged useful enough for Mathlib itself and were submitted:

| PR | Content | Notes |
|---|---|---|
| [mathlib4#43749](https://github.com/leanprover-community/mathlib4/pull/43749) | `IsMultiplicative.prodPrimeFactors_one_sub`: `∏_{p ∣ n} (1 − f p) = Σ_{d ∣ n} μ d · f d` for **every** `n ≠ 0` (Mathlib had only the squarefree case). Source: `mathlib-pr/MoebiusProdPR.lean`. | 33 lines, no new imports; proof avoids `radical` on purpose so that `Moebius.lean` keeps its two imports. |
| [mathlib4#43758](https://github.com/leanprover-community/mathlib4/pull/43758) | New file `Mathlib/NumberTheory/ArithmeticFunction/Redheffer.lean`: `Matrix.zetaMatrix`, `Matrix.redheffer`, `ArithmeticFunction.mertens`, and `Matrix.det_redheffer`. Source: `mathlib-pr/Redheffer.lean`. | Neither the Mertens function nor the Redheffer matrix existed in Mathlib. Under review; the first round of review (naming, `mertens` as an `ArithmeticFunction`, moving the general lemma to `Moebius.lean`) is addressed. |

The `mathlib-pr/` files target Mathlib **master** (module system, `public import`,
`@[expose] public section`, current lemma names such as `det_of_isUpperTriangular`) and are
therefore not part of this project's default build, which pins Mathlib `v4.32.0`.

Mathlib asks contributors to disclose AI assistance; both pull requests carry that
disclosure and the `LLM-generated` label, and the review is answered by the author in
person. The same disclosure applies to this repository (see the README).

## How the results were found

The campaign that produced these files worked from computation towards proof: a candidate
identity was first tested numerically (thousands of instances, exact arithmetic), then
formalized, and the formalization was only counted when the kernel accepted it. Several
candidates were refuted along the way and are not in this repository. The figures in
`figures/` keep that habit: each one recomputes the theorem's two sides from scratch and
asserts they agree before drawing.
