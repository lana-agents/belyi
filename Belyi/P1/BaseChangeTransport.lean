/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.P1.AffineChartBaseChange
import Belyi.P1.PointsBaseChange

/-!
# Transport of the marked and valued points across the base-change isomorphism

The comparison morphism `Belyi.P1.toPullback k₀ K : P1 K ⟶ pullback (P1 k₀ ↘ Spec k₀)
(specAlgebraMap k₀ K)` is an isomorphism (`Belyi.P1.isIso_toPullback`, from
`Belyi/P1/BaseChangeIso.lean`), realizing the canonical identification
`ℙ¹_{k₀} ×_{k₀} K ≅ ℙ¹_K`. This file phrases the naturality facts of #110 (marked-point
transport from `Belyi/P1/PointsBaseChange.lean`, valued-point transport from
`Belyi/P1/AffineChartBaseChange.lean`) *across* that identification, i.e. through the
first projection `pullback.fst`. These are the compatibilities that the pair version of
statement B3 (#48) consumes: a valued point / marked point of `ℙ¹_{k₀}` base-changes to
the corresponding point of `ℙ¹_K`.

## Main results

* `Belyi.P1.point_comp_toPullback`: for a `K`-algebra `R` (hence a `k₀`-algebra by
  restriction) and `t : R`, the `K`-valued point `point K t` maps, across the
  identification `toPullback`, to the base change of the `k₀`-valued point `point k₀ t`;
  concretely `point K t ≫ toPullback k₀ K = pullback.lift (point k₀ t) …`.
* `Belyi.P1.toPullback_base_zero` / `_one` / `_infty`: over fields `k₀ ⊆ K`, the first
  projection of the base change sends the image of the marked point of `ℙ¹_K` under
  `toPullback` back to the corresponding marked point of `ℙ¹_{k₀}`.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory Limits

section ValuedPoints

variable (k₀ K : Type u) [CommRing k₀] [CommRing K] [Algebra k₀ K]
variable {R : Type u} [CommRing R] [Algebra k₀ R] [Algebra K R] [IsScalarTower k₀ K R]

/-- The `k₀`-valued point `point k₀ t` is a morphism over `Spec k₀` in the way required to
lift `point K t` into the base change: its composite with the structure morphism agrees,
across `specAlgebraMap`, with the `Spec K`-side leg. -/
lemma point_structMap_specAlgebraMap_compat (t : R) :
    point k₀ t ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)) =
      Spec.map (CommRingCat.ofHom (algebraMap K R)) ≫ specAlgebraMap k₀ K := by
  rw [structMap_eq, point_structMap, specAlgebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

/-- **Valued-point transport across the identification `ℙ¹_{k₀} ×_{k₀} K ≅ ℙ¹_K`.**
For a `K`-algebra `R` (a `k₀`-algebra by restriction) and `t : R`, the `K`-valued point of
affine coordinate `t` maps, under the comparison isomorphism `toPullback`, to the point of
the base change whose `ℙ¹_{k₀}`-leg is the `k₀`-valued point of the same coordinate `t` and
whose `Spec K`-leg is `Spec (algebraMap K R)`. This is the naturality of valued points under
the canonical identification, consumed by the pair version of B3 (#48). -/
lemma point_comp_toPullback (t : R) :
    point K t ≫ toPullback k₀ K =
      pullback.lift (point k₀ t) (Spec.map (CommRingCat.ofHom (algebraMap K R)))
        (point_structMap_specAlgebraMap_compat k₀ K t) := by
  apply pullback.hom_ext
  · rw [Category.assoc, toPullback_fst, point_comp_mapOfAlgebra, pullback.lift_fst]
  · rw [Category.assoc, toPullback_snd, pullback.lift_snd, structMap_eq, point_structMap]

end ValuedPoints

section MarkedPoints

variable (k₀ K : Type u) [Field k₀] [Field K] [Algebra k₀ K]

/-- **Marked-point transport across the identification `ℙ¹_{k₀} ×_{k₀} K ≅ ℙ¹_K`** for `0`.
The first projection of the base change sends the image of `zero K` under the comparison
isomorphism `toPullback` back to `zero k₀`. -/
lemma toPullback_base_zero :
    (pullback.fst (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)).base
        ((toPullback k₀ K).base (zero K)) = zero k₀ := by
  change (toPullback k₀ K ≫ pullback.fst _ _).base (zero K) = zero k₀
  rw [toPullback_fst]
  exact mapOfAlgebra_base_zero k₀ K

/-- **Marked-point transport across the identification `ℙ¹_{k₀} ×_{k₀} K ≅ ℙ¹_K`** for `1`.
The first projection of the base change sends the image of `one K` under the comparison
isomorphism `toPullback` back to `one k₀`. -/
lemma toPullback_base_one :
    (pullback.fst (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)).base
        ((toPullback k₀ K).base (one K)) = one k₀ := by
  change (toPullback k₀ K ≫ pullback.fst _ _).base (one K) = one k₀
  rw [toPullback_fst]
  exact mapOfAlgebra_base_one k₀ K

/-- **Marked-point transport across the identification `ℙ¹_{k₀} ×_{k₀} K ≅ ℙ¹_K`** for `∞`.
The first projection of the base change sends the image of `infty K` under the comparison
isomorphism `toPullback` back to `infty k₀`. -/
lemma toPullback_base_infty :
    (pullback.fst (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)).base
        ((toPullback k₀ K).base (infty K)) = infty k₀ := by
  change (toPullback k₀ K ≫ pullback.fst _ _).base (infty K) = infty k₀
  rw [toPullback_fst]
  exact mapOfAlgebra_base_infty k₀ K

end MarkedPoints

end Belyi.P1
