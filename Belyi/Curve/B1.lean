/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Curve.ToP1
import Belyi.P1.Transcendental
import Belyi.Dimension
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# B1: the morphism to `ℙ¹` attached to a non-constant rational function is finite

The finiteness statement of B1 (taxis issue #46), modulo the stalk hypotheses: let `X`
be an integral scheme, proper over a field `k`, whose local rings are valuation rings
of Krull dimension `≤ 1` (e.g. a smooth curve over `k`, once "smooth curves have DVR
stalks" lands). Then for every `t ∈ K(X)` transcendental over `k`, the induced
morphism `X ⟶ ℙ¹` (`Belyi.homOfFunctionField`) is finite.

Proof assembly: the morphism is proper (`isProper_homOfFunctionField`); its generic
point maps to the point of `ℙ¹` attached to `t` (`homOfFunctionField_genericPoint`),
which is not closed for transcendental `t`
(`P1.not_isClosed_singleton_point_of_transcendental`); hence all fibers are finite
(`finite_preimage_singleton_of_isClosedMap`, using Noetherianity from
`isNoetherian_of_over`), so the morphism is quasi-finite
(`LocallyQuasiFinite.of_finite_preimage_singleton`) and finite by Zariski's main
theorem (`IsFinite.of_isProper_of_locallyQuasiFinite`).

For a curve `X/k` in the sense of `Belyi.IsCurveOver`, all scheme-level hypotheses
hold (`IsCurveOver.isIntegral` and properness); the hypotheses `hX`/`hdim` on the
stalks remain to be discharged by the smoothness input (remaining part of #46).
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Scheme

variable (k : Type u) [Field k] (X : Scheme.{u}) [IrreducibleSpace X]
  [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  [IsProper (X ↘ Spec (CommRingCat.of k))]

omit [IsProper (X ↘ Spec (CommRingCat.of k))] in
/-- The rational map attached to `t` restricts to the `K(X)`-valued point attached to
`t` on the function field. -/
lemma fromFunctionField_ratMapOfFunctionField (t : X.functionField) :
    (ratMapOfFunctionField k X t).fromFunctionField = functionFieldPoint k X t :=
  RationalMap.fromFunctionField_ofFunctionField _ _ _ _

omit [IsProper (X ↘ Spec (CommRingCat.of k))] in
/-- The extension of the rational map attached to `t` sends the generic point of `X`
to the point of `ℙ¹` attached to `t`. -/
lemma homOfFunctionField_genericPoint
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (t : X.functionField) :
    homOfFunctionField k X hX t (genericPoint X) =
      P1.point (R := X.functionField) k t (IsLocalRing.closedPoint X.functionField) := by
  have h1 : X.fromSpecStalk (genericPoint X) ≫ homOfFunctionField k X hX t =
      functionFieldPoint k X t := by
    have h3 := congrArg RationalMap.fromFunctionField
      (toRationalMap_homOfFunctionField k X hX t)
    rw [Hom.toRationalMap, RationalMap.fromFunctionField_toRationalMap,
      fromFunctionField_ratMapOfFunctionField, PartialMap.fromFunctionField,
      PartialMap.fromSpecStalkOfMem_toPartialMap] at h3
    exact h3
  calc homOfFunctionField k X hX t (genericPoint X)
      = (X.fromSpecStalk (genericPoint X) ≫ homOfFunctionField k X hX t)
          (IsLocalRing.closedPoint _) := by
        rw [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
    _ = functionFieldPoint k X t (IsLocalRing.closedPoint _) := by rw [h1]
    _ = _ := rfl

/-- **B1, finiteness** (modulo the stalk hypotheses): for `X` integral and proper over
`k` with valuation-ring local rings of dimension `≤ 1`, and `t ∈ K(X)` transcendental
over `k`, the induced morphism `X ⟶ ℙ¹` is finite. -/
theorem isFinite_homOfFunctionField
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x))
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x))
    {t : X.functionField} (ht : Transcendental k t) :
    IsFinite (homOfFunctionField k X hX t) := by
  haveI : IsProper (homOfFunctionField k X hX t) := isProper_homOfFunctionField k X hX t
  haveI : IsNoetherian X := isNoetherian_of_over X (Spec (CommRingCat.of k))
  have hfib : ∀ y, ((homOfFunctionField k X hX t).base ⁻¹' {y}).Finite := by
    intro y
    refine finite_preimage_singleton_of_isClosedMap _ hdim
      (homOfFunctionField k X hX t).isClosedMap ?_ y
    rw [homOfFunctionField_genericPoint]
    exact P1.not_isClosed_singleton_point_of_transcendental k ht
  haveI : LocallyQuasiFinite (homOfFunctionField k X hX t) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ hfib
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end Belyi
