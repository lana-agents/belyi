/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Converse.Normalization
import Pi1.Mathlib.AlgebraicGeometry.Normalization

/-!
# Dense open immersions into normal integral schemes have trivial normalization

For an integral scheme `X` with integrally closed stalks and a quasi-compact open immersion
`j : Y ⟶ X` with dense range, the relative normalization of `X` in `Y` is `X` itself:
`j.fromNormalization` is an isomorphism
(`AlgebraicGeometry.isIso_fromNormalization_of_isIntegrallyClosed`). This is the hypothesis
`IsIso U.ι.fromNormalization` of pi1's étale van Kampen theorem for the charts of a curve.
The same holds for a nonempty open subscheme `U` in place of `X`
(`AlgebraicGeometry.isIso_fromNormalization_of_isIntegrallyClosed_opens`), e.g. for the
inclusion `U ∩ U' ⟶ U'`.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A quasi-compact open immersion with dense range into an integral scheme with integrally
closed stalks has trivial relative normalization. -/
theorem isIso_fromNormalization_of_isIntegrallyClosed {X Y : Scheme.{u}} [IsIntegral X]
    (j : Y ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (hj : DenseRange j.base)
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) : IsIso j.fromNormalization := by
  have h := isIso_normalizationDesc_of_isIntegrallyClosed (𝟙 X) j hj hX
  have e := (Category.comp_id _).symm.trans ((j ≫ 𝟙 X).normalizationDesc_comp j (𝟙 X) rfl)
  have : IsIso (j ≫ 𝟙 X).fromNormalization := by
    rw [← e]
    infer_instance
  exact Scheme.Hom.isIso_fromNormalization_of_eq (Category.comp_id j)

/-- The stalks of an open subscheme are those of the ambient scheme. -/
lemma isIntegrallyClosed_stalk_opens {X : Scheme.{u}} (U : X.Opens)
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (x : U) :
    IsIntegrallyClosed (U.toScheme.presheaf.stalk x) :=
  haveI := hX x.1
  IsIntegrallyClosed.of_equiv (U.stalkIso x).commRingCatIsoToRingEquiv.symm

/-- The version of `isIso_fromNormalization_of_isIntegrallyClosed` with target a nonempty open
subscheme `U` of an integral scheme with integrally closed stalks. -/
theorem isIso_fromNormalization_of_isIntegrallyClosed_opens {X Y : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (j : Y ⟶ U) [IsOpenImmersion j] [QuasiCompact j]
    (hj : DenseRange j.base) (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIso j.fromNormalization :=
  haveI : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
  isIso_fromNormalization_of_isIntegrallyClosed j hj (isIntegrallyClosed_stalk_opens U hX)

end AlgebraicGeometry
