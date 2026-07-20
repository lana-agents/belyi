/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Curve.Basic
import Belyi.Definable

/-!
# Base change of curves along a field extension

The base-change half of **B3c** (taxis issue #48): the curve predicate
`Belyi.IsCurveOver` is stable under base change along a field extension `k₀ ⊆ K`, so a
scheme with a curve model over `k₀` is itself a curve over `K`.

All three constituents of `IsCurveOver` are stable under base change in mathlib
(`SmoothOfRelativeDimension`, `IsProper`, `GeometricallyIntegral`), so the content here
is the packaging: transporting the predicate along the identification stored inside a
`Belyi.DefinableOver` witness.

The converse (descent of the curve predicate from `X/K` to a model `X₀/k₀` along the
faithfully flat map `Spec K ⟶ Spec k₀`) is separate, harder work on the same issue.

## Main results

* `Belyi.isCurveOver_pullback`: the base change of a curve along `Spec K ⟶ Spec k₀` is a
  curve over `K`.
* `Belyi.IsCurveOver.of_isCurveOver_model`: if a `DefinableOver` witness has a model that
  is a curve over `k₀`, then `X` is a curve over `K`.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

variable (k₀ K : Type u) [Field k₀] [Field K] [Algebra k₀ K]

section Pullback

variable (X₀ : Scheme.{u}) [X₀.Over (Spec (CommRingCat.of k₀))] [IsCurveOver k₀ X₀]

/-- The base change of `X₀/k₀` along `Spec K ⟶ Spec k₀`, as a scheme over `Spec K`. -/
noncomputable instance : (pullback (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)).Over
    (Spec (CommRingCat.of K)) :=
  ⟨pullback.snd _ _⟩

/-- **B3c** (base-change direction): the base change of a curve along a field extension
is a curve. -/
instance isCurveOver_pullback :
    IsCurveOver K (pullback (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)) := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have hs : SmoothOfRelativeDimension 1
      (pullback (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K) ↘
        Spec (CommRingCat.of K)) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  have hp : IsProper (pullback (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K) ↘
      Spec (CommRingCat.of K)) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  have hg : GeometricallyIntegral (pullback (X₀ ↘ Spec (CommRingCat.of k₀))
      (specAlgebraMap k₀ K) ↘ Spec (CommRingCat.of K)) :=
    MorphismProperty.pullback_snd (P := @GeometricallyIntegral) _ _ inferInstance
  exact ⟨⟩

end Pullback

section Transport

variable {k₀ K} {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [Y.Over (Spec (CommRingCat.of K))]

/-- The curve predicate transports along an isomorphism over the base. -/
lemma IsCurveOver.of_iso (φ : X ≅ Y)
    (hφ : φ.hom ≫ (Y ↘ Spec (CommRingCat.of K)) = X ↘ Spec (CommRingCat.of K))
    [IsCurveOver K X] : IsCurveOver K Y := by
  have he : (Y ↘ Spec (CommRingCat.of K)) =
      φ.inv ≫ (X ↘ Spec (CommRingCat.of K)) := by
    rw [← hφ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hs : SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of K)) := by
    rw [he]
    exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1)
      φ.inv _).mpr inferInstance
  have hp : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    rw [he]
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper φ.inv _).mpr inferInstance
  have hg : GeometricallyIntegral (Y ↘ Spec (CommRingCat.of K)) := by
    rw [he]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral
      φ.inv _).mpr inferInstance
  exact ⟨⟩

/-- **B3c** for `DefinableOver` witnesses: a scheme over `K` with a model that is a curve
over `k₀` is a curve over `K`. -/
lemma IsCurveOver.of_isCurveOver_model
    (h : ∃ (X₀ : Scheme.{u}) (_ : X₀.Over (Spec (CommRingCat.of k₀)))
      (_ : IsCurveOver k₀ X₀)
      (e : X ≅ pullback (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)),
      e.hom ≫ pullback.snd (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K) =
        X ↘ Spec (CommRingCat.of K)) :
    IsCurveOver K X := by
  obtain ⟨X₀, _, _, e, he⟩ := h
  have : IsCurveOver K (pullback (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)) :=
    isCurveOver_pullback k₀ K X₀
  exact IsCurveOver.of_iso e.symm (by rw [Iso.symm_hom, Iso.inv_comp_eq, ← he]; rfl)

end Transport

end Belyi
