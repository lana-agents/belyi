/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Curve.Basic
import Belyi.Curve.Descent
import Belyi.Curve.GeometricIntegralDescent
import Belyi.Curve.SmoothRelDimDescent
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

The converse — **descent** of the curve predicate from `X/K` to a model `X₀/k₀` along the
faithfully flat map `Spec K ⟶ Spec k₀` — is the descent direction of B3c (taxis #167). It
is *assembled* here from `MorphismProperty.DescendsAlong` instances for the three curve
properties along `@Surjective ⊓ @Flat ⊓ @QuasiCompact`:

* `@IsProper` descends unconditionally
  (`AlgebraicGeometry.descendsAlong_isProper_surjective_inf_flat_inf_quasicompact`, taxis #167);
* `@GeometricallyIntegral` descends along the field extension by the direct `Geometrically`-API
  argument `Belyi.geometricallyIntegral_of_baseChange` (taxis #204) — no `DescendsAlong` instance
  is needed, because the cover here always has a *field* base;
* `@SmoothOfRelativeDimension 1` descends along the field extension by the direct field-specific
  argument `Belyi.smoothOfRelativeDimension_of_baseChange` (taxis #205) — again no `DescendsAlong`
  instance is needed, for the same reason (the general codescent of
  `Locally (IsStandardSmoothOfRelativeDimension n)` is a genuine mathlib gap, but the field base
  sidesteps it via a per-chart rank-of-Kähler-differentials computation).

Since all three legs descend directly, the descent assembly `IsCurveOver.of_pullback` /
`IsCurveOver.of_baseChangeModel` is now **unconditional** — it carries no `DescendsAlong` instance
hypotheses. This upgrades `IsCurveOver.of_isCurveOver_model` to an equivalence and discharges the
forward-direction gate of the main theorem (`Belyi/Main.lean`, taxis #55/#188).

## Main results

* `Belyi.isCurveOver_pullback`: the base change of a curve along `Spec K ⟶ Spec k₀` is a
  curve over `K`.
* `Belyi.IsCurveOver.of_isCurveOver_model`: if a `DefinableOver` witness has a model that
  is a curve over `k₀`, then `X` is a curve over `K`.
* `Belyi.IsCurveOver.of_pullback` / `Belyi.IsCurveOver.of_baseChangeModel` (descent direction,
  now unconditional): a scheme over `K` that is a curve and admits a `k₀`-model has a **curve**
  model over `k₀`.
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

section Descent

open MorphismProperty

/-! ### Descent direction of B3c (taxis #167)

The descent of the curve predicate along the field extension `k₀ ⊆ K` is assembled from the
descent of the three curve properties along the faithfully-flat cover
`specAlgebraMap k₀ K : Spec K ⟶ Spec k₀` (which is `@Surjective ⊓ @Flat ⊓ @QuasiCompact`).
`@IsProper` descends unconditionally via `MorphismProperty.of_pullback_snd_of_descendsAlong`;
`@GeometricallyIntegral` and `@SmoothOfRelativeDimension 1` descend by the field-specific
arguments `geometricallyIntegral_of_baseChange` (taxis #204) and
`smoothOfRelativeDimension_of_baseChange` (taxis #205), which exploit that the cover here has a
*field* base. So the assembly is unconditional (no `DescendsAlong` instance hypotheses).

The `MorphismProperty Scheme.{u}` annotation on the cover pins its universe to that of the
ambient schemes at the `@IsProper` descent call site. -/

/-- **B3c** (descent direction), assembly: if the base change of `X₀/k₀` along the field
extension `k₀ ⊆ K` is a curve over `K`, then `X₀` is already a curve over `k₀`.

`@IsProper` descends along the faithfully-flat cover `specAlgebraMap k₀ K` via
`MorphismProperty.of_pullback_snd_of_descendsAlong` (unconditionally, taxis #167). The
`@GeometricallyIntegral` and `@SmoothOfRelativeDimension 1` legs are discharged directly by the
field-specific arguments `geometricallyIntegral_of_baseChange` (taxis #204) and
`smoothOfRelativeDimension_of_baseChange` (taxis #205), which exploit that the cover here has a
field base — so no `DescendsAlong` instance is required for any leg and the theorem is
unconditional. -/
theorem IsCurveOver.of_pullback
    (X₀ : Scheme.{u}) [X₀.Over (Spec (CommRingCat.of k₀))]
    [IsCurveOver K (pullback (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K))] :
    IsCurveOver k₀ X₀ := by
  -- the structure morphism of the base change is `pullback.snd`, so `IsCurveOver K` of the
  -- base change supplies each curve property of `pullback.snd`
  have hsnd_smooth : SmoothOfRelativeDimension 1
      (pullback (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K) ↘
        Spec (CommRingCat.of K)) := inferInstance
  have hsnd_proper : IsProper
      (pullback (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K) ↘
        Spec (CommRingCat.of K)) := inferInstance
  have hsnd_gi : GeometricallyIntegral
      (pullback (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K) ↘
        Spec (CommRingCat.of K)) := inferInstance
  -- The `@SmoothOfRelativeDimension 1` leg descends directly via the field-base argument,
  -- avoiding the (research-grade) general `DescendsAlong (@SmoothOfRelativeDimension 1)` instance.
  have hs : SmoothOfRelativeDimension 1 (X₀ ↘ Spec (CommRingCat.of k₀)) :=
    smoothOfRelativeDimension_of_baseChange hsnd_smooth
  have hp : IsProper (X₀ ↘ Spec (CommRingCat.of k₀)) :=
    of_pullback_snd_of_descendsAlong
      (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}))
      (g := specAlgebraMap k₀ K) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsnd_proper
  -- The `@GeometricallyIntegral` leg descends directly via the field-base argument, avoiding
  -- the (research-grade) general `DescendsAlong (@GeometricallyIntegral)` instance.
  have hg : GeometricallyIntegral (X₀ ↘ Spec (CommRingCat.of k₀)) :=
    geometricallyIntegral_of_baseChange X₀ hsnd_gi
  exact ⟨⟩

/-- **B3c** (descent direction) for `DefinableOver`-shaped witnesses: if `X/K` is a curve and is
isomorphic over `Spec K` to the base change of `X₀/k₀`, then the model `X₀` is a curve over `k₀`.

This is the exact converse of `IsCurveOver.of_isCurveOver_model` and the shape a
`Belyi.DefinableOver` witness supplies (the model `X₀`, its structure morphism, and the
identification `e`). Unconditional, like `IsCurveOver.of_pullback`. -/
theorem IsCurveOver.of_baseChangeModel
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    [IsCurveOver K X] (X₀ : Scheme.{u}) [X₀.Over (Spec (CommRingCat.of k₀))]
    (e : X ≅ pullback (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K))
    (he : e.hom ≫ pullback.snd (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K) =
      X ↘ Spec (CommRingCat.of K)) :
    IsCurveOver k₀ X₀ := by
  haveI : IsCurveOver K (pullback (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)) :=
    IsCurveOver.of_iso e he
  exact IsCurveOver.of_pullback k₀ K X₀

end Descent

end Belyi
