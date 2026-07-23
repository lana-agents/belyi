/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Curve.Basic
import Belyi.Curve.Descent
import Belyi.Curve.GeometricIntegralDescent
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
* `@GeometricallyIntegral` descends here by the field-extension-specific
  `Belyi.geometricallyIntegral_of_baseChange` (taxis #204, in
  `Belyi/Curve/GeometricIntegralDescent.lean`): the descent cover is always `specAlgebraMap k₀ K`
  (base a field), so the general `DescendsAlong @GeometricallyIntegral` instance — a genuine
  mathlib v4.32 gap — is **not** needed;
* `@SmoothOfRelativeDimension 1` is **not** yet known to descend in mathlib v4.32 (it needs a
  faithfully-flat codescent of `Locally (IsStandardSmoothOfRelativeDimension n)`, an unresolved
  ring-theoretic gap, taxis #205), and is the sole remaining instance hypothesis below.

The descent assembly `IsCurveOver.of_pullback` / `IsCurveOver.of_baseChangeModel` therefore
takes only the `@SmoothOfRelativeDimension 1` `DescendsAlong` instance as an instance hypothesis:
the moment it is supplied (here or upstream), the curve predicate descends with no further wiring,
upgrading `IsCurveOver.of_isCurveOver_model` to an equivalence and discharging the
forward-direction gate of the main theorem (`Belyi/Main.lean`, taxis #55/#188).

## Main results

* `Belyi.isCurveOver_pullback`: the base change of a curve along `Spec K ⟶ Spec k₀` is a
  curve over `K`.
* `Belyi.IsCurveOver.of_isCurveOver_model`: if a `DefinableOver` witness has a model that
  is a curve over `k₀`, then `X` is a curve over `K`.
* `Belyi.IsCurveOver.of_pullback` / `Belyi.IsCurveOver.of_baseChangeModel` (descent direction,
  gated on the single remaining `@SmoothOfRelativeDimension 1` `DescendsAlong` instance): a scheme
  over `K` that is a curve and admits a `k₀`-model has a **curve** model over `k₀`.
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

The descent of the curve predicate along the field extension `k₀ ⊆ K` is assembled from
`DescendsAlong` instances for the three curve properties along the faithfully-flat cover
`specAlgebraMap k₀ K : Spec K ⟶ Spec k₀` (which is `@Surjective ⊓ @Flat ⊓ @QuasiCompact`).
`@IsProper` descends unconditionally and `@GeometricallyIntegral` descends by
`geometricallyIntegral_of_baseChange` (the base is a field); only `@SmoothOfRelativeDimension 1`
is taken as an instance hypothesis (see the module docstring).

The `MorphismProperty Scheme.{u}` annotation on the cover pins its universe to that of the
ambient schemes, so the instance hypothesis matches the term produced at the descent call site. -/

/-- **B3c** (descent direction), assembly: if the base change of `X₀/k₀` along the field
extension `k₀ ⊆ K` is a curve over `K`, then `X₀` is already a curve over `k₀`.

`@IsProper` and `@SmoothOfRelativeDimension 1` descend along the faithfully-flat cover
`specAlgebraMap k₀ K` via `MorphismProperty.of_pullback_snd_of_descendsAlong`: `@IsProper`
descends unconditionally (taxis #167) and `@SmoothOfRelativeDimension 1` is supplied as an
instance hypothesis (the sole remaining mathlib gap, taxis #205). `@GeometricallyIntegral`
descends directly by `geometricallyIntegral_of_baseChange` (taxis #204) — the base of the
descent cover is always a field, so no general `DescendsAlong` instance is required. -/
theorem IsCurveOver.of_pullback
    [DescendsAlong (@SmoothOfRelativeDimension 1)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})]
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
  -- `@SmoothOfRelativeDimension 1` descends as an instance hypothesis (the one remaining
  -- research-grade gap, taxis #205); `@IsProper` descends unconditionally (PR #59); geometric
  -- integrality descends by the field-extension-specific `geometricallyIntegral_of_baseChange`
  -- (PR #61) — the base here is always a field, so no general `DescendsAlong` instance is needed.
  have hs : SmoothOfRelativeDimension 1 (X₀ ↘ Spec (CommRingCat.of k₀)) :=
    of_pullback_snd_of_descendsAlong
      (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}))
      (g := specAlgebraMap k₀ K) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsnd_smooth
  have hp : IsProper (X₀ ↘ Spec (CommRingCat.of k₀)) :=
    of_pullback_snd_of_descendsAlong
      (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}))
      (g := specAlgebraMap k₀ K) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsnd_proper
  have hg : GeometricallyIntegral (X₀ ↘ Spec (CommRingCat.of k₀)) :=
    geometricallyIntegral_of_baseChange X₀ hsnd_gi
  exact ⟨⟩

/-- **B3c** (descent direction) for `DefinableOver`-shaped witnesses: if `X/K` is a curve and is
isomorphic over `Spec K` to the base change of `X₀/k₀`, then the model `X₀` is a curve over `k₀`.

This is the exact converse of `IsCurveOver.of_isCurveOver_model` and the shape a
`Belyi.DefinableOver` witness supplies (the model `X₀`, its structure morphism, and the
identification `e`). Gated, like `IsCurveOver.of_pullback`, on the single remaining
`@SmoothOfRelativeDimension 1` `DescendsAlong` instance. -/
theorem IsCurveOver.of_baseChangeModel
    [DescendsAlong (@SmoothOfRelativeDimension 1)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})]
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
