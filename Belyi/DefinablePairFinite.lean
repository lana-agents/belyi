/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.DefinablePair
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finiteness transports from a pair model (base-change direction of B3d)

This file supplies the **base-change direction** of statement **B3d** of
`references/proof-outline.md` (taxis issue #48) for finiteness: if a model
`f₀ : X₀ ⟶ ℙ¹_{k₀}` of a morphism `f : X ⟶ ℙ¹_K` over an extension `k₀ ⊆ K` is finite, then
`f` itself is finite.

This is exactly the implication the **forward direction** (B8) consumes: it produces a finite
model `f₀` over `ℚ̄`, base-changes to `ℂ`, and needs the base change to stay finite. (The
converse — `f` finite ⇒ the model `f₀` is finite — is the harder *descent* direction, needed
by the converse of Belyi, and is left as separate follow-up work on #48.)

## Main results

* `Belyi.isPullback_baseChangeModelHom`: the base change `baseChangeModelHom` of a model
  morphism realizes `f₀` as a pullback (the square with the two first projections and `f₀` on
  both sides is cartesian).
* `Belyi.isFinite_baseChangeModelHom`: hence `IsFinite f₀ ⟹ IsFinite (baseChangeModelHom …)`
  (finiteness is stable under base change).
* `Belyi.isFinite_of_isFinite_model`: the packaged statement against the identification data of
  `Belyi.DefinableOverPair` — `IsFinite f₀ ⟹ IsFinite f`, transporting finiteness through the
  source identification `e` and the canonical identification `Belyi.P1.toPullback` (an
  isomorphism by `Belyi.P1.isIso_toPullback`).
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

variable (k₀ K : Type u) [CommRing k₀] [CommRing K] [Algebra k₀ K]

section

variable {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ Spec (CommRingCat.of k₀)) (f₀ : X₀ ⟶ P1 k₀)
  (hf₀ : f₀ ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)) = p₀)

/-- The base change `baseChangeModelHom` of a model morphism `f₀` realizes `f₀` as a pullback:
the square
```
  pullback p₀ (specAlgebraMap …) --fst--> X₀
        │                                  │
   baseChangeModelHom                      f₀
        ↓                                  ↓
  pullback (ℙ¹_{k₀} ↘ Spec k₀) (…) --fst--> ℙ¹_{k₀}
```
is cartesian. Obtained by pasting the two standard pullback squares (of `p₀` resp.
`ℙ¹_{k₀} ↘ Spec k₀` along `specAlgebraMap k₀ K`) vertically via `IsPullback.of_bot`, using
`baseChangeModelHom_snd`/`_fst` and `hf₀`. -/
lemma isPullback_baseChangeModelHom :
    IsPullback (pullback.fst p₀ (specAlgebraMap k₀ K))
      (baseChangeModelHom k₀ K p₀ f₀ hf₀) f₀
      (pullback.fst (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)) := by
  have t := IsPullback.of_hasPullback (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)
  have s : IsPullback (pullback.fst p₀ (specAlgebraMap k₀ K))
      (baseChangeModelHom k₀ K p₀ f₀ hf₀ ≫
        pullback.snd (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K))
      (f₀ ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀))) (specAlgebraMap k₀ K) := by
    rw [baseChangeModelHom_snd, hf₀]
    exact IsPullback.of_hasPullback p₀ (specAlgebraMap k₀ K)
  exact s.of_bot (baseChangeModelHom_fst k₀ K p₀ f₀ hf₀).symm t

/-- **Base-change direction of B3d (finiteness), core form.** The base change of a finite model
morphism is finite. -/
lemma isFinite_baseChangeModelHom (hfin : IsFinite f₀) :
    IsFinite (baseChangeModelHom k₀ K p₀ f₀ hf₀) :=
  MorphismProperty.of_isPullback (P := @IsFinite)
    (isPullback_baseChangeModelHom k₀ K p₀ f₀ hf₀) hfin

end

/-- **Base-change direction of B3d (finiteness), packaged form.** Against the identification data
of `Belyi.DefinableOverPair` — a model `f₀ : X₀ ⟶ ℙ¹_{k₀}`, an identification `e` of `X` with the
base change of the model source, and the pair condition
`f ≫ toPullback = e.hom ≫ baseChangeModelHom …` — finiteness of `f₀` implies finiteness of `f`.

`f` is `e.hom ≫ baseChangeModelHom … ≫ inv toPullback`, a composite of two isomorphisms with the
(finite) base change of `f₀`; finiteness is stable under composition and contains isomorphisms. -/
lemma isFinite_of_isFinite_model {X₀ : Scheme.{u}} {p₀ : X₀ ⟶ Spec (CommRingCat.of k₀)}
    {f₀ : X₀ ⟶ P1 k₀} (hf₀ : f₀ ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)) = p₀)
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {f : X ⟶ P1 K}
    (e : X ≅ pullback p₀ (specAlgebraMap k₀ K))
    (hfe : f ≫ P1.toPullback k₀ K = e.hom ≫ baseChangeModelHom k₀ K p₀ f₀ hf₀)
    (hfin : IsFinite f₀) : IsFinite f := by
  haveI hbc : IsFinite (baseChangeModelHom k₀ K p₀ f₀ hf₀) :=
    isFinite_baseChangeModelHom k₀ K p₀ f₀ hf₀ hfin
  have hfeq : f = (e.hom ≫ baseChangeModelHom k₀ K p₀ f₀ hf₀) ≫ inv (P1.toPullback k₀ K) := by
    rw [← hfe, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hfeq]
  infer_instance

end Belyi
