/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.DefinablePairFinite
import Belyi.QuasiFiniteDescent

/-!
# Finiteness descends to a pair model (descent direction of B3d)

This file supplies the **descent direction** of statement **B3d** of `references/proof-outline.md`
(taxis issue #48) for finiteness — the converse of the base-change direction in
`Belyi/DefinablePairFinite.lean`: if a morphism `f : X ⟶ ℙ¹_K` over a field extension `k₀ ⊆ K` is
finite and `f₀ : X₀ ⟶ ℙ¹_{k₀}` is a *proper* model of `f`, then `f₀` itself is finite.

This is exactly the implication the **converse direction** of Belyi's theorem needs: it recognises
a Belyi map `f` over `ℂ` as the base change of a `ℚ̄`-model `f₀` and must know that `f₀` is again a
(finite) Belyi map. Properness of the model comes for free from the curve-descent B3c
(`Belyi.IsCurveOver.of_pullback`, taxis #167): a model `X₀` of a curve is a curve, hence proper
over `k₀`, and `f₀` is proper because `ℙ¹_{k₀}` is separated over `k₀`.

When this residual was first scoped (July 2026) the required faithfully-flat descent of finiteness
was absent from mathlib; it has since become assemblable — `RingHom.Finite`/`FiniteType` codescent
landed, and quasi-finiteness descent is supplied in `Belyi/QuasiFiniteDescent.lean`. `IsFinite` of
the model then follows from `IsProper ⊓ LocallyQuasiFinite` via Zariski's main theorem.

## Main results

* `Belyi.isFinite_of_isFinite_baseChangeModelHom`: core form — if the base change
  `baseChangeModelHom` of a *proper* model `f₀` is finite, then `f₀` is finite.
* `Belyi.isFinite_model_of_isFinite`: packaged form against the identification data of
  `Belyi.DefinableOverPair` — `IsFinite f ⟹ IsFinite f₀` for a proper model `f₀`.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

variable (k₀ K : Type u) [Field k₀] [Field K] [Algebra k₀ K]

section

variable {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ Spec (CommRingCat.of k₀)) (f₀ : X₀ ⟶ P1 k₀)
  (hf₀ : f₀ ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)) = p₀)

/-- **Descent direction of B3d (finiteness), core form.** If the base change `baseChangeModelHom`
of a model morphism `f₀` is finite and `f₀` is proper, then `f₀` is finite.

`baseChangeModelHom` is the base change of `f₀` along the faithfully-flat cover
`pullback.fst (ℙ¹_{k₀} ↘ Spec k₀) (specAlgebraMap k₀ K)` (itself a base change of the field
extension `specAlgebraMap k₀ K`, hence `@Surjective ⊓ @Flat ⊓ @QuasiCompact`); finiteness descends
by `AlgebraicGeometry.isFinite_of_isPullback_of_faithfullyFlat` applied to the (flipped) cartesian
square `Belyi.isPullback_baseChangeModelHom`. -/
lemma isFinite_of_isFinite_baseChangeModelHom [IsProper f₀]
    (hbc : IsFinite (baseChangeModelHom k₀ K p₀ f₀ hf₀)) : IsFinite f₀ := by
  haveI := hbc
  exact isFinite_of_isPullback_of_faithfullyFlat
    (isPullback_baseChangeModelHom k₀ K p₀ f₀ hf₀).flip

end

/-- **Descent direction of B3d (finiteness), packaged form.** Against the identification data of
`Belyi.DefinableOverPair` — a *proper* model `f₀ : X₀ ⟶ ℙ¹_{k₀}`, an identification `e` of `X` with
the base change of the model source, and the pair condition
`f ≫ toPullback = e.hom ≫ baseChangeModelHom …` — finiteness of `f` implies finiteness of `f₀`.

`baseChangeModelHom` is `inv e.hom ≫ f ≫ toPullback`, a composite of two isomorphisms with the
finite `f`, hence finite; then `isFinite_of_isFinite_baseChangeModelHom` descends finiteness to the
model. -/
lemma isFinite_model_of_isFinite {X₀ : Scheme.{u}} {p₀ : X₀ ⟶ Spec (CommRingCat.of k₀)}
    {f₀ : X₀ ⟶ P1 k₀} (hf₀ : f₀ ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)) = p₀) [IsProper f₀]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {f : X ⟶ P1 K}
    (e : X ≅ pullback p₀ (specAlgebraMap k₀ K))
    (hfe : f ≫ P1.toPullback k₀ K = e.hom ≫ baseChangeModelHom k₀ K p₀ f₀ hf₀)
    (hfin : IsFinite f) : IsFinite f₀ := by
  haveI := hfin
  haveI hbc : IsFinite (baseChangeModelHom k₀ K p₀ f₀ hf₀) := by
    have hbceq : baseChangeModelHom k₀ K p₀ f₀ hf₀ = inv e.hom ≫ f ≫ P1.toPullback k₀ K := by
      rw [hfe, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
    rw [hbceq]; infer_instance
  exact isFinite_of_isFinite_baseChangeModelHom k₀ K p₀ f₀ hf₀ hbc

end Belyi
