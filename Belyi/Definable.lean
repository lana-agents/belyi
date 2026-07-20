/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Over

/-!
# Definability of a scheme over a subfield

This file begins statement **B3** of `references/proof-outline.md` (taxis issue #48):
for an extension `k₀ ⊆ K` (encoded as `[Algebra k₀ K]`), a scheme `X` over `Spec K` is
*definable over* `k₀` if it is isomorphic, as a scheme over `Spec K`, to the base change
of a scheme over `Spec k₀`.

Belyi's theorem is the statement that a curve over `ℂ` is definable over `ℚ̄` if and
only if it admits a Belyi map.

## Main definitions

* `Belyi.DefinableOver k₀ K X`: the existence of a model of `X` over `k₀`. The witness
  data (the model `X₀`, its structure morphism, and the identification) is packaged in
  an existential so that both directions of Belyi produce/consume explicit models.

## Main results

* `Belyi.DefinableOver.of_iso` (B3a): invariance under isomorphism over `Spec K`.

The pair version (models of morphisms to `ℙ¹`), transitivity in a tower `k₀ ⊆ k₁ ⊆ K`
(B3b) and the descent of curve properties to models (B3c/B3d) are follow-up work on the
same issue.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

variable (k₀ K : Type u) [CommRing k₀] [CommRing K] [Algebra k₀ K]

/-- The morphism `Spec K ⟶ Spec k₀` induced by the ring extension `k₀ ⊆ K`. -/
noncomputable def specAlgebraMap : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k₀) :=
  Spec.map (CommRingCat.ofHom (algebraMap k₀ K))

/-- A scheme `X` over `Spec K` is *definable over* `k₀` if there is a scheme `X₀` over
`Spec k₀` (a *model*) whose base change to `K` is isomorphic to `X` over `Spec K`. -/
def DefinableOver (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] : Prop :=
  ∃ (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Spec (CommRingCat.of k₀))
    (e : X ≅ pullback f₀ (specAlgebraMap k₀ K)),
    e.hom ≫ pullback.snd f₀ (specAlgebraMap k₀ K) = X ↘ Spec (CommRingCat.of K)

/-- In a tower `k₀ ⊆ k₁ ⊆ K`, the induced morphisms of spectra compose as expected. -/
lemma specAlgebraMap_comp (k₁ : Type u) [CommRing k₁] [Algebra k₀ k₁] [Algebra k₁ K]
    [IsScalarTower k₀ k₁ K] :
    specAlgebraMap k₁ K ≫ specAlgebraMap k₀ k₁ = specAlgebraMap k₀ K := by
  rw [specAlgebraMap, specAlgebraMap, specAlgebraMap, ← Spec.map_comp]
  congr 1
  rw [← CommRingCat.ofHom_comp]
  congr 1
  exact (IsScalarTower.algebraMap_eq k₀ k₁ K).symm

namespace DefinableOver

variable {k₀ K} {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [Y.Over (Spec (CommRingCat.of K))]

/-- **B3a**: definability over a subfield is invariant under isomorphism over `Spec K`. -/
lemma of_iso (φ : X ≅ Y) (hφ : φ.hom ≫ (Y ↘ Spec (CommRingCat.of K)) =
    X ↘ Spec (CommRingCat.of K)) (h : DefinableOver k₀ K X) : DefinableOver k₀ K Y := by
  obtain ⟨X₀, f₀, e, he⟩ := h
  refine ⟨X₀, f₀, φ.symm ≪≫ e, ?_⟩
  rw [Iso.trans_hom, Category.assoc, he, Iso.symm_hom, Iso.inv_comp_eq, hφ]

/-- **B3b**: a scheme definable over `k₀` is definable over any intermediate `k₁` in a
tower `k₀ ⊆ k₁ ⊆ K`, by base-changing the model. -/
lemma trans (k₁ : Type u) [CommRing k₁] [Algebra k₀ k₁] [Algebra k₁ K]
    [IsScalarTower k₀ k₁ K] (h : DefinableOver k₀ K X) : DefinableOver k₁ K X := by
  obtain ⟨X₀, f₀, e, he⟩ := h
  have h1 : (pullbackLeftPullbackSndIso f₀ (specAlgebraMap k₀ k₁) (specAlgebraMap k₁ K)).inv ≫
      pullback.snd (pullback.snd f₀ (specAlgebraMap k₀ k₁)) (specAlgebraMap k₁ K) =
      pullback.snd f₀ (specAlgebraMap k₁ K ≫ specAlgebraMap k₀ k₁) := by
    rw [Iso.inv_comp_eq, pullbackLeftPullbackSndIso_hom_snd]
  refine ⟨pullback f₀ (specAlgebraMap k₀ k₁), pullback.snd _ _,
    e ≪≫ pullback.congrHom rfl (specAlgebraMap_comp k₀ K k₁).symm ≪≫
      (pullbackLeftPullbackSndIso f₀ (specAlgebraMap k₀ k₁) (specAlgebraMap k₁ K)).symm, ?_⟩
  rw [Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc, Iso.symm_hom, h1, ← he]
  congr 1
  rw [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]

end DefinableOver

end Belyi
