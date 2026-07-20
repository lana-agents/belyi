/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.DefinablePair

/-!
# Transitivity of pair definability in a tower (B3b, pair version)

This file proves the **pair version of B3b** of `references/proof-outline.md` (taxis issue
#48): in a tower of fields `k₀ ⊆ k₁ ⊆ K`, a morphism `f : X ⟶ ℙ¹_K` definable over `k₀`
is definable over the intermediate field `k₁`, by base-changing the model from `k₀` to
`k₁`. This mirrors the scheme version `Belyi.DefinableOver.trans` (in `Belyi/Definable.lean`).

The key new ingredient over the scheme version is the compatibility of the comparison
morphism `Belyi.P1.mapOfAlgebra` (and hence `Belyi.P1.toPullback`) with the tower: since
`mapOfAlgebra` is a `Proj.map` of the coefficient map, its tower factorisation follows from
the functoriality `AlgebraicGeometry.Proj.map_comp` together with the composition of the
graded coefficient maps.

## Main results

* `Belyi.P1.gradedMapOfAlgebra_comp`: the coefficient map `k₀[X₀,X₁] → K[X₀,X₁]` factors as
  `k₀[X₀,X₁] → k₁[X₀,X₁] → K[X₀,X₁]` (as graded ring homomorphisms).
* `Belyi.P1.mapOfAlgebra_comp`: `mapOfAlgebra k₀ K = mapOfAlgebra k₁ K ≫ mapOfAlgebra k₀ k₁`.
* `Belyi.DefinableOverPair.trans` (**B3b**, pair version): a pair-definable morphism over
  `k₀` is pair-definable over any intermediate `k₁`.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

namespace P1

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k₀ k₁ K : Type u) [CommRing k₀] [CommRing k₁] [CommRing K]
  [Algebra k₀ k₁] [Algebra k₁ K] [Algebra k₀ K] [IsScalarTower k₀ k₁ K]

/-- The coefficient map `k₀[X₀,X₁] → K[X₀,X₁]` factors through `k₁[X₀,X₁]` in a tower
`k₀ ⊆ k₁ ⊆ K`, as graded ring homomorphisms. -/
lemma gradedMapOfAlgebra_comp :
    gradedMapOfAlgebra k₀ K = (gradedMapOfAlgebra k₁ K).comp (gradedMapOfAlgebra k₀ k₁) := by
  refine GradedRingHom.ext fun p => ?_
  simp only [GradedRingHom.comp_apply, gradedMapOfAlgebra_apply]
  rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]

/-- **Tower compatibility of the base-change comparison for `ℙ¹`.** In a tower
`k₀ ⊆ k₁ ⊆ K`, the comparison morphism `mapOfAlgebra k₀ K : ℙ¹_K ⟶ ℙ¹_{k₀}` factors through
`ℙ¹_{k₁}`. This is `AlgebraicGeometry.Proj.map_comp` applied to the coefficient maps. -/
lemma mapOfAlgebra_comp :
    mapOfAlgebra k₀ K = mapOfAlgebra k₁ K ≫ mapOfAlgebra k₀ k₁ := by
  -- prove the identity at the `Proj` level (avoiding the `P1 = Proj (P1Grading)` def wall),
  -- then bridge to the `P1`-level goal by `exact` (default transparency unfolds `P1`)
  have h : AlgebraicGeometry.Proj.map (gradedMapOfAlgebra k₀ K)
        (irrelevant_le_map_gradedMapOfAlgebra k₀ K) =
      AlgebraicGeometry.Proj.map (gradedMapOfAlgebra k₁ K)
          (irrelevant_le_map_gradedMapOfAlgebra k₁ K) ≫
        AlgebraicGeometry.Proj.map (gradedMapOfAlgebra k₀ k₁)
          (irrelevant_le_map_gradedMapOfAlgebra k₀ k₁) := by
    rw [← AlgebraicGeometry.Proj.map_comp]
    congr 1
    exact gradedMapOfAlgebra_comp k₀ k₁ K
  exact h

end P1

namespace DefinableOverPair

variable {k₀ K : Type u} [CommRing k₀] [CommRing K] [Algebra k₀ K]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

/-- **B3b** (pair version): a morphism `f : X ⟶ ℙ¹_K` definable over `k₀` is definable over
any intermediate field `k₁` in a tower `k₀ ⊆ k₁ ⊆ K`, by base-changing the model. -/
lemma trans (k₁ : Type u) [CommRing k₁] [Algebra k₀ k₁] [Algebra k₁ K]
    [IsScalarTower k₀ k₁ K] {f : X ⟶ P1 K} (h : DefinableOverPair k₀ K X f) :
    DefinableOverPair k₁ K X f := by
  obtain ⟨X₀, p₀, f₀, hf₀, e, hsnd, hf⟩ := h
  -- first projection of the original pair condition `hf`
  have hffst := hf =≫ pullback.fst (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)
  rw [Category.assoc, P1.toPullback_fst, Category.assoc, baseChangeModelHom_fst] at hffst
  -- `f` is a morphism over `Spec K` (forced by the definability condition)
  have hcs : f ≫ (P1 K ↘ Spec (CommRingCat.of K)) = X ↘ Spec (CommRingCat.of K) := by
    have := hf =≫ pullback.snd (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)
    rwa [Category.assoc, P1.toPullback_snd, Category.assoc, baseChangeModelHom_snd, hsnd] at this
  -- the base-changed model morphism over `k₁`
  set f₁ : pullback p₀ (specAlgebraMap k₀ k₁) ⟶ P1 k₁ :=
    baseChangeModelHom k₀ k₁ p₀ f₀ hf₀ ≫ inv (P1.toPullback k₀ k₁) with hf₁def
  have hf₁ : f₁ ≫ (P1 k₁ ↘ Spec (CommRingCat.of k₁)) =
      pullback.snd p₀ (specAlgebraMap k₀ k₁) := by
    rw [hf₁def, Category.assoc, ← P1.toPullback_snd k₀ k₁, IsIso.inv_hom_id_assoc,
      baseChangeModelHom_snd]
  -- the identification of `X` with the base change of the `k₁`-model
  set e₁ : X ≅ pullback (pullback.snd p₀ (specAlgebraMap k₀ k₁)) (specAlgebraMap k₁ K) :=
    e ≪≫ pullback.congrHom rfl (specAlgebraMap_comp k₀ K k₁).symm ≪≫
      (pullbackLeftPullbackSndIso p₀ (specAlgebraMap k₀ k₁) (specAlgebraMap k₁ K)).symm
    with he₁def
  -- structure-morphism compatibility of the identification (as in `DefinableOver.trans`)
  have h1 : (pullbackLeftPullbackSndIso p₀ (specAlgebraMap k₀ k₁) (specAlgebraMap k₁ K)).inv ≫
      pullback.snd (pullback.snd p₀ (specAlgebraMap k₀ k₁)) (specAlgebraMap k₁ K) =
      pullback.snd p₀ (specAlgebraMap k₁ K ≫ specAlgebraMap k₀ k₁) := by
    rw [Iso.inv_comp_eq, pullbackLeftPullbackSndIso_hom_snd]
  have hsnd₁ : e₁.hom ≫
      pullback.snd (pullback.snd p₀ (specAlgebraMap k₀ k₁)) (specAlgebraMap k₁ K) =
      X ↘ Spec (CommRingCat.of K) := by
    rw [he₁def, Iso.trans_hom, Iso.trans_hom, Category.assoc, Category.assoc, Iso.symm_hom, h1,
      ← hsnd]
    congr 1
    rw [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
  refine ⟨pullback p₀ (specAlgebraMap k₀ k₁), pullback.snd _ _, f₁, hf₁, e₁, hsnd₁, ?_⟩
  -- the pair condition over `k₁`
  apply pullback.hom_ext
  · -- first projection: land in `ℙ¹_{k₁}`, then reduce through the iso `toPullback k₀ k₁`
    simp only [Category.assoc, P1.toPullback_fst, baseChangeModelHom_fst]
    rw [← cancel_mono (P1.toPullback k₀ k₁), hf₁def]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · -- project to `ℙ¹_{k₀}`
      simp only [Category.assoc, P1.toPullback_fst, baseChangeModelHom_fst]
      rw [← P1.mapOfAlgebra_comp, hffst, he₁def]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
        pullbackLeftPullbackSndIso_inv_fst_assoc, pullback.congrHom_hom, pullback.map,
        pullback.lift_fst_assoc, Category.comp_id]
    · -- project to `Spec k₁`
      simp only [Category.assoc, P1.toPullback_snd, baseChangeModelHom_snd]
      rw [P1.mapOfAlgebra_comp_structMap, ← Category.assoc f, hcs, pullback.condition,
        ← Category.assoc e₁.hom, hsnd₁]
  · -- second projection: both sides equal `X ↘ Spec K`
    simp only [Category.assoc, P1.toPullback_snd, baseChangeModelHom_snd]
    rw [hcs, hsnd₁]

end DefinableOverPair

end Belyi
