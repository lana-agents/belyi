/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Converse.Normalization
import Belyi.Converse.NormalizationBaseChange
import Belyi.Converse.PuncturedLineBelyi
import Belyi.P1.PointsBaseChange

/-!
# Curves with a Belyi map are definable over `k`, assuming finite étale descent

This file is package (P2c) of the converse of Belyi's theorem
(`references/converse-rie-design.md`). Assuming the core descent statement (★)
`Belyi.Converse.FEtDescent k K` (finite étale algebras over `K ⊗[k] R` descend to `R`), we show
that a curve `X` over `K` admitting a Belyi map `f : X ⟶ ℙ¹_K` is definable over `k`:
```
X ≅ norm(Y ⟶ ℙ¹_K) ≅ norm(Y₀ ×_k K ⟶ ℙ¹_k ×_k K) ≅ norm(Y₀ ⟶ ℙ¹_k) ×_k K,
```
where `Y = f⁻¹(ℙ¹_K ∖ {0, 1, ∞}) = Spec B` and `Y₀ = Spec B₀` with `K ⊗[k] B₀ ≅ B` given by (★).

## The structure morphism

`IsBelyiMap K f` does not ask `f` to be a morphism over `Spec K`. Since `X` is proper and
integral over the algebraically closed field `K`, `Γ(X, ⊤) = K`, so the composite
`X ⟶ ℙ¹_K ⟶ Spec K` differs from the structure morphism by `Spec σ` for a field automorphism
`σ` of `K` (`Belyi.Converse.exists_iso_comp_eq`). Post-composing `f` with the automorphism
`P1.mapOfAlgebra` of `ℙ¹_K` attached to `σ⁻¹`, which fixes the three marked points, gives a
Belyi map over `Spec K` (`Belyi.Converse.exists_isBelyiMap_comp_eq`).

## Main definitions

* `Belyi.Converse.FEtDescent k K`: the descent statement (★), as a hypothesis.
* `Belyi.Converse.normalizationIsoOfArrowIso`: relative normalization is invariant under
  isomorphisms of arrows.

## Main results

* `Belyi.Converse.exists_isBelyiMap_comp_eq`: a curve with a Belyi map has a Belyi map over
  `Spec K`.
* `Belyi.Converse.definableOver_of_isBelyiMap_of_comp_eq`: the assembly for a Belyi map over
  `Spec K`.
* `Belyi.Converse.definableOver_of_isBelyiMap_of_fEtDescent`: (★) implies that a curve with a
  Belyi map is definable over `k`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace Belyi.Converse

/-- **Finite étale descent along `k ⊆ K`** (the core theorem (★) of
`references/converse-rie-design.md`): every finite étale `K ⊗[k] R`-algebra `B`, for `R` a
finitely generated `k`-algebra, is the base change `K ⊗[k] B₀` of a finite étale `R`-algebra
`B₀`, compatibly with the structure maps from `K` and from `R`. -/
def FEtDescent (k K : Type u) [Field k] [Field K] [Algebra k K] : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    (B : Type u) [CommRing B] [Algebra (K ⊗[k] R) B] [Algebra.Etale (K ⊗[k] R) B]
    [Module.Finite (K ⊗[k] R) B],
    ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra R B₀) (_ : Algebra k B₀)
      (_ : IsScalarTower k R B₀) (_ : Algebra.Etale R B₀) (_ : Module.Finite R B₀)
      (e : K ⊗[k] B₀ ≃+* B),
      (∀ x : K, e (x ⊗ₜ 1) = algebraMap (K ⊗[k] R) B (x ⊗ₜ 1)) ∧
      (∀ r : R, e (1 ⊗ₜ algebraMap R B₀ r) = algebraMap (K ⊗[k] R) B (1 ⊗ₜ r))

/-! ### Normalization is invariant under isomorphisms of arrows -/

section NormalizationIso

variable {Y Y' S S' : Scheme.{u}} {f : Y ⟶ S} {f' : Y' ⟶ S'} [QuasiCompact f]
  [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f'] (a : Y ≅ Y') (b : S ≅ S')
  (w : a.hom ≫ f' = f ≫ b.hom)

omit [QuasiCompact f'] [QuasiSeparated f'] in
@[reassoc]
private lemma normalizationDesc_comp_of_isIso {T : Scheme.{u}} (f₁ : Y ⟶ T) (h : T ⟶ S')
    (c : S' ⟶ S) [IsIso c] [IsIntegralHom (h ≫ c)] (H : f = f₁ ≫ h ≫ c) :
    f.normalizationDesc f₁ (h ≫ c) H ≫ h = f.fromNormalization ≫ inv c := by
  rw [IsIso.eq_comp_inv, Category.assoc]
  exact f.normalizationDesc_comp _ _ H

/-- An isomorphism of arrows `f ≅ f'` induces an isomorphism of relative normalizations. -/
noncomputable def normalizationIsoOfArrowIso : f.normalization ≅ f'.normalization where
  hom := f.normalizationDesc (a.hom ≫ f'.toNormalization) (f'.fromNormalization ≫ b.inv) (by
    rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization_assoc, reassoc_of% w,
      Iso.hom_inv_id, Category.comp_id])
  inv := f'.normalizationDesc (a.inv ≫ f.toNormalization) (f.fromNormalization ≫ b.hom) (by
    rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization_assoc, ← w,
      Iso.inv_hom_id_assoc])
  hom_inv_id := by
    refine Scheme.Hom.normalization.hom_ext _ _ _ f.fromNormalization ?_ ?_ ?_
    · simp
    · simp [normalizationDesc_comp_of_isIso]
    · simp
  inv_hom_id := by
    refine Scheme.Hom.normalization.hom_ext _ _ _ f'.fromNormalization ?_ ?_ ?_
    · simp
    · simp [normalizationDesc_comp_of_isIso]
    · simp

@[reassoc (attr := simp)]
lemma normalizationIsoOfArrowIso_hom_fromNormalization :
    (normalizationIsoOfArrowIso a b w).hom ≫ f'.fromNormalization =
      f.fromNormalization ≫ b.hom := by
  simp [normalizationIsoOfArrowIso, normalizationDesc_comp_of_isIso]

end NormalizationIso

/-! ### Replacing a Belyi map by one over `Spec K` -/

/-- Two morphisms from an integral scheme `X` to `Spec K`, both universally closed and locally
of finite type, over an algebraically closed field `K`, differ by `Spec σ` for a ring
automorphism `σ` of `K`: both induce isomorphisms `K ≅ Γ(X, ⊤)`. -/
theorem exists_iso_comp_eq (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u})
    [IsIntegral X] (s s' : X ⟶ Spec (CommRingCat.of K)) [UniversallyClosed s]
    [LocallyOfFiniteType s] [UniversallyClosed s'] [LocallyOfFiniteType s'] :
    ∃ σ : CommRingCat.of K ≅ CommRingCat.of K, s' = s ≫ Spec.map σ.hom := by
  have key : ∀ (t : X ⟶ Spec (CommRingCat.of K)) [UniversallyClosed t] [LocallyOfFiniteType t],
      IsIso ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ t.appTop) ∧
      t = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ t.appTop) := by
    intro t _ _
    refine ⟨?_, ?_⟩
    · rw [ConcreteCategory.isIso_iff_bijective]
      apply IsAlgClosed.ringHom_bijective_of_isIntegral
      have hfin := finite_appTop_of_universallyClosed K t
      have hiso : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom.Finite :=
        RingHom.Finite.of_surjective _
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
      exact (hfin.comp hiso).to_isIntegral
    · rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  obtain ⟨hF, hs⟩ := key s
  obtain ⟨hF', hs'⟩ := key s'
  refine ⟨asIso ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ s'.appTop) ≪≫
    (asIso ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ s.appTop)).symm, ?_⟩
  refine hs'.trans ?_
  conv_rhs => enter [1]; rw [hs]
  rw [Category.assoc, ← Spec.map_comp, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The base-change morphism `ℙ¹_K ⟶ ℙ¹_L` along a bijective `L → K` is an isomorphism. -/
theorem isIso_mapOfAlgebra_of_bijective (L K : Type u) [Field L] [Field K] [Algebra L K]
    (h : Function.Bijective (algebraMap L K)) : IsIso (P1.mapOfAlgebra L K) := by
  haveI : IsIso (CommRingCat.ofHom (algebraMap L K)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h
  haveI : IsIso (specAlgebraMap L K) := by rw [specAlgebraMap]; infer_instance
  exact (P1.isPullback_mapOfAlgebra L K).isIso_fst_of_isIso

/-- The base-change morphism `ℙ¹_K ⟶ ℙ¹_L` maps marked points to marked points. -/
theorem mapOfAlgebra_image_markedPoints_subset (L K : Type u) [Field L] [Field K]
    [Algebra L K] : (P1.mapOfAlgebra L K) '' markedPoints K ⊆ markedPoints L := by
  rintro _ ⟨y, hy, rfl⟩
  rcases hy with rfl | rfl | rfl
  · simp [P1.mapOfAlgebra_base_zero]
  · simp [P1.mapOfAlgebra_base_one]
  · simp [P1.mapOfAlgebra_base_infty]

/-- **A curve with a Belyi map has a Belyi map over `Spec K`.** The composite of a Belyi map
`f` with the structure morphism of `ℙ¹_K` differs from the structure morphism of `X` by
`Spec σ` for an automorphism `σ` of `K` (`exists_iso_comp_eq`); composing `f` with the
automorphism of `ℙ¹_K` induced by `σ⁻¹` (which fixes the marked points) corrects this. -/
theorem exists_isBelyiMap_comp_eq (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X] (f : X ⟶ P1 K)
    (hf : IsBelyiMap K f) :
    ∃ f' : X ⟶ P1 K, IsBelyiMap K f' ∧
      f' ≫ (P1 K ↘ Spec (CommRingCat.of K)) = X ↘ Spec (CommRingCat.of K) := by
  haveI := IsCurveOver.isIntegral K X
  haveI := hf.isFinite
  haveI := hf.locallyOfFinitePresentation
  obtain ⟨σ, hσ⟩ := exists_iso_comp_eq K X (X ↘ Spec (CommRingCat.of K))
    (f ≫ (P1 K ↘ Spec (CommRingCat.of K)))
  letI alg : Algebra K K := σ.inv.hom.toAlgebra
  let g : P1 K ⟶ P1 K := @P1.mapOfAlgebra K K _ _ alg
  haveI : IsIso g := @isIso_mapOfAlgebra_of_bijective K K _ _ alg
    (ConcreteCategory.bijective_of_isIso σ.inv)
  have hg : g ≫ (P1 K ↘ Spec (CommRingCat.of K)) =
      (P1 K ↘ Spec (CommRingCat.of K)) ≫ Spec.map σ.inv :=
    (@P1.mapOfAlgebra_comp_structMap K K _ _ alg).trans (by
      rw [specAlgebraMap]
      rfl)
  refine ⟨f ≫ g, IsBelyiMap.comp g ?_ (by simp), ?_⟩
  · refine subset_trans (Set.image_mono hf.branch_subset) ?_
    exact @mapOfAlgebra_image_markedPoints_subset K K _ _ alg
  · rw [Category.assoc, hg, reassoc_of% hσ, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]

/-! ### The assembly -/

/-- **(P2c) for a Belyi map over `Spec K`.** -/
theorem definableOver_of_isBelyiMap_of_comp_eq (k K : Type u) [Field k] [CharZero k]
    [Field K] [CharZero K] [IsAlgClosed K] [Algebra k K] (hD : FEtDescent k K)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X] (f : X ⟶ P1 K)
    (hf : IsBelyiMap K f)
    (hfK : f ≫ (P1 K ↘ Spec (CommRingCat.of K)) = X ↘ Spec (CommRingCat.of K)) :
    DefinableOver k K X := by
  haveI := hf.isFinite
  haveI := isAffine_puncturedCover hf
  haveI := puncturedCoverRing_finite hf
  haveI := puncturedCoverRing_etale hf
  -- Step 1: descend `B = Γ(Y, ⊤)` to `B₀` over `R_k`.
  letI : Algebra (K ⊗[k] puncturedRing k) (puncturedCoverRing f) :=
    ((algebraMap (puncturedRing K) (puncturedCoverRing f)).comp
      (puncturedRingBaseChange k K).toRingHom).toAlgebra
  haveI : Algebra.Etale (K ⊗[k] puncturedRing k) (puncturedCoverRing f) := by
    rw [← RingHom.etale_algebraMap]
    exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (puncturedRingBaseChange k K).bijective)
      (RingHom.etale_algebraMap.mpr inferInstance)
  haveI : Module.Finite (K ⊗[k] puncturedRing k) (puncturedCoverRing f) := by
    rw [← RingHom.finite_algebraMap]
    exact RingHom.Finite.comp (RingHom.finite_algebraMap.mpr inferInstance)
      (RingHom.Finite.of_surjective _ (puncturedRingBaseChange k K).surjective)
  obtain ⟨B₀, _, _, _, _, _, _, e, he₁, he₂⟩ := hD (puncturedRing k) (puncturedCoverRing f)
  letI : Algebra K (puncturedCoverRing f) :=
    ((algebraMap (puncturedRing K) (puncturedCoverRing f)).comp
      (algebraMap K (puncturedRing K))).toAlgebra
  haveI : IsScalarTower K (puncturedRing K) (puncturedCoverRing f) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e' : K ⊗[k] B₀ ≃ₐ[K] puncturedCoverRing f := AlgEquiv.ofRingEquiv (f := e) fun x => by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, he₁]
    change algebraMap (puncturedRing K) (puncturedCoverRing f)
      (puncturedRingBaseChange k K (x ⊗ₜ 1)) = _
    rw [puncturedRingBaseChange_tmul, map_one, mul_one]
    rfl
  have he : ∀ r : puncturedRing k, e' (1 ⊗ₜ algebraMap (puncturedRing k) B₀ r) =
      algebraMap (puncturedRing K) (puncturedCoverRing f) (puncturedRingMap k K r) := fun r => by
    change e _ = _
    rw [he₂]
    change algebraMap (puncturedRing K) (puncturedCoverRing f)
      (puncturedRingBaseChange k K (1 ⊗ₜ r)) = _
    rw [puncturedRingBaseChange_tmul, map_one, one_mul]
  have hP1 :=
    isPullback_puncturedRing_baseChange_P1 _ (isPushout_puncturedRing_of_tensorEquiv e' he)
  -- Step 2: `Y ⟶ ℙ¹_K` is the base change of `y₀ : Spec B₀ ⟶ ℙ¹_k`.
  set y₀ : Spec (CommRingCat.of B₀) ⟶ P1 k :=
    Spec.map (CommRingCat.ofHom (algebraMap (puncturedRing k) B₀)) ≫ puncturedι k
  set g := pullback.fst (P1 k ↘ Spec (CommRingCat.of k)) (specAlgebraMap k K)
  have hP := hP1.of_iso (Iso.refl _) (Iso.refl _) (asIso (P1.toPullback k K)) (Iso.refl _)
    (snd' := (Spec.map (CommRingCat.ofHom (algebraMap (puncturedRing K) (puncturedCoverRing f))) ≫
      puncturedι K) ≫ P1.toPullback k K) (f' := y₀) (g' := g)
    ((Category.comp_id _).trans (Category.id_comp _).symm) (by simp) (by simp [y₀])
    (by simp [g])
  let a : puncturedCover f ≅ pullback y₀ g := (puncturedCover f).isoSpec ≪≫ hP.isoPullback
  have ha : a.hom ≫ pullback.snd y₀ g =
      (pullback.fst f (puncturedι K) ≫ f) ≫ P1.toPullback k K := by
    simp only [a, Iso.trans_hom, Category.assoc, IsPullback.isoPullback_hom_snd]
    rw [← Category.assoc (Scheme.isoSpec _).hom, ← Category.assoc ((Scheme.isoSpec _).hom ≫ _),
      puncturedCover_isoSpec_hom_comp hf, pullback.condition_assoc, Category.assoc]
  -- Step 3: normalizations.
  haveI := quasiCompact_of_isCurveOver K X (pullback.fst f (puncturedι K))
  haveI := isIso_normalizationDesc_of_isCurveOver K X f (pullback.fst f (puncturedι K))
    (denseRange_puncturedCover_fst hf)
  haveI := isIso_normalizationPullback_specAlgebraMap k K (P1 k ↘ Spec (CommRingCat.of k)) y₀
  let E : X ≅ pullback (y₀.fromNormalization ≫ (P1 k ↘ Spec (CommRingCat.of k)))
      (specAlgebraMap k K) :=
    (asIso ((pullback.fst f (puncturedι K) ≫ f).normalizationDesc
      (pullback.fst f (puncturedι K)) f rfl)).symm ≪≫
    normalizationIsoOfArrowIso a (asIso (P1.toPullback k K)) ha ≪≫
    asIso (y₀.normalizationPullback g) ≪≫ pullbackRightPullbackFstIso _ _ _
  refine ⟨y₀.normalization, y₀.fromNormalization ≫ (P1 k ↘ Spec (CommRingCat.of k)), E, ?_⟩
  simp only [E, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
    pullbackRightPullbackFstIso_hom_snd]
  rw [Scheme.Hom.normalizationPullback_snd_assoc y₀ g,
    normalizationIsoOfArrowIso_hom_fromNormalization_assoc, asIso_hom, P1.toPullback_snd,
    IsIso.inv_comp_eq,
    ← Scheme.Hom.normalizationDesc_comp_assoc (pullback.fst f (puncturedι K) ≫ f)
      (pullback.fst f (puncturedι K)) f rfl, hfK]

/-- **(P2c) Belyi maps give definability, assuming finite étale descent (★).** A curve `X`
over an algebraically closed field `K` of characteristic zero admitting a Belyi map is
definable over the algebraically closed subfield `k`, provided finite étale algebras over
`K ⊗[k] R` descend to `R` (`FEtDescent k K`). The Belyi map need not be a morphism over
`Spec K` (`exists_isBelyiMap_comp_eq`). -/
theorem definableOver_of_isBelyiMap_of_fEtDescent (k K : Type u) [Field k] [IsAlgClosed k]
    [CharZero k] [Field K] [IsAlgClosed K] [CharZero K] [Algebra k K] (hD : FEtDescent k K)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X]
    (f : X ⟶ P1 K) (hf : IsBelyiMap K f) : DefinableOver k K X := by
  obtain ⟨f', hf', hf'K⟩ := exists_isBelyiMap_comp_eq K X f hf
  exact definableOver_of_isBelyiMap_of_comp_eq k K hD X f' hf' hf'K

end Belyi.Converse
