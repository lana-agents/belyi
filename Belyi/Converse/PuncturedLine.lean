/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.BaseChangeIso
import Belyi.BelyiCoverRestrict
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Finiteness

/-!
# The thrice-punctured line as an affine scheme

This file is package (P1) of the converse of Belyi's theorem
(`references/converse-rie-design.md`): it presents the open subscheme
`ℙ¹_k ∖ {0, 1, ∞}` (`Belyi.puncturedLine k`) as the spectrum of the finitely generated
`k`-algebra `R_k := k[t][(t(t-1))⁻¹]`, and shows that this presentation commutes with base
change along a ring map `k → K`, compatibly with the identification `ℙ¹_K ≅ ℙ¹_k ×_k K`
(`Belyi.P1.toPullback`, `Belyi.P1.isIso_toPullback`).

The punctured line lies in the standard chart `D₊(X₁)` (the chart not containing `∞`), whose
chart ring is `k[t]` with `t = X₀/X₁` (`Belyi.P1.awayChartEquivOne`); in this coordinate
`0 = {t = 0}` and `1 = {t = 1}`, so `ℙ¹ ∖ {0, 1, ∞} = D(t(t-1)) ⊆ D₊(X₁)`.

## Main definitions

* `Belyi.puncturedRing k`: the ring `k[t][(t(t-1))⁻¹]` (`Localization.Away`), a finitely
  generated `k`-algebra.
* `Belyi.puncturedι k : Spec (puncturedRing k) ⟶ P1 k`: the open immersion onto
  `D₊(X₀ X₁ (X₀ - X₁))`, which is `puncturedLine k` for a field `k`.
* `Belyi.puncturedRingMap k K : puncturedRing k →+* puncturedRing K`: coefficient extension.
* `Belyi.puncturedRingBaseChange k K : K ⊗[k] puncturedRing k ≃ₐ[K] puncturedRing K`.

## Main results

* `Belyi.opensRange_puncturedι`: `(puncturedι k).opensRange = puncturedLine k`.
* `Belyi.puncturedι_comp_mapOfAlgebra`, `Belyi.isPullback_puncturedι_mapOfAlgebra`: the square
  `Spec R_K → Spec R_k`, `puncturedι`, `P1.mapOfAlgebra` commutes and is cartesian.
* `Belyi.isPushout_puncturedRing`: `R_K` is the pushout `K ⊗[k] R_k` in `CommRingCat`.
* `Belyi.isPullback_puncturedRing_baseChange`: for finite étale covers (indeed any algebras)
  `B₀` of `R_k` and `B` of `R_K` with `B = R_K ⊗[R_k] B₀`, the scheme `Spec B` over `ℙ¹_K` is
  the base change of `Spec B₀` over `ℙ¹_k`, both over `ℙ¹_k` and over `Spec k`;
  `Belyi.isoPullback_puncturedRing_baseChange_comp` records the compatibility with
  `P1.toPullback`. `Belyi.isPushout_puncturedRing_of_tensorEquiv` produces the pushout
  hypothesis from an isomorphism `K ⊗[k] B₀ ≃ₐ[K] B`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization TensorProduct

namespace Belyi

open scoped P1

attribute [local instance] MvPolynomial.gradedAlgebra

section Ring

variable (k : Type u) [CommRing k]

/-- The polynomial `t (t - 1) ∈ k[t]` cutting out `0` and `1` in the affine line. -/
noncomputable abbrev puncturedPoly : Polynomial k :=
  Polynomial.X * (Polynomial.X - 1)

/-- The coordinate ring `k[t][(t(t-1))⁻¹]` of the thrice-punctured line `ℙ¹_k ∖ {0, 1, ∞}`. -/
abbrev puncturedRing : Type u :=
  Localization.Away (puncturedPoly k)

instance : Algebra.FiniteType k (puncturedRing k) :=
  Algebra.FiniteType.trans (S := Polynomial k) inferInstance inferInstance

/-- The homogeneous quadric `X₀ (X₀ - X₁)`, which dehomogenises to `t (t - 1)` on `D₊(X₁)`. -/
noncomputable abbrev puncturedQuadric : MvPolynomial (Fin 2) k :=
  X 0 * (X 0 - X 1)

lemma puncturedQuadric_mem : puncturedQuadric k ∈ P1Grading k 2 :=
  (mem_homogeneousSubmodule _ _).mpr
    ((isHomogeneous_X k 0).mul ((isHomogeneous_X k 0).sub (isHomogeneous_X k 1)))

/-- The chart element `X₀ (X₀ - X₁) / X₁²` of `D₊(X₁)`, i.e. `t (t - 1)`. -/
noncomputable abbrev puncturedChartElem : Away (P1Grading k) (X 1 : MvPolynomial (Fin 2) k) :=
  Away.isLocalizationElem (P1.X_mem_P1Grading k 1) (puncturedQuadric_mem k)

lemma awayChartEquivOne_puncturedChartElem :
    P1.awayChartEquivOne k (puncturedChartElem k) = puncturedPoly k := by
  change P1.awayEval k Polynomial.X (Away.mk _ _ _ _ _) = _
  rw [P1.awayEval_mk]
  simp

/-- The ring map from the chart ring of `D₊(X₁)` to the coordinate ring of the punctured line:
the chart isomorphism `(k[X₀,X₁]_{X₁})₀ ≅ k[t]` followed by the localization map. -/
noncomputable def puncturedChartMap :
    Away (P1Grading k) (X 1 : MvPolynomial (Fin 2) k) →+* puncturedRing k :=
  (algebraMap (Polynomial k) (puncturedRing k)).comp
    (P1.awayChartEquivOne k).toRingEquiv.toRingHom

/-- `puncturedRing k` is the localization of the chart ring of `D₊(X₁)` away from
`X₀ (X₀ - X₁) / X₁²`. -/
lemma isLocalization_puncturedChartMap :
    letI := (puncturedChartMap k).toAlgebra
    IsLocalization.Away (puncturedChartElem k) (puncturedRing k) := by
  have h := IsLocalization.isLocalization_of_base_ringEquiv (Submonoid.powers (puncturedPoly k))
    (puncturedRing k) (P1.awayChartEquivOne k).toRingEquiv.symm
  rw [Submonoid.map_powers] at h
  have he : (P1.awayChartEquivOne k).toRingEquiv.symm (puncturedPoly k) =
      puncturedChartElem k := by
    rw [RingEquiv.symm_apply_eq]
    exact (awayChartEquivOne_puncturedChartElem k).symm
  rw [he] at h
  exact h

/-- The open immersion `Spec R_k ⟶ ℙ¹_k` of the thrice-punctured line: `D(t(t-1))` inside the
chart `D₊(X₁) = Spec k[t]`. -/
noncomputable def puncturedι : Spec (CommRingCat.of (puncturedRing k)) ⟶ P1 k :=
  Spec.map (CommRingCat.ofHom (puncturedChartMap k)) ≫
    Proj.awayι (P1Grading k) (X 1) (P1.X_mem_P1Grading k 1) one_pos

instance : IsOpenImmersion (puncturedι k) := by
  letI := (puncturedChartMap k).toAlgebra
  haveI := isLocalization_puncturedChartMap k
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (puncturedChartMap k))) :=
    IsOpenImmersion.of_isLocalization (puncturedChartElem k)
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom (puncturedChartMap k)) ≫
    Proj.awayι (P1Grading k) (X 1) (P1.X_mem_P1Grading k 1) one_pos)
  infer_instance

/-- The image of `puncturedι` is the basic open `D₊(X₁ · X₀ (X₀ - X₁))`. -/
lemma opensRange_puncturedι_eq_basicOpen :
    (puncturedι k).opensRange =
      Proj.basicOpen (P1Grading k) (X 1 * puncturedQuadric k) := by
  letI := (puncturedChartMap k).toAlgebra
  haveI := isLocalization_puncturedChartMap k
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (puncturedChartMap k))) :=
    IsOpenImmersion.of_isLocalization (puncturedChartElem k)
  have hSpec : (Spec.map (CommRingCat.ofHom (puncturedChartMap k))).opensRange =
      PrimeSpectrum.basicOpen (puncturedChartElem k) :=
    TopologicalSpace.Opens.ext
      (PrimeSpectrum.localization_away_comap_range (puncturedRing k) (puncturedChartElem k))
  change (Spec.map (CommRingCat.ofHom (puncturedChartMap k)) ≫
    Proj.awayι (P1Grading k) (X 1) (P1.X_mem_P1Grading k 1) one_pos).opensRange = _
  rw [Scheme.Hom.opensRange_comp, hSpec,
    ← Proj.awayι_preimage_basicOpen (P1Grading k) (P1.X_mem_P1Grading k 1) one_pos
      (puncturedQuadric_mem k) two_pos,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Proj.opensRange_awayι, ← Proj.basicOpen_mul]

end Ring

section Field

variable (k : Type u) [Field k]

/-- A point of `ℙ¹` whose homogeneous ideal contains the linear form `ℓ` of a marked point `p`
(i.e. `p`'s ideal is `(ℓ)`) is `p` itself: `p` is a closed point and specialises to it. -/
private lemma eq_of_mem_of_markedPoint {p x : P1 k} (hp : p ∈ markedPoints k)
    {ℓ : MvPolynomial (Fin 2) k} (hpℓ : p.asHomogeneousIdeal.toIdeal = Ideal.span {ℓ})
    (hx : ℓ ∈ x.asHomogeneousIdeal.toIdeal) : x = p := by
  let p' : ProjectiveSpectrum (P1Grading k) := p
  let x' : ProjectiveSpectrum (P1Grading k) := x
  have hle : p' ≤ x' := by
    change p.asHomogeneousIdeal.toIdeal ≤ x.asHomogeneousIdeal.toIdeal
    rw [hpℓ, Ideal.span_le]
    simpa using hx
  have hcl : x' ∈ closure ({p'} : Set (ProjectiveSpectrum (P1Grading k))) :=
    (ProjectiveSpectrum.le_iff_mem_closure _ p' x').mp hle
  have hclosed : IsClosed ({p'} : Set (ProjectiveSpectrum (P1Grading k))) :=
    isClosed_singleton_markedPoint k hp
  rw [hclosed.closure_eq] at hcl
  exact hcl

/-- For a field `k`, the basic open `D₊(X₀ X₁ (X₀ - X₁))` is the thrice-punctured line. -/
lemma basicOpen_eq_puncturedLine :
    Proj.basicOpen (P1Grading k) (X 1 * puncturedQuadric k) = puncturedLine k := by
  ext x
  change X 1 * (X 0 * (X 0 - X 1)) ∉ x.asHomogeneousIdeal ↔ x ∉ markedPoints k
  have hprime := x.isPrime
  have h0 : (X 0 : MvPolynomial (Fin 2) k) ∈ x.asHomogeneousIdeal.toIdeal ↔ x = P1.zero k :=
    ⟨fun h => eq_of_mem_of_markedPoint k (zero_mem_markedPoints k)
        (by rw [P1.zero, P1.mkPoint_asIdeal]) h,
      fun h => by subst h; rw [P1.zero, P1.mkPoint_asIdeal]; exact Ideal.mem_span_singleton_self _⟩
  have h1 : (X 0 - X 1 : MvPolynomial (Fin 2) k) ∈ x.asHomogeneousIdeal.toIdeal ↔
      x = P1.one k :=
    ⟨fun h => eq_of_mem_of_markedPoint k (one_mem_markedPoints k)
        (by rw [P1.one, P1.mkPoint_asIdeal]) h,
      fun h => by subst h; rw [P1.one, P1.mkPoint_asIdeal]; exact Ideal.mem_span_singleton_self _⟩
  have h2 : (X 1 : MvPolynomial (Fin 2) k) ∈ x.asHomogeneousIdeal.toIdeal ↔ x = P1.infty k :=
    ⟨fun h => eq_of_mem_of_markedPoint k (infty_mem_markedPoints k)
        (by rw [P1.infty, P1.mkPoint_asIdeal]) h,
      fun h => by subst h; rw [P1.infty, P1.mkPoint_asIdeal]; exact Ideal.mem_span_singleton_self _⟩
  change X 1 * (X 0 * (X 0 - X 1)) ∉ x.asHomogeneousIdeal.toIdeal ↔ _
  rw [hprime.mul_mem_iff_mem_or_mem, hprime.mul_mem_iff_mem_or_mem, h0, h1, h2]
  change _ ↔ ¬ (x = P1.zero k ∨ x = P1.one k ∨ x = P1.infty k)
  tauto

/-- **The image of `puncturedι` is the thrice-punctured line** `ℙ¹_k ∖ {0, 1, ∞}`. -/
theorem opensRange_puncturedι : (puncturedι k).opensRange = puncturedLine k := by
  rw [opensRange_puncturedι_eq_basicOpen, basicOpen_eq_puncturedLine]

end Field

section BaseChange

variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]

lemma map_puncturedPoly :
    Polynomial.map (algebraMap k K) (puncturedPoly k) = puncturedPoly K := by
  simp

/-- The coefficient-extension map `k[t][(t(t-1))⁻¹] → K[t][(t(t-1))⁻¹]`. -/
noncomputable def puncturedRingMap : puncturedRing k →+* puncturedRing K :=
  IsLocalization.Away.lift (puncturedPoly k)
    (g := (algebraMap (Polynomial K) (puncturedRing K)).comp
      (Polynomial.mapRingHom (algebraMap k K)))
    (by
      rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, map_puncturedPoly]
      exact IsLocalization.Away.algebraMap_isUnit _)

@[simp]
lemma puncturedRingMap_algebraMap (p : Polynomial k) :
    puncturedRingMap k K (algebraMap (Polynomial k) (puncturedRing k) p) =
      algebraMap (Polynomial K) (puncturedRing K) (p.map (algebraMap k K)) :=
  IsLocalization.lift_eq _ _

attribute [local instance] Polynomial.algebra

/-- The `puncturedRing k`-algebra structure on `puncturedRing K` given by `puncturedRingMap`.
Not a global instance (it would form a diamond with `Algebra.id` for `K = k`). -/
noncomputable abbrev puncturedRingAlgebra : Algebra (puncturedRing k) (puncturedRing K) :=
  (puncturedRingMap k K).toAlgebra

attribute [local instance] puncturedRingAlgebra

instance : IsScalarTower (Polynomial k) (puncturedRing k) (puncturedRing K) :=
  IsScalarTower.of_algebraMap_eq fun p => by
    change _ = puncturedRingMap k K _
    rw [puncturedRingMap_algebraMap, IsScalarTower.algebraMap_apply (Polynomial k)
      (Polynomial K) (puncturedRing K), Polynomial.algebraMap_def, Polynomial.coe_mapRingHom]

instance : IsScalarTower k (puncturedRing k) (puncturedRing K) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change _ = puncturedRingMap k K _
    rw [IsScalarTower.algebraMap_apply k (Polynomial k) (puncturedRing k),
      puncturedRingMap_algebraMap, IsScalarTower.algebraMap_apply k K (puncturedRing K),
      IsScalarTower.algebraMap_apply K (Polynomial K) (puncturedRing K)]
    simp

/-- `puncturedRing K` is the base change `K ⊗[k] puncturedRing k`: localization and polynomial
rings commute with base change. -/
instance isPushout_puncturedRing_algebra :
    Algebra.IsPushout k K (puncturedRing k) (puncturedRing K) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (Polynomial K)
      (Submonoid.powers (puncturedPoly k))) (puncturedRing K) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, Polynomial.algebraMap_def,
      Polynomial.coe_mapRingHom, map_puncturedPoly]
    infer_instance
  haveI h1 : Algebra.IsPushout (Polynomial k) (Polynomial K) (puncturedRing k)
      (puncturedRing K) :=
    Algebra.isPushout_of_isLocalization (A := puncturedRing k)
      (Submonoid.powers (puncturedPoly k)) (Polynomial K) (puncturedRing K)
  haveI := h1.symm
  exact ((Algebra.IsPushout.comp_iff k (Polynomial k) K (Polynomial K)).mpr this).symm

/-- **Base change of the coordinate ring of the punctured line**:
`K ⊗[k] k[t][(t(t-1))⁻¹] ≅ K[t][(t(t-1))⁻¹]`. -/
noncomputable def puncturedRingBaseChange :
    K ⊗[k] puncturedRing k ≃ₐ[K] puncturedRing K :=
  Algebra.IsPushout.equiv k K (puncturedRing k) (puncturedRing K)

@[simp]
lemma puncturedRingBaseChange_tmul (a : K) (r : puncturedRing k) :
    puncturedRingBaseChange k K (a ⊗ₜ r) =
      algebraMap K (puncturedRing K) a * puncturedRingMap k K r :=
  Algebra.IsPushout.equiv_tmul (R := k) (S := K) (R' := puncturedRing k)
    (S' := puncturedRing K) a r

@[simp]
lemma puncturedRingBaseChange_symm_puncturedRingMap (r : puncturedRing k) :
    (puncturedRingBaseChange k K).symm (puncturedRingMap k K r) = 1 ⊗ₜ r := by
  rw [AlgEquiv.symm_apply_eq, puncturedRingBaseChange_tmul, map_one, one_mul]

/-- The base-change square of coordinate rings is a pushout in `CommRingCat`. -/
theorem isPushout_puncturedRing :
    IsPushout (CommRingCat.ofHom (algebraMap k K))
      (CommRingCat.ofHom (algebraMap k (puncturedRing k)))
      (CommRingCat.ofHom (algebraMap K (puncturedRing K)))
      (CommRingCat.ofHom (puncturedRingMap k K)) :=
  CommRingCat.isPushout_of_isPushout k K (puncturedRing k) (puncturedRing K)

/-- The base-change square of `Spec`s of coordinate rings is cartesian:
`Spec R_K = Spec R_k ×_{Spec k} Spec K`. -/
theorem isPullback_Spec_puncturedRing :
    IsPullback (Spec.map (CommRingCat.ofHom (puncturedRingMap k K)))
      (Spec.map (CommRingCat.ofHom (algebraMap K (puncturedRing K))))
      (Spec.map (CommRingCat.ofHom (algebraMap k (puncturedRing k))))
      (specAlgebraMap k K) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_puncturedRing k K)).flip

/-- `puncturedChartMap` is natural in the base ring: it intertwines the chart base-change map
`P1.chartMap k K 1` with `puncturedRingMap k K`. -/
lemma puncturedChartMap_comp_chartMap :
    (puncturedChartMap K).comp (P1.chartMap k K 1) =
      (puncturedRingMap k K).comp (puncturedChartMap k) := by
  ext q
  simp only [puncturedChartMap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
  rw [P1.chartMap_naturality_one, puncturedRingMap_algebraMap]

/-- The punctured-line inclusions commute with the base-change morphism
`P1.mapOfAlgebra k K : ℙ¹_K ⟶ ℙ¹_k`. -/
@[reassoc]
theorem puncturedι_comp_mapOfAlgebra :
    puncturedι K ≫ P1.mapOfAlgebra k K =
      Spec.map (CommRingCat.ofHom (puncturedRingMap k K)) ≫ puncturedι k := by
  have h := P1.awayι_comp_mapOfAlgebra k K 1
  change Spec.map (CommRingCat.ofHom (puncturedChartMap K)) ≫
      (Proj.awayι (P1Grading K) (X 1) (P1.X_mem_P1Grading K 1) one_pos ≫
        P1.mapOfAlgebra k K) =
    Spec.map (CommRingCat.ofHom (puncturedRingMap k K)) ≫
      (Spec.map (CommRingCat.ofHom (puncturedChartMap k)) ≫
        Proj.awayι (P1Grading k) (X 1) (P1.X_mem_P1Grading k 1) one_pos)
  have hr : Spec.map (CommRingCat.ofHom (puncturedChartMap K)) ≫
      Spec.map (CommRingCat.ofHom (P1.chartMap k K 1)) =
      Spec.map (CommRingCat.ofHom (puncturedRingMap k K)) ≫
        Spec.map (CommRingCat.ofHom (puncturedChartMap k)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      puncturedChartMap_comp_chartMap]
  rw [h]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ Proj.awayι (P1Grading k) (X 1) (P1.X_mem_P1Grading k 1) one_pos) hr).trans
      (Category.assoc _ _ _))

/-- The preimage of the punctured line under the base-change morphism is the punctured line. -/
lemma mapOfAlgebra_preimage_opensRange_puncturedι :
    P1.mapOfAlgebra k K ⁻¹ᵁ (puncturedι k).opensRange = (puncturedι K).opensRange := by
  rw [opensRange_puncturedι_eq_basicOpen, opensRange_puncturedι_eq_basicOpen]
  have h := Proj.map_preimage_basicOpen (P1.gradedMapOfAlgebra k K)
    (P1.irrelevant_le_map_gradedMapOfAlgebra k K) (X 1 * puncturedQuadric k)
  refine h.trans ?_
  congr 1
  simp [puncturedQuadric]

/-- **The punctured line commutes with base change, over `ℙ¹`**: the square
```
Spec R_K ──puncturedι K──→ ℙ¹_K
   │                          │ mapOfAlgebra
   ▼                          ▼
Spec R_k ──puncturedι k──→ ℙ¹_k
```
is cartesian. -/
theorem isPullback_puncturedι_mapOfAlgebra :
    IsPullback (Spec.map (CommRingCat.ofHom (puncturedRingMap k K))) (puncturedι K)
      (puncturedι k) (P1.mapOfAlgebra k K) :=
  IsOpenImmersion.isPullback _ _ _ _ (puncturedι_comp_mapOfAlgebra k K)
    (mapOfAlgebra_preimage_opensRange_puncturedι k K)

/-- The punctured-line inclusion followed by the structure morphism of `ℙ¹_k` is `Spec` of the
`k`-algebra structure of `puncturedRing k`. -/
@[reassoc]
lemma puncturedι_structMap (k : Type u) [CommRing k] :
    puncturedι k ≫ (P1 k ↘ Spec (CommRingCat.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (puncturedRing k))) := by
  change Spec.map (CommRingCat.ofHom (puncturedChartMap k)) ≫
      (Proj.awayι (P1Grading k) (X 1) (P1.X_mem_P1Grading k 1) one_pos ≫ P1.structMap k) = _
  rw [P1.awayι_comp_structMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext c
  change algebraMap (Polynomial k) (puncturedRing k)
    (P1.awayChartEquivOne k (P1.chartAlgHom k 1 c)) = _
  rw [show P1.chartAlgHom k 1 c = algebraMap k _ c from rfl, AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply]

/-! ### Base change of covers of the punctured line -/

variable {k K}
variable {B₀ B : Type u} [CommRing B₀] [CommRing B] [Algebra (puncturedRing k) B₀]
  [Algebra (puncturedRing K) B] (φ : B₀ →+* B)

/-- **Base change of a cover of the punctured line, over `ℙ¹`.** If `B = R_K ⊗[R_k] B₀`
(a pushout square of rings with comparison map `φ : B₀ → B`), then `Spec B ⟶ ℙ¹_K` is the base
change of `Spec B₀ ⟶ ℙ¹_k` along `P1.mapOfAlgebra k K : ℙ¹_K ⟶ ℙ¹_k`. -/
theorem isPullback_puncturedRing_baseChange_P1
    (hB : IsPushout (CommRingCat.ofHom (puncturedRingMap k K))
      (CommRingCat.ofHom (algebraMap (puncturedRing k) B₀))
      (CommRingCat.ofHom (algebraMap (puncturedRing K) B)) (CommRingCat.ofHom φ)) :
    IsPullback (Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom (algebraMap (puncturedRing K) B)) ≫ puncturedι K)
      (Spec.map (CommRingCat.ofHom (algebraMap (puncturedRing k) B₀)) ≫ puncturedι k)
      (P1.mapOfAlgebra k K) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ hB).flip.paste_vert
    (isPullback_puncturedι_mapOfAlgebra k K)

/-- **Base change of a cover of the punctured line, over `Spec k`.** Under the hypotheses of
`isPullback_puncturedRing_baseChange_P1`, `Spec B` is the fibre product
`Spec B₀ ×_{Spec k} Spec K`, the maps to the factors being `Spec φ` and
`Spec B ⟶ ℙ¹_K ⟶ Spec K`. -/
theorem isPullback_puncturedRing_baseChange
    (hB : IsPushout (CommRingCat.ofHom (puncturedRingMap k K))
      (CommRingCat.ofHom (algebraMap (puncturedRing k) B₀))
      (CommRingCat.ofHom (algebraMap (puncturedRing K) B)) (CommRingCat.ofHom φ)) :
    IsPullback (Spec.map (CommRingCat.ofHom φ))
      ((Spec.map (CommRingCat.ofHom (algebraMap (puncturedRing K) B)) ≫ puncturedι K) ≫
        (P1 K ↘ Spec (CommRingCat.of K)))
      ((Spec.map (CommRingCat.ofHom (algebraMap (puncturedRing k) B₀)) ≫ puncturedι k) ≫
        (P1 k ↘ Spec (CommRingCat.of k)))
      (specAlgebraMap k K) :=
  (isPullback_puncturedRing_baseChange_P1 φ hB).paste_vert (P1.isPullback_mapOfAlgebra k K)

/-- **Compatibility with `P1.toPullback`.** The identification
`Spec B ≅ Spec B₀ ×_{Spec k} Spec K` of `isPullback_puncturedRing_baseChange`, followed by the
base change of `Spec B₀ ⟶ ℙ¹_k`, is `Spec B ⟶ ℙ¹_K` followed by
`P1.toPullback k K : ℙ¹_K ≅ ℙ¹_k ×_k K`. -/
theorem isoPullback_puncturedRing_baseChange_comp
    (hB : IsPushout (CommRingCat.ofHom (puncturedRingMap k K))
      (CommRingCat.ofHom (algebraMap (puncturedRing k) B₀))
      (CommRingCat.ofHom (algebraMap (puncturedRing K) B)) (CommRingCat.ofHom φ)) :
    (isPullback_puncturedRing_baseChange φ hB).isoPullback.hom ≫
        pullback.map _ _ (P1 k ↘ Spec (CommRingCat.of k)) (specAlgebraMap k K)
          (Spec.map (CommRingCat.ofHom (algebraMap (puncturedRing k) B₀)) ≫ puncturedι k)
          (𝟙 _) (𝟙 _) (by simp) (by simp) =
      (Spec.map (CommRingCat.ofHom (algebraMap (puncturedRing K) B)) ≫ puncturedι K) ≫
        P1.toPullback k K := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc,
      Category.assoc, P1.toPullback_fst]
    exact (isPullback_puncturedRing_baseChange_P1 φ hB).w
  · simp only [Category.assoc, pullback.lift_snd, Category.comp_id, P1.toPullback_snd]
    rw [IsPullback.isoPullback_hom_snd]

/-- **From a tensor-product description to the pushout square.** If `B` is an `R_K`-algebra
and `e : K ⊗[k] B₀ ≃ₐ[K] B` is compatible with the structure maps from `R_k` (via
`puncturedRingMap`), then `B = R_K ⊗[R_k] B₀`, i.e. the hypothesis of
`isPullback_puncturedRing_baseChange` holds with comparison map `b ↦ e (1 ⊗ b)`. -/
theorem isPushout_puncturedRing_of_tensorEquiv [Algebra k B₀]
    [IsScalarTower k (puncturedRing k) B₀] [Algebra K B] [IsScalarTower K (puncturedRing K) B]
    (e : K ⊗[k] B₀ ≃ₐ[K] B)
    (he : ∀ r : puncturedRing k, e (1 ⊗ₜ algebraMap (puncturedRing k) B₀ r) =
      algebraMap (puncturedRing K) B (puncturedRingMap k K r)) :
    IsPushout (CommRingCat.ofHom (puncturedRingMap k K))
      (CommRingCat.ofHom (algebraMap (puncturedRing k) B₀))
      (CommRingCat.ofHom (algebraMap (puncturedRing K) B))
      (CommRingCat.ofHom (e.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := B₀)).toRingHom)) := by
  set φ : B₀ →+* B := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := B₀)).toRingHom with hφ
  letI : Algebra B₀ B := φ.toAlgebra
  letI : Algebra (puncturedRing k) B :=
    ((algebraMap (puncturedRing K) B).comp (puncturedRingMap k K)).toAlgebra
  letI : Algebra k B := ((algebraMap K B).comp (algebraMap k K)).toAlgebra
  haveI : IsScalarTower (puncturedRing k) (puncturedRing K) B :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (puncturedRing k) B₀ B :=
    IsScalarTower.of_algebraMap_eq fun r => (he r).symm
  haveI : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k B₀ B := IsScalarTower.of_algebraMap_eq fun c => by
    change _ = e (1 ⊗ₜ algebraMap k B₀ c)
    rw [← Algebra.TensorProduct.algebraMap_apply', IsScalarTower.algebraMap_apply k K (K ⊗[k] B₀),
      AlgEquiv.commutes]
    rfl
  haveI : IsScalarTower k (puncturedRing K) B := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap K B (algebraMap k K c) = _
    rw [IsScalarTower.algebraMap_apply k K (puncturedRing K),
      ← IsScalarTower.algebraMap_apply K (puncturedRing K) B]
  -- `B = K ⊗[k] B₀`
  haveI h1 : Algebra.IsPushout k K B₀ B := by
    rw [Algebra.isPushout_iff]
    exact IsBaseChange.of_equiv e.toLinearEquiv fun _ => rfl
  haveI h1' := h1.symm
  haveI : Algebra.IsPushout k (puncturedRing k) K (puncturedRing K) :=
    (isPushout_puncturedRing_algebra k K).symm
  haveI h2 : Algebra.IsPushout (puncturedRing k) B₀ (puncturedRing K) B :=
    (Algebra.IsPushout.comp_iff k (puncturedRing k) K (puncturedRing K)).mp h1'
  haveI := h2.symm
  exact CommRingCat.isPushout_of_isPushout (puncturedRing k) (puncturedRing K) B₀ B

end BaseChange

end Belyi
