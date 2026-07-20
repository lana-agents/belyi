/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.BaseChange
import Belyi.P1.ChartCoord
import Belyi.P1.AffineChartBaseChange
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# The base change of `ℙ¹` is an isomorphism

We show that the comparison morphism
`Belyi.P1.toPullback : P1 K ⟶ pullback (P1 k₀ ↘ Spec k₀) (specAlgebraMap k₀ K)`
from `Belyi/P1/BaseChange.lean` is an isomorphism, giving the canonical identification
`ℙ¹_{k₀} ×_{k₀} K ≅ ℙ¹_K` required by the pair version of B3 (#48).

## Strategy

Cover `ℙ¹_{k₀}` by the two standard charts `D₊(X₀), D₊(X₁)`. On each chart the comparison
morphism is `Spec` of the base-change ring map `chartMap`, and the chart square is a pullback
(`IsOpenImmersion.isPullback`). The chart rings are polynomial rings (`ChartCoord`), so the
square
```
k₀           → (k₀[X₀,X₁]_{Xᵢ})₀
↓                    ↓ chartMap
K            → (K[X₀,X₁]_{Xᵢ})₀
```
is a pushout (polynomial base change), giving each chart square of the structure morphisms as a
pullback. `Scheme.isPullback_of_openCover` assembles these into
`IsPullback (mapOfAlgebra) (structMap K) (structMap k₀) (specAlgebraMap)`, whence
`IsIso toPullback`.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory Limits MvPolynomial ProjectiveSpectrum
  HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k₀ K : Type u) [CommRing k₀] [CommRing K] [Algebra k₀ K]

/-! ### The base-change chart map -/

/-- The coefficient map fixes the coordinates: `gradedMapOfAlgebra k₀ K (Xᵢ) = Xᵢ`. -/
lemma gradedMap_X (i : Fin 2) :
    gradedMapOfAlgebra k₀ K (X i) = (X i : MvPolynomial (Fin 2) K) := by
  rw [gradedMapOfAlgebra_apply, map_X]

/-- The base-change ring map on the `D₊(Xᵢ)` chart ring, `(k₀[X₀,X₁]_{Xᵢ})₀ → (K[X₀,X₁]_{Xᵢ})₀`,
obtained from `HomogeneousLocalization.Away.map` of the coefficient map, transported along
`gradedMapOfAlgebra k₀ K (Xᵢ) = Xᵢ`. -/
noncomputable def chartMap (i : Fin 2) :
    Away (P1Grading k₀) (X i : MvPolynomial (Fin 2) k₀) →+*
      Away (P1Grading K) (X i : MvPolynomial (Fin 2) K) :=
  (eqToHom (congrArg (fun s => CommRingCat.of (Away (P1Grading K) s))
      (gradedMap_X k₀ K i))).hom.comp (Away.map (gradedMapOfAlgebra k₀ K) (X i))

/-- `chartMap` on a homogeneous fraction `a / Xᵢⁿ` extends coefficients of the numerator. -/
lemma chartMap_mk (i : Fin 2) (n : ℕ) (a : MvPolynomial (Fin 2) k₀)
    (ha : a ∈ P1Grading k₀ (n • 1)) :
    chartMap k₀ K i (Away.mk (P1Grading k₀) (X_mem_P1Grading k₀ i) n a ha) =
      Away.mk (P1Grading K) (X_mem_P1Grading K i) n (MvPolynomial.map (algebraMap k₀ K) a)
        ((mem_homogeneousSubmodule _ _).mpr (((mem_homogeneousSubmodule _ _).mp ha).map _)) := by
  simp only [chartMap, RingHom.comp_apply, Away.map_mk]
  rw [Away_mk_eqToHom (gradedMap_X k₀ K i)]
  rfl

/-- The `k`-algebra structure map of the chart ring `(k[X₀,X₁]_{Xᵢ})₀`, as an explicit ring
homomorphism (definitionally the `algebraMap` for the literal charts `X₀`, `X₁`). -/
noncomputable def chartAlgHom (k : Type u) [CommRing k] (i : Fin 2) :
    k →+* Away (P1Grading k) (X i : MvPolynomial (Fin 2) k) :=
  (fromZeroRingHom (P1Grading k) (Submonoid.powers (X i : MvPolynomial (Fin 2) k))).comp
    (algebraMap k (P1Grading k 0))

/-! ### The chart map corresponds to `Polynomial.map` -/

/-- Coefficient extension `MvPolynomial.map (algebraMap k₀ K)` commutes with evaluation `aeval`
into a univariate polynomial ring, provided the evaluation points correspond under
`Polynomial.map`. Both sides are ring homomorphisms out of `MvPolynomial σ k₀` which agree on
constants and on the generators, so they coincide. -/
lemma aeval_map_algebraMap_comm {σ : Type*} (v : σ → Polynomial K) (w : σ → Polynomial k₀)
    (hvw : ∀ i, v i = Polynomial.map (algebraMap k₀ K) (w i)) (a : MvPolynomial σ k₀) :
    aeval v (MvPolynomial.map (algebraMap k₀ K) a) =
      Polynomial.map (algebraMap k₀ K) (aeval w a) := by
  have h : ((aeval v : MvPolynomial σ K →ₐ[K] Polynomial K).toRingHom.comp
        (MvPolynomial.map (algebraMap k₀ K))) =
      (Polynomial.mapRingHom (algebraMap k₀ K)).comp
        (aeval w : MvPolynomial σ k₀ →ₐ[k₀] Polynomial k₀).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp [hvw i])
  exact DFunLike.congr_fun h a

/-- Under the chart-coordinate isomorphisms `awayChartEquivOne` (`ChartCoord`), the base-change
chart map `chartMap 1` corresponds to `Polynomial.map`. This is the naturality square underlying
the chart pushout. -/
lemma chartMap_naturality_one (q : Away (P1Grading k₀) (X 1)) :
    awayChartEquivOne K (chartMap k₀ K 1 q) =
      Polynomial.map (algebraMap k₀ K) (awayChartEquivOne k₀ q) := by
  have hK : ∀ x : Away (P1Grading K) (X 1),
      awayChartEquivOne K x = awayEval K Polynomial.X x := fun _ => rfl
  have h0 : ∀ x : Away (P1Grading k₀) (X 1),
      awayChartEquivOne k₀ x = awayEval k₀ Polynomial.X x := fun _ => rfl
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (P1Grading k₀) (X_mem_P1Grading k₀ 1) q
  rw [chartMap_mk, hK, h0, awayEval_mk, awayEval_mk]
  exact aeval_map_algebraMap_comm k₀ K ![Polynomial.X, 1] ![Polynomial.X, 1]
    (fun i => by fin_cases i <;> simp) a

/-- Under `awayChartEquivZero`, the base-change chart map `chartMap 0` corresponds to
`Polynomial.map`. -/
lemma chartMap_naturality_zero (q : Away (P1Grading k₀) (X 0)) :
    awayChartEquivZero K (chartMap k₀ K 0 q) =
      Polynomial.map (algebraMap k₀ K) (awayChartEquivZero k₀ q) := by
  have hK : ∀ x : Away (P1Grading K) (X 0),
      awayChartEquivZero K x = awayEval0 K Polynomial.X x := fun _ => rfl
  have h0 : ∀ x : Away (P1Grading k₀) (X 0),
      awayChartEquivZero k₀ x = awayEval0 k₀ Polynomial.X x := fun _ => rfl
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (P1Grading k₀) (X_mem_P1Grading k₀ 0) q
  rw [chartMap_mk, hK, h0, awayEval0_mk, awayEval0_mk]
  exact aeval_map_algebraMap_comm k₀ K ![1, Polynomial.X] ![1, Polynomial.X]
    (fun i => by fin_cases i <;> simp) a

/-! ### The chart pushout -/

/-- The base-change square of the `D₊(X₁)` chart ring is a pushout in `CommRingCat`. -/
lemma isPushout_chart_one :
    IsPushout (CommRingCat.ofHom (algebraMap k₀ K))
      (CommRingCat.ofHom (chartAlgHom k₀ 1))
      (CommRingCat.ofHom (chartAlgHom K 1))
      (CommRingCat.ofHom (chartMap k₀ K 1)) := by
  letI : Algebra (Polynomial k₀) (Polynomial K) := Polynomial.algebra k₀ K
  haveI : IsScalarTower k₀ K (Polynomial K) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k₀ (Polynomial k₀) (Polynomial K) :=
    .of_algebraMap_eq fun x => by simp [Polynomial.algebraMap_def, Polynomial.coe_mapRingHom]
  refine (CommRingCat.isPushout_of_isPushout k₀ K (Polynomial k₀) (Polynomial K)).of_iso
    (Iso.refl _) (Iso.refl _)
    (awayChartEquivOne k₀).symm.toRingEquiv.toCommRingCatIso
    (awayChartEquivOne K).symm.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
  · simp
  · refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    simp only [RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply, CommRingCat.hom_ofHom, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv,
      Iso.refl_hom, CommRingCat.hom_id, RingHom.id_apply]
    rw [AlgEquiv.commutes]
    rfl
  · refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    simp only [RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply, CommRingCat.hom_ofHom, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv,
      Iso.refl_hom, CommRingCat.hom_id, RingHom.id_apply]
    rw [AlgEquiv.commutes]
    rfl
  · refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
    simp only [RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply, CommRingCat.hom_ofHom, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
    rw [Polynomial.algebraMap_def, Polynomial.coe_mapRingHom, AlgEquiv.symm_apply_eq,
      chartMap_naturality_one, AlgEquiv.apply_symm_apply]

/-- The base-change square of the `D₊(X₀)` chart ring is a pushout in `CommRingCat`. -/
lemma isPushout_chart_zero :
    IsPushout (CommRingCat.ofHom (algebraMap k₀ K))
      (CommRingCat.ofHom (chartAlgHom k₀ 0))
      (CommRingCat.ofHom (chartAlgHom K 0))
      (CommRingCat.ofHom (chartMap k₀ K 0)) := by
  letI : Algebra (Polynomial k₀) (Polynomial K) := Polynomial.algebra k₀ K
  haveI : IsScalarTower k₀ K (Polynomial K) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k₀ (Polynomial k₀) (Polynomial K) :=
    .of_algebraMap_eq fun x => by simp [Polynomial.algebraMap_def, Polynomial.coe_mapRingHom]
  refine (CommRingCat.isPushout_of_isPushout k₀ K (Polynomial k₀) (Polynomial K)).of_iso
    (Iso.refl _) (Iso.refl _)
    (awayChartEquivZero k₀).symm.toRingEquiv.toCommRingCatIso
    (awayChartEquivZero K).symm.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
  · simp
  · refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    simp only [RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply, CommRingCat.hom_ofHom, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv,
      Iso.refl_hom, CommRingCat.hom_id, RingHom.id_apply]
    rw [AlgEquiv.commutes]
    rfl
  · refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    simp only [RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply, CommRingCat.hom_ofHom, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv,
      Iso.refl_hom, CommRingCat.hom_id, RingHom.id_apply]
    rw [AlgEquiv.commutes]
    rfl
  · refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
    simp only [RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply, CommRingCat.hom_ofHom, RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
    rw [Polynomial.algebraMap_def, Polynomial.coe_mapRingHom, AlgEquiv.symm_apply_eq,
      chartMap_naturality_zero, AlgEquiv.apply_symm_apply]

/-! ### The two-chart cover and the geometric chart square -/

/-- The irrelevant ideal of `k[X₀,X₁]` is contained in the ideal generated by the coordinates
`X₀, X₁`: every monomial of a positive-degree homogeneous polynomial uses a coordinate. -/
lemma irrelevant_le_span_X (k : Type u) [CommRing k] :
    (HomogeneousIdeal.irrelevant (P1Grading k)).toIdeal ≤
      Ideal.span (Set.range (fun i : Fin 2 => (X i : MvPolynomial (Fin 2) k))) := by
  classical
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi p hp
  have hph : p.IsHomogeneous i := (mem_homogeneousSubmodule _ _).mp hp
  rw [p.as_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact absurd (hph (mem_support_iff.mp hd)) (by simpa using hi.ne)
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra h
    exact hd0 (by ext j; simpa using not_not.mp (not_exists.mp h j))
  have hXj : (X j : MvPolynomial (Fin 2) k) ∈
      Ideal.span (Set.range (fun i : Fin 2 => (X i : MvPolynomial (Fin 2) k))) :=
    Ideal.subset_span ⟨j, rfl⟩
  have hdvd : (X j : MvPolynomial (Fin 2) k) ∣ monomial d (coeff d p) := by
    rw [X, MvPolynomial.monomial_dvd_monomial]
    exact ⟨Or.inr (by simpa [Finsupp.single_le_iff] using Nat.one_le_iff_ne_zero.mpr hj),
      one_dvd _⟩
  exact Ideal.mem_of_dvd _ hdvd hXj

/-- The two-chart affine open cover of `ℙ¹` by `D₊(X₀)`, `D₊(X₁)`. -/
noncomputable def coordCover : (P1 k₀).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (P1Grading k₀)
    (fun i : Fin 2 => (X i : MvPolynomial (Fin 2) k₀))
    (m := fun _ => 1) (fun i => X_mem_P1Grading k₀ i) (fun _ => one_pos)
    (irrelevant_le_span_X k₀)

@[simp] lemma coordCover_f (i : Fin 2) :
    (coordCover k₀).openCover.f i =
      Proj.awayι (P1Grading k₀) (X i) (X_mem_P1Grading k₀ i) one_pos := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The structure morphism of `ℙ¹` restricted to the chart `D₊(Xᵢ)` is `Spec` of the chart
algebra structure map. -/
lemma awayι_comp_structMap (k : Type u) [CommRing k] (i : Fin 2) :
    Proj.awayι (P1Grading k) (X i) (X_mem_P1Grading k i) one_pos ≫ structMap k =
      Spec.map (CommRingCat.ofHom (chartAlgHom k i)) := by
  rw [structMap, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The base-change morphism restricted to charts: `mapOfAlgebra` intertwines the chart
inclusions via `Spec (chartMap)`. -/
lemma awayι_comp_mapOfAlgebra (i : Fin 2) :
    Proj.awayι (P1Grading K) (X i) (X_mem_P1Grading K i) one_pos ≫ mapOfAlgebra k₀ K =
      Spec.map (CommRingCat.ofHom (chartMap k₀ K i)) ≫
        Proj.awayι (P1Grading k₀) (X i) (X_mem_P1Grading k₀ i) one_pos := by
  have hfX : gradedMapOfAlgebra k₀ K (X i) = (X i : MvPolynomial (Fin 2) K) := gradedMap_X k₀ K i
  have h := AlgebraicGeometry.Proj.awayι_comp_map
    (f := gradedMapOfAlgebra k₀ K) (hf := irrelevant_le_map_gradedMapOfAlgebra k₀ K)
    one_pos (X i : MvPolynomial (Fin 2) k₀) (X_mem_P1Grading k₀ i)
  simp only [mapOfAlgebra, P1]
  rw [awayι_eqToHom_transport one_pos hfX.symm (X_mem_P1Grading K i)
      ((gradedMapOfAlgebra k₀ K).map_mem (X_mem_P1Grading k₀ i))]
  simp only [Category.assoc]
  rw [h, ← Spec.map_eqToHom (e := congrArg (fun s =>
      CommRingCat.of (HomogeneousLocalization.Away (P1Grading K) s)) hfX)]
  simp only [← Category.assoc]
  congr 1
  simp only [← Spec.map_comp]
  congr 1

/-- The chart square is a pullback: the base change of `mapOfAlgebra` along the chart inclusion
`D₊(Xᵢ) ↪ ℙ¹_{k₀}` is the chart inclusion `D₊(Xᵢ) ↪ ℙ¹_K` with top map `Spec (chartMap)`. -/
lemma isPullback_chartSquare (i : Fin 2) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartMap k₀ K i)))
      (Proj.awayι (P1Grading K) (X i) (X_mem_P1Grading K i) one_pos)
      (Proj.awayι (P1Grading k₀) (X i) (X_mem_P1Grading k₀ i) one_pos)
      (mapOfAlgebra k₀ K) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (awayι_comp_mapOfAlgebra k₀ K i) ?_
  rw [Proj.opensRange_awayι, Proj.opensRange_awayι, mapOfAlgebra,
    Proj.map_preimage_basicOpen, gradedMap_X]

/-- The chart square of the structure morphisms is a pullback: `Spec` of the chart pushout. -/
lemma isPullback_chartStructSquare (i : Fin 2) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartMap k₀ K i)))
      (Proj.awayι (P1Grading K) (X i) (X_mem_P1Grading K i) one_pos ≫ structMap K)
      (Proj.awayι (P1Grading k₀) (X i) (X_mem_P1Grading k₀ i) one_pos ≫ structMap k₀)
      (specAlgebraMap k₀ K) := by
  have hpush : IsPushout (CommRingCat.ofHom (algebraMap k₀ K))
      (CommRingCat.ofHom (chartAlgHom k₀ i)) (CommRingCat.ofHom (chartAlgHom K i))
      (CommRingCat.ofHom (chartMap k₀ K i)) := by
    fin_cases i
    · exact isPushout_chart_zero k₀ K
    · exact isPushout_chart_one k₀ K
  have h := isPullback_SpecMap_of_isPushout _ _ _ _ hpush
  rw [← awayι_comp_structMap K i, ← awayι_comp_structMap k₀ i] at h
  exact h.flip

set_option backward.isDefEq.respectTransparency false in
/-- The chart-local pullback condition feeding `Scheme.isPullback_of_openCover`. -/
lemma isPullback_Hcond (i : Fin 2) :
    IsPullback
      (pullback.snd (mapOfAlgebra k₀ K)
        (Proj.awayι (P1Grading k₀) (X i) (X_mem_P1Grading k₀ i) one_pos))
      (pullback.fst (mapOfAlgebra k₀ K)
        (Proj.awayι (P1Grading k₀) (X i) (X_mem_P1Grading k₀ i) one_pos) ≫ structMap K)
      (Proj.awayι (P1Grading k₀) (X i) (X_mem_P1Grading k₀ i) one_pos ≫ structMap k₀)
      (specAlgebraMap k₀ K) := by
  refine (isPullback_chartStructSquare k₀ K i).of_iso
    (isPullback_chartSquare k₀ K i).flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [(isPullback_chartSquare k₀ K i).flip.isoPullback_hom_snd]
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [← Category.assoc, (isPullback_chartSquare k₀ K i).flip.isoPullback_hom_fst]
  · simp
  · simp

/-! ### Assembly -/

/-- **`ℙ¹` commutes with base change.** The square of structure morphisms is cartesian. -/
theorem isPullback_mapOfAlgebra :
    IsPullback (mapOfAlgebra k₀ K) (P1 K ↘ Spec (CommRingCat.of K))
      (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K) := by
  refine AlgebraicGeometry.Scheme.isPullback_of_openCover (mapOfAlgebra k₀ K)
    (P1 K ↘ Spec (CommRingCat.of K)) (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)
    (coordCover k₀).openCover (fun i => ?_)
  rw [structMap_eq, structMap_eq]
  exact isPullback_Hcond k₀ K i

/-- **The comparison morphism `toPullback` is an isomorphism** (taxis issue #82/#48). -/
instance isIso_toPullback : IsIso (toPullback k₀ K) := by
  have h := isPullback_mapOfAlgebra k₀ K
  have heq : toPullback k₀ K = h.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [toPullback_fst, h.isoPullback_hom_fst]
    · rw [toPullback_snd, h.isoPullback_hom_snd]
  rw [heq]
  infer_instance

end Belyi.P1
