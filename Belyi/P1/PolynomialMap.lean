/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.AffineChart0
import Belyi.P1.Transcendental
import Belyi.P1.ChartTransition
import Belyi.P1.ChartCoord
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# The polynomial self-map of the projective line

For a non-constant polynomial `g : k[X]` of degree `d := g.natDegree`, this file constructs
the finite self-map of `ℙ¹` realizing `[x₀ : x₁] ↦ [g.homogenize d : X₁ᵈ]` — on the affine
chart `D₊(X₁) ≅ 𝔸¹` it is `x ↦ g(x)` (taxis issue #106, statement **B4** of the proof
outline).

## Construction (route: chart gluing over the source cover `{D₊(X₁), D₊(G)}`)

Write `G := g.homogenize d`, homogeneous of degree `d`. The source `ℙ¹` is covered by the two
affine charts `D₊(X₁)` and `D₊(G)`, and — crucially — **each maps into a single target
chart**, so no nested gluing is needed:

* on `D₊(X₁)` (coordinate `x = X₀/X₁`) the map is `x ↦ g(x)`, landing in the target chart
  `D₊(X₁)`: it is `Belyi.P1.point k (Polynomial.aeval (affineCoord k) g)`;
* on `D₊(G)` (coordinate `X₁/X₀`) the map sends `Y₁/Y₀ ↦ X₁ᵈ/G`, landing in the target chart
  `D₊(X₀)`: it is `Belyi.P1.point₀ k (X₁ᵈ/G)`.

The two agree on the overlap `D₊(X₁·G)` because there the target coordinates `g(x) = G/X₁ᵈ`
and `X₁ᵈ/G` are mutually inverse.

## Main definitions

* `Belyi.P1.polynomialSelfMap g : P1 k ⟶ P1 k`.
* `Belyi.P1.polynomialSelfMap_structMap`: it is a morphism over `Spec k`.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open scoped Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (g : k[X])

/-- The homogenization `g.homogenize (g.natDegree)`, a homogeneous polynomial of degree
`g.natDegree` cutting out the graph of `g` at infinity. -/
noncomputable def homogInput : MvPolynomial (Fin 2) k := g.homogenize g.natDegree

lemma homogInput_mem : homogInput k g ∈ P1Grading k g.natDegree :=
  (mem_homogeneousSubmodule _ _).mpr (Polynomial.isHomogeneous_homogenize g)

/-- `X₁ ∣ (G - C(leading coeff)·X₀ᵈ)`: modulo `X₁`, the homogenization is `lc · X₀ᵈ`. -/
lemma X1_dvd_homogInput_sub :
    (X 1 : MvPolynomial (Fin 2) k) ∣
      homogInput k g - C (g.coeff g.natDegree) * X 0 ^ g.natDegree := by
  rw [MvPolynomial.X_dvd_iff_modMonomial_eq_zero]
  ext m
  rw [coeff_zero]
  by_cases hm : Finsupp.single (1 : Fin 2) 1 ≤ m
  · exact MvPolynomial.coeff_modMonomial_of_le _ hm
  · rw [MvPolynomial.coeff_modMonomial_of_not_le _ hm]
    have hm1 : m 1 = 0 := by
      rw [Finsupp.single_le_iff] at hm; omega
    rw [coeff_sub, homogInput, Polynomial.coeff_homogenize, MvPolynomial.coeff_C_mul,
      MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial, hm1, add_zero]
    by_cases hmd : m 0 = g.natDegree
    · have hsm : Finsupp.single (0 : Fin 2) g.natDegree = m := by
        ext i; fin_cases i
        · simpa using hmd.symm
        · simpa using hm1.symm
      rw [if_pos hmd, if_pos hsm, mul_one, hmd, sub_self]
    · have hsm : Finsupp.single (0 : Fin 2) g.natDegree ≠ m := by
        intro h; exact hmd (by rw [← h]; simp)
      rw [if_neg hmd, if_neg hsm, mul_zero, sub_zero]

/-- The two charts `D₊(X₁)` and `D₊(G)` cover the source `ℙ¹`: no homogeneous prime of `Proj`
contains both `X₁` and `G`. -/
lemma X1_notMem_or_homogInput_notMem (hd : 0 < g.natDegree)
    (x : ProjectiveSpectrum (P1Grading k)) :
    (X 1 : MvPolynomial (Fin 2) k) ∉ x.asHomogeneousIdeal ∨
      homogInput k g ∉ x.asHomogeneousIdeal := by
  by_contra h
  rw [not_or, not_not, not_not] at h
  obtain ⟨hX1, hG⟩ := h
  -- from `X₁ ∈ x` and `G ∈ x` deduce `X₀ ∈ x`
  have hg_ne : g ≠ 0 := fun h0 => by simp [h0] at hd
  have hlc : IsUnit (C (g.coeff g.natDegree) : MvPolynomial (Fin 2) k) :=
    IsUnit.map (MvPolynomial.C (σ := Fin 2))
      (isUnit_iff_ne_zero.mpr ((Polynomial.leadingCoeff_ne_zero (p := g)).mpr hg_ne))
  have hCXd : (C (g.coeff g.natDegree) * X 0 ^ g.natDegree : MvPolynomial (Fin 2) k) ∈
      x.asHomogeneousIdeal.toIdeal := by
    obtain ⟨H, hH⟩ := X1_dvd_homogInput_sub k g
    have hrw : (C (g.coeff g.natDegree) * X 0 ^ g.natDegree : MvPolynomial (Fin 2) k) =
        homogInput k g - X 1 * H := by rw [← hH]; ring
    rw [hrw]
    exact Ideal.sub_mem _ hG (Ideal.mul_mem_right _ _ hX1)
  have hXd : (X 0 ^ g.natDegree : MvPolynomial (Fin 2) k) ∈ x.asHomogeneousIdeal.toIdeal := by
    rcases x.isPrime.mem_or_mem hCXd with hc | hc
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ hc hlc) x.isPrime.ne_top
    · exact hc
  have hX0 : (X 0 : MvPolynomial (Fin 2) k) ∈ x.asHomogeneousIdeal.toIdeal :=
    x.isPrime.mem_of_pow_mem _ hXd
  -- then `irrelevant ≤ x`, contradiction
  refine x.not_irrelevant_le ?_
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi p hp
  have hph : p.IsHomogeneous i := (mem_homogeneousSubmodule _ _).mp hp
  rw [p.as_sum]
  refine Ideal.sum_mem _ fun dd hdd => ?_
  have hd0 : dd ≠ 0 := by
    rintro rfl
    exact absurd (hph (mem_support_iff.mp hdd)) (by simpa using hi.ne)
  obtain ⟨j, hj⟩ : ∃ j, dd j ≠ 0 := by
    by_contra hcon
    exact hd0 (by ext j; simpa using not_not.mp (not_exists.mp hcon j))
  have hdvd : (X j : MvPolynomial (Fin 2) k) ∣ monomial dd (coeff dd p) := by
    rw [MvPolynomial.X, MvPolynomial.monomial_dvd_monomial]
    exact ⟨Or.inr (by simpa [Finsupp.single_le_iff] using Nat.one_le_iff_ne_zero.mpr hj),
      one_dvd _⟩
  refine Ideal.mem_of_dvd _ hdvd ?_
  fin_cases j
  · exact hX0
  · exact hX1

/-- The chart ring `(k[X₀,X₁]_G)₀` of `D₊(G)` as a `k`-algebra. -/
noncomputable scoped instance instAlgebraAwayHomogInput :
    Algebra k (Away (P1Grading k) (homogInput k g)) :=
  ((fromZeroRingHom (P1Grading k) (Submonoid.powers (homogInput k g))).comp
    (algebraMap k (P1Grading k 0))).toAlgebra

/-- The target coordinate `X₁ᵈ/G` in the chart ring of `D₊(G)`, i.e. the image of the point
`[x₀:x₁] ↦ [G : X₁ᵈ]` in the target chart `D₊(X₀)` (coordinate `Y₁/Y₀`). -/
noncomputable def selfMapCoordZero : Away (P1Grading k) (homogInput k g) :=
  Away.mk (P1Grading k) (homogInput_mem k g) 1 (X 1 ^ g.natDegree)
    (by simpa using SetLike.pow_mem_graded g.natDegree (X_mem_P1Grading k 1))

/-- The chart map on `D₊(X₁)`: `x ↦ g(x)`, landing in the target chart `D₊(X₁)`. -/
noncomputable def selfMapChartOne : Spec (CommRingCat.of (Away (P1Grading k) (X 1))) ⟶ P1 k :=
  point k (Polynomial.aeval (affineCoord k) g)

/-- The chart map on `D₊(G)`: `Y₁/Y₀ ↦ X₁ᵈ/G`, landing in the target chart `D₊(X₀)`. -/
noncomputable def selfMapChartZero :
    Spec (CommRingCat.of (Away (P1Grading k) (homogInput k g))) ⟶ P1 k :=
  point₀ k (selfMapCoordZero k g)

/-- The homogeneous element cutting out chart `b` of the source cover: `X₁` for `false`,
`G` for `true`. -/
noncomputable def coverElem (b : Bool) : MvPolynomial (Fin 2) k :=
  bif b then homogInput k g else X 1

/-- The degree of `coverElem b`. -/
def coverDeg (b : Bool) : ℕ := bif b then g.natDegree else 1

lemma coverElem_mem (b : Bool) : coverElem k g b ∈ P1Grading k (coverDeg k g b) := by
  cases b
  · exact X_mem_P1Grading k 1
  · exact homogInput_mem k g

lemma coverDeg_pos (hd : 0 < g.natDegree) (b : Bool) : 0 < coverDeg k g b := by
  cases b
  · exact one_pos
  · exact hd

/-- The two charts `D₊(X₁)`, `D₊(G)` cover `ℙ¹`: every point lies in one of them. -/
lemma exists_mem_coverElem (hd : 0 < g.natDegree) (x : Proj (P1Grading k)) :
    ∃ b, x ∈ Proj.basicOpen (P1Grading k) (coverElem k g b) := by
  by_cases hX1 : x ∈ Proj.basicOpen (P1Grading k) (X 1)
  · exact ⟨false, hX1⟩
  · refine ⟨true, ?_⟩
    rw [Proj.mem_basicOpen] at hX1 ⊢
    rw [not_not] at hX1
    exact (X1_notMem_or_homogInput_notMem k g hd x).resolve_left (not_not.mpr hX1)

/-- The affine open cover of the source `ℙ¹` by the two charts `D₊(X₁)` and `D₊(G)`. -/
noncomputable def sourceCover (hd : 0 < g.natDegree) : (Proj (P1Grading k)).AffineOpenCover where
  I₀ := Bool
  X b := CommRingCat.of (Away (P1Grading k) (coverElem k g b))
  f b := Proj.awayι (P1Grading k) (coverElem k g b) (coverElem_mem k g b) (coverDeg_pos k g hd b)
  idx x := (exists_mem_coverElem k g hd x).choose
  covers x := by
    change x ∈ (Proj.awayι (P1Grading k) _ _ _).opensRange
    rw [Proj.opensRange_awayι]
    exact (exists_mem_coverElem k g hd x).choose_spec

/-- The family of chart maps over the source cover, to be glued into `polynomialSelfMap`.
Chart `false` is `x ↦ g(x)` on `D₊(X₁)`; chart `true` is `Y₁/Y₀ ↦ X₁ᵈ/G` on `D₊(G)`. -/
noncomputable def selfMapFamily (hd : 0 < g.natDegree) :
    ∀ b : Bool, ((sourceCover k g hd).openCover.X b) ⟶ P1 k :=
  fun b => Bool.rec (selfMapChartOne k g) (selfMapChartZero k g) b

/-!
### Naturality of the valued points in the coefficient ring

For a `k`-algebra map `φ : R →+* R'` (compatibly with the algebra structures), precomposing a
valued point by `Spec.map φ` reindexes its affine coordinate: `Spec.map φ ≫ point k t =
point k (φ t)` (and likewise for `point₀`). This is what turns the two `awayMap`s coming out of
`Proj.pullbackAwayιIso` into a plain change of coordinate.
-/

section Naturality

variable {k}
variable {R : Type u} [CommRing R] [Algebra k R]
variable {R' : Type u} [CommRing R'] [Algebra k R']

/-- Naturality of the `D₊(X₁)` valued point: `Spec.map φ ≫ point k t = point k (φ t)` for a
ring hom `φ` compatible with the `k`-algebra structures. -/
lemma SpecMap_comp_point (φ : R →+* R')
    (hφ : ∀ c : k, φ (algebraMap k R c) = algebraMap k R' c) (t : R) :
    Spec.map (CommRingCat.ofHom φ) ≫ point k t = point k (φ t) := by
  have key : awayEval k (φ t) = φ.comp (awayEval k t) := by
    refine RingHom.ext fun z => ?_
    obtain ⟨n, a, ha, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (P1Grading k) (X_mem_P1Grading k 1) z
    have hv : (![φ t, 1] : Fin 2 → R') = fun i => φ (![t, 1] i) := by
      funext i; fin_cases i <;> simp
    rw [awayEval_mk, RingHom.comp_apply, awayEval_mk, map_aeval,
      show φ.comp (algebraMap k R) = algebraMap k R' from RingHom.ext hφ, aeval_eq_eval₂Hom, hv]
  simp only [point]
  rw [key, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/-- Naturality of the `D₊(X₀)` valued point: `Spec.map φ ≫ point₀ k s = point₀ k (φ s)`. -/
lemma SpecMap_comp_point₀ (φ : R →+* R')
    (hφ : ∀ c : k, φ (algebraMap k R c) = algebraMap k R' c) (s : R) :
    Spec.map (CommRingCat.ofHom φ) ≫ point₀ k s = point₀ k (φ s) := by
  have key : awayEval₀ k (φ s) = φ.comp (awayEval₀ k s) := by
    refine RingHom.ext fun z => ?_
    obtain ⟨n, a, ha, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (P1Grading k) (X_mem_P1Grading k 0) z
    have hv : (![1, φ s] : Fin 2 → R') = fun i => φ (![1, s] i) := by
      funext i; fin_cases i <;> simp
    rw [awayEval₀_mk, RingHom.comp_apply, awayEval₀_mk, map_aeval,
      show φ.comp (algebraMap k R) = algebraMap k R' from RingHom.ext hφ, aeval_eq_eval₂Hom, hv]
  simp only [point₀]
  rw [key, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

end Naturality

/-- The overlap-chart ring `(k[X₀,X₁]_{X₁·G})₀` of `D₊(X₁·G)` as a `k`-algebra. -/
noncomputable scoped instance instAlgebraAwayMul :
    Algebra k (Away (P1Grading k) (X 1 * homogInput k g)) :=
  ((fromZeroRingHom (P1Grading k) (Submonoid.powers (X 1 * homogInput k g))).comp
    (algebraMap k (P1Grading k 0))).toAlgebra

/-- The dehomogenisation identity `g(X₀/X₁) = G/X₁ᵈ` in the chart ring of `D₊(X₁)`. -/
lemma aeval_affineCoord_eq :
    Polynomial.aeval (affineCoord k) g =
      Away.mk (P1Grading k) (X_mem_P1Grading k 1) g.natDegree (homogInput k g)
        (by simpa using homogInput_mem k g) := by
  apply (awayChartEquivOne k).injective
  rw [← Polynomial.aeval_algHom_apply, awayChartEquivOne_affineCoord, Polynomial.aeval_X_left_apply,
    awayChartEquivOne, AlgEquiv.ofBijective_apply]
  change g = awayEval k (Polynomial.X)
    (Away.mk (P1Grading k) (X_mem_P1Grading k 1) g.natDegree (homogInput k g) _)
  rw [awayEval_mk, homogInput]
  exact (Polynomial.aeval_homogenize_X_one g le_rfl).symm

/-- The two chart maps of `polynomialSelfMap` agree on the overlap `D₊(X₁·G)`: the target
coordinates `g(x) = G/X₁ᵈ` and `X₁ᵈ/G` are mutually inverse. -/
lemma selfMapChart_compat (hd : 0 < g.natDegree) :
    Limits.pullback.fst
        (Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos)
        (Proj.awayι (P1Grading k) (homogInput k g) (homogInput_mem k g) hd)
      ≫ selfMapChartOne k g =
    Limits.pullback.snd _ _ ≫ selfMapChartZero k g := by
  rw [← cancel_epi (Proj.pullbackAwayιIso (P1Grading k) (X_mem_P1Grading k 1) one_pos
    (homogInput_mem k g) hd (rfl : (X 1 * homogInput k g) = X 1 * homogInput k g)).inv]
  rw [← Category.assoc, ← Category.assoc, Proj.pullbackAwayιIso_inv_fst,
    Proj.pullbackAwayιIso_inv_snd, selfMapChartOne, selfMapChartZero]
  -- the two `awayMap`s are `k`-algebra maps into the overlap ring
  have hφ₁ : ∀ c : k, HomogeneousLocalization.awayMap (P1Grading k) (homogInput_mem k g)
        (rfl : (X 1 * homogInput k g) = X 1 * homogInput k g)
        (algebraMap k (Away (P1Grading k) (X 1)) c) =
      algebraMap k (Away (P1Grading k) (X 1 * homogInput k g)) c := fun c => by
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      RingHom.comp_apply]
    exact HomogeneousLocalization.awayMap_fromZeroRingHom (P1Grading k) (homogInput_mem k g) rfl _
  have hφ₀ : ∀ c : k, HomogeneousLocalization.awayMap (P1Grading k) (X_mem_P1Grading k 1)
        (Eq.trans (rfl : (X 1 * homogInput k g) = X 1 * homogInput k g)
          (mul_comm (X 1) (homogInput k g)))
        (algebraMap k (Away (P1Grading k) (homogInput k g)) c) =
      algebraMap k (Away (P1Grading k) (X 1 * homogInput k g)) c := fun c => by
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
      RingHom.comp_apply]
    exact HomogeneousLocalization.awayMap_fromZeroRingHom (P1Grading k) (X_mem_P1Grading k 1) _ _
  rw [SpecMap_comp_point _ hφ₁, SpecMap_comp_point₀ _ hφ₀]
  -- reduce to the chart-transition lemma with reciprocal coordinates
  refine point_eq_point₀ _ _ ?_
  rw [aeval_affineCoord_eq, selfMapCoordZero]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, mul_one]
  ring

/-- The overlap compatibility of the chart-map family over the source cover, packaging both
diagonal cases (`Proj.awayι` is a mono) and the off-diagonal cases (`selfMapChart_compat` and
its `pullbackSymmetry` mirror). -/
lemma selfMapFamily_compat (hd : 0 < g.natDegree) (b b' : Bool) :
    Limits.pullback.fst ((sourceCover k g hd).openCover.f b)
        ((sourceCover k g hd).openCover.f b') ≫ selfMapFamily k g hd b =
      Limits.pullback.snd _ _ ≫ selfMapFamily k g hd b' := by
  cases b <;> cases b'
  · exact congrArg (· ≫ _) (Limits.fst_eq_snd_of_mono_eq _)
  · exact selfMapChart_compat k g hd
  · rw [← cancel_epi (Limits.pullbackSymmetry _ _).hom, ← Category.assoc, ← Category.assoc,
      Limits.pullbackSymmetry_hom_comp_fst, Limits.pullbackSymmetry_hom_comp_snd]
    exact (selfMapChart_compat k g hd).symm
  · exact congrArg (· ≫ _) (Limits.fst_eq_snd_of_mono_eq _)

/-- **The polynomial self-map of `ℙ¹`.** For a non-constant `g : k[X]` of degree `d`, the finite
self-map `[x₀ : x₁] ↦ [g.homogenize d : X₁ᵈ]` of `ℙ¹`, obtained by gluing the two chart maps
`x ↦ g(x)` on `D₊(X₁)` and `Y₁/Y₀ ↦ X₁ᵈ/G` on `D₊(G)` over the source cover. -/
noncomputable def polynomialSelfMap (hd : 0 < g.natDegree) : P1 k ⟶ P1 k :=
  (sourceCover k g hd).openCover.glueMorphisms (selfMapFamily k g hd) (selfMapFamily_compat k g hd)

@[reassoc]
lemma ι_polynomialSelfMap (hd : 0 < g.natDegree) (b : Bool) :
    (sourceCover k g hd).openCover.f b ≫ polynomialSelfMap k g hd = selfMapFamily k g hd b :=
  (sourceCover k g hd).openCover.ι_glueMorphisms _ _ b

/-- A chart inclusion followed by the structure morphism is the structure map of the chart ring:
`awayι f' ≫ structMap = Spec.map (k → 𝒜₀ → (k[X₀,X₁]_{f'})₀)`. -/
lemma awayι_comp_structMap {f' : MvPolynomial (Fin 2) k} {m : ℕ} (hf' : f' ∈ P1Grading k m)
    (hm : 0 < m) :
    Proj.awayι (P1Grading k) f' hf' hm ≫ structMap k =
      Spec.map (CommRingCat.ofHom ((fromZeroRingHom (P1Grading k) (Submonoid.powers f')).comp
        (algebraMap k (P1Grading k 0)))) := by
  change Proj.awayι (P1Grading k) f' hf' hm ≫ Proj.toSpecZero (P1Grading k) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (P1Grading k 0))) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The polynomial self-map is a morphism over `Spec k`. -/
lemma polynomialSelfMap_structMap (hd : 0 < g.natDegree) :
    polynomialSelfMap k g hd ≫ structMap k = structMap k := by
  refine (sourceCover k g hd).openCover.hom_ext _ _ fun b => ?_
  rw [ι_polynomialSelfMap_assoc, Scheme.AffineOpenCover.openCover_f]
  cases b
  · change selfMapChartOne k g ≫ structMap k =
      Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos ≫ structMap k
    rw [selfMapChartOne, point_structMap, awayι_comp_structMap]; rfl
  · change selfMapChartZero k g ≫ structMap k =
      Proj.awayι (P1Grading k) (homogInput k g) (homogInput_mem k g) hd ≫ structMap k
    rw [selfMapChartZero, point₀_structMap, awayι_comp_structMap]; rfl

/-!
### Local finite presentation

Each chart map is `Spec.map (awayEval …) ≫ awayι`; the `awayι` is an open immersion (hence
locally of finite presentation) and `awayEval` is a map from the Noetherian chart ring
`(k[X₀,X₁]_{X₁})₀ ≅ k[T]` which is of finite type — over a Noetherian source finite type is
finite presentation. Locality at source then assembles the two charts.
-/

section FinitePresentation

variable {k}
variable {R : Type u} [CommRing R] [Algebra k R]

/-- Any chart inclusion `awayι f'` is locally of finite presentation (it is an open immersion);
stated standalone so the instance is available without polluting instance search in the
finite-presentation proofs below. -/
lemma locallyOfFinitePresentation_awayι {f' : MvPolynomial (Fin 2) k} {m : ℕ}
    (hf' : f' ∈ P1Grading k m) (hm : 0 < m) :
    LocallyOfFinitePresentation (Proj.awayι (P1Grading k) f' hf' hm) :=
  inferInstance

/-- The chart ring of `D₊(X₁)` is Noetherian (it is `k[T]`). -/
instance : IsNoetherianRing (Away (P1Grading k) (X 1 : MvPolynomial (Fin 2) k)) :=
  Algebra.FiniteType.isNoetherianRing k _ (h := finiteType_away k)

/-- The chart ring of `D₊(X₀)` is Noetherian (it is `k[T]`). -/
lemma isNoetherianRing_awayZero :
    IsNoetherianRing (Away (P1Grading k) (X 0 : MvPolynomial (Fin 2) k)) := by
  have h1 : (fromZeroRingHom (P1Grading k)
      (Submonoid.powers (X 0 : MvPolynomial (Fin 2) k))).FiniteType :=
    HomogeneousLocalization.Away.finiteType (X 0) 1 (X_mem_P1Grading k 0)
  have h2 : (algebraMap k (P1Grading k 0)).FiniteType :=
    RingHom.FiniteType.of_surjective _ (gradeZeroEquiv k).surjective
  exact Algebra.FiniteType.isNoetherianRing k _ (h := h1.comp h2)

/-- The `D₊(X₁)` valued point is locally of finite presentation whenever its coefficient ring is
of finite type over `k`. -/
lemma locallyOfFinitePresentation_point (t : R) [Algebra.FiniteType k R] :
    LocallyOfFinitePresentation (point k t) := by
  have hft : RingHom.FiniteType (awayEval k t) := by
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k (Away (P1Grading k) (X 1)))
    have heq : (awayEval k t).comp (algebraMap k (Away (P1Grading k) (X 1))) = algebraMap k R := by
      ext c; exact (awayEvalₐ k t).commutes c
    rw [heq, RingHom.finiteType_algebraMap]
    infer_instance
  haveI : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (awayEval k t))) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff, CommRingCat.hom_ofHom]
    exact RingHom.FinitePresentation.of_finiteType.mp hft
  rw [point]
  exact locallyOfFinitePresentation_comp _ _
    (hg := locallyOfFinitePresentation_awayι (X_mem_P1Grading k 1) one_pos)

/-- The `D₊(X₀)` valued point is locally of finite presentation whenever its coefficient ring is
of finite type over `k`. -/
lemma locallyOfFinitePresentation_point₀ (s : R) [Algebra.FiniteType k R] :
    LocallyOfFinitePresentation (point₀ k s) := by
  haveI := isNoetherianRing_awayZero (k := k)
  have hft : RingHom.FiniteType (awayEval₀ k s) := by
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k (Away (P1Grading k) (X 0)))
    have heq : (awayEval₀ k s).comp (algebraMap k (Away (P1Grading k) (X 0))) = algebraMap k R := by
      ext c
      have h := awayEval₀_fromZeroRingHom k s (algebraMap k (P1Grading k 0) c)
      simp only [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq, aeval_C] at h
      exact h
    rw [heq, RingHom.finiteType_algebraMap]
    infer_instance
  haveI : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (awayEval₀ k s))) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff, CommRingCat.hom_ofHom]
    exact RingHom.FinitePresentation.of_finiteType.mp hft
  rw [point₀]
  exact locallyOfFinitePresentation_comp _ _
    (hg := locallyOfFinitePresentation_awayι (X_mem_P1Grading k 0) one_pos)

end FinitePresentation

/-- The chart ring `(k[X₀,X₁]_G)₀` of `D₊(G)` is of finite type over `k`. -/
lemma finiteType_awayHomogInput : Algebra.FiniteType k (Away (P1Grading k) (homogInput k g)) := by
  have h1 : (fromZeroRingHom (P1Grading k)
      (Submonoid.powers (homogInput k g))).FiniteType :=
    HomogeneousLocalization.Away.finiteType (homogInput k g) g.natDegree (homogInput_mem k g)
  have h2 : (algebraMap k (P1Grading k 0)).FiniteType :=
    RingHom.FiniteType.of_surjective _ (gradeZeroEquiv k).surjective
  exact h1.comp h2

set_option backward.isDefEq.respectTransparency false in
/-- **The polynomial self-map is locally of finite presentation.** This is the property consumed
by the downstream branch-locus / `IsBelyiMap` API (issues #107, #108). -/
lemma locallyOfFinitePresentation_polynomialSelfMap (hd : 0 < g.natDegree) :
    LocallyOfFinitePresentation (polynomialSelfMap k g hd) := by
  refine IsZariskiLocalAtSource.of_openCover (sourceCover k g hd).openCover fun b => ?_
  rw [ι_polynomialSelfMap]
  cases b
  · haveI := finiteType_away k
    exact locallyOfFinitePresentation_point (Polynomial.aeval (affineCoord k) g)
  · haveI := finiteType_awayHomogInput k g
    exact locallyOfFinitePresentation_point₀ (selfMapCoordZero k g)

end Belyi.P1
