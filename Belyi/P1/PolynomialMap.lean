/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.AffineChart0
import Belyi.P1.Transcendental
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.MvPolynomial.Division

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
### Remaining step: gluing the two chart maps

`polynomialSelfMap g` is `(sourceCover k g hd).openCover.glueMorphisms (selfMapFamily k g hd) h`,
where `h` is the overlap compatibility
`∀ b b', pullback.fst (𝒰.f b) (𝒰.f b') ≫ selfMapFamily b = pullback.snd _ _ ≫ selfMapFamily b'`.

* The diagonal cases `b = b'` are `CategoryTheory.Limits.pullback.fst_eq_snd_of_mono_eq`
  (`Proj.awayι` is a mono).
* The off-diagonal `(false, true)` reduces, via `Proj.pullbackAwayιIso` for `f = X₁`, `g = G`,
  `x = X₁·G` and the naturality `h ∘ awayEval k t = awayEval k (h t)` of the valued points, to
  the clean statement
  ```
  point k u = point₀ k v        (u v : Away (P1Grading k) (X 1 * homogInput k g), u * v = 1)
  ```
  with `u = G/X₁ᵈ = aeval (affineCoord k) g` (dehomogenisation, `aeval_homogenize_X_one`) and
  `v = X₁ᵈ/G = selfMapCoordZero`, so `u * v = 1` by the reciprocity of the two target-chart
  coordinates. The equality `point k u = point₀ k v` for `u * v = 1` (`u` a unit) is a reusable
  chart-transition lemma: both sides factor through `Proj.awayι (X₀·X₁)` via
  `Proj.SpecMap_awayMap_awayι`, and the two induced `HomogeneousLocalization.Away` ring maps
  agree (`awayLift (aeval ![u,1])` on the `D₊(X₀X₁)` chart).
* `(true, false)` is the mirror via `pullbackSymmetry`.

Then `polynomialSelfMap g ≫ structMap k = structMap k` follows chartwise from `point_structMap`
/ `point₀_structMap` + `Cover.hom_ext`, and `LocallyOfFinitePresentation` chartwise via
`IsLocalAtSource`.
-/

end Belyi.P1
