/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.ClosedPoints
import Belyi.P1.MarkedPointMatching
import Belyi.P1.AffineChartBaseChange

/-!
# The value → marked-point dictionary for the affine chart

The branch-locus bound of the polynomial self-map (`Belyi.P1.branch_polynomialSelfMap_subset`,
`Belyi/P1/PolynomialBranchLocus.lean`) phrases its finite branch points as affine `k`-points
`(point k v).base (closedPoint (of k))` — the image of the closed point of `Spec k` under the
affine-chart valued point `point k v : Spec k ⟶ ℙ¹_k` (`Belyi/P1/AffineChart.lean`) with
coordinate `v`.  The marked points `Belyi.P1.zero`, `one`, `infty` (`Belyi/P1/Points.lean`),
however, are the explicit homogeneous primes `(X₀)`, `(X₀ - X₁)`, `(X₁)` cut out by `mkPoint`.

This file identifies the two constructions at the values `0` and `1`, the input needed to turn
`branch_polynomialSelfMap_subset` into `Branch (polynomialSelfMap g) ⊆ markedPoints k` (the `hbg`
hypothesis of `Belyi.P1.isBelyiMap_comp_polynomialSelfMap`) once the reductions guarantee every
critical value lies in `{0, 1}`.  This is a piece of the forward direction of Belyi's theorem
(B8, taxis #189, parent #51).

## Main results

* `Belyi.P1.mem_affinePoint_iff`: a homogeneous form lies in the homogeneous ideal of the affine
  point `[a : 1]` iff it vanishes at `(a, 1)` (`aeval ![a, 1]`).
* `Belyi.P1.point_base_eq_zero`: `(point k 0).base (closedPoint (of k)) = zero k`.
* `Belyi.P1.point_base_eq_one`: `(point k 1).base (closedPoint (of k)) = one k`.

The membership characterization goes through the chart-ring computation of
`Belyi/P1/ClosedPoints.lean` (the affine point is `awayι` of `ker (awayEval k a)`) together with
`awayEval_mk`; the two identifications then reuse the divisibility skeleton of
`Belyi/P1/MarkedPointMatching.lean` (`eq_span_of_forall_dvd`, `dvd_of_isHomog_mem`, and the
`shear` argument for `X₀ - X₁`).
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open scoped Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- **Membership in the ideal of an affine point.** For `a : k` and a homogeneous form
`f ∈ k[X₀, X₁]` of degree `n`, `f` lies in the homogeneous ideal of the affine point
`[a : 1] = (point k a).base (closedPoint)` iff `f(a, 1) = 0`.  The affine point is `awayι` of the
prime `ker (awayEval k a)` of the chart ring `D₊(X₁)`, and on the fraction `f / X₁ⁿ` the map
`awayEval k a` returns `aeval ![a, 1] f` (`awayEval_mk`). -/
lemma mem_affinePoint_iff {a : k} {n : ℕ} {f : MvPolynomial (Fin 2) k} (hf : f ∈ P1Grading k n) :
    f ∈ ((point k a).base
        (IsLocalRing.closedPoint (CommRingCat.of k))).asHomogeneousIdeal.toIdeal
      ↔ aeval ![a, 1] f = 0 := by
  have hf' : f ∈ P1Grading k (n • 1) := by simpa using hf
  -- The affine point `[a : 1]` is `awayι` applied to `comap (awayEval k a)` of the closed point.
  have hpt : (point k a).base (IsLocalRing.closedPoint (CommRingCat.of k))
      = (Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos).base
          ((Spec.map (CommRingCat.ofHom (awayEval k a))).base
            (IsLocalRing.closedPoint (CommRingCat.of k))) := rfl
  -- the prime of the chart ring cut out by the closed point is `ker (awayEval k a)`.
  have hyker : ((Spec.map (CommRingCat.ofHom (awayEval k a))).base
        (IsLocalRing.closedPoint (CommRingCat.of k)) :
        PrimeSpectrum (Away (P1Grading k) (X 1))).asIdeal = RingHom.ker (awayEval k a) := by
    have hbot : (IsLocalRing.closedPoint (CommRingCat.of k)).asIdeal = ⊥ :=
      IsLocalRing.maximalIdeal_eq_bot
    rw [show ((Spec.map (CommRingCat.ofHom (awayEval k a))).base
          (IsLocalRing.closedPoint (CommRingCat.of k)) :
          PrimeSpectrum (Away (P1Grading k) (X 1))) =
        PrimeSpectrum.comap (awayEval k a) (IsLocalRing.closedPoint (CommRingCat.of k)) from rfl,
      PrimeSpectrum.comap_asIdeal, hbot]
    rfl
  rw [hpt, HomogeneousIdeal.mem_iff,
    ← Proj.awayMk_mem_iff_mem_awayι (P1Grading k) (X_mem_P1Grading k 1) one_pos _ n f hf',
    hyker, RingHom.mem_ker, awayEval_mk]

/-- **The affine point `[0 : 1]` is the marked point `0`.** -/
lemma point_base_eq_zero :
    (point k 0).base (IsLocalRing.closedPoint (CommRingCat.of k)) = zero k := by
  set x := (point k 0).base (IsLocalRing.closedPoint (CommRingCat.of k)) with hx
  have hX0 : (X 0 : MvPolynomial (Fin 2) k) ∈ x.asHomogeneousIdeal.toIdeal := by
    rw [hx, mem_affinePoint_iff k (X_mem_P1Grading k 0)]; simp
  have hX1 : (X 1 : MvPolynomial (Fin 2) k) ∉ x.asHomogeneousIdeal.toIdeal := by
    rw [hx, mem_affinePoint_iff k (X_mem_P1Grading k 1)]; simp
  have hspan : x.asHomogeneousIdeal.toIdeal = Ideal.span {(X 0 : MvPolynomial (Fin 2) k)} :=
    eq_span_of_forall_dvd x.asHomogeneousIdeal.isHomogeneous (isHomogeneous_X k 0) hX0
      (fun n w hw hwJ => dvd_of_isHomog_mem x.isPrime 0 1 (by decide) hX0 hX1 hw hwJ)
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  rw [hspan, zero, mkPoint_asIdeal]

/-- **The affine point `[1 : 1]` is the marked point `1`.** The linear form is `X₀ - X₁`; the
divisibility skeleton is reduced to the `X₀` case by the `shear` automorphism
(`shear (X₀ - X₁) = X₀`), exactly as in `mapOfAlgebra_base_eq_one`. -/
lemma point_base_eq_one :
    (point k 1).base (IsLocalRing.closedPoint (CommRingCat.of k)) = one k := by
  set x := (point k 1).base (IsLocalRing.closedPoint (CommRingCat.of k)) with hx
  have hℓdeg : (X 0 - X 1 : MvPolynomial (Fin 2) k) ∈ P1Grading k 1 :=
    (mem_homogeneousSubmodule _ _).mpr ((isHomogeneous_X k 0).sub (isHomogeneous_X k 1))
  have hℓ : (X 0 - X 1 : MvPolynomial (Fin 2) k) ∈ x.asHomogeneousIdeal.toIdeal := by
    rw [hx, mem_affinePoint_iff k hℓdeg]; simp
  have hX1 : (X 1 : MvPolynomial (Fin 2) k) ∉ x.asHomogeneousIdeal.toIdeal := by
    rw [hx, mem_affinePoint_iff k (X_mem_P1Grading k 1)]; simp
  -- divisibility skeleton for `X₀ - X₁` via `shear`
  have hdvd : ∀ (n : ℕ) (hh : MvPolynomial (Fin 2) k), hh.IsHomogeneous n →
      hh ∈ x.asHomogeneousIdeal.toIdeal → (X 0 - X 1 : MvPolynomial (Fin 2) k) ∣ hh := by
    intro n w hw hwJ
    have hsh : (shear k w).IsHomogeneous n := by
      have h1 : (shear k w).IsHomogeneous (1 * n) :=
        hw.aeval ![X 0 + X 1, X 1] (fun t => by
          fin_cases t
          · exact (isHomogeneous_X k 0).add (isHomogeneous_X k 1)
          · exact isHomogeneous_X k 1)
      rwa [one_mul] at h1
    set c := (shear k w).coeff (Finsupp.single 1 n) with hc
    obtain ⟨g, hg⟩ := X_dvd_sub hsh 0 1 (by decide)
    rw [← hc] at hg
    have hg' : w - C c * X 1 ^ n = (X 0 - X 1) * shearInv k g := by
      have hcong := congrArg (shearInv k) hg
      simp only [map_sub, map_mul, map_pow, shearInv_shear] at hcong
      rw [show shearInv k (X 1) = X 1 by simp [shearInv],
        show shearInv k (X 0) = X 0 - X 1 by simp [shearInv],
        show shearInv k (C c) = C c by simp [shearInv, algebraMap_eq]] at hcong
      exact hcong
    have hmem : C c * X 1 ^ n ∈ x.asHomogeneousIdeal.toIdeal := by
      have hrw : C c * X 1 ^ n = w - (X 0 - X 1) * shearInv k g := by rw [← hg']; ring
      rw [hrw]
      exact x.asHomogeneousIdeal.toIdeal.sub_mem hwJ
        (x.asHomogeneousIdeal.toIdeal.mul_mem_right _ hℓ)
    have hc0 : c = 0 := by
      by_contra hcne
      have hunit : IsUnit (C c : MvPolynomial (Fin 2) k) :=
        (isUnit_iff_ne_zero.mpr hcne).map (C : k →+* MvPolynomial (Fin 2) k)
      rcases x.isPrime.mem_or_mem hmem with hCc | hXpow
      · exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hCc hunit)
      · exact hX1 (x.isPrime.mem_of_pow_mem n hXpow)
    rw [hc0, map_zero, zero_mul, sub_zero] at hg'
    exact ⟨shearInv k g, hg'⟩
  have hspan : x.asHomogeneousIdeal.toIdeal
      = Ideal.span {(X 0 - X 1 : MvPolynomial (Fin 2) k)} :=
    eq_span_of_forall_dvd x.asHomogeneousIdeal.isHomogeneous
      ((isHomogeneous_X k 0).sub (isHomogeneous_X k 1)) hℓ hdvd
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  rw [hspan, one, mkPoint_asIdeal]

end Belyi.P1
