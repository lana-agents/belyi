/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.PolynomialBranchLocus
import Belyi.Polynomial.CritVal

/-!
# B4c (marked branch locus): the critical-value ↔ marked-point dictionary

Second glue piece of the forward direction (taxis issue #186, parent #51).  This file joins the
two currently-disjoint halves of the repository — the field-value algebra of `Belyi/Polynomial/*`
and the scheme geometry of `Belyi/P1/*` — by upgrading the merged branch-locus inclusion
`Belyi.P1.branch_polynomialSelfMap_subset` into a statement about `Belyi.markedPoints`.

## The dictionary

The affine `k`-point `[a : 1]` (`point k a` evaluated at the closed point of `Spec k`) is the
marked point `0`/`1` exactly when `a = 0`/`a = 1`:

* `Belyi.P1.point_closedPoint_zero_eq`: `point k 0 (closedPoint) = P1.zero k`;
* `Belyi.P1.point_closedPoint_one_eq`: `point k 1 (closedPoint) = P1.one k`.

Both are homogeneous-prime computations mirroring the reverse marked-point matching of
`Belyi/P1/MarkedPointMatching.lean` (issue #164): the homogeneous ideal of `[a : 1]` contains a
homogeneous polynomial iff it vanishes at `(a, 1)` (`Belyi.P1.mem_point_closedPoint_iff`), which
pins the ideal down to `span {X₀}` resp. `span {X₀ - X₁}` via `eq_span_of_forall_dvd`.

## Main results

* `Belyi.P1.branch_polynomialSelfMap_subset_markedPoints`: for `g : k[X]` all of whose critical
  values lie in `{0, 1}`, `Branch (polynomialSelfMap g) ⊆ markedPoints k`.
* `Belyi.P1.branch_map_polynomialSelfMap_subset_markedPoints`: the same conclusion phrased for the
  base change `g.map (algebraMap ℚ k)` of a rational polynomial `g : ℚ[X]` whose `Belyi.critVal`
  lies in `{0, 1}` — the exact output shape of the combined reduction (issue #185) that the B8
  assembly (issue #188) consumes.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization ProjectiveSpectrum
open scoped Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- **Membership criterion for the homogeneous ideal of the affine `k`-point `[a : 1]`.** A
homogeneous polynomial of degree `n` lies in the homogeneous ideal of `point k a (closedPoint)`
iff it vanishes at the vector `(a, 1)`.  The point lies in the chart `D₊(X₁)`, where the ideal is
the kernel of `awayEval k a` (evaluation `X₀/X₁ ↦ a`); membership of `Away.mk … n h` reduces to
`aeval ![a, 1] h = 0` via `awayEval_mk` and `IsLocalRing.maximalIdeal_eq_bot`. -/
lemma mem_point_closedPoint_iff (a : k) {n : ℕ} (h : MvPolynomial (Fin 2) k)
    (hh : h ∈ P1Grading k (n • 1)) :
    h ∈ ((point k (a : k)).base
        (IsLocalRing.closedPoint (CommRingCat.of k))).asHomogeneousIdeal.toIdeal
      ↔ aeval ![a, 1] h = 0 := by
  have hpt : (point k (a : k)).base (IsLocalRing.closedPoint (CommRingCat.of k))
      = (Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos).base
          ((Spec.map (CommRingCat.ofHom (awayEval k a))).base
            (IsLocalRing.closedPoint (CommRingCat.of k))) := by
    rw [point, Scheme.Hom.comp_apply]
    rfl
  have hbot : (IsLocalRing.closedPoint (CommRingCat.of k)).asIdeal = ⊥ :=
    IsLocalRing.maximalIdeal_eq_bot
  rw [HomogeneousIdeal.mem_iff, hpt,
    ← Proj.awayMk_mem_iff_mem_awayι (P1Grading k) (X_mem_P1Grading k 1) one_pos _ n h hh,
    show ((Spec.map (CommRingCat.ofHom (awayEval k a))).base
          (IsLocalRing.closedPoint (CommRingCat.of k)) :
          PrimeSpectrum (Away (P1Grading k) (X 1))) =
        PrimeSpectrum.comap (awayEval k a) (IsLocalRing.closedPoint (CommRingCat.of k)) from rfl,
    PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, awayEval_mk, hbot, Ideal.mem_bot]

/-- **The affine `k`-point `[0 : 1]` is the marked point `0`.** -/
lemma point_closedPoint_zero_eq :
    (point k (0 : k)).base (IsLocalRing.closedPoint (CommRingCat.of k)) = zero k := by
  set y := (point k (0 : k)).base (IsLocalRing.closedPoint (CommRingCat.of k)) with hy
  have hX0 : (X 0 : MvPolynomial (Fin 2) k) ∈ y.asHomogeneousIdeal.toIdeal := by
    rw [hy, mem_point_closedPoint_iff k 0 (X 0) (by simpa using X_mem_P1Grading k 0)]
    simp
  have hX1 : (X 1 : MvPolynomial (Fin 2) k) ∉ y.asHomogeneousIdeal.toIdeal := by
    rw [hy, mem_point_closedPoint_iff k 0 (X 1) (by simpa using X_mem_P1Grading k 1)]
    simp
  have hspan : y.asHomogeneousIdeal.toIdeal = Ideal.span {(X 0 : MvPolynomial (Fin 2) k)} :=
    eq_span_of_forall_dvd y.asHomogeneousIdeal.isHomogeneous (isHomogeneous_X k 0) hX0
      (fun n w hw hwJ => dvd_of_isHomog_mem y.isPrime 0 1 (by decide) hX0 hX1 hw hwJ)
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  rw [hspan, zero, mkPoint_asIdeal]

/-- **The affine `k`-point `[1 : 1]` is the marked point `1`.** The linear form is `X₀ - X₁`; the
divisibility skeleton is reduced to the `X₀` case by the `shear` automorphism
(`shear (X₀ - X₁) = X₀`), exactly as in `Belyi.P1.mapOfAlgebra_base_eq_one`. -/
lemma point_closedPoint_one_eq :
    (point k (1 : k)).base (IsLocalRing.closedPoint (CommRingCat.of k)) = one k := by
  set y := (point k (1 : k)).base (IsLocalRing.closedPoint (CommRingCat.of k)) with hy
  have hℓ : (X 0 - X 1 : MvPolynomial (Fin 2) k) ∈ y.asHomogeneousIdeal.toIdeal := by
    rw [hy, mem_point_closedPoint_iff k 1 (X 0 - X 1)
      (by simpa using (isHomogeneous_X k 0).sub (isHomogeneous_X k 1))]
    simp
  have hX1 : (X 1 : MvPolynomial (Fin 2) k) ∉ y.asHomogeneousIdeal.toIdeal := by
    rw [hy, mem_point_closedPoint_iff k 1 (X 1) (by simpa using X_mem_P1Grading k 1)]
    simp
  -- divisibility skeleton for `X₀ - X₁` via `shear`
  have hdvd : ∀ (n : ℕ) (w : MvPolynomial (Fin 2) k), w.IsHomogeneous n →
      w ∈ y.asHomogeneousIdeal.toIdeal → (X 0 - X 1 : MvPolynomial (Fin 2) k) ∣ w := by
    intro n w hw hwJ
    have hsh : (shear k w).IsHomogeneous n := by
      have h1 : (shear k w).IsHomogeneous (1 * n) :=
        hw.aeval ![X 0 + X 1, X 1] (fun t => by
          fin_cases t
          · exact (isHomogeneous_X k 0).add (isHomogeneous_X k 1)
          · exact isHomogeneous_X k 1)
      rwa [one_mul] at h1
    set c := (shear k w).coeff (Finsupp.single 1 n) with hc
    obtain ⟨d, hd⟩ := X_dvd_sub hsh 0 1 (by decide)
    rw [← hc] at hd
    have hg' : w - C c * X 1 ^ n = (X 0 - X 1) * shearInv k d := by
      have hcong := congrArg (shearInv k) hd
      simp only [map_sub, map_mul, map_pow, shearInv_shear] at hcong
      rw [show shearInv k (X 1) = X 1 by simp [shearInv],
        show shearInv k (X 0) = X 0 - X 1 by simp [shearInv],
        show shearInv k (C c) = C c by simp [shearInv, algebraMap_eq]] at hcong
      exact hcong
    have hmem : C c * X 1 ^ n ∈ y.asHomogeneousIdeal.toIdeal := by
      have hrw : C c * X 1 ^ n = w - (X 0 - X 1) * shearInv k d := by rw [← hg']; ring
      rw [hrw]
      exact y.asHomogeneousIdeal.toIdeal.sub_mem hwJ
        (y.asHomogeneousIdeal.toIdeal.mul_mem_right _ hℓ)
    have hc0 : c = 0 := by
      by_contra hcne
      have hunit : IsUnit (C c : MvPolynomial (Fin 2) k) :=
        (isUnit_iff_ne_zero.mpr hcne).map (C : k →+* MvPolynomial (Fin 2) k)
      rcases y.isPrime.mem_or_mem hmem with hCc | hXpow
      · exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hCc hunit)
      · exact hX1 (y.isPrime.mem_of_pow_mem n hXpow)
    rw [hc0, map_zero, zero_mul, sub_zero] at hg'
    exact ⟨shearInv k d, hg'⟩
  have hspan : y.asHomogeneousIdeal.toIdeal = Ideal.span {(X 0 - X 1 : MvPolynomial (Fin 2) k)} :=
    eq_span_of_forall_dvd y.asHomogeneousIdeal.isHomogeneous
      ((isHomogeneous_X k 0).sub (isHomogeneous_X k 1)) hℓ hdvd
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  rw [hspan, one, mkPoint_asIdeal]

variable (g : k[X]) (hd : 0 < g.natDegree)

noncomputable local instance instLOFP_polynomialSelfMap'' :
    LocallyOfFinitePresentation (polynomialSelfMap k g hd) :=
  locallyOfFinitePresentation_polynomialSelfMap k g hd

/-- **B4c (marked branch locus).** Over an algebraically closed field of characteristic zero, if
every critical value of a non-constant `g : k[X]` lies in `{0, 1}` — i.e. `g'(a) = 0` forces
`g(a) ∈ {0, 1}` — then the branch locus of the polynomial self-map `x ↦ g(x)` is contained in the
three marked points `{0, 1, ∞}`.  This is the "`polynomialSelfMap` is unramified over
`markedPoints`" half of the forward direction. -/
theorem branch_polynomialSelfMap_subset_markedPoints [IsAlgClosed k] [CharZero k]
    (hcrit : ∀ a : k, Polynomial.aeval a (Polynomial.derivative g) = 0 →
      Polynomial.aeval a g = 0 ∨ Polynomial.aeval a g = 1) :
    Branch (polynomialSelfMap k g hd) ⊆ Belyi.markedPoints k := by
  refine (branch_polynomialSelfMap_subset k g hd).trans ?_
  rintro y (⟨a, ha, rfl⟩ | hy)
  · rcases hcrit a ha with h | h
    · rw [h, point_closedPoint_zero_eq]; exact Belyi.zero_mem_markedPoints k
    · rw [h, point_closedPoint_one_eq]; exact Belyi.one_mem_markedPoints k
  · rw [Set.mem_singleton_iff] at hy
    rw [hy]; exact Belyi.infty_mem_markedPoints k

end Belyi.P1

namespace Belyi

open Polynomial AlgebraicGeometry

noncomputable local instance instLOFP_polynomialSelfMap_map {k : Type u} [Field k] (g : k[X])
    (hd : 0 < g.natDegree) : LocallyOfFinitePresentation (P1.polynomialSelfMap k g hd) :=
  P1.locallyOfFinitePresentation_polynomialSelfMap k g hd

/-- **B4c (marked branch locus, rational form).** The combined reduction (issue #185) produces a
non-constant `g : ℚ[X]` whose critical values in `k` lie in `{0, 1}` (`Belyi.critVal k g ⊆ {0, 1}`).
Transporting `g` to `k[X]` via `algebraMap ℚ k`, the polynomial self-map of its base change has
branch locus inside `markedPoints k`.  The forward-direction assembly (issue #188) consumes exactly
this shape.  The transport uses `aeval_map_algebraMap`/`derivative_map` (values and derivative are
unchanged) and `mem_critVal_iff` (the `hcrit` hypothesis is precisely the `critVal` condition). -/
theorem branch_map_polynomialSelfMap_subset_markedPoints {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] [Algebra ℚ k] {g : ℚ[X]} (hgd : g.natDegree ≠ 0)
    (hcv : ∀ x ∈ Belyi.critVal k g, x = 0 ∨ x = 1)
    (hd : 0 < (g.map (algebraMap ℚ k)).natDegree) :
    Branch (P1.polynomialSelfMap k (g.map (algebraMap ℚ k)) hd) ⊆ Belyi.markedPoints k := by
  apply P1.branch_polynomialSelfMap_subset_markedPoints
  intro a ha
  have hderiv : derivative g ≠ 0 := derivative_ne_zero.mpr hgd
  have hda : aeval a (derivative g) = 0 := by
    rwa [derivative_map, aeval_map_algebraMap k] at ha
  have hval : aeval a (g.map (algebraMap ℚ k)) = aeval a g := aeval_map_algebraMap k a g
  rw [hval]
  exact hcv _ (aeval_mem_critVal hderiv hda)

end Belyi
