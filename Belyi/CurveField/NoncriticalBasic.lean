/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.Point
import Belyi.CurveField.RamIdx
import Belyi.NoncriticalP1.ElemMap

/-!
# Ramification indices and cusps of functions on a curve

Let `K` be a curve field (`Belyi.CurveField.IsCurveField`) and `φ ∈ K` transcendental over
`ℚ`, i.e. a nonconstant map `φ : X → ℙ¹` from the curve with function field `K`.

* The *ramification index* `e_P(φ)` of `φ` at a place `P`
  (`Belyi.CurveField.Noncritical.ramIdx P φ`) is `ord_P (m(φ))`, where `m ∈ ℚ[X]` is the
  minimal polynomial of the residue of `φ` in `κ(P)`, if `φ` is regular at `P`, and
  `-ord_P φ` if `φ` has a pole at `P`. It is positive (`ramIdx_pos`).
* The *cusps* of `φ` (`Belyi.CurveField.Noncritical.cusps φ`) are the places where `φ` takes
  a value in `{0, 1, ∞}`.
* `φ` is a *Belyi map* (`Belyi.CurveField.Noncritical.IsBelyi φ`) if it is unramified outside
  its cusps.

The value of `φ` at an algebraic point `x` is `val x φ ∈ ℙ¹(ℚ̄) = Option ℚ̄` (`none = ∞`).

## Main results

* `Belyi.CurveField.Noncritical.ord_aeval_eq`: for `g ∈ ℚ[X]` nonzero and `φ` regular at
  `x`, `ord_P (g(φ)) = e_P(φ) · mult_{φ(x)}(g)`: the order of `g(φ)` is the ramification index
  times the multiplicity of the value `φ(x)` as a root of `g`.
* `Belyi.CurveField.Noncritical.ramIdx_of_ord_pos`: at a zero `P` of `φ`, `e_P(φ) = ord_P φ`.
* `Belyi.CurveField.Noncritical.mem_cusps_iff`: `x.P` is a cusp of `φ` iff
  `val x φ ∈ {0, 1, ∞}`.
-/

open Polynomial IsLocalRing
open Belyi.NoncriticalP1 (Pt Qbar zeroOneInf mem_zeroOneInf)

namespace Belyi.CurveField

namespace Place

variable {K : Type*} [Field K] [CharZero K] (P : Place K)

variable [IsCurveField K]

/-- A regular function with nonzero residue is a unit. -/
theorem ord_eq_zero_of_residue_ne_zero {y : K} (hy : y ∈ P.1)
    (h : P.residue ⟨y, hy⟩ ≠ 0) : P.ord y = 0 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact h (by rw [show (⟨0, hy⟩ : P.1) = 0 from rfl, map_zero])
  refine le_antisymm ?_ (P.ord_nonneg_of_mem hy)
  by_contra hlt
  push Not at hlt
  exact h ((P.residue_eq_zero_iff).mpr ((P.ord_pos_iff_mem_maximalIdeal (a := ⟨y, hy⟩) hy0).mp hlt))

theorem ord_pos_of_residue_eq_zero {y : K} (hy : y ∈ P.1) (hy0 : y ≠ 0)
    (h : P.residue ⟨y, hy⟩ = 0) : 0 < P.ord y :=
  (P.ord_pos_iff_mem_maximalIdeal (a := ⟨y, hy⟩) hy0).mpr ((P.residue_eq_zero_iff).mp h)

theorem residue_eq_zero_of_ord_pos {y : K} (hy : 0 < P.ord y) :
    P.residue ⟨y, P.mem_of_ord_nonneg hy.le⟩ = 0 := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  exact (P.residue_eq_zero_iff).mpr ((P.ord_pos_iff_mem_maximalIdeal (a := ⟨y, _⟩) hy0).mp hy)

end Place

namespace QbarPoint

variable {K : Type*} [Field K] [CharZero K] (x : QbarPoint K)

theorem eval_aeval {f : K} (hf : f ∈ x.P.1) (p : ℚ[X]) :
    x.eval (aeval f p) (x.P.aeval_mem hf p) = aeval (x.eval f hf) p := by
  rw [eval, Place.residue_aeval, eval]
  exact (aeval_algHom_apply x.σ.toRatAlgHom _ p).symm

end QbarPoint

namespace Noncritical

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

open Classical in
/-- The ramification index `e_P(φ)` of `φ` at the place `P`: `ord_P (m(φ))` where `m` is the
minimal polynomial over `ℚ` of the residue of `φ`, if `φ ∈ O_P`, and `-ord_P φ` otherwise. -/
noncomputable def ramIdx (P : Place K) (φ : K) : ℤ :=
  if h : φ ∈ P.1 then P.ord (aeval φ (minpoly ℚ (P.residue ⟨φ, h⟩))) else -P.ord φ

/-- The cusps of `φ`: the places where `φ` takes a value in `{0, 1, ∞}`. -/
def cusps (φ : K) : Set (Place K) := {P | P.ord φ ≠ 0 ∨ 0 < P.ord (φ - 1)}

/-- `φ` is a Belyi map: it is nonconstant and unramified outside its cusps. -/
def IsBelyi (φ : K) : Prop :=
  Transcendental ℚ φ ∧ ∀ P : Place K, 1 < ramIdx P φ → P ∈ cusps φ

open Classical in
/-- The value `φ(x) ∈ ℙ¹(ℚ̄)` of `φ` at an algebraic point `x` (`none = ∞`). -/
noncomputable def val (x : QbarPoint K) (φ : K) : Pt :=
  if h : φ ∈ x.P.1 then some (x.eval φ h) else none

variable {φ : K}

theorem ramIdx_of_mem {P : Place K} (h : φ ∈ P.1) :
    ramIdx P φ = P.ord (aeval φ (minpoly ℚ (P.residue ⟨φ, h⟩))) := dif_pos h

theorem ramIdx_of_notMem {P : Place K} (h : φ ∉ P.1) : ramIdx P φ = -P.ord φ := dif_neg h

omit [IsCurveField K] in
theorem val_of_mem {x : QbarPoint K} (h : φ ∈ x.P.1) : val x φ = some (x.eval φ h) := dif_pos h

omit [IsCurveField K] in
theorem val_of_notMem {x : QbarPoint K} (h : φ ∉ x.P.1) : val x φ = none := dif_neg h

omit [IsCurveField K] in
theorem val_eq_none_iff {x : QbarPoint K} : val x φ = none ↔ φ ∉ x.P.1 := by
  unfold val
  split_ifs with h <;> simp [h]

theorem ramIdx_pos (hφ : Transcendental ℚ φ) (P : Place K) : 0 < ramIdx P φ := by
  unfold ramIdx
  split_ifs with h
  · have hr := P.isIntegral_residue ⟨φ, h⟩
    have hm0 : aeval φ (minpoly ℚ (P.residue ⟨φ, h⟩)) ≠ 0 :=
      fun h0 ↦ hφ ⟨_, minpoly.ne_zero hr, h0⟩
    refine P.ord_pos_of_residue_eq_zero (P.aeval_mem h _) hm0 ?_
    rw [P.residue_aeval h]
    exact minpoly.aeval ℚ _
  · have := (P.ord_neg_iff).mpr h
    omega

/-- At a zero of `φ`, the ramification index is the order of vanishing. -/
theorem ramIdx_of_ord_pos {P : Place K} (h : 0 < P.ord φ) : ramIdx P φ = P.ord φ := by
  have hmem : φ ∈ P.1 := P.mem_of_ord_nonneg h.le
  rw [ramIdx_of_mem hmem, P.residue_eq_zero_of_ord_pos h, minpoly.zero, aeval_X]

/-- At a pole of `φ`, the ramification index is the order of the pole. -/
theorem ramIdx_of_ord_neg {P : Place K} (h : P.ord φ < 0) : ramIdx P φ = -P.ord φ :=
  ramIdx_of_notMem ((P.ord_neg_iff).mp h)

/-- **The order of `g(φ)`**: for `g ∈ ℚ[X]` nonzero and `φ` regular at `x`,
`ord_P (g(φ)) = e_P(φ) · mult_{φ(x)} g`. -/
theorem ord_aeval_eq (hφ : Transcendental ℚ φ) (x : QbarPoint K) (hx : φ ∈ x.P.1) {g : ℚ[X]}
    (hg : g ≠ 0) :
    x.P.ord (aeval φ g) =
      ramIdx x.P φ * ((g.map (algebraMap ℚ Qbar)).rootMultiplicity (x.eval φ hx) : ℤ) := by
  induction h : g.natDegree using Nat.strong_induction_on generalizing g with
  | _ n ih =>
  set r := x.P.residue ⟨φ, hx⟩ with hr_def
  have hr : IsIntegral ℚ r := x.P.isIntegral_residue _
  have heval : ∀ p : ℚ[X], aeval (x.eval φ hx) p = x.σ (aeval r p) := fun p ↦
    aeval_algHom_apply x.σ.toRatAlgHom r p
  have hnz : ∀ p : ℚ[X], p ≠ 0 → aeval φ p ≠ 0 := fun p hp h0 ↦ hφ ⟨p, hp, h0⟩
  by_cases hdvd : minpoly ℚ r ∣ g
  · obtain ⟨g', rfl⟩ := hdvd
    have hm0 := minpoly.ne_zero hr
    have hg' : g' ≠ 0 := by rintro rfl; simp at hg
    have hdeg : g'.natDegree < n := by
      rw [← h, natDegree_mul hm0 hg']
      have := minpoly.natDegree_pos hr
      omega
    have hsep : ((minpoly ℚ r).map (algebraMap ℚ Qbar)).Separable :=
      (minpoly.irreducible hr).separable.map
    have hroot : ((minpoly ℚ r).map (algebraMap ℚ Qbar)).IsRoot (x.eval φ hx) := by
      rw [IsRoot, eval_map_algebraMap, heval, minpoly.aeval, map_zero]
    have hmap0 : (minpoly ℚ r).map (algebraMap ℚ Qbar) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ℚ Qbar).injective).mpr hm0
    have h1 : ((minpoly ℚ r).map (algebraMap ℚ Qbar)).rootMultiplicity (x.eval φ hx) = 1 :=
      le_antisymm (rootMultiplicity_le_one_of_separable hsep _)
        ((rootMultiplicity_pos hmap0).mpr hroot)
    have hprod : ((minpoly ℚ r * g').map (algebraMap ℚ Qbar)) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ℚ Qbar).injective).mpr hg
    rw [map_mul, x.P.ord_mul (hnz _ hm0) (hnz _ hg'), ih _ hdeg hg' rfl, Polynomial.map_mul,
      rootMultiplicity_mul (by rwa [Polynomial.map_mul] at hprod), h1, ramIdx_of_mem hx]
    push_cast
    ring
  · have hne : aeval r g ≠ 0 := fun h0 ↦ hdvd (minpoly.dvd ℚ r h0)
    have hne' : ¬ (g.map (algebraMap ℚ Qbar)).IsRoot (x.eval φ hx) := by
      rw [IsRoot, eval_map_algebraMap, heval]
      exact (map_ne_zero_iff _ x.σ.injective).mpr hne
    rw [rootMultiplicity_eq_zero hne', Nat.cast_zero, mul_zero]
    refine x.P.ord_eq_zero_of_residue_ne_zero (x.P.aeval_mem hx g) ?_
    rwa [x.P.residue_aeval hx]

/-! ### Values -/

theorem val_eq_some_zero_iff {x : QbarPoint K} (hφ0 : φ ≠ 0) :
    val x φ = some 0 ↔ 0 < x.P.ord φ := by
  unfold val
  split_ifs with h
  · rw [Option.some.injEq, x.eval_eq_zero_iff h hφ0]
  · simp only [false_iff, not_lt]
    exact (le_of_lt ((x.P.ord_neg_iff).mpr h))

theorem val_eq_some_one_iff {x : QbarPoint K} (hφ1 : φ - 1 ≠ 0) :
    val x φ = some 1 ↔ 0 < x.P.ord (φ - 1) := by
  constructor
  · intro hv
    have h : φ ∈ x.P.1 := by
      by_contra h
      rw [val_of_notMem h] at hv
      exact absurd hv (by simp)
    rw [val_of_mem h, Option.some.injEq] at hv
    have h1 : φ - 1 ∈ x.P.1 := sub_mem h x.P.1.one_mem
    rw [← x.eval_eq_zero_iff h1 hφ1, x.eval_sub h x.P.1.one_mem, hv, x.eval_one, sub_self]
  · intro hpos
    have h1 : φ - 1 ∈ x.P.1 := x.P.mem_of_ord_nonneg hpos.le
    have h : φ ∈ x.P.1 := by simpa using add_mem h1 x.P.1.one_mem
    rw [val_of_mem h, Option.some.injEq]
    have := (x.eval_eq_zero_iff h1 hφ1).mpr hpos
    rw [x.eval_sub h x.P.1.one_mem, x.eval_one, sub_eq_zero] at this
    exact this

/-- A place is a cusp of `φ` iff the value of `φ` at a point over it is `0`, `1` or `∞`. -/
theorem mem_cusps_iff (hφ : Transcendental ℚ φ) (x : QbarPoint K) :
    x.P ∈ cusps φ ↔ val x φ ∈ zeroOneInf := by
  have hφ0 : φ ≠ 0 := ne_zero_of_transcendental hφ
  have hφ1 : φ - 1 ≠ 0 := by
    intro h0
    apply hφ
    rw [sub_eq_zero] at h0
    rw [h0]
    exact isAlgebraic_one
  rw [mem_zeroOneInf, val_eq_none_iff, val_eq_some_zero_iff hφ0, val_eq_some_one_iff hφ1,
    ← x.P.ord_neg_iff]
  simp only [cusps, Set.mem_setOf_eq]
  omega

end Noncritical

end Belyi.CurveField
