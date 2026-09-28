/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.Canonical

/-!
# Belyi functions and the Belyi relation `K + E ~ (φ)_∞`

A function `φ` on a curve (an element of the curve field `K`) is a *Belyi function* if it is
nonconstant (transcendental over `ℚ`) and unramified outside `φ⁻¹ {0, 1, ∞}`. The places over
`0, 1, ∞` — the *cusps* of `φ` — are the places `P` with `ord_P φ ≠ 0` (zeros and poles of `φ`)
or `ord_P (φ - 1) > 0` (zeros of `φ - 1`); see `Belyi.CurveField.belyiCusps`.

For a Belyi function `φ`, with `E = ∑_{P cusp} P` the reduced divisor of cusps
(`Belyi.CurveField.cuspDivisor`), the canonical divisor of `dφ` satisfies
`K_φ + E = div (φ (φ - 1)) + (φ)_∞` (`Belyi.CurveField.canonicalDiv_add_cuspDivisor`): at a
cusp of ramification index `e` over `0` or `1` both sides are `e`, at a pole of order `e`
both sides are `-e`, and at the unramified non-cusps both sides vanish. Hence
`K + E ~ (φ)_∞` (`Belyi.CurveField.canonicalDiv_add_cuspDivisor_sub_polarDivisor`) and
`deg K + deg E = [K : ℚ(φ)]` (`Belyi.CurveField.deg_canonicalDiv_add_deg_cuspDivisor`).
-/

open Belyi.CurveDeriv Belyi.CurveField.Divisor
open scoped IntermediateField

namespace Belyi.CurveField

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-- The cusps of `φ`: the places over `0`, `1`, `∞`, i.e. with `ord_P φ ≠ 0` or
`ord_P (φ - 1) > 0`. -/
def belyiCusps (φ : K) : Set (Place K) := {P | P.ord φ ≠ 0 ∨ 0 < P.ord (φ - 1)}

theorem finite_belyiCusps (φ : K) : (belyiCusps φ).Finite :=
  (Place.finite_setOf_ord_ne_zero φ).union (Place.finite_setOf_ord_pos (φ - 1))

/-- `φ` is a **Belyi function**: nonconstant and unramified outside `φ⁻¹ {0, 1, ∞}`. -/
def IsBelyi (φ : K) : Prop :=
  Transcendental ℚ φ ∧ ∀ P : Place K, 1 < ramIdx φ P → P ∈ belyiCusps φ

open Classical in
/-- The reduced divisor `E = ∑_{P ∈ belyiCusps φ} P` of the cusps of `φ`. -/
noncomputable def cuspDivisor (φ : K) : Divisor K :=
  Finsupp.ofSupportFinite (fun P ↦ if P ∈ belyiCusps φ then 1 else 0)
    ((finite_belyiCusps φ).subset fun P hP ↦ by
      by_contra h
      exact hP (if_neg h))

theorem cuspDivisor_apply_of_mem {φ : K} {P : Place K} (h : P ∈ belyiCusps φ) :
    cuspDivisor φ P = 1 := by
  classical
  exact if_pos h

theorem cuspDivisor_apply_of_notMem {φ : K} {P : Place K} (h : P ∉ belyiCusps φ) :
    cuspDivisor φ P = 0 := by
  classical
  exact if_neg h

theorem cuspDivisor_eq_sum (φ : K) :
    cuspDivisor φ = ∑ P ∈ (finite_belyiCusps φ).toFinset, Finsupp.single P 1 := by
  classical
  ext Q
  rw [Finsupp.finsetSum_apply]
  by_cases hQ : Q ∈ belyiCusps φ
  · rw [cuspDivisor_apply_of_mem hQ,
      Finset.sum_eq_single_of_mem Q ((Set.Finite.mem_toFinset _).mpr hQ)]
    · simp
    · intro P _ hPQ
      exact Finsupp.single_eq_of_ne hPQ.symm
  · rw [cuspDivisor_apply_of_notMem hQ, Finset.sum_eq_zero]
    intro P hP
    refine Finsupp.single_eq_of_ne ?_
    rintro rfl
    exact hQ ((Set.Finite.mem_toFinset _).mp hP)

theorem deg_cuspDivisor (φ : K) :
    (cuspDivisor φ).deg = ∑ P ∈ (finite_belyiCusps φ).toFinset, (P.deg : ℤ) := by
  rw [cuspDivisor_eq_sum, ← degHom_apply, map_sum]
  simp

/-- **The Belyi relation**: for a Belyi function `φ` with reduced divisor of cusps `E`,
`K_φ + E = div (φ (φ - 1)) + (φ)_∞`. -/
theorem canonicalDiv_add_cuspDivisor {φ : K} (hφ : IsBelyi φ) :
    canonicalDiv φ + cuspDivisor φ = div (φ * (φ - 1)) + polarDivisor φ := by
  obtain ⟨ht, hram⟩ := hφ
  have hφ0 : φ ≠ 0 := ne_zero_of_transcendental ht
  have hφ1 : φ - 1 ≠ 0 := fun h ↦ ht ⟨Polynomial.X - 1, Polynomial.X_sub_C_ne_zero 1,
    by simpa using h⟩
  have hm1 : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  rw [div_mul hφ0 hφ1]
  ext P
  simp only [Finsupp.add_apply, div_apply]
  by_cases h : φ ∈ P.1
  · rw [canonicalDiv_apply_of_mem ht h, polarDivisor_apply_of_mem h]
    have h0 := P.ord_nonneg_of_mem h
    rcases h0.lt_or_eq with hpos | hzero
    · -- a zero of `φ`
      have hord1 : P.ord (φ - 1) = 0 := by
        rw [sub_eq_neg_add, P.ord_add_eq_of_lt hm1 hφ0 (by rw [Place.ord_neg, Place.ord_one]; exact hpos),
          Place.ord_neg, Place.ord_one]
      have hres : P.residue ⟨φ, h⟩ = algebraMap ℚ P.ResidueField 0 := by
        rw [map_zero]; exact (residue_eq_zero_iff_ord_pos h hφ0).mpr hpos
      rw [ramIdx_of_residue_eq h hres, map_zero, sub_zero,
        cuspDivisor_apply_of_mem (Or.inl hpos.ne'), hord1]
      ring
    · by_cases h1 : 0 < P.ord (φ - 1)
      · -- a zero of `φ - 1`
        have h1P : φ - 1 ∈ P.1 := P.mem_of_ord_nonneg h1.le
        have hres : P.residue ⟨φ, h⟩ = algebraMap ℚ P.ResidueField 1 := by
          have hsplit : (⟨φ, h⟩ : P.1) = ⟨φ - 1, h1P⟩ + 1 := Subtype.ext (by simp)
          rw [hsplit, map_add, (residue_eq_zero_iff_ord_pos h1P hφ1).mpr h1, map_one, map_one,
            zero_add]
        rw [ramIdx_of_residue_eq h hres, map_one, cuspDivisor_apply_of_mem (Or.inr h1),
          ← hzero]
        ring
      · -- neither a zero of `φ` nor of `φ - 1`, nor a pole: unramified
        have hnot : P ∉ belyiCusps φ := by
          rintro (h' | h')
          · exact h' hzero.symm
          · exact h1 h'
        have he : ramIdx φ P = 1 := by
          have := ramIdx_pos ht P
          have := mt (hram P) hnot
          omega
        have hord1 : P.ord (φ - 1) = 0 := by
          have := P.ord_nonneg_of_mem (sub_mem h P.1.one_mem)
          omega
        rw [he, cuspDivisor_apply_of_notMem hnot, hord1, ← hzero]
        simp
  · -- a pole of `φ`
    have hneg := (P.ord_neg_iff).mpr h
    have hord1 : P.ord (φ - 1) = P.ord φ := by
      rw [sub_eq_add_neg, P.ord_add_eq_of_lt hφ0 hm1 (by rw [Place.ord_neg, Place.ord_one]; exact hneg)]
    rw [canonicalDiv_apply_of_notMem h, polarDivisor_apply_eq_ramIdx h, ramIdx_of_notMem h,
      cuspDivisor_apply_of_mem (Or.inl hneg.ne), hord1]
    ring

/-- `K + E ~ (φ)_∞` for a Belyi function `φ`: `K_φ + E - (φ)_∞ = div (φ (φ - 1))`. -/
theorem canonicalDiv_add_cuspDivisor_sub_polarDivisor {φ : K} (hφ : IsBelyi φ) :
    canonicalDiv φ + cuspDivisor φ - polarDivisor φ = div (φ * (φ - 1)) := by
  rw [canonicalDiv_add_cuspDivisor hφ, add_sub_cancel_right]

/-- For a Belyi function `φ`: `deg K_φ + #cusps (counted with degree) = [K : ℚ(φ)]`. -/
theorem deg_canonicalDiv_add_deg_cuspDivisor {φ : K} (hφ : IsBelyi φ) :
    (canonicalDiv φ).deg + (cuspDivisor φ).deg = Module.finrank ℚ⟮φ⟯ K := by
  rw [← deg_add, canonicalDiv_add_cuspDivisor hφ, deg_add, deg_div, deg_polarDivisor hφ.1,
    zero_add]

end Belyi.CurveField
