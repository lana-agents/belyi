/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveDeriv.Local

/-!
# The order of `d/dπ` of a function at a place

Setting as in `Belyi/CurveDeriv/Local.lean`: `π : K` transcendental over `ℚ`, `K` finite over
`ℚ⟮π⟯`, `O` a discrete valuation subring of `K` containing `ℚ`, with uniformiser `π` and
residue field algebraic over `ℚ`; write `v := O.valuation`, so that units of `O` are the
elements with `v w = 1`.  We compute the order of `d/dπ` of a function at the place `O`, the
local input for the canonical divisor and the Riemann–Hurwitz formula:

* `derivAlong_unit_mul_pow`: `d/dπ (u π^(k+1)) = w π^k` with `w` a unit, for `u` a unit;
* `derivAlong_eq_unit_mul_pow_of_aeval` (a): if `t ∈ O`, `m ∈ ℚ[X]` is separable (e.g. the
  minimal polynomial of the residue of `t`) and `m(t) = u π^e` with `u` a unit and `e ≥ 1`, then
  `d/dπ t = w π^(e-1)` with `w` a unit;
* `derivAlong_eq_unit_mul_zpow_of_inv` (b): if `t⁻¹ = u π^e` with `u` a unit and `e ≥ 1`, then
  `d/dπ t = w π^(-(e+1))` with `w` a unit;
* `valuation_derivAlong_uniformizer` (c): for another uniformiser `π'` of `O`, `d/dπ π'` is a
  unit of `O` (independence of the uniformiser).
-/

open Polynomial IntermediateField
open scoped IntermediateField

namespace Belyi.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] {O : ValuationSubring K} {π : K}
  (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
  (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O)
  (hres : ∀ x ∈ O, ∃ p : ℚ[X], p ≠ 0 ∧ O.valuation (aeval x p) < 1)
  [IsDiscreteValuationRing O] (hπO : π ∈ O) (hirr : Irreducible (⟨π, hπO⟩ : O))
include ht hQ hres hirr

/-- `d/dπ (u π^(k+1)) = w π^k` with `w` a unit of `O`, for `u` a unit of `O`. -/
theorem derivAlong_unit_mul_pow {u : K} (hu : O.valuation u = 1) (k : ℕ) :
    ∃ w : K, O.valuation w = 1 ∧ derivAlong π (u * π ^ (k + 1)) = w * π ^ k := by
  have huO : u ∈ O := (O.valuation_le_one_iff u).mp hu.le
  have hDu := derivAlong_mem O ht hQ hres hπO hirr huO
  refine ⟨((k + 1 : ℕ) : K) * u + π * derivAlong π u, ?_, ?_⟩
  · have h1 : O.valuation (((k + 1 : ℕ) : K) * u) = 1 := by
      rw [map_mul, hu, mul_one, ← map_natCast (algebraMap ℚ K)]
      exact valuation_algebraMap_rat hQ (by positivity)
    have h2 : O.valuation (π * derivAlong π u) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' ((O.valuation_le_one_iff _).mpr hDu))
        (valuation_lt_one_of_irreducible hπO hirr)
    rw [add_comm, Valuation.map_add_eq_of_lt_right _ (h1 ▸ h2), h1]
  · rw [Derivation.leibniz, Derivation.leibniz_pow, derivAlong_self ht]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, mul_one]
    push_cast
    ring

/-- **(a)** If `t ∈ O`, `m ∈ ℚ[X]` is separable (e.g. the minimal polynomial of the residue of
`t`, which is irreducible, hence separable in characteristic zero) and `m(t) = u π^e` with `u` a
unit and `e ≥ 1`, then `d/dπ t = w π^(e-1)` with `w` a unit. -/
theorem derivAlong_eq_unit_mul_pow_of_aeval {t : K} (htO : t ∈ O) {m : ℚ[X]}
    (hm : m.Separable) {u : K} (hu : O.valuation u = 1) {e : ℕ} (he : 1 ≤ e)
    (hmt : aeval t m = u * π ^ e) :
    ∃ w : K, O.valuation w = 1 ∧ derivAlong π t = w * π ^ (e - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have hπ1 := valuation_lt_one_of_irreducible hπO hirr
  have hv : O.valuation (aeval t m) < 1 := by
    rw [hmt, map_mul, hu, one_mul, map_pow]
    exact pow_lt_one₀ zero_le hπ1 (Nat.succ_ne_zero k)
  have hm' := valuation_aeval_derivative_eq_one hQ htO hm hv
  have hne : aeval t (derivative m) ≠ 0 := by
    intro h
    rw [h, map_zero] at hm'
    exact zero_ne_one hm'
  obtain ⟨w₀, hw₀, hD⟩ := derivAlong_unit_mul_pow ht hQ hres hπO hirr hu k
  refine ⟨(aeval t (derivative m))⁻¹ * w₀, by rw [map_mul, map_inv₀, hm', hw₀]; simp, ?_⟩
  have := (derivAlong π).map_aeval m t
  rw [hmt, hD, smul_eq_mul] at this
  rw [Nat.add_sub_cancel, mul_assoc, this, inv_mul_cancel_left₀ hne]

/-- **(b)** If `t⁻¹ = u π^e` with `u` a unit and `e ≥ 1` (a pole of order `e`), then
`d/dπ t = w π^(-(e+1))` with `w` a unit. -/
theorem derivAlong_eq_unit_mul_zpow_of_inv {t : K} {u : K} (hu : O.valuation u = 1) {e : ℕ}
    (he : 1 ≤ e) (htu : t⁻¹ = u * π ^ e) :
    ∃ w : K, O.valuation w = 1 ∧ derivAlong π t = w * π ^ (-(e + 1 : ℤ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  have hπ0 := ne_zero_of_irreducible hπO hirr
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  obtain ⟨w₀, hw₀, hD⟩ := derivAlong_unit_mul_pow ht hQ hres hπO hirr hu k
  refine ⟨-(u⁻¹ ^ 2 * w₀), by rw [Valuation.map_neg, map_mul, map_pow, map_inv₀, hu, hw₀]; simp,
    ?_⟩
  have ht' : t = (u * π ^ (k + 1))⁻¹ := by rw [← htu, inv_inv]
  rw [ht', Derivation.leibniz_inv, hD, smul_eq_mul]
  rw [show (-(((k + 1 : ℕ) : ℤ) + 1)) = -(k : ℤ) - 2 by push_cast; ring, zpow_sub₀ hπ0,
    zpow_neg, zpow_natCast]
  field_simp
  ring

/-- **(c)** Independence of the uniformiser: for another uniformiser `π'` of `O`, `d/dπ π'` is a
unit of `O`. -/
theorem valuation_derivAlong_uniformizer {π' : K} (hπ'O : π' ∈ O)
    (hirr' : Irreducible (⟨π', hπ'O⟩ : O)) : O.valuation (derivAlong π π') = 1 := by
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.associated_of_irreducible O hirr hirr'
  have hw' : π' = ((w : O) : K) * π ^ (0 + 1) := by
    rw [zero_add, pow_one, mul_comm]
    exact (congrArg Subtype.val hw).symm
  obtain ⟨w₀, hw₀, hD⟩ := derivAlong_unit_mul_pow ht hQ hres hπO hirr (O.valuation_unit w) 0
  rw [hw', hD, pow_zero, mul_one, hw₀]

end Belyi.CurveDeriv
