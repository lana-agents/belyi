/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.NoncriticalBasic
import Belyi.CurveField.Extension
import Belyi.CurveDeriv.Order

/-!
# A nonconstant function is ramified at only finitely many places

Let `t` be a nonconstant function on a curve. We show that `e_P(t) > 1` for only finitely
many places `P` (`Belyi.CurveField.Noncritical.finite_setOf_one_lt_ramIdx`).

The poles of `t` are finite in number. At a place `P` where `t` is regular, let `π` be a
uniformiser. By `Belyi.CurveDeriv.derivAlong_eq_unit_mul_pow_of_aeval`,
`d/dπ t = w π^(e-1)` with `w` a unit and `e = e_P(t)`, so by the chain rule
`d/dt π = w⁻¹ π^(1-e)`: if `e > 1`, the derivation `d/dt` does not preserve `O_P`
(`exists_derivAlong_notMem`). On the other hand `d/dt` preserves `O_P` as soon as it maps
the finitely many generators of the chart ring `A_t` (a finite `ℚ[t]`-module) into `O_P`,
since `O_P` is a localisation of `A_t`; this excludes only finitely many places
(`finite_setOf_derivAlong_notMem`).
-/

open Polynomial IsDedekindDomain
open scoped IntermediateField
open Belyi.CurveDeriv (derivAlong)

namespace Belyi.CurveField.Noncritical

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

theorem transcendental_of_ord_ne_zero {P : Place K} {π : K} (h : P.ord π ≠ 0) :
    Transcendental ℚ π :=
  fun ha ↦ h (P.ord_eq_zero_of_isAlgebraic ha)

theorem isUnit_iff_ord_eq_zero (P : Place K) (y : P.1) (hy : (y : K) ≠ 0) :
    IsUnit y ↔ P.ord y = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ((u : P.1) : K) * ((u⁻¹ : P.1ˣ) : P.1) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
    have hu0 : (((u⁻¹ : P.1ˣ) : P.1) : K) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
    have := congrArg P.ord h1
    rw [P.ord_mul hy hu0, P.ord_one] at this
    have h2 := P.ord_nonneg_of_mem (u : P.1).2
    have h3 := P.ord_nonneg_of_mem ((u⁻¹ : P.1ˣ) : P.1).2
    omega
  · intro h0
    have hinv : (y : K)⁻¹ ∈ P.1 := ((P.ord_eq_zero_iff hy).mp h0).2
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hy)⟩

/-- An element of order `1` is a uniformiser. -/
theorem irreducible_of_ord_eq_one (P : Place K) {π : K} (hπ : P.ord π = 1) :
    Irreducible (⟨π, P.mem_of_ord_nonneg (by omega)⟩ : P.1) := by
  have hπ0 : π ≠ 0 := by rintro rfl; simp at hπ
  rw [irreducible_iff]
  refine ⟨fun h ↦ ?_, fun a b hab ↦ ?_⟩
  · rw [isUnit_iff_ord_eq_zero P _ hπ0] at h
    change P.ord π = 0 at h
    omega
  · have hab' : π = (a : K) * b := congrArg Subtype.val hab
    have ha0 : (a : K) ≠ 0 := by rintro h0; rw [h0, zero_mul] at hab'; exact hπ0 hab'
    have hb0 : (b : K) ≠ 0 := by rintro h0; rw [h0, mul_zero] at hab'; exact hπ0 hab'
    rw [isUnit_iff_ord_eq_zero P _ ha0, isUnit_iff_ord_eq_zero P _ hb0]
    have := congrArg P.ord hab'
    rw [P.ord_mul ha0 hb0, hπ] at this
    have h2 := P.ord_nonneg_of_mem a.2
    have h3 := P.ord_nonneg_of_mem b.2
    omega

/-- Residues are algebraic: every regular function is a root modulo `𝔪_P` of a nonzero
rational polynomial. -/
theorem exists_valuation_aeval_lt_one (P : Place K) :
    ∀ y ∈ P.1, ∃ p : ℚ[X], p ≠ 0 ∧ P.1.valuation (aeval y p) < 1 := by
  intro y hy
  refine ⟨minpoly ℚ (P.residue ⟨y, hy⟩), minpoly.ne_zero (P.isIntegral_residue _), ?_⟩
  refine (P.1.valuation_lt_one_iff ⟨_, P.aeval_mem hy _⟩).mp ((P.residue_eq_zero_iff).mp ?_)
  rw [P.residue_aeval hy]
  exact minpoly.aeval ℚ _

theorem valuation_eq_one_of_ord_eq_zero (P : Place K) {u : K} (hu0 : u ≠ 0)
    (hu : P.ord u = 0) : P.1.valuation u = 1 := by
  obtain ⟨h1, h2⟩ := (P.ord_eq_zero_iff hu0).mp hu
  have := (P.1.valuation_eq_one_iff ⟨u, h1⟩).mp
    ((isUnit_iff_ord_eq_zero P ⟨u, h1⟩ hu0).mpr hu)
  exact this

theorem ord_eq_zero_of_valuation_eq_one (P : Place K) {w : K} (hw : P.1.valuation w = 1) :
    P.ord w = 0 := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  exact (P.ord_eq_zero_iff hw0).mpr
    ⟨(P.1.valuation_le_one_iff w).mp hw.le, Belyi.CurveDeriv.inv_mem_of_valuation_eq_one hw⟩

/-- At a place where `t` is regular and ramified, `d/dt` does not preserve `O_P`. -/
theorem exists_derivAlong_notMem {t : K} (ht : Transcendental ℚ t) {P : Place K}
    (htP : t ∈ P.1) (hram : 1 < ramIdx P t) : ∃ s ∈ P.1, derivAlong t s ∉ P.1 := by
  set π := P.uniformizer
  have hπ : P.ord π = 1 := P.ord_uniformizer
  have hπ0 : π ≠ 0 := P.uniformizer_ne_zero
  have hπt : Transcendental ℚ π := transcendental_of_ord_ne_zero (by omega : P.ord π ≠ 0)
  have hπO : π ∈ P.1 := P.mem_of_ord_nonneg (by omega)
  have hirr := irreducible_of_ord_eq_one P hπ
  haveI : FiniteDimensional ℚ⟮π⟯ K := finiteDimensional_adjoin hπt
  haveI : Algebra.IsAlgebraic ℚ⟮π⟯ K := isAlgebraic_adjoin hπt
  haveI : Algebra.IsAlgebraic ℚ⟮t⟯ K := isAlgebraic_adjoin ht
  set m := minpoly ℚ (P.residue ⟨t, htP⟩)
  have hsep : m.Separable := (minpoly.irreducible (P.isIntegral_residue _)).separable
  have hm := ramIdx_of_mem htP
  have hmt0 : aeval t m ≠ 0 := fun h0 ↦ ht ⟨m, minpoly.ne_zero (P.isIntegral_residue _), h0⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ, ramIdx P t = e := ⟨(ramIdx P t).toNat, by omega⟩
  have he1 : 1 ≤ e := by omega
  set u := aeval t m / π ^ e
  have hu0 : u ≠ 0 := div_ne_zero hmt0 (pow_ne_zero _ hπ0)
  have hu : P.1.valuation u = 1 := by
    refine valuation_eq_one_of_ord_eq_zero P hu0 ?_
    rw [P.ord_div hmt0 (pow_ne_zero _ hπ0), P.ord_pow, hπ, ← hm, he]
    ring
  have hmt : aeval t m = u * π ^ e := by
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hπ0)]
  obtain ⟨w, hw, hD⟩ := Belyi.CurveDeriv.derivAlong_eq_unit_mul_pow_of_aeval hπt P.algebraMap_mem
    (exists_valuation_aeval_lt_one P) hπO hirr htP hsep hu he1 hmt
  refine ⟨π, hπO, fun hDπ ↦ ?_⟩
  have h1 := Belyi.CurveDeriv.derivAlong_mul_derivAlong hπt ht
  rw [hD] at h1
  have hD0 : derivAlong t π ≠ 0 := by rintro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have := congrArg P.ord h1
  rw [P.ord_one, P.ord_mul hD0 (mul_ne_zero hw0 (pow_ne_zero _ hπ0)),
    P.ord_mul hw0 (pow_ne_zero _ hπ0), ord_eq_zero_of_valuation_eq_one P hw, P.ord_pow, hπ]
    at this
  have h2 := P.ord_nonneg_of_mem hDπ
  have h3 : (1 : ℤ) ≤ ((e - 1 : ℕ) : ℤ) := by omega
  omega

/-- `d/dt` preserves `O_P` for all but finitely many places `P` containing `t`. -/
theorem finite_setOf_derivAlong_notMem {t : K} (ht : Transcendental ℚ t) :
    {P : Place K | t ∈ P.1 ∧ ∃ s ∈ P.1, derivAlong t s ∉ P.1}.Finite := by
  haveI : Fact (Transcendental ℚ t) := ⟨ht⟩
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := Algebra.adjoin ℚ {t}) (M := chartRing t)
  refine (G.finite_toSet.biUnion fun g _ ↦ Place.finite_setOf_notMem (derivAlong t g)).subset ?_
  rintro P ⟨htP, s, hs, hDs⟩
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  by_contra hgood
  push Not at hgood
  apply hDs
  -- `d/dt` maps the chart ring into `O_P`
  have hA : ∀ r : chartRing t, derivAlong t (r : K) ∈ P.1 := by
    intro r
    have hr : r ∈ Submodule.span (Algebra.adjoin ℚ {t}) (G : Set (chartRing t)) :=
      hG ▸ Submodule.mem_top
    induction hr using Submodule.span_induction with
    | mem g hg => exact hgood g hg
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Subalgebra.coe_add, map_add]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [Subalgebra.coe_smul, Algebra.smul_def]
      change derivAlong t ((a : K) * x) ∈ P.1
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact add_mem (mul_mem (Belyi.CurveDeriv.mem_of_mem_adjoin P.algebraMap_mem htP a.2) hx)
        (mul_mem (P.algebraMap_chartRing_mem t htP x)
          (Belyi.CurveDeriv.derivAlong_mem_of_mem_adjoin ht P.algebraMap_mem htP a.2))
  -- every element of `O_P` is a quotient of elements of the chart ring
  have hs' : s ∈ (Place.ofChart t (P.toChart t htP)).1 := by rwa [Place.ofChart_toChart]
  rw [Place.ofChart_val] at hs'
  obtain ⟨a, u, hu, hsu⟩ := hs'
  subst hsu
  have hun : ((u : chartRing t) : K) ∉ P.1.nonunits := by
    rw [← Place.mem_toChart_iff t P htP]; exact hu
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hun
  change derivAlong t ((a : K) * (u : K)⁻¹) ∈ P.1
  rw [← div_eq_mul_inv]
  rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  exact mul_mem (pow_mem hun.2 2) (sub_mem (mul_mem (P.algebraMap_chartRing_mem t htP u) (hA a))
    (mul_mem (P.algebraMap_chartRing_mem t htP a) (hA u)))

/-- **A nonconstant function is ramified at only finitely many places.** -/
theorem finite_setOf_one_lt_ramIdx {t : K} (ht : Transcendental ℚ t) :
    {P : Place K | 1 < ramIdx P t}.Finite := by
  refine ((Place.finite_setOf_notMem t).union (finite_setOf_derivAlong_notMem ht)).subset ?_
  intro P hP
  by_cases htP : t ∈ P.1
  · exact Or.inr ⟨htP, exists_derivAlong_notMem ht htP hP⟩
  · exact Or.inl htP

end Belyi.CurveField.Noncritical
