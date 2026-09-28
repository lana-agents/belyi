/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.RamIdx

/-!
# The canonical divisor and the Hurwitz formula for a function

Let `K` be a curve field and `t ∈ K` transcendental over `ℚ`. The *canonical divisor*
`K_t = div (dt)` of the differential `dt` (`Belyi.CurveField.Divisor.canonicalDiv t`) has
coefficient `ord_P (dt/dπ_P)` at a place `P` with uniformiser `π_P`. By
`Belyi/CurveField/RamIdx.lean` this is `e_t(P) - 1` if `t ∈ O_P` and `-e_t(P) - 1` at a pole,
so `K_t = R_t - 2 (t)_∞`, where `R_t = ∑_P (e_t(P) - 1) P` is the ramification divisor
(`Belyi.CurveField.Divisor.ramDiv`) and `(t)_∞` the divisor of poles.

## Main results

* `Belyi.CurveField.Divisor.canonicalDiv_apply_of_mem`,
  `Belyi.CurveField.Divisor.canonicalDiv_apply_of_notMem`: the coefficients of `K_t`.
* `Belyi.CurveField.Divisor.canonicalDiv_eq_ramDiv_sub`: `K_t = R_t - 2 (t)_∞`.
* `Belyi.CurveField.Divisor.canonicalDiv_eq_add_div`: `K_s = K_t + div (ds/dt)` (chain rule),
  so all canonical divisors are linearly equivalent
  (`Belyi.CurveField.Divisor.exists_canonicalDiv_eq_add_div`) and have the same degree
  (`Belyi.CurveField.Divisor.deg_canonicalDiv_eq`).
* `Belyi.CurveField.Divisor.deg_canonicalDiv`: the **Hurwitz formula**
  `deg K_t = -2 [K : ℚ(t)] + ∑_P (e_t(P) - 1) deg P`.
* `Belyi.CurveField.Divisor.canonicalDiv_eq_of_adjoin_eq_top`: for `K = ℚ(t)` all ramification
  indices of `t` are `1` (`Belyi.CurveField.Divisor.ramIdx_eq_one_of_adjoin_eq_top`) and
  `K_t = -2 [∞]` with `∞` the unique pole of `t`, of degree `1`; so `deg K_t = -2`
  (`Belyi.CurveField.Divisor.deg_canonicalDiv_of_adjoin_eq_top`).
-/

open Belyi.CurveDeriv IntermediateField
open scoped IntermediateField

namespace Belyi.CurveField

namespace Divisor

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K] {t : K}

theorem finite_setOf_ord_derivAlong_ne_zero (t : K) :
    {P : Place K | P.ord (derivAlong P.uniformizer t) ≠ 0}.Finite := by
  by_cases ht : Transcendental ℚ t
  · refine ((Place.finite_setOf_notMem t).union (finite_setOf_one_lt_ramIdx ht)).subset
      fun P hP ↦ ?_
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, not_lt] at hn hP
    obtain ⟨htP, hle⟩ := hn
    rw [P.ord_derivAlong_of_mem ht htP] at hP
    have := ramIdx_pos ht P
    have h1 : ramIdx t P = 1 := by omega
    rw [h1] at hP
    exact hP (by norm_num)
  · have ht' : IsAlgebraic ℚ t := not_not.mp ht
    convert Set.finite_empty
    ext P
    simp [derivAlong_eq_zero_of_isAlgebraic ht']

/-- The **canonical divisor** `K_t = div (dt)` of a function `t`: its coefficient at a place `P`
is `ord_P (dt/dπ_P)` for the chosen uniformiser `π_P` of `P` (and `K_t = 0` for `t` algebraic
over `ℚ`, where `dt = 0`). -/
noncomputable def canonicalDiv (t : K) : Divisor K :=
  Finsupp.ofSupportFinite (fun P ↦ P.ord (derivAlong P.uniformizer t))
    (finite_setOf_ord_derivAlong_ne_zero t)

theorem canonicalDiv_apply (t : K) (P : Place K) :
    canonicalDiv t P = P.ord (derivAlong P.uniformizer t) := rfl

theorem canonicalDiv_apply_of_mem (ht : Transcendental ℚ t) {P : Place K} (h : t ∈ P.1) :
    canonicalDiv t P = ramIdx t P - 1 :=
  P.ord_derivAlong_of_mem ht h

theorem canonicalDiv_apply_of_notMem {P : Place K} (h : t ∉ P.1) :
    canonicalDiv t P = -ramIdx t P - 1 :=
  P.ord_derivAlong_of_notMem h

theorem canonicalDiv_of_isAlgebraic (ht : IsAlgebraic ℚ t) : canonicalDiv t = 0 := by
  ext P
  simp [canonicalDiv_apply, derivAlong_eq_zero_of_isAlgebraic ht]

/-! ### The ramification divisor -/

/-- The **ramification divisor** `R_t = ∑_P (e_t(P) - 1) P` of a transcendental `t`
(defined as `K_t + 2 (t)_∞`, see `Belyi.CurveField.Divisor.ramDiv_apply`). -/
noncomputable def ramDiv (t : K) : Divisor K := canonicalDiv t + (2 : ℤ) • polarDivisor t

theorem canonicalDiv_eq_ramDiv_sub (t : K) :
    canonicalDiv t = ramDiv t - (2 : ℤ) • polarDivisor t := by
  rw [ramDiv, add_sub_cancel_right]

theorem polarDivisor_apply_eq_ramIdx {P : Place K} (h : t ∉ P.1) :
    polarDivisor t P = ramIdx t P := by
  rw [polarDivisor_apply, ramIdx_of_notMem h]
  have := (P.ord_neg_iff).mpr h
  omega

theorem polarDivisor_apply_of_mem {P : Place K} (h : t ∈ P.1) : polarDivisor t P = 0 := by
  rw [polarDivisor_apply]
  have := P.ord_nonneg_of_mem h
  omega

theorem ramDiv_apply (ht : Transcendental ℚ t) (P : Place K) :
    ramDiv t P = ramIdx t P - 1 := by
  rw [ramDiv, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  by_cases h : t ∈ P.1
  · rw [canonicalDiv_apply_of_mem ht h, polarDivisor_apply_of_mem h]
    ring
  · rw [canonicalDiv_apply_of_notMem h, polarDivisor_apply_eq_ramIdx h]
    ring

theorem ramDiv_nonneg (ht : Transcendental ℚ t) : 0 ≤ ramDiv t := fun P ↦ by
  rw [Finsupp.coe_zero, Pi.zero_apply, ramDiv_apply ht]
  have := ramIdx_pos ht P
  omega

theorem support_ramDiv (ht : Transcendental ℚ t) :
    (ramDiv t).support = (finite_setOf_one_lt_ramIdx ht).toFinset := by
  ext P
  rw [Finsupp.mem_support_iff, ramDiv_apply ht, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have := ramIdx_pos ht P
  omega

theorem deg_ramDiv (ht : Transcendental ℚ t) :
    (ramDiv t).deg = ∑ P ∈ (finite_setOf_one_lt_ramIdx ht).toFinset,
      ((ramIdx t P : ℤ) - 1) * P.deg := by
  rw [deg_eq_sum_of_support_subset _ (support_ramDiv ht).le]
  exact Finset.sum_congr rfl fun P _ ↦ by rw [ramDiv_apply ht]

/-- If `t` is unramified everywhere, then `K_t = -2 (t)_∞`. -/
theorem canonicalDiv_eq_of_forall_ramIdx_eq_one (ht : Transcendental ℚ t)
    (h1 : ∀ P, ramIdx t P = 1) : canonicalDiv t = (-2 : ℤ) • polarDivisor t := by
  have : ramDiv t = 0 := by
    ext P
    rw [ramDiv_apply ht, h1]
    simp
  rw [canonicalDiv_eq_ramDiv_sub, this, zero_sub, neg_smul]

/-! ### Independence of the function -/

/-- **Chain rule for canonical divisors**: `K_s = K_t + div (ds/dt)`. -/
theorem canonicalDiv_eq_add_div {s : K} (hs : Transcendental ℚ s) (ht : Transcendental ℚ t) :
    canonicalDiv s = canonicalDiv t + div (derivAlong t s) := by
  have := isAlgebraic_adjoin hs
  have := isAlgebraic_adjoin ht
  have hts : derivAlong t s ≠ 0 := fun h0 ↦ by
    have h1 := derivAlong_mul_derivAlong hs ht
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  ext P
  rw [Finsupp.add_apply, canonicalDiv_apply, canonicalDiv_apply, div_apply]
  have hchain := congrArg (· s) (derivAlong_eq_smul P.uniformizer ht)
  simp only [Derivation.smul_apply, smul_eq_mul] at hchain
  rw [hchain, P.ord_mul (P.derivAlong_uniformizer_ne_zero ht) hts]

/-- All canonical divisors are linearly equivalent. -/
theorem exists_canonicalDiv_eq_add_div {s : K} (hs : Transcendental ℚ s)
    (ht : Transcendental ℚ t) : ∃ f : K, f ≠ 0 ∧ canonicalDiv s = canonicalDiv t + div f := by
  have := isAlgebraic_adjoin hs
  have := isAlgebraic_adjoin ht
  refine ⟨derivAlong t s, fun h0 ↦ ?_, canonicalDiv_eq_add_div hs ht⟩
  have h1 := derivAlong_mul_derivAlong hs ht
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

/-- The degree of the canonical divisor does not depend on the function. -/
theorem deg_canonicalDiv_eq {s : K} (hs : Transcendental ℚ s) (ht : Transcendental ℚ t) :
    (canonicalDiv s).deg = (canonicalDiv t).deg := by
  rw [canonicalDiv_eq_add_div hs ht, deg_add, deg_div, add_zero]

/-! ### The Hurwitz formula -/

/-- **Hurwitz formula** for a function `t : X → ℙ¹`:
`deg K_t = -2 [K : ℚ(t)] + ∑_P (e_t(P) - 1) deg P`. -/
theorem deg_canonicalDiv (ht : Transcendental ℚ t) :
    (canonicalDiv t).deg = -2 * Module.finrank ℚ⟮t⟯ K +
      ∑ P ∈ (finite_setOf_one_lt_ramIdx ht).toFinset, ((ramIdx t P : ℤ) - 1) * P.deg := by
  rw [canonicalDiv_eq_ramDiv_sub, deg_sub, deg_zsmul, deg_polarDivisor ht, deg_ramDiv ht]
  ring

/-! ### The rational function field -/

section Rational

omit [IsCurveField K] in
/-- If `K = ℚ(t)` and `s = m(t)` with `m ∈ ℚ[X]` monic nonconstant, then `[K : ℚ(s)] ≤ deg m`. -/
theorem finrank_adjoin_aeval_le (htop : ℚ⟮t⟯ = ⊤) {m : Polynomial ℚ} (hm : m.Monic)
    (hm1 : m.natDegree ≠ 0) :
    Module.finrank ℚ⟮Polynomial.aeval t m⟯ K ≤ m.natDegree := by
  set s := Polynomial.aeval t m
  set F := ℚ⟮s⟯
  let p : Polynomial F := m.map (algebraMap ℚ F) - Polynomial.C ⟨s, mem_adjoin_simple_self ℚ s⟩
  have hdeg : p.natDegree = m.natDegree := by
    rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_map]
  have hmonic : p.Monic := by
    refine (hm.map _).sub_of_left (Polynomial.degree_C_le.trans_lt ?_)
    rw [Polynomial.degree_map]
    exact Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hm1)
  have haeval : Polynomial.aeval t p = 0 := by
    simp [p, s, Polynomial.aeval_map_algebraMap]
  have hint : IsIntegral F t := ⟨p, hmonic, by rwa [← Polynomial.aeval_def]⟩
  have htop' : F⟮t⟯ = ⊤ := by
    have : ℚ⟮t⟯ ≤ (F⟮t⟯).restrictScalars ℚ :=
      IntermediateField.adjoin_simple_le_iff.mpr (mem_adjoin_simple_self F t)
    rwa [htop, top_le_iff, IntermediateField.restrictScalars_eq_top_iff] at this
  rw [← IntermediateField.finrank_top', ← htop', IntermediateField.adjoin.finrank hint, ← hdeg]
  exact Polynomial.natDegree_le_natDegree (minpoly.min F t hmonic haeval)

/-- For `K = ℚ(t)`, the function `t` is unramified everywhere. -/
theorem ramIdx_eq_one_of_adjoin_eq_top (ht : Transcendental ℚ t) (htop : ℚ⟮t⟯ = ⊤)
    (P : Place K) : ramIdx t P = 1 := by
  have hpos := ramIdx_pos ht P
  have hdeg := P.deg_pos
  suffices h : (ramIdx t P : ℤ) * P.deg ≤ P.deg by
    have h' : ramIdx t P * P.deg ≤ 1 * P.deg := by rw [one_mul]; exact_mod_cast h
    have := Nat.le_of_mul_le_mul_right h' hdeg
    omega
  by_cases h : t ∈ P.1
  · have hint := P.isIntegral_residue ⟨t, h⟩
    have hmon : (P.resMinpoly h).Monic := minpoly.monic hint
    have hm1 : (P.resMinpoly h).natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
    have hs : Transcendental ℚ (Polynomial.aeval t (P.resMinpoly h)) :=
      ht.aeval _ hm1 (by rw [hmon.leadingCoeff]; exact one_mem _)
    have hord := ramIdx_of_mem h
    have hle1 : P.ord (Polynomial.aeval t (P.resMinpoly h)) * P.deg ≤
        Module.finrank ℚ⟮Polynomial.aeval t (P.resMinpoly h)⟯ K := by
      rw [← Place.sum_ord_mul_deg_zeros _ hs]
      refine Finset.single_le_sum
        (f := fun Q : Place K ↦ Q.ord (Polynomial.aeval t (P.resMinpoly h)) * (Q.deg : ℤ))
        (fun Q hQ ↦ ?_) ?_
      · have := (Set.Finite.mem_toFinset _).mp hQ
        exact mul_nonneg (le_of_lt this) (Int.natCast_nonneg _)
      · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ← hord]
        exact_mod_cast hpos
    have hle2 := finrank_adjoin_aeval_le htop hmon hm1
    have hle3 : (P.resMinpoly h).natDegree ≤ P.deg := minpoly.natDegree_le _
    rw [hord]
    have : (Module.finrank ℚ⟮Polynomial.aeval t (P.resMinpoly h)⟯ K : ℤ) ≤ P.deg := by
      exact_mod_cast hle2.trans hle3
    omega
  · have hneg := (P.ord_neg_iff).mpr h
    have hpoles := Place.sum_ord_mul_deg_poles t ht
    rw [htop, IntermediateField.finrank_top, Nat.cast_one] at hpoles
    have hle : -P.ord t * P.deg ≤ 1 := by
      rw [← hpoles]
      refine Finset.single_le_sum (f := fun Q : Place K ↦ -Q.ord t * (Q.deg : ℤ))
        (fun Q hQ ↦ ?_) ?_
      · have := (Set.Finite.mem_toFinset _).mp hQ
        exact mul_nonneg (by simp only [Set.mem_setOf_eq] at this; omega) (Int.natCast_nonneg _)
      · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
        exact hneg
    rw [ramIdx_of_notMem h]
    have : (1 : ℤ) ≤ P.deg := by exact_mod_cast hdeg
    omega

/-- **The canonical divisor of `ℙ¹`**: for `K = ℚ(t)`, `K_t = -2 [∞]`, where `∞` is the unique
pole of `t`, a simple pole of degree `1`. -/
theorem canonicalDiv_eq_of_adjoin_eq_top (ht : Transcendental ℚ t) (htop : ℚ⟮t⟯ = ⊤) :
    ∃ P : Place K, P.ord t = -1 ∧ P.deg = 1 ∧ canonicalDiv t = Finsupp.single P (-2) := by
  obtain ⟨P, hP⟩ := Place.exists_ord_neg ht
  have hPnot : t ∉ P.1 := (P.ord_neg_iff).mp hP
  have he := ramIdx_eq_one_of_adjoin_eq_top ht htop P
  have hordP : P.ord t = -1 := by
    have := ramIdx_of_notMem hPnot
    rw [he] at this
    omega
  have hpolP : polarDivisor t P = 1 := by rw [polarDivisor_apply, hordP]; rfl
  have hdegpol : (polarDivisor t).deg = 1 := by
    rw [deg_polarDivisor ht, htop, IntermediateField.finrank_top]; rfl
  have hle : Finsupp.single P 1 ≤ polarDivisor t := by
    classical
    intro Q
    rw [Finsupp.single_apply]
    split_ifs with hQ
    · rw [← hQ, hpolP]
    · exact polarDivisor_nonneg t Q
  have hrest : 0 ≤ polarDivisor t - Finsupp.single P 1 := sub_nonneg.mpr hle
  have hdegP : P.deg = 1 := by
    have h1 := deg_nonneg hrest
    rw [deg_sub, hdegpol, deg_single] at h1
    have := P.deg_pos
    omega
  have hpol : polarDivisor t = Finsupp.single P 1 := by
    by_contra hne
    have h1 := deg_pos_of_nonneg_of_ne_zero hrest (sub_ne_zero.mpr hne)
    rw [deg_sub, hdegpol, deg_single, hdegP] at h1
    norm_num at h1
  refine ⟨P, hordP, hdegP, ?_⟩
  rw [canonicalDiv_eq_of_forall_ramIdx_eq_one ht (ramIdx_eq_one_of_adjoin_eq_top ht htop), hpol,
    Finsupp.smul_single, smul_eq_mul, mul_one]

/-- For `K = ℚ(t)`, `deg K_t = -2`. -/
theorem deg_canonicalDiv_of_adjoin_eq_top (ht : Transcendental ℚ t) (htop : ℚ⟮t⟯ = ⊤) :
    (canonicalDiv t).deg = -2 := by
  obtain ⟨P, -, hdeg, h⟩ := canonicalDiv_eq_of_adjoin_eq_top ht htop
  rw [h, deg_single, hdeg]
  rfl

end Rational

end Divisor

end Belyi.CurveField
