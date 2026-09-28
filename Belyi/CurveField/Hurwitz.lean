/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.Canonical
import Belyi.CurveField.Fundamental

/-!
# The Riemann–Hurwitz formula for finite extensions of curve fields

Let `L / K` be a finite extension of curve fields (a finite morphism of curves `Y → X`) and
`t ∈ K` transcendental. For a place `Q` of `L` over `P = Q ∩ K` with ramification index
`e = e(Q|P)`, the ramification indices of functions are multiplicative,
`e_t(Q) = e(Q|P) · e_t(P)` (`Belyi.CurveField.ramIdx_algebraMap`), and hence the canonical
divisors satisfy the local Riemann–Hurwitz formula
`ord_Q (dt) = e · ord_P (dt) + (e - 1)` (`Belyi.CurveField.Divisor.canonicalDiv_algebraMap_apply`).

Globally, `K_L = φ^* K_K + R_{L/K}` (`Belyi.CurveField.Divisor.canonicalDiv_algebraMap`), where
`φ^*` is the pullback of divisors (`Belyi.CurveField.Divisor.pullback`, with
`deg φ^* D = [L : K] deg D` by the fundamental identity, `Belyi.CurveField.Divisor.deg_pullback`)
and `R_{L/K} = ∑_Q (e(Q|P) - 1) Q` is the ramification divisor of `L / K`
(`Belyi.CurveField.Divisor.relRamDiv`). Taking degrees gives the **Riemann–Hurwitz formula**
`deg K_L = [L : K] deg K_K + ∑_Q (e_Q - 1) deg Q`
(`Belyi.CurveField.Divisor.deg_canonicalDiv_algebraMap`).
-/

open Polynomial Module Belyi.CurveDeriv
open scoped IntermediateField

namespace Belyi.CurveField

variable {K L : Type*} [Field K] [CharZero K] [IsCurveField K] [Field L] [CharZero L]
  [IsCurveField L] [Algebra K L] [FiniteDimensional K L]

omit [IsCurveField K] [IsCurveField L] [FiniteDimensional K L] in
theorem transcendental_algebraMap {t : K} (ht : Transcendental ℚ t) :
    Transcendental ℚ (algebraMap K L t) :=
  (transcendental_algebraMap_iff (algebraMap K L).injective).mpr ht

omit [CharZero K] [IsCurveField K] [CharZero L] [IsCurveField L] in
/-- The residue of the image of `x` at `Q` is the image of the residue of `x` at `Q ∩ K`. -/
theorem Place.residue_algebraMap (Q : Place L) {x : K} (hx : x ∈ (Q.restrict K).1) :
    Q.residue ⟨algebraMap K L x, hx⟩ = Q.residueFieldMap K ((Q.restrict K).residue ⟨x, hx⟩) := by
  rw [Place.residueFieldMap_residue]
  rfl

omit [IsCurveField K] [IsCurveField L] in
theorem Place.resMinpoly_algebraMap (Q : Place L) {x : K} (hx : x ∈ (Q.restrict K).1) :
    Q.resMinpoly (x := algebraMap K L x) hx = (Q.restrict K).resMinpoly hx := by
  rw [Place.resMinpoly, Place.resMinpoly, Q.residue_algebraMap hx]
  exact minpoly.algHom_eq (Q.residueFieldMap K).toRatAlgHom (Q.residueFieldMap K).injective _

/-- **Multiplicativity of ramification indices**: `e_t(Q) = e(Q|P) · e_t(P)`. -/
theorem ramIdx_algebraMap {t : K} (Q : Place L) :
    ramIdx (algebraMap K L t) Q = Q.ramificationIdx K * ramIdx t (Q.restrict K) := by
  suffices h : (ramIdx (algebraMap K L t) Q : ℤ) =
      Q.ramificationIdx K * (ramIdx t (Q.restrict K) : ℤ) by exact_mod_cast h
  by_cases h : t ∈ (Q.restrict K).1
  · have h' : algebraMap K L t ∈ Q.1 := h
    rw [ramIdx_of_mem h', ramIdx_of_mem h, Q.resMinpoly_algebraMap h, aeval_algebraMap_apply,
      Q.ord_algebraMap_eq_mul]
  · have h' : algebraMap K L t ∉ Q.1 := h
    rw [ramIdx_of_notMem h', ramIdx_of_notMem h, Q.ord_algebraMap_eq_mul]
    ring

theorem one_lt_ramIdx_algebraMap {t : K} (ht : Transcendental ℚ t) {Q : Place L}
    (hQ : 1 < Q.ramificationIdx K) : 1 < ramIdx (algebraMap K L t) Q := by
  rw [ramIdx_algebraMap]
  have := ramIdx_pos ht (Q.restrict K)
  nlinarith

variable (K L) in
/-- Only finitely many places of `L` are ramified over `K`. -/
theorem finite_setOf_one_lt_ramificationIdx :
    {Q : Place L | 1 < Q.ramificationIdx K}.Finite := by
  obtain ⟨t, ht⟩ := exists_transcendental K
  exact (finite_setOf_one_lt_ramIdx (transcendental_algebraMap (L := L) ht)).subset
    fun Q hQ ↦ one_lt_ramIdx_algebraMap ht hQ

namespace Divisor

/-! ### Pullback of divisors -/

theorem finite_setOf_restrict_mem_support (D : Divisor K) :
    {Q : Place L | Q.restrict K ∈ D.support}.Finite :=
  (D.support.finite_toSet.preimage' fun P _ ↦ Place.finite_setOf_restrict_eq (L := L) K P :)

variable (L) in
/-- The pullback `φ^* D = ∑_Q e(Q|P) D(P) Q` of a divisor of `K` to `L`. -/
noncomputable def pullback (D : Divisor K) : Divisor L :=
  Finsupp.ofSupportFinite (fun Q ↦ (Q.ramificationIdx K : ℤ) * D (Q.restrict K))
    ((finite_setOf_restrict_mem_support D).subset fun Q hQ ↦ by
      rw [Set.mem_setOf_eq, Finsupp.mem_support_iff]
      exact right_ne_zero_of_mul hQ)

theorem pullback_apply (D : Divisor K) (Q : Place L) :
    pullback L D Q = Q.ramificationIdx K * D (Q.restrict K) := rfl

theorem pullback_add (D E : Divisor K) : pullback L (D + E) = pullback L D + pullback L E := by
  ext Q
  simp only [pullback_apply, Finsupp.add_apply]
  ring

/-- `deg φ^* D = [L : K] · deg D`. -/
theorem deg_pullback (D : Divisor K) : (pullback L D).deg = finrank K L * D.deg := by
  classical
  let fib : Place K → Finset (Place L) := fun P ↦
    (Place.finite_setOf_restrict_eq (L := L) K P).toFinset
  have hfib : ∀ P Q, Q ∈ fib P ↔ Q.restrict K = P := fun P Q ↦ by
    simp only [fib, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hsupp : (pullback L D).support ⊆ D.support.biUnion fib := by
    intro Q hQ
    rw [Finsupp.mem_support_iff, pullback_apply] at hQ
    rw [Finset.mem_biUnion]
    exact ⟨Q.restrict K, Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hQ),
      (hfib _ _).mpr rfl⟩
  have hdisj : (D.support : Set (Place K)).PairwiseDisjoint fib := by
    intro P _ P' _ hPP'
    refine Finset.disjoint_left.mpr fun Q hQ hQ' ↦ hPP' ?_
    rw [← (hfib _ _).mp hQ, (hfib _ _).mp hQ']
  rw [deg_eq_sum_of_support_subset _ hsupp, Finset.sum_biUnion hdisj,
    deg_eq_sum_of_support_subset D subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  have hsum := Place.sum_ramificationIdx_mul_deg (L := L) P
  have hsum' : ∑ Q ∈ fib P, ((Q.ramificationIdx K : ℤ) * Q.deg) = finrank K L * P.deg := by
    exact_mod_cast hsum
  calc ∑ Q ∈ fib P, pullback L D Q * (Q.deg : ℤ)
      = ∑ Q ∈ fib P, D P * ((Q.ramificationIdx K : ℤ) * Q.deg) :=
        Finset.sum_congr rfl fun Q hQ ↦ by
          rw [pullback_apply, (hfib _ _).mp hQ]
          ring
    _ = finrank K L * (D P * P.deg) := by
      rw [← Finset.mul_sum, hsum']
      ring

/-! ### The ramification divisor of `L / K` -/

variable (K L) in
/-- The ramification divisor `R_{L/K} = ∑_Q (e(Q|P) - 1) Q` of `L / K` (in characteristic zero
all ramification is tame, so this is the different). -/
noncomputable def relRamDiv : Divisor L :=
  Finsupp.ofSupportFinite (fun Q ↦ (Q.ramificationIdx K : ℤ) - 1)
    ((finite_setOf_one_lt_ramificationIdx K L).subset fun Q hQ ↦ by
      have := Q.ramificationIdx_pos (K := K)
      simp only [Function.mem_support, ne_eq] at hQ
      rw [Set.mem_setOf_eq]
      omega)

theorem relRamDiv_apply (Q : Place L) : relRamDiv K L Q = (Q.ramificationIdx K : ℤ) - 1 := rfl

theorem deg_relRamDiv : (relRamDiv K L).deg =
    ∑ Q ∈ (finite_setOf_one_lt_ramificationIdx K L).toFinset,
      ((Q.ramificationIdx K : ℤ) - 1) * Q.deg := by
  refine deg_eq_sum_of_support_subset _ fun Q hQ ↦ ?_
  rw [Finsupp.mem_support_iff, relRamDiv_apply] at hQ
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have := Q.ramificationIdx_pos (K := K)
  omega

/-! ### Riemann–Hurwitz -/

/-- **Local Riemann–Hurwitz formula**: for `Q` over `P` with ramification index `e`,
`ord_Q (dt) = e · ord_P (dt) + (e - 1)`. -/
theorem canonicalDiv_algebraMap_apply {t : K} (ht : Transcendental ℚ t) (Q : Place L) :
    canonicalDiv (algebraMap K L t) Q =
      Q.ramificationIdx K * canonicalDiv t (Q.restrict K) + ((Q.ramificationIdx K : ℤ) - 1) := by
  have hr := ramIdx_algebraMap (t := t) Q
  by_cases h : t ∈ (Q.restrict K).1
  · have h' : algebraMap K L t ∈ Q.1 := h
    rw [canonicalDiv_apply_of_mem (transcendental_algebraMap ht) h',
      canonicalDiv_apply_of_mem ht h, hr]
    push_cast
    ring
  · have h' : algebraMap K L t ∉ Q.1 := h
    rw [canonicalDiv_apply_of_notMem h', canonicalDiv_apply_of_notMem h, hr]
    push_cast
    ring

/-- **Riemann–Hurwitz**, divisor form: `K_L = φ^* K_K + R_{L/K}`. -/
theorem canonicalDiv_algebraMap {t : K} (ht : Transcendental ℚ t) :
    canonicalDiv (algebraMap K L t) = pullback L (canonicalDiv t) + relRamDiv K L := by
  ext Q
  rw [Finsupp.add_apply, canonicalDiv_algebraMap_apply ht, pullback_apply, relRamDiv_apply]

/-- **The Riemann–Hurwitz formula**:
`deg K_L = [L : K] · deg K_K + ∑_Q (e(Q|P) - 1) deg Q`. -/
theorem deg_canonicalDiv_algebraMap {t : K} (ht : Transcendental ℚ t) :
    (canonicalDiv (algebraMap K L t)).deg = finrank K L * (canonicalDiv t).deg +
      ∑ Q ∈ (finite_setOf_one_lt_ramificationIdx K L).toFinset,
        ((Q.ramificationIdx K : ℤ) - 1) * Q.deg := by
  rw [canonicalDiv_algebraMap ht, deg_add, deg_pullback, deg_relRamDiv]

end Divisor

end Belyi.CurveField
