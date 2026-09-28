/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.NoncriticalElem
import Belyi.CurveField.NoncriticalFinite
import Belyi.CurveField.Riemann
import Belyi.NoncriticalP1.Main

/-!
# Noncritical Belyi maps on curves

This file proves Theorem 2.5 of S. Mochizuki, *Noncritical Belyi maps*, Math. J. Okayama
Univ. **46** (2004), in the case `S = ∅`, for curves over number fields represented by
their function fields (`Belyi.CurveField.IsCurveField`):

> For every finite set `T` of places of `K` there is a Belyi map `φ ∈ K` (a nonconstant
> function unramified outside `φ⁻¹{0, 1, ∞}`) which is *noncritical* at `T`: `φ(P) ∉ {0, 1, ∞}`
> for all `P ∈ T` (`Belyi.CurveField.Noncritical.exists_isBelyi_forall_notMem_cusps`).

## Proof

1. Enlarge `T` to a finite set `T'` with `∑_{P ∈ T'} deg P ≥ N₁`, so that
   `A = ∑_{P ∈ T'} P` is the polar divisor of some `f` (`Divisor.exists_polarDivisor_eq`);
   `ψ = f⁻¹` has simple zeros exactly at the places of `T'`.
2. The set `S ⊆ ℙ¹(ℚ̄)` of branch values of `ψ` (together with `∞`) is finite
   (`finite_setOf_one_lt_ramIdx`), Galois stable, and does not contain `0` since `ψ` is
   unramified at its zeros.
3. The `ℙ¹` case (`Belyi.NoncriticalP1.exists_isNoncriticalBelyi`) gives a composite `H` of
   elementary maps with `H(S) ⊆ {0, 1, ∞}`, `H(0) ∉ {0, 1, ∞}`, unramified over
   `ℙ¹ ∖ {0, 1, ∞}`.
4. `φ = H ∘ ψ` works, by multiplicativity of ramification indices (`compK_spec`).
-/

open Polynomial
open Belyi.NoncriticalP1 (Pt Qbar ElemMap evalComp ramIdxComp zeroOneInf)

namespace Belyi.CurveField.Noncritical

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

variable (K) in
/-- A curve field has infinitely many places. -/
theorem infinite_place : Infinite (Place K) := by
  obtain ⟨t, ht⟩ := exists_transcendental K
  have hq : ∀ q : ℚ, Transcendental ℚ (t - algebraMap ℚ K q) := fun q ↦ by
    have := transcendental_aeval ht (p := X - C q) (by rw [natDegree_X_sub_C]; exact one_pos)
    simpa using this
  choose P hP using fun q ↦ Place.exists_ord_pos (hq q)
  refine Infinite.of_injective P fun q q' hqq' ↦ ?_
  by_contra hne
  have h1 := hP q
  have h2 := hP q'
  rw [← hqq'] at h2
  have hsum : (t - algebraMap ℚ K q) + -(t - algebraMap ℚ K q') = algebraMap ℚ K (q' - q) := by
    rw [map_sub]; ring
  have hsum0 : (t - algebraMap ℚ K q) + -(t - algebraMap ℚ K q') ≠ 0 := by
    rw [hsum, Ne, map_eq_zero_iff _ (algebraMap ℚ K).injective, sub_eq_zero]
    exact Ne.symm hne
  have := (P q).min_le_ord_add hsum0
  rw [hsum, Place.ord_algebraMap_rat, Place.ord_neg] at this
  omega

/-- The action of `σ ∈ Gal(ℚ̄/ℚ)` on algebraic points. -/
noncomputable def galPt (σ : Qbar ≃ₐ[ℚ] Qbar) (x : QbarPoint K) : QbarPoint K :=
  ⟨x.P, σ.toAlgHom.toRingHom.comp x.σ⟩

omit [IsCurveField K] in
theorem val_galPt (σ : Qbar ≃ₐ[ℚ] Qbar) (x : QbarPoint K) (φ : K) :
    val (galPt σ x) φ = (val x φ).map σ := by
  by_cases h : φ ∈ x.P.1
  · rw [val_of_mem (x := galPt σ x) h, val_of_mem h]
    rfl
  · rw [val_of_notMem (x := galPt σ x) h, val_of_notMem h]
    rfl

/-- **Theorem 2.5 of [Mochizuki, *Noncritical Belyi maps*] (with `S = ∅`)**: for every finite
set `T` of places of a curve field `K`, there is a Belyi map `φ ∈ K` (nonconstant, unramified
outside its cusps `φ⁻¹{0, 1, ∞}`) such that no place of `T` is a cusp of `φ`. -/
theorem exists_isBelyi_forall_notMem_cusps (T : Finset (Place K)) :
    ∃ φ : K, IsBelyi φ ∧ ∀ P ∈ T, P ∉ cusps φ := by
  classical
  haveI := infinite_place K
  -- Step 1: a function `ψ` with simple zeros exactly at `T' ⊇ T`
  obtain ⟨N₁, hN₁⟩ := Divisor.exists_polarDivisor_eq (K := K)
  obtain ⟨T', hTT', hcard⟩ :=
    Infinite.exists_superset_card_eq T (T.card + N₁.toNat + 1) (by omega)
  set A : Divisor K := ∑ P ∈ T', Finsupp.single P 1 with hA_def
  have hA : ∀ P, A P = if P ∈ T' then 1 else 0 := by
    intro P
    rw [hA_def, Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply]
  have hA0 : 0 ≤ A := fun P ↦ by rw [hA P]; split_ifs <;> simp
  have hdeg : N₁ ≤ A.deg := by
    have h1 : A.deg = ∑ P ∈ T', (P.deg : ℤ) := by
      rw [← Divisor.degHom_apply, hA_def, map_sum]
      simp
    have h2 : ∑ P ∈ T', (1 : ℤ) ≤ ∑ P ∈ T', (P.deg : ℤ) :=
      Finset.sum_le_sum fun P _ ↦ by exact_mod_cast P.deg_pos
    rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one] at h2
    push_cast at h2
    omega
  obtain ⟨f, hf⟩ := hN₁ A hA0 hdeg
  set ψ := f⁻¹ with hψ_def
  have hψT' : ∀ P ∈ T', P.ord ψ = 1 := by
    intro P hP
    have := congrArg (· P) hf
    simp only [Divisor.polarDivisor_apply, hA P, if_pos hP] at this
    rw [hψ_def, Place.ord_inv]
    omega
  have hψnT' : ∀ P ∉ T', P.ord ψ ≤ 0 := by
    intro P hP
    have := congrArg (· P) hf
    simp only [Divisor.polarDivisor_apply, hA P, if_neg hP] at this
    rw [hψ_def, Place.ord_inv]
    omega
  obtain ⟨P₀, hP₀⟩ : T'.Nonempty := Finset.card_pos.mp (by omega)
  have hψ : Transcendental ℚ ψ :=
    transcendental_of_ord_ne_zero (P := P₀) (by rw [hψT' P₀ hP₀]; exact one_ne_zero)
  have hψ0 : ψ ≠ 0 := ne_zero_of_transcendental hψ
  -- Step 2: the branch values of `ψ`
  have hR := finite_setOf_one_lt_ramIdx hψ
  have hX := QbarPoint.finite_setOf_mem hR
  set S : Finset Pt := insert none (hX.toFinset.image fun x ↦ val x ψ) with hS_def
  have hmemS : ∀ x : QbarPoint K, 1 < ramIdx x.P ψ → val x ψ ∈ S := fun x hx ↦
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hX.mem_toFinset.mpr hx, rfl⟩)
  have hSgal : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ z ∈ S, z.map σ ∈ S := by
    intro σ z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_insert_self _ _
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      rw [← val_galPt]
      exact hmemS (galPt σ x) (show 1 < ramIdx x.P ψ from hX.mem_toFinset.mp hx)
  have hval0 : ∀ x : QbarPoint K, x.P ∈ T' → val x ψ = NoncriticalP1.ratPt (some 0) := by
    intro x hx
    rw [NoncriticalP1.ratPt_some, NoncriticalP1.ofRat, Rat.cast_zero,
      val_eq_some_zero_iff hψ0, hψT' _ hx]
    exact one_pos
  have hτ : NoncriticalP1.ratPt (some 0) ∉ S := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact absurd h (by simp [NoncriticalP1.ratPt])
    · obtain ⟨x, hx, hxv⟩ := Finset.mem_image.mp h
      have hram : 1 < ramIdx x.P ψ := hX.mem_toFinset.mp hx
      rw [NoncriticalP1.ratPt_some, NoncriticalP1.ofRat, Rat.cast_zero,
        val_eq_some_zero_iff hψ0] at hxv
      have hxT : x.P ∈ T' := by
        by_contra hn; have := hψnT' _ hn; omega
      rw [ramIdx_of_ord_pos hxv, hψT' _ hxT] at hram
      exact lt_irrefl _ hram
  -- Step 3: the noncritical Belyi map of `ℙ¹`
  obtain ⟨hs, hhs⟩ := NoncriticalP1.exists_isNoncriticalBelyi S hSgal (some 0) hτ
  -- Step 4: `φ = H ∘ ψ`
  obtain ⟨x₀, -⟩ := QbarPoint.exists_P_eq P₀
  have hφ : Transcendental ℚ (compK hs ψ) := (compK_spec x₀ hs hψ).1
  refine ⟨compK hs ψ, ⟨hφ, fun P hP ↦ ?_⟩, fun P hPT ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := QbarPoint.exists_P_eq P
    obtain ⟨-, hv, he⟩ := compK_spec x hs hψ
    rw [mem_cusps_iff hφ x, hv]
    rw [he] at hP
    by_cases h1 : 1 < ramIdx x.P ψ
    · exact hhs.maps_to _ (Finset.mem_coe.mpr (hmemS x h1))
    · have hpos := ramIdx_pos hψ x.P
      have h1' : ramIdx x.P ψ = 1 := by omega
      rw [h1', one_mul] at hP
      exact hhs.unramified _ (by exact_mod_cast hP)
  · obtain ⟨x, rfl⟩ := QbarPoint.exists_P_eq P
    obtain ⟨-, hv, -⟩ := compK_spec x hs hψ
    rw [mem_cusps_iff hφ x, hv, hval0 x (hTT' hPT)]
    exact hhs.tau_notMem

end Belyi.CurveField.Noncritical
