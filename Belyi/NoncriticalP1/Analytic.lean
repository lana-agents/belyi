/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.NoncriticalP1.ElemMap

/-!
# Archimedean estimates for noncritical Belyi maps

This file collects the complex-analytic (in fact elementary) estimates behind
S. Mochizuki, *Noncritical Belyi maps*, Math. J. Okayama Univ. **46** (2004),
Lemmas 2.3 and 2.4. Absolute values of algebraic numbers are taken through a fixed
embedding `ι : ℚ̄ → ℂ` (`Belyi.NoncriticalP1.ι`, obtained from `IsAlgClosed.lift`).

## Main results

* `Belyi.NoncriticalP1.exists_mob_normalize` (**Lemma 2.3**): for a finite set `T ⊆ ℚ̄`,
  a rational `τ ∉ T` and a rational `C > 0`, a Möbius transformation
  `x ↦ C ε / (x - (τ - ε))` with `ε ∈ ℚ` small sends `τ ↦ C`, `∞ ↦ 0`, and `T` into the
  closed unit disc (with respect to `ι`).
* `Belyi.NoncriticalP1.norm_aeval_le`, `Belyi.NoncriticalP1.norm_aeval_crit_le`,
  `Belyi.NoncriticalP1.pow_le_abs_eval_nine` (the estimates in the proof of **Lemma 2.4**):
  if all roots of a monic `f ∈ ℚ[X]` of degree `d` lie in the unit disc, then `|f| ≤ 2ᵈ` on
  the unit disc and at every critical point of `f` (the critical points lie in the unit
  disc by the Gauss–Lucas theorem), while `|f(9)| ≥ 8ᵈ`.
-/

namespace Belyi.NoncriticalP1

open Polynomial

/-- A fixed embedding `ℚ̄ → ℂ`, used to measure absolute values of algebraic numbers. -/
noncomputable def ι : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift

lemma ι_injective : Function.Injective ι := ι.toRingHom.injective

@[simp] lemma ι_ratCast (q : ℚ) : ι (q : Qbar) = (q : ℂ) := map_ratCast ι q

@[simp] lemma norm_ι_ratCast (q : ℚ) : ‖ι (q : Qbar)‖ = |(q : ℝ)| := by
  rw [ι_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

/-- **Lemma 2.3 of Mochizuki** (separation of collections of points), in the normalised form
used here: for a finite `T ⊆ ℚ̄`, a rational point `τ ∉ T` and a rational `C > 0`, there is a
Möbius transformation with rational coefficients sending `τ ↦ C`, `∞ ↦ 0`, and every point
of `T` to a finite point in the closed unit disc. -/
theorem exists_mob_normalize (T : Finset Qbar) {τ : ℚ} (hτ : (τ : Qbar) ∉ T) {C : ℚ}
    (hC : 0 < C) :
    ∃ u : ElemMap, (∀ z, u.ramIdx z = 1) ∧ u.apply (ofRat τ) = ofRat C ∧
      u.apply none = ofRat 0 ∧ ∀ t ∈ T, ∃ y, u.apply (some t) = some y ∧ ‖ι y‖ ≤ 1 := by
  -- a positive lower bound `δ` for the distances `|t - τ|`, `t ∈ T`
  obtain ⟨δ, hδ, hδT⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ T, δ ≤ ‖ι t - (τ : ℂ)‖ := by
    rcases T.eq_empty_or_nonempty with hT | hT
    · exact ⟨1, one_pos, by simp [hT]⟩
    · obtain ⟨t₀, ht₀, hmin⟩ := T.exists_min_image (fun t => ‖ι t - (τ : ℂ)‖) hT
      refine ⟨_, ?_, hmin⟩
      rw [norm_pos_iff, sub_ne_zero, ← ι_ratCast]
      intro h
      exact hτ (ι_injective h ▸ ht₀)
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  obtain ⟨ε, hε0, hεδ⟩ := exists_rat_btwn (div_pos hδ (by linarith : (0 : ℝ) < C + 1))
  have hε0' : (0 : ℚ) < ε := by exact_mod_cast hε0
  have hεδ' : (C + 1) * (ε : ℝ) < δ := by
    rw [lt_div_iff₀ (by linarith)] at hεδ; linarith
  have hdet : (0 : ℚ) * -(τ - ε) - C * ε * 1 ≠ 0 := by
    have : C * ε ≠ 0 := by positivity
    simpa using this
  refine ⟨ElemMap.mob 0 (C * ε) 1 (-(τ - ε)) hdet, fun z => rfl, ?_, ?_, ?_⟩
  · rw [ElemMap.apply_mob_ofRat _ (by simp [hε0'.ne'])]
    congr 1
    rw [show (0 : ℚ) * τ + C * ε = C * ε by ring, show (1 : ℚ) * τ + -(τ - ε) = ε by ring,
      mul_div_assoc, div_self hε0'.ne', mul_one]
  · simp [ElemMap.apply_mob_none, ofRat]
  · intro t ht
    have hdist : δ - ε ≤ ‖ι t - ((τ - ε : ℚ) : ℂ)‖ := by
      have h1 := hδT t ht
      have h2 : ι t - (τ : ℂ) = (ι t - ((τ - ε : ℚ) : ℂ)) - (ε : ℂ) := by push_cast; ring
      have h3 := norm_sub_le (ι t - ((τ - ε : ℚ) : ℂ)) (ε : ℂ)
      rw [← h2] at h3
      have h4 : ‖(ε : ℂ)‖ = ε := by
        rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by exact_mod_cast hε0')]
      linarith
    have hpos : 0 < ‖ι t - ((τ - ε : ℚ) : ℂ)‖ := by nlinarith
    have hne : ((1 : ℚ) : Qbar) * t + ((-(τ - ε) : ℚ) : Qbar) ≠ 0 := by
      intro h0
      have : ι t - ((τ - ε : ℚ) : ℂ) = 0 := by
        have := congrArg ι h0
        simp only [map_add, map_mul, ι_ratCast, map_zero] at this
        push_cast at this ⊢
        linear_combination this
      rw [this, norm_zero] at hpos
      exact lt_irrefl _ hpos
    refine ⟨_, ElemMap.apply_mob_some_of_ne _ hne, ?_⟩
    have hval : ι ((((0 : ℚ) : Qbar) * t + ((C * ε : ℚ) : Qbar)) /
        (((1 : ℚ) : Qbar) * t + ((-(τ - ε) : ℚ) : Qbar))) =
        ((C * ε : ℚ) : ℂ) / (ι t - ((τ - ε : ℚ) : ℂ)) := by
      simp only [map_div₀, map_add, map_mul, ι_ratCast]
      push_cast
      ring
    rw [hval, norm_div, div_le_one hpos]
    have h5 : ‖((C * ε : ℚ) : ℂ)‖ = C * ε := by
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by exact_mod_cast mul_pos hC hε0')]
      push_cast; ring
    rw [h5]
    nlinarith

/-! ### Estimates for monic polynomials with roots in the unit disc -/

lemma norm_prod_sub_le (s : Multiset ℂ) (hs : ∀ ρ ∈ s, ‖ρ‖ ≤ 1) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(s.map fun ρ => w - ρ).prod‖ ≤ 2 ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ]
    have h1 : ‖w - a‖ ≤ 2 := by
      have := norm_sub_le w a
      have := hs a (Multiset.mem_cons_self a s)
      linarith
    have h2 := ih (fun ρ hρ => hs ρ (Multiset.mem_cons_of_mem hρ))
    rw [mul_comm ‖w - a‖]
    exact mul_le_mul h2 h1 (norm_nonneg _) (by positivity)

lemma pow_le_norm_prod_sub (s : Multiset ℂ) (hs : ∀ ρ ∈ s, ‖ρ‖ ≤ 1) {w : ℂ} (hw : 1 ≤ ‖w‖) :
    (‖w‖ - 1) ^ Multiset.card s ≤ ‖(s.map fun ρ => w - ρ).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ]
    have h1 : ‖w‖ - 1 ≤ ‖w - a‖ := by
      have := norm_sub_norm_le w a
      have := hs a (Multiset.mem_cons_self a s)
      linarith
    have h2 := ih (fun ρ hρ => hs ρ (Multiset.mem_cons_of_mem hρ))
    rw [mul_comm ‖w - a‖]
    exact mul_le_mul h2 h1 (by linarith) (norm_nonneg _)

/-- The roots in `ℚ̄` (with multiplicity) of a rational polynomial. -/
noncomputable def qroots (f : ℚ[X]) : Multiset Qbar := (f.map (algebraMap ℚ Qbar)).roots

lemma card_qroots (f : ℚ[X]) : Multiset.card (qroots f) = f.natDegree := by
  rw [qroots, IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

lemma mem_qroots {f : ℚ[X]} (hf : f ≠ 0) {ρ : Qbar} : ρ ∈ qroots f ↔ aeval ρ f = 0 := by
  rw [qroots, mem_roots (Polynomial.map_ne_zero hf), IsRoot, eval_map_algebraMap]

lemma map_eq_prod_qroots {f : ℚ[X]} (hf : f.Monic) :
    f.map (algebraMap ℚ Qbar) = ((qroots f).map fun ρ => X - C ρ).prod :=
  (prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hf.map _)
    IsAlgClosed.card_roots_eq_natDegree).symm

lemma ι_aeval_eq_prod {f : ℚ[X]} (hf : f.Monic) (z : Qbar) :
    ι (aeval z f) = (((qroots f).map ι).map fun ρ => ι z - ρ).prod := by
  rw [← eval_map_algebraMap, map_eq_prod_qroots hf, eval_multiset_prod, Multiset.map_map,
    map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro ρ _
  simp

lemma map_complex_eq_prod {f : ℚ[X]} (hf : f.Monic) :
    f.map (algebraMap ℚ ℂ) = (((qroots f).map ι).map fun ρ => X - C ρ).prod := by
  have h : algebraMap ℚ ℂ = (ι : Qbar →+* ℂ).comp (algebraMap ℚ Qbar) := by
    ext q; simp
  rw [h, ← Polynomial.map_map, map_eq_prod_qroots hf, Polynomial.map_multiset_prod,
    Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro ρ _
  simp

variable {f : ℚ[X]}

/-- If all roots of the monic `f` lie in the unit disc, then `|f| ≤ 2ᵈ` on the unit disc. -/
lemma norm_aeval_le (hf : f.Monic) (hroots : ∀ ρ ∈ qroots f, ‖ι ρ‖ ≤ 1) {z : Qbar}
    (hz : ‖ι z‖ ≤ 1) : ‖ι (aeval z f)‖ ≤ 2 ^ f.natDegree := by
  rw [ι_aeval_eq_prod hf, ← card_qroots, ← Multiset.card_map ι]
  refine norm_prod_sub_le _ ?_ hz
  intro ρ hρ
  obtain ⟨ρ, hρ', rfl⟩ := Multiset.mem_map.mp hρ
  exact hroots ρ hρ'

/-- If all roots of the monic `f` lie in the unit disc, then `|f(9)| ≥ 8ᵈ`. -/
lemma pow_le_abs_eval_nine (hf : f.Monic) (hroots : ∀ ρ ∈ qroots f, ‖ι ρ‖ ≤ 1) :
    (8 : ℝ) ^ f.natDegree ≤ |((f.eval 9 : ℚ) : ℝ)| := by
  have h9 : ‖ι ((9 : ℚ) : Qbar)‖ = 9 := by rw [norm_ι_ratCast]; norm_num
  have hbd := pow_le_norm_prod_sub ((qroots f).map ι) ?_ (w := ι ((9 : ℚ) : Qbar))
    (by rw [h9]; norm_num)
  · rw [← ι_aeval_eq_prod hf, h9, Multiset.card_map, card_qroots] at hbd
    have he : aeval ((9 : ℚ) : Qbar) f = ((f.eval 9 : ℚ) : Qbar) := by
      have := aeval_algebraMap_apply_eq_algebraMap_eval (A := Qbar) (p := f) (9 : ℚ)
      simpa only [eq_ratCast] using this
    rw [he, norm_ι_ratCast] at hbd
    norm_num at hbd
    exact hbd
  · intro ρ hρ
    obtain ⟨ρ, hρ', rfl⟩ := Multiset.mem_map.mp hρ
    exact hroots ρ hρ'

/-- Gauss–Lucas: if all roots of the monic `f` of positive degree lie in the unit disc, so do
all critical points of `f`. -/
lemma norm_le_one_of_aeval_derivative (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hroots : ∀ ρ ∈ qroots f, ‖ι ρ‖ ≤ 1) {c : Qbar} (hc : aeval c (derivative f) = 0) :
    ‖ι c‖ ≤ 1 := by
  set F : ℂ[X] := f.map (algebraMap ℚ ℂ) with hF
  have hFdeg : 0 < F.degree := by
    rw [hF, degree_map]; exact natDegree_pos_iff_degree_pos.mp hdeg
  have hF0 : F ≠ 0 := by rintro h; rw [h] at hFdeg; simp at hFdeg
  have hderiv : derivative F ≠ 0 := by
    rw [hF, derivative_map]
    refine Polynomial.map_ne_zero ?_
    intro h0
    have := derivative_eq_zero.mp h0
    omega
  have hmem : ι c ∈ (derivative F).rootSet ℂ := by
    rw [mem_rootSet]
    refine ⟨hderiv, ?_⟩
    rw [hF, derivative_map, aeval_map_algebraMap, aeval_algHom_apply, hc, map_zero]
  have hsub : F.rootSet ℂ ⊆ Metric.closedBall 0 1 := by
    intro x hx
    rw [mem_rootSet] at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    have h2 := hx.2
    rw [coe_aeval_eq_eval, hF, map_complex_eq_prod hf, eval_multiset_prod,
      Multiset.map_map] at h2
    obtain ⟨y, hy, hy0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h2)
    obtain ⟨ρ, hρ, rfl⟩ := Multiset.mem_map.mp hy
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C] at hy0
    rw [sub_eq_zero.mp hy0]
    exact hroots ρ hρ
  have := convexHull_min hsub (convex_closedBall 0 1)
    (rootSet_derivative_subset_convexHull_rootSet hFdeg hmem)
  rwa [Metric.mem_closedBall, dist_zero_right] at this

/-- At the critical points of a monic `f` whose roots lie in the unit disc, `|f| ≤ 2ᵈ`. -/
lemma norm_aeval_crit_le (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hroots : ∀ ρ ∈ qroots f, ‖ι ρ‖ ≤ 1) {c : Qbar} (hc : aeval c (derivative f) = 0) :
    ‖ι (aeval c f)‖ ≤ 2 ^ f.natDegree :=
  norm_aeval_le hf hroots (norm_le_one_of_aeval_derivative hf hdeg hroots hc)

end Belyi.NoncriticalP1
