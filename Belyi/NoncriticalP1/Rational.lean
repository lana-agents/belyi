/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.NoncriticalP1.ElemMap
import Belyi.Polynomial.ReductionZeroOne

/-!
# Noncritical Belyi maps for rational branch sets

This file proves the rational case of the `ℙ¹` part of
S. Mochizuki, *Noncritical Belyi maps*, Math. J. Okayama Univ. **46** (2004):
Lemma 2.1 (the separating properties of `f(x) = x^m (x - 1)^n`) and Lemma 2.2 (Belyi maps
noncritical at a prescribed rational point, for a rational branch set).

## Normalisation

Mochizuki works with sets `S ∋ 0, ∞` of non-negative rationals and `τ ≥ 2 · max S`, and
translates by the constant `f₀` after each application of `f`. We use the following
equivalent, slightly more symmetric normalisation, which is re-established by an affine
map before each step:

* every finite point `t` of the branch set satisfies `|t| ≤ 1`, and
* the distinguished point satisfies `τ ≥ 9`.

For a step, the affine map `x ↦ (x - a)/(b - a)` (`a = min T`, `b = max T`) moves `T` into
`[0, 1]` with `0, 1` in the image and `τ` to a point `≥ 4`; a third point `r = m/(m+n)`
lies in `(0, 1)`. The polynomial `f = X^m (X - 1)^n` has critical points `0, 1, r` only,
identifies `0` and `1` (so the branch set shrinks), maps `[0, 1]` into `[-1, 1]` and maps
the image of `τ` to a point `≥ 4 · 3 = 12 ≥ 9`.

## Main result

* `Belyi.NoncriticalP1.exists_isNoncriticalBelyi_rat`
-/

namespace Belyi.NoncriticalP1

open Polynomial

/-- The affine map `x ↦ (x - a)/(b - a)`, sending `a ↦ 0`, `b ↦ 1`, `∞ ↦ ∞`. -/
def affineMap (a b : ℚ) (h : a ≠ b) : ElemMap :=
  ElemMap.mob 1 (-a) 0 (b - a) (by
    have : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    simpa using this)

@[simp] lemma affineMap_none {a b : ℚ} (h : a ≠ b) : (affineMap a b h).apply none = none := by
  simp [affineMap, ElemMap.apply_mob_none]

@[simp] lemma affineMap_ramIdx {a b : ℚ} (h : a ≠ b) (z : Pt) :
    (affineMap a b h).ramIdx z = 1 := rfl

lemma IsNoncriticalBelyi.cons_affineMap {hs : List ElemMap} {S S' : Set Pt} {τ : Pt}
    {a b : ℚ} (h : a ≠ b) (hS : ∀ z ∈ S, (affineMap a b h).apply z ∈ S')
    (hg : IsNoncriticalBelyi hs S' ((affineMap a b h).apply τ)) :
    IsNoncriticalBelyi (affineMap a b h :: hs) S τ :=
  IsNoncriticalBelyi.cons _ hS (fun z hz => by simp at hz) hg

lemma affineMap_ofRat {a b : ℚ} (h : a ≠ b) (q : ℚ) :
    (affineMap a b h).apply (ofRat q) = ofRat ((q - a) / (b - a)) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  rw [affineMap, ElemMap.apply_mob_ofRat _ (by simpa using hba)]
  congr 1
  ring

/-- The polynomial `x^m (x - 1)^n` of Mochizuki's Lemma 2.1. -/
noncomputable def sepPoly (m n : ℕ) : ℚ[X] := X ^ m * (X - C 1) ^ n

lemma natDegree_sepPoly (m n : ℕ) : (sepPoly m n).natDegree = m + n := by
  rw [sepPoly, natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ (X_sub_C_ne_zero 1)),
    natDegree_pow, natDegree_pow, natDegree_X, natDegree_X_sub_C (1 : ℚ)]
  ring

lemma eval_sepPoly (m n : ℕ) (x : ℚ) : (sepPoly m n).eval x = x ^ m * (x - 1) ^ n := by
  simp [sepPoly]

lemma derivative_sepPoly (m n : ℕ) :
    derivative (sepPoly (m + 1) (n + 1)) =
      X ^ m * (X - C 1) ^ n * (((m : ℚ[X]) + 1) * (X - C 1) + ((n : ℚ[X]) + 1) * X) := by
  simp only [sepPoly, derivative_mul, derivative_pow, derivative_X, derivative_sub,
    derivative_C]
  push_cast
  simp only [C_add, C_1, C_eq_natCast]
  ring

/-- Property (b) of Lemma 2.1: the finite critical points of `x^m (x - 1)^n` are `0`, `1`
and `m/(m+n)`. -/
lemma crit_sepPoly {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) {z : Qbar}
    (hz : aeval z (derivative (sepPoly m n)) = 0) :
    z = 0 ∨ z = 1 ∨ z = (((m : ℚ) / ((m : ℚ) + n) : ℚ) : Qbar) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [derivative_sepPoly] at hz
  simp only [map_mul, map_pow, aeval_X, map_sub, map_one, map_add,
    map_natCast] at hz
  rcases mul_eq_zero.mp hz with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (pow_eq_zero_iff'.mp h).1
    · exact Or.inr (Or.inl (sub_eq_zero.mp (pow_eq_zero_iff'.mp h).1))
  · right; right
    have hden : ((m : Qbar) + 1 + ((n : Qbar) + 1)) ≠ 0 := by
      have : (((m + 1 + (n + 1) : ℕ) : Qbar)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at this
      exact this
    push_cast
    rw [eq_div_iff hden]
    linear_combination h

lemma abs_eval_sepPoly_le_one (m n : ℕ) {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    |(sepPoly m n).eval x| ≤ 1 := by
  rw [eval_sepPoly, abs_mul, abs_pow, abs_pow]
  have ha : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hb : |x - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  calc |x| ^ m * |x - 1| ^ n ≤ 1 * 1 :=
        mul_le_mul (pow_le_one₀ (abs_nonneg _) ha) (pow_le_one₀ (abs_nonneg _) hb)
          (by positivity) zero_le_one
    _ = 1 := one_mul 1

lemma twelve_le_eval_sepPoly {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) {x : ℚ} (hx : 4 ≤ x) :
    12 ≤ (sepPoly m n).eval x := by
  rw [eval_sepPoly]
  have h1 : x ≤ x ^ m := le_self_pow₀ (by linarith) hm
  have h2 : x - 1 ≤ (x - 1) ^ n := le_self_pow₀ (by linarith) hn
  nlinarith

/-- **Lemma 2.2 of Mochizuki (rational case), normalised**: if `T ⊆ [-1, 1]` is a finite set
of rationals and `τ ≥ 9` is rational, there is a composite of elementary maps mapping
`T ∪ {∞}` into `{0, 1, ∞}`, `τ` outside `{0, 1, ∞}`, unramified over `ℙ¹ ∖ {0, 1, ∞}`. -/
theorem exists_isNoncriticalBelyi_rat (T : Finset ℚ) (τ : ℚ) (hT : ∀ t ∈ T, |t| ≤ 1)
    (hτ : 9 ≤ τ) :
    ∃ hs : List ElemMap, IsNoncriticalBelyi hs (insert none (ofRat '' (T : Set ℚ))) (ofRat τ) := by
  induction h : T.card using Nat.strong_induction_on generalizing T τ with
  | _ N ihN =>
  have hτT : ∀ t ∈ T, t < τ := fun t ht => by
    have := (abs_le.mp (hT t ht)).2; linarith
  by_cases hsmall : T.card ≤ 2
  · -- base case: an affine map sends `T` into `{0, 1}`
    obtain ⟨a, b, hab, hTab, hτa, hτb⟩ : ∃ a b : ℚ, a ≠ b ∧ T ⊆ {a, b} ∧ τ ≠ a ∧ τ ≠ b := by
      interval_cases hc : T.card
      · exact ⟨2, 3, by norm_num, by simp [Finset.card_eq_zero.mp hc], by linarith,
          by linarith⟩
      · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
        have ha1 : |a| ≤ 1 := hT a (by simp [ha])
        have ha2 : a ≠ 2 := by
          intro h2; rw [h2] at ha1; norm_num at ha1
        exact ⟨a, 2, ha2, by simp [ha], (hτT a (by simp [ha])).ne', by linarith⟩
      · obtain ⟨a, b, hab, hTe⟩ := Finset.card_eq_two.mp hc
        exact ⟨a, b, hab, hTe.le, (hτT a (by simp [hTe])).ne', (hτT b (by simp [hTe])).ne'⟩
    refine ⟨[affineMap a b hab], IsNoncriticalBelyi.cons_affineMap _ (S' := zeroOneInf) ?_ ?_⟩
    · rintro z (rfl | ⟨t, ht, rfl⟩)
      · simp [affineMap_none]
      · rw [affineMap_ofRat, ofRat_mem_zeroOneInf]
        have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
        rcases Finset.mem_insert.mp (hTab ht) with rfl | ht'
        · simp
        · rw [Finset.mem_singleton.mp ht', div_self hba]; simp
    · refine IsNoncriticalBelyi.nil subset_rfl ?_
      rw [affineMap_ofRat, ofRat_mem_zeroOneInf]
      have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
      rintro (h0 | h1)
      · rw [div_eq_zero_iff] at h0
        rcases h0 with h0 | h0
        · exact hτa (sub_eq_zero.mp h0)
        · exact hba h0
      · rw [div_eq_one_iff_eq hba] at h1
        exact hτb (by linarith)
  · -- inductive step: `#T ≥ 3`
    push Not at hsmall
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    set a := T.min' hne with ha
    set b := T.max' hne with hb
    have hab : a < b := T.min'_lt_max'_of_card (by omega)
    obtain ⟨s₀, hs₀⟩ : ((T.erase a).erase b).Nonempty := by
      rw [← Finset.card_pos]
      have h1 := Finset.pred_card_le_card_erase (a := a) (s := T)
      have h2 := Finset.pred_card_le_card_erase (a := b) (s := T.erase a)
      omega
    have hs₀b : s₀ ≠ b := (Finset.mem_erase.mp hs₀).1
    have hs₀a : s₀ ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hs₀).2).1
    have hs₀T : s₀ ∈ T := (Finset.mem_erase.mp (Finset.mem_erase.mp hs₀).2).2
    have hs₀l : a < s₀ := lt_of_le_of_ne (T.min'_le s₀ hs₀T) (Ne.symm hs₀a)
    have hs₀r : s₀ < b := lt_of_le_of_ne (T.le_max' s₀ hs₀T) hs₀b
    have hba : 0 < b - a := sub_pos.mpr hab
    -- the normalised set `T₁ = μ(T) ⊆ [0, 1]`
    set μ : ℚ → ℚ := fun t => (t - a) / (b - a) with hμ
    have hμ01 : ∀ t ∈ T, 0 ≤ μ t ∧ μ t ≤ 1 := by
      intro t ht
      have h1 : a ≤ t := T.min'_le t ht
      have h2 : t ≤ b := T.le_max' t ht
      refine ⟨div_nonneg (by linarith) hba.le, (div_le_one hba).mpr (by linarith)⟩
    have hμa : μ a = 0 := by simp [hμ]
    have hμb : μ b = 1 := by simp [hμ, div_self hba.ne']
    set x₀ := μ s₀ with hx₀
    have hx₀pos : 0 < x₀ := div_pos (by linarith) hba
    have hx₀lt : x₀ < 1 := (div_lt_one hba).mpr (by linarith)
    obtain ⟨m, n, hm, hn, hmn⟩ := exists_eq_num_div_num_add_den hx₀pos hx₀lt
    set f := sepPoly m n with hf
    have hfdeg : 0 < f.natDegree := by rw [hf, natDegree_sepPoly]; omega
    -- the new data
    classical
    set T₂ : Finset ℚ := T.image fun t => f.eval (μ t) with hT₂
    set τ₁ := μ τ with hτ₁
    have hτ₁4 : 4 ≤ τ₁ := by
      have h1 : |a| ≤ 1 := hT a (T.min'_mem hne)
      have h2 : |b| ≤ 1 := hT b (T.max'_mem hne)
      have h3 : b - a ≤ 2 := by
        have := abs_le.mp h1; have := abs_le.mp h2; linarith
      rw [hτ₁, hμ, le_div_iff₀ hba]
      have := abs_le.mp h1
      linarith
    have hT₂bd : ∀ t ∈ T₂, |t| ≤ 1 := by
      intro y hy
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
      exact abs_eval_sepPoly_le_one m n (hμ01 t ht).1 (hμ01 t ht).2
    have hτ₂ : 9 ≤ f.eval τ₁ := by
      have := twelve_le_eval_sepPoly hm hn hτ₁4
      linarith
    have hT₂card : T₂.card < N := by
      have hsub : T₂ ⊆ (T.erase b).image fun t => f.eval (μ t) := by
        intro y hy
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
        by_cases htb : t = b
        · refine Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr ⟨hab.ne, T.min'_mem hne⟩, ?_⟩
          rw [htb, hμa, hμb, hf, eval_sepPoly, eval_sepPoly]
          simp [zero_pow hm, zero_pow hn]
        · exact Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨htb, ht⟩, rfl⟩
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_image_le (s := T.erase b) (f := fun t => f.eval (μ t))
      have h3 := Finset.card_erase_of_mem (T.max'_mem hne)
      rw [← hb] at h3
      omega
    obtain ⟨hs, hhs⟩ := ihN T₂.card (h ▸ hT₂card) T₂ (f.eval τ₁) hT₂bd hτ₂ rfl
    refine ⟨affineMap a b hab.ne :: ElemMap.poly f hfdeg :: hs, ?_⟩
    refine IsNoncriticalBelyi.cons_affineMap _
      (S' := insert none (ofRat '' ((T.image μ : Finset ℚ) : Set ℚ))) ?_ ?_
    · rintro z (rfl | ⟨t, ht, rfl⟩)
      · simp [affineMap_none]
      · rw [affineMap_ofRat]
        exact Set.mem_insert_of_mem _ ⟨μ t, by simpa using ⟨t, ht, rfl⟩, rfl⟩
    · rw [affineMap_ofRat]
      refine IsNoncriticalBelyi.cons_poly hfdeg (S' := insert none (ofRat '' (T₂ : Set ℚ))) ?_
        (Set.mem_insert _ _) ?_ ?_
      · rintro z (rfl | ⟨t, ht, rfl⟩)
        · simp
        · rw [ElemMap.apply_poly_ofRat]
          refine Set.mem_insert_of_mem _ ⟨f.eval t, ?_, rfl⟩
          obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
          exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨t', ht', rfl⟩)
      · intro z hz
        have hval : ∀ t ∈ T, some (aeval ((μ t : ℚ) : Qbar) f) ∈
            insert none (ofRat '' (T₂ : Set ℚ)) := by
          intro t ht
          refine Set.mem_insert_of_mem _ ⟨f.eval (μ t),
            Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨t, ht, rfl⟩), ?_⟩
          rw [← ElemMap.apply_poly_ofRat hfdeg]
          rfl
        rcases crit_sepPoly hm hn hz with rfl | rfl | rfl
        · have := hval a (T.min'_mem hne)
          rwa [hμa, Rat.cast_zero] at this
        · have := hval b (T.max'_mem hne)
          rwa [hμb, Rat.cast_one] at this
        · have := hval s₀ hs₀T
          rwa [← hx₀, hmn] at this
      · rw [ElemMap.apply_poly_ofRat]
        exact hhs

end Belyi.NoncriticalP1
