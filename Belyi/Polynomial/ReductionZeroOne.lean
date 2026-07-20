/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Polynomial.Lambda

/-!
# Belyi reduction II: moving rational branch points into `{0, 1}`

This file proves statement **B7** of `references/proof-outline.md`, the second reduction
step of Belyi's theorem: for every finite set `S ⊆ ℚ` there is a non-constant polynomial
`g ∈ ℚ[X]` such that `g(S) ⊆ {0, 1}` and all critical values of `g` lie in `{0, 1}`.

## Main result

* `Belyi.exists_eval_mem_and_critVal_mem`

## Design note: no Möbius maps, no point at infinity

The issue specification (taxis #50) proposed working with rational functions acting on
`OnePoint ℚ̄` and normalizing with Möbius transformations. This is unnecessary: since
polynomials fix `∞` and `∞` is always an allowed branch point, it suffices to normalize
with the *affine* map `t ↦ (t - a)/(b - a)` sending the minimum `a` and maximum `b` of
`S` to `0` and `1`. The whole reduction then happens inside `ℚ[X]`, and the geometric
bridge (statement B4, taxis #51) only ever needs to identify branch loci of *polynomial*
maps `ℙ¹ ⟶ ℙ¹`, namely `Branch g = CritVal g ∪ {∞}`.

## Proof sketch

Induct on `#S`. If `#S ≤ 2`, an affine map sends `S` into `{0, 1}` and has no critical
values. Otherwise normalize by the affine map `μ` with `μ(min S) = 0`, `μ(max S) = 1`;
any third element lands at some `x = m/(m+n) ∈ (0, 1)`. The Belyi polynomial `λ_{m,n}`
(see `Belyi.Polynomial.Lambda`) maps `0, 1 ↦ 0` and `x ↦ 1`, and its critical values lie
in `{0, 1}`; since `0` and `1` collide, `#(λ_{m,n}(μ(S))) < #S` and we can recurse. The
critical values of the composite are controlled by `Belyi.critVal_comp_subset`, and land
in the recursive image of `{0, 1} ⊆ λ_{m,n}(μ(S))`.
-/

namespace Belyi

open Polynomial

/-- Writing a rational number in `(0, 1)` as `m/(m+n)` with `m, n ≥ 1`. -/
lemma exists_eq_num_div_num_add_den {x : ℚ} (h0 : 0 < x) (h1 : x < 1) :
    ∃ m n : ℕ, m ≠ 0 ∧ n ≠ 0 ∧ x = (m : ℚ) / ((m : ℚ) + (n : ℚ)) := by
  have hnum : 0 < x.num := Rat.num_pos.mpr h0
  have hlt : x.num < x.den := Rat.num_lt_denom_iff.mpr h1
  have hm : x.num.toNat ≠ 0 := by omega
  refine ⟨x.num.toNat, x.den - x.num.toNat, hm, by omega, ?_⟩
  have h2 : ((x.num.toNat : ℕ) : ℚ) = (x.num : ℚ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (Int.toNat_of_nonneg hnum.le)
  have h3 : ((x.num.toNat : ℕ) : ℚ) + ((x.den - x.num.toNat : ℕ) : ℚ) = (x.den : ℚ) := by
    rw [← Nat.cast_add]
    congr 1
    omega
  rw [h3, h2, Rat.num_div_den]

/-- The affine polynomial `t ↦ (t - a)/(b - a)` sending `a ↦ 0` and `b ↦ 1`. -/
noncomputable def affine (a b : ℚ) : ℚ[X] :=
  C ((b - a)⁻¹) * (X - C a)

lemma affine_eval (a b t : ℚ) : (affine a b).eval t = (t - a) / (b - a) := by
  simp [affine, div_eq_inv_mul]

@[simp]
lemma affine_eval_left (a b : ℚ) : (affine a b).eval a = 0 := by
  simp [affine_eval]

lemma affine_eval_right {a b : ℚ} (h : a ≠ b) : (affine a b).eval b = 1 := by
  rw [affine_eval, div_self (sub_ne_zero.mpr (Ne.symm h))]

lemma natDegree_affine {a b : ℚ} (h : a ≠ b) : (affine a b).natDegree = 1 := by
  rw [affine, natDegree_C_mul (inv_ne_zero (sub_ne_zero.mpr (Ne.symm h))), natDegree_X_sub_C]

lemma critVal_affine (K : Type*) [Field K] [Algebra ℚ K] {a b : ℚ} (h : a ≠ b) :
    critVal K (affine a b) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨y, ⟨-, hy⟩, -⟩ := mem_critVal_iff.mp hx
  rw [affine, derivative_C_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
    mul_one] at hy
  simp only [aeval_C] at hy
  exact (map_ne_zero_iff _ (algebraMap ℚ K).injective).mpr
    (inv_ne_zero (sub_ne_zero.mpr (Ne.symm h))) hy

variable {K : Type*} [Field K] [Algebra ℚ K]

private lemma reduction_key : ∀ (N : ℕ) (S : Finset ℚ), S.card ≤ N →
    ∃ g : ℚ[X], g.natDegree ≠ 0 ∧
      (∀ s ∈ S, g.eval s = 0 ∨ g.eval s = 1) ∧
      (∀ x ∈ critVal K g, x = 0 ∨ x = 1) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
  intro S hcard
  by_cases hsmall : S.card ≤ 2
  · -- base case: `S ⊆ {a, b}` for some `a ≠ b`; the affine map finishes
    obtain ⟨a, b, hab, hS⟩ : ∃ a b : ℚ, a ≠ b ∧ S ⊆ {a, b} := by
      interval_cases h : S.card
      · exact ⟨0, 1, by norm_num, by simp [Finset.card_eq_zero.mp h]⟩
      · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
        exact ⟨a, a + 1, by norm_num, by simp [ha]⟩
      · obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp h
        exact ⟨a, b, hab, hS.le⟩
    refine ⟨affine a b, by rw [natDegree_affine hab]; omega, fun s hs => ?_, fun x hx => ?_⟩
    · rcases Finset.mem_insert.mp (hS hs) with h' | hs'
      · rw [h']
        exact Or.inl (affine_eval_left a b)
      · rw [Finset.mem_singleton.mp hs']
        exact Or.inr (affine_eval_right hab)
    · rw [critVal_affine K hab] at hx
      simp at hx
  · -- inductive step: `#S ≥ 3`
    push Not at hsmall
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    set a := S.min' hne with ha
    set b := S.max' hne with hb
    have hab : a < b := S.min'_lt_max'_of_card (by omega)
    -- a third element of `S`, strictly between `a` and `b`
    obtain ⟨s₀, hs₀⟩ : ((S.erase a).erase b).Nonempty := by
      rw [← Finset.card_pos]
      have h1 := Finset.pred_card_le_card_erase (a := a) (s := S)
      have h2 := Finset.pred_card_le_card_erase (a := b) (s := S.erase a)
      omega
    have hs₀b : s₀ ≠ b := (Finset.mem_erase.mp hs₀).1
    have hs₀a : s₀ ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hs₀).2).1
    have hs₀S : s₀ ∈ S := (Finset.mem_erase.mp (Finset.mem_erase.mp hs₀).2).2
    have hs₀l : a < s₀ := lt_of_le_of_ne (S.min'_le s₀ hs₀S) (Ne.symm hs₀a)
    have hs₀r : s₀ < b := lt_of_le_of_ne (S.le_max' s₀ hs₀S) hs₀b
    -- normalize: `T = μ(S)` with `0, 1 ∈ T` and `x₀ ∈ T ∩ (0, 1)`
    classical
    set T : Finset ℚ := S.image fun t => (affine a b).eval t with hT
    have h0T : (0 : ℚ) ∈ T :=
      hT ▸ Finset.mem_image.mpr ⟨a, S.min'_mem hne, affine_eval_left a b⟩
    have h1T : (1 : ℚ) ∈ T :=
      hT ▸ Finset.mem_image.mpr ⟨b, S.max'_mem hne, affine_eval_right hab.ne⟩
    set x₀ : ℚ := (affine a b).eval s₀ with hx₀
    have hx₀T : x₀ ∈ T := hT ▸ Finset.mem_image.mpr ⟨s₀, hs₀S, rfl⟩
    have hx₀pos : 0 < x₀ := by
      rw [hx₀, affine_eval]
      exact div_pos (by linarith) (by linarith)
    have hx₀lt : x₀ < 1 := by
      rw [hx₀, affine_eval, div_lt_one (by linarith)]
      linarith
    obtain ⟨m, n, hm, hn, hmn⟩ := exists_eq_num_div_num_add_den hx₀pos hx₀lt
    set L : ℚ[X] := lambda m n with hL
    -- the image `S₁ = L(T)` is strictly smaller: `0` and `1` collide
    set S₁ : Finset ℚ := T.image fun t => L.eval t with hS₁
    have hS₁sub : S₁ ⊆ (T.erase 1).image fun t => L.eval t := by
      intro y hy
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
      by_cases h1 : t = 1
      · subst h1
        refine Finset.mem_image.mpr ⟨0, Finset.mem_erase.mpr ⟨by norm_num, h0T⟩, ?_⟩
        rw [lambda_eval_zero hm, lambda_eval_one hn]
      · exact Finset.mem_image.mpr ⟨t, Finset.mem_erase.mpr ⟨h1, ht⟩, rfl⟩
    have hS₁card : S₁.card ≤ N - 1 := by
      have h1 : S₁.card ≤ (T.erase 1).card := le_trans (Finset.card_le_card hS₁sub)
        Finset.card_image_le
      have h2 : (T.erase 1).card = T.card - 1 := Finset.card_erase_of_mem h1T
      have h3 : T.card ≤ S.card := Finset.card_image_le
      omega
    -- recurse and compose
    obtain ⟨g₁, hg₁ne, hg₁S, hg₁crit⟩ := ihN (N - 1) (by omega) S₁ hS₁card
    have hLdeg : L.natDegree ≠ 0 := by rw [hL, natDegree_lambda hm hn]; omega
    have hAdeg : (affine a b).natDegree = 1 := natDegree_affine hab.ne
    have hLA : (L.comp (affine a b)).natDegree ≠ 0 := by
      rw [natDegree_comp, hAdeg, mul_one]; exact hLdeg
    have h0S₁ : (0 : ℚ) ∈ S₁ := by
      refine hS₁ ▸ Finset.mem_image.mpr ⟨1, h1T, lambda_eval_one hn⟩
    have h1S₁ : (1 : ℚ) ∈ S₁ := by
      refine hS₁ ▸ Finset.mem_image.mpr ⟨x₀, hx₀T, ?_⟩
      rw [hmn, hL, lambda_eval_mid hm hn]
    refine ⟨g₁.comp (L.comp (affine a b)), ?_, fun s hs => ?_, fun x hx => ?_⟩
    · rw [natDegree_comp]
      exact Nat.mul_ne_zero hg₁ne hLA
    · rw [eval_comp, eval_comp]
      exact hg₁S _ <| hS₁ ▸ Finset.mem_image.mpr
        ⟨(affine a b).eval s, hT ▸ Finset.mem_image_of_mem _ hs, rfl⟩
    · have hsub := critVal_comp_subset (K := K) (derivative_ne_zero.mpr hg₁ne)
        (derivative_ne_zero.mpr hLA) hx
      rcases Finset.mem_union.mp hsub with hx' | hx'
      · -- critical value of the inner composite, hence of `L`, hence `g₁` of `0` or `1`
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx'
        have hyL : y ∈ critVal K L := by
          have h2 := critVal_comp_subset (K := K) (derivative_ne_zero.mpr hLdeg)
            (derivative_ne_zero.mpr (by rw [hAdeg]; omega : (affine a b).natDegree ≠ 0)) hy
          rcases Finset.mem_union.mp h2 with h3 | h3
          · rw [critVal_affine K hab.ne] at h3
            simp at h3
          · exact h3
        have hy01 : y = 0 ∨ y = 1 := critVal_lambda hm hn hyL
        rcases hy01 with rfl | rfl
        · rw [show (0 : K) = algebraMap ℚ K 0 by simp,
            aeval_algebraMap_apply_eq_algebraMap_eval]
          rcases hg₁S 0 h0S₁ with h4 | h4 <;> rw [h4] <;> simp
        · rw [show (1 : K) = algebraMap ℚ K 1 by simp,
            aeval_algebraMap_apply_eq_algebraMap_eval]
          rcases hg₁S 1 h1S₁ with h4 | h4 <;> rw [h4] <;> simp
      · exact hg₁crit _ hx'

/-- **Belyi reduction II** (statement B7 of `references/proof-outline.md`): for every
finite set `S ⊆ ℚ` there is a non-constant polynomial `g ∈ ℚ[X]` with `g(S) ⊆ {0, 1}`
all of whose critical values (in any field extension `K` of `ℚ`) lie in `{0, 1}`. -/
theorem exists_eval_mem_and_critVal_mem (S : Finset ℚ) :
    ∃ g : ℚ[X], g.natDegree ≠ 0 ∧
      (∀ s ∈ S, g.eval s = 0 ∨ g.eval s = 1) ∧
      (∀ x ∈ critVal K g, x = 0 ∨ x = 1) :=
  reduction_key S.card S le_rfl

end Belyi
