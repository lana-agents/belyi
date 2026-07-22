/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Polynomial.ReductionRational
import Belyi.Polynomial.ReductionZeroOne

/-!
# Belyi's combined reduction

This file chains the two reduction steps of Belyi's descending induction into a single
statement (the composite of **B6** and **B7** of `references/proof-outline.md`): for every
finite set `S` of elements of a field `K` algebraic over `ℚ`, there is a non-constant
`g ∈ ℚ[X]` sending `S` into `{0, 1}` all of whose critical values lie in `{0, 1}`.

The forward direction of Belyi's theorem feeds this to the polynomial self-map of `ℙ¹`
(statement B4): the branch points of the composite `X → ℙ¹ → ℙ¹` then lie over `{0, 1, ∞}`.

* `Belyi.exists_aeval_mem_and_critVal_mem_zeroOne`.
-/

namespace Belyi

open Polynomial

variable {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]

/-- **Belyi's combined reduction** (the composite of B6 and B7 of
`references/proof-outline.md`): for every finite set `S ⊆ K` of algebraic points, there is a
non-constant polynomial `g ∈ ℚ[X]` mapping `S` into `{0, 1}` all of whose critical values
(in `K`) lie in `{0, 1}`.

Take `g₁` from reduction I, mapping `S` and its critical values into (the image of) `ℚ`;
collect those rational values into a finite set `S' ⊆ ℚ` and take `g₂` from reduction II
applied to `S'`. The composite `g₂ ∘ g₁` works: its values on `S` are `g₂` of rational
values in `S'`, and `critVal (g₂ ∘ g₁) ⊆ g₂(critVal g₁) ∪ critVal g₂` reduces to `{0, 1}`
in the same way. -/
theorem exists_aeval_mem_and_critVal_mem_zeroOne (S : Finset K) :
    ∃ g : ℚ[X], g.natDegree ≠ 0 ∧
      (∀ s ∈ S, aeval s g = 0 ∨ aeval s g = 1) ∧
      (∀ x ∈ critVal K g, x = 0 ∨ x = 1) := by
  classical
  obtain ⟨g₁, hg₁ne, hg₁S, hg₁crit⟩ := exists_aeval_mem_range_and_critVal_mem_range (K := K) S
  have hφinj : Function.Injective (algebraMap ℚ K) := (algebraMap ℚ K).injective
  -- the finite set of rational values to feed to reduction II
  set T : Finset K := S.image (fun s => aeval s g₁) ∪ critVal K g₁ with hT
  obtain ⟨g₂, hg₂ne, hg₂S, hg₂crit⟩ :=
    exists_eval_mem_and_critVal_mem (K := K) (T.preimage (algebraMap ℚ K) hφinj.injOn)
  refine ⟨g₂.comp g₁, ?_, ?_, ?_⟩
  · rw [natDegree_comp]; exact Nat.mul_ne_zero hg₂ne hg₁ne
  · -- the composite maps `S` into `{0, 1}`
    intro s hs
    obtain ⟨q, hq⟩ := RingHom.mem_range.mp (hg₁S s hs)
    have hmem : aeval s g₁ ∈ T := Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs)
    have hqmem : q ∈ T.preimage (algebraMap ℚ K) hφinj.injOn :=
      Finset.mem_preimage.mpr (by rw [hq]; exact hmem)
    have hval : aeval s (g₂.comp g₁) = algebraMap ℚ K (g₂.eval q) := by
      rw [aeval_comp, ← hq, aeval_algebraMap_apply_eq_algebraMap_eval]
    rw [hval]; rcases hg₂S q hqmem with h | h <;> rw [h] <;> simp
  · -- the composite's critical values lie in `{0, 1}`
    intro x hx
    rcases Finset.mem_union.mp (critVal_comp_subset (K := K)
        (derivative_ne_zero.mpr hg₂ne) (derivative_ne_zero.mpr hg₁ne) hx) with hx' | hx'
    · -- `g₂`-image of a critical value of `g₁`, which is rational
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx'
      obtain ⟨q, hq⟩ := RingHom.mem_range.mp (hg₁crit y hy)
      have hmem : y ∈ T := Finset.mem_union_right _ hy
      have hqmem : q ∈ T.preimage (algebraMap ℚ K) hφinj.injOn :=
        Finset.mem_preimage.mpr (by rw [hq]; exact hmem)
      have hval : aeval y g₂ = algebraMap ℚ K (g₂.eval q) := by
        rw [← hq, aeval_algebraMap_apply_eq_algebraMap_eval]
      rw [hval]; rcases hg₂S q hqmem with h | h <;> rw [h] <;> simp
    · -- a critical value of `g₂` directly
      exact hg₂crit _ hx'

end Belyi
