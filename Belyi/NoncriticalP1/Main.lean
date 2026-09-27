/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.NoncriticalP1.Reduction

/-!
# Noncritical Belyi maps on `ℙ¹`

This file proves the `ℙ¹` case of Theorem 2.5 of
S. Mochizuki, *Noncritical Belyi maps*, Math. J. Okayama Univ. **46** (2004):

> Let `S ⊆ ℙ¹(ℚ̄)` be a finite `Gal(ℚ̄/ℚ)`-stable set and `τ ∈ ℙ¹(ℚ) ∖ S`. Then there is a
> composite `H = hₙ ∘ ⋯ ∘ h₁` of Möbius transformations and polynomials with rational
> coefficients such that `H(S) ⊆ {0, 1, ∞}`, `H(τ) ∉ {0, 1, ∞}`, and `H` is unramified over
> `ℙ¹ ∖ {0, 1, ∞}`.

The composite is non-constant: every elementary map has positive degree
(`Belyi.NoncriticalP1.degreeComp_pos`) and is surjective on `ℙ¹(ℚ̄)`
(`Belyi.NoncriticalP1.evalComp_surjective`).

## Proof

After a Möbius transformation we may assume `τ ≠ ∞`, and adding `∞` to `S` we reduce to
branch sets `T ∪ {∞}` with `T ⊆ ℚ̄` finite and Galois stable. We then perform the nested
induction of Lemma 2.4 on the maximal degree `d` of the points of `T` and the number of
points of degree `d` (`Belyi.NoncriticalP1.exists_isNoncriticalBelyi_withInf`): at each
step we normalise with Lemma 2.3 (`Belyi.NoncriticalP1.normalize_step`), and either all
points are rational and Lemma 2.2 finishes (`Belyi.NoncriticalP1.rational_step`), or we
apply the minimal polynomial of a point of degree `d` (`Belyi.NoncriticalP1.minpoly_step`).

## Main results

* `Belyi.NoncriticalP1.exists_isNoncriticalBelyi`: the theorem above;
* `Belyi.NoncriticalP1.exists_isNoncriticalBelyi_of_poly`: the variant where `S` is `∞`
  together with the roots of a nonzero `f ∈ ℚ[X]`, and `τ ∈ ℚ` with `f(τ) ≠ 0`.
-/

namespace Belyi.NoncriticalP1

open Polynomial

/-- The nested induction of Lemma 2.4 on the maximal degree `d` and the number of points of
degree `d`. -/
private lemma core_key (d : ℕ) : ∀ (n : ℕ) (T : Finset Qbar), IsGalStable T →
    (∀ t ∈ T, deg t ≤ d) → (T.filter fun t => deg t = d).card ≤ n →
    ∀ τ : ℚ, (τ : Qbar) ∉ T → ∃ hs, IsNoncriticalBelyi hs (withInf T) (ofRat τ) := by
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  by_cases hd : d ≤ 1
  · -- all points are rational: normalise and apply Lemma 2.2
    intro n T hT hdeg _ τ hτ
    obtain ⟨u, T₁, hT₁, hbd, hdeg₁, hgood⟩ := normalize_step T hT hτ
    have h1 : ∀ y ∈ T₁, deg y ≤ 1 := (hdeg₁ 1 le_rfl (fun t ht => (hdeg t ht).trans hd)).1
    obtain ⟨hs, hhs⟩ := rational_step T₁ hbd h1
    exact ⟨u :: hs, hgood hs hhs⟩
  · push Not at hd
    -- if no point has degree `d`, the outer induction hypothesis applies
    have hlower : ∀ T : Finset Qbar, IsGalStable T → (∀ t ∈ T, deg t ≤ d) →
        (T.filter fun t => deg t = d).card = 0 →
        ∀ τ : ℚ, (τ : Qbar) ∉ T → ∃ hs, IsNoncriticalBelyi hs (withInf T) (ofRat τ) := by
      intro T hT hdeg h0 τ hτ
      have hb' : ∀ t ∈ T, deg t ≤ d - 1 := by
        intro t ht
        have hne : deg t ≠ d := fun h => by
          have hmem : t ∈ T.filter fun t => deg t = d := Finset.mem_filter.mpr ⟨ht, h⟩
          rw [Finset.card_eq_zero.mp h0] at hmem
          exact Finset.notMem_empty t hmem
        have := hdeg t ht
        omega
      exact ihd (d - 1) (by omega) _ T hT hb' le_rfl τ hτ
    intro n
    induction n with
    | zero =>
      intro T hT hdeg hcard τ hτ
      exact hlower T hT hdeg (Nat.le_zero.mp hcard) τ hτ
    | succ n ihn =>
      intro T hT hdeg hcard τ hτ
      obtain ⟨u, T₁, hT₁, hbd, hdeg₁, hgood⟩ := normalize_step T hT hτ
      obtain ⟨hdeg₁', hcard₁⟩ := hdeg₁ d (by omega) hdeg
      have hcard₁' := (hcard₁ hd).trans hcard
      have h9 : ((9 : ℚ) : Qbar) ∉ T₁ := fun h => by
        have := hbd _ h
        rw [norm_ι_ratCast] at this
        norm_num at this
      by_cases h0 : (T₁.filter fun y => deg y = d).card = 0
      · obtain ⟨hs, hhs⟩ := hlower T₁ hT₁ hdeg₁' h0 9 h9
        exact ⟨u :: hs, hgood hs hhs⟩
      · obtain ⟨σ₀, hσ₀⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
        obtain ⟨hσ₀T, hσ₀d⟩ := Finset.mem_filter.mp hσ₀
        obtain ⟨T₂, τ₂, hT₂, hτ₂, hdeg₂, hcard₂, v, hv⟩ :=
          minpoly_step T₁ hT₁ hbd hd hdeg₁' hcard₁' hσ₀T hσ₀d
        obtain ⟨hs, hhs⟩ := ihn T₂ hT₂ hdeg₂ hcard₂ τ₂ hτ₂
        exact ⟨u :: v :: hs, hgood _ (hv hs hhs)⟩

/-- **Lemma 2.4 combined with Lemma 2.2**: for a finite Galois-stable `T ⊆ ℚ̄` and a rational
`τ ∉ T` there is a noncritical Belyi map for `(T ∪ {∞}, τ)`. -/
theorem exists_isNoncriticalBelyi_withInf (T : Finset Qbar) (hT : IsGalStable T) {τ : ℚ}
    (hτ : (τ : Qbar) ∉ T) : ∃ hs, IsNoncriticalBelyi hs (withInf T) (ofRat τ) :=
  core_key _ _ T hT (fun _ ht => Finset.le_sup (f := deg) ht) le_rfl τ hτ

/-- The inclusion `ℙ¹(ℚ) → ℙ¹(ℚ̄)` (`none = ∞`). -/
noncomputable def ratPt (τ : Option ℚ) : Pt := τ.map fun q => (q : Qbar)

@[simp] lemma ratPt_some (q : ℚ) : ratPt (some q) = ofRat q := rfl

@[simp] lemma ratPt_none : ratPt none = none := rfl

/-- **Theorem 2.5 of Mochizuki for `X = ℙ¹`** (Belyi maps noncritical at a prescribed point):
for a finite `Gal(ℚ̄/ℚ)`-stable set `S ⊆ ℙ¹(ℚ̄)` and a point `τ ∈ ℙ¹(ℚ) ∖ S`, there is a
composite `H = hₙ ∘ ⋯ ∘ h₁` of elementary maps (Möbius transformations and polynomials over
`ℚ`) with `H(S) ⊆ {0, 1, ∞}`, `H(τ) ∉ {0, 1, ∞}`, unramified over `ℙ¹ ∖ {0, 1, ∞}`. -/
theorem exists_isNoncriticalBelyi (S : Finset Pt)
    (hS : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ z ∈ S, z.map σ ∈ S) (τ : Option ℚ) (hτ : ratPt τ ∉ S) :
    ∃ hs : List ElemMap, IsNoncriticalBelyi hs S (ratPt τ) := by
  set T : Finset Qbar := S.eraseNone with hTdef
  have hT : IsGalStable T := by
    intro σ t ht
    rw [hTdef, Finset.mem_eraseNone] at ht ⊢
    exact hS σ _ ht
  have hST : (S : Set Pt) ⊆ withInf T := by
    intro z hz
    cases z with
    | none => exact none_mem_withInf T
    | some t => exact some_mem_withInf (Finset.mem_eraseNone.mpr hz)
  cases τ with
  | some q =>
    have hq : (q : Qbar) ∉ T := by
      rw [Finset.mem_eraseNone]; exact hτ
    obtain ⟨hs, hhs⟩ := exists_isNoncriticalBelyi_withInf T hT hq
    exact ⟨hs, hhs.mono hST⟩
  | none =>
    -- move `τ = ∞` to `0` by `x ↦ 1/(x - α)` with `α ∈ ℚ ∖ S`
    obtain ⟨α, hα⟩ := Infinite.exists_notMem_finset
      (T.preimage (fun q : ℚ => (q : Qbar)) Rat.cast_injective.injOn)
    have hα' : (α : Qbar) ∉ T := fun h => hα (Finset.mem_preimage.mpr h)
    have hdet : (0 : ℚ) * -α - 1 * 1 ≠ 0 := by norm_num
    set u := ElemMap.mob 0 1 1 (-α) hdet with hu
    have hne : ∀ t ∈ T, ((1 : ℚ) : Qbar) * t + ((-α : ℚ) : Qbar) ≠ 0 := by
      intro t ht h0
      apply hα'
      have : t = α := by push_cast at h0; linear_combination h0
      rwa [← this]
    have h0 : ((0 : ℚ) : Qbar) ∉ pushFin u T := by
      intro h
      obtain ⟨t, ht, hty⟩ := mem_pushFin.mp h
      rw [hu, ElemMap.apply_mob_some_of_ne _ (hne t ht), Option.some.injEq] at hty
      rw [Rat.cast_zero, div_eq_zero_iff] at hty
      rcases hty with h1 | h1
      · simp at h1
      · exact hne t ht h1
    obtain ⟨hs, hhs⟩ := exists_isNoncriticalBelyi_withInf (pushFin u T) (hT.pushFin u) h0
    refine ⟨u :: hs, IsNoncriticalBelyi.cons_mob hdet (S' := withInf (pushFin u T)) ?_ ?_⟩
    · intro z hz
      cases z with
      | none => exact absurd hz hτ
      | some t =>
        have ht : t ∈ T := Finset.mem_eraseNone.mpr hz
        have happ := ElemMap.apply_mob_some_of_ne hdet (hne t ht)
        rw [happ]
        exact some_mem_withInf (mem_pushFin.mpr ⟨t, ht, happ⟩)
    · have : u.apply (ratPt none) = ofRat 0 := by
        simp [hu, ElemMap.apply_mob_none, ofRat]
      rw [this]
      exact hhs

/-- **Theorem 2.5 of Mochizuki for `X = ℙ¹`, polynomial form**: for a nonzero `f ∈ ℚ[X]` and
`τ ∈ ℚ` with `f(τ) ≠ 0` there is a composite `H` of elementary maps sending `∞` and all
roots of `f` in `ℚ̄` into `{0, 1, ∞}`, with `H(τ) ∉ {0, 1, ∞}`, unramified over
`ℙ¹ ∖ {0, 1, ∞}`. -/
theorem exists_isNoncriticalBelyi_of_poly (f : ℚ[X]) (hf : f ≠ 0) {τ : ℚ}
    (hτ : f.eval τ ≠ 0) :
    ∃ hs : List ElemMap,
      IsNoncriticalBelyi hs {z | z = none ∨ ∃ x, z = some x ∧ aeval x f = 0} (ofRat τ) := by
  set T : Finset Qbar := (qroots f).toFinset with hTdef
  have hmem : ∀ x, x ∈ T ↔ aeval x f = 0 := fun x => by
    rw [hTdef, Multiset.mem_toFinset, mem_qroots hf]
  have hT : IsGalStable T := by
    intro σ t ht
    rw [hmem] at ht ⊢
    rw [aeval_algHom_apply, ht, map_zero]
  have hτT : (τ : Qbar) ∉ T := by
    rw [hmem]
    have := aeval_algebraMap_apply_eq_algebraMap_eval (A := Qbar) (p := f) τ
    simp only [eq_ratCast] at this
    rw [this]
    exact_mod_cast hτ
  obtain ⟨hs, hhs⟩ := exists_isNoncriticalBelyi_withInf T hT hτT
  refine ⟨hs, hhs.mono ?_⟩
  rintro z (rfl | ⟨x, rfl, hx⟩)
  · exact none_mem_withInf T
  · exact some_mem_withInf ((hmem x).mpr hx)

end Belyi.NoncriticalP1
