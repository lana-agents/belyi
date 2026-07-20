/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Polynomial.CritVal

/-!
# Belyi reduction I: moving algebraic branch points to `ℚ`

This file proves statement **B6** of `references/proof-outline.md`, the first reduction
step of Belyi's theorem: for every finite set `S` of elements of a field `K` algebraic
over `ℚ`, there is a non-constant polynomial `g ∈ ℚ[X]` such that both the image `g(S)`
and all critical values of `g` are rational.

Geometrically (via the dictionary of statement B4, proved in a later issue): composing a
finite morphism `X ⟶ ℙ¹` whose branch points are algebraic with the map `ℙ¹ ⟶ ℙ¹` given
by `g` yields a morphism all of whose finite branch points are rational — the point `∞`
is fixed by polynomials and is always an allowed branch point.

## Main result

* `Belyi.exists_aeval_mem_range_and_critVal_mem_range`

## Proof sketch (Belyi's descending induction)

Induct on the lexicographic measure `(d, n)`, where `d` bounds the degrees over `ℚ` of the
elements of `S` and `n` counts the elements of degree exactly `d`. If `d ≤ 1` every element
is rational and `g = X` works. Otherwise pick `s ∈ S` of degree `d` with minimal polynomial
`m` and replace `S` by `S' = m(S) ∪ CritVal m`:

* `m(s') ∈ ℚ(s')`, so degrees do not increase (`Belyi.natDegree_minpoly_aeval_le`);
* elements with minimal polynomial `m` (in particular `s`) map to `0`, so the count at
  degree `d` strictly decreases;
* critical values of `m` have degree `< d` (`Belyi.natDegree_minpoly_critVal_lt`).

The polynomial produced for `S'` is then composed with `m`, using
`Belyi.critVal_comp_subset` to control the critical values of the composite.
-/

namespace Belyi

open Polynomial

variable {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]

private lemma rational_of_natDegree_minpoly_le_one {x : K}
    (hx : (minpoly ℚ x).natDegree ≤ 1) : x ∈ (algebraMap ℚ K).range := by
  have h1 : 0 < (minpoly ℚ x).natDegree :=
    minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)
  exact minpoly.natDegree_eq_one_iff.mp (le_antisymm hx h1)

/-- The inductive core of Belyi's reduction: `d` bounds the degrees over `ℚ` of elements
of `S`, and `n` bounds the number of elements of degree exactly `d`. -/
private lemma reduction_key (d : ℕ) : ∀ (n : ℕ) (S : Finset K),
    (∀ s ∈ S, (minpoly ℚ s).natDegree ≤ d) →
    (S.filter fun s => (minpoly ℚ s).natDegree = d).card ≤ n →
    ∃ g : ℚ[X], g.natDegree ≠ 0 ∧
      (∀ s ∈ S, aeval s g ∈ (algebraMap ℚ K).range) ∧
      (∀ x ∈ critVal K g, x ∈ (algebraMap ℚ K).range) := by
  classical
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  by_cases hd : d ≤ 1
  · -- base case: all elements of `S` are rational, `g = X` works
    intro n S hbound _
    refine ⟨X, by simp, fun s hs => ?_, fun x hx => by simp at hx⟩
    simpa using rational_of_natDegree_minpoly_le_one ((hbound s hs).trans hd)
  · -- inductive step: `d ≥ 2`; inner induction on the count at top degree
    push Not at hd
    intro n
    induction n with
    | zero =>
      -- no element has degree `d`: lower the degree bound and use the outer IH
      intro S hbound hcard
      have hb' : ∀ s ∈ S, (minpoly ℚ s).natDegree ≤ d - 1 := by
        intro s hs
        have h1 : (minpoly ℚ s).natDegree ≠ d := by
          intro h
          have : s ∈ S.filter fun s => (minpoly ℚ s).natDegree = d :=
            Finset.mem_filter.mpr ⟨hs, h⟩
          simp [Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)] at this
        exact Nat.le_sub_one_of_lt <| lt_of_le_of_ne (hbound s hs) h1
      exact ihd (d - 1) (by omega) _ S hb' le_rfl
    | succ n ihn =>
      intro S hbound hcard
      by_cases hle : (S.filter fun s => (minpoly ℚ s).natDegree = d).card ≤ n
      · exact ihn S hbound hle
      -- pick an element `s` of top degree `d` and pass to `S' = m(S) ∪ CritVal m`
      push Not at hle
      obtain ⟨s, hs⟩ := Finset.card_pos.mp (by omega :
        0 < (S.filter fun s => (minpoly ℚ s).natDegree = d).card)
      obtain ⟨hsS, hsd⟩ := Finset.mem_filter.mp hs
      set m : ℚ[X] := minpoly ℚ s with hm
      have hmdeg : m.natDegree = d := hsd
      have hmne : m.natDegree ≠ 0 := by omega
      have hmder : derivative m ≠ 0 := derivative_ne_zero.mpr hmne
      set S' : Finset K := S.image (fun t => aeval t m) ∪ critVal K m with hS'
      -- degrees do not increase when passing to `S'`
      have hbound' : ∀ y ∈ S', (minpoly ℚ y).natDegree ≤ d := by
        intro y hy
        rcases Finset.mem_union.mp hy with hy | hy
        · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
          exact (natDegree_minpoly_aeval_le t m).trans (hbound t ht)
        · exact le_of_lt <| hmdeg ▸ natDegree_minpoly_critVal_lt hmne hy
      -- the count at degree `d` strictly decreases
      have hsub : (S'.filter fun y => (minpoly ℚ y).natDegree = d) ⊆
          (S.filter fun t => (minpoly ℚ t).natDegree = d ∧ minpoly ℚ t ≠ m).image
            (fun t => aeval t m) := by
        intro y hy
        obtain ⟨hyS', hyd⟩ := Finset.mem_filter.mp hy
        rcases Finset.mem_union.mp hyS' with hy' | hy'
        · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy'
          have htd : (minpoly ℚ t).natDegree = d :=
            le_antisymm (hbound t ht) (hyd ▸ natDegree_minpoly_aeval_le t m)
          have htm : minpoly ℚ t ≠ m := by
            intro h
            have h0 : aeval t m = 0 := h ▸ minpoly.aeval ℚ t
            have : (minpoly ℚ (aeval t m)).natDegree = 1 := by
              rw [h0]
              exact minpoly.natDegree_eq_one_iff.mpr ⟨0, by simp⟩
            omega
          exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, htd, htm⟩, rfl⟩
        · exact absurd hyd (by have := natDegree_minpoly_critVal_lt hmne hy'; omega)
      have hcard' : (S'.filter fun y => (minpoly ℚ y).natDegree = d).card ≤ n := by
        have h1 : s ∈ (S.filter fun t => (minpoly ℚ t).natDegree = d).filter
            (fun t => minpoly ℚ t = m) :=
          Finset.mem_filter.mpr ⟨hs, rfl⟩
        have h2 := Finset.card_filter_add_card_filter_not
          (p := fun t => minpoly ℚ t = m) (s := S.filter fun t => (minpoly ℚ t).natDegree = d)
        have h3 : (S.filter fun t => (minpoly ℚ t).natDegree = d ∧ minpoly ℚ t ≠ m) =
            (S.filter fun t => (minpoly ℚ t).natDegree = d).filter
              (fun t => ¬minpoly ℚ t = m) := by
          rw [Finset.filter_filter]
        have h4 : 0 < ((S.filter fun t => (minpoly ℚ t).natDegree = d).filter
            (fun t => minpoly ℚ t = m)).card := Finset.card_pos.mpr ⟨s, h1⟩
        calc (S'.filter fun y => (minpoly ℚ y).natDegree = d).card
            ≤ ((S.filter fun t => (minpoly ℚ t).natDegree = d ∧ minpoly ℚ t ≠ m).image
                (fun t => aeval t m)).card := Finset.card_le_card hsub
          _ ≤ (S.filter fun t => (minpoly ℚ t).natDegree = d ∧ minpoly ℚ t ≠ m).card :=
              Finset.card_image_le
          _ ≤ n := by rw [h3]; omega
      -- recurse on `S'` and compose
      obtain ⟨g₁, hg₁ne, hg₁S, hg₁crit⟩ := ihn S' hbound' hcard'
      have hg₁der : derivative g₁ ≠ 0 := derivative_ne_zero.mpr hg₁ne
      refine ⟨g₁.comp m, ?_, fun t ht => ?_, fun x hx => ?_⟩
      · rw [natDegree_comp]
        exact Nat.mul_ne_zero hg₁ne hmne
      · rw [aeval_comp]
        exact hg₁S _ <| Finset.mem_union_left _ <| Finset.mem_image_of_mem _ ht
      · rcases Finset.mem_union.mp (critVal_comp_subset hg₁der hmder hx) with hx' | hx'
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx'
          exact hg₁S _ <| Finset.mem_union_right _ hy
        · exact hg₁crit _ hx'

/-- **Belyi reduction I** (statement B6 of `references/proof-outline.md`): for every finite
set `S` of elements of `K` algebraic over `ℚ`, there is a non-constant polynomial
`g ∈ ℚ[X]` mapping `S` into `ℚ` whose critical values are all rational. -/
theorem exists_aeval_mem_range_and_critVal_mem_range (S : Finset K) :
    ∃ g : ℚ[X], g.natDegree ≠ 0 ∧
      (∀ s ∈ S, aeval s g ∈ (algebraMap ℚ K).range) ∧
      (∀ x ∈ critVal K g, x ∈ (algebraMap ℚ K).range) :=
  reduction_key (S.sup fun s => (minpoly ℚ s).natDegree) _ S
    (fun _ hs => Finset.le_sup (f := fun s => (minpoly ℚ s).natDegree) hs) le_rfl

end Belyi
