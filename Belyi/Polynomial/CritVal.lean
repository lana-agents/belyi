/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Finite

/-!
# Critical values of rational polynomials

This file defines the finite set `Belyi.critVal K g` of critical values in a field extension
`K` of `ℚ` of a polynomial `g : ℚ[X]`, i.e. the values `g(a)` at the roots `a ∈ K` of the
derivative of `g`, and proves the two facts that drive Belyi's descending induction
(statement B6 in `references/proof-outline.md`):

* `Belyi.critVal_comp_subset`: critical values of a composite are controlled by
  `CritVal (g ∘ h) ⊆ g(CritVal h) ∪ CritVal g`;
* `Belyi.natDegree_minpoly_critVal_lt`: a critical value of `g` has degree over `ℚ`
  strictly smaller than `deg g`.

The auxiliary lemma `Belyi.natDegree_minpoly_aeval_le` (the degree over `ℚ` does not grow
under evaluation of a rational polynomial) is used repeatedly in the induction.

The point `∞` of `ℙ¹` needs no tracking here: polynomials fix `∞`, and `∞` is always an
allowed branch point in reduction step B6.
-/

namespace Belyi

open Polynomial IntermediateField

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- The critical values in `K` of a polynomial `g : ℚ[X]`: the images `g(a)` of the roots
`a ∈ K` of the derivative of `g`. For the intended use `g` is non-constant; for constant `g`
this set is empty. -/
noncomputable def critVal (K : Type*) [Field K] [Algebra ℚ K] (g : ℚ[X]) : Finset K :=
  letI := Classical.decEq K
  ((derivative g).aroots K).toFinset.image fun a => aeval a g

lemma mem_critVal_iff {g : ℚ[X]} {x : K} :
    x ∈ critVal K g ↔
      ∃ a : K, (derivative g ≠ 0 ∧ aeval a (derivative g) = 0) ∧ aeval a g = x := by
  simp only [critVal, Finset.mem_image, Multiset.mem_toFinset, mem_aroots]

lemma aeval_mem_critVal {g : ℚ[X]} (hg : derivative g ≠ 0) {a : K}
    (ha : aeval a (derivative g) = 0) : aeval a g ∈ critVal K g :=
  mem_critVal_iff.mpr ⟨a, ⟨hg, ha⟩, rfl⟩

@[simp]
lemma critVal_X : critVal K X = ∅ := by
  classical
  simp [critVal, aroots_one]

/-- Critical values of a composite polynomial: `CritVal (g ∘ h) ⊆ g(CritVal h) ∪ CritVal g`.
This is the bookkeeping engine of Belyi's descending induction. -/
lemma critVal_comp_subset [DecidableEq K] {g h : ℚ[X]} (hg : derivative g ≠ 0)
    (hh : derivative h ≠ 0) :
    critVal K (g.comp h) ⊆ (critVal K h).image (fun y => aeval y g) ∪ critVal K g := by
  intro x hx
  obtain ⟨a, ⟨-, ha⟩, rfl⟩ := mem_critVal_iff.mp hx
  rw [derivative_comp, map_mul] at ha
  rcases mul_eq_zero.mp ha with ha' | ha'
  · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨aeval a h, aeval_mem_critVal hh ha', ?_⟩)
    exact (aeval_comp (p := g) (q := h) a).symm
  · rw [aeval_comp] at ha'
    rw [aeval_comp (p := g) (q := h) a]
    exact Finset.mem_union_right _ (aeval_mem_critVal hg ha')

variable [Algebra.IsAlgebraic ℚ K]

/-- Evaluating a rational polynomial does not increase the degree over `ℚ`:
`g(x)` lies in `ℚ(x)`. -/
lemma natDegree_minpoly_aeval_le (x : K) (p : ℚ[X]) :
    (minpoly ℚ (aeval x p)).natDegree ≤ (minpoly ℚ x).natDegree := by
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have : FiniteDimensional ℚ ℚ⟮x⟯ := adjoin.finiteDimensional hx
  have h1 : aeval x p = algebraMap ℚ⟮x⟯ K (aeval (AdjoinSimple.gen ℚ x) p) := by
    rw [← aeval_algebraMap_apply, AdjoinSimple.algebraMap_gen]
  rw [h1, minpoly.algebraMap_eq (algebraMap ℚ⟮x⟯ K).injective]
  calc (minpoly ℚ (aeval (AdjoinSimple.gen ℚ x) p)).natDegree
      ≤ Module.finrank ℚ ℚ⟮x⟯ := minpoly.natDegree_le _
    _ = (minpoly ℚ x).natDegree := adjoin.finrank hx

/-- A critical value of a non-constant `g : ℚ[X]` has degree over `ℚ` strictly smaller than
`deg g`: it is the image of a root of the derivative, which has degree at most `deg g - 1`. -/
lemma natDegree_minpoly_critVal_lt {m : ℚ[X]} (hm : m.natDegree ≠ 0) {x : K}
    (hx : x ∈ critVal K m) : (minpoly ℚ x).natDegree < m.natDegree := by
  obtain ⟨a, ⟨hd, ha⟩, rfl⟩ := mem_critVal_iff.mp hx
  have h1 : (minpoly ℚ a).natDegree ≤ (derivative m).natDegree :=
    natDegree_le_of_dvd (minpoly.dvd ℚ a ha) hd
  have h2 : (derivative m).natDegree < m.natDegree := natDegree_derivative_lt hm
  exact lt_of_le_of_lt ((natDegree_minpoly_aeval_le a m).trans h1) h2

end Belyi
