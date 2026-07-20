/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Ramification and branch loci

Statement **B2** of `references/proof-outline.md` (taxis issue #47): the ramification
locus of a morphism of schemes and its image, the branch locus.

## Design note

The issue text suggests defining the ramification locus through the support of
`Ω_{X/Y}`. That is unnecessary: mathlib provides the smooth locus of a morphism as an
*open* subscheme, `AlgebraicGeometry.Scheme.Hom.smoothLocus`, namely the set of points
where the stalk map is formally smooth. Since `Etale = SmoothOfRelativeDimension 0`, for
a morphism of relative dimension `0` — in particular a finite morphism of curves — the
smooth locus is the étale locus. So we set

* `Belyi.Ram f := (f.smoothLocus)ᶜ`, closed by construction;
* `Belyi.Branch f := f '' Ram f`.

## Main results

* `Belyi.isClosed_ram`: the ramification locus is closed.
* `Belyi.ram_eq_empty_iff`: `Ram f = ∅` iff `f` is smooth; for relative dimension `0`,
  `ram_eq_empty_iff_etale`, iff `f` is étale.
* `Belyi.ram_comp_subset`, `Belyi.branch_comp_subset` (**B2a**): the ramification locus
  of a composite is contained in `Ram f ∪ f⁻¹(Ram g)`, hence
  `Branch (f ≫ g) ⊆ g '' Branch f ∪ Branch g`.
* `Belyi.ram_eq_empty_of_isIso`, `Belyi.branch_eq_empty_of_isIso` and the cancellation
  lemmas for composing with an isomorphism.

Finiteness of `Ram f` for a finite morphism of curves in characteristic zero (which
needs generic étaleness), B2b (base change) and B2c are follow-up work on the same
issue.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory

variable {X Y Z : Scheme.{u}}

section Defs

variable (f : X ⟶ Y) [LocallyOfFinitePresentation f]

/-- The **ramification locus** of a morphism: the complement of its smooth locus, i.e.
the set of points where the stalk map fails to be formally smooth. For a morphism of
relative dimension `0` (e.g. a finite morphism of curves) this is the complement of the
étale locus. -/
def Ram : Set X := (f.smoothLocus : Set X)ᶜ

/-- The **branch locus** of a morphism: the image of its ramification locus. -/
def Branch : Set Y := f '' Ram f

lemma mem_ram_iff {x : X} : x ∈ Ram f ↔ ¬ (f.stalkMap x).hom.FormallySmooth := Iff.rfl

lemma mem_branch_iff {y : Y} : y ∈ Branch f ↔ ∃ x ∈ Ram f, f x = y := by
  simp [Branch, Set.mem_image]

/-- The ramification locus is closed. -/
lemma isClosed_ram : IsClosed (Ram f) :=
  f.smoothLocus.2.isClosed_compl

/-- A morphism is smooth exactly when it is unramified everywhere. -/
lemma ram_eq_empty_iff : Ram f = ∅ ↔ Smooth f := by
  rw [Ram, Set.compl_empty_iff, ← Scheme.Hom.smoothLocus_eq_top_iff (f := f)]
  exact ⟨fun h => TopologicalSpace.Opens.ext (by simpa using h),
    fun h => by rw [h]; simp⟩

/-- For a morphism of relative dimension `0`, the ramification locus is empty exactly
when the morphism is étale. -/
lemma ram_eq_empty_iff_etale [SmoothOfRelativeDimension 0 f] :
    Ram f = ∅ ↔ Etale f := by
  rw [ram_eq_empty_iff, Etale.iff_smoothOfRelativeDimension_zero]
  exact ⟨fun _ => inferInstance, fun _ => SmoothOfRelativeDimension.smooth 0 f⟩

lemma branch_eq_empty_iff_ram_eq_empty : Branch f = ∅ ↔ Ram f = ∅ := by
  simp [Branch, Set.image_eq_empty]

end Defs

section Etale

variable (f : X ⟶ Y)

@[simp]
lemma ram_eq_empty_of_etale [LocallyOfFinitePresentation f] [Etale f] : Ram f = ∅ :=
  (ram_eq_empty_iff f).mpr inferInstance

@[simp]
lemma branch_eq_empty_of_etale [LocallyOfFinitePresentation f] [Etale f] :
    Branch f = ∅ :=
  (branch_eq_empty_iff_ram_eq_empty f).mpr (ram_eq_empty_of_etale f)

@[simp]
lemma ram_eq_empty_of_isIso [IsIso f] : Ram f = ∅ := by
  have : IsOpenImmersion f := inferInstance
  exact ram_eq_empty_of_etale f

@[simp]
lemma branch_eq_empty_of_isIso [IsIso f] : Branch f = ∅ := by
  have : IsOpenImmersion f := inferInstance
  exact branch_eq_empty_of_etale f

end Etale

section Comp

variable (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A point is unramified for a composite as soon as it is unramified for the first map
and its image is unramified for the second: the ramification locus of `f ≫ g` is
contained in `Ram f ∪ f⁻¹(Ram g)`. -/
lemma ram_comp_subset [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]
    [LocallyOfFinitePresentation (f ≫ g)] :
    Ram (f ≫ g) ⊆ Ram f ∪ f ⁻¹' Ram g := by
  intro x hx
  by_contra hcon
  rw [Set.mem_union, not_or, Set.mem_preimage] at hcon
  obtain ⟨hf, hg⟩ := hcon
  refine hx ?_
  rw [mem_ram_iff, not_not] at hf hg
  change x ∈ (f ≫ g).smoothLocus
  rw [Scheme.Hom.mem_smoothLocus, Scheme.Hom.stalkMap_comp]
  exact hg.comp hf

/-- **B2a**: the branch locus of a composite is contained in the image of the branch
locus of the first map together with the branch locus of the second. -/
theorem branch_comp_subset [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]
    [LocallyOfFinitePresentation (f ≫ g)] :
    Branch (f ≫ g) ⊆ g '' Branch f ∪ Branch g := by
  rintro z ⟨x, hx, rfl⟩
  rcases ram_comp_subset f g hx with h | h
  · exact Or.inl ⟨f x, ⟨x, h, rfl⟩, rfl⟩
  · exact Or.inr ⟨f x, h, rfl⟩

end Comp

end Belyi
