/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Smooth.Field
import Belyi.Dimension

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
* `Belyi.finite_ram`, `Belyi.finite_branch`: on an irreducible Noetherian scheme with
  one-dimensional local rings, a morphism smooth at the generic point ramifies only at
  finitely many points; `Belyi.finite_ram_of_perfectField` discharges the generic
  hypothesis for morphisms to the spectrum of a perfect field.
* `Belyi.smooth_morphismRestrict_of_disjoint_branch` (**B2c**): a morphism is smooth
  over any open subset of the target disjoint from its branch locus.
* `Belyi.ram_isIso_comp`, `Belyi.branch_isIso_comp`, `Belyi.ram_comp_isIso`,
  `Belyi.branch_comp_isIso`: the behaviour of the ramification and branch loci under
  composition with an isomorphism on either side.
* `Belyi.genericPoint_mem_smoothLocus`: **generic étaleness** — a dominant, locally-of-
  finite-presentation morphism of integral schemes with perfect target function field
  (e.g. a dominant finite morphism of curves in characteristic zero) is smooth at the
  generic point of the source. Hence `Belyi.finite_ram_of_isDominant`,
  `Belyi.finite_branch_of_isDominant` discharge the generic hypothesis of `finite_ram`
  for such morphisms — in particular the finite surjective `X ⟶ ℙ¹` produced by B1.

B2b (compatibility with base change along a field extension) is follow-up work on the
same issue.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory TopologicalSpace

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

section Finite

variable (f : X ⟶ Y) [LocallyOfFinitePresentation f]

/-- **Finiteness of the ramification locus.** On an irreducible Noetherian scheme whose
local rings have Krull dimension `≤ 1` (e.g. a curve, by issue #75), a morphism that is
smooth at the generic point ramifies only at finitely many points: `Ram f` is a closed
set avoiding the generic point.

For a finite morphism of curves in characteristic zero the hypothesis `hgen` holds
because the function-field extension is separable (generic étaleness). -/
theorem finite_ram [IrreducibleSpace X] [NoetherianSpace X]
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x))
    (hgen : genericPoint X ∈ f.smoothLocus) : (Ram f).Finite :=
  finite_of_isClosed_of_genericPoint_notMem hdim (isClosed_ram f) (by simpa [Ram] using hgen)

/-- The branch locus of a generically smooth morphism as above is finite. -/
theorem finite_branch [IrreducibleSpace X] [NoetherianSpace X]
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x))
    (hgen : genericPoint X ∈ f.smoothLocus) : (Branch f).Finite :=
  (finite_ram f hdim hgen).image f

/-- Over a perfect base field (e.g. in characteristic zero), a morphism from an integral
scheme is automatically smooth at the generic point, so the ramification locus of a
morphism of such schemes over the field is finite as soon as the source has
one-dimensional stalks. -/
theorem finite_ram_of_perfectField {k : Type u} [Field k] [PerfectField k] [IsIntegral X]
    [NoetherianSpace X] (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x))
    (g : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFinitePresentation g] : (Ram g).Finite :=
  finite_ram g hdim g.genericPoint_mem_smoothLocus_of_perfectField

end Finite

section GenericEtale

/-- For a **dominant** morphism of integral schemes, the generic point of the source maps
to the generic point of the target. -/
lemma image_genericPoint_eq_of_isDominant (f : X ⟶ Y) [IrreducibleSpace X]
    [IrreducibleSpace Y] [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have h := (genericPoint_spec X).image (f := ⇑f) f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at h
  exact h.eq (genericPoint_spec Y)

/-- **Generic étaleness.** A dominant morphism of integral schemes that is locally of
finite presentation is smooth at the generic point of the source, provided the function
field of the target is perfect (e.g. in characteristic zero). Indeed the stalk map at the
generic point is the extension of function fields `K(Y) → K(X)`, an essentially finite type
extension of a perfect field, hence formally smooth.

This discharges the `hgen` hypothesis of `finite_ram`/`finite_branch` for a dominant
finite morphism of curves in characteristic zero — in particular for the finite surjective
morphism `X ⟶ ℙ¹` produced by B1. -/
theorem genericPoint_mem_smoothLocus (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant f] [LocallyOfFinitePresentation f] [PerfectField Y.functionField] :
    genericPoint X ∈ f.smoothLocus := by
  have hgen : f (genericPoint X) = genericPoint Y := image_genericPoint_eq_of_isDominant f
  have hess := LocallyOfFiniteType.stalkMap f (genericPoint X)
  rw [Scheme.Hom.mem_smoothLocus]
  -- the source stalk is the function field of `Y` (a perfect field), via `f genX = genY`
  let ee : Y.presheaf.stalk (f (genericPoint X)) ≃+* Y.functionField :=
    (Y.presheaf.stalkCongr (.of_eq hgen)).commRingCatIsoToRingEquiv
  letI : Field (Y.presheaf.stalk (f (genericPoint X))) :=
    (ee.isField (Field.toIsField Y.functionField)).toField
  letI : PerfectField (Y.presheaf.stalk (f (genericPoint X))) :=
    PerfectField.of_ringEquiv ee.symm
  algebraize [(f.stalkMap (genericPoint X)).hom]
  exact Algebra.FormallySmooth.of_perfectField

/-- The ramification locus of a dominant, locally-of-finite-presentation morphism of
integral schemes is finite, provided the source has one-dimensional stalks and the target
function field is perfect (e.g. a dominant finite morphism of curves in characteristic
zero). -/
theorem finite_ram_of_isDominant (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [NoetherianSpace X] [IsDominant f] [LocallyOfFinitePresentation f]
    [PerfectField Y.functionField]
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x)) : (Ram f).Finite :=
  finite_ram f hdim (genericPoint_mem_smoothLocus f)

/-- The branch locus of such a morphism is finite. -/
theorem finite_branch_of_isDominant (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [NoetherianSpace X] [IsDominant f] [LocallyOfFinitePresentation f]
    [PerfectField Y.functionField]
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x)) : (Branch f).Finite :=
  finite_branch f hdim (genericPoint_mem_smoothLocus f)

end GenericEtale

section Restrict

/-- Composing with an open immersion on the target does not change the smooth locus. -/
lemma smoothLocus_comp_of_isOpenImmersion (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g]
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (f ≫ g)] :
    (f ≫ g).smoothLocus = f.smoothLocus := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  change x ∈ (f ≫ g).smoothLocus ↔ x ∈ f.smoothLocus
  rw [Scheme.Hom.mem_smoothLocus, Scheme.Hom.mem_smoothLocus, Scheme.Hom.stalkMap_comp]
  exact RingHom.FormallySmooth.respectsIso.cancel_left_isIso
    (g.stalkMap (f x)) (f.stalkMap x)

/-- A morphism is smooth over any open subset of the target above which it is
unramified. -/
lemma smooth_morphismRestrict (f : X ⟶ Y) [LocallyOfFinitePresentation f] (U : Y.Opens)
    [LocallyOfFinitePresentation (f ∣_ U)] (h : (f ⁻¹ᵁ U : Set X) ⊆ (f.smoothLocus : Set X)) :
    Smooth (f ∣_ U) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  have h1 : ((f ∣_ U) ≫ U.ι).smoothLocus = (f ∣_ U).smoothLocus :=
    smoothLocus_comp_of_isOpenImmersion _ _
  have h2 : ((f ⁻¹ᵁ U).ι ≫ f).smoothLocus = (f ⁻¹ᵁ U).ι ⁻¹ᵁ f.smoothLocus :=
    (Scheme.Hom.preimage_smoothLocus_eq _ _).symm
  have h3 : ((f ∣_ U) ≫ U.ι).smoothLocus = ((f ⁻¹ᵁ U).ι ≫ f).smoothLocus := by
    congr 1
    exact morphismRestrict_ι f U
  have h4 : (f ⁻¹ᵁ U).ι ⁻¹ᵁ f.smoothLocus = ⊤ :=
    TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x => h x.2)
  rw [← h1, h3, h2, h4]

/-- **B2c**: a morphism is smooth over any open subset of the target avoiding its branch
locus. For a morphism of relative dimension `0` (e.g. a finite morphism of curves) this
says it is étale there. -/
theorem smooth_morphismRestrict_of_disjoint_branch (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (U : Y.Opens)
    [LocallyOfFinitePresentation (f ∣_ U)] (h : Disjoint (U : Set Y) (Branch f)) :
    Smooth (f ∣_ U) := by
  refine smooth_morphismRestrict f U fun x hx => ?_
  by_contra hxs
  exact Set.disjoint_left.mp h hx ⟨x, hxs, rfl⟩

end Restrict

section IsoCancel

variable (f : X ⟶ Y)

/-- Precomposing with an isomorphism pulls the ramification locus back along it. -/
lemma ram_isIso_comp (e : Z ⟶ X) [IsIso e] [LocallyOfFinitePresentation f] :
    Ram (e ≫ f) = e ⁻¹' Ram f := by
  rw [Ram, Ram, ← Scheme.Hom.preimage_smoothLocus_eq e f, Scheme.Hom.coe_preimage,
    Set.preimage_compl]

/-- Precomposing with an isomorphism leaves the branch locus unchanged. -/
lemma branch_isIso_comp (e : Z ⟶ X) [IsIso e] [LocallyOfFinitePresentation f] :
    Branch (e ≫ f) = Branch f := by
  have hsurj : Function.Surjective ⇑e := (Scheme.homeoOfIso (asIso e)).surjective
  rw [Branch, Branch, ram_isIso_comp f e, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.image_comp, Set.image_preimage_eq _ hsurj]

/-- Postcomposing with an isomorphism leaves the ramification locus unchanged. -/
lemma ram_comp_isIso (e : Y ⟶ Z) [IsIso e] [LocallyOfFinitePresentation f] :
    Ram (f ≫ e) = Ram f := by
  have : IsOpenImmersion e := inferInstance
  rw [Ram, Ram, smoothLocus_comp_of_isOpenImmersion f e]

/-- Postcomposing with an isomorphism pushes the branch locus forward along it. -/
lemma branch_comp_isIso (e : Y ⟶ Z) [IsIso e] [LocallyOfFinitePresentation f] :
    Branch (f ≫ e) = e '' Branch f := by
  rw [Branch, Branch, ram_comp_isIso f e, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.image_comp]

end IsoCancel

end Belyi
