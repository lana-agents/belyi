/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Ramification
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Ramification and branch loci under base change (forward inclusion, part of B2b)

Statement **B2b** of `references/proof-outline.md` (taxis issue #47) asks for the
compatibility of the ramification and branch loci with base change. The full statement is
an *equality* `Ram (f') = pr⁻¹ (Ram f)` (for `f'` the base change of `f`), whose second
inclusion is a descent statement requiring faithful flatness — the "stalk of a base change
is a localization of a tensor product" bridge that mathlib v4.32 does not provide.

This file supplies the **forward inclusion**, which is exactly what the forward direction of
Belyi's theorem (B8, issue #51) consumes: it constructs a finite morphism `f₀` over `ℚ̄`
with `Branch f₀ ⊆ {0, 1, ∞}`, base-changes to `ℂ`, and needs the base change to still have
its branch locus inside `{0, 1, ∞}`. For that only the inclusion
`Branch (f') ⊆ q⁻¹ (Branch f)` is needed, and — crucially — it needs **no** stalk bridge:
it follows purely from the fact that `Smooth` is stable under base change, by pasting the
open-immersion restriction square of the smooth locus onto the base-change square.

## Main results

* `Belyi.smoothLocus_preimage_subset`: for a pullback square `IsPullback pr f' f q`, the
  preimage `pr⁻¹ (smoothLocus f)` is contained in `smoothLocus f'`.
* `Belyi.ram_subset_preimage`: hence `Ram f' ⊆ pr⁻¹ (Ram f)`.
* `Belyi.branch_subset_preimage`: hence `Branch f' ⊆ q⁻¹ (Branch f)` — the branch locus of a
  base change lies over the branch locus of the original morphism.

The remaining (descent) inclusion, and the specialisation to a field extension
`k₀ ⊆ K` with the matching of the marked points `{0, 1, ∞}`, are separate follow-up work
on #47/#48.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {pr : X' ⟶ X} {q : Y' ⟶ Y}

/-- **Forward inclusion of B2b (smooth locus).** For a pullback square
```
  X' --pr--> X
  f'|        |f
  Y' --q---> Y
```
the preimage of the smooth locus of `f` is contained in the smooth locus of the base
change `f'`. Since `Smooth` is stable under base change, restricting `pr` to the open
`smoothLocus f ⊆ X` and pasting with the base-change square exhibits the restriction of `f'`
to `pr⁻¹ (smoothLocus f)` as the base change of the smooth morphism
`(smoothLocus f).ι ≫ f`, hence smooth; no descent (stalk-of-base-change) argument is
required. -/
lemma smoothLocus_preimage_subset (hsq : IsPullback pr f' f q)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation f'] :
    ((pr ⁻¹ᵁ f.smoothLocus : X'.Opens) : Set X') ⊆ (f'.smoothLocus : Set X') := by
  -- The inclusion of the smooth locus of `f`, followed by `f`, is smooth.
  have hsm : Smooth ((f.smoothLocus).ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq (f.smoothLocus).ι f]
    exact TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x => x.2)
  -- Paste the open-immersion restriction square of `pr` along `smoothLocus f` onto the
  -- base-change square, and read off that the base change of `(smoothLocus f).ι ≫ f` is
  -- smooth.
  have hpaste := (isPullback_morphismRestrict pr f.smoothLocus).paste_vert hsq
  have hsm' : Smooth ((pr ⁻¹ᵁ f.smoothLocus).ι ≫ f') :=
    MorphismProperty.of_isPullback (P := @Smooth) hpaste hsm
  haveI := hsm'
  have hpre : (pr ⁻¹ᵁ f.smoothLocus).ι ⁻¹ᵁ f'.smoothLocus = ⊤ := by
    rw [Scheme.Hom.preimage_smoothLocus_eq (pr ⁻¹ᵁ f.smoothLocus).ι f']
    exact Scheme.Hom.smoothLocus_eq_top _
  intro z hz
  have hmem : (⟨z, hz⟩ : ↥(pr ⁻¹ᵁ f.smoothLocus)) ∈
      (pr ⁻¹ᵁ f.smoothLocus).ι ⁻¹ᵁ f'.smoothLocus := by
    rw [hpre]; trivial
  exact hmem

/-- **Forward inclusion of B2b (ramification locus).** For a pullback square
`IsPullback pr f' f q`, the ramification locus of the base change `f'` is contained in the
preimage under `pr` of the ramification locus of `f`. -/
lemma ram_subset_preimage (hsq : IsPullback pr f' f q)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation f'] :
    Ram f' ⊆ pr ⁻¹' Ram f := by
  rw [Ram, Ram, Set.preimage_compl]
  refine Set.compl_subset_compl.mpr ?_
  rw [← Scheme.Hom.coe_preimage]
  exact smoothLocus_preimage_subset hsq

/-- **Forward inclusion of B2b (branch locus).** For a pullback square
`IsPullback pr f' f q`, the branch locus of the base change `f'` lies over the branch locus
of `f`: `Branch f' ⊆ q⁻¹ (Branch f)`. This is the input the forward direction of Belyi's
theorem uses to base-change a Belyi map (`Branch f ⊆ {0, 1, ∞}`) while keeping its branch
locus inside `{0, 1, ∞}`. -/
theorem branch_subset_preimage (hsq : IsPullback pr f' f q)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation f'] :
    Branch f' ⊆ q ⁻¹' Branch f := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨pr x, ram_subset_preimage hsq hx, ?_⟩
  have hw : (pr ≫ f).base x = (f' ≫ q).base x := congrArg (fun m => m.base x) hsq.w
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hw
  exact hw

end Belyi
