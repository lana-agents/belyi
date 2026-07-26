/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.DefinablePairFinite
import Belyi.RamificationBaseChange

/-!
# Branch-locus matching from a pair model (branch direction of B3d)

Statement **B3d** of `references/proof-outline.md` (taxis issue #48) asks, among other
things, for the matching of branch loci under the pair-definability identification: if
`f : X ⟶ ℙ¹_K` has a model `f₀ : X₀ ⟶ ℙ¹_{k₀}` over a subfield `k₀ ⊆ K` (the data of
`Belyi.DefinableOverPair`), then in characteristic `0`

```
  Branch f = (ℙ¹_K ⟶ ℙ¹_{k₀}) ⁻¹ (Branch f₀),
```

the branch locus of `f` is the preimage of `Branch f₀` under the canonical model map
`Belyi.P1.mapOfAlgebra k₀ K : ℙ¹_K ⟶ ℙ¹_{k₀}`.

This file provides the **repackaging half** of that statement: it reduces the
`DefinableOverPair`-level branch matching to the ramification equality
`Ram (baseChangeModelHom …) = pr⁻¹ (Ram f₀)` of the single base-change pullback square that
`Belyi.isPullback_baseChangeModelHom` already exhibits (with `pr = pullback.fst p₀
(specAlgebraMap …)`). That ramification equality is the descent (reverse) inclusion of B2b
supplied by the ℙ¹ chart-glue core (taxis #220); everything downstream of it — upgrading
`Ram` to `Branch`, transporting through the source identification `e` and the canonical
identification `Belyi.P1.toPullback` — is unconditional and lives here.

The proof:
* upgrades the ramification equality to `Branch (baseChangeModelHom …) = pr⁻¹ (Branch f₀)`
  via the merged, unconditional `Belyi.branch_preimage_eq`;
* pushes `Branch` through the pair identification `f ≫ toPullback = e.hom ≫
  baseChangeModelHom …` using the iso-cancellation lemmas `Belyi.branch_comp_isIso` /
  `Belyi.branch_isIso_comp` (an isomorphism source leaves the branch locus untouched, an
  isomorphism target images it), so `toPullback '' Branch f = pr⁻¹ (Branch f₀)`;
* recovers `Branch f` by injectivity of the homeomorphism `toPullback` and rewrites
  `pr ∘ toPullback = mapOfAlgebra` (`Belyi.P1.toPullback_fst`).

## Main results

* `Belyi.branch_definableOverPair_eq`: the branch-locus matching for a pair model, given the
  ramification equality of the model base-change square.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

variable {k₀ K : Type u} [CommRing k₀] [CommRing K] [Algebra k₀ K]

/-- The base change `baseChangeModelHom` of a locally-of-finite-presentation model morphism is
locally of finite presentation (it is a base change of `f₀`, and `LocallyOfFinitePresentation`
is stable under base change). -/
lemma locallyOfFinitePresentation_baseChangeModelHom {X₀ : Scheme.{u}}
    (p₀ : X₀ ⟶ Spec (CommRingCat.of k₀)) (f₀ : X₀ ⟶ P1 k₀)
    (hf₀ : f₀ ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)) = p₀) [LocallyOfFinitePresentation f₀] :
    LocallyOfFinitePresentation (baseChangeModelHom k₀ K p₀ f₀ hf₀) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
    (isPullback_baseChangeModelHom k₀ K p₀ f₀ hf₀) inferInstance

/-- **Branch-locus matching of B3d, from a pair model.** Given the pair-definability data of
`Belyi.DefinableOverPair` — a model `f₀ : X₀ ⟶ ℙ¹_{k₀}`, an identification `e` of `X` with the
base change of the model source, and the pair condition `f ≫ toPullback = e.hom ≫
baseChangeModelHom …` — together with the ramification equality
`Ram (baseChangeModelHom …) = pr⁻¹ (Ram f₀)` of the base-change square exhibited by
`Belyi.isPullback_baseChangeModelHom` (`pr = pullback.fst p₀ (specAlgebraMap …)`), the branch
locus of `f` is the preimage of `Branch f₀` under the canonical model map
`Belyi.P1.mapOfAlgebra k₀ K`.

The ramification equality is the descent (reverse) inclusion of B2b (taxis #220); this lemma
supplies the unconditional repackaging that turns it into the `DefinableOverPair`-level branch
matching consumed by #48/#53. -/
theorem branch_definableOverPair_eq {X₀ : Scheme.{u}} {p₀ : X₀ ⟶ Spec (CommRingCat.of k₀)}
    {f₀ : X₀ ⟶ P1 k₀} (hf₀ : f₀ ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)) = p₀)
    [LocallyOfFinitePresentation f₀]
    [LocallyOfFinitePresentation (baseChangeModelHom k₀ K p₀ f₀ hf₀)]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {f : X ⟶ P1 K}
    [LocallyOfFinitePresentation f]
    (e : X ≅ pullback p₀ (specAlgebraMap k₀ K))
    (hfe : f ≫ P1.toPullback k₀ K = e.hom ≫ baseChangeModelHom k₀ K p₀ f₀ hf₀)
    (hram : Ram (baseChangeModelHom k₀ K p₀ f₀ hf₀)
      = pullback.fst p₀ (specAlgebraMap k₀ K) ⁻¹' Ram f₀) :
    Branch f = P1.mapOfAlgebra k₀ K ⁻¹' Branch f₀ := by
  -- Upgrade the ramification equality to a branch equality on the base-change square.
  have hbc : Branch (baseChangeModelHom k₀ K p₀ f₀ hf₀)
      = pullback.fst (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K) ⁻¹' Branch f₀ :=
    branch_preimage_eq (isPullback_baseChangeModelHom k₀ K p₀ f₀ hf₀) hram
  -- Push `Branch` through the pair identification. (Rewriting the morphism *under* `Branch`
  -- is blocked by the `LocallyOfFinitePresentation` instance argument, so bridge the pair
  -- condition with `congr 1` — the instances match by proof irrelevance.)
  have hbranch_f : ⇑(P1.toPullback k₀ K) '' Branch f
      = Branch (e.hom ≫ baseChangeModelHom k₀ K p₀ f₀ hf₀) := by
    rw [← branch_comp_isIso f (P1.toPullback k₀ K)]
    congr 1
  have key : ⇑(P1.toPullback k₀ K) '' Branch f
      = pullback.fst (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K) ⁻¹' Branch f₀ := by
    rw [hbranch_f, branch_isIso_comp, hbc]
  have hinj : Function.Injective ⇑(P1.toPullback k₀ K) :=
    (Scheme.homeoOfIso (asIso (P1.toPullback k₀ K))).injective
  have hcomp : ⇑(P1.mapOfAlgebra k₀ K)
      = ⇑(pullback.fst (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K))
          ∘ ⇑(P1.toPullback k₀ K) := by
    rw [← P1.toPullback_fst k₀ K, Scheme.Hom.comp_base, TopCat.coe_comp]
  calc Branch f
      = ⇑(P1.toPullback k₀ K) ⁻¹' (⇑(P1.toPullback k₀ K) '' Branch f) :=
        (Set.preimage_image_eq _ hinj).symm
    _ = ⇑(P1.toPullback k₀ K) ⁻¹'
          (pullback.fst (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)
            ⁻¹' Branch f₀) := by
        rw [key]
    _ = (⇑(pullback.fst (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K))
          ∘ ⇑(P1.toPullback k₀ K)) ⁻¹' Branch f₀ := (Set.preimage_comp).symm
    _ = P1.mapOfAlgebra k₀ K ⁻¹' Branch f₀ := by rw [hcomp]

end Belyi
