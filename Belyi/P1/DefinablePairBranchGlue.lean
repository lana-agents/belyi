/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.SmoothLocusChartGlue
import Belyi.DefinablePairBranch

/-!
# ℙ¹ chart-glue: concrete branch-locus matching under base change (B3d, taxis #221/#48)

This file discharges the two remaining, `#220`-gated slices of taxis issue #221, using the ℙ¹
chart-glue ramification equality `Belyi.P1.ram_baseChange_p1_eq` (taxis #220, the geometric
core) as its only substantive input:

* **Part 1 — the concrete ℙ¹ Branch equality.** For a finite dominant curve cover
  `f₀ : X₀ ⟶ ℙ¹_{k₀}` over a field `k₀ ⊆ K` of characteristic zero, the branch locus of the
  ℙ¹ base change `pullback.snd f₀ (mapOfAlgebra k₀ K)` is the `mapOfAlgebra`-preimage of
  `Branch f₀` (`Belyi.P1.branch_baseChange_p1_eq`) — the equality upgrade of the merged forward
  inclusion, obtained by feeding `ram_baseChange_p1_eq` into the unconditional
  `Belyi.branch_preimage_eq`.

* **Part 2 — the `DefinableOverPair` repackaging.** The chart-glue ramification equality is
  stated for the ℙ¹ base-change square `pullback.snd f₀ (mapOfAlgebra k₀ K)`. The pair-model
  branch matching `Belyi.branch_definableOverPair_eq` (its unconditional half, already merged)
  instead consumes the ramification equality of the *model* base-change square exhibited by
  `Belyi.isPullback_baseChangeModelHom` (with `pr = pullback.fst p₀ (specAlgebraMap …)`). These
  are two presentations of the base change of `f₀`, related by the canonical identification
  `Belyi.P1.toPullback` (`mapOfAlgebra = toPullback ≫ pullback.fst`, an isomorphism). We
  transport the chart-glue ramification equality across that identification
  (`Belyi.ram_baseChangeModelHom_eq`) and plug the result into `branch_definableOverPair_eq`,
  yielding the fully-discharged B3d branch matching `Belyi.branch_definableOverPair_eq_of_isFinite`:

  ```
  Branch f = mapOfAlgebra k₀ K ⁻¹' Branch f₀
  ```

  for any pair model `f₀` of a finite dominant curve cover — the marked-point/branch-locus
  statement the converse direction (#53) consumes, closing #48's B3d branch-locus item.

The transport (`ram_baseChangeModelHom_eq`) compares the two base-change squares by their common
universal property: `Belyi.isPullback_baseChangeModelHom` re-based onto the cospan of the ℙ¹
square (via the iso `toPullback`) and the ℙ¹ square `IsPullback.of_hasPullback` are two pullbacks
of the same cospan, so `IsPullback.isoIsPullback` identifies their vertices compatibly with the
projections; `Belyi.ram_isIso_comp` / `Belyi.ram_comp_isIso` then move `Ram` across the
identifying isomorphisms and injectivity of the comparison homeomorphism cancels it.

## Main results

* `Belyi.P1.branch_baseChange_p1_eq` — part 1.
* `Belyi.ram_baseChangeModelHom_eq` — the ramification equality of the model base-change square.
* `Belyi.branch_definableOverPair_eq_of_isFinite` — part 2, the discharged B3d branch matching.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

namespace P1

/-- **Part 1: concrete ℙ¹ branch-locus matching under base change.** For a finite dominant curve
cover `f₀ : X₀ ⟶ ℙ¹_{k₀}` over a field `k₀ ⊆ K` of characteristic zero, the branch locus of the
base change `pullback.snd f₀ (mapOfAlgebra k₀ K)` is the `mapOfAlgebra`-preimage of `Branch f₀`.
The equality upgrade of the merged forward inclusion, via `Belyi.branch_preimage_eq` fed the
chart-glue ramification equality `Belyi.P1.ram_baseChange_p1_eq` (taxis #220). -/
theorem branch_baseChange_p1_eq
    {k₀ K : Type u} [Field k₀] [Field K] [CharZero k₀] [CharZero K] [Algebra k₀ K]
    {X₀ : Scheme.{u}} [X₀.Over (Spec (CommRingCat.of k₀))] [IsCurveOver k₀ X₀]
    (f₀ : X₀ ⟶ P1 k₀) [IsFinite f₀] [LocallyOfFinitePresentation f₀] [Surjective f₀]
    [f₀.IsOver (Spec (CommRingCat.of k₀))] :
    Branch (pullback.snd f₀ (mapOfAlgebra k₀ K)) = mapOfAlgebra k₀ K ⁻¹' Branch f₀ := by
  haveI : LocallyOfFinitePresentation (pullback.snd f₀ (mapOfAlgebra k₀ K)) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  exact branch_preimage_eq (IsPullback.of_hasPullback f₀ (mapOfAlgebra k₀ K))
    (ram_baseChange_p1_eq f₀)

end P1

/-- **Ramification equality of the model base-change square** (the `hram` input to
`Belyi.branch_definableOverPair_eq`, discharged). For a finite dominant curve cover
`f₀ : X₀ ⟶ ℙ¹_{k₀}` over a field `k₀ ⊆ K` of characteristic zero with model structure morphism
`p₀ = f₀ ≫ (ℙ¹_{k₀} ↘ Spec k₀)`,
```
  Ram (baseChangeModelHom k₀ K p₀ f₀ hf₀) = pullback.fst p₀ (specAlgebraMap k₀ K) ⁻¹' Ram f₀.
```

The chart-glue core (`Belyi.P1.ram_baseChange_p1_eq`, taxis #220) proves the analogous equality for
the ℙ¹ base-change square `pullback.snd f₀ (mapOfAlgebra k₀ K)`. Both `baseChangeModelHom` and
`pullback.snd f₀ (mapOfAlgebra k₀ K)` are base changes of `f₀`, related by the canonical
isomorphism `Belyi.P1.toPullback` (`toPullback ≫ pullback.fst = mapOfAlgebra`). Re-basing
`isPullback_baseChangeModelHom` onto the cospan of the ℙ¹ square identifies the two pullback
vertices (`IsPullback.isoIsPullback`) compatibly with the projections; `ram_isIso_comp` /
`ram_comp_isIso` transport `Ram` across the identifying isomorphisms, and injectivity of the
comparison homeomorphism cancels it. -/
theorem ram_baseChangeModelHom_eq
    {k₀ K : Type u} [Field k₀] [Field K] [CharZero k₀] [CharZero K] [Algebra k₀ K]
    {X₀ : Scheme.{u}} [X₀.Over (Spec (CommRingCat.of k₀))] [IsCurveOver k₀ X₀]
    {p₀ : X₀ ⟶ Spec (CommRingCat.of k₀)} {f₀ : X₀ ⟶ P1 k₀}
    (hf₀ : f₀ ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)) = p₀)
    [IsFinite f₀] [LocallyOfFinitePresentation f₀] [Surjective f₀]
    [f₀.IsOver (Spec (CommRingCat.of k₀))]
    [LocallyOfFinitePresentation (baseChangeModelHom k₀ K p₀ f₀ hf₀)] :
    Ram (baseChangeModelHom k₀ K p₀ f₀ hf₀)
      = pullback.fst p₀ (specAlgebraMap k₀ K) ⁻¹' Ram f₀ := by
  -- Square A: the ℙ¹ base-change square (cospan `f₀`, `mapOfAlgebra`).
  have hA : IsPullback (pullback.fst f₀ (P1.mapOfAlgebra k₀ K))
      (pullback.snd f₀ (P1.mapOfAlgebra k₀ K)) f₀ (P1.mapOfAlgebra k₀ K) :=
    IsPullback.of_hasPullback f₀ (P1.mapOfAlgebra k₀ K)
  -- Square B: the model base-change square
  -- (cospan `f₀`, `pullback.fst (ℙ¹ ↘ Spec) specAlgebraMap`).
  have hB : IsPullback (pullback.fst p₀ (specAlgebraMap k₀ K))
      (baseChangeModelHom k₀ K p₀ f₀ hf₀) f₀
      (pullback.fst (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)) :=
    isPullback_baseChangeModelHom k₀ K p₀ f₀ hf₀
  -- The iso-corner square re-basing Square B's cospan corner onto `ℙ¹_K` via `toPullback`.
  have hiso : IsPullback (inv (P1.toPullback k₀ K))
      (pullback.fst (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K))
      (P1.mapOfAlgebra k₀ K) (𝟙 (P1 k₀)) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.comp_id, ← P1.toPullback_fst k₀ K, IsIso.inv_hom_id_assoc]
  -- Square B re-based onto the cospan of Square A.
  have hB' : IsPullback (pullback.fst p₀ (specAlgebraMap k₀ K))
      (baseChangeModelHom k₀ K p₀ f₀ hf₀ ≫ inv (P1.toPullback k₀ K)) f₀
      (P1.mapOfAlgebra k₀ K) := by
    have hp := hB.flip.paste_horiz hiso
    rw [Category.comp_id] at hp
    exact hp.flip
  -- The two vertices agree, compatibly with the projections.
  have hψ_fst : (hA.isoIsPullback _ _ hB').hom ≫ pullback.fst p₀ (specAlgebraMap k₀ K)
      = pullback.fst f₀ (P1.mapOfAlgebra k₀ K) := hA.isoIsPullback_hom_fst _ _ hB'
  have hψ_snd : (hA.isoIsPullback _ _ hB').hom
      ≫ (baseChangeModelHom k₀ K p₀ f₀ hf₀ ≫ inv (P1.toPullback k₀ K))
      = pullback.snd f₀ (P1.mapOfAlgebra k₀ K) := hA.isoIsPullback_hom_snd _ _ hB'
  -- Transport `Ram` across the identifying isomorphisms. (We move `Ram` onto the composite
  -- through the merged iso-cancellation lemmas rather than rewriting the raw morphism under
  -- `Ram` — the latter is blocked by the `LocallyOfFinitePresentation` instance argument, so the
  -- final morphism identification is bridged by `congr 1`.)
  have hway2 : ⇑(hA.isoIsPullback _ _ hB').hom ⁻¹' Ram (baseChangeModelHom k₀ K p₀ f₀ hf₀)
      = Ram (pullback.snd f₀ (P1.mapOfAlgebra k₀ K)) := by
    rw [← ram_comp_isIso (baseChangeModelHom k₀ K p₀ f₀ hf₀) (inv (P1.toPullback k₀ K)),
      ← ram_isIso_comp (baseChangeModelHom k₀ K p₀ f₀ hf₀ ≫ inv (P1.toPullback k₀ K))
        (hA.isoIsPullback _ _ hB').hom]
    congr 1
  have hcomb : ⇑(hA.isoIsPullback _ _ hB').hom ⁻¹' Ram (baseChangeModelHom k₀ K p₀ f₀ hf₀)
      = ⇑(hA.isoIsPullback _ _ hB').hom ⁻¹'
        (⇑(pullback.fst p₀ (specAlgebraMap k₀ K)) ⁻¹' Ram f₀) := by
    rw [hway2, P1.ram_baseChange_p1_eq f₀, ← Set.preimage_comp, ← TopCat.coe_comp,
      ← Scheme.Hom.comp_base, hψ_fst]
  have hsurj : Function.Surjective ⇑(hA.isoIsPullback _ _ hB').hom :=
    (Scheme.homeoOfIso (hA.isoIsPullback _ _ hB')).surjective
  exact hsurj.preimage_injective hcomb

/-- **B3d branch-locus matching for a pair model, fully discharged.** Given the pair-definability
data of `Belyi.DefinableOverPair` — a model `f₀ : X₀ ⟶ ℙ¹_{k₀}` of a finite dominant curve cover
over a subfield `k₀ ⊆ K` of characteristic zero, an identification `e` of `X` with the base change
of the model source, and the pair condition `f ≫ toPullback = e.hom ≫ baseChangeModelHom …` — the
branch locus of `f` is the preimage of `Branch f₀` under the canonical model map
`Belyi.P1.mapOfAlgebra k₀ K`:
```
  Branch f = mapOfAlgebra k₀ K ⁻¹' Branch f₀.
```

This is `Belyi.branch_definableOverPair_eq` with its ramification hypothesis discharged by the ℙ¹
chart-glue core (`ram_baseChangeModelHom_eq`); it closes the B3d branch-locus item of taxis #48,
the statement consumed by the converse direction (#53). -/
theorem branch_definableOverPair_eq_of_isFinite
    {k₀ K : Type u} [Field k₀] [Field K] [CharZero k₀] [CharZero K] [Algebra k₀ K]
    {X₀ : Scheme.{u}} [X₀.Over (Spec (CommRingCat.of k₀))] [IsCurveOver k₀ X₀]
    {p₀ : X₀ ⟶ Spec (CommRingCat.of k₀)} {f₀ : X₀ ⟶ P1 k₀}
    (hf₀ : f₀ ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)) = p₀)
    [IsFinite f₀] [LocallyOfFinitePresentation f₀] [Surjective f₀]
    [f₀.IsOver (Spec (CommRingCat.of k₀))]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {f : X ⟶ P1 K}
    [LocallyOfFinitePresentation f]
    (e : X ≅ pullback p₀ (specAlgebraMap k₀ K))
    (hfe : f ≫ P1.toPullback k₀ K = e.hom ≫ baseChangeModelHom k₀ K p₀ f₀ hf₀) :
    Branch f = P1.mapOfAlgebra k₀ K ⁻¹' Branch f₀ := by
  haveI : LocallyOfFinitePresentation (baseChangeModelHom k₀ K p₀ f₀ hf₀) :=
    locallyOfFinitePresentation_baseChangeModelHom p₀ f₀ hf₀
  exact branch_definableOverPair_eq hf₀ e hfe (ram_baseChangeModelHom_eq hf₀)

end Belyi
