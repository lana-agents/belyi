/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.BelyiMap
import Belyi.RamificationBaseChange
import Belyi.P1.PointsBaseChange

/-!
# Base change of a Belyi map along a field extension

This file supplies the **field-extension specialisation** of statement **B2b** (taxis issue
#47): the compatibility of the branch locus, and of the `IsBelyiMap` predicate, with base
change along a field extension `k₀ ⊆ K`.

Concretely, for a morphism `f₀ : X₀ ⟶ ℙ¹_{k₀}` we take its base change along the canonical
map `Belyi.P1.mapOfAlgebra k₀ K : ℙ¹_K ⟶ ℙ¹_{k₀}` (which exhibits `ℙ¹_K` as the base change
of `ℙ¹_{k₀}`, `Belyi.P1.isPullback_mapOfAlgebra`), namely
`pullback.snd f₀ (mapOfAlgebra k₀ K) : (X₀ ×_{ℙ¹_{k₀}} ℙ¹_K) ⟶ ℙ¹_K`.

## Main results

* `Belyi.branch_baseChange_subset` — the **geometric core**: the branch locus of the base
  change lies over the branch locus of `f₀`:
  `Branch (pullback.snd f₀ (mapOfAlgebra k₀ K)) ⊆ (mapOfAlgebra k₀ K) ⁻¹' Branch f₀`.
  Bridge-free — a direct instantiation of `Belyi.branch_subset_preimage` (the forward
  inclusion of B2b) at the base-change square `Belyi.P1.isPullback_mapOfAlgebra`.
* `Belyi.isBelyiMap_baseChange_of_mapsTo` — the **packaged form**: if `f₀` is a Belyi map and
  the base-change map `mapOfAlgebra k₀ K` sends the fibre of the marked points `{0, 1, ∞}` of
  `ℙ¹_{k₀}` into the marked points of `ℙ¹_K` (the "marked-point matching" hypothesis), then the
  base change is a Belyi map over `K`.

`IsFinite` and `LocallyOfFinitePresentation` are stable under base change in mathlib, so the
only genuine input beyond the geometric core is the marked-point matching, i.e. that the
preimage of a marked point of `ℙ¹_{k₀}` under `mapOfAlgebra k₀ K` is again a marked point of
`ℙ¹_K`. The forward direction of this matching (a marked point maps to a marked point) is
`Belyi.P1.mapOfAlgebra_base_{zero,one,infty}`; the reverse (fibre-singleton) inclusion is a
separate homogeneous-prime computation, left as follow-up on #47.

This is exactly the input the forward direction of Belyi's theorem (B8, issue #51) consumes:
it produces a finite `f₀` over `ℚ̄` with `Branch f₀ ⊆ {0, 1, ∞}`, base-changes to `ℂ`, and
needs the base change to stay a Belyi map.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

variable (k₀ K : Type u) [Field k₀] [Field K] [Algebra k₀ K]

section

variable {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ P1 k₀)

/-- `LocallyOfFinitePresentation` is stable under base change, so the base change of a
locally-of-finite-presentation model morphism is again locally of finite presentation. -/
instance locallyOfFinitePresentation_baseChange [LocallyOfFinitePresentation f₀] :
    LocallyOfFinitePresentation (pullback.snd f₀ (P1.mapOfAlgebra k₀ K)) :=
  MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance

/-- `IsFinite` is stable under base change, so the base change of a finite model morphism is
again finite. -/
instance isFinite_baseChange [IsFinite f₀] :
    IsFinite (pullback.snd f₀ (P1.mapOfAlgebra k₀ K)) :=
  MorphismProperty.pullback_snd (P := @IsFinite) _ _ inferInstance

/-- **Geometric core of the field-extension specialisation of B2b.** The branch locus of the
base change of `f₀ : X₀ ⟶ ℙ¹_{k₀}` along the field extension `k₀ ⊆ K` lies over the branch
locus of `f₀`. Bridge-free: an instantiation of the forward inclusion `branch_subset_preimage`
at the cartesian square `Belyi.P1.isPullback_mapOfAlgebra`. -/
lemma branch_baseChange_subset [LocallyOfFinitePresentation f₀] :
    Branch (pullback.snd f₀ (P1.mapOfAlgebra k₀ K)) ⊆
      (P1.mapOfAlgebra k₀ K) ⁻¹' Branch f₀ :=
  branch_subset_preimage (IsPullback.of_hasPullback f₀ (P1.mapOfAlgebra k₀ K))

end

/-- **Field-extension specialisation of B2b for `IsBelyiMap`, packaged form.** If `f₀` is a
Belyi map over `k₀` and the base-change map `mapOfAlgebra k₀ K` maps every point lying over a
marked point of `ℙ¹_{k₀}` to a marked point of `ℙ¹_K` (the marked-point matching), then the
base change `pullback.snd f₀ (mapOfAlgebra k₀ K)` is a Belyi map over `K`.

The three conjuncts of `IsBelyiMap` are discharged as: `IsFinite` and
`LocallyOfFinitePresentation` from base-change stability (`isFinite_baseChange`,
`locallyOfFinitePresentation_baseChange`); and `Branch ⊆ markedPoints K` from
`branch_baseChange_subset` (`Branch` lies over `Branch f₀ ⊆ markedPoints k₀`) followed by the
matching hypothesis. -/
theorem isBelyiMap_baseChange_of_mapsTo {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ P1 k₀}
    (hf₀ : IsBelyiMap k₀ f₀)
    (hmatch : ∀ y : P1 K, (P1.mapOfAlgebra k₀ K).base y ∈ markedPoints k₀ →
      y ∈ markedPoints K) :
    IsBelyiMap K (pullback.snd f₀ (P1.mapOfAlgebra k₀ K)) := by
  haveI := hf₀.isFinite
  haveI := hf₀.locallyOfFinitePresentation
  refine ⟨inferInstance, inferInstance, fun y hy => ?_⟩
  have h1 : (P1.mapOfAlgebra k₀ K).base y ∈ Branch f₀ := branch_baseChange_subset k₀ K f₀ hy
  exact hmatch y (hf₀.branch_subset h1)

end Belyi
