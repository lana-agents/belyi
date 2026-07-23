/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Curve.Existence
import Belyi.Curve.SmoothStalk
import Belyi.Dimension
import Belyi.P1.BranchExtraction
import Belyi.P1.PolynomialBranchLocus
import Belyi.P1.PolynomialMarkedBranch
import Belyi.P1.MarkedPointMatching
import Belyi.Polynomial.ReductionCombined

/-!
# Forward direction of Belyi's theorem (B8): a curve over `ℚ̄` admits a Belyi map

This file assembles statement **B8** of `references/proof-outline.md` — the forward direction
of Belyi's theorem — out of the glue pieces produced by taxis issues #185, #186, #187 and the
merged B1/B4/base-change machinery.

Working over an algebraically closed field `k` of characteristic zero that is **algebraic over
`ℚ`** (i.e. a copy of `ℚ̄`, the model case being `k = AlgebraicClosure ℚ`), the main result

* `Belyi.exists_isBelyiMap_of_isCurveOver` :  every curve `X` over `k` admits a Belyi map
  `∃ f : X ⟶ ℙ¹_k, IsBelyiMap k f`,

is proved by the classical chain:

1. **B1.** `Belyi.exists_isFinite_surjective_hom_to_P1` gives a finite surjective `f₀ : X ⟶ ℙ¹_k`.
2. **B2.** `Belyi.P1.branchFinset` extracts the finite set `S ⊆ k` of affine branch coordinates
   of `f₀` (`Belyi/P1/BranchExtraction.lean`, #187).
3. **B6∘B7.** `Belyi.exists_aeval_mem_and_critVal_mem_zeroOne` produces a non-constant `g : ℚ[X]`
   with `g(S) ⊆ {0, 1}` and all critical values of `g` (in `k`) in `{0, 1}` (#185).
4. **B4/B5.** With `ĝ = g.map (algebraMap ℚ k)`, the polynomial self-map's branch locus lands in
   `{0,1,∞}` (`branch_map_polynomialSelfMap_subset_markedPoints`, #186) and it carries `Branch f₀`
   into `{0,1,∞}` (`polynomialSelfMap_image_branch_subset_markedPoints`, #187), so
   `isBelyiMap_comp_polynomialSelfMap` yields `IsBelyiMap k (f₀ ≫ polynomialSelfMap ĝ)`.

Base-changing along any field extension `k ⊆ K` (`Belyi.isBelyiMap_baseChange`, the merged
unconditional B2b/B3d specialisation) then transports the Belyi map to `K`:

* `Belyi.exists_isBelyiMap_baseChange_of_isCurveOver` :  the base change of a curve over `k = ℚ̄`
  to an arbitrary extension field `K` (the model case `K = ℂ`) admits a Belyi map over `K`.

Together these are the forward direction B8 for a curve **presented with a `ℚ̄`-model**.  The
fully general statement "`X/ℂ` definable over `ℚ̄` ⇒ `X` admits a Belyi map" additionally
requires the B3c *descent* direction (a `ℂ`-curve definable over `ℚ̄` has a model that is itself
a `ℚ̄`-curve, taxis #167), which is off the forward-direction critical path and not yet
available; the two results here supply everything on the forward side of that gap.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory
open scoped Polynomial

/-- **Forward direction of Belyi's theorem, model form (B8).** Every curve `X` over an
algebraically closed field `k` of characteristic zero that is algebraic over `ℚ` — i.e. over
`ℚ̄` — admits a Belyi map: a finite morphism `f : X ⟶ ℙ¹_k` whose branch locus is contained in
`{0, 1, ∞}`.

The map is the composite `f₀ ≫ polynomialSelfMap ĝ` of a B1 cover `f₀ : X ⟶ ℙ¹_k` with the
polynomial self-map attached to the reduction polynomial `ĝ = g.map (algebraMap ℚ k)` of B6∘B7. -/
theorem exists_isBelyiMap_of_isCurveOver
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] :
    ∃ f : X ⟶ P1 k, IsBelyiMap k f ∧ f.IsOver (Spec (CommRingCat.of k)) := by
  classical
  -- B1: a finite surjective cover `f₀ : X ⟶ ℙ¹_k`, itself a `k`-morphism.
  haveI : IsIntegral X := IsCurveOver.isIntegral k X
  obtain ⟨f₀, hf₀fin, hf₀surj, hf₀over⟩ := exists_isFinite_surjective_hom_to_P1 k X
  haveI : f₀.IsOver (Spec (CommRingCat.of k)) := hf₀over
  haveI : IsFinite f₀ := hf₀fin
  -- Instances the branch-extraction API consumes.
  haveI : IsDominant f₀ := ⟨hf₀surj.denseRange⟩
  haveI : IsNoetherian (P1 k) := isNoetherian_of_over (P1 k) (Spec (CommRingCat.of k))
  haveI : LocallyOfFinitePresentation f₀ := inferInstance
  haveI : IsNoetherian X := isNoetherian_of_over X (Spec (CommRingCat.of k))
  have hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
    fun x => krullDimLE_one_stalk_of_isCurveOver k X x
  -- B2: the finite set of affine branch coordinates.
  set S : Finset k := P1.branchFinset k f₀ hdim with hS
  -- B6∘B7: a reduction polynomial `g : ℚ[X]`.
  obtain ⟨g, hgne, hgS, hgcrit⟩ := exists_aeval_mem_and_critVal_mem_zeroOne (K := k) S
  -- Transport `g` to `k[X]`; the degree is preserved because `algebraMap ℚ k` is injective.
  have hinj : Function.Injective (algebraMap ℚ k) := (algebraMap ℚ k).injective
  have hd : 0 < (g.map (algebraMap ℚ k)).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective hinj]
    exact Nat.pos_of_ne_zero hgne
  -- The polynomial self-map of `ℙ¹` is a `k`-morphism, so the composite is too.
  haveI : (P1.polynomialSelfMap k (g.map (algebraMap ℚ k)) hd).IsOver
      (Spec (CommRingCat.of k)) :=
    ⟨by rw [P1.structMap_eq]
        exact P1.polynomialSelfMap_structMap k (g.map (algebraMap ℚ k)) hd⟩
  refine ⟨f₀ ≫ P1.polynomialSelfMap k (g.map (algebraMap ℚ k)) hd, ?_, inferInstance⟩
  -- B4/B5: the composite is a Belyi map.
  refine P1.isBelyiMap_comp_polynomialSelfMap k (g.map (algebraMap ℚ k)) hd f₀ ?_ ?_
  · -- `polynomialSelfMap ĝ '' Branch f₀ ⊆ {0,1,∞}` (#187), from `g(S) ⊆ {0,1}`.
    refine P1.polynomialSelfMap_image_branch_subset_markedPoints k f₀ hdim
      (g.map (algebraMap ℚ k)) hd ?_
    intro s hs
    rw [Polynomial.aeval_map_algebraMap]
    exact hgS s (by rw [hS]; exact hs)
  · -- `Branch (polynomialSelfMap ĝ) ⊆ {0,1,∞}` (#186), from `critVal g ⊆ {0,1}`.
    exact branch_map_polynomialSelfMap_subset_markedPoints hgne hgcrit hd

/-- **Forward direction of Belyi's theorem after base change (B8 + B2b/B3d).** The base change of
a curve over `k = ℚ̄` (algebraically closed, characteristic zero, algebraic over `ℚ`) to an
arbitrary extension field `K` — the model case being `K = ℂ` — admits a Belyi map over `K`.

Concretely: take the model Belyi map `f₀ : X₀ ⟶ ℙ¹_k` from
`Belyi.exists_isBelyiMap_of_isCurveOver` and base change it along the field extension `k ⊆ K` via
the unconditional `Belyi.isBelyiMap_baseChange`.  The resulting scheme
`pullback f₀ (mapOfAlgebra k K)` is the base change of `X₀` to `K`; this is exactly the sense in
which a `K`-scheme *definable over `ℚ̄`* (given by such a model) admits a Belyi map. -/
theorem exists_isBelyiMap_baseChange_of_isCurveOver
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
    (K : Type u) [Field K] [Algebra k K]
    (X₀ : Scheme.{u}) [X₀.Over (Spec (CommRingCat.of k))] [IsCurveOver k X₀] :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ P1 K), IsBelyiMap K f := by
  obtain ⟨f₀, hf₀, -⟩ := exists_isBelyiMap_of_isCurveOver k X₀
  exact ⟨_, _, isBelyiMap_baseChange k K hf₀⟩

end Belyi
