/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Marked

/-!
# Marked curves after base change (B13): tracking the marked points along `k ⊆ K`

This file supplies the **base-change layer** of statement **B13** of
`references/proof-outline.md`, extending the model form
`Belyi.exists_isBelyiMap_marked_of_isCurveOver` (`Belyi/Marked.lean`) along a field extension
`k ⊆ K` — the model case being `k = ℚ̄`, `K = ℂ`.

Working over an algebraically closed field `k` of characteristic zero that is algebraic over
`ℚ` (a copy of `ℚ̄`) and an arbitrary extension field `K`, the main result

* `Belyi.exists_isBelyiMap_marked_baseChange_of_isCurveOver` : for a curve `X₀` over `k` and a
  finite set `S` of closed points of `X₀`, the base change `Y = X₀ ×_{ℙ¹_k} ℙ¹_K` carries a
  Belyi map `f : Y ⟶ ℙ¹_K` such that every point of `Y` lying over `S` lands in the fibre over
  the marked set `{0, 1, ∞}` of `ℙ¹_K`,

is the exact analogue, on the marked side, of the forward direction's base-change theorem
`Belyi.exists_isBelyiMap_baseChange_of_isCurveOver` (`Belyi/Forward.lean`).

The construction is: take the marked model map `f₀ : X₀ ⟶ ℙ¹_k` from the model form (B13), base
change it along `k ⊆ K` via the unconditional `Belyi.isBelyiMap_baseChange` to get the Belyi
map `f = pullback.snd f₀ (mapOfAlgebra k K)`. The marked-point tracking then follows purely
from the pullback square: a point `z` of `Y` over `s ∈ S` satisfies
`(mapOfAlgebra k K)(f z) = f₀(π z) = f₀ s ∈ {0, 1, ∞}` (the model marking), so the reverse
marked-point matching `Belyi.P1.mapsTo_markedPoints` forces `f z ∈ {0, 1, ∞}`.

Packaging the pair `(Y, f)` as *definable over `ℚ̄`* and the `MarkedBelyiPair` structure the
Belyi-cuspidalization consumers (successors of taxis issue #8) expect — on the same footing as
the pair-definability layer of the forward direction, and to be coordinated with the
maintainers per the issue — remains the natural follow-up.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

/-- **Marked forward direction of Belyi's theorem after base change (B13 + B2b/B3d).** Let `X₀`
be a curve over an algebraically closed field `k` of characteristic zero that is algebraic over
`ℚ` (i.e. over `ℚ̄`), let `S` be a finite set of closed points of `X₀`, and let `K` be an
arbitrary extension field of `k` (the model case being `K = ℂ`).

Then the base change `Y = X₀ ×_{ℙ¹_k} ℙ¹_K` — presented with its projection `π : Y ⟶ X₀` —
carries a Belyi map `f : Y ⟶ ℙ¹_K` such that every point of `Y` lying over `S` maps into the
fibre over the marked set: `∀ z, π z ∈ S → f z ∈ {0, 1, ∞}`.

The map is `f = pullback.snd f₀ (mapOfAlgebra k K)` for the marked model map `f₀` produced by
`Belyi.exists_isBelyiMap_marked_of_isCurveOver`; the Belyi property is the unconditional
`Belyi.isBelyiMap_baseChange`, and the marked-point containment comes from the pullback square
together with the reverse marked-point matching `Belyi.P1.mapsTo_markedPoints`. -/
theorem exists_isBelyiMap_marked_baseChange_of_isCurveOver
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
    (K : Type u) [Field K] [Algebra k K]
    (X₀ : Scheme.{u}) [X₀.Over (Spec (CommRingCat.of k))] [IsCurveOver k X₀]
    (S : Set X₀) (hSfin : S.Finite) (hScl : ∀ s ∈ S, IsClosed ({s} : Set X₀)) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X₀) (f : Y ⟶ P1 K),
      IsBelyiMap K f ∧ ∀ z : Y, π.base z ∈ S → f.base z ∈ markedPoints K := by
  -- B13 model form: a marked Belyi map `f₀ : X₀ ⟶ ℙ¹_k`.
  obtain ⟨f₀, hf₀, hmk⟩ := exists_isBelyiMap_marked_of_isCurveOver k X₀ S hSfin hScl
  refine ⟨pullback f₀ (P1.mapOfAlgebra k K), pullback.fst f₀ (P1.mapOfAlgebra k K),
    pullback.snd f₀ (P1.mapOfAlgebra k K), isBelyiMap_baseChange k K hf₀, ?_⟩
  intro z hz
  -- The pullback square, evaluated pointwise at `z`:
  -- `f₀ (π z) = (mapOfAlgebra k K) (f z)`.
  have hsq := IsPullback.of_hasPullback f₀ (P1.mapOfAlgebra k K)
  have hw : f₀.base ((pullback.fst f₀ (P1.mapOfAlgebra k K)).base z) =
      (P1.mapOfAlgebra k K).base ((pullback.snd f₀ (P1.mapOfAlgebra k K)).base z) := by
    have h := congrArg (fun m => m.base z) hsq.w
    rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
  -- `f₀ (π z) ∈ {0, 1, ∞}` from the model marking, hence `(mapOfAlgebra) (f z) ∈ {0, 1, ∞}`.
  have hmark : (P1.mapOfAlgebra k K).base ((pullback.snd f₀ (P1.mapOfAlgebra k K)).base z) ∈
      markedPoints k := hw ▸ hmk _ hz
  -- Reverse marked-point matching: `f z ∈ {0, 1, ∞}`.
  exact P1.mapsTo_markedPoints k K _ hmark

end Belyi
