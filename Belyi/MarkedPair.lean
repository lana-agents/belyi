/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.ForwardPair

/-!
# The `MarkedBelyiPair` structure — a single package for the marked forward direction (B13)

The marked forward direction of Belyi's theorem (statement **B13** of
`references/proof-outline.md`) is delivered across several files as a chain of existence
theorems:

* `Belyi.exists_isBelyiMap_marked_of_isCurveOver` (`Belyi/Marked.lean`) — the model form;
* `Belyi.exists_isBelyiMap_marked_baseChange_of_isCurveOver` (`Belyi/MarkedBaseChange.lean`) —
  the base change to an extension `K` (the model case `K = ℂ`);
* `Belyi.exists_definableOverPair_isBelyiMap_marked_baseChange_of_isCurveOver`
  (`Belyi/ForwardPair.lean`) — the same, with the pair `(Y, f)` moreover *definable over `ℚ̄`*.

The Belyi-cuspidalization consumers (the successors of taxis issue #8) want to *hold* this data
as a single object rather than repeatedly `obtain` it out of a nested existential.  This file
bundles it into a structure.

## Main definitions

* `Belyi.MarkedBelyiPair k K X₀ S` — a scheme `Y` over `K` with a projection `π : Y ⟶ X₀` to a
  model `X₀` over `k`, a Belyi map `f : Y ⟶ ℙ¹_K`, the containment of the marked fibre
  (`π z ∈ S → f z ∈ {0, 1, ∞}`), and a witness that `(Y, f)` is `Belyi.DefinableOverPair k K`.
  The structure fixes only `[Field k] [Field K] [Algebra k K]`, so it is reusable; the strong
  hypotheses on `k` (`= ℚ̄`) live on the constructor.

* `Belyi.MarkedBelyiPair.ofIsCurveOver` — the constructor: for a curve `X₀` over `ℚ̄` and a finite
  set `S` of closed points, base change to `K` produces a `MarkedBelyiPair`.  This is exactly the
  existence theorem `exists_definableOverPair_isBelyiMap_marked_baseChange_of_isCurveOver`
  repackaged as data (via choice, hence `noncomputable`).

## Design note

The `Over (Spec K)` structure on `Y` is stored as a field (`over`) and registered as an instance
(`attribute [instance] MarkedBelyiPair.over`), matching the way the source existence theorem
existentially quantifies the `Over` witness.  The precise API these consumers need is to be
coordinated with the maintainers before it is treated as final; the structure here is the minimal
faithful packaging of what B13 already proves, and further accessors can be layered on top without
touching the geometry.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

/-- A **marked Belyi pair** over an extension `k ⊆ K`, with model source `X₀` over `k` and marked
set `S ⊆ X₀`.  This bundles the full output of the marked forward direction (B13):

* a scheme `Y` over `K` with a projection `π : Y ⟶ X₀` (the base change `Y = X₀ ×_{ℙ¹_k} ℙ¹_K`
  in the produced instances);
* a Belyi map `f : Y ⟶ ℙ¹_K` (`isBelyiMap`);
* the marked-fibre containment: every point of `Y` lying over `S` is sent into `{0, 1, ∞}`
  (`marked`);
* a witness that the pair `(Y, f)` is definable over `k` (`= ℚ̄`) with the model `f₀`
  (`definable`).

Only `[Field k] [Field K] [Algebra k K]` are assumed here; the constructor
`MarkedBelyiPair.ofIsCurveOver` supplies the arithmetic hypotheses on `k`. -/
structure MarkedBelyiPair (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X₀ : Scheme.{u}) (S : Set X₀) where
  /-- The base-changed curve carrying the Belyi map (the model case is `Y = X₀ ×_ℚ̄ ℂ`). -/
  Y : Scheme.{u}
  /-- `Y` is a scheme over `K`. -/
  over : Y.Over (Spec (CommRingCat.of K))
  /-- The projection to the model source `X₀`. -/
  π : Y ⟶ X₀
  /-- The Belyi map on `Y`. -/
  f : Y ⟶ P1 K
  /-- `f` is a Belyi map: finite, locally of finite presentation, branched only over
  `{0, 1, ∞}`. -/
  isBelyiMap : IsBelyiMap K f
  /-- Every point of `Y` lying over the marked set `S` is carried into the fibre over
  `{0, 1, ∞}`. -/
  marked : ∀ z : Y, π.base z ∈ S → f.base z ∈ markedPoints K
  /-- The pair `(Y, f)` is definable over `k` (`= ℚ̄`). -/
  definable : @DefinableOverPair k K _ _ _ Y over f

attribute [instance] MarkedBelyiPair.over

namespace MarkedBelyiPair

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X₀ : Scheme.{u}} {S : Set X₀}

/-- The marked-fibre containment as an inclusion of sets: `π ⁻¹ S ⊆ f ⁻¹ {0, 1, ∞}`. -/
lemma preimage_subset (P : MarkedBelyiPair k K X₀ S) :
    P.π.base ⁻¹' S ⊆ P.f.base ⁻¹' markedPoints K :=
  fun _ hz => P.marked _ hz

/-- Forgetting the marked-point and definability data, a `MarkedBelyiPair` gives a Belyi map on
its total space. -/
lemma exists_isBelyiMap (P : MarkedBelyiPair k K X₀ S) : ∃ f : P.Y ⟶ P1 K, IsBelyiMap K f :=
  ⟨P.f, P.isBelyiMap⟩

end MarkedBelyiPair

/-- **Constructor for `MarkedBelyiPair` (B13, packaged).** For a curve `X₀` over an algebraically
closed field `k` of characteristic zero that is algebraic over `ℚ` (i.e. over `ℚ̄`), a finite set
`S` of closed points of `X₀`, and an arbitrary extension field `K` (the model case `K = ℂ`), the
base change of `X₀` to `K` assembles into a `MarkedBelyiPair k K X₀ S`.

This is the existence theorem
`Belyi.exists_definableOverPair_isBelyiMap_marked_baseChange_of_isCurveOver` repackaged as data
(via `Classical.choice`, hence `noncomputable`). -/
noncomputable def MarkedBelyiPair.ofIsCurveOver
    (k K : Type u) [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
    [Field K] [Algebra k K]
    (X₀ : Scheme.{u}) [X₀.Over (Spec (CommRingCat.of k))] [IsCurveOver k X₀]
    (S : Set X₀) (hSfin : S.Finite) (hScl : ∀ s ∈ S, IsClosed ({s} : Set X₀)) :
    MarkedBelyiPair k K X₀ S :=
  let h := exists_definableOverPair_isBelyiMap_marked_baseChange_of_isCurveOver k K X₀ S hSfin hScl
  { Y := h.choose
    over := h.choose_spec.choose
    π := h.choose_spec.choose_spec.choose
    f := h.choose_spec.choose_spec.choose_spec.choose
    isBelyiMap := h.choose_spec.choose_spec.choose_spec.choose_spec.1
    marked := h.choose_spec.choose_spec.choose_spec.choose_spec.2.1
    definable := h.choose_spec.choose_spec.choose_spec.choose_spec.2.2 }

end Belyi
