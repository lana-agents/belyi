/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Forward
import Belyi.MarkedBaseChange
import Belyi.DefinablePairFinite

/-!
# Pair-definability of the Belyi maps produced by the forward direction (the "moreover" of B8/B13)

The forward direction (`Belyi/Forward.lean`, B8) and its marked strengthening
(`Belyi/MarkedBaseChange.lean`, B13) produce, for a curve `X₀` over `ℚ̄` and an extension field
`K` (the model case `K = ℂ`), a Belyi map `f : Y ⟶ ℙ¹_K` on the base change
`Y = X₀ ×_{ℙ¹_{ℚ̄}} ℙ¹_K = pullback f₀ (mapOfAlgebra ℚ̄ K)`.  Both files flag as follow-up the
**"moreover"** clause of the outline: the pair `(Y, f)` is itself *definable over `ℚ̄`*
(`Belyi.DefinableOverPair`), which the marked-curve / Belyi-cuspidalization consumers (successors
of taxis issue #8) consume.

This file supplies that clause.  The heart is a single reusable lemma, valid for **any** model
morphism `f₀ : X₀ ⟶ ℙ¹_{k}` and **any** extension `k ⊆ K` (only `CommRing`s are needed):

* `Belyi.definableOverPair_pullback_snd_mapOfAlgebra` : the base change
  `pullback.snd f₀ (mapOfAlgebra k K) : pullback f₀ (mapOfAlgebra k K) ⟶ ℙ¹_K` is definable over
  `k`, with model `f₀`.

Its proof is pure pullback bookkeeping — no descent, no missing infrastructure.  The base change
`pullback f₀ (mapOfAlgebra k K)` (a pullback over `ℙ¹_k`) is identified with the
`DefinableOverPair` shape `pullback (f₀ ≫ (ℙ¹_k ↘ Spec k)) (specAlgebraMap k K)` (a pullback over
`Spec k`) by:

1. absorbing the canonical identification `Belyi.P1.toPullback k K : ℙ¹_K ≅ ℙ¹_k ×_{Spec k} Spec K`
   (an isomorphism by `Belyi.P1.isIso_toPullback`) into the right leg via `pullback.map`, then
2. pasting with `CategoryTheory.Limits.pullbackRightPullbackFstIso`.

The two `DefinableOverPair` conditions then reduce, through the `@[simp]` projection lemmas
`toPullback_fst`/`toPullback_snd`, `baseChangeModelHom_fst`/`_snd` and the
`pullbackRightPullbackFstIso` projections, to `pullback.condition`.

Combining this with the merged forward / marked base-change Belyi results gives the packaged
"moreover" theorems:

* `Belyi.exists_definableOverPair_isBelyiMap_baseChange_of_isCurveOver` (forward, B8),
* `Belyi.exists_definableOverPair_isBelyiMap_marked_baseChange_of_isCurveOver` (marked, B13).

Both are unconditional on the base-change side and stay off the research-grade *descent* frontier
(#167/#168): they only ever **produce** a model, never descend one.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

section Core

variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]
  {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ P1 k)

/-- The canonical isomorphism identifying the base change of a `ℙ¹`-morphism as a pullback over
`ℙ¹_k` with the base change of its source as a pullback over `Spec k` (the shape used by
`Belyi.DefinableOverPair`):
```
  pullback f₀ (mapOfAlgebra k K) ≅ pullback (f₀ ≫ (ℙ¹_k ↘ Spec k)) (specAlgebraMap k K).
```
Built by absorbing the identification `Belyi.P1.toPullback k K` (an iso) into the right leg via
`pullback.map`, then pasting with `pullbackRightPullbackFstIso`. -/
noncomputable def pullbackMapOfAlgebraIso :
    pullback f₀ (P1.mapOfAlgebra k K) ≅
      pullback (f₀ ≫ (P1 k ↘ Spec (CommRingCat.of k))) (specAlgebraMap k K) :=
  (asIso (pullback.map f₀ (P1.mapOfAlgebra k K) f₀
      (pullback.fst (P1 k ↘ Spec (CommRingCat.of k)) (specAlgebraMap k K))
      (𝟙 X₀) (P1.toPullback k K) (𝟙 (P1 k))
      (by simp)
      (by rw [Category.comp_id, P1.toPullback_fst]))) ≪≫
    pullbackRightPullbackFstIso (P1 k ↘ Spec (CommRingCat.of k)) (specAlgebraMap k K) f₀

@[reassoc (attr := simp)]
lemma pullbackMapOfAlgebraIso_hom_fst :
    (pullbackMapOfAlgebraIso k K f₀).hom ≫
        pullback.fst (f₀ ≫ (P1 k ↘ Spec (CommRingCat.of k))) (specAlgebraMap k K) =
      pullback.fst f₀ (P1.mapOfAlgebra k K) := by
  simp only [pullbackMapOfAlgebraIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullbackRightPullbackFstIso_hom_fst, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
lemma pullbackMapOfAlgebraIso_hom_snd :
    (pullbackMapOfAlgebraIso k K f₀).hom ≫
        pullback.snd (f₀ ≫ (P1 k ↘ Spec (CommRingCat.of k))) (specAlgebraMap k K) =
      pullback.snd f₀ (P1.mapOfAlgebra k K) ≫ (P1 K ↘ Spec (CommRingCat.of K)) := by
  simp only [pullbackMapOfAlgebraIso, Iso.trans_hom, asIso_hom, Category.assoc,
    pullbackRightPullbackFstIso_hom_snd, pullback.lift_snd_assoc, P1.toPullback_snd]

/-- **The pair-definability "moreover" of the forward/marked base change, core form.** For any
model morphism `f₀ : X₀ ⟶ ℙ¹_k` and any extension `k ⊆ K`, the base change
`pullback.snd f₀ (mapOfAlgebra k K) : pullback f₀ (mapOfAlgebra k K) ⟶ ℙ¹_K` is definable over
`k`, with model `f₀`.

The `DefinableOverPair` witness uses the model `f₀`, the structure morphism
`f₀ ≫ (ℙ¹_k ↘ Spec k)`, and the identification `pullbackMapOfAlgebraIso`. -/
lemma definableOverPair_pullback_snd_mapOfAlgebra
    [inst : (pullback f₀ (P1.mapOfAlgebra k K)).Over (Spec (CommRingCat.of K))]
    (hover : pullback f₀ (P1.mapOfAlgebra k K) ↘ Spec (CommRingCat.of K) =
        pullback.snd f₀ (P1.mapOfAlgebra k K) ≫ (P1 K ↘ Spec (CommRingCat.of K))) :
    DefinableOverPair k K (pullback f₀ (P1.mapOfAlgebra k K))
      (pullback.snd f₀ (P1.mapOfAlgebra k K)) := by
  refine ⟨X₀, f₀ ≫ (P1 k ↘ Spec (CommRingCat.of k)), f₀, rfl,
    pullbackMapOfAlgebraIso k K f₀, ?_, ?_⟩
  · -- `hsnd`: the identification is compatible with the structure morphisms.
    rw [hover, pullbackMapOfAlgebraIso_hom_snd]
  · -- the pair condition, checked leg-by-leg into the base change of `ℙ¹_k`.
    apply pullback.hom_ext
    · -- `fst` leg: both sides equal `pullback.fst f₀ (mapOfAlgebra k K) ≫ f₀`.
      rw [Category.assoc, Category.assoc, P1.toPullback_fst, baseChangeModelHom_fst,
        pullbackMapOfAlgebraIso_hom_fst_assoc]
      exact pullback.condition.symm
    · -- `snd` leg: both sides equal the structure morphism of the base change.
      rw [Category.assoc, Category.assoc, P1.toPullback_snd, baseChangeModelHom_snd,
        pullbackMapOfAlgebraIso_hom_snd]

end Core

/-- **Forward direction of Belyi's theorem, base change with pair-definability (B8, "moreover").**
For a curve `X₀` over an algebraically closed field `k` of characteristic zero that is algebraic
over `ℚ` (i.e. over `ℚ̄`) and an arbitrary extension field `K` (the model case `K = ℂ`), the base
change `Y = X₀ ×_{ℙ¹_k} ℙ¹_K` carries a Belyi map `f : Y ⟶ ℙ¹_K` that is moreover **definable
over `ℚ̄`** as a pair, with model the Belyi map `f₀ : X₀ ⟶ ℙ¹_k` produced by
`Belyi.exists_isBelyiMap_of_isCurveOver`. -/
theorem exists_definableOverPair_isBelyiMap_baseChange_of_isCurveOver
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
    (K : Type u) [Field K] [Algebra k K]
    (X₀ : Scheme.{u}) [X₀.Over (Spec (CommRingCat.of k))] [IsCurveOver k X₀] :
    ∃ (Y : Scheme.{u}) (hY : Y.Over (Spec (CommRingCat.of K))) (f : Y ⟶ P1 K),
      IsBelyiMap K f ∧ @DefinableOverPair k K _ _ _ Y hY f := by
  obtain ⟨f₀, hf₀, -⟩ := exists_isBelyiMap_of_isCurveOver k X₀
  letI hY : (pullback f₀ (P1.mapOfAlgebra k K)).Over (Spec (CommRingCat.of K)) :=
    ⟨pullback.snd f₀ (P1.mapOfAlgebra k K) ≫ (P1 K ↘ Spec (CommRingCat.of K))⟩
  refine ⟨pullback f₀ (P1.mapOfAlgebra k K), hY,
    pullback.snd f₀ (P1.mapOfAlgebra k K), isBelyiMap_baseChange k K hf₀, ?_⟩
  exact definableOverPair_pullback_snd_mapOfAlgebra k K f₀ rfl

/-- **Marked forward direction of Belyi's theorem, base change with pair-definability
(B13, "moreover").** For a curve `X₀` over `ℚ̄`, a finite set `S` of closed points, and an
extension field `K` (the model case `K = ℂ`), the base change `Y = X₀ ×_{ℙ¹_k} ℙ¹_K` — with its
projection `π : Y ⟶ X₀` — carries a Belyi map `f : Y ⟶ ℙ¹_K` such that

* every point of `Y` over `S` maps into the marked set `{0, 1, ∞}` of `ℙ¹_K`, and
* the pair `(Y, f)` is **definable over `ℚ̄`**, with model the marked Belyi map `f₀`.

This is exactly the packaging the Belyi-cuspidalization consumers (successors of taxis issue #8)
require; the underlying `MarkedBelyiPair` structure, whose precise shape is to be coordinated with
the maintainers, can be built directly on top of this statement. -/
theorem exists_definableOverPair_isBelyiMap_marked_baseChange_of_isCurveOver
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
    (K : Type u) [Field K] [Algebra k K]
    (X₀ : Scheme.{u}) [X₀.Over (Spec (CommRingCat.of k))] [IsCurveOver k X₀]
    (S : Set X₀) (hSfin : S.Finite) (hScl : ∀ s ∈ S, IsClosed ({s} : Set X₀)) :
    ∃ (Y : Scheme.{u}) (hY : Y.Over (Spec (CommRingCat.of K))) (π : Y ⟶ X₀) (f : Y ⟶ P1 K),
      IsBelyiMap K f ∧ (∀ z : Y, π.base z ∈ S → f.base z ∈ markedPoints K) ∧
      @DefinableOverPair k K _ _ _ Y hY f := by
  obtain ⟨f₀, hf₀, hmk⟩ := exists_isBelyiMap_marked_of_isCurveOver k X₀ S hSfin hScl
  letI hY : (pullback f₀ (P1.mapOfAlgebra k K)).Over (Spec (CommRingCat.of K)) :=
    ⟨pullback.snd f₀ (P1.mapOfAlgebra k K) ≫ (P1 K ↘ Spec (CommRingCat.of K))⟩
  refine ⟨pullback f₀ (P1.mapOfAlgebra k K), hY,
    pullback.fst f₀ (P1.mapOfAlgebra k K), pullback.snd f₀ (P1.mapOfAlgebra k K),
    isBelyiMap_baseChange k K hf₀, ?_, ?_⟩
  · -- marked-point tracking (as in `MarkedBaseChange.lean`).
    intro z hz
    have hsq := IsPullback.of_hasPullback f₀ (P1.mapOfAlgebra k K)
    have hw : f₀.base ((pullback.fst f₀ (P1.mapOfAlgebra k K)).base z) =
        (P1.mapOfAlgebra k K).base ((pullback.snd f₀ (P1.mapOfAlgebra k K)).base z) := by
      have h := congrArg (fun m => m.base z) hsq.w
      rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
    have hmark : (P1.mapOfAlgebra k K).base ((pullback.snd f₀ (P1.mapOfAlgebra k K)).base z) ∈
        markedPoints k := hw ▸ hmk _ hz
    exact P1.mapsTo_markedPoints k K _ hmark
  · exact definableOverPair_pullback_snd_mapOfAlgebra k K f₀ rfl

end Belyi
