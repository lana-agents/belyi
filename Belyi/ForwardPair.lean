/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.DefinablePairFinite
import Belyi.Forward

/-!
# Pair-definability of the base-changed forward map (the B8 "moreover")

This file supplies the **"moreover" clause of statement B8** of `references/proof-outline.md`
(taxis issue #51): the Belyi pair produced by the forward base-change theorem is itself
*definable over `ℚ̄`*.

Concretely, the forward direction (`Belyi/Forward.lean`,
`Belyi.exists_isBelyiMap_baseChange_of_isCurveOver`) base changes a model map `f₀ : X₀ ⟶ ℙ¹_k`
over `k = ℚ̄` to `Y = pullback f₀ (mapOfAlgebra k K)` with the Belyi map
`f = pullback.snd f₀ (mapOfAlgebra k K) : Y ⟶ ℙ¹_K` (`Belyi.isBelyiMap_baseChange`). The main
result here is that this `f` is `Belyi.DefinableOverPair k K Y f`: it *is* a base change of the
model `f₀`, compatibly with the canonical identification `ℙ¹_k ×_k K ≅ ℙ¹_K`
(`Belyi.P1.toPullback`).

This is the **production (base-change) direction** of pair-definability — unlike the bare
`DefinableOver`-witness wiring of the forward assembly (taxis #188), it does **not** need the
B3c *descent* direction (#167). It is the pair-level strengthening consumed by the marked
base-change layer (taxis #54) and by the main-theorem assembly (taxis #55).

## Main results

* `Belyi.definableOverPair_baseChange`: for any model map `f₀ : X₀ ⟶ ℙ¹_k` and extension
  `k ⊆ K`, the second projection `pullback.snd f₀ (mapOfAlgebra k K)` is definable over `k`.
  The `Over (Spec K)` structure on the pullback is the one forced by
  `DefinableOverPair.comp_structMap` (postcomposition of the projection with `ℙ¹_K ↘ Spec K`),
  supplied via `letI` in the statement.

## Construction

Both `Y = pullback f₀ (mapOfAlgebra k K)` and `pullback p₀ (specAlgebraMap k K)` (the source of
the base-change model `baseChangeModelHom`, `p₀ = f₀ ≫ (ℙ¹_k ↘ Spec k)`) are pullbacks over the
**common cospan** `X₀ --f₀--> ℙ¹_k <--fst-- pullback (ℙ¹_k ↘ Spec k) (specAlgebraMap k K)`:

* the model side is `Belyi.isPullback_baseChangeModelHom` (`Belyi/DefinablePairFinite.lean`);
* the `Y` side is obtained from `IsPullback.of_hasPullback f₀ (mapOfAlgebra k K)` by absorbing
  the isomorphism `P1.toPullback` (`P1.isIso_toPullback`) into the second-projection leg — using
  `mapOfAlgebra k K = toPullback ≫ pullback.fst _ _` (`P1.toPullback_fst`) and `paste_vert` with
  the trivial iso-square `IsPullback.of_vert_isIso`.

The comparison isomorphism `e := IsPullback.isoIsPullback` then intertwines the two second-leg
maps, discharging the pair condition `f ≫ toPullback = e.hom ≫ baseChangeModelHom` directly
(`isoIsPullback_hom_snd`), and the structure-morphism compatibility via `baseChangeModelHom_snd`
+ `P1.toPullback_snd`.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]

/-- **The base-changed forward pair is definable over `k` (B8 "moreover").** For any model map
`f₀ : X₀ ⟶ ℙ¹_k` and an extension `k ⊆ K`, the second projection
`pullback.snd f₀ (mapOfAlgebra k K) : pullback f₀ (mapOfAlgebra k K) ⟶ ℙ¹_K` — the base change of
`f₀` produced by `Belyi.isBelyiMap_baseChange` — is `Belyi.DefinableOverPair k K`, with the model
`f₀` itself.

The `Over (Spec K)` structure on the pullback is the one forced by
`Belyi.DefinableOverPair.comp_structMap` (the projection postcomposed with `ℙ¹_K ↘ Spec K`),
provided here via `letI` so that the structure morphism is definitionally the projection to
`Spec K`; any downstream consumer is free to supply its own. -/
theorem definableOverPair_baseChange {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ P1 k) :
    letI : (pullback f₀ (P1.mapOfAlgebra k K)).Over (Spec (CommRingCat.of K)) :=
      ⟨pullback.snd f₀ (P1.mapOfAlgebra k K) ≫ (P1 K ↘ Spec (CommRingCat.of K))⟩
    DefinableOverPair k K (pullback f₀ (P1.mapOfAlgebra k K))
      (pullback.snd f₀ (P1.mapOfAlgebra k K)) := by
  -- The model source structure morphism `p₀ = f₀ ≫ (ℙ¹_k ↘ Spec k)`.
  set p₀ : X₀ ⟶ Spec (CommRingCat.of k) := f₀ ≫ (P1 k ↘ Spec (CommRingCat.of k)) with hp₀
  -- `Y` is a pullback over the same cospan `(f₀, fst)` as the base-change model, once we absorb
  -- the isomorphism `toPullback` into the second-projection leg.
  have hY : IsPullback (pullback.fst f₀ (P1.mapOfAlgebra k K))
      (pullback.snd f₀ (P1.mapOfAlgebra k K) ≫ P1.toPullback k K) f₀
      (pullback.fst (P1 k ↘ Spec (CommRingCat.of k)) (specAlgebraMap k K)) := by
    have s := IsPullback.of_hasPullback f₀ (P1.mapOfAlgebra k K)
    have t : IsPullback (P1.mapOfAlgebra k K) (P1.toPullback k K) (𝟙 (P1 k))
        (pullback.fst (P1 k ↘ Spec (CommRingCat.of k)) (specAlgebraMap k K)) :=
      IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, P1.toPullback_fst]⟩
    have h := s.paste_vert t
    rwa [Category.comp_id] at h
  -- The base-change model side is a pullback over the same cospan.
  have hbc := isPullback_baseChangeModelHom k K p₀ f₀ rfl
  -- Compare the two pullbacks.
  refine ⟨X₀, p₀, f₀, rfl, hY.isoIsPullback _ _ hbc, ?_, ?_⟩
  · -- structure-morphism compatibility
    rw [← baseChangeModelHom_snd k K p₀ f₀ rfl, ← Category.assoc,
      IsPullback.isoIsPullback_hom_snd, Category.assoc, P1.toPullback_snd]
    rfl
  · -- pair condition `f ≫ toPullback = e.hom ≫ baseChangeModelHom`
    exact (IsPullback.isoIsPullback_hom_snd _ _ _ _).symm

end Belyi
