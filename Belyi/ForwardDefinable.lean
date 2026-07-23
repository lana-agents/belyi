/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Curve.BaseChange
import Belyi.ForwardPair

/-!
# Forward direction of Belyi's theorem from a curve model (bare-`DefinableOver` wiring, B8)

The forward direction proved in `Belyi/Forward.lean` produces a Belyi map on a curve **presented
with its own `ℚ̄`-model** (`exists_isBelyiMap_of_isCurveOver`) or, after base change, on the
canonical pullback `pullback f₀ (mapOfAlgebra k K)` (`exists_isBelyiMap_baseChange_of_isCurveOver`).
This file supplies the last piece of the forward assembly (taxis #188): wiring an *arbitrary*
scheme `X` over `K` that is isomorphic to the base change of a `ℚ̄`-curve model through to a Belyi
map on `X` **itself**, by transporting the base-changed Belyi map along the definability
isomorphism.

* `Belyi.exists_isBelyiMap_of_isCurveOver_baseChangeModel` : if `X` (over `K`) is isomorphic to
  `X₀ ×_{Spec k} Spec K` for a curve `X₀` over `k = ℚ̄`, then `X` admits a Belyi map over `K`.

This is exactly the shape a `Belyi.DefinableOver k K X` witness unpacks to, with the model
`X₀` presented via its structure morphism `X₀ ↘ Spec k`.  The only missing input to conclude the
full "`X/ℂ` definable over `ℚ̄` ⇒ `X` admits a Belyi map" from a *bare* `DefinableOver` witness is
then the **B3c descent** direction — that a `ℂ`-curve definable over `ℚ̄` has a model that is
itself a `ℚ̄`-curve, i.e. the `[IsCurveOver k X₀]` instance (taxis #167, research-grade against
mathlib v4.32).  Everything on the forward side of that gap is discharged here.

## Method

Given the Belyi map `f₀ : X₀ ⟶ ℙ¹_k` from `exists_isBelyiMap_of_isCurveOver` — which is moreover a
`k`-morphism, so `f₀ ≫ (ℙ¹_k ↘ Spec k) = X₀ ↘ Spec k` — the base change
`g = pullback.snd f₀ (mapOfAlgebra k K)` is a Belyi map over `K` (`isBelyiMap_baseChange`).  The
identification `pullbackMapOfAlgebraIso` (`Belyi/ForwardPair.lean`) rewrites its source
`pullback f₀ (mapOfAlgebra k K)` as `pullback (f₀ ≫ (ℙ¹_k ↘ Spec k)) (specAlgebraMap k K)`, and
`pullback.congrHom` (using the `k`-morphism equation) turns that into
`pullback (X₀ ↘ Spec k) (specAlgebraMap k K)` — precisely the target of the definability iso `e`.
Composing `e` with this identification gives an isomorphism `X ≅ pullback f₀ (mapOfAlgebra k K)`,
along which `IsBelyiMap.of_isIso_comp` transports `g` to a Belyi map on `X`.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

/-- **Forward direction of Belyi's theorem, definable form (B8).** If a scheme `X` over an
extension field `K` of `k = ℚ̄` (algebraically closed, characteristic zero, algebraic over `ℚ`;
the model case `K = ℂ`) is isomorphic to the base change `X₀ ×_{Spec k} Spec K` of a **curve**
`X₀` over `k`, then `X` admits a Belyi map `f : X ⟶ ℙ¹_K`.

The Belyi map is the base-changed model Belyi map from `exists_isBelyiMap_of_isCurveOver`,
transported to `X` along the definability isomorphism `e`.  This is the wiring the main theorem
(taxis #55) consumes on the forward side; the remaining input to feed it from a bare
`Belyi.DefinableOver k K X` witness is the B3c descent instance `[IsCurveOver k X₀]` (taxis
#167). -/
theorem exists_isBelyiMap_of_isCurveOver_baseChangeModel
    (k K : Type u) [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
    [Field K] [Algebra k K]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))]
    (X₀ : Scheme.{u}) [X₀.Over (Spec (CommRingCat.of k))] [IsCurveOver k X₀]
    (e : X ≅ pullback (X₀ ↘ Spec (CommRingCat.of k)) (specAlgebraMap k K)) :
    ∃ f : X ⟶ P1 K, IsBelyiMap K f := by
  -- Forward direction on the model: a Belyi map `f₀ : X₀ ⟶ ℙ¹_k`, itself a `k`-morphism.
  obtain ⟨f₀, hf₀, hf₀over⟩ := exists_isBelyiMap_of_isCurveOver k X₀
  haveI : f₀.IsOver (Spec (CommRingCat.of k)) := hf₀over
  -- Base change to `K`: a Belyi map `g` on `Y = pullback f₀ (mapOfAlgebra k K)`.
  have hg : IsBelyiMap K (pullback.snd f₀ (P1.mapOfAlgebra k K)) := isBelyiMap_baseChange k K hf₀
  -- `f₀` is a `k`-morphism, so its `ℙ¹_k`-structure map composes to the structure map of `X₀`.
  have hcomp : f₀ ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X₀ ↘ Spec (CommRingCat.of k) :=
    comp_over f₀ (Spec (CommRingCat.of k))
  -- Identify `Y` with the target of the definability iso `e`, and build `X ≅ Y`.
  let ι : pullback f₀ (P1.mapOfAlgebra k K) ≅
      pullback (X₀ ↘ Spec (CommRingCat.of k)) (specAlgebraMap k K) :=
    pullbackMapOfAlgebraIso k K f₀ ≪≫ pullback.congrHom hcomp rfl
  let φ : X ≅ pullback f₀ (P1.mapOfAlgebra k K) := e ≪≫ ι.symm
  -- Transport the Belyi map `g` on `Y` back to `X` along the isomorphism `φ`.
  haveI : LocallyOfFinitePresentation (pullback.snd f₀ (P1.mapOfAlgebra k K)) :=
    hg.locallyOfFinitePresentation
  haveI : LocallyOfFinitePresentation (φ.hom ≫ pullback.snd f₀ (P1.mapOfAlgebra k K)) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFinitePresentation)
      φ.hom (pullback.snd f₀ (P1.mapOfAlgebra k K))).mpr ‹_›
  exact ⟨φ.hom ≫ pullback.snd f₀ (P1.mapOfAlgebra k K), hg.of_isIso_comp φ.hom⟩

/-- **Forward direction of Belyi's theorem, bare-`DefinableOver` form (B8).** A curve `X` over an
extension field `K` of `k = ℚ̄` (algebraically closed, characteristic zero, algebraic over `ℚ`;
the model case `K = ℂ`) that is *definable over `k`* — `Belyi.DefinableOver k K X` — admits a Belyi
map `f : X ⟶ ℙ¹_K`.

This is the final connector of the forward assembly (taxis #188): it feeds a *bare*
`Belyi.DefinableOver` witness into `exists_isBelyiMap_of_isCurveOver_baseChangeModel`.  Unpacking
the witness gives a model `X₀` over `k` with structure morphism `f₀` and an isomorphism
`e : X ≅ pullback f₀ (specAlgebraMap k K)`; equipping `X₀` with the `Over (Spec k)` structure `⟨f₀⟩`
turns `e` into the shape both `IsCurveOver.of_baseChangeModel` and the transport lemma consume.  The
descent `IsCurveOver.of_baseChangeModel` supplies the `[IsCurveOver k X₀]` instance — a `ℂ`-curve
definable over `ℚ̄` has a `ℚ̄`-curve model — which is exactly the previously-missing input.

Like `IsCurveOver.of_baseChangeModel`, this is gated on the single remaining
`MorphismProperty.DescendsAlong (@SmoothOfRelativeDimension 1)` instance (taxis #205/#167).  The
moment that instance lands globally, this theorem fires unconditionally and discharges the
`hforward` hypothesis of `Belyi.belyi_iff` (`Belyi/Main.lean`, taxis #55) in a single step,
upgrading the headline `belyi_iff` to its ungated form. -/
theorem exists_isBelyiMap_of_definableOver
    (k K : Type u) [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
    [Field K] [Algebra k K]
    [MorphismProperty.DescendsAlong (@SmoothOfRelativeDimension 1)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X]
    (hdef : DefinableOver k K X) :
    ∃ f : X ⟶ P1 K, IsBelyiMap K f := by
  obtain ⟨X₀, f₀, e, he⟩ := hdef
  letI : X₀.Over (Spec (CommRingCat.of k)) := ⟨f₀⟩
  haveI : IsCurveOver k X₀ := IsCurveOver.of_baseChangeModel k K X₀ e he
  exact exists_isBelyiMap_of_isCurveOver_baseChangeModel k K X X₀ e

end Belyi
