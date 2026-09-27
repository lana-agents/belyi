/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Converse.DefinableOfBelyi
import Belyi.Converse.RigidityC

/-!
# The converse direction of Belyi's theorem (B12)

A curve `X` over an algebraically closed field `K` of characteristic zero that admits a Belyi map
is definable over any algebraically closed subfield `k ⊆ K` that is algebraic over `ℚ` (i.e. over
`ℚ̄`).

This assembles the proof laid out in `references/converse-rie-design.md`:

* `Belyi.Converse.rigidityOverC` — finite étale families over a smooth connected base have
  isomorphic fibres at any two `ℂ`-points (Riemann existence, via `oka`);
* `Belyi.Converse.fEtDescent_of_rigidity` — hence finite étale covers of affine `k`-schemes of
  finite type descend from `K` to `k` (statement (★));
* `Belyi.Converse.definableOver_of_isBelyiMap_of_fEtDescent` — applied to the restriction of a
  Belyi map over `ℙ¹ ∖ {0, 1, ∞}` and followed by relative normalization, (★) produces a
  `k`-model of `X`.

## Main results

* `Belyi.Converse.fEtDescent`: statement (★), unconditionally.
* `Belyi.definableOver_of_exists_isBelyiMap` (**B12**): the converse of Belyi's theorem.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace Belyi

namespace Converse

/-- **Descent of finite étale covers (★).** For algebraically closed fields `k ⊆ K` of
characteristic zero with `k` algebraic over `ℚ`, every finite étale cover of `Spec (K ⊗[k] R)`,
`R` a finitely generated `k`-algebra, is the base change of a finite étale cover of `Spec R`. -/
theorem fEtDescent (k K : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    [Algebra.IsAlgebraic ℚ k] [Field K] [IsAlgClosed K] [Algebra k K] : FEtDescent k K :=
  fEtDescent_of_rigidity k K fun {_} ↦ rigidityOverC k

end Converse

/-- **B12 (converse of Belyi's theorem).** A curve `X` over `K` (algebraically closed,
characteristic zero; e.g. `K = ℂ`) that admits a Belyi map is definable over `k` (algebraically
closed, characteristic zero, algebraic over `ℚ`; i.e. `k = ℚ̄`). -/
theorem definableOver_of_exists_isBelyiMap (k K : Type u) [Field k] [IsAlgClosed k]
    [CharZero k] [Algebra.IsAlgebraic ℚ k] [Field K] [IsAlgClosed K] [CharZero K]
    [Algebra k K] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X]
    (h : ∃ f : X ⟶ P1 K, IsBelyiMap K f) : DefinableOver k K X := by
  obtain ⟨f, hf⟩ := h
  exact Converse.definableOver_of_isBelyiMap_of_fEtDescent k K (Converse.fEtDescent k K) X f hf

end Belyi
