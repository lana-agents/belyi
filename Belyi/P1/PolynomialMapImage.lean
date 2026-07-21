/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.PolynomialFinite
import Belyi.P1.Points

/-!
# B4c (images): where the polynomial self-map sends the affine points

For a non-constant `g : k[X]` the self-map `Belyi.P1.polynomialSelfMap g : ℙ¹ ⟶ ℙ¹`
(realizing `x ↦ g(x)` on the affine chart `D₊(X₁)`, taxis issue #106) acts on the affine
closed points as `[a : 1] ↦ [g(a) : 1]`. This is the point-level half of statement **B4c**
(taxis issue #108) for the affine chart: it identifies the images of the affine points with
the values of `g`, one of the two inputs the branch-locus identification consumes (the
other being that `∞` is fixed).

## Main results

* `Belyi.P1.polynomialSelfMap_point`: `polynomialSelfMap g [a : 1] = [g(a) : 1]` for the
  `K`-point with affine coordinate `a` in a field extension `K/k`.
* `Belyi.P1.polynomialSelfMap_point_closedPoint`: the specialisation to `K = k`.

The complementary facts of B4c — that `∞` is fixed, and the resulting branch-locus
identification `Branch (polynomialSelfMap g) ⊆ {g(a) : g'(a) = 0} ∪ {∞}` — are follow-up
work on issue #108, building on the affine identification here.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open scoped Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (g : k[X])

/-- **B4c (affine points).** The polynomial self-map sends the closed point with affine
coordinate `a` in a field extension `K/k` to the closed point with affine coordinate
`g(a)`: `polynomialSelfMap g [a : 1] = [g(a) : 1]`. This is the naturality
`point_comp_polynomialSelfMap` evaluated at the closed point of `Spec K`. -/
lemma polynomialSelfMap_point (hd : 0 < g.natDegree) {K : Type u} [Field K] [Algebra k K]
    (a : K) :
    polynomialSelfMap k g hd (point k a (IsLocalRing.closedPoint K)) =
      point k (Polynomial.aeval a g) (IsLocalRing.closedPoint K) := by
  rw [← Scheme.Hom.comp_apply, point_comp_polynomialSelfMap k g hd a]

/-- The image of the affine `k`-point `[a : 1]` under the polynomial self-map is
`[g(a) : 1]`. -/
lemma polynomialSelfMap_point_closedPoint (hd : 0 < g.natDegree) (a : k) :
    polynomialSelfMap k g hd (point k (a : k) (IsLocalRing.closedPoint k)) =
      point k (Polynomial.aeval a g) (IsLocalRing.closedPoint k) :=
  polynomialSelfMap_point k g hd a

end Belyi.P1
