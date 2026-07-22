/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.PolynomialBranchLocus
import Belyi.P1.AffineMarkedPoint

/-!
# B4 bridge: the polynomial self-map is a Belyi self-map when its critical values lie in `{0, 1}`

For a non-constant `g : k[X]` over an algebraically closed field `k` of characteristic zero, the
merged branch-locus bound
`Belyi.P1.branch_polynomialSelfMap_subset` (`Belyi/P1/PolynomialBranchLocus.lean`) phrases the
finite branch points of `polynomialSelfMap g` as affine critical values
`(point k (aeval a g)).base closedPoint` with `aeval a (derivative g) = 0`, plus the point at
infinity.  The value → marked-point dictionary
`Belyi.P1.point_base_eq_zero` / `point_base_eq_one` (`Belyi/P1/AffineMarkedPoint.lean`, taxis #189)
identifies those two affine points at the values `0` and `1` with the marked points `zero k` and
`one k`.

Combining the two, this file discharges the last quantitative input of the forward direction: as
soon as **every critical value of `g` lies in `{0, 1}`**, the branch locus of the polynomial
self-map is contained in `markedPoints k = {0, 1, ∞}`.  This is exactly the `hbg` hypothesis of the
already-merged B8 glue `Belyi.P1.isBelyiMap_comp_polynomialSelfMap`, so we also package the B8
corollary that consumes it (forward direction, taxis #190, parent #51).

## Main results

* `Belyi.P1.branch_polynomialSelfMap_subset_markedPoints`: if `∀ a, g'(a) = 0 → g(a) ∈ {0, 1}`,
  then `Branch (polynomialSelfMap g) ⊆ markedPoints k`.
* `Belyi.P1.isBelyiMap_comp_polynomialSelfMap_of_critVal`: the B8 corollary — for a finite
  `f : X ⟶ ℙ¹` with `polynomialSelfMap g '' Branch f ⊆ {0, 1, ∞}` and critical values of `g` in
  `{0, 1}`, the composite `f ≫ polynomialSelfMap g` is a Belyi map.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped Polynomial

variable (k : Type u) [Field k] (g : k[X]) (hd : 0 < g.natDegree)

noncomputable local instance instLOFP_polynomialSelfMap'' :
    LocallyOfFinitePresentation (polynomialSelfMap k g hd) :=
  locallyOfFinitePresentation_polynomialSelfMap k g hd

/-- **The branch locus of the polynomial self-map lands in `{0, 1, ∞}` when its critical values
do.** Over an algebraically closed field of characteristic zero, if every critical value of `g`
(a value `g(a)` at a root `a` of `g'`) lies in `{0, 1}`, then every branch point of
`polynomialSelfMap g` is one of the marked points `0`, `1`, `∞`.  The finite affine branch points
are the critical values `[g(a) : 1]` (`branch_polynomialSelfMap_subset`), which the value →
marked-point dictionary `point_base_eq_zero` / `point_base_eq_one` (#189) identifies with `zero k`
or `one k`; the remaining branch point is `∞ = infty k`. -/
theorem branch_polynomialSelfMap_subset_markedPoints [IsAlgClosed k] [CharZero k]
    (hcrit : ∀ a : k, Polynomial.aeval a (Polynomial.derivative g) = 0 →
      Polynomial.aeval a g = 0 ∨ Polynomial.aeval a g = 1) :
    Branch (polynomialSelfMap k g hd) ⊆ Belyi.markedPoints k := by
  intro y hy
  rcases branch_polynomialSelfMap_subset k g hd hy with ⟨a, hderiv, hya⟩ | hyinf
  · -- affine critical branch point `[g(a) : 1]`, with `g(a) ∈ {0, 1}`
    rcases hcrit a hderiv with h0 | h1
    · rw [hya, h0, point_base_eq_zero k]
      exact Belyi.zero_mem_markedPoints k
    · rw [hya, h1, point_base_eq_one k]
      exact Belyi.one_mem_markedPoints k
  · -- point at infinity
    rw [Set.mem_singleton_iff] at hyinf
    rw [hyinf]
    exact Belyi.infty_mem_markedPoints k

/-- **B8 corollary.** For a finite morphism `f : X ⟶ ℙ¹` (locally of finite presentation) whose
branch points are carried into `{0, 1, ∞}` by the polynomial self-map, and a polynomial `g` whose
critical values all lie in `{0, 1}`, the composite `f ≫ polynomialSelfMap g` is a Belyi map.  The
self-map's own branch-locus hypothesis (`hbg`) is discharged by
`branch_polynomialSelfMap_subset_markedPoints`, so only the branch-value hypothesis on `f` (`hbf`)
and the critical-value hypothesis on `g` remain.  This is the glue the forward direction (B8, taxis
#51) consumes. -/
theorem isBelyiMap_comp_polynomialSelfMap_of_critVal [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (f : X ⟶ P1 k) [IsFinite f] [LocallyOfFinitePresentation f]
    (hcrit : ∀ a : k, Polynomial.aeval a (Polynomial.derivative g) = 0 →
      Polynomial.aeval a g = 0 ∨ Polynomial.aeval a g = 1)
    (hbf : (polynomialSelfMap k g hd) '' Branch f ⊆ Belyi.markedPoints k) :
    Belyi.IsBelyiMap k (f ≫ polynomialSelfMap k g hd) :=
  isBelyiMap_comp_polynomialSelfMap k g hd f hbf
    (branch_polynomialSelfMap_subset_markedPoints k g hd hcrit)

end Belyi.P1
