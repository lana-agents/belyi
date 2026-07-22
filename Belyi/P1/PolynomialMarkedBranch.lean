/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.PolynomialBranchMarked
import Belyi.Polynomial.CritVal

/-!
# B4c (marked branch locus, rational form)

Second glue piece of the forward direction (taxis issue #186, parent #51): the rational-polynomial
form of the branch-locus / marked-point bridge.

The `k[X]`-form of the statement — for `g : k[X]` all of whose critical values lie in `{0, 1}`,
`Branch (polynomialSelfMap g) ⊆ markedPoints k` — is the merged
`Belyi.P1.branch_polynomialSelfMap_subset_markedPoints`
(`Belyi/P1/PolynomialBranchMarked.lean`, taxis #190), which itself rests on the value → marked-point
dictionary `Belyi.P1.point_base_eq_zero` / `point_base_eq_one` (`Belyi/P1/AffineMarkedPoint.lean`,
taxis #189).

This file adds the remaining rational-transport corollary: the combined reduction (issue #185)
produces a non-constant `g : ℚ[X]` whose critical values in `k` lie in `{0, 1}`
(`Belyi.critVal k g ⊆ {0, 1}`), whereas `polynomialSelfMap` needs a polynomial over `k = ℚ̄`.  We
transport the critical-value hypothesis from `ℚ[X]` to `g.map (algebraMap ℚ k) : k[X]` and conclude
the marked-branch containment in exactly the shape the B8 assembly (issue #188) consumes.

## Main result

* `Belyi.branch_map_polynomialSelfMap_subset_markedPoints`: for `g : ℚ[X]` with `g.natDegree ≠ 0`
  and `Belyi.critVal k g ⊆ {0, 1}`, the polynomial self-map of `g.map (algebraMap ℚ k)` has branch
  locus contained in `Belyi.markedPoints k`.
-/

universe u

namespace Belyi

open Polynomial

noncomputable local instance instLOFP_polynomialSelfMap_map {k : Type u} [Field k] (g : k[X])
    (hd : 0 < g.natDegree) : AlgebraicGeometry.LocallyOfFinitePresentation
      (P1.polynomialSelfMap k g hd) :=
  P1.locallyOfFinitePresentation_polynomialSelfMap k g hd

/-- **B4c (marked branch locus, rational form).** The combined reduction (issue #185) produces a
non-constant `g : ℚ[X]` whose critical values in `k` lie in `{0, 1}` (`Belyi.critVal k g ⊆ {0, 1}`).
Transporting `g` to `k[X]` via `algebraMap ℚ k`, the polynomial self-map of its base change has
branch locus inside `markedPoints k`.  The forward-direction assembly (issue #188) consumes exactly
this shape.  The transport uses `aeval_map_algebraMap` / `derivative_map` (values and derivative are
unchanged) and `aeval_mem_critVal` (the pointwise hypothesis is precisely the `critVal` condition),
feeding the result into the merged `Belyi.P1.branch_polynomialSelfMap_subset_markedPoints`. -/
theorem branch_map_polynomialSelfMap_subset_markedPoints {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] [Algebra ℚ k] {g : ℚ[X]} (hgd : g.natDegree ≠ 0)
    (hcv : ∀ x ∈ Belyi.critVal k g, x = 0 ∨ x = 1)
    (hd : 0 < (g.map (algebraMap ℚ k)).natDegree) :
    Branch (P1.polynomialSelfMap k (g.map (algebraMap ℚ k)) hd) ⊆ Belyi.markedPoints k := by
  apply P1.branch_polynomialSelfMap_subset_markedPoints
  intro a ha
  have hderiv : derivative g ≠ 0 := derivative_ne_zero.mpr hgd
  have hda : aeval a (derivative g) = 0 := by
    rwa [derivative_map, aeval_map_algebraMap k] at ha
  have hval : aeval a (g.map (algebraMap ℚ k)) = aeval a g := aeval_map_algebraMap k a g
  rw [hval]
  exact hcv _ (aeval_mem_critVal hderiv hda)

end Belyi
