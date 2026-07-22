/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.PolynomialBranchMarked
import Belyi.Polynomial.CritVal

/-!
# B4c (marked branch locus): the rational-polynomial transport

Third glue piece of the forward direction (taxis issue #186, parent #51).  The marked branch-locus
bound itself — `Branch (polynomialSelfMap g) ⊆ markedPoints` when the critical values of `g : k[X]`
lie in `{0, 1}` — is `Belyi.P1.branch_polynomialSelfMap_subset_markedPoints`
(`Belyi/P1/PolynomialBranchMarked.lean`, issue #190), built on the value → marked-point dictionary
of `Belyi/P1/AffineMarkedPoint.lean` (issue #189).  This file adds the one remaining piece the
forward assembly (issue #188) needs on top of it: the transport of that bound across the
coefficient map `algebraMap ℚ k`.

## Main result

* `Belyi.branch_map_polynomialSelfMap_subset_markedPoints`: the marked branch-locus bound phrased
  for the base change `g.map (algebraMap ℚ k)` of a rational polynomial `g : ℚ[X]` whose
  `Belyi.critVal` lies in `{0, 1}` — the exact output shape of the combined reduction (issue #185)
  that the B8 assembly (issue #188) consumes.
-/

universe u

namespace Belyi

open Polynomial AlgebraicGeometry

noncomputable local instance instLOFP_polynomialSelfMap_map {k : Type u} [Field k] (g : k[X])
    (hd : 0 < g.natDegree) : LocallyOfFinitePresentation (P1.polynomialSelfMap k g hd) :=
  P1.locallyOfFinitePresentation_polynomialSelfMap k g hd

/-- **B4c (marked branch locus, rational form).** The combined reduction (issue #185) produces a
non-constant `g : ℚ[X]` whose critical values in `k` lie in `{0, 1}` (`Belyi.critVal k g ⊆ {0, 1}`).
Transporting `g` to `k[X]` via `algebraMap ℚ k`, the polynomial self-map of its base change has
branch locus inside `markedPoints k`.  The forward-direction assembly (issue #188) consumes exactly
this shape.  The transport uses `aeval_map_algebraMap`/`derivative_map` (values and derivative are
unchanged) and `aeval_mem_critVal` (the hypothesis is precisely the `critVal` condition), reducing
to `Belyi.P1.branch_polynomialSelfMap_subset_markedPoints`. -/
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
