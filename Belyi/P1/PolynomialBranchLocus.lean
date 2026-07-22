/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.PolynomialMapBranch
import Belyi.P1.PolynomialMapImage
import Belyi.P1.PolynomialMapInfty
import Belyi.P1.ClosedPoints
import Belyi.BelyiMap

/-!
# B4c (branch locus): the assembled branch-locus inclusion and the B8 corollary

For a non-constant `g : k[X]` over an algebraically closed field `k` of characteristic zero, this
file assembles the **branch-locus inclusion** for the polynomial self-map
`Belyi.P1.polynomialSelfMap g : ℙ¹ ⟶ ℙ¹` (taxis issue #108, goal 2), combining the three merged
inputs:

* the scheme-level per-point étale bridge `Belyi.P1.point_notMem_ram_polynomialSelfMap` — an affine
  point `[a : 1]` with `g'(a) ≠ 0` is not ramified (issue #108, PR #32);
* the closed-point classification `Belyi.P1.exists_eq_point_or_eq_infty_of_ne_genericPoint` — every
  non-generic point of `ℙ¹` is affine `[a : 1]` or `∞` (issue #184);
* the point-image formulas `polynomialSelfMap_point_closedPoint` (`[a:1] ↦ [g(a):1]`) and
  `polynomialSelfMap_infty` (`∞ ↦ ∞`).

The generic point is excluded from the ramification locus by an elementary density argument:
`(polynomialSelfMap g).smoothLocus` is a *nonempty* open subset of the *irreducible* space `ℙ¹`
(nonempty because `[a : 1] ∈ smoothLocus` for any `a` with `g'(a) ≠ 0`, and such `a` exists over an
infinite field once `g' ≠ 0`, which holds in characteristic zero), hence it contains the generic
point.  This avoids the heavier generic-étaleness input (`IsDominant` + perfectness of the function
field) that `Belyi.genericPoint_mem_smoothLocus` would require.

## Main results

* `Belyi.P1.genericPoint_notMem_ram_polynomialSelfMap`: the generic point is unramified.
* `Belyi.P1.branch_polynomialSelfMap_subset` (**B4c goal 2**):
  `Branch (polynomialSelfMap g) ⊆ {[g(a):1] : g'(a) = 0} ∪ {∞}`.
* `Belyi.P1.isBelyiMap_comp_polynomialSelfMap` (**B4c goal 3 / B8 glue**): for a finite
  `f : X ⟶ ℙ¹`, `f ≫ polynomialSelfMap g` is a Belyi map as soon as `g '' Branch f ⊆ {0,1,∞}`
  and `Branch (polynomialSelfMap g) ⊆ {0,1,∞}`.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped Polynomial

variable (k : Type u) [Field k] (g : k[X]) (hd : 0 < g.natDegree)

noncomputable local instance instLOFP_polynomialSelfMap' :
    LocallyOfFinitePresentation (polynomialSelfMap k g hd) :=
  locallyOfFinitePresentation_polynomialSelfMap k g hd

include hd in
/-- There is an affine point `[a : 1]` at which `g` is unramified: over an algebraically closed
(hence infinite) field of characteristic zero, the derivative `g'` is a nonzero polynomial, so it
has a non-root. -/
theorem exists_aeval_derivative_ne_zero [IsAlgClosed k] [CharZero k] :
    ∃ a : k, Polynomial.aeval a (Polynomial.derivative g) ≠ 0 := by
  have hderiv : Polynomial.derivative g ≠ 0 := Polynomial.derivative_ne_zero.mpr hd.ne'
  have hfin : {x : k | (Polynomial.derivative g).IsRoot x}.Finite :=
    Polynomial.finite_setOf_isRoot hderiv
  obtain ⟨a, ha⟩ := (hfin.infinite_compl).nonempty
  refine ⟨a, ?_⟩
  rw [Polynomial.coe_aeval_eq_eval]
  simpa [Set.mem_compl_iff, Set.mem_setOf_eq, Polynomial.IsRoot.def] using ha

/-- The **generic point** of `ℙ¹` is unramified for the polynomial self-map: the smooth locus is a
nonempty open of the irreducible space `ℙ¹`, hence contains the generic point. -/
theorem genericPoint_mem_smoothLocus_polynomialSelfMap [IsAlgClosed k] [CharZero k] :
    _root_.genericPoint (P1 k) ∈ ((polynomialSelfMap k g hd).smoothLocus : Set (P1 k)) := by
  obtain ⟨a, ha⟩ := exists_aeval_derivative_ne_zero k g hd
  have hmem : point k a (IsLocalRing.closedPoint k) ∈
      ((polynomialSelfMap k g hd).smoothLocus : Set (P1 k)) :=
    mem_smoothLocus_polynomialSelfMap k g hd a ha
  have hopen : IsOpen ((polynomialSelfMap k g hd).smoothLocus : Set (P1 k)) :=
    (polynomialSelfMap k g hd).smoothLocus.isOpen
  rw [(genericPoint_spec (P1 k)).mem_open_set_iff hopen]
  exact ⟨_, Set.mem_univ _, hmem⟩

theorem genericPoint_notMem_ram_polynomialSelfMap [IsAlgClosed k] [CharZero k] :
    _root_.genericPoint (P1 k) ∉ Ram (polynomialSelfMap k g hd) := by
  rw [Belyi.mem_ram_iff, not_not, ← Scheme.Hom.mem_smoothLocus]
  exact genericPoint_mem_smoothLocus_polynomialSelfMap k g hd

/-- **B4c (branch-locus inclusion, goal 2).** Over an algebraically closed field of characteristic
zero, every branch point of the polynomial self-map `x ↦ g(x)` is a critical value `[g(a) : 1]` with
`g'(a) = 0`, or the point at infinity. -/
theorem branch_polynomialSelfMap_subset [IsAlgClosed k] [CharZero k] :
    Branch (polynomialSelfMap k g hd) ⊆
      {y : P1 k | ∃ a : k, Polynomial.aeval a (Polynomial.derivative g) = 0 ∧
          y = point k (Polynomial.aeval a g) (IsLocalRing.closedPoint k)} ∪ {infty k} := by
  intro y hy
  rw [Belyi.mem_branch_iff] at hy
  obtain ⟨x, hxram, hxy⟩ := hy
  have hxne : x ≠ _root_.genericPoint (P1 k) := by
    rintro rfl
    exact genericPoint_notMem_ram_polynomialSelfMap k g hd hxram
  rcases exists_eq_point_or_eq_infty_of_ne_genericPoint k x hxne with ⟨a, hxa⟩ | hxinf
  · -- affine point: `x ∈ Ram` forces `g'(a) = 0`, and `x ↦ [g(a):1]`.
    refine Or.inl ?_
    have hcrit : Polynomial.aeval a (Polynomial.derivative g) = 0 := by
      by_contra hne
      exact point_notMem_ram_polynomialSelfMap k g hd a hne (hxa ▸ hxram)
    refine ⟨a, hcrit, ?_⟩
    rw [← hxy, hxa]
    exact polynomialSelfMap_point_closedPoint k g hd a
  · -- point at infinity: `∞ ↦ ∞`.
    refine Or.inr ?_
    rw [Set.mem_singleton_iff, ← hxy, hxinf]
    exact polynomialSelfMap_infty k g hd

/-- **B4c (the B8 corollary, goal 3).** For a finite morphism `f : X ⟶ ℙ¹` whose branch points are
carried into the marked set by `g` (`g '' Branch f ⊆ {0,1,∞}`), and a polynomial self-map whose own
branch locus lands in the marked set (`Branch (polynomialSelfMap g) ⊆ {0,1,∞}`), the composite
`f ≫ polynomialSelfMap g` is a Belyi map.  This is the glue the forward direction (B8, taxis #51)
consumes, specialising the already-proved `Belyi.IsBelyiMap.comp` to `g = polynomialSelfMap g`. -/
theorem isBelyiMap_comp_polynomialSelfMap {X : Scheme.{u}} (f : X ⟶ P1 k)
    [IsFinite f] [LocallyOfFinitePresentation f]
    (hbf : (polynomialSelfMap k g hd) '' Branch f ⊆ Belyi.markedPoints k)
    (hbg : Branch (polynomialSelfMap k g hd) ⊆ Belyi.markedPoints k) :
    Belyi.IsBelyiMap k (f ≫ polynomialSelfMap k g hd) := by
  haveI : IsFinite (polynomialSelfMap k g hd) := isFinite_polynomialSelfMap k g hd
  exact Belyi.IsBelyiMap.comp (polynomialSelfMap k g hd) hbf hbg

end Belyi.P1
