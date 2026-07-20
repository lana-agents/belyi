/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Curve.B1
import Belyi.P1.ChartInjective
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
# B1, surjectivity: the morphism to `ℙ¹` attached to a transcendental function is surjective

The surjectivity half of B1 (taxis issue #46). The finiteness half is
`Belyi.isFinite_homOfFunctionField` (`Belyi/Curve/B1.lean`). Together they give the main
theorem of the issue: for a curve `X/k` and a non-constant `t ∈ K(X)`, the induced
morphism `X ⟶ ℙ¹` is finite **and surjective**.

## Strategy

Surjectivity is automatic from `[IsFinite f] [IsDominant f]`: mathlib gives
`IsFinite → IsIntegralHom → UniversallyClosed` and
`Surjective.of_universallyClosed_of_isDominant` (an instance). So the content is
`IsDominant (homOfFunctionField k X hX t)`, i.e. the image is dense.

* `X` is irreducible, so `closure (range f.base) = closure {f.base (genericPoint X)}`
  and `homOfFunctionField_genericPoint` (`Belyi/Curve/B1.lean`) identifies
  `f.base (genericPoint X)` with `P1.point k t (closedPoint K(X))`.
* So density reduces to `closure {P1.point k t (closedPoint)} = univ`, and by
  `ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure` + `vanishingIdeal_singleton`
  + `zeroLocus_bot`, this is exactly
  `(P1.point k t (closedPoint)).asHomogeneousIdeal = ⊥`.
* The point `P1.point k t (closedPoint)` lies in the chart `D₊(X₁)` and equals
  `Proj.awayι … q` where `q = ker (awayEval k t)` as a prime of the chart ring (see
  `Belyi/P1/Transcendental.lean`, the `himg`/`hyker` computation), and `q = ⊥` because
  `awayEval k t` is injective for transcendental `t` (`Belyi.P1.ker_awayEval`).
  Transporting `q = ⊥` through the chart correspondence
  (`ProjIsoSpecTopComponent.FromSpec.carrier`, `mem_carrier_iff_of_mem`) and using that
  `k[X₀,X₁]` is a domain gives `asHomogeneousIdeal = ⊥`.

## Main results

* `Belyi.P1.asHomogeneousIdeal_point_eq_bot`: for `t` transcendental,
  `(P1.point k t (closedPoint)).asHomogeneousIdeal = ⊥`.
* `Belyi.isDominant_homOfFunctionField`, `Belyi.surjective_homOfFunctionField`.
* `Belyi.isFinite_and_surjective_homOfFunctionField`: B1's main theorem, finite + surjective.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
  ProjIsoSpecTopComponent IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] {K : Type u} [Field K] [Algebra k K]

/-- **The point of `ℙ¹` attached to a transcendental element is the generic point.**
For `t : K` transcendental over `k`, the homogeneous ideal of the point
`P1.point k t (closedPoint K)` is `⊥`.

The point lies in the chart `D₊(X₁)`; it equals `Proj.awayι … q` with
`q = ker (awayEval k t)` (`Belyi/P1/Transcendental.lean`), and `q = ⊥` by
`ker_awayEval` (`Belyi/P1/ChartInjective.lean`). Since `k[X₀,X₁]` is a domain and
`X₁ ≠ 0`, the chart correspondence forces every homogeneous element of the ideal to be
zero.

NOTE (route for the prover): the homogeneous ideal of the point `Proj.awayι … q` is
`ProjIsoSpecTopComponent.FromSpec.carrier.asHomogeneousIdeal f_deg hm q`
(`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean`), whose membership on
homogeneous `a ∈ 𝒜 n` is given by `mem_carrier_iff_of_mem`:
`a ∈ carrier q ↔ mk ⟨m*n, aᵐ, fⁿ⟩ ∈ q.asIdeal`. With `q.asIdeal = ⊥` and `A` a domain,
`mk ⟨m*n, aᵐ, fⁿ⟩ = 0 ↔ aᵐ = 0 ↔ a = 0`. The identification of `(Proj.awayι …).base q`
with `FromSpec.toFun f_deg hm q` may require a helper: `awayι = basicOpenIsoSpec.inv ≫ ι`
and `basicOpenIsoSpec.hom`'s base map agrees with `Proj.toSpec 𝒜 f`
(`toSpec_base_apply_eq`), whose topological inverse is `FromSpec.toFun`. Alternatively use
`mk_mem_toSpec_base_apply` after establishing `(Proj.toSpec 𝒜 f).base ⟨point, _⟩ = q`. -/
theorem asHomogeneousIdeal_point_eq_bot {t : K} (ht : Transcendental k t) :
    (point k t (closedPoint K)).asHomogeneousIdeal = ⊥ := by
  sorry

/-- The point of `ℙ¹` attached to a transcendental element has dense closure: its closure
is all of `ℙ¹`. Reduces to `asHomogeneousIdeal_point_eq_bot` via
`ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure`, `vanishingIdeal_singleton`,
`zeroLocus_bot`. -/
theorem closure_point_eq_univ {t : K} (ht : Transcendental k t) :
    closure ({point k t (closedPoint K)} : Set (P1 k)) = Set.univ := by
  have hpbot : (point k t (closedPoint K) :
      ProjectiveSpectrum (P1Grading k)).asHomogeneousIdeal = ⊥ :=
    asHomogeneousIdeal_point_eq_bot k ht
  have huniv : closure ({(point k t (closedPoint K) : ProjectiveSpectrum (P1Grading k))} :
      Set (ProjectiveSpectrum (P1Grading k))) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    refine (ProjectiveSpectrum.le_iff_mem_closure (P1Grading k)
      (point k t (closedPoint K) : ProjectiveSpectrum (P1Grading k)) y).mp ?_
    have hle : (point k t (closedPoint K) : ProjectiveSpectrum (P1Grading k)).asHomogeneousIdeal ≤
        y.asHomogeneousIdeal := by rw [hpbot]; exact bot_le
    exact hle
  exact huniv

end Belyi.P1

namespace Belyi

open AlgebraicGeometry CategoryTheory Scheme IsLocalRing

variable (k : Type u) [Field k] (X : Scheme.{u}) [IrreducibleSpace X]
  [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
  [IsProper (X ↘ Spec (CommRingCat.of k))]

omit [IsProper (X ↘ Spec (CommRingCat.of k))] in
/-- **B1, dominance**: the morphism `X ⟶ ℙ¹` attached to a transcendental function is
dominant. The generic point of `X` maps to the generic point of `ℙ¹`
(`homOfFunctionField_genericPoint` + `P1.asHomogeneousIdeal_point_eq_bot`), and `X` is
irreducible, so the image is dense.

NOTE (route for the prover): `IsDominant` unfolds to `DenseRange f.base`, i.e.
`closure (range f.base) = univ`. Since `X` is irreducible with generic point
`genericPoint X` (dense), `range f.base ⊆ closure {f.base (genericPoint X)}` and the
latter is dense, so `closure (range f.base) ⊇ closure {f.base (genericPoint X)}` which is
`univ` by `P1.closure_point_eq_univ` (rewriting `f.base (genericPoint X)` via
`homOfFunctionField_genericPoint`). Use `denseRange_iff_closure_range`,
`IrreducibleSpace`/`genericPoint_specializes`/`dense` lemmas. Note the target of
`P1.point k t` uses `R := X.functionField`; match the implicit argument as in
`homOfFunctionField_genericPoint`. -/
theorem isDominant_homOfFunctionField
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x))
    {t : X.functionField} (ht : Transcendental k t) :
    IsDominant (homOfFunctionField k X hX t) := by
  refine ⟨denseRange_iff_closure_range.mpr (Set.eq_univ_of_univ_subset ?_)⟩
  rw [← P1.closure_point_eq_univ k ht, ← homOfFunctionField_genericPoint k X hX t]
  exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self _))

/-- **B1, surjectivity**: the morphism `X ⟶ ℙ¹` attached to a transcendental function is
surjective. Finite ⇒ integral ⇒ universally closed, plus dominant ⇒ surjective
(`Surjective.of_universallyClosed_of_isDominant`). -/
theorem surjective_homOfFunctionField
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x))
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x))
    {t : X.functionField} (ht : Transcendental k t) :
    Function.Surjective (homOfFunctionField k X hX t).base := by
  haveI := isFinite_homOfFunctionField k X hX hdim ht
  haveI := isDominant_homOfFunctionField k X hX ht
  exact (homOfFunctionField k X hX t).surjective

/-- **B1, main theorem** (modulo the stalk hypotheses): for `X` integral and proper over
`k` with valuation-ring local rings of dimension `≤ 1`, and `t ∈ K(X)` transcendental
over `k`, the induced morphism `X ⟶ ℙ¹` is finite and surjective. -/
theorem isFinite_and_surjective_homOfFunctionField
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x))
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x))
    {t : X.functionField} (ht : Transcendental k t) :
    IsFinite (homOfFunctionField k X hX t) ∧
      Function.Surjective (homOfFunctionField k X hX t).base :=
  ⟨isFinite_homOfFunctionField k X hX hdim ht,
    surjective_homOfFunctionField k X hX hdim ht⟩

end Belyi
