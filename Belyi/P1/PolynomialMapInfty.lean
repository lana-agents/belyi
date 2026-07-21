/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.PolynomialFinite
import Belyi.P1.MarkedPointMatching

/-!
# B4c (`∞` is fixed): the polynomial self-map fixes the point at infinity

For a non-constant `g : k[X]` the self-map `Belyi.P1.polynomialSelfMap g : ℙ¹ ⟶ ℙ¹`
(realizing `x ↦ g(x)` on the affine chart `D₊(X₁)`, taxis issue #106) fixes the point at
infinity: `polynomialSelfMap g ∞ = ∞`.  Together with the affine-point images
`[a : 1] ↦ [g(a) : 1]` (`Belyi/P1/PolynomialMapImage.lean`) this completes the point-level
part of statement **B4c** (taxis issue #108), goal 1.

## Strategy

Rather than compute the image of `∞` chart-by-chart, we argue topologically:

* `polynomialSelfMap g` maps the affine chart `D₊(X₁)` into itself
  (`polynomialSelfMap_mem_basicOpen_X1`): the `false`-chart identity
  `awayι X₁ ≫ polynomialSelfMap = point k (g(X₀/X₁))` shows the image of `D₊(X₁)` lands in the
  range of the affine chart `point`, i.e. in `D₊(X₁)`.
* `polynomialSelfMap g` is surjective (finite by B4b + dominant, since it sends the generic
  point to a transcendental point, again the generic point).

So any preimage `z` of `∞` cannot lie in `D₊(X₁)` (else `∞ = polynomialSelfMap g z ∈ D₊(X₁)`),
hence `X₁ ∈ z`, hence `z = ∞` by the `V(X₁) = {∞}` identification
(`Belyi.P1.eq_infty_of_X1_mem`).  Therefore `polynomialSelfMap g ∞ = polynomialSelfMap g z = ∞`.

## Main results

* `Belyi.P1.polynomialSelfMap_infty`: `polynomialSelfMap g ∞ = ∞`.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (g : k[X])

/-- The polynomial self-map maps the affine chart `D₊(X₁)` into itself: if `X₁` avoids the
homogeneous prime of `w` (i.e. `w ∈ D₊(X₁)`), then it avoids the prime of the image too.  This
is because on `D₊(X₁)` the map is `x ↦ g(x)`, whose image factors through the affine chart
`point`, whose range is `D₊(X₁)`.

The statement is phrased in terms of `asHomogeneousIdeal` (uniform on `ProjectiveSpectrum`)
rather than `Proj.basicOpen` membership, so that all `TopologicalSpace.Opens` membership stays
on the `Proj`-typed range of `Proj.awayι`, avoiding the `P1 k = Proj _` transparency wall. -/
lemma polynomialSelfMap_X1_notMem (hd : 0 < g.natDegree)
    {w : Proj (P1Grading k)}
    (hw : (X 1 : MvPolynomial (Fin 2) k) ∉ w.asHomogeneousIdeal) :
    (X 1 : MvPolynomial (Fin 2) k) ∉
      ((polynomialSelfMap k g hd).base w).asHomogeneousIdeal := by
  -- `w ∈ D₊(X₁)`, so `w = awayι X₁ u`
  have hwrange : w ∈ (Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos).opensRange := by
    rw [Proj.opensRange_awayι]; exact hw
  obtain ⟨u, rfl⟩ := hwrange
  have hchart : Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos ≫
      polynomialSelfMap k g hd = point k (Polynomial.aeval (affineCoord k) g) :=
    ι_polynomialSelfMap k g hd false
  -- the image is again in the range of `awayι X₁` (the affine chart `point` factors through it);
  -- built in term mode so elaboration bridges the `P1 k = Proj _` boundary in the composition
  have himg : (polynomialSelfMap k g hd).base
      ((Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos).base u) =
      (Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos).base
        ((Spec.map (CommRingCat.ofHom
          (awayEval k (Polynomial.aeval (affineCoord k) g)))).base u) :=
    ((Scheme.Hom.comp_apply (Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos)
          (polynomialSelfMap k g hd) u).symm.trans
        (congrArg (fun m => m.base u) hchart)).trans
      (Scheme.Hom.comp_apply
        (Spec.map (CommRingCat.ofHom (awayEval k (Polynomial.aeval (affineCoord k) g))))
        (Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos) u)
  rw [himg]
  -- points in the range of `awayι X₁` avoid `X₁`
  have hmem : (Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos).base
      ((Spec.map (CommRingCat.ofHom
        (awayEval k (Polynomial.aeval (affineCoord k) g)))).base u)
      ∈ (Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos).opensRange := ⟨_, rfl⟩
  rw [Proj.opensRange_awayι] at hmem
  exact hmem

/-- **B4c (`∞` is fixed).** The polynomial self-map fixes the point at infinity:
`polynomialSelfMap g ∞ = ∞`. -/
theorem polynomialSelfMap_infty (hd : 0 < g.natDegree) :
    (polynomialSelfMap k g hd).base (infty k) = infty k := by
  haveI := isFinite_polynomialSelfMap k g hd
  -- dominance: the generic point maps to a transcendental point, again the generic point
  haveI hdom : IsDominant (polynomialSelfMap k g hd) := by
    have hgne : g ≠ 0 := by rintro rfl; simp at hd
    have hs : Transcendental k (RatFunc.X : RatFunc k) := by
      rw [← RatFunc.algebraMap_X]
      exact (transcendental_algebraMap_iff (RatFunc.algebraMap_injective k)).2
        (Polynomial.transcendental_X k)
    have hlc : g.leadingCoeff ∈ nonZeroDivisors k :=
      mem_nonZeroDivisors_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hgne)
    have hgs : Transcendental k (Polynomial.aeval (RatFunc.X : RatFunc k) g) :=
      hs.aeval g hd.ne' hlc
    have hgen : _root_.genericPoint (P1 k) =
        point k (RatFunc.X : RatFunc k) (IsLocalRing.closedPoint (RatFunc k)) :=
      (genericPoint_spec (P1 k)).eq (closure_point_eq_univ k hs)
    have himg : (polynomialSelfMap k g hd).base (_root_.genericPoint (P1 k)) =
        point k (Polynomial.aeval (RatFunc.X : RatFunc k) g)
          (IsLocalRing.closedPoint (RatFunc k)) := by
      rw [hgen, ← Scheme.Hom.comp_apply, point_comp_polynomialSelfMap]
    refine ⟨denseRange_iff_closure_range.mpr (Set.eq_univ_of_univ_subset ?_)⟩
    rw [← closure_point_eq_univ k hgs]
    exact closure_mono (Set.singleton_subset_iff.mpr (himg ▸ Set.mem_range_self _))
  -- surjectivity (finite ⇒ universally closed, plus dominant)
  obtain ⟨z, hz⟩ := (polynomialSelfMap k g hd).surjective (infty k)
  -- `X₁` lies in the ideal of `∞`
  have hX1inf : (X 1 : MvPolynomial (Fin 2) k) ∈ (infty k).asHomogeneousIdeal := by
    rw [← HomogeneousIdeal.mem_iff, infty, mkPoint_asIdeal]
    exact Ideal.mem_span_singleton_self _
  -- `z` cannot lie in `D₊(X₁)`, so `X₁ ∈ z`, so `z = ∞`
  have hX1z : (X 1 : MvPolynomial (Fin 2) k) ∈ (z : Proj (P1Grading k)).asHomogeneousIdeal := by
    by_contra hnot
    have hnotmem : (X 1 : MvPolynomial (Fin 2) k) ∉
        ((polynomialSelfMap k g hd).base z).asHomogeneousIdeal :=
      polynomialSelfMap_X1_notMem k g hd hnot
    rw [show (polynomialSelfMap k g hd).base z = infty k from hz] at hnotmem
    exact hnotmem hX1inf
  have hzinf : z = infty k :=
    eq_infty_of_X1_mem (HomogeneousIdeal.mem_iff.mp hX1z)
  calc (polynomialSelfMap k g hd).base (infty k)
      = (polynomialSelfMap k g hd).base z := by rw [hzinf]
    _ = infty k := hz

end Belyi.P1
