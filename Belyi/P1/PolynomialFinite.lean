/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.PolynomialMap
import Belyi.P1.Curve
import Belyi.Curve.B1Surjective
import Belyi.Dimension
import Belyi.Curve.ToP1
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# B4b: the polynomial self-map of `ℙ¹` is finite

For a non-constant polynomial `g : k[X]` over a field `k`, the self-map
`Belyi.P1.polynomialSelfMap g : ℙ¹ ⟶ ℙ¹` constructed in `Belyi/P1/PolynomialMap.lean`
(realizing `[x₀ : x₁] ↦ [g.homogenize d : X₁ᵈ]`, i.e. `x ↦ g(x)` on the affine chart) is
**finite**.

The proof mirrors `Belyi.isFinite_homOfFunctionField` (`Belyi/Curve/B1.lean`), via
Zariski's main theorem `IsFinite.of_isProper_of_locallyQuasiFinite`:

* **Proper.** `polynomialSelfMap g` is a morphism over `Spec k`
  (`polynomialSelfMap_structMap`), so `Belyi.isProper_of_isOver` applies: the source
  `ℙ¹` is proper over `k` and the target `ℙ¹` is separated over `k`.
* **Locally quasi-finite.** All fibers are finite. `ℙ¹` is integral with one-dimensional
  stalks (`Belyi/P1/Curve.lean`), so `Belyi.finite_preimage_singleton_of_isClosedMap`
  reduces finite fibers of the (closed, by properness) map to the *non-constancy* input:
  the generic point is not sent to a closed point.
* **Non-constancy (the crux).** The generic point of `ℙ¹` is the point attached to a
  transcendental element (`Belyi.P1.closure_point_eq_univ`). Precomposing
  `polynomialSelfMap g` with the valued point `point k s` (`s = X ∈ k(X)` transcendental)
  gives `point k (g(s))` (`point_comp_polynomialSelfMap`), and `g(s)` is again
  transcendental (`Transcendental.aeval`, using `g` non-constant), so its point is not
  closed (`Belyi.P1.not_isClosed_singleton_point_of_transcendental`).

## Main results

* `Belyi.P1.point_comp_polynomialSelfMap`: `point k s ≫ polynomialSelfMap g = point k (g(s))`.
* `Belyi.P1.isFinite_polynomialSelfMap`: `IsFinite (polynomialSelfMap g)`.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open scoped nonZeroDivisors

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (g : Polynomial k)

/-- Precomposing the polynomial self-map with the `K`-valued point of `ℙ¹` at `s`
reindexes the coordinate by `g`: `point k s ≫ polynomialSelfMap g = point k (g(s))`.
This is the naturality behind the identification of the generic-point image. -/
lemma point_comp_polynomialSelfMap (hd : 0 < g.natDegree) {K : Type u} [Field K] [Algebra k K]
    (s : K) :
    point k s ≫ polynomialSelfMap k g hd = point k (Polynomial.aeval s g) := by
  have hchart :
      Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos ≫ polynomialSelfMap k g hd =
        point k (Polynomial.aeval (affineCoord k) g) :=
    ι_polynomialSelfMap k g hd false
  have key : Spec.map (CommRingCat.ofHom (awayEval k s)) ≫
      (Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos ≫ polynomialSelfMap k g hd) =
        point k (Polynomial.aeval s g) := by
    rw [hchart, SpecMap_comp_point (awayEval k s) (fun c => (awayEvalₐ k s).commutes c)]
    congr 1
    change awayEvalₐ k s (Polynomial.aeval (affineCoord k) g) = Polynomial.aeval s g
    rw [← Polynomial.aeval_algHom_apply,
      show awayEvalₐ k s (affineCoord k) = s from awayEval_affineCoord k s]
  rw [← key, ← Category.assoc]
  rfl

/-- **B4b: the polynomial self-map of `ℙ¹` is finite.** For a non-constant `g : k[X]`, the
self-map `[x₀ : x₁] ↦ [g.homogenize d : X₁ᵈ]` of `ℙ¹` is a finite morphism. -/
theorem isFinite_polynomialSelfMap (hd : 0 < g.natDegree) :
    IsFinite (polynomialSelfMap k g hd) := by
  -- the map is over `Spec k`, hence proper (source proper, target separated over `k`)
  haveI hover : (polynomialSelfMap k g hd).IsOver (Spec (CommRingCat.of k)) :=
    ⟨by rw [structMap_eq]; exact polynomialSelfMap_structMap k g hd⟩
  haveI hproper : IsProper (polynomialSelfMap k g hd) :=
    isProper_of_isOver (S := Spec (CommRingCat.of k)) _
  haveI hnoeth : IsNoetherian (P1 k) := isNoetherian_of_over (P1 k) (Spec (CommRingCat.of k))
  -- a transcendental element in a field over `k`, and its image under `g`
  have hgne : g ≠ 0 := by rintro rfl; simp at hd
  have hs : Transcendental k (RatFunc.X : RatFunc k) := by
    rw [← RatFunc.algebraMap_X]
    exact (transcendental_algebraMap_iff (RatFunc.algebraMap_injective k)).2
      (Polynomial.transcendental_X k)
  have hlc : g.leadingCoeff ∈ nonZeroDivisors k :=
    mem_nonZeroDivisors_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hgne)
  have hgs : Transcendental k (Polynomial.aeval (RatFunc.X : RatFunc k) g) :=
    hs.aeval g hd.ne' hlc
  -- the generic point is the point attached to a transcendental element
  have hgen : _root_.genericPoint (P1 k) =
      point k (RatFunc.X : RatFunc k) (IsLocalRing.closedPoint (RatFunc k)) :=
    (genericPoint_spec (P1 k)).eq (closure_point_eq_univ k hs)
  -- the image of the generic point is not closed
  have hnc : ¬ IsClosed ({polynomialSelfMap k g hd (_root_.genericPoint (P1 k))} : Set (P1 k)) := by
    have himg : polynomialSelfMap k g hd (_root_.genericPoint (P1 k)) =
        point k (Polynomial.aeval (RatFunc.X : RatFunc k) g)
          (IsLocalRing.closedPoint (RatFunc k)) := by
      rw [hgen, ← Scheme.Hom.comp_apply, point_comp_polynomialSelfMap]
    rw [himg]
    exact not_isClosed_singleton_point_of_transcendental k hgs
  -- finite fibers ⇒ locally quasi-finite; with properness ⇒ finite (Zariski's main theorem)
  have hfib : ∀ y, ((polynomialSelfMap k g hd).base ⁻¹' {y}).Finite := fun y =>
    finite_preimage_singleton_of_isClosedMap _ (krullDimLE_one_stalk_P1 k)
      (polynomialSelfMap k g hd).isClosedMap hnc y
  haveI : LocallyQuasiFinite (polynomialSelfMap k g hd) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ hfib
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end Belyi.P1
