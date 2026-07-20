/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.AffineChart

/-!
# The other affine chart of the projective line and its valued points

Mirror of `Belyi/P1/AffineChart.lean` for the chart `D₊(X₀)` (rather than `D₊(X₁)`).
For a `k`-algebra `R` and an element `s : R`, this file builds the `R`-valued point
`Spec R ⟶ P1 k` with affine coordinate `X₁/X₀ = s`, landing in the chart `D₊(X₀)`.

The evaluation `X₀ ↦ 1, X₁ ↦ s` sends `X₀` to a unit, hence factors through the
localization at `X₀` (`Localization.awayLift`), and restricting along
`val : (k[X₀,X₁]_{X₀})₀ → k[X₀,X₁]_{X₀}` yields a ring map out of the chart ring.

This is used by the construction of the polynomial self-map of `ℙ¹` (taxis issue #106,
statement B4): the chart `D₊(G)` of the source maps into this chart `D₊(X₀)` of the
target.

## Main definitions

* `Belyi.P1.awayEval₀ k s`: the evaluation `(k[X₀,X₁]_{X₀})₀ →+* R` sending `X₁/X₀ ↦ s`.
* `Belyi.P1.point₀ k s : Spec (.of R) ⟶ P1 k`: the `R`-valued point with affine
  coordinate `s` in the chart `D₊(X₀)`.
* `Belyi.P1.point₀_structMap`: `point₀ k s` is a morphism over `Spec k`.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [CommRing k]

variable {R : Type u} [CommRing R] [Algebra k R]

/-- Evaluation of the chart ring of `D₊(X₀) ⊆ ℙ¹` at an element `s` of a `k`-algebra:
the ring map `(k[X₀,X₁]_{X₀})₀ →+* R` sending `X₁/X₀` to `s`. -/
noncomputable def awayEval₀ (s : R) : Away (P1Grading k) (X 0) →+* R :=
  (Localization.awayLift ((aeval ![1, s] : MvPolynomial (Fin 2) k →ₐ[k] R) : _ →+* R)
      (X 0) (by simp)).comp
    (algebraMap (Away (P1Grading k) (X 0)) (Localization.Away (X 0 : MvPolynomial (Fin 2) k)))

lemma awayEval₀_fromZeroRingHom (s : R) (x : P1Grading k 0) :
    awayEval₀ k s (fromZeroRingHom (P1Grading k) _ x) =
      aeval ![1, s] (x : MvPolynomial (Fin 2) k) := by
  have hval : (fromZeroRingHom (P1Grading k)
        (Submonoid.powers (X 0 : MvPolynomial (Fin 2) k)) x).val =
      algebraMap (MvPolynomial (Fin 2) k)
        (Localization.Away (X 0 : MvPolynomial (Fin 2) k)) x := by
    simp only [fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, val_mk]
    exact Localization.mk_one_eq_algebraMap _
  simp [awayEval₀, hval]

/-- The `R`-valued point of the projective line with affine coordinate `s` in the chart
`D₊(X₀)`, i.e. the composition `Spec R ⟶ Spec (k[X₀,X₁]_{X₀})₀ ⟶ P1 k` of the evaluation
at `s` with the affine chart `D₊(X₀)`. -/
noncomputable def point₀ (s : R) : Spec (CommRingCat.of R) ⟶ P1 k :=
  Spec.map (CommRingCat.ofHom (awayEval₀ k s)) ≫
    Proj.awayι (P1Grading k) (X 0) (X_mem_P1Grading k 0) one_pos

/-- The valued points in the chart `D₊(X₀)` are morphisms over `Spec k`. -/
@[reassoc]
lemma point₀_structMap (s : R) :
    point₀ k s ≫ structMap k = Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
  change (Spec.map (CommRingCat.ofHom (awayEval₀ k s)) ≫
      Proj.awayι (P1Grading k) (X 0) (X_mem_P1Grading k 0) one_pos) ≫
      Proj.toSpecZero (P1Grading k) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (P1Grading k 0))) =
    Spec.map (CommRingCat.ofHom (algebraMap k R))
  rw [Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  simp [awayEval₀_fromZeroRingHom, SetLike.GradeZero.coe_algebraMap,
    MvPolynomial.algebraMap_eq]

end Belyi.P1
