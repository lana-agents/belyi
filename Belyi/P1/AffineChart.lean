/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1

/-!
# The affine chart of the projective line and its valued points

This file provides the input to B1 (taxis issue #46) on the `ℙ¹` side: for a `k`-algebra
`R` and an element `t : R`, the `R`-valued point `Spec R ⟶ P1 k` with affine coordinate
`t`, landing in the affine chart `D₊(X₁)`.

The construction avoids the chart isomorphism `(k[X₀,X₁]_{X₁})₀ ≃ k[t]`: the evaluation
`X₀ ↦ t, X₁ ↦ 1` sends `X₁` to a unit, hence factors through the localization at `X₁`
(`Localization.awayLift`), and restricting along
`val : (k[X₀,X₁]_{X₁})₀ → k[X₀,X₁]_{X₁}` yields a ring map out of the chart ring.

## Main definitions

* `Belyi.P1.awayEval k t`: the evaluation `(k[X₀,X₁]_{X₁})₀ →+* R` sending `X₀/X₁ ↦ t`.
* `Belyi.P1.point k t : Spec (.of R) ⟶ P1 k`: the `R`-valued point with affine
  coordinate `t`.
* `Belyi.P1.point_structMap`: `point k t` is a morphism over `Spec k`.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [CommRing k]

lemma X_mem_P1Grading (i : Fin 2) : (X i : MvPolynomial (Fin 2) k) ∈ P1Grading k 1 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i)

variable {R : Type u} [CommRing R] [Algebra k R]

/-- Evaluation of the chart ring of `D₊(X₁) ⊆ ℙ¹` at an element `t` of a `k`-algebra:
the ring map `(k[X₀,X₁]_{X₁})₀ →+* R` sending `X₀/X₁` to `t`. -/
noncomputable def awayEval (t : R) : Away (P1Grading k) (X 1) →+* R :=
  (Localization.awayLift ((aeval ![t, 1] : MvPolynomial (Fin 2) k →ₐ[k] R) : _ →+* R)
      (X 1) (by simp)).comp
    (algebraMap (Away (P1Grading k) (X 1)) (Localization.Away (X 1 : MvPolynomial (Fin 2) k)))

lemma awayEval_fromZeroRingHom (t : R) (x : P1Grading k 0) :
    awayEval k t (fromZeroRingHom (P1Grading k) _ x) =
      aeval ![t, 1] (x : MvPolynomial (Fin 2) k) := by
  have hval : (fromZeroRingHom (P1Grading k)
        (Submonoid.powers (X 1 : MvPolynomial (Fin 2) k)) x).val =
      algebraMap (MvPolynomial (Fin 2) k)
        (Localization.Away (X 1 : MvPolynomial (Fin 2) k)) x := by
    simp only [fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, val_mk]
    exact Localization.mk_one_eq_algebraMap _
  simp [awayEval, hval]

/-- The `R`-valued point of the projective line with affine coordinate `t`, i.e. the
composition `Spec R ⟶ Spec (k[X₀,X₁]_{X₁})₀ ⟶ P1 k` of the evaluation at `t` with the
affine chart `D₊(X₁)`. -/
noncomputable def point (t : R) : Spec (CommRingCat.of R) ⟶ P1 k :=
  Spec.map (CommRingCat.ofHom (awayEval k t)) ≫
    Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos

/-- The valued points of the projective line are morphisms over `Spec k`. -/
@[reassoc]
lemma point_structMap (t : R) :
    point k t ≫ structMap k = Spec.map (CommRingCat.ofHom (algebraMap k R)) := by
  change (Spec.map (CommRingCat.ofHom (awayEval k t)) ≫
      Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos) ≫
      Proj.toSpecZero (P1Grading k) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (P1Grading k 0))) =
    Spec.map (CommRingCat.ofHom (algebraMap k R))
  rw [Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  simp [awayEval_fromZeroRingHom, SetLike.GradeZero.coe_algebraMap,
    MvPolynomial.algebraMap_eq]

end Belyi.P1
