/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.AffineChart
import Belyi.P1.BaseChange

/-!
# Base change of the valued points of the projective line

The base-change morphism `Belyi.P1.mapOfAlgebra k₀ K : P1 K ⟶ P1 k₀` (from
`Belyi/P1/BaseChange.lean`) is natural for the `R`-valued points
`Belyi.P1.point k t : Spec R ⟶ P1 k` of the affine chart `D₊(X₁)` (from
`Belyi/P1/AffineChart.lean`): for a `K`-algebra `R` (hence a `k₀`-algebra by restriction)
and `t : R`, the `K`-valued point with affine coordinate `t` maps under `mapOfAlgebra` to
the `k₀`-valued point with the same affine coordinate `t`. This is the naturality fact for
valued points consumed by the pair version of B3 (#48).

## Main results

* `Belyi.P1.point_comp_mapOfAlgebra`:
  `point K t ≫ mapOfAlgebra k₀ K = point k₀ t`.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [CommRing k] {R : Type u} [CommRing R] [Algebra k R]

/-- The chart-ring evaluation `awayEval k t` on a homogeneous fraction `a / (X₁)^n`
returns `aeval ![t, 1] a`: the denominator `X₁` evaluates to `1`, so it drops out. -/
lemma awayEval_mk (t : R) (n : ℕ) (a : MvPolynomial (Fin 2) k)
    (ha : a ∈ P1Grading k (n • 1)) :
    awayEval k t (Away.mk (P1Grading k) (X_mem_P1Grading k 1) n a ha) = aeval ![t, 1] a := by
  simp only [awayEval, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.awayLift_mk (v := 1) (hv := by simp)]
  simp

/-- Transporting `Proj.awayι` along an equality of homogeneous elements: the chart
inclusion at `a` factors through the chart inclusion at an equal element `b` via the
`eqToHom` induced by `a = b`. -/
lemma awayι_eqToHom_transport {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] {i : ℕ} (hi : 0 < i) {a b : A}
    (hab : a = b) (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 i) :
    AlgebraicGeometry.Proj.awayι 𝒜 a ha hi =
      eqToHom (by rw [hab]) ≫ AlgebraicGeometry.Proj.awayι 𝒜 b hb hi := by
  subst hab
  simp

/-- The `eqToHom` cast induced by an equality `a = b` of denominators acts on a homogeneous
fraction `x / a ^ n` by simply reindexing it as `x / b ^ n`. -/
lemma Away_mk_eqToHom {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ} {a b : A} (hab : a = b) (hf : a ∈ 𝒜 d)
    (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d)) :
    (eqToHom (congrArg (fun s => CommRingCat.of (HomogeneousLocalization.Away 𝒜 s)) hab)).hom
        (HomogeneousLocalization.Away.mk 𝒜 hf n x hx) =
      HomogeneousLocalization.Away.mk 𝒜 (hab ▸ hf) n x hx := by
  subst hab
  simp

section BaseChange

variable (k₀ K : Type u) [CommRing k₀] [CommRing K] [Algebra k₀ K]
variable {R : Type u} [CommRing R] [Algebra k₀ R] [Algebra K R] [IsScalarTower k₀ K R]

open ProjectiveSpectrum

set_option backward.isDefEq.respectTransparency false in
/-- The base-change morphism `mapOfAlgebra` sends the `K`-valued point of affine coordinate
`t` to the `k₀`-valued point of the same affine coordinate `t`. -/
lemma point_comp_mapOfAlgebra (t : R) :
    point K t ≫ mapOfAlgebra k₀ K = point k₀ t := by
  have hfX : gradedMapOfAlgebra k₀ K (X 1) = (X 1 : MvPolynomial (Fin 2) K) := by
    rw [gradedMapOfAlgebra_apply, map_X]
  have h := AlgebraicGeometry.Proj.awayι_comp_map
    (f := gradedMapOfAlgebra k₀ K) (hf := irrelevant_le_map_gradedMapOfAlgebra k₀ K)
    one_pos (X 1 : MvPolynomial (Fin 2) k₀) (X_mem_P1Grading k₀ 1)
  rw [point, point]
  simp only [mapOfAlgebra, P1]
  rw [awayι_eqToHom_transport one_pos hfX.symm (X_mem_P1Grading K 1)
      ((gradedMapOfAlgebra k₀ K).map_mem (X_mem_P1Grading k₀ 1))]
  simp only [Category.assoc]
  rw [h, ← Spec.map_eqToHom (e := congrArg (fun s =>
      CommRingCat.of (HomogeneousLocalization.Away (P1Grading K) s)) hfX)]
  simp only [← Category.assoc]
  congr 1
  simp only [← Spec.map_comp]
  congr 1
  ext z
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (P1Grading k₀) (X_mem_P1Grading k₀ 1) z
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom]
  rw [HomogeneousLocalization.Away.map_mk, Away_mk_eqToHom hfX, awayEval_mk, awayEval_mk,
    gradedMapOfAlgebra_apply, MvPolynomial.aeval_map_algebraMap]

end BaseChange

end Belyi.P1
