/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Over
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The projective line

This file constructs the model of `ℙ¹` used throughout the Belyi project (taxis issue
#46): `Belyi.P1 k := Proj k[X₀, X₁]`, the `Proj` of the polynomial ring in two
variables with its standard grading (`MvPolynomial.homogeneousSubmodule (Fin 2) k`).

## Main definitions

* `Belyi.P1 k`: the projective line over a commutative ring `k`.
* `Belyi.P1.structMap k : P1 k ⟶ Spec (.of k)`: the structure morphism, obtained from
  `Proj.toSpecZero` and the identification `k ≅ 𝒜 0` of the base ring with the
  degree-zero part of the grading (`Belyi.P1.gradeZeroEquiv`).
* The `(P1 k).Over (Spec (.of k))` instance, and properness and separatedness of the
  structure morphism.

The points ↔ `k ∪ {∞}` dictionary over the two standard affine charts is follow-up
work on the same issue.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [CommRing k]

/-- The standard grading on `k[X₀, X₁]`, by total degree. -/
noncomputable abbrev P1Grading : ℕ → Submodule k (MvPolynomial (Fin 2) k) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) k

/-- The projective line over `k`, as the `Proj` of `k[X₀, X₁]` with its standard
grading. -/
noncomputable def P1 : Scheme.{u} :=
  Proj (P1Grading k)

namespace P1

/-- The degree-zero part of the standard grading on `k[X₀, X₁]` is a copy of `k`
(the constants). -/
noncomputable def gradeZeroEquiv : k ≃+* P1Grading k 0 := by
  refine RingEquiv.ofBijective (algebraMap k (P1Grading k 0)) ⟨fun a b hab => ?_, fun p => ?_⟩
  · have h1 : (algebraMap k (MvPolynomial (Fin 2) k)) a =
        (algebraMap k (MvPolynomial (Fin 2) k)) b := by
      rw [← SetLike.GradeZero.coe_algebraMap (P1Grading k),
        ← SetLike.GradeZero.coe_algebraMap (P1Grading k), hab]
    exact C_injective (Fin 2) k (by simpa [MvPolynomial.algebraMap_eq] using h1)
  · have hp : (p : MvPolynomial (Fin 2) k) ∈ (1 : Submodule k (MvPolynomial (Fin 2) k)) := by
      rw [← homogeneousSubmodule_zero (σ := Fin 2) (R := k)]
      exact p.2
    obtain ⟨c, hc⟩ := Submodule.mem_one.mp hp
    exact ⟨c, Subtype.ext (by rw [SetLike.GradeZero.coe_algebraMap (P1Grading k)]; exact hc)⟩

/-- The structure morphism of the projective line. -/
noncomputable def structMap : P1 k ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (P1Grading k) ≫ Spec.map (CommRingCat.ofHom (algebraMap k (P1Grading k 0)))

noncomputable instance : (P1 k).Over (Spec (CommRingCat.of k)) :=
  ⟨structMap k⟩

lemma structMap_eq : (P1 k ↘ Spec (CommRingCat.of k)) = structMap k := rfl

instance : IsIso (CommRingCat.ofHom (algebraMap k (P1Grading k 0))) := by
  have h : CommRingCat.ofHom (algebraMap k (P1Grading k 0)) =
      (gradeZeroEquiv k).toCommRingCatIso.hom := rfl
  rw [h]
  infer_instance

/-- `k[X₀, X₁]` is of finite type over the degree-zero part of its grading. -/
instance : Algebra.FiniteType (P1Grading k 0) (MvPolynomial (Fin 2) k) := by
  have h : IsScalarTower k (P1Grading k 0) (MvPolynomial (Fin 2) k) :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := P1Grading k 0)
      (A := MvPolynomial (Fin 2) k)
      (fun c => (SetLike.GradeZero.coe_algebraMap (P1Grading k) c).symm)
  exact Algebra.FiniteType.of_restrictScalars_finiteType k (P1Grading k 0)
    (MvPolynomial (Fin 2) k)

instance : IsProper (structMap k) := by
  have h2 : IsProper (Spec.map (CommRingCat.ofHom (algebraMap k (P1Grading k 0)))) :=
    MorphismProperty.of_isIso @IsProper _
  change IsProper (Proj.toSpecZero (P1Grading k) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (P1Grading k 0))))
  infer_instance

instance : IsProper (P1 k ↘ Spec (CommRingCat.of k)) := by
  have h2 : IsProper (Spec.map (CommRingCat.ofHom (algebraMap k (P1Grading k 0)))) :=
    MorphismProperty.of_isIso @IsProper _
  change IsProper (Proj.toSpecZero (P1Grading k) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (P1Grading k 0))))
  infer_instance

instance : IsSeparated (P1 k ↘ Spec (CommRingCat.of k)) :=
  inferInstance

end P1

end Belyi
