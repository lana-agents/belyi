/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1
import Belyi.Definable
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.Algebra.MvPolynomial.Division

/-!
# The projective line and change of base ring

First steps towards the canonical identification `ℙ¹_{k₀} ×_{k₀} K ≅ ℙ¹_K` required by
the pair version of B3 (taxis issue #48): this file constructs the comparison morphism

`Belyi.P1.mapOfAlgebra : P1 K ⟶ P1 k₀`

induced by the coefficient map `k₀[X₀,X₁] → K[X₀,X₁]` (a graded ring homomorphism),
shows that it commutes with the structure morphisms, and packages it as the canonical
morphism into the base change

`Belyi.P1.toPullback : P1 K ⟶ pullback (P1 k₀ ↘ Spec k₀) (specAlgebraMap k₀ K)`.

That `toPullback` is an isomorphism is the remaining content of the identification; it
is a chart-by-chart computation (`Away 𝒜 (X i) ⊗_{k₀} K ≅ Away ℬ (X i)`) and is left to
follow-up work.

## Main definitions

* `Belyi.P1.gradedMapOfAlgebra`: the coefficient map as a graded ring homomorphism.
* `Belyi.P1.mapOfAlgebra`: the induced morphism `P1 K ⟶ P1 k₀`.
* `Belyi.P1.toPullback`: the comparison morphism into the base change of `P1 k₀`.

## Main results

* `AlgebraicGeometry.Proj.map_comp_toSpecZero`: functoriality of `Proj` commutes with the
  structure morphisms `toSpecZero`, the induced map on the base being the degree-zero
  component `f.gradedZeroRingHom` of the graded ring homomorphism. Stated in the mathlib
  `AlgebraicGeometry` namespace as a PR candidate.
* `Belyi.P1.mapOfAlgebra_comp_structMap`: the resulting commuting square for `ℙ¹`, which
  makes `toPullback` unconditional (the hypothesis previously carried by `toPullback` is
  now discharged).
-/

universe u

namespace AlgebraicGeometry.Proj

open CategoryTheory HomogeneousLocalization HomogeneousIdeal ProjectiveSpectrum

section Naturality

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Naturality of `fromZeroRingHom` under `Away.map`: forming the degree-zero fraction
`a ↦ a/1` commutes with a graded ring homomorphism `f`, its degree-zero component acting
on the numerator. -/
lemma _root_.HomogeneousLocalization.Away.map_fromZeroRingHom
    (f : 𝒜 →+*ᵍ ℬ) (s : A) (a : 𝒜 0) :
    HomogeneousLocalization.Away.map f s (fromZeroRingHom 𝒜 (.powers s) a) =
      fromZeroRingHom ℬ (.powers (f s)) (f.gradedZeroRingHom a) := by
  apply HomogeneousLocalization.val_injective
  have e : fromZeroRingHom 𝒜 (Submonoid.powers s) a =
      HomogeneousLocalization.mk ⟨0, a, 1, by simp⟩ := rfl
  have e2 : fromZeroRingHom ℬ (Submonoid.powers (f s)) (f.gradedZeroRingHom a) =
      HomogeneousLocalization.mk ⟨0, f.gradedZeroRingHom a, 1, by simp⟩ := rfl
  rw [e, e2, HomogeneousLocalization.Away.map, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
  simp only [GradedRingHom.gradedZeroRingHom_apply_coe]
  congr 1
  exact Subtype.ext (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- **Functoriality of `Proj` commutes with the structure morphism.** For a graded ring
homomorphism `f : 𝒜 →+*ᵍ ℬ` with `ℬ₊ ≤ 𝒜₊.map f`, the square
```
Proj ℬ  --- map f hf --->  Proj 𝒜
  |                          |
toSpecZero ℬ           toSpecZero 𝒜
  v                          v
Spec (ℬ 0) - Spec f₀ -> Spec (𝒜 0)
```
commutes, where `f₀ = f.gradedZeroRingHom` is the degree-zero component of `f`. -/
theorem map_comp_toSpecZero (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) :
    map f hf ≫ toSpecZero 𝒜 =
      toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  refine (mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_f, mapAffineOpenCover_f]
  rw [awayι_comp_map_assoc f hf s.1.2 (s.2 : A) s.2.2,
    awayι_toSpecZero 𝒜 (s.2 : A) s.2.2 s.1.2,
    awayι_toSpecZero_assoc ℬ (f s.2) (f.2 s.2.2) s.1.2,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext (HomogeneousLocalization.Away.map_fromZeroRingHom f (s.2 : A))

end Naturality

end AlgebraicGeometry.Proj

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory Limits MvPolynomial ProjectiveSpectrum

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k₀ K : Type u) [CommRing k₀] [CommRing K] [Algebra k₀ K]

/-- The coefficient map `k₀[X₀,X₁] → K[X₀,X₁]` as a graded ring homomorphism for the
standard gradings. -/
noncomputable def gradedMapOfAlgebra : P1Grading k₀ →+*ᵍ P1Grading K where
  __ := MvPolynomial.map (algebraMap k₀ K)
  map_mem hx := (mem_homogeneousSubmodule _ _).mpr
    (((mem_homogeneousSubmodule _ _).mp hx).map _)

@[simp]
lemma gradedMapOfAlgebra_apply (p : MvPolynomial (Fin 2) k₀) :
    gradedMapOfAlgebra k₀ K p = MvPolynomial.map (algebraMap k₀ K) p := rfl

/-- The irrelevant ideal of `K[X₀,X₁]` is generated by the images of the coordinates,
hence contained in the ideal generated by the image of the irrelevant ideal of
`k₀[X₀,X₁]`. This is the hypothesis needed to apply `Proj.map`. -/
lemma irrelevant_le_map_gradedMapOfAlgebra :
    HomogeneousIdeal.irrelevant (P1Grading K) ≤
      HomogeneousIdeal.map (gradedMapOfAlgebra k₀ K)
        (HomogeneousIdeal.irrelevant (P1Grading k₀)) := by
  classical
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi p hp
  -- `p` is homogeneous of positive degree `i`, so every monomial of `p` uses some variable
  have hph : p.IsHomogeneous i := (mem_homogeneousSubmodule _ _).mp hp
  change p ∈ (HomogeneousIdeal.map (gradedMapOfAlgebra k₀ K)
    (HomogeneousIdeal.irrelevant (P1Grading k₀))).toIdeal
  rw [p.as_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact absurd (hph (mem_support_iff.mp hd)) (by simpa using hi.ne)
  obtain ⟨j, hj⟩ : ∃ j, d j ≠ 0 := by
    by_contra h
    exact hd0 (by ext j; simpa using not_not.mp (not_exists.mp h j))
  -- the coordinate `X j` lies in the image ideal, and divides the monomial
  have hXj : (X j : MvPolynomial (Fin 2) k₀) ∈
      HomogeneousIdeal.irrelevant (P1Grading k₀) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
      ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k₀ j))
  have hmemX : (X j : MvPolynomial (Fin 2) K) ∈
      (HomogeneousIdeal.map (gradedMapOfAlgebra k₀ K)
        (HomogeneousIdeal.irrelevant (P1Grading k₀))).toIdeal := by
    have h := Ideal.mem_map_of_mem (f := gradedMapOfAlgebra k₀ K)
      (show X j ∈ (HomogeneousIdeal.irrelevant (P1Grading k₀)).toIdeal from hXj)
    rwa [gradedMapOfAlgebra_apply, MvPolynomial.map_X] at h
  have hdvd : (X j : MvPolynomial (Fin 2) K) ∣ monomial d (coeff d p) := by
    rw [X, MvPolynomial.monomial_dvd_monomial]
    exact ⟨Or.inr (by simpa [Finsupp.single_le_iff] using Nat.one_le_iff_ne_zero.mpr hj),
      one_dvd _⟩
  exact Ideal.mem_of_dvd _ hdvd hmemX

/-- The morphism `ℙ¹_K ⟶ ℙ¹_{k₀}` induced by the base ring extension. -/
noncomputable def mapOfAlgebra : P1 K ⟶ P1 k₀ :=
  Proj.map (gradedMapOfAlgebra k₀ K) (irrelevant_le_map_gradedMapOfAlgebra k₀ K)

/-- The degree-zero component of the coefficient map, precomposed with the constants of
`k₀`, is the constants of `K` precomposed with `k₀ ⊆ K`: both send `c` to the constant
polynomial `C (algebraMap k₀ K c)`. This is the ring-level identity underlying the
commuting square. -/
lemma gradedZeroRingHom_gradedMapOfAlgebra_comp :
    (gradedMapOfAlgebra k₀ K).gradedZeroRingHom.comp
        (algebraMap k₀ (P1Grading k₀ 0)) =
      (algebraMap K (P1Grading K 0)).comp (algebraMap k₀ K) := by
  refine RingHom.ext fun c => Subtype.ext ?_
  simp only [RingHom.comp_apply, GradedRingHom.gradedZeroRingHom_apply_coe,
    gradedMapOfAlgebra_apply]
  rw [SetLike.GradeZero.coe_algebraMap (P1Grading k₀), MvPolynomial.algebraMap_eq,
    MvPolynomial.map_C, SetLike.GradeZero.coe_algebraMap (P1Grading K),
    MvPolynomial.algebraMap_eq]

/-- **The commuting square for the projective line** (taxis issue #82). The base-change
comparison `mapOfAlgebra` commutes with the structure morphisms, so `ℙ¹_K` maps
canonically into the base change of `ℙ¹_{k₀}`. -/
theorem mapOfAlgebra_comp_structMap :
    mapOfAlgebra k₀ K ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)) =
      (P1 K ↘ Spec (CommRingCat.of K)) ≫ specAlgebraMap k₀ K := by
  change Proj.map (gradedMapOfAlgebra k₀ K) (irrelevant_le_map_gradedMapOfAlgebra k₀ K) ≫
      (Proj.toSpecZero (P1Grading k₀) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k₀ (P1Grading k₀ 0)))) =
    (Proj.toSpecZero (P1Grading K) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (P1Grading K 0)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k₀ K))
  rw [← Category.assoc, AlgebraicGeometry.Proj.map_comp_toSpecZero, Category.assoc,
    Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, gradedZeroRingHom_gradedMapOfAlgebra_comp]

/-- The comparison morphism from `ℙ¹_K` to the base change of `ℙ¹_{k₀}` along
`Spec K ⟶ Spec k₀`. Showing that this is an isomorphism is the remaining content of the
canonical identification `ℙ¹_{k₀} ×_{k₀} K ≅ ℙ¹_K` (taxis issue #48). -/
noncomputable def toPullback :
    P1 K ⟶ pullback (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K) :=
  pullback.lift (mapOfAlgebra k₀ K) (P1 K ↘ Spec (CommRingCat.of K))
    (mapOfAlgebra_comp_structMap k₀ K)

@[reassoc (attr := simp)]
lemma toPullback_snd :
    toPullback k₀ K ≫ pullback.snd _ _ = (P1 K ↘ Spec (CommRingCat.of K)) :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma toPullback_fst :
    toPullback k₀ K ≫ pullback.fst _ _ = mapOfAlgebra k₀ K :=
  pullback.lift_fst _ _ _

end Belyi.P1
