/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.P1.BaseChange
import Belyi.P1.Points

/-!
# Base change of the marked points of the projective line

The base-change morphism `Belyi.P1.mapOfAlgebra k₀ K : P1 K ⟶ P1 k₀` (from
`Belyi/P1/BaseChange.lean`) acts on the underlying space by `ProjectiveSpectrum.comap`,
i.e. by contracting homogeneous prime ideals along the coefficient map
`k₀[X₀,X₁] → K[X₀,X₁]`. This file records that it sends each marked point of `ℙ¹_K` to the
corresponding marked point of `ℙ¹_{k₀}` (taxis issue #110, split out of #82). These are the
naturality facts consumed by the pair version of B3 (#48) and by the marked-curve API (#54).

## Main results

* `Belyi.P1.mapOfAlgebra_base_zero`, `Belyi.P1.mapOfAlgebra_base_one`,
  `Belyi.P1.mapOfAlgebra_base_infty`: the base-change morphism sends `0 ↦ 0`, `1 ↦ 1`,
  `∞ ↦ ∞`.

The computations reduce, via `ProjectiveSpectrum.comap`, to contractions of principal
homogeneous ideals `Ideal.comap (MvPolynomial.map (algebraMap k₀ K)) (span {g_K}) =
span {g_{k₀}}` for the linear forms `g = X₀, X₀ - X₁, X₁`. The supporting divisibility
lemmas `MvPolynomial.monomial_one_dvd_iff_forall_coeff`,
`MvPolynomial.monomial_one_dvd_map_iff` and `MvPolynomial.X_dvd_map_iff` are stated in the
`MvPolynomial` namespace as upstream candidates.
-/

universe u

namespace MvPolynomial

variable {σ : Type*} {R S : Type*} [CommRing R] [CommRing S]

/-- `x` is divisible by `monomial s 1` iff every coefficient at a multi-index not `≥ s`
vanishes. -/
lemma monomial_one_dvd_iff_forall_coeff (x : MvPolynomial σ R) (s : σ →₀ ℕ) :
    (monomial s 1) ∣ x ↔ ∀ d, ¬ s ≤ d → coeff d x = 0 := by
  rw [monomial_one_dvd_iff_modMonomial_eq_zero, MvPolynomial.ext_iff]
  simp only [coeff_zero]
  constructor
  · intro h d hd
    rw [← coeff_modMonomial_of_not_le x hd]
    exact h d
  · intro h d
    by_cases hd : s ≤ d
    · exact coeff_modMonomial_of_le x hd
    · rw [coeff_modMonomial_of_not_le x hd]; exact h d hd

/-- Divisibility by a monomial `monomial s 1` is reflected and preserved by an injective
coefficient extension. -/
lemma monomial_one_dvd_map_iff {φ : R →+* S} (hφ : Function.Injective φ)
    (s : σ →₀ ℕ) (p : MvPolynomial σ R) :
    (monomial s 1 : MvPolynomial σ S) ∣ MvPolynomial.map φ p ↔
      (monomial s 1 : MvPolynomial σ R) ∣ p := by
  rw [monomial_one_dvd_iff_forall_coeff, monomial_one_dvd_iff_forall_coeff]
  refine forall_congr' fun d => imp_congr_right fun _ => ?_
  rw [coeff_map, map_eq_zero_iff φ hφ]

/-- Divisibility by `X i` is reflected and preserved by an injective coefficient
extension. -/
lemma X_dvd_map_iff {φ : R →+* S} (hφ : Function.Injective φ) (i : σ)
    (p : MvPolynomial σ R) :
    (X i : MvPolynomial σ S) ∣ MvPolynomial.map φ p ↔ (X i : MvPolynomial σ R) ∣ p := by
  simpa only [X] using monomial_one_dvd_map_iff hφ (Finsupp.single i 1) p

end MvPolynomial

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial ProjectiveSpectrum

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k₀ K : Type u) [Field k₀] [Field K] [Algebra k₀ K]

/-- The shear automorphism `X₀ ↦ X₀ + X₁, X₁ ↦ X₁` of `R[X₀, X₁]`, used to reduce
divisibility by the linear form `X₀ - X₁` to divisibility by `X₀`. -/
noncomputable def shear (R : Type u) [CommRing R] :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval ![X 0 + X 1, X 1]

/-- The inverse shear `X₀ ↦ X₀ - X₁, X₁ ↦ X₁`. -/
noncomputable def shearInv (R : Type u) [CommRing R] :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval ![X 0 - X 1, X 1]

@[simp] lemma shear_X0 (R : Type u) [CommRing R] : shear R (X 0) = X 0 + X 1 := by simp [shear]

@[simp] lemma shear_X1 (R : Type u) [CommRing R] : shear R (X 1) = X 1 := by simp [shear]

lemma shear_X0_sub_X1 (R : Type u) [CommRing R] : shear R (X 0 - X 1) = X 0 := by simp [shear]

lemma shearInv_shear (R : Type u) [CommRing R] (p : MvPolynomial (Fin 2) R) :
    shearInv R (shear R p) = p := by
  have h : (shearInv R).comp (shear R) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [shear, shearInv, sub_add_cancel]
  exact congrArg (fun f => f p) h

/-- The shear commutes with the coefficient extension `k₀[X₀,X₁] → K[X₀,X₁]`. -/
lemma map_shear (p : MvPolynomial (Fin 2) k₀) :
    MvPolynomial.map (algebraMap k₀ K) (shear k₀ p) =
      shear K (MvPolynomial.map (algebraMap k₀ K) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [shear, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      congr 1
      fin_cases i <;> simp

/-- Divisibility by the linear form `X₀ - X₁` is reflected and preserved by the coefficient
extension `k₀[X₀,X₁] → K[X₀,X₁]`. -/
lemma X0_sub_X1_dvd_map_iff (p : MvPolynomial (Fin 2) k₀) :
    (X 0 - X 1 : MvPolynomial (Fin 2) K) ∣ MvPolynomial.map (algebraMap k₀ K) p ↔
      (X 0 - X 1 : MvPolynomial (Fin 2) k₀) ∣ p := by
  constructor
  · intro h
    -- shear turns `X₀ - X₁` into `X₀`, and commutes with the coefficient extension
    have h1 : (X 0 : MvPolynomial (Fin 2) K) ∣
        shear K (MvPolynomial.map (algebraMap k₀ K) p) := by
      rw [← shear_X0_sub_X1 K]; exact map_dvd _ h
    rw [← map_shear, X_dvd_map_iff (algebraMap k₀ K).injective] at h1
    have h2 := map_dvd (shearInv k₀) h1
    rwa [shearInv_shear, show shearInv k₀ (X 0) = X 0 - X 1 by simp [shearInv]] at h2
  · intro h
    have hg : MvPolynomial.map (algebraMap k₀ K) (X 0 - X 1) =
        (X 0 - X 1 : MvPolynomial (Fin 2) K) := by simp
    rw [← hg]; exact map_dvd _ h

/-- The base-change morphism sends the marked point `0` of `ℙ¹_K` to the marked point `0`
of `ℙ¹_{k₀}`. -/
lemma mapOfAlgebra_base_zero :
    (mapOfAlgebra k₀ K).base (zero K) = zero k₀ := by
  have hb : (mapOfAlgebra k₀ K).base (zero K) =
      comap (gradedMapOfAlgebra k₀ K) (irrelevant_le_map_gradedMapOfAlgebra k₀ K) (zero K) := rfl
  rw [hb]
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective ?_)
  change ((zero K).asHomogeneousIdeal.comap (gradedMapOfAlgebra k₀ K)).toIdeal =
    (zero k₀).asHomogeneousIdeal.toIdeal
  rw [HomogeneousIdeal.toIdeal_comap, zero, zero, mkPoint_asIdeal, mkPoint_asIdeal]
  ext p
  simp only [Ideal.mem_comap, gradedMapOfAlgebra_apply, Ideal.mem_span_singleton]
  exact X_dvd_map_iff (algebraMap k₀ K).injective 0 p

/-- The base-change morphism sends the marked point `∞` of `ℙ¹_K` to the marked point `∞`
of `ℙ¹_{k₀}`. -/
lemma mapOfAlgebra_base_infty :
    (mapOfAlgebra k₀ K).base (infty K) = infty k₀ := by
  have hb : (mapOfAlgebra k₀ K).base (infty K) =
      comap (gradedMapOfAlgebra k₀ K) (irrelevant_le_map_gradedMapOfAlgebra k₀ K) (infty K) := rfl
  rw [hb]
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective ?_)
  change ((infty K).asHomogeneousIdeal.comap (gradedMapOfAlgebra k₀ K)).toIdeal =
    (infty k₀).asHomogeneousIdeal.toIdeal
  rw [HomogeneousIdeal.toIdeal_comap, infty, infty, mkPoint_asIdeal, mkPoint_asIdeal]
  ext p
  simp only [Ideal.mem_comap, gradedMapOfAlgebra_apply, Ideal.mem_span_singleton]
  exact X_dvd_map_iff (algebraMap k₀ K).injective 1 p

/-- The base-change morphism sends the marked point `1` of `ℙ¹_K` to the marked point `1`
of `ℙ¹_{k₀}`. -/
lemma mapOfAlgebra_base_one :
    (mapOfAlgebra k₀ K).base (one K) = one k₀ := by
  have hb : (mapOfAlgebra k₀ K).base (one K) =
      comap (gradedMapOfAlgebra k₀ K) (irrelevant_le_map_gradedMapOfAlgebra k₀ K) (one K) := rfl
  rw [hb]
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective ?_)
  change ((one K).asHomogeneousIdeal.comap (gradedMapOfAlgebra k₀ K)).toIdeal =
    (one k₀).asHomogeneousIdeal.toIdeal
  rw [HomogeneousIdeal.toIdeal_comap, one, one, mkPoint_asIdeal, mkPoint_asIdeal]
  ext p
  simp only [Ideal.mem_comap, gradedMapOfAlgebra_apply, Ideal.mem_span_singleton]
  exact X0_sub_X1_dvd_map_iff k₀ K p

end Belyi.P1
