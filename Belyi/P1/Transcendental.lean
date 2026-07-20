/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.AffineChart
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Points of `ℙ¹` attached to transcendental elements are not closed

The non-constancy input (c) to B1 (taxis issue #46): for a field extension `K/k` and
`t : K` transcendental over `k`, the image of the `K`-valued point
`P1.point k t : Spec K ⟶ P1 k` is not a closed point of `ℙ¹`.

The proof avoids the chart isomorphism `(k[X₀,X₁]_{X₁})₀ ≃ k[t]`: the image point lies
in the chart `Spec (k[X₀,X₁]_{X₁})₀` and its prime is `ker (awayEval k t)`. If it were
closed, the kernel would be maximal (`PrimeSpectrum.isClosed_singleton_iff_isMaximal`,
transported along the open immersion `Proj.awayι` by continuity), so the residue ring —
a finite-type `k`-algebra which is a field — would be finite over `k` by Zariski's
lemma (`finite_of_finite_type_of_isJacobsonRing`). But `t` is the image of the degree-1
fraction `X₀/X₁` (`Belyi.P1.affineCoord`), hence would be algebraic over `k`.

## Main definitions

* `Belyi.P1.awayEvalₐ`: `awayEval` as a `k`-algebra homomorphism (for the scoped
  `k`-algebra structure on the chart ring).
* `Belyi.P1.affineCoord`: the affine coordinate `X₀/X₁` in the chart ring, with
  `awayEval k t (affineCoord k) = t`.
* `Belyi.P1.not_isClosed_singleton_point_of_transcendental`: the main statement.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

section AlgebraStructure

variable (k : Type u) [CommRing k]

/-- The chart ring `(k[X₀,X₁]_{X₁})₀` as a `k`-algebra, through the identification of
`k` with the degree-zero part of the grading. -/
noncomputable scoped instance instAlgebraAway :
    Algebra k (Away (P1Grading k) (X 1 : MvPolynomial (Fin 2) k)) :=
  ((fromZeroRingHom (P1Grading k) (Submonoid.powers (X 1 : MvPolynomial (Fin 2) k))).comp
    (algebraMap k (P1Grading k 0))).toAlgebra

variable {R : Type u} [CommRing R] [Algebra k R]

/-- The evaluation of the chart ring at `t` as a `k`-algebra homomorphism. -/
noncomputable def awayEvalₐ (t : R) :
    Away (P1Grading k) (X 1 : MvPolynomial (Fin 2) k) →ₐ[k] R :=
  { awayEval k t with
    commutes' := fun c => by
      have h := awayEval_fromZeroRingHom k t (algebraMap k (P1Grading k 0) c)
      simp only [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq, aeval_C] at h
      exact h }

@[simp]
lemma awayEvalₐ_toRingHom (t : R) : (awayEvalₐ k t : _ →+* R) = awayEval k t := rfl

/-- The affine coordinate `X₀/X₁` of the standard chart, as an element of the chart
ring. -/
noncomputable def affineCoord : Away (P1Grading k) (X 1 : MvPolynomial (Fin 2) k) :=
  HomogeneousLocalization.mk
    ⟨1, ⟨X 0, X_mem_P1Grading k 0⟩, ⟨X 1, X_mem_P1Grading k 1⟩, 1, pow_one _⟩

/-- Evaluation at `t` sends the affine coordinate to `t`. -/
lemma awayEval_affineCoord (t : R) : awayEval k t (affineCoord k) = t := by
  have hv : ((aeval ![t, 1] : MvPolynomial (Fin 2) k →ₐ[k] R) :
      MvPolynomial (Fin 2) k →+* R) (X 1) * 1 = 1 := by simp
  have hval : (affineCoord k).val =
      Localization.mk (X 0 : MvPolynomial (Fin 2) k)
        (⟨X 1 ^ 1, 1, rfl⟩ : Submonoid.powers (X 1 : MvPolynomial (Fin 2) k)) := by
    rw [affineCoord, val_mk]
    congr 1
    exact Subtype.ext (pow_one _).symm
  rw [awayEval, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, hval,
    Localization.awayLift_mk (v := 1) (hv := hv)]
  simp

/-- The chart ring is of finite type over `k`. -/
lemma finiteType_away : Algebra.FiniteType k
    (Away (P1Grading k) (X 1 : MvPolynomial (Fin 2) k)) := by
  have h1 : (fromZeroRingHom (P1Grading k)
      (Submonoid.powers (X 1 : MvPolynomial (Fin 2) k))).FiniteType :=
    HomogeneousLocalization.Away.finiteType (X 1) 1 (X_mem_P1Grading k 1)
  have h2 : (algebraMap k (P1Grading k 0)).FiniteType :=
    RingHom.FiniteType.of_surjective _ (gradeZeroEquiv k).surjective
  exact h1.comp h2

end AlgebraStructure

section Transcendental

variable (k : Type u) [Field k] {K : Type u} [Field K] [Algebra k K]

/-- The image of the `K`-valued point of `ℙ¹` with affine coordinate a transcendental
element is not a closed point. This is the non-constancy input to B1: for a
non-constant rational function `t` on a curve, the induced map to `ℙ¹` sends the
generic point to a non-closed point, so its fibers are finite. -/
theorem not_isClosed_singleton_point_of_transcendental {t : K} (ht : Transcendental k t) :
    ¬ IsClosed ({point k t (IsLocalRing.closedPoint K)} : Set (P1 k)) := by
  intro hcl
  set R := Away (P1Grading k) (X 1 : MvPolynomial (Fin 2) k) with hR
  set y : Spec (CommRingCat.of R) :=
    (Spec.map (CommRingCat.ofHom (awayEval k t))) (IsLocalRing.closedPoint K) with hy
  have himg : point k t (IsLocalRing.closedPoint K) =
      Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos y := by
    rw [point, Scheme.Hom.comp_apply]
    rfl
  -- closedness descends to the chart
  have hy1 : IsClosed ({y} : Set (Spec (CommRingCat.of R))) := by
    have hpre := hcl.preimage
      (Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos).continuous
    convert hpre using 1
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, himg]
    exact ⟨fun h => h ▸ rfl, fun h => (Proj.awayι (P1Grading k) (X 1)
      (X_mem_P1Grading k 1) one_pos).isOpenEmbedding.injective h⟩
  -- the prime of the image point is the kernel of the evaluation
  let y' : PrimeSpectrum R := y
  have hyker : y'.asIdeal = RingHom.ker (awayEval k t) := by
    change (PrimeSpectrum.comap (awayEval k t) (IsLocalRing.closedPoint K)).asIdeal = _
    have hbot : (IsLocalRing.closedPoint K).asIdeal = ⊥ :=
      IsLocalRing.maximalIdeal_eq_bot
    rw [PrimeSpectrum.comap_asIdeal, hbot]
    rfl
  have hmax : (RingHom.ker (awayEval k t)).IsMaximal := by
    rw [← hyker]
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal y').mp hy1
  -- Zariski's lemma: the residue field is algebraic over k
  haveI : (RingHom.ker ((awayEvalₐ k t : _ →ₐ[k] K) : R →+* K)).IsMaximal := hmax
  set m : Ideal R := RingHom.ker ((awayEvalₐ k t : _ →ₐ[k] K) : R →+* K)
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI := finiteType_away k
  haveI hqft : Algebra.FiniteType k (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m)
      (Ideal.Quotient.mkₐ_surjective k m)
  haveI hfin : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _
  haveI : Algebra.IsIntegral k (R ⧸ m) := Algebra.IsIntegral.of_finite k _
  -- transport algebraicity to t along the induced embedding into K
  let ψ : (R ⧸ m) →ₐ[k] K :=
    Ideal.Quotient.liftₐ m (awayEvalₐ k t) fun a ha => RingHom.mem_ker.mp ha
  have h1 : IsIntegral k (Ideal.Quotient.mkₐ k m (affineCoord k)) :=
    Algebra.IsIntegral.isIntegral _
  have h2 := h1.map ψ
  have h3 : ψ (Ideal.Quotient.mkₐ k m (affineCoord k)) = t := by
    change ψ (Ideal.Quotient.mk m (affineCoord k)) = t
    rw [show ψ (Ideal.Quotient.mk m (affineCoord k)) = awayEvalₐ k t (affineCoord k) from
      Ideal.Quotient.liftₐ_apply m (awayEvalₐ k t) _ _]
    exact awayEval_affineCoord k t
  rw [h3] at h2
  exact ht h2.isAlgebraic

end Transcendental

end Belyi.P1
