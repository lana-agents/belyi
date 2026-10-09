/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.P1.ChartInjective
import Belyi.P1.Transcendental
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# The standard affine charts of `ℙ¹` are affine lines

The two standard affine charts `D₊(X₀)`, `D₊(X₁)` of the projective line `ℙ¹ = Proj k[X₀,X₁]`
have degree-zero chart ring a univariate polynomial ring: the affine coordinate
(`X₀/X₁` on `D₊(X₁)`, resp. `X₁/X₀` on `D₊(X₀)`) is a free polynomial generator over `k`.

This is the reusable commutative-algebra foundation for the base-change isomorphism
`ℙ¹_{k₀} ×_{k₀} K ≅ ℙ¹_K` (taxis issue #109/#126), and also feeds the surjectivity half
of B1 (#46) and the branch-locus computations (#47, #106).

The proof reuses the injectivity of the chart evaluation at a transcendental point
(`Belyi/P1/ChartInjective.lean`) applied to the transcendental `Polynomial.X`:
* **injectivity** is `Belyi.P1.awayEval_injective` (generalised here to a base commutative
  ring, since the argument never used that `k`, `K` are fields);
* **surjectivity** holds because the image is a `k`-subalgebra containing the affine
  coordinate, which maps to `Polynomial.X`, and `Algebra.adjoin k {X} = ⊤`.

The `D₊(X₀)` chart is reduced to the `D₊(X₁)` chart by the coordinate swap
`Equiv.swap 0 1`, using the identity `aeval ![1, t] a = aeval ![t, 1] (rename (swap 0 1) a)`.

## Main definitions

* `Belyi.P1.awayChartEquivOne k : Away (P1Grading k) X₁ ≃ₐ[k] k[T]` — the `D₊(X₁)` chart.
* `Belyi.P1.awayChartEquivZero k : Away (P1Grading k) X₀ ≃ₐ[k] k[T]` — the `D₊(X₀)` chart.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

section OneChart

variable (k : Type u) [CommRing k] {R : Type u} [CommRing R] [Algebra k R]

/-- **Injectivity of the chart evaluation at a transcendental point**, over an arbitrary
base commutative ring. For `t : R` transcendental over `k`, the evaluation
`awayEval k t : (k[X₀,X₁]_{X₁})₀ →+* R` sending `X₀/X₁ ↦ t` is injective. This is the
`CommRing` generalisation of `Belyi.P1.awayEval_injective`; the proof is identical, as it
never uses that the rings are fields. -/
theorem awayEval_injective_of_transcendental {t : R} (ht : Transcendental k t) :
    Function.Injective (awayEval k t) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (P1Grading k) (X_mem_P1Grading k 1) z
  rw [awayEval_mk] at hz
  have ha' : a.IsHomogeneous (n • 1) := (mem_homogeneousSubmodule _ _).mp ha
  have : a = 0 := aeval_isHomogeneous_eq_zero_of_transcendental ht ha' hz
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, this, HomogeneousLocalization.val_zero,
    Localization.mk_zero]

/-- The chart evaluation at `Polynomial.X` is surjective: its image is a `k`-subalgebra
containing the affine coordinate (which maps to `Polynomial.X`), hence is everything. -/
theorem awayEvalₐ_surjective :
    Function.Surjective (awayEvalₐ k (Polynomial.X : Polynomial k)) := by
  rw [← AlgHom.range_eq_top, eq_top_iff, ← Polynomial.adjoin_X, Algebra.adjoin_le_iff]
  rintro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨affineCoord k, awayEval_affineCoord k (Polynomial.X : Polynomial k)⟩

/-- **The `D₊(X₁)` chart of `ℙ¹` is the affine line.** The chart ring
`(k[X₀,X₁]_{X₁})₀` is `k`-algebra isomorphic to `k[T]`, the affine coordinate `X₀/X₁`
corresponding to `Polynomial.X`. -/
noncomputable def awayChartEquivOne :
    Away (P1Grading k) (X 1 : MvPolynomial (Fin 2) k) ≃ₐ[k] Polynomial k :=
  AlgEquiv.ofBijective (awayEvalₐ k (Polynomial.X : Polynomial k))
    ⟨awayEval_injective_of_transcendental k (Polynomial.transcendental_X k),
      awayEvalₐ_surjective k⟩

@[simp]
lemma awayChartEquivOne_affineCoord :
    awayChartEquivOne k (affineCoord k) = (Polynomial.X : Polynomial k) :=
  awayEval_affineCoord k (Polynomial.X : Polynomial k)

end OneChart

section ZeroChart

variable (k : Type u) [CommRing k] {R : Type u} [CommRing R] [Algebra k R]

/-- The chart ring `(k[X₀,X₁]_{X₀})₀` of `D₊(X₀)` as a `k`-algebra, through the
identification of `k` with the degree-zero part of the grading. -/
noncomputable scoped instance instAlgebraAwayZero :
    Algebra k (Away (P1Grading k) (X 0 : MvPolynomial (Fin 2) k)) :=
  ((fromZeroRingHom (P1Grading k) (Submonoid.powers (X 0 : MvPolynomial (Fin 2) k))).comp
    (algebraMap k (P1Grading k 0))).toAlgebra

/-- Evaluation of the chart ring of `D₊(X₀) ⊆ ℙ¹` at an element `t` of a `k`-algebra:
the ring map `(k[X₀,X₁]_{X₀})₀ →+* R` sending `X₁/X₀` to `t`. -/
noncomputable def awayEval0 (t : R) : Away (P1Grading k) (X 0 : MvPolynomial (Fin 2) k) →+* R :=
  (Localization.awayLift ((aeval ![1, t] : MvPolynomial (Fin 2) k →ₐ[k] R) : _ →+* R)
      (X 0) (by simp)).comp
    (algebraMap (Away (P1Grading k) (X 0)) (Localization.Away (X 0 : MvPolynomial (Fin 2) k)))

/-- The chart-ring evaluation `awayEval0 k t` on a homogeneous fraction `a / (X₀)^n`
returns `aeval ![1, t] a`: the denominator `X₀` evaluates to `1`, so it drops out. -/
lemma awayEval0_mk (t : R) (n : ℕ) (a : MvPolynomial (Fin 2) k)
    (ha : a ∈ P1Grading k (n • 1)) :
    awayEval0 k t (Away.mk (P1Grading k) (X_mem_P1Grading k 0) n a ha) = aeval ![1, t] a := by
  simp only [awayEval0, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.awayLift_mk (v := 1) (hv := by simp)]
  simp

lemma awayEval0_fromZeroRingHom (t : R) (x : P1Grading k 0) :
    awayEval0 k t (fromZeroRingHom (P1Grading k) _ x) =
      aeval ![1, t] (x : MvPolynomial (Fin 2) k) := by
  have hval : (fromZeroRingHom (P1Grading k)
        (Submonoid.powers (X 0 : MvPolynomial (Fin 2) k)) x).val =
      algebraMap (MvPolynomial (Fin 2) k)
        (Localization.Away (X 0 : MvPolynomial (Fin 2) k)) x := by
    simp only [fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, val_mk]
    exact Localization.mk_one_eq_algebraMap _
  simp [awayEval0, hval]

/-- The evaluation of the `D₊(X₀)` chart ring at `t` as a `k`-algebra homomorphism. -/
noncomputable def awayEvalₐ0 (t : R) :
    Away (P1Grading k) (X 0 : MvPolynomial (Fin 2) k) →ₐ[k] R :=
  { awayEval0 k t with
    commutes' := fun c => by
      have h := awayEval0_fromZeroRingHom k t (algebraMap k (P1Grading k 0) c)
      simp only [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq, aeval_C] at h
      exact h }

@[simp]
lemma awayEvalₐ0_toRingHom (t : R) : (awayEvalₐ0 k t : _ →+* R) = awayEval0 k t := rfl

/-- The affine coordinate `X₁/X₀` of the chart `D₊(X₀)`, as an element of the chart ring. -/
noncomputable def affineCoord0 : Away (P1Grading k) (X 0 : MvPolynomial (Fin 2) k) :=
  HomogeneousLocalization.mk
    ⟨1, ⟨X 1, X_mem_P1Grading k 1⟩, ⟨X 0, X_mem_P1Grading k 0⟩, 1, pow_one _⟩

/-- Evaluation at `t` sends the affine coordinate `X₁/X₀` to `t`. -/
lemma awayEval0_affineCoord (t : R) : awayEval0 k t (affineCoord0 k) = t := by
  have hv : ((aeval ![1, t] : MvPolynomial (Fin 2) k →ₐ[k] R) :
      MvPolynomial (Fin 2) k →+* R) (X 0) * 1 = 1 := by simp
  have hval : (affineCoord0 k).val =
      Localization.mk (X 1 : MvPolynomial (Fin 2) k)
        (⟨X 0 ^ 1, 1, rfl⟩ : Submonoid.powers (X 0 : MvPolynomial (Fin 2) k)) := by
    rw [affineCoord0, val_mk]
    congr 1
    exact Subtype.ext (pow_one _).symm
  rw [awayEval0, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, hval,
    Localization.awayLift_mk (v := 1) (hv := hv)]
  simp

/-- Evaluating at `(1, t)` factors, via the coordinate swap `X₀ ↔ X₁`, through evaluation
at `(t, 1)`: `aeval ![1, t] a = aeval ![t, 1] (rename (swap 0 1) a)`. -/
lemma aeval_cons_swap (t : R) (a : MvPolynomial (Fin 2) k) :
    (aeval ![1, t] : MvPolynomial (Fin 2) k →ₐ[k] R) a =
      aeval ![t, 1] (rename (Equiv.swap 0 1) a) := by
  rw [aeval_rename]
  have hfun : (![1, t] : Fin 2 → R) = ![t, 1] ∘ (Equiv.swap (0 : Fin 2) 1) := by
    funext i
    fin_cases i <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [hfun]

/-- **Injectivity of the `D₊(X₀)` chart evaluation at a transcendental point.** Reduced to
the `D₊(X₁)` case by the coordinate swap. -/
theorem awayEval0_injective_of_transcendental {t : R} (ht : Transcendental k t) :
    Function.Injective (awayEval0 k t) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, a, ha, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (P1Grading k) (X_mem_P1Grading k 0) z
  rw [awayEval0_mk, aeval_cons_swap] at hz
  have ha' : a.IsHomogeneous (n • 1) := (mem_homogeneousSubmodule _ _).mp ha
  have hra : (rename (Equiv.swap 0 1) a).IsHomogeneous (n • 1) := ha'.rename_isHomogeneous
  have hz0 : rename (Equiv.swap 0 1) a = 0 :=
    aeval_isHomogeneous_eq_zero_of_transcendental ht hra hz
  have ha0 : a = 0 := by
    rwa [← rename_zero (Equiv.swap (0 : Fin 2) 1),
      (rename_injective _ (Equiv.injective _)).eq_iff] at hz0
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, ha0, HomogeneousLocalization.val_zero,
    Localization.mk_zero]

/-- The `D₊(X₀)` chart evaluation at `Polynomial.X` is surjective. -/
theorem awayEvalₐ0_surjective :
    Function.Surjective (awayEvalₐ0 k (Polynomial.X : Polynomial k)) := by
  rw [← AlgHom.range_eq_top, eq_top_iff, ← Polynomial.adjoin_X, Algebra.adjoin_le_iff]
  rintro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨affineCoord0 k, awayEval0_affineCoord k (Polynomial.X : Polynomial k)⟩

/-- **The `D₊(X₀)` chart of `ℙ¹` is the affine line.** The chart ring
`(k[X₀,X₁]_{X₀})₀` is `k`-algebra isomorphic to `k[T]`, the affine coordinate `X₁/X₀`
corresponding to `Polynomial.X`. -/
noncomputable def awayChartEquivZero :
    Away (P1Grading k) (X 0 : MvPolynomial (Fin 2) k) ≃ₐ[k] Polynomial k :=
  AlgEquiv.ofBijective (awayEvalₐ0 k (Polynomial.X : Polynomial k))
    ⟨awayEval0_injective_of_transcendental k (Polynomial.transcendental_X k),
      awayEvalₐ0_surjective k⟩

@[simp]
lemma awayChartEquivZero_affineCoord :
    awayChartEquivZero k (affineCoord0 k) = (Polynomial.X : Polynomial k) :=
  awayEval0_affineCoord k (Polynomial.X : Polynomial k)

end ZeroChart

end Belyi.P1
