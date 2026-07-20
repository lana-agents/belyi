/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.AffineChartBaseChange
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Homogenize

/-!
# The affine-chart evaluation at a transcendental element is injective

For a field extension `K/k` and `t : K` transcendental over `k`, the chart evaluation
`Belyi.P1.awayEval k t : (k[X₀,X₁]_{X₁})₀ →+* K` (which sends the affine coordinate
`X₀/X₁` to `t`) is injective, i.e. its kernel is `⊥`.

This strengthens `Belyi.P1.not_isClosed_singleton_point_of_transcendental`
(`Belyi/P1/Transcendental.lean`), which only shows the image prime `ker (awayEval k t)`
is *not maximal*. Injectivity says it is the *bottom* prime — the algebraic content of
"the point `Belyi.P1.point k t` attached to a transcendental element is the generic
point of the affine chart", which feeds the dominance/surjectivity half of B1
(taxis issue #46).

The proof uses that a homogeneous polynomial `a` of degree `n` is recovered from its
dehomogenisation `aeval ![X, 1] a : k[X]` via `Polynomial.homogenize`
(`Polynomial.homogenize_eq_of_isHomogeneous`): so if `aeval ![t, 1] a = 0` with `t`
transcendental, then `aeval ![X, 1] a = 0` (`transcendental_iff_injective`), hence
`a = 0`. Combined with `Belyi.P1.awayEval_mk` (every chart element is `a / X₁ⁿ` with
`a` homogeneous, evaluating to `aeval ![t, 1] a`) this gives injectivity.

## Main results

* `Belyi.P1.aeval_isHomogeneous_eq_zero_of_transcendental`: a homogeneous polynomial
  killed by `aeval ![t, 1]` (for `t` transcendental) is zero.
* `Belyi.P1.awayEval_injective`: `awayEval k t` is injective for `t` transcendental.
* `Belyi.P1.ker_awayEval`: `RingHom.ker (awayEval k t) = ⊥`.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

section
variable (k : Type u) [CommRing k] {K : Type u} [CommRing K] [Algebra k K]

/-- Evaluating a two-variable polynomial at `(t, 1)` factors as dehomogenising in the
second variable (`X₁ ↦ 1`, landing in `k[X]`) followed by evaluating at `t`. -/
lemma aeval_cons_eq_aeval_dehomogenize (t : K) (a : MvPolynomial (Fin 2) k) :
    MvPolynomial.aeval ![t, 1] a =
      Polynomial.aeval t (MvPolynomial.aeval ![(Polynomial.X : Polynomial k), 1] a) := by
  have h : (MvPolynomial.aeval ![t, 1] : MvPolynomial (Fin 2) k →ₐ[k] K) =
      (Polynomial.aeval t).comp
        (MvPolynomial.aeval ![(Polynomial.X : Polynomial k), 1]) :=
    MvPolynomial.algHom_ext fun i => by fin_cases i <;> simp
  exact DFunLike.congr_fun h a

variable {k}

/-- A homogeneous polynomial annihilated by evaluation `X₀ ↦ t, X₁ ↦ 1` at a
transcendental `t` is zero: the evaluation is injective on each homogeneous piece. -/
lemma aeval_isHomogeneous_eq_zero_of_transcendental {t : K} (ht : Transcendental k t)
    {n : ℕ} {a : MvPolynomial (Fin 2) k} (ha : a.IsHomogeneous n)
    (h : MvPolynomial.aeval ![t, 1] a = 0) : a = 0 := by
  rw [aeval_cons_eq_aeval_dehomogenize] at h
  have hp : MvPolynomial.aeval ![(Polynomial.X : Polynomial k), 1] a = 0 :=
    transcendental_iff_injective.mp ht (h.trans (map_zero _).symm)
  have hhom := Polynomial.homogenize_eq_of_isHomogeneous ha hp
  rwa [Polynomial.homogenize_zero, eq_comm] at hhom

end

section Transcendental
variable (k : Type u) [Field k] {K : Type u} [Field K] [Algebra k K]

/-- **Injectivity of the chart evaluation at a transcendental point.** For `t : K`
transcendental over `k`, the evaluation `awayEval k t : (k[X₀,X₁]_{X₁})₀ →+* K` sending
`X₀/X₁ ↦ t` is injective. -/
theorem awayEval_injective {t : K} (ht : Transcendental k t) :
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

/-- The kernel of the chart evaluation at a transcendental point is `⊥`. -/
theorem ker_awayEval {t : K} (ht : Transcendental k t) :
    RingHom.ker (awayEval k t) = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).mp (awayEval_injective k ht)

end Transcendental

end Belyi.P1
