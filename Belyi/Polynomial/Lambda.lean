/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Polynomial.CritVal
import Mathlib.Algebra.CharP.Algebra

/-!
# The Belyi polynomials `λ_{m,n}`

This file defines the polynomials

`λ_{m,n} = ((m+n)^(m+n) / (m^m n^n)) · X^m (1-X)^n ∈ ℚ[X]`   (`m, n ≥ 1`)

used in the second reduction step of Belyi's theorem (statement B7 of
`references/proof-outline.md`), and proves their key properties:

* `Belyi.lambda_eval_zero`, `Belyi.lambda_eval_one`: `λ_{m,n}` maps `0` and `1` to `0`;
* `Belyi.lambda_eval_mid`: `λ_{m,n}` maps `m/(m+n)` to `1`;
* `Belyi.critVal_lambda`: all critical values of `λ_{m,n}` lie in `{0, 1}`
  (the critical points are `0`, `1` and `m/(m+n)`);
* `Belyi.natDegree_lambda`: `λ_{m,n}` has degree `m + n`.

Together with `Belyi.exists_pos_num_add_den` (writing a rational in `(0,1)` as `m/(m+n)`),
these are the ingredients of the inductive reduction in
`Belyi.Polynomial.ReductionZeroOne`.
-/

namespace Belyi

open Polynomial

/-- The normalizing constant of the Belyi polynomial `λ_{m,n}`. -/
def lambdaConst (m n : ℕ) : ℚ :=
  ((m + n : ℚ) ^ (m + n)) / ((m : ℚ) ^ m * (n : ℚ) ^ n)

/-- The Belyi polynomial `λ_{m,n} = ((m+n)^(m+n) / (m^m n^n)) · X^m (1-X)^n`.
For `m, n ≥ 1` it maps `{0, 1, m/(m+n), ∞}` into `{0, 1, ∞}` and all its critical
values lie in `{0, 1}`. -/
noncomputable def lambda (m n : ℕ) : ℚ[X] :=
  C (lambdaConst m n) * (X ^ m * (1 - X) ^ n)

lemma lambdaConst_ne_zero {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : lambdaConst m n ≠ 0 := by
  have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have h2 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h3 : (m + n : ℚ) ≠ 0 := by positivity
  simp only [lambdaConst]
  positivity

lemma lambda_ne_zero {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : lambda m n ≠ 0 := by
  have h1 : (1 - X : ℚ[X]) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval 0) h
    simp at this
  simp [lambda, lambdaConst_ne_zero hm hn, X_ne_zero, h1]

lemma natDegree_lambda {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (lambda m n).natDegree = m + n := by
  have h1 : (1 - X : ℚ[X]).natDegree = 1 := by
    rw [show (1 - X : ℚ[X]) = -(X - C 1) by simp]
    rw [natDegree_neg, natDegree_X_sub_C]
  have h2 : (1 - X : ℚ[X]) ≠ 0 := fun h => by
    have := congrArg (Polynomial.eval 0) h; simp at this
  rw [lambda, natDegree_C_mul (lambdaConst_ne_zero hm hn),
    natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ h2),
    natDegree_pow, natDegree_pow, natDegree_X, h1, mul_one, mul_one]

@[simp]
lemma lambda_eval_zero {m n : ℕ} (hm : m ≠ 0) : (lambda m n).eval 0 = 0 := by
  simp [lambda, zero_pow hm]

@[simp]
lemma lambda_eval_one {m n : ℕ} (hn : n ≠ 0) : (lambda m n).eval 1 = 0 := by
  simp [lambda, zero_pow hn]

lemma lambda_eval_mid {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (lambda m n).eval ((m : ℚ) / (m + n)) = 1 := by
  have h1 : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have h2 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h3 : (m + n : ℚ) ≠ 0 := by positivity
  have h4 : 1 - (m : ℚ) / (m + n) = (n : ℚ) / (m + n) := by
    field_simp
    ring_nf
  simp only [lambda, lambdaConst, eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one, h4,
    div_pow]
  field_simp
  ring

/-- The derivative of `λ_{m,n}` in factored form: its roots are `0`, `1` and `m/(m+n)`. -/
lemma derivative_lambda (m n : ℕ) :
    derivative (lambda (m + 1) (n + 1)) =
      C (lambdaConst (m + 1) (n + 1)) *
        (X ^ m * (1 - X) ^ n * (((m : ℚ[X]) + 1) - ((m : ℚ[X]) + (n : ℚ[X]) + 2) * X)) := by
  simp only [lambda, derivative_mul, derivative_C, derivative_pow, derivative_X,
    derivative_sub, derivative_one]
  push_cast
  simp only [C_add, C_1, C_eq_natCast]
  ring

/-- The critical values of `λ_{m,n}` (in any field extension `K` of `ℚ`) lie in `{0, 1}`. -/
lemma critVal_lambda {K : Type*} [Field K] [Algebra ℚ K] {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {x : K} (hx : x ∈ critVal K (lambda m n)) : x = 0 ∨ x = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  obtain ⟨a, ⟨-, ha⟩, rfl⟩ := mem_critVal_iff.mp hx
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  rw [derivative_lambda] at ha
  simp only [map_mul, map_sub, map_pow, aeval_C, aeval_X, map_ofNat, map_add, map_one,
    map_natCast] at ha
  have hc : algebraMap ℚ K (lambdaConst (m + 1) (n + 1)) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap ℚ K).injective).mpr
      (lambdaConst_ne_zero (Nat.succ_ne_zero m) (Nat.succ_ne_zero n))
  rcases mul_eq_zero.mp ha with h | h
  · exact absurd h hc
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · -- `a = 0`
      left
      obtain ⟨ha0, -⟩ := pow_eq_zero_iff'.mp h
      simp [ha0, lambda, zero_pow (Nat.succ_ne_zero m)]
    · -- `a = 1`, with critical value `λ(1) = 0`
      left
      obtain ⟨ha1', -⟩ := pow_eq_zero_iff'.mp h
      have ha1 : a = 1 := (sub_eq_zero.mp ha1').symm
      simp [ha1, lambda, zero_pow (Nat.succ_ne_zero n)]
  · -- `a = m/(m+n)`, the critical value is `1`
    right
    have hden : ((m : K) + (n : K) + 2) ≠ 0 := by
      have h0 : ((m + n + 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at h0
      exact h0
    have haval : a = algebraMap ℚ K (((m : ℚ) + 1) / ((m : ℚ) + (n : ℚ) + 2)) := by
      rw [map_div₀]
      simp only [map_add, map_one, map_natCast, map_ofNat]
      rw [eq_div_iff hden]
      linear_combination -h
    have hmid : Polynomial.eval (((m : ℚ) + 1) / ((m : ℚ) + (n : ℚ) + 2))
        (lambda (m + 1) (n + 1)) = 1 := by
      have h1 := lambda_eval_mid (m := m + 1) (n := n + 1)
        (Nat.succ_ne_zero m) (Nat.succ_ne_zero n)
      have h2 : ((m + 1 : ℕ) : ℚ) / ((m + 1 : ℕ) + (n + 1 : ℕ)) =
          ((m : ℚ) + 1) / ((m : ℚ) + (n : ℚ) + 2) := by
        push_cast; ring_nf
      rwa [h2] at h1
    rw [haval, aeval_algebraMap_apply_eq_algebraMap_eval, hmid, map_one]

end Belyi
