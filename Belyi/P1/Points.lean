/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1

/-!
# The marked points `0`, `1`, `∞` of the projective line

This file defines the three marked points of `Belyi.P1 k` (taxis issue #46) as points of
the underlying space of `Proj k[X₀, X₁]`, i.e. as homogeneous prime ideals:

* `0 = [0:1]` is the homogeneous prime `(X₀)`;
* `1 = [1:1]` is the homogeneous prime `(X₀ - X₁)`;
* `∞ = [1:0]` is the homogeneous prime `(X₁)`.

Design note (recorded on the issue): we take the "direct route" — the marked points are
explicit homogeneous primes, not images of points under chart isomorphisms
`Away 𝒜 (Xᵢ) ≃ k[t]`. The full closed-points ↔ `k ∪ {∞}` dictionary over the affine
charts is deferred until the branch-locus work (issue #47) makes precise what is needed.

## Main definitions

* `Belyi.P1.mkPoint`: the point of `P1 k` cut out by a homogeneous prime polynomial that
  vanishes at some vector with a nonzero coordinate (the last two hypotheses guarantee
  that the ideal does not contain the irrelevant ideal).
* `Belyi.P1.zero`, `Belyi.P1.one`, `Belyi.P1.infty`: the three marked points.
* `Belyi.P1.zero_ne_one`, `Belyi.P1.zero_ne_infty`, `Belyi.P1.one_ne_infty`: the marked
  points are pairwise distinct.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

section mkPoint

/-- The point of the projective line cut out by a homogeneous prime polynomial `f`.
The hypotheses `eval v f = 0` and `v i ≠ 0` exhibit a point of `𝔸² \ {0}` on the cone
`f = 0`, which guarantees that `(f)` does not contain the irrelevant ideal. -/
noncomputable def mkPoint (f : MvPolynomial (Fin 2) k) (hp : Prime f) (n : ℕ)
    (hn : f.IsHomogeneous n) (v : Fin 2 → k) (hv : eval v f = 0) (i : Fin 2)
    (hvi : v i ≠ 0) :
    ProjectiveSpectrum (P1Grading k) where
  asHomogeneousIdeal :=
    ⟨Ideal.span {f}, Ideal.homogeneous_span _ _ fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ ⟨n, (mem_homogeneousSubmodule _ _).mpr hn⟩⟩
  isPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  not_irrelevant_le := by
    intro hle
    have hXi : (X i : MvPolynomial (Fin 2) k) ∈ HomogeneousIdeal.irrelevant (P1Grading k) :=
      HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
        ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i))
    have hdvd : f ∣ X i := Ideal.mem_span_singleton.mp (hle hXi)
    have h0 : (0 : k) ∣ v i := by simpa [hv] using map_dvd (eval v) hdvd
    exact hvi (zero_dvd_iff.mp h0)

@[simp]
lemma mkPoint_asIdeal (f : MvPolynomial (Fin 2) k) (hp : Prime f) (n : ℕ)
    (hn : f.IsHomogeneous n) (v : Fin 2 → k) (hv : eval v f = 0) (i : Fin 2)
    (hvi : v i ≠ 0) :
    (mkPoint k f hp n hn v hv i hvi).asHomogeneousIdeal.toIdeal = Ideal.span {f} :=
  rfl

end mkPoint

section Prime

/-- The coordinate functions are prime in `k[X₀, X₁]`. -/
lemma prime_X (i : Fin 2) : Prime (X i : MvPolynomial (Fin 2) k) := by
  have h0 : Prime (X 0 : MvPolynomial (Fin 2) k) := by
    have h : Prime ((finSuccEquiv k 1) (X 0)) := by
      rw [finSuccEquiv_X_zero]
      exact Polynomial.prime_X
    exact (MulEquiv.prime_iff _).mp h
  fin_cases i
  · exact h0
  · have h := (MulEquiv.prime_iff (renameEquiv k (Equiv.swap (0 : Fin 2) 1))).mpr h0
    simpa using h

/-- The linear form `X₀ - X₁` is prime in `k[X₀, X₁]`. -/
lemma prime_X_sub_X : Prime (X 0 - X 1 : MvPolynomial (Fin 2) k) := by
  have h : Prime ((finSuccEquiv k 1) (X 0 - X 1)) := by
    have h1 : (X 1 : MvPolynomial (Fin 2) k) = X (Fin.succ 0) := rfl
    rw [map_sub, finSuccEquiv_X_zero, h1, finSuccEquiv_X_succ]
    exact Polynomial.prime_X_sub_C _
  exact (MulEquiv.prime_iff _).mp h

end Prime

/-- The marked point `0 = [0:1]` of the projective line: the homogeneous prime `(X₀)`. -/
noncomputable def zero : P1 k :=
  mkPoint k (X 0) (prime_X k 0) 1 (isHomogeneous_X k 0) ![0, 1] (by simp) 1 one_ne_zero

/-- The marked point `1 = [1:1]` of the projective line: the homogeneous prime
`(X₀ - X₁)`. -/
noncomputable def one : P1 k :=
  mkPoint k (X 0 - X 1) (prime_X_sub_X k) 1
    ((isHomogeneous_X k 0).sub (isHomogeneous_X k 1)) ![1, 1] (by simp) 0 one_ne_zero

/-- The marked point `∞ = [1:0]` of the projective line: the homogeneous prime `(X₁)`. -/
noncomputable def infty : P1 k :=
  mkPoint k (X 1) (prime_X k 1) 1 (isHomogeneous_X k 1) ![1, 0] (by simp) 0 one_ne_zero

section Distinct

variable {k}

/-- Everything in the ideal of a point vanishes at a vector on its cone. -/
lemma eval_eq_zero_of_mem_span {f g : MvPolynomial (Fin 2) k} {v : Fin 2 → k}
    (hv : eval v f = 0) (hg : g ∈ Ideal.span {f}) : eval v g = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hg
  simp [hv]

variable (k)

lemma zero_ne_one : zero k ≠ one k := by
  intro h
  have hId : Ideal.span {(X 0 : MvPolynomial (Fin 2) k)} =
      Ideal.span {(X 0 - X 1 : MvPolynomial (Fin 2) k)} :=
    congrArg (fun x : ProjectiveSpectrum (P1Grading k) => x.asHomogeneousIdeal.toIdeal) h
  have hmem : (X 0 : MvPolynomial (Fin 2) k) ∈
      Ideal.span {(X 0 - X 1 : MvPolynomial (Fin 2) k)} :=
    hId ▸ Ideal.subset_span rfl
  have := eval_eq_zero_of_mem_span (v := ![1, 1]) (by simp) hmem
  simp at this

lemma zero_ne_infty : zero k ≠ infty k := by
  intro h
  have hId : Ideal.span {(X 0 : MvPolynomial (Fin 2) k)} =
      Ideal.span {(X 1 : MvPolynomial (Fin 2) k)} :=
    congrArg (fun x : ProjectiveSpectrum (P1Grading k) => x.asHomogeneousIdeal.toIdeal) h
  have hmem : (X 0 : MvPolynomial (Fin 2) k) ∈
      Ideal.span {(X 1 : MvPolynomial (Fin 2) k)} :=
    hId ▸ Ideal.subset_span rfl
  have := eval_eq_zero_of_mem_span (v := ![1, 0]) (by simp) hmem
  simp at this

lemma one_ne_infty : one k ≠ infty k := by
  intro h
  have hId : Ideal.span {(X 0 - X 1 : MvPolynomial (Fin 2) k)} =
      Ideal.span {(X 1 : MvPolynomial (Fin 2) k)} :=
    congrArg (fun x : ProjectiveSpectrum (P1Grading k) => x.asHomogeneousIdeal.toIdeal) h
  have hmem : (X 0 - X 1 : MvPolynomial (Fin 2) k) ∈
      Ideal.span {(X 1 : MvPolynomial (Fin 2) k)} :=
    hId ▸ Ideal.subset_span rfl
  have := eval_eq_zero_of_mem_span (v := ![1, 0]) (by simp) hmem
  simp at this

end Distinct

end Belyi.P1
