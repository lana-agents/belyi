/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Unramified.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.Separable

/-!
# Derivations along a transcendental element of a function field

Let `K` be a field of characteristic zero and `t : K` transcendental over `ℚ` such that
`K` is algebraic over `ℚ⟮t⟯` (e.g. `K` a function field of a curve over a number field
and `t` a nonconstant function).  Then there is a unique `ℚ`-derivation `d/dt` of `K`
with `t ↦ 1`; we call it `Belyi.CurveDeriv.derivAlong t`.

## Main definitions and results

* `Derivation.extendOfFormallyEtale`, `Derivation.ext_of_formallyUnramified`: a derivation
  `S → T` (with `T` a formally étale `S`-algebra) extends uniquely to `T`; two derivations of
  `T` which agree on `S` agree if `T` is formally unramified over `S`.  These are proved via
  `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`.
* `Belyi.CurveDeriv.derivAlong t : Derivation ℚ K K`, the derivation `d/dt`
  (defined to be `0` if the hypotheses fail).
* `derivAlong_self`: `derivAlong t t = 1`.
* `derivation_ext_of_eq`: two `ℚ`-derivations of `K` agreeing on `t` are equal.
* `derivAlong_aeval`: `derivAlong t (aeval t p) = aeval t (derivative p)`.
* `derivAlong_eq_smul`, `derivAlong_mul_derivAlong`: the chain rule.
* `Derivation.map_eq_zero_of_isAlgebraic`: derivations kill elements algebraic over `ℚ`.
-/

open Polynomial IntermediateField
open scoped IntermediateField

/-! ### Extending derivations along formally étale maps -/

section Extension

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T]

open KaehlerDifferential TensorProduct

/-- Extension of a derivation `d : S → T` to a derivation `T → T` when `T` is formally étale
over `S`: the composite `Ω[T⁄R] ≅ T ⊗[S] Ω[S⁄R] → T`. -/
noncomputable def Derivation.extendOfFormallyEtale [Algebra.FormallyEtale S T]
    (d : Derivation R S T) : Derivation R T T :=
  ((LinearMap.liftBaseChange T d.liftKaehlerDifferential) ∘ₗ
    (tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer (KaehlerDifferential.D R T)

@[simp]
theorem Derivation.extendOfFormallyEtale_algebraMap [Algebra.FormallyEtale S T]
    (d : Derivation R S T) (s : S) :
    d.extendOfFormallyEtale (algebraMap S T s) = d s := by
  simp [Derivation.extendOfFormallyEtale, tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

omit [Algebra R S] [IsScalarTower R S T] in
/-- A derivation of a formally unramified `S`-algebra `T` which vanishes on `S` vanishes. -/
theorem Derivation.eq_zero_of_formallyUnramified [Algebra.FormallyUnramified S T]
    (D : Derivation R T T) (hD : ∀ s : S, D (algebraMap S T s) = 0) : D = 0 := by
  let D' : Derivation S T T :=
    { toFun := D
      map_add' := D.map_add
      map_smul' := fun s x => by
        rw [Algebra.smul_def, D.leibniz, hD, smul_zero, add_zero, smul_eq_mul, RingHom.id_apply,
          Algebra.smul_def]
      map_one_eq_zero' := D.map_one_eq_zero
      leibniz' := D.leibniz }
  ext x
  change D' x = 0
  rw [← D'.liftKaehlerDifferential_comp_D, Subsingleton.elim (KaehlerDifferential.D S T x) 0,
    map_zero]

omit [Algebra R S] [IsScalarTower R S T] in
/-- Two derivations of a formally unramified `S`-algebra `T` which agree on `S` agree. -/
theorem Derivation.ext_of_formallyUnramified [Algebra.FormallyUnramified S T]
    (D₁ D₂ : Derivation R T T) (h : ∀ s : S, D₁ (algebraMap S T s) = D₂ (algebraMap S T s)) :
    D₁ = D₂ := by
  rw [← sub_eq_zero]
  exact Derivation.eq_zero_of_formallyUnramified (S := S) _ fun s => by simp [h s]

end Extension

/-! ### Derivations killing algebraic elements -/

section Algebraic

variable {K : Type*} [Field K] [CharZero K]

/-- A `ℚ`-derivation of a field of characteristic zero kills every element algebraic
over `ℚ`. -/
theorem Derivation.map_eq_zero_of_isAlgebraic (D : Derivation ℚ K K) {x : K}
    (hx : IsAlgebraic ℚ x) : D x = 0 := by
  have hint := hx.isIntegral
  have hsep : (minpoly ℚ x).Separable := (minpoly.irreducible hint).separable
  have h0 : aeval x (derivative (minpoly ℚ x)) ≠ 0 := by
    intro h
    obtain ⟨a, b, hab⟩ := hsep
    have := congrArg (aeval x) hab
    simp [h, minpoly.aeval] at this
  have := D.map_aeval (minpoly ℚ x) x
  rw [minpoly.aeval, D.map_zero, smul_eq_mul, eq_comm, mul_eq_zero] at this
  exact this.resolve_left h0

end Algebraic

namespace Belyi.CurveDeriv

variable {K : Type*} [Field K] [CharZero K]

/-! ### The derivation `d/dt` -/

section Construction

variable (t : K)

/-- The value in `K` of the isomorphism `ℚ[X] ≃ ℚ[t]` is evaluation at `t`. -/
theorem coe_algEquivOfTranscendental (ht : Transcendental ℚ t) (p : ℚ[X]) :
    ((Polynomial.algEquivOfTranscendental ℚ t ht p : Algebra.adjoin ℚ {t}) : K) = aeval t p := by
  rw [Polynomial.algEquivOfTranscendental_apply]
  exact (aeval_algHom_apply (Algebra.adjoin ℚ {t}).val _ p).symm

theorem aeval_algEquivOfTranscendental_symm (ht : Transcendental ℚ t)
    (a : Algebra.adjoin ℚ {t}) :
    aeval t ((Polynomial.algEquivOfTranscendental ℚ t ht).symm a) = (a : K) := by
  rw [← coe_algEquivOfTranscendental t ht, AlgEquiv.apply_symm_apply]

/-- The derivation `d/dt : ℚ[t] → K` on the polynomial ring `ℚ[t] ⊆ K`, for `t`
transcendental over `ℚ`. -/
noncomputable def polyDeriv (ht : Transcendental ℚ t) : Derivation ℚ (Algebra.adjoin ℚ {t}) K where
  toFun a := aeval t (derivative ((Polynomial.algEquivOfTranscendental ℚ t ht).symm a))
  map_add' a b := by simp
  map_smul' q a := by simp
  map_one_eq_zero' := by simp
  leibniz' a b := by
    change aeval t (derivative ((Polynomial.algEquivOfTranscendental ℚ t ht).symm (a * b))) =
      (a : K) * aeval t (derivative ((Polynomial.algEquivOfTranscendental ℚ t ht).symm b)) +
      (b : K) * aeval t (derivative ((Polynomial.algEquivOfTranscendental ℚ t ht).symm a))
    simp only [map_mul, derivative_mul, map_add, aeval_algEquivOfTranscendental_symm]
    ring

theorem polyDeriv_apply (ht : Transcendental ℚ t) (p : ℚ[X]) :
    polyDeriv t ht (Polynomial.algEquivOfTranscendental ℚ t ht p) = aeval t (derivative p) := by
  simp only [polyDeriv, Derivation.mk_coe, LinearMap.coe_mk, AddHom.coe_mk,
    AlgEquiv.symm_apply_apply]

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem formallyEtale_adjoin [Algebra.IsAlgebraic ℚ⟮t⟯ K] :
    Algebra.FormallyEtale (Algebra.adjoin ℚ {t}) K := by
  have : Algebra.FormallyEtale (Algebra.adjoin ℚ {t}) ℚ⟮t⟯ :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (Algebra.adjoin ℚ {t}))
  have : Algebra.FormallyEtale ℚ⟮t⟯ K := Algebra.FormallyEtale.of_isSeparable _ _
  exact Algebra.FormallyEtale.comp _ ℚ⟮t⟯ K

open Classical in
/-- The derivation `d/dt` of `K`: the unique `ℚ`-derivation of `K` with `t ↦ 1`, when `t` is
transcendental over `ℚ` and `K` is algebraic over `ℚ⟮t⟯` (and `0` otherwise). -/
noncomputable def derivAlong : Derivation ℚ K K :=
  if h : Transcendental ℚ t ∧ Algebra.IsAlgebraic ℚ⟮t⟯ K then
    have := h.2
    have := formallyEtale_adjoin t
    (polyDeriv t h.1).extendOfFormallyEtale
  else 0

variable {t}

theorem derivAlong_aeval (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K] (p : ℚ[X]) :
    derivAlong t (aeval t p) = aeval t (derivative p) := by
  have := formallyEtale_adjoin t
  have key : aeval t p = algebraMap (Algebra.adjoin ℚ {t}) K
      (Polynomial.algEquivOfTranscendental ℚ t ht p) :=
    (coe_algEquivOfTranscendental t ht p).symm
  rw [derivAlong, dif_pos ⟨ht, ‹_›⟩, key, Derivation.extendOfFormallyEtale_algebraMap,
    polyDeriv_apply]

@[simp]
theorem derivAlong_self (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K] :
    derivAlong t t = 1 := by
  simpa using derivAlong_aeval ht X

/-- Uniqueness: two `ℚ`-derivations of `K` which agree on `t` are equal. -/
theorem derivation_ext_of_eq (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K]
    (D₁ D₂ : Derivation ℚ K K) (h : D₁ t = D₂ t) : D₁ = D₂ := by
  have := formallyEtale_adjoin t
  refine Derivation.ext_of_formallyUnramified (S := Algebra.adjoin ℚ {t}) D₁ D₂ fun s => ?_
  obtain ⟨p, hp⟩ := (Polynomial.algEquivOfTranscendental ℚ t ht).surjective s
  have : algebraMap (Algebra.adjoin ℚ {t}) K s = aeval t p := by
    rw [← hp]; exact coe_algEquivOfTranscendental t ht p
  rw [this, D₁.map_aeval, D₂.map_aeval, h]

/-- Uniqueness, characterisation form: a `ℚ`-derivation `D` of `K` with `D t = 1` is
`derivAlong t`. -/
theorem eq_derivAlong (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K]
    (D : Derivation ℚ K K) (h : D t = 1) : D = derivAlong t :=
  derivation_ext_of_eq ht _ _ (by rw [h, derivAlong_self ht])

/-- Every `ℚ`-derivation of `K` is a multiple of `d/dt`: `D = (D t) • d/dt`. -/
theorem eq_smul_derivAlong (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K]
    (D : Derivation ℚ K K) : D = D t • derivAlong t :=
  derivation_ext_of_eq ht _ _ (by simp [derivAlong_self ht])

/-- Chain rule: `d/ds = (ds/dt) • d/dt`. -/
theorem derivAlong_eq_smul (s : K) (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K] :
    derivAlong s = derivAlong s t • derivAlong t :=
  eq_smul_derivAlong ht _

/-- Chain rule: `(dt/ds) · (ds/dt) = 1`. -/
theorem derivAlong_mul_derivAlong {s : K} (hs : Transcendental ℚ s) [Algebra.IsAlgebraic ℚ⟮s⟯ K]
    (ht : Transcendental ℚ t) [Algebra.IsAlgebraic ℚ⟮t⟯ K] :
    derivAlong t s * derivAlong s t = 1 := by
  have := congrArg (· s) (derivAlong_eq_smul s ht)
  simp only [derivAlong_self hs, Derivation.smul_apply, smul_eq_mul] at this
  rw [this, mul_comm]

/-- `d/dt` kills the elements of `K` algebraic over `ℚ`. -/
theorem derivAlong_eq_zero_of_isAlgebraic {x : K} (hx : IsAlgebraic ℚ x) :
    derivAlong t x = 0 :=
  (derivAlong t).map_eq_zero_of_isAlgebraic hx

@[simp]
theorem derivAlong_algebraMap (q : ℚ) : derivAlong t (algebraMap ℚ K q) = 0 :=
  (derivAlong t).map_algebraMap q

end Construction

end Belyi.CurveDeriv
