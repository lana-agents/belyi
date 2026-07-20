/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Curve.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Stalks of one-dimensional schemes: from cotangent rank to valuation rings

Reduction step for taxis issue #75 (the last blocker of B1, split off from #46): the
hypotheses `ValuationRing 𝒪_{X,x}` and `Ring.KrullDimLE 1 𝒪_{X,x}` consumed by
`Belyi.homOfFunctionField` and `Belyi.isFinite_homOfFunctionField` both follow from a
single statement about the *cotangent space*, which is what smoothness of relative
dimension `1` is expected to provide:

> for each `x : X`, the residue-field vector space `𝔪ₓ/𝔪ₓ²` has dimension `≤ 1`.

This file proves that implication (`Belyi.valuationRing_of_finrank_cotangentSpace_le_one`
and friends), so that the remaining smoothness work in #75 only has to produce the
cotangent bound — no valuation theory, no Krull dimension.

The local ring hypotheses are the ones automatically available on an integral,
locally Noetherian scheme: the stalks are Noetherian local domains
(`AlgebraicGeometry.IsLocallyNoetherian`, `IsIntegral`).

## Main results

* `Belyi.isDiscreteValuationRing_or_isField_of_finrank_cotangentSpace_le_one`:
  a Noetherian local domain with `dim 𝔪/𝔪² ≤ 1` is a DVR or a field.
* `Belyi.valuationRing_of_finrank_cotangentSpace_le_one`,
  `Belyi.krullDimLE_one_of_finrank_cotangentSpace_le_one`: the two consequences.
* `Belyi.valuationRing_stalk_of_cotangent`, `Belyi.krullDimLE_one_stalk_of_cotangent`:
  the scheme-level packaging, in exactly the `∀ x : X, …` shape that
  `Belyi.isFinite_homOfFunctionField` consumes.
-/

universe u

namespace Belyi

open AlgebraicGeometry Module IsLocalRing

section LocalRing

variable (A : Type*) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]

/-- A Noetherian local domain whose cotangent space has dimension `≤ 1` is a discrete
valuation ring or a field. -/
theorem isDiscreteValuationRing_or_isField_of_finrank_cotangentSpace_le_one
    (h : finrank (ResidueField A) (CotangentSpace A) ≤ 1) :
    IsDiscreteValuationRing A ∨ IsField A := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · exact Or.inr (finrank_cotangentSpace_eq_zero_iff.mp h0)
  · exact Or.inl (finrank_CotangentSpace_eq_one_iff.mp h1)

/-- A Noetherian local domain whose cotangent space has dimension `≤ 1` is a valuation
ring. -/
theorem valuationRing_of_finrank_cotangentSpace_le_one
    (h : finrank (ResidueField A) (CotangentSpace A) ≤ 1) : ValuationRing A := by
  rcases isDiscreteValuationRing_or_isField_of_finrank_cotangentSpace_le_one A h with hd | hf
  · exact inferInstance
  · letI := hf.toField
    infer_instance

/-- A Noetherian local domain whose cotangent space has dimension `≤ 1` has Krull
dimension `≤ 1`. -/
theorem krullDimLE_one_of_finrank_cotangentSpace_le_one
    (h : finrank (ResidueField A) (CotangentSpace A) ≤ 1) : Ring.KrullDimLE 1 A := by
  rcases isDiscreteValuationRing_or_isField_of_finrank_cotangentSpace_le_one A h with hd | hf
  · exact inferInstance
  · letI := hf.toField
    have h0 : Ring.KrullDimLE 0 A :=
      Ring.KrullDimLE.mk₀ fun I hI => by
        letI := hI
        rw [Ideal.eq_bot_of_prime I]
        exact Ideal.bot_isMaximal
    infer_instance

end LocalRing

section Scheme

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

/-- Stalks of an integral locally Noetherian scheme with cotangent spaces of dimension
`≤ 1` are valuation rings: the hypothesis `hX` of `Belyi.homOfFunctionField`. -/
theorem valuationRing_stalk_of_cotangent
    (h : ∀ x : X, finrank (ResidueField (X.presheaf.stalk x))
      (CotangentSpace (X.presheaf.stalk x)) ≤ 1) (x : X) :
    ValuationRing (X.presheaf.stalk x) :=
  valuationRing_of_finrank_cotangentSpace_le_one _ (h x)

/-- Stalks of an integral locally Noetherian scheme with cotangent spaces of dimension
`≤ 1` have Krull dimension `≤ 1`: the hypothesis `hdim` of
`Belyi.isFinite_homOfFunctionField`. -/
theorem krullDimLE_one_stalk_of_cotangent
    (h : ∀ x : X, finrank (ResidueField (X.presheaf.stalk x))
      (CotangentSpace (X.presheaf.stalk x)) ≤ 1) (x : X) :
    Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
  krullDimLE_one_of_finrank_cotangentSpace_le_one _ (h x)

end Scheme

end Belyi
