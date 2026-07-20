/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Curve.Stalks
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Kähler differentials of a localization and the rank at a stalk

Taxis issue #75: the remaining input to the cotangent bound of `Belyi/Curve/Stalks.lean`
is the *rank of `Ω` at a stalk* of a smooth morphism.  A stalk `𝒪_{X,x}` is a
localization of an affine chart ring `A`, so this file provides the purely
ring-theoretic bridge, over a **fixed** base field `k`:

* `Belyi.kaehlerLocalizationEquiv`: for `B` a localization of a `k`-algebra `A`, the
  canonical `B`-linear identification `B ⊗[A] Ω[A⁄k] ≃ₗ[B] Ω[B⁄k]`.  This is
  `KaehlerDifferential.isLocalizedModule_map` (`Ω` localizes over the fixed base),
  packaged as a base change.
* `Belyi.finrank_residue_tensor_kaehler_localization`: if `Ω[A⁄k]` is a finite free
  `A`-module, then over a *local* localization `B` the residue-field base change
  `κ_B ⊗[B] Ω[B⁄k]` is finite and
  `finrank κ_B (κ_B ⊗[B] Ω[B⁄k]) = finrank A Ω[A⁄k]`.

Specialised to a **standard smooth chart of relative dimension `n`**
(`Belyi.finrank_residue_tensor_kaehler_of_standardSmooth`), where `Ω[A⁄k]` is free of
rank `n` (`Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`), this
computes the residue rank at the stalk to be exactly `n`.  Combined with the
formal-smoothness transfer (`Belyi.formallySmooth_of_isLocalization`) and the cotangent
criterion of `Belyi/Curve/Stalks.lean`, a standard smooth chart of relative dimension `1`
gives the `ValuationRing` and `Ring.KrullDimLE 1` hypotheses of B1
(`Belyi.valuationRing_of_standardSmooth_localization`,
`Belyi.krullDimLE_one_of_standardSmooth_localization`).

The only piece still deferred to the scheme layer is producing, around a point of a
smooth curve, an affine chart that is standard smooth of relative dimension `1` and
identifying the stalk with a localization of its coordinate ring.
-/

universe u v

namespace Belyi

open Module IsLocalRing TensorProduct KaehlerDifferential

section Localization

variable (k : Type u) [Field k]
variable (A : Type v) [CommRing A] [Algebra k A]
variable (M : Submonoid A) (B : Type v) [CommRing B] [Algebra A B] [IsLocalization M B]
variable [Algebra k B] [IsScalarTower k A B]

/-- **Kähler differentials commute with localization of the algebra over a fixed base.**
For `B` a localization of the `k`-algebra `A` at a submonoid `M ⊆ A`, the canonical map
`Ω[A⁄k] → Ω[B⁄k]` exhibits `Ω[B⁄k]` as the base change of `Ω[A⁄k]` along `A → B`. -/
noncomputable def kaehlerLocalizationEquiv : B ⊗[A] Ω[A⁄k] ≃ₗ[B] Ω[B⁄k] :=
  ((isLocalizedModule_iff_isBaseChange M B (map k k A B)).mp inferInstance).equiv

variable [Nontrivial A] [IsLocalRing B]
variable [Module.Free A Ω[A⁄k]] [Module.Finite A Ω[A⁄k]]

include A M

omit [Nontrivial A] [IsLocalRing B] [Module.Finite A Ω[A⁄k]] in
/-- The module of Kähler differentials of a localization of `A` (with `Ω[A⁄k]` finite
free) is finite free. -/
theorem free_kaehler_localization : Module.Free B Ω[B⁄k] :=
  Module.Free.of_equiv (kaehlerLocalizationEquiv k A M B)

omit [Nontrivial A] [IsLocalRing B] [Module.Free A Ω[A⁄k]] in
theorem finite_kaehler_localization : Module.Finite B Ω[B⁄k] :=
  Module.Finite.equiv (kaehlerLocalizationEquiv k A M B)

omit [Module.Finite A Ω[A⁄k]] in
/-- The `B`-rank of `Ω[B⁄k]` equals the `A`-rank of `Ω[A⁄k]`. -/
theorem finrank_kaehler_localization :
    finrank B Ω[B⁄k] = finrank A Ω[A⁄k] := by
  rw [← LinearEquiv.finrank_eq (kaehlerLocalizationEquiv k A M B), Module.finrank_baseChange]

omit [Nontrivial A] [Module.Free A Ω[A⁄k]] in
/-- The residue-field base change of `Ω` at a local localization is finite. -/
theorem finite_residue_tensor_kaehler_localization :
    Module.Finite (ResidueField B) (ResidueField B ⊗[B] Ω[B⁄k]) := by
  haveI := finite_kaehler_localization k A M B
  infer_instance

omit [Module.Finite A Ω[A⁄k]] in
/-- **The rank of `Ω` at the stalk.** For `B` a local localization of the `k`-algebra `A`
whose Kähler differentials are finite free, the residue-field base change
`κ_B ⊗[B] Ω[B⁄k]` has dimension equal to the `A`-rank of `Ω[A⁄k]`. -/
theorem finrank_residue_tensor_kaehler_localization :
    finrank (ResidueField B) (ResidueField B ⊗[B] Ω[B⁄k]) = finrank A Ω[A⁄k] := by
  haveI := free_kaehler_localization k A M B
  rw [Module.finrank_baseChange]
  exact finrank_kaehler_localization k A M B

end Localization

section StandardSmooth

open Algebra

variable (k : Type u) [Field k]
variable (A : Type v) [CommRing A] [Nontrivial A] [Algebra k A]

/-- For a standard smooth algebra of relative dimension `n` over a field, `Ω[A⁄k]` has
`A`-rank `n`. -/
theorem finrank_kaehler_of_standardSmooth (n : ℕ)
    [IsStandardSmoothOfRelativeDimension n k A] : finrank A Ω[A⁄k] = n := by
  haveI : IsStandardSmooth k A := IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  exact finrank_eq_of_rank_eq
    (IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := A) n)

variable (M : Submonoid A) (B : Type v) [CommRing B] [Algebra A B] [IsLocalization M B]
variable [Algebra k B] [IsScalarTower k A B] [IsLocalRing B]

include k A M in
/-- **The rank of `Ω` at a stalk of a standard smooth chart.** If `A` is standard smooth
of relative dimension `n` over `k` and `B` is a local localization of `A`, then the
residue-field base change `κ_B ⊗[B] Ω[B⁄k]` has dimension exactly `n`. -/
theorem finrank_residue_tensor_kaehler_of_standardSmooth (n : ℕ)
    [IsStandardSmoothOfRelativeDimension n k A] :
    finrank (ResidueField B) (ResidueField B ⊗[B] Ω[B⁄k]) = n := by
  haveI : IsStandardSmooth k A := IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  rw [finrank_residue_tensor_kaehler_localization k A M B,
    finrank_kaehler_of_standardSmooth k A n]

omit [Nontrivial A] [IsLocalRing B] in
include k A M in
/-- A localization of a formally smooth `k`-algebra is formally smooth over `k`. -/
theorem formallySmooth_localization [FormallySmooth k A] : FormallySmooth k B := by
  haveI : FormallySmooth A B := FormallySmooth.of_isLocalization (Rₘ := B) M
  exact FormallySmooth.comp k A B

include k A M in
/-- **From a standard smooth chart of relative dimension `1` to a valuation ring.** A
Noetherian local domain that is a localization of a chart standard smooth of relative
dimension `1` over `k` (with formally smooth residue field, automatic in characteristic
zero) is a valuation ring — the hypothesis `hX` of `Belyi.isFinite_homOfFunctionField`. -/
theorem valuationRing_of_standardSmooth_localization
    [IsStandardSmoothOfRelativeDimension 1 k A] [IsNoetherianRing B] [IsDomain B]
    [FormallySmooth k (ResidueField B)] : ValuationRing B := by
  haveI : IsStandardSmooth k A := IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  haveI := formallySmooth_localization k A M B
  haveI := finite_residue_tensor_kaehler_localization k A M B
  exact valuationRing_of_finrank_kaehler_le_one B
    (le_of_eq (finrank_residue_tensor_kaehler_of_standardSmooth k A M B 1))

include k A M in
/-- **From a standard smooth chart of relative dimension `1` to Krull dimension `≤ 1`.**
The companion of `Belyi.valuationRing_of_standardSmooth_localization`; the hypothesis
`hdim` of `Belyi.isFinite_homOfFunctionField`. -/
theorem krullDimLE_one_of_standardSmooth_localization
    [IsStandardSmoothOfRelativeDimension 1 k A] [IsNoetherianRing B] [IsDomain B]
    [FormallySmooth k (ResidueField B)] : Ring.KrullDimLE 1 B := by
  haveI : IsStandardSmooth k A := IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  haveI := formallySmooth_localization k A M B
  haveI := finite_residue_tensor_kaehler_localization k A M B
  exact krullDimLE_one_of_finrank_kaehler_le_one B
    (le_of_eq (finrank_residue_tensor_kaehler_of_standardSmooth k A M B 1))

end StandardSmooth

end Belyi
