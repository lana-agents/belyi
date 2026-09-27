/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.Place

/-!
# Residue fields and degrees of places

The residue field `κ(P)` of a place `P` of a curve field `K` is a number field: by the chart
description, it is a quotient of the chart ring `A_t` (a `ℚ`-algebra of finite type) by a
maximal ideal, hence finite over `ℚ` by Zariski's lemma. The degree of `P` is `[κ(P) : ℚ]`.

## Main definitions

* `Belyi.CurveField.Place.ResidueField P`: the residue field of `P`, with its canonical
  `ℚ`-algebra structure (it has characteristic `0`).
* `Belyi.CurveField.Place.residue P : P.1 →+* P.ResidueField`.
* `Belyi.CurveField.Place.deg P : ℕ := Module.finrank ℚ P.ResidueField`.

## Main results

* `FiniteDimensional ℚ P.ResidueField`, `NumberField P.ResidueField`, `0 < P.deg`.
-/

open IsLocalRing

namespace Belyi.CurveField.Place

variable {K : Type*} [Field K] (P : Place K)

/-- The residue field of a place. -/
def ResidueField (P : Place K) : Type _ := IsLocalRing.ResidueField P.1

noncomputable instance : Field P.ResidueField :=
  inferInstanceAs (Field (IsLocalRing.ResidueField P.1))

noncomputable instance : Algebra P.1 P.ResidueField :=
  inferInstanceAs (Algebra P.1 (IsLocalRing.ResidueField P.1))

/-- The residue map `O_P → κ(P)`. -/
noncomputable def residue : P.1 →+* P.ResidueField := IsLocalRing.residue P.1

theorem algebraMap_eq_residue : algebraMap P.1 P.ResidueField = P.residue := rfl

theorem residue_surjective : Function.Surjective P.residue := IsLocalRing.residue_surjective

theorem residue_eq_zero_iff {a : P.1} : P.residue a = 0 ↔ a ∈ maximalIdeal P.1 :=
  IsLocalRing.residue_eq_zero_iff a

variable [CharZero K]

/-- The inclusion `ℚ → O_P`. -/
noncomputable def ratHom : ℚ →+* P.1 := (Rat.castHom K).codRestrict P.1 P.ratCast_mem

@[simp]
theorem coe_ratHom (q : ℚ) : (P.ratHom q : K) = q := rfl

instance : CharZero P.ResidueField :=
  charZero_of_injective_ringHom (P.residue.comp P.ratHom).injective

@[simp]
theorem residue_ratHom (q : ℚ) : P.residue (P.ratHom q) = (q : P.ResidueField) :=
  map_ratCast (P.residue.comp P.ratHom) q

theorem residue_mk_ratCast (q : ℚ) :
    P.residue ⟨(q : K), P.ratCast_mem q⟩ = (q : P.ResidueField) :=
  P.residue_ratHom q

variable [IsCurveField K]

instance : FiniteDimensional ℚ P.ResidueField := by
  obtain ⟨t, ht, htP⟩ := P.exists_transcendental_mem
  have : Fact (Transcendental ℚ t) := ⟨ht⟩
  let φ : chartRing t →+* P.ResidueField := (IsLocalRing.residue P.1).comp
    ((algebraMap (chartRing t) K).codRestrict P.1 (P.algebraMap_chartRing_mem t htP))
  have hφ : Function.Surjective φ := P.residue_comp_surjective t htP
  have : Algebra.FiniteType ℚ P.ResidueField :=
    Algebra.FiniteType.of_surjective φ.toRatAlgHom hφ
  exact finite_of_finite_type_of_isJacobsonRing ℚ P.ResidueField

/-- The residue field of a place is a number field. -/
instance : NumberField P.ResidueField where

/-- The degree `[κ(P) : ℚ]` of a place. -/
noncomputable def deg : ℕ := Module.finrank ℚ P.ResidueField

theorem deg_pos : 0 < P.deg := Module.finrank_pos

end Belyi.CurveField.Place
