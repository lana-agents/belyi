/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.Noncritical
import Belyi.CurveField.BelyiRelation

/-!
# Noncritical Belyi maps, in the language of `Belyi.CurveField.IsBelyi`

The ramification indices and cusps of `Belyi.CurveField.Noncritical` agree with those of
`Belyi.CurveField.ramIdx` and `Belyi.CurveField.belyiCusps`; hence **noncritical Belyi maps**
([NCB] = S. Mochizuki, *Noncritical Belyi maps*, Theorem 2.5): for every finite set `T` of places
of a curve over a number field there is a Belyi function `φ` none of whose cusps lies in `T`
(`Belyi.CurveField.exists_isBelyi_notMem_belyiCusps`).
-/

namespace Belyi.CurveField

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

theorem Noncritical.ramIdx_eq (P : Place K) (φ : K) :
    Noncritical.ramIdx P φ = (Belyi.CurveField.ramIdx φ P : ℤ) := by
  by_cases h : φ ∈ P.1
  · rw [Belyi.CurveField.ramIdx_of_mem h]
    unfold Noncritical.ramIdx
    rw [dif_pos h]
    rfl
  · rw [Belyi.CurveField.ramIdx_of_notMem h]
    unfold Noncritical.ramIdx
    rw [dif_neg h]

theorem Noncritical.cusps_eq (φ : K) :
    Noncritical.cusps φ = Belyi.CurveField.belyiCusps φ := rfl

theorem Noncritical.isBelyi_iff (φ : K) :
    Noncritical.IsBelyi φ ↔ Belyi.CurveField.IsBelyi φ := by
  refine and_congr Iff.rfl (forall_congr' fun P => ?_)
  rw [Noncritical.ramIdx_eq, Noncritical.cusps_eq]
  constructor
  · intro h h1
    exact h (by exact_mod_cast h1)
  · intro h h1
    exact h (by exact_mod_cast h1)

/-- **Noncritical Belyi maps** ([NCB], Theorem 2.5): for every finite set `T` of places there is
a Belyi function whose cusps avoid `T`. -/
theorem exists_isBelyi_notMem_belyiCusps (T : Finset (Place K)) :
    ∃ φ : K, IsBelyi φ ∧ ∀ P ∈ T, P ∉ belyiCusps φ := by
  obtain ⟨φ, hφ, hT⟩ := Noncritical.exists_isBelyi_forall_notMem_cusps T
  exact ⟨φ, (Noncritical.isBelyi_iff φ).mp hφ, hT⟩

end Belyi.CurveField
