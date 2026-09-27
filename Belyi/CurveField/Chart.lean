/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.Basic

/-!
# Affine charts of a curve field

For `t` in a curve field `K` transcendental over `ℚ`, the *chart ring* `A_t` is the integral
closure of `ℚ[t] = Algebra.adjoin ℚ {t}` in `K`. It is the coordinate ring of the affine
open `{t ≠ ∞}` of the regular proper model of the curve: a Dedekind domain, finite over
`ℚ[t]`, of finite type over `ℚ`, with fraction field `K`. Every place of `K` containing `t` is
the localisation of `A_t` at a height-one prime (see `Belyi.CurveField.Place`).

The instances depending on the transcendence of `t` take the hypothesis in the form
`[Fact (Transcendental ℚ t)]`.

## Main definitions and results

* `Belyi.CurveField.chartRing t`: the integral closure of `ℚ[t]` in `K`.
* instances `IsDedekindDomain (chartRing t)`, `IsFractionRing (chartRing t) K`,
  `Module.Finite (Algebra.adjoin ℚ {t}) (chartRing t)`, `Algebra.FiniteType ℚ (chartRing t)`.
* `Belyi.CurveField.chartRing_le`: `A_t` is contained in every integrally closed subring
  containing `ℚ` and `t` (e.g. valuation subrings).
* `Belyi.CurveField.inv_notMem_chartRing`: `t⁻¹ ∉ A_t`, i.e. `t` is not a unit of `A_t`.
-/

open Polynomial
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin

namespace Belyi.CurveField

variable {K : Type*} [Field K] [CharZero K]

/-- The chart ring `A_t`: the integral closure of `ℚ[t]` in `K`. -/
abbrev chartRing (t : K) : Subalgebra (Algebra.adjoin ℚ {t}) K :=
  integralClosure (Algebra.adjoin ℚ {t}) K

variable {t : K}

theorem mem_chartRing_of_mem_adjoin {x : K} (hx : x ∈ Algebra.adjoin ℚ {t}) :
    x ∈ chartRing t :=
  (chartRing t).algebraMap_mem ⟨x, hx⟩

variable (t) in
theorem self_mem_chartRing : t ∈ chartRing t :=
  mem_chartRing_of_mem_adjoin (Algebra.self_mem_adjoin_singleton ℚ t)

variable (t) in
theorem ratCast_mem_chartRing (q : ℚ) : (q : K) ∈ chartRing t :=
  mem_chartRing_of_mem_adjoin (Subalgebra.algebraMap_mem _ q)

/-- The chart ring is contained in every integrally closed subring containing `ℚ` and `t`. -/
theorem chartRing_le {S : Subring K} [IsIntegrallyClosedIn S K] (hq : ∀ q : ℚ, (q : K) ∈ S)
    (ht : t ∈ S) : (chartRing t).toSubring ≤ S := by
  rw [Subring.integralClosure_le_iff]
  rintro ⟨r, hr⟩
  change r ∈ S
  induction hr using Algebra.adjoin_induction with
  | mem x hx => obtain rfl := Set.mem_singleton_iff.mp hx; exact ht
  | algebraMap q => exact hq q
  | add x y _ _ hx hy => exact S.add_mem hx hy
  | mul x y _ _ hx hy => exact S.mul_mem hx hy

/-- The chart ring is contained in every valuation subring containing `ℚ` and `t`. -/
theorem mem_of_mem_chartRing (V : ValuationSubring K) (hq : ∀ q : ℚ, (q : K) ∈ V)
    (ht : t ∈ V) {x : K} (hx : x ∈ chartRing t) : x ∈ V := by
  have : IsIntegrallyClosedIn V.toSubring K := inferInstanceAs (IsIntegrallyClosedIn V K)
  exact chartRing_le (S := V.toSubring) hq ht hx

theorem isDedekindDomain_adjoin (ht : Transcendental ℚ t) :
    IsDedekindDomain (Algebra.adjoin ℚ {t}) := by
  have e := Polynomial.algEquivOfTranscendental ℚ t ht
  have : IsPrincipalIdealRing (Algebra.adjoin ℚ {t}) :=
    IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  infer_instance

instance [Fact (Transcendental ℚ t)] : IsDedekindDomain (Algebra.adjoin ℚ {t}) :=
  isDedekindDomain_adjoin Fact.out

/-- The element `t` is not a unit of the chart ring `A_t`. -/
theorem inv_notMem_chartRing (ht : Transcendental ℚ t) : t⁻¹ ∉ chartRing t := by
  have := isDedekindDomain_adjoin ht
  intro h
  have ht0 : t ≠ 0 := ne_zero_of_transcendental ht
  let y : ℚ⟮t⟯ := ⟨t⁻¹, inv_mem (IntermediateField.mem_adjoin_simple_self ℚ t)⟩
  have hy : IsIntegral (Algebra.adjoin ℚ {t}) y := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom (Algebra.adjoin ℚ {t}) ℚ⟮t⟯ K)
      (algebraMap ℚ⟮t⟯ K).injective]
    exact h
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hy
  have hr' : (r : K) = t⁻¹ := congrArg Subtype.val hr
  obtain ⟨p, hp⟩ : ∃ p : ℚ[X], aeval t p = r := by
    have : (r : K) ∈ (aeval (R := ℚ) t).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact r.2
    obtain ⟨p, hp⟩ := this
    exact ⟨p, hp⟩
  apply ht
  refine ⟨X * p - 1, fun h0 ↦ ?_, ?_⟩
  · have := congrArg (Polynomial.coeff · 0) h0
    simp at this
  · simp [hp, hr', ht0]

variable [IsCurveField K]

instance [Fact (Transcendental ℚ t)] : FiniteDimensional ℚ⟮t⟯ K :=
  finiteDimensional_adjoin Fact.out

instance [Fact (Transcendental ℚ t)] : IsFractionRing (chartRing t) K :=
  integralClosure.isFractionRing_of_finite_extension ℚ⟮t⟯ K

instance [Fact (Transcendental ℚ t)] : IsDedekindDomain (chartRing t) :=
  IsIntegralClosure.isDedekindDomain (Algebra.adjoin ℚ {t}) ℚ⟮t⟯ K (chartRing t)

instance [Fact (Transcendental ℚ t)] : Module.Finite (Algebra.adjoin ℚ {t}) (chartRing t) :=
  IsIntegralClosure.finite (Algebra.adjoin ℚ {t}) ℚ⟮t⟯ K (chartRing t)

instance [Fact (Transcendental ℚ t)] : Algebra.FiniteType ℚ (chartRing t) := by
  have : Algebra.FiniteType ℚ (Algebra.adjoin ℚ {t}) :=
    .adjoin_of_finite (Set.finite_singleton t)
  exact Algebra.FiniteType.trans (S := Algebra.adjoin ℚ {t}) inferInstance inferInstance

end Belyi.CurveField
