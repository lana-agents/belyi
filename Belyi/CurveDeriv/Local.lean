/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveDeriv.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# `d/dπ` preserves the valuation ring of a place with uniformiser `π`

Let `K` be a field of characteristic zero, `π : K` transcendental over `ℚ` with `K` finite
over `ℚ⟮π⟯`, and let `O` be a discrete valuation subring of `K` containing `ℚ`, with
uniformiser `π` and residue field algebraic over `ℚ`.  We prove
(`Belyi.CurveDeriv.derivAlong_mem`) that `derivAlong π` maps `O` into `O`.

## Strategy

The proof is elementary modulo the finiteness of integral closures:

* **A uniform bound** (`exists_pow_mul_derivAlong_mem`): there is `N` with
  `π ^ N * (d/dπ) x ∈ O` for all `x ∈ O`.  Let `B` be the integral closure of `ℚ[π]` in `K`;
  it is a finite `ℚ[π]`-module (`IsIntegralClosure.finite`) and a Dedekind domain.  Since
  `d/dπ` maps `ℚ[π]` into itself, a finite set of generators of `B` gives the bound on `B`.
  Moreover every `x ∈ O` is a quotient `b / s` with `b, s ∈ B` and `s` a unit of `O`, because
  the localisation of `B` at `𝔭 = B ∩ 𝔪_O` is a discrete valuation ring, hence a valuation
  ring (`exists_eq_div`); the quotient rule extends the bound to `O`.
* **An ascent** (`exists_pow_succ_mul_derivAlong_not_mem`): if `π ^ k * (d/dπ) x ∉ O` for some
  `x ∈ O`, choose a separable `q ∈ ℚ[X]` with `q(x) ∈ 𝔪_O` (the residue of `x` is algebraic);
  then `q'(x)` is a unit, `q(x) = π g` with `g ∈ O`, and `q'(x) (d/dπ) x = g + π (d/dπ) g`
  forces `π ^ (k + 1) * (d/dπ) g ∉ O`.

Iterating the ascent contradicts the uniform bound.

The residue field hypothesis is phrased without residue fields: every `x ∈ O` is a root of a
nonzero rational polynomial modulo the maximal ideal (`O.valuation (aeval x p) < 1`).
-/

open Polynomial IntermediateField
open scoped IntermediateField

namespace Belyi.CurveDeriv

variable {K : Type*} [Field K] [CharZero K] (O : ValuationSubring K)

/-! ### Elementary facts about `O` -/

section Elementary

variable {O}

theorem aeval_mem (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) {x : K} (hx : x ∈ O) (p : ℚ[X]) :
    aeval x p ∈ O := by
  rw [aeval_eq_sum_range]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def]
  exact mul_mem (hQ _) (pow_mem hx _)

theorem valuation_algebraMap_rat (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) {q : ℚ} (hq : q ≠ 0) :
    O.valuation (algebraMap ℚ K q) = 1 := by
  have h1 := (O.valuation_le_one_iff _).mpr (hQ q)
  have h2 := (O.valuation_le_one_iff _).mpr (hQ q⁻¹)
  rw [map_inv₀, map_inv₀] at h2
  have h0 : O.valuation (algebraMap ℚ K q) ≠ 0 := by simpa using hq
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2)

omit [CharZero K] in
theorem inv_mem_of_valuation_eq_one {u : K} (hu : O.valuation u = 1) : u⁻¹ ∈ O := by
  rw [← O.valuation_le_one_iff, map_inv₀, hu, inv_one]

/-- If some nonzero rational polynomial vanishes at `x ∈ O` modulo `𝔪_O`, so does an irreducible
one. -/
theorem exists_irreducible_valuation_lt_one (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) {x : K}
    (hx : x ∈ O) {p : ℚ[X]} (hp : p ≠ 0) (hv : O.valuation (aeval x p) < 1) :
    ∃ q : ℚ[X], Irreducible q ∧ O.valuation (aeval x q) < 1 := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => exact absurd rfl hp
  | unit u hu =>
    obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp hu
    rw [aeval_C, valuation_algebraMap_rat hQ hc.ne_zero] at hv
    exact absurd hv (lt_irrefl 1)
  | mul a i ha hi ih =>
    rw [map_mul, map_mul] at hv
    rcases (O.valuation_le_one_iff _).mpr (aeval_mem hQ hx i) |>.lt_or_eq with h | h
    · exact ⟨i, hi, h⟩
    · rw [h, one_mul] at hv
      exact ih ha hv

/-- If `q` is separable and `q(x) ∈ 𝔪_O` then `q'(x)` is a unit of `O`. -/
theorem valuation_aeval_derivative_eq_one (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) {x : K}
    (hx : x ∈ O) {q : ℚ[X]} (hq : q.Separable) (hv : O.valuation (aeval x q) < 1) :
    O.valuation (aeval x (derivative q)) = 1 := by
  obtain ⟨a, b, hab⟩ := hq
  have h : aeval x a * aeval x q + aeval x b * aeval x (derivative q) = 1 := by
    simpa using congrArg (aeval x) hab
  refine ((O.valuation_le_one_iff _).mpr (aeval_mem hQ hx _)).antisymm (not_lt.mp fun hlt => ?_)
  have h1 : O.valuation (aeval x a * aeval x q) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((O.valuation_le_one_iff _).mpr
      (aeval_mem hQ hx _))) hv
  have h2 : O.valuation (aeval x b * aeval x (derivative q)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((O.valuation_le_one_iff _).mpr
      (aeval_mem hQ hx _))) hlt
  have := O.valuation.map_add_lt h1 h2
  rw [h, map_one] at this
  exact lt_irrefl _ this

variable [IsDiscreteValuationRing O] {π : K} (hπO : π ∈ O)
  (hirr : Irreducible (⟨π, hπO⟩ : O))
include hirr

omit [CharZero K] [IsDiscreteValuationRing O] in
theorem ne_zero_of_irreducible : π ≠ 0 := fun h =>
  hirr.ne_zero (Subtype.ext h)

omit [CharZero K] in
theorem valuation_lt_one_of_irreducible : O.valuation π < 1 := by
  have := (O.valuation_lt_one_iff ⟨π, hπO⟩).mp
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirr ▸
      Ideal.mem_span_singleton_self _)
  simpa using this

omit [CharZero K] in
/-- Division by the uniformiser. -/
theorem mul_inv_mem_of_valuation_lt_one {y : K} (hy : y ∈ O) (hv : O.valuation y < 1) :
    y * π⁻¹ ∈ O := by
  have hm : (⟨y, hy⟩ : O) ∈ IsLocalRing.maximalIdeal O := (O.valuation_lt_one_iff _).mpr hv
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirr,
    Ideal.mem_span_singleton'] at hm
  obtain ⟨g, hg⟩ := hm
  have hg' : (g : K) * π = y := congrArg Subtype.val hg
  rw [← hg', mul_assoc, mul_inv_cancel₀ (ne_zero_of_irreducible hπO hirr), mul_one]
  exact g.2

omit [CharZero K] in
/-- Every element of `K` becomes integral after multiplication by a power of `π`. -/
theorem exists_pow_mul_mem (y : K) : ∃ n : ℕ, π ^ n * y ∈ O := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, by simp⟩
  by_cases hyO : y ∈ O
  · exact ⟨0, by simpa using hyO⟩
  have hyi : y⁻¹ ∈ O := (O.mem_or_inv_mem y).resolve_left hyO
  have hne : (⟨y⁻¹, hyi⟩ : O) ≠ 0 := fun h => hy (inv_eq_zero.mp (congrArg Subtype.val h))
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hirr
  refine ⟨n, ?_⟩
  have hu' : y⁻¹ = (u : O) * π ^ n := congrArg Subtype.val hu
  have hinv : (((u⁻¹ : Oˣ) : O) : K) * ((u : O) : K) = 1 := by
    exact_mod_cast congrArg Subtype.val u.inv_mul
  have hπ0 := ne_zero_of_irreducible hπO hirr
  have hy' : y = ((u : O) : K)⁻¹ * (π ^ n)⁻¹ := by rw [← mul_inv, ← hu', inv_inv]
  have : π ^ n * y = ((u⁻¹ : Oˣ) : O) := by
    rw [hy', eq_inv_of_mul_eq_one_left hinv]
    field_simp
  rw [this]
  exact SetLike.coe_mem _

end Elementary

/-! ### The ascent -/

section Ascent

variable {O} {π : K} (ht : Transcendental ℚ π) [Algebra.IsAlgebraic ℚ⟮π⟯ K]
  (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O)
  (hres : ∀ x ∈ O, ∃ p : ℚ[X], p ≠ 0 ∧ O.valuation (aeval x p) < 1)
  [IsDiscreteValuationRing O] (hπO : π ∈ O) (hirr : Irreducible (⟨π, hπO⟩ : O))
include ht hQ hres hirr

/-- The ascent: if `π ^ k * (d/dπ) x ∉ O` for some `x ∈ O`, then
`π ^ (k + 1) * (d/dπ) y ∉ O` for some `y ∈ O`. -/
theorem exists_pow_succ_mul_derivAlong_not_mem {k : ℕ} {x : K} (hx : x ∈ O)
    (hk : π ^ k * derivAlong π x ∉ O) : ∃ y ∈ O, π ^ (k + 1) * derivAlong π y ∉ O := by
  obtain ⟨p, hp0, hp⟩ := hres x hx
  obtain ⟨q, hq, hqv⟩ := exists_irreducible_valuation_lt_one hQ hx hp0 hp
  have hq' := valuation_aeval_derivative_eq_one hQ hx hq.separable hqv
  have hgO : aeval x q * π⁻¹ ∈ O :=
    mul_inv_mem_of_valuation_lt_one hπO hirr (aeval_mem hQ hx q) hqv
  refine ⟨aeval x q * π⁻¹, hgO, fun hmem => hk ?_⟩
  have hπ0 := ne_zero_of_irreducible hπO hirr
  set g := aeval x q * π⁻¹ with hg
  have hqx : aeval x q = π * g := by rw [hg]; field_simp
  have hD : aeval x (derivative q) * derivAlong π x = g + π * derivAlong π g := by
    have := (derivAlong π).map_aeval q x
    rw [smul_eq_mul] at this
    rw [← this, hqx, Derivation.leibniz, derivAlong_self ht, smul_eq_mul, smul_eq_mul]
    ring
  have hne : aeval x (derivative q) ≠ 0 := by
    intro h
    rw [h, map_zero] at hq'
    exact zero_ne_one hq'
  have : π ^ k * derivAlong π x =
      (aeval x (derivative q))⁻¹ * (π ^ k * g + π ^ (k + 1) * derivAlong π g) := by
    rw [eq_inv_mul_iff_mul_eq₀ hne]
    linear_combination (π ^ k) * hD
  rw [this]
  exact mul_mem (inv_mem_of_valuation_eq_one hq') (add_mem (mul_mem (pow_mem hπO k) hgO) hmem)

end Ascent

/-! ### The uniform bound -/

section Bound

open scoped IntermediateField.algebraAdjoinAdjoin

variable {O} {π : K}

set_option quotPrecheck false in
/-- The integral closure of `ℚ[π]` in `K`. -/
local notation "𝓑" => integralClosure (Algebra.adjoin ℚ ({π} : Set K)) K

theorem mem_of_mem_adjoin (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) (hπO : π ∈ O) {x : K}
    (hx : x ∈ Algebra.adjoin ℚ {π}) : x ∈ O := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨p, rfl⟩ := hx
  exact aeval_mem hQ hπO p

theorem mem_of_isIntegral (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) (hπO : π ∈ O) {x : K}
    (hx : IsIntegral (Algebra.adjoin ℚ {π}) x) : x ∈ O := by
  let f : Algebra.adjoin ℚ {π} →+* O :=
    ((Algebra.adjoin ℚ {π}).val.toRingHom).codRestrict O
      (fun a => mem_of_mem_adjoin hQ hπO a.2)
  letI : Algebra (Algebra.adjoin ℚ {π}) O := f.toAlgebra
  haveI : IsScalarTower (Algebra.adjoin ℚ {π}) O K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A := O))
  rw [← hy]
  exact y.2

theorem isPrincipalIdealRing_adjoin (ht : Transcendental ℚ π) :
    IsPrincipalIdealRing (Algebra.adjoin ℚ {π}) :=
  IsPrincipalIdealRing.of_surjective
    ((Polynomial.algEquivOfTranscendental ℚ π ht : ℚ[X] ≃ₐ[ℚ] _) : ℚ[X] →+* _)
    (Polynomial.algEquivOfTranscendental ℚ π ht).surjective

variable (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
  (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O) (hπO : π ∈ O)
include ht hQ hπO

/-- Every element of `O` is a quotient `b / s` with `b, s` integral over `ℚ[π]` and `s` a unit
of `O`. -/
theorem exists_eq_div (hπ1 : O.valuation π < 1) {x : K} (hx : x ∈ O) :
    ∃ b s : 𝓑, O.valuation (s : K) = 1 ∧ x = b / s := by
  haveI := isPrincipalIdealRing_adjoin ht
  haveI : IsDedekindDomain 𝓑 :=
    IsIntegralClosure.isDedekindDomain (Algebra.adjoin ℚ {π}) ℚ⟮π⟯ K 𝓑
  haveI : IsFractionRing 𝓑 K :=
    IsIntegralClosure.isFractionRing_of_finite_extension (Algebra.adjoin ℚ {π}) ℚ⟮π⟯ K 𝓑
  have hBO : ∀ b : 𝓑, (b : K) ∈ O := fun b => mem_of_isIntegral hQ hπO b.2
  let fB : 𝓑 →+* O := ((integralClosure (Algebra.adjoin ℚ {π}) K).val.toRingHom).codRestrict O
    (fun b => hBO b)
  let 𝔭 : Ideal 𝓑 := Ideal.comap fB (IsLocalRing.maximalIdeal O)
  have hmem : ∀ b : 𝓑, b ∈ 𝔭 ↔ O.valuation (b : K) < 1 := fun b =>
    O.valuation_lt_one_iff (fB b)
  have hle : ∀ b : 𝓑, O.valuation (b : K) ≤ 1 := fun b => (O.valuation_le_one_iff _).mpr (hBO b)
  -- `𝔭` is a nonzero prime: it contains `π`
  have hπB : IsIntegral (Algebra.adjoin ℚ {π}) π :=
    isIntegral_algebraMap (x := (⟨π, Algebra.self_mem_adjoin_singleton ℚ π⟩ :
      Algebra.adjoin ℚ {π}))
  have hπ0 : π ≠ 0 := fun h => ht (h ▸ isAlgebraic_zero)
  have h𝔭 : 𝔭 ≠ ⊥ := by
    intro h
    have : (⟨π, hπB⟩ : 𝓑) ∈ 𝔭 := (hmem _).mpr hπ1
    rw [h, Ideal.mem_bot] at this
    exact hπ0 (congrArg Subtype.val this)
  let Loc := Localization.AtPrime 𝔭
  haveI : IsDiscreteValuationRing Loc :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain 𝓑 h𝔭 Loc
  have hinj : Function.Injective (algebraMap 𝓑 Loc) :=
    IsLocalization.injective Loc (Ideal.primeCompl_le_nonZeroDivisors 𝔭)
  obtain ⟨b, c, hc, hbc⟩ := IsFractionRing.div_surjective (A := 𝓑) x
  change (b : K) / (c : K) = x at hbc
  have hc0 : (c : K) ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero hc (Subtype.ext h)
  have hunit : ∀ s : 𝓑, s ∉ 𝔭 → O.valuation (s : K) = 1 := fun s hs =>
    (hle s).antisymm (not_lt.mp fun h => hs ((hmem s).mpr h))
  have hne0 : ∀ s : 𝓑, s ∉ 𝔭 → (s : K) ≠ 0 := fun s hs h => by
    have := hunit s hs
    rw [h, map_zero] at this
    exact zero_ne_one this
  obtain ⟨z, hz⟩ := ValuationRing.cond (algebraMap 𝓑 Loc b) (algebraMap 𝓑 Loc c)
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl z
  simp only [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul,
    ← map_mul] at hz
  have hs := hne0 s s.2
  rcases hz with hz | hz
  · -- `b * r = c * s`
    have hz' : (b : K) * r = c * s := by exact_mod_cast congrArg Subtype.val (hinj hz)
    by_cases hr : r ∈ 𝔭
    · refine absurd ((hmem s).mpr ?_) s.2
      have : (s : K) = x * r := by
        rw [← hbc]; field_simp; linear_combination -hz'
      rw [this, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ((O.valuation_le_one_iff _).mpr hx))
        ((hmem r).mp hr)
    · refine ⟨s, r, hunit r hr, ?_⟩
      rw [← hbc, div_eq_div_iff hc0 (hne0 r hr)]
      linear_combination hz'
  · -- `c * r = b * s`
    have hz' : (c : K) * r = b * s := by exact_mod_cast congrArg Subtype.val (hinj hz)
    refine ⟨r, s, hunit s s.2, ?_⟩
    rw [← hbc, div_eq_div_iff hc0 hs]
    linear_combination -hz'

/-- `d/dπ` maps `ℚ[π]` into `O`. -/
theorem derivAlong_mem_of_mem_adjoin {a : K} (ha : a ∈ Algebra.adjoin ℚ {π}) :
    derivAlong π a ∈ O := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨p, rfl⟩ := ha
  change derivAlong π (aeval π p) ∈ O
  rw [derivAlong_aeval ht]
  exact aeval_mem hQ hπO _

variable [IsDiscreteValuationRing O] (hirr : Irreducible (⟨π, hπO⟩ : O))
include hirr

/-- The uniform bound on the integral closure `B` of `ℚ[π]`. -/
theorem exists_pow_mul_derivAlong_mem_integralClosure :
    ∃ N : ℕ, ∀ b : 𝓑, π ^ N * derivAlong π b ∈ O := by
  haveI := isPrincipalIdealRing_adjoin ht
  haveI : Module.Finite (Algebra.adjoin ℚ {π}) 𝓑 :=
    IsIntegralClosure.finite (Algebra.adjoin ℚ {π}) ℚ⟮π⟯ K 𝓑
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := Algebra.adjoin ℚ {π}) (M := 𝓑)
  choose n hn using fun i : 𝓑 => exists_pow_mul_mem hπO hirr (derivAlong π (i : K))
  refine ⟨S.sup n, fun b => ?_⟩
  have hb : b ∈ Submodule.span (Algebra.adjoin ℚ {π}) (S : Set 𝓑) := hS ▸ Submodule.mem_top
  have hBO : ∀ b : 𝓑, (b : K) ∈ O := fun b => mem_of_isIntegral hQ hπO b.2
  induction hb using Submodule.span_induction with
  | mem i hi =>
    have : π ^ S.sup n = π ^ (S.sup n - n i) * π ^ n i := by
      rw [← pow_add, Nat.sub_add_cancel (Finset.le_sup (f := n) hi)]
    rw [this, mul_assoc]
    exact mul_mem (pow_mem hπO _) (hn i)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subalgebra.coe_add, map_add, mul_add]
    exact add_mem hx hy
  | smul a x _ hx =>
    have hax : ((a • x : 𝓑) : K) = (a : K) * x := by
      rw [Subalgebra.coe_smul, Algebra.smul_def]; rfl
    rw [hax, Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add]
    refine add_mem ?_ ?_
    · rw [mul_left_comm]
      exact mul_mem (mem_of_mem_adjoin hQ hπO a.2) hx
    · rw [← mul_assoc]
      exact mul_mem (mul_mem (pow_mem hπO _) (hBO x))
        (derivAlong_mem_of_mem_adjoin ht hQ hπO a.2)

/-- The uniform bound: some fixed power of `π` times `d/dπ` maps `O` into `O`. -/
theorem exists_pow_mul_derivAlong_mem :
    ∃ N : ℕ, ∀ x ∈ O, π ^ N * derivAlong π x ∈ O := by
  obtain ⟨N, hN⟩ := exists_pow_mul_derivAlong_mem_integralClosure ht hQ hπO hirr
  refine ⟨N, fun x hx => ?_⟩
  obtain ⟨b, s, hs, rfl⟩ :=
    exists_eq_div ht hQ hπO (valuation_lt_one_of_irreducible hπO hirr) hx
  have hBO : ∀ b : 𝓑, (b : K) ∈ O := fun b => mem_of_isIntegral hQ hπO b.2
  rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  have : π ^ N * ((s : K)⁻¹ ^ 2 * ((s : K) * derivAlong π b - b * derivAlong π s)) =
      (s : K)⁻¹ ^ 2 * ((s : K) * (π ^ N * derivAlong π b) - b * (π ^ N * derivAlong π s)) := by
    ring
  rw [this]
  exact mul_mem (pow_mem (inv_mem_of_valuation_eq_one hs) 2)
    (sub_mem (mul_mem (hBO s) (hN b)) (mul_mem (hBO b) (hN s)))

end Bound

/-! ### The main theorem -/

/-- **`d/dπ` preserves `O`.**  Let `π : K` be transcendental over `ℚ` with `K` finite over
`ℚ⟮π⟯`, and let `O` be a discrete valuation subring of `K` containing `ℚ`, with uniformiser `π`
and residue field algebraic over `ℚ` (every `x ∈ O` is a root of a nonzero rational polynomial
modulo `𝔪_O`).  Then `derivAlong π` maps `O` into `O`. -/
theorem derivAlong_mem {π : K} (ht : Transcendental ℚ π) [FiniteDimensional ℚ⟮π⟯ K]
    (hQ : ∀ q : ℚ, algebraMap ℚ K q ∈ O)
    (hres : ∀ x ∈ O, ∃ p : ℚ[X], p ≠ 0 ∧ O.valuation (aeval x p) < 1)
    [IsDiscreteValuationRing O] (hπO : π ∈ O) (hirr : Irreducible (⟨π, hπO⟩ : O))
    {x : K} (hx : x ∈ O) : derivAlong π x ∈ O := by
  by_contra h
  obtain ⟨N, hN⟩ := exists_pow_mul_derivAlong_mem ht hQ hπO hirr
  have key : ∀ k : ℕ, ∃ y ∈ O, π ^ k * derivAlong π y ∉ O := by
    intro k
    induction k with
    | zero => exact ⟨x, hx, by simpa using h⟩
    | succ k ih =>
      obtain ⟨y, hy, hk⟩ := ih
      exact exists_pow_succ_mul_derivAlong_not_mem ht hQ hres hπO hirr hy hk
  obtain ⟨y, hy, hN'⟩ := key N
  exact hN' (hN y hy)

end Belyi.CurveDeriv
