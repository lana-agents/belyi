/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.Divisor
import Belyi.CurveField.Extension
import Belyi.CurveDeriv.Order

/-!
# Ramification indices of a function and the order of `dt`

Let `K` be a curve field and `t ∈ K` transcendental over `ℚ`, i.e. a finite morphism
`t : X → ℙ¹`. For a place `P` of `K` the *ramification index* `e_t(P)` of `t` at `P`
(`Belyi.CurveField.ramIdx t P`) is the ramification index of `P` over the place of `ℚ(t)`
below it. Concretely:

* if `t ∈ O_P` and `m ∈ ℚ[X]` is the minimal polynomial of the residue `t(P)` of `t`, then
  `m(t)` is a uniformiser of the place of `ℚ(t)` below `P`, and `e_t(P) = ord_P (m(t))`;
* if `t ∉ O_P` (a pole of `t`), then `e_t(P) = -ord_P t`.

We take these formulas as the definition (`Belyi.CurveField.ramIdx_of_mem`,
`Belyi.CurveField.ramIdx_of_notMem`) and prove `0 < e_t(P)`.

Writing `π = π_P` for the chosen uniformiser of `P` and `d/dπ` for
`Belyi.CurveDeriv.derivAlong π`, the local computation of `Belyi/CurveDeriv/Order.lean` gives
the order of `dt = (dt/dπ) dπ` at `P`:

* `Belyi.CurveField.Place.ord_derivAlong_of_mem`: `ord_P (dt/dπ) = e_t(P) - 1` if `t ∈ O_P`;
* `Belyi.CurveField.Place.ord_derivAlong_of_notMem`: `ord_P (dt/dπ) = -e_t(P) - 1` at poles.

Finally, `t` is ramified at only finitely many places
(`Belyi.CurveField.finite_setOf_one_lt_ramIdx`): if `t ∈ O_P` and `e_t(P) > 1`, then
`d/dt` does not preserve `O_P`, which fails outside the (finitely many) poles of the images
under `d/dt` of a finite set of `ℚ`-algebra generators of the chart ring `A_t`.

## Main definitions and results

* `Belyi.CurveField.ramIdx t P : ℕ`, with `ramIdx_of_mem`, `ramIdx_of_notMem`, `ramIdx_pos`,
  `ramIdx_of_residue_eq` (`e_t(P) = ord_P (t - c)` if `t(P) = c ∈ ℚ`).
* `Belyi.CurveField.Place.ord_derivAlong_of_mem`, `ord_derivAlong_of_notMem`.
* `Belyi.CurveField.finite_setOf_one_lt_ramIdx`.
-/

open Polynomial IsLocalRing Belyi.CurveDeriv
open scoped IntermediateField

namespace Belyi.CurveField

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

namespace Place

variable (P : Place K)

/-! ### The valuation subring valuation versus `ord` -/

theorem valuation_eq_one_iff {x : K} (hx : x ≠ 0) : P.1.valuation x = 1 ↔ P.ord x = 0 := by
  rw [P.ord_eq_zero_iff hx, ← P.1.valuation_le_one_iff, ← P.1.valuation_le_one_iff, map_inv₀]
  constructor
  · intro h
    rw [h, inv_one]
    exact ⟨le_rfl, le_rfl⟩
  · rintro ⟨h1, h2⟩
    have h0 : P.1.valuation x ≠ 0 := by simpa using hx
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2)

theorem ord_eq_zero_of_valuation_eq_one' {x : K} (hx : P.1.valuation x = 1) : P.ord x = 0 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact zero_ne_one hx
  exact (P.valuation_eq_one_iff hx0).mp hx

theorem isUnit_iff_ord_eq_zero {a : P.1} (ha : (a : K) ≠ 0) : IsUnit a ↔ P.ord a = 0 := by
  rw [ValuationSubring.valuation_eq_one_iff, P.valuation_eq_one_iff ha]

/-! ### Residues of polynomial expressions -/

omit [IsCurveField K] in
theorem aeval_mem {x : K} (hx : x ∈ P.1) (p : ℚ[X]) : aeval x p ∈ P.1 :=
  CurveDeriv.aeval_mem P.algebraMap_mem hx p

omit [IsCurveField K] in
theorem residue_aeval {x : K} (hx : x ∈ P.1) (p : ℚ[X]) :
    P.residue ⟨aeval x p, P.aeval_mem hx p⟩ = aeval (P.residue ⟨x, hx⟩) p := by
  have h1 : (⟨aeval x p, P.aeval_mem hx p⟩ : P.1) = eval₂ P.ratHom ⟨x, hx⟩ p := by
    apply Subtype.ext
    change aeval x p = P.1.subtype (eval₂ P.ratHom ⟨x, hx⟩ p)
    rw [hom_eval₂, aeval_def]
    congr 1
  rw [h1, hom_eval₂, aeval_def]
  congr 1
  exact RingHom.ext_rat _ _

omit [IsCurveField K] in
/-- `aeval x p` lies in the maximal ideal iff `p` kills the residue of `x`. -/
theorem aeval_mem_nonunits_iff {x : K} (hx : x ∈ P.1) (p : ℚ[X]) :
    aeval x p ∈ P.1.nonunits ↔ aeval (P.residue ⟨x, hx⟩) p = 0 := by
  rw [← residue_aeval, residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]

/-- The minimal polynomial over `ℚ` of the residue of `x ∈ O_P`. -/
noncomputable def resMinpoly {x : K} (hx : x ∈ P.1) : ℚ[X] := minpoly ℚ (P.residue ⟨x, hx⟩)

theorem isIntegral_residue (a : P.1) : IsIntegral ℚ (P.residue a) :=
  Algebra.IsIntegral.isIntegral _

theorem resMinpoly_ne_zero {x : K} (hx : x ∈ P.1) : P.resMinpoly hx ≠ 0 :=
  minpoly.ne_zero (P.isIntegral_residue _)

theorem irreducible_resMinpoly {x : K} (hx : x ∈ P.1) : Irreducible (P.resMinpoly hx) :=
  minpoly.irreducible (P.isIntegral_residue _)

theorem separable_resMinpoly {x : K} (hx : x ∈ P.1) : (P.resMinpoly hx).Separable :=
  (P.irreducible_resMinpoly hx).separable

omit [IsCurveField K] in
theorem aeval_resMinpoly_mem_nonunits {x : K} (hx : x ∈ P.1) :
    aeval x (P.resMinpoly hx) ∈ P.1.nonunits :=
  (P.aeval_mem_nonunits_iff hx _).mpr (minpoly.aeval _ _)

/-- The residue field of a place is algebraic over `ℚ`, in the form used in
`Belyi/CurveDeriv/Local.lean`. -/
theorem exists_valuation_aeval_lt_one {x : K} (hx : x ∈ P.1) :
    ∃ p : ℚ[X], p ≠ 0 ∧ P.1.valuation (aeval x p) < 1 := by
  refine ⟨P.resMinpoly hx, P.resMinpoly_ne_zero hx, ?_⟩
  have := P.aeval_resMinpoly_mem_nonunits hx
  rw [ValuationSubring.mem_nonunits_iff] at this
  exact this

/-! ### The uniformiser -/

theorem transcendental_uniformizer : Transcendental ℚ P.uniformizer := fun h ↦ by
  have := P.ord_eq_zero_of_isAlgebraic h
  rw [ord_uniformizer] at this
  exact one_ne_zero this

theorem uniformizer_mem : P.uniformizer ∈ P.1 :=
  P.mem_of_ord_nonneg (by rw [ord_uniformizer]; exact zero_le_one)

theorem irreducible_uniformizer : Irreducible (⟨P.uniformizer, P.uniformizer_mem⟩ : P.1) := by
  refine ⟨fun h ↦ ?_, fun a b hab ↦ ?_⟩
  · have := (P.isUnit_iff_ord_eq_zero (a := ⟨P.uniformizer, P.uniformizer_mem⟩)
      P.uniformizer_ne_zero).mp h
    rw [ord_uniformizer] at this
    exact one_ne_zero this
  · have hab' : P.uniformizer = (a : K) * b := congrArg Subtype.val hab
    have ha0 : (a : K) ≠ 0 := fun h ↦ P.uniformizer_ne_zero (by rw [hab', h, zero_mul])
    have hb0 : (b : K) ≠ 0 := fun h ↦ P.uniformizer_ne_zero (by rw [hab', h, mul_zero])
    have hsum := P.ord_mul ha0 hb0
    rw [← hab', ord_uniformizer] at hsum
    have ha := P.ord_nonneg_of_mem a.2
    have hb := P.ord_nonneg_of_mem b.2
    rw [P.isUnit_iff_ord_eq_zero ha0, P.isUnit_iff_ord_eq_zero hb0]
    omega

instance finiteDimensional_adjoin_uniformizer : FiniteDimensional ℚ⟮P.uniformizer⟯ K :=
  finiteDimensional_adjoin P.transcendental_uniformizer

instance isAlgebraic_adjoin_uniformizer : Algebra.IsAlgebraic ℚ⟮P.uniformizer⟯ K :=
  isAlgebraic_adjoin P.transcendental_uniformizer

/-- `d/dπ_P` preserves `O_P`. -/
theorem derivAlong_uniformizer_mem {x : K} (hx : x ∈ P.1) :
    derivAlong P.uniformizer x ∈ P.1 :=
  derivAlong_mem P.1 P.transcendental_uniformizer P.algebraMap_mem
    (fun _ hy ↦ P.exists_valuation_aeval_lt_one hy) P.uniformizer_mem P.irreducible_uniformizer hx

/-- `u := x · π^(-ord x)` is a unit. -/
theorem valuation_mul_uniformizer_zpow {x : K} (hx : x ≠ 0) :
    P.1.valuation (x * P.uniformizer ^ (-P.ord x)) = 1 := by
  rw [P.valuation_eq_one_iff (mul_ne_zero hx (zpow_ne_zero _ P.uniformizer_ne_zero)),
    P.ord_mul hx (zpow_ne_zero _ P.uniformizer_ne_zero), ord_zpow, ord_uniformizer]
  ring

theorem eq_unit_mul_pow {x : K} {e : ℕ} (he : P.ord x = e) :
    x = x * P.uniformizer ^ (-P.ord x) * P.uniformizer ^ e := by
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ P.uniformizer_ne_zero, he, neg_add_cancel,
    zpow_zero, mul_one]

end Place

/-! ### The ramification index of a function -/

open Classical in
/-- The ramification index `e_t(P)` of a function `t` at a place `P`: the ramification index of
`P` over the place of `ℚ(t)` below it. If `t ∈ O_P`, it is `ord_P (m(t))` with `m` the minimal
polynomial of the residue of `t` (`m(t)` is a uniformiser of the place of `ℚ(t)` below `P`); if
`t ∉ O_P`, it is `-ord_P t`. (Junk value `0` for `t` algebraic over `ℚ`.) -/
noncomputable def ramIdx (t : K) (P : Place K) : ℕ :=
  if h : t ∈ P.1 then (P.ord (aeval t (P.resMinpoly h))).toNat else (-P.ord t).toNat

variable {t : K} {P : Place K}

theorem ramIdx_of_mem (h : t ∈ P.1) : (ramIdx t P : ℤ) = P.ord (aeval t (P.resMinpoly h)) := by
  rw [ramIdx, dif_pos h, Int.toNat_of_nonneg (P.ord_nonneg_of_mem (P.aeval_mem h _))]

theorem ramIdx_of_notMem (h : t ∉ P.1) : (ramIdx t P : ℤ) = -P.ord t := by
  rw [ramIdx, dif_neg h, Int.toNat_of_nonneg]
  have := (P.ord_neg_iff).mpr h
  omega

theorem aeval_resMinpoly_ne_zero (ht : Transcendental ℚ t) (h : t ∈ P.1) :
    aeval t (P.resMinpoly h) ≠ 0 :=
  fun h0 ↦ ht ⟨_, P.resMinpoly_ne_zero h, h0⟩

theorem ramIdx_pos (ht : Transcendental ℚ t) (P : Place K) : 0 < ramIdx t P := by
  by_cases h : t ∈ P.1
  · have := (P.ord_pos_iff).mpr ⟨aeval_resMinpoly_ne_zero ht h,
      P.aeval_resMinpoly_mem_nonunits h⟩
    rw [← ramIdx_of_mem h] at this
    exact_mod_cast this
  · have := (P.ord_neg_iff).mpr h
    have h2 := ramIdx_of_notMem h
    omega

/-- If the residue of `t` at `P` is a rational number `c`, then `e_t(P) = ord_P (t - c)`. -/
theorem ramIdx_of_residue_eq (h : t ∈ P.1) {c : ℚ}
    (hc : P.residue ⟨t, h⟩ = algebraMap ℚ P.ResidueField c) :
    (ramIdx t P : ℤ) = P.ord (t - algebraMap ℚ K c) := by
  rw [ramIdx_of_mem h, Place.resMinpoly, hc, minpoly.eq_X_sub_C]
  simp

/-- The residue of `t` is zero iff `t` has a zero at `P`. -/
theorem residue_eq_zero_iff_ord_pos (h : t ∈ P.1) (ht : t ≠ 0) :
    P.residue ⟨t, h⟩ = 0 ↔ 0 < P.ord t := by
  rw [Place.residue_eq_zero_iff, P.ord_pos_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  simp [ht]

/-! ### The order of `dt/dπ` -/

namespace Place

variable (P)

/-- At a place `P` with `t ∈ O_P`: `ord_P (dt/dπ_P) = e_t(P) - 1`. -/
theorem ord_derivAlong_of_mem (ht : Transcendental ℚ t) (h : t ∈ P.1) :
    P.ord (derivAlong P.uniformizer t) = ramIdx t P - 1 := by
  set e := ramIdx t P with he
  have he1 : 1 ≤ e := ramIdx_pos ht P
  have hm0 := aeval_resMinpoly_ne_zero ht h
  have hord : P.ord (aeval t (P.resMinpoly h)) = e := (ramIdx_of_mem h).symm
  obtain ⟨w, hw, hD⟩ := derivAlong_eq_unit_mul_pow_of_aeval P.transcendental_uniformizer
    P.algebraMap_mem (fun _ hy ↦ P.exists_valuation_aeval_lt_one hy) P.uniformizer_mem
    P.irreducible_uniformizer h (P.separable_resMinpoly h)
    (P.valuation_mul_uniformizer_zpow hm0) he1 (P.eq_unit_mul_pow hord)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [map_zero] at hw
    exact zero_ne_one hw
  rw [hD, P.ord_mul hw0 (pow_ne_zero _ P.uniformizer_ne_zero), ord_pow, ord_uniformizer,
    P.ord_eq_zero_of_valuation_eq_one' hw]
  push_cast [Nat.cast_sub he1]
  ring

/-- At a pole `P` of `t`: `ord_P (dt/dπ_P) = -e_t(P) - 1`. -/
theorem ord_derivAlong_of_notMem (h : t ∉ P.1) :
    P.ord (derivAlong P.uniformizer t) = -ramIdx t P - 1 := by
  have ht0 : t ≠ 0 := fun h0 ↦ h (h0 ▸ P.1.zero_mem)
  set e := ramIdx t P with he
  have hneg := (P.ord_neg_iff).mpr h
  have he' : (e : ℤ) = -P.ord t := ramIdx_of_notMem h
  have he1 : 1 ≤ e := by omega
  have hord : P.ord t⁻¹ = e := by rw [ord_inv, he']
  obtain ⟨w, hw, hD⟩ := derivAlong_eq_unit_mul_zpow_of_inv P.transcendental_uniformizer
    P.algebraMap_mem (fun _ hy ↦ P.exists_valuation_aeval_lt_one hy) P.uniformizer_mem
    P.irreducible_uniformizer (P.valuation_mul_uniformizer_zpow (inv_ne_zero ht0)) he1
    (P.eq_unit_mul_pow hord)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [map_zero] at hw
    exact zero_ne_one hw
  rw [hD, P.ord_mul hw0 (zpow_ne_zero _ P.uniformizer_ne_zero), ord_zpow, ord_uniformizer,
    P.ord_eq_zero_of_valuation_eq_one' hw]
  ring

/-- `dt/dπ_P ≠ 0` for `t` transcendental. -/
theorem derivAlong_uniformizer_ne_zero (ht : Transcendental ℚ t) :
    derivAlong P.uniformizer t ≠ 0 := by
  have := isAlgebraic_adjoin ht
  intro h0
  have h1 := derivAlong_mul_derivAlong P.transcendental_uniformizer ht
  rw [h0, mul_zero] at h1
  exact zero_ne_one h1

end Place

/-! ### Finiteness of ramification -/

/-- If `t ∈ O_P` is ramified at `P`, then `d/dt` does not preserve `O_P`: `dπ_P/dt ∉ O_P`. -/
theorem derivAlong_uniformizer_notMem (ht : Transcendental ℚ t) (h : t ∈ P.1)
    (h1 : 1 < ramIdx t P) : derivAlong t P.uniformizer ∉ P.1 := by
  have := isAlgebraic_adjoin ht
  intro hmem
  have hprod := derivAlong_mul_derivAlong P.transcendental_uniformizer ht
  have h0 : derivAlong t P.uniformizer ≠ 0 := fun h0 ↦ by
    rw [h0, zero_mul] at hprod
    exact zero_ne_one hprod
  have hord := congrArg P.ord hprod
  rw [P.ord_mul h0 (P.derivAlong_uniformizer_ne_zero ht), Place.ord_one,
    P.ord_derivAlong_of_mem ht h] at hord
  have := P.ord_nonneg_of_mem hmem
  have h1' : (1 : ℤ) < ramIdx t P := by exact_mod_cast h1
  omega

/-- **Finiteness of ramification**: a transcendental `t` is ramified (`e_t(P) > 1`) at only
finitely many places. -/
theorem finite_setOf_one_lt_ramIdx (ht : Transcendental ℚ t) :
    {P : Place K | 1 < ramIdx t P}.Finite := by
  have : Fact (Transcendental ℚ t) := ⟨ht⟩
  have := isAlgebraic_adjoin ht
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℚ (chartRing t)).FG)
  have hfin : ({P : Place K | t ∉ P.1} ∪
      ⋃ b ∈ s, {P : Place K | derivAlong t (b : K) ∉ P.1}).Finite :=
    (Place.finite_setOf_notMem t).union
      (s.finite_toSet.biUnion fun b _ ↦ Place.finite_setOf_notMem _)
  refine hfin.subset fun P hP ↦ ?_
  by_contra hPn
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists,
    not_not] at hPn
  obtain ⟨htP, hgen⟩ := hPn
  -- `d/dt` maps `A_t` into `O_P`
  have hA : ∀ a : chartRing t, derivAlong t (a : K) ∈ P.1 := by
    intro a
    have ha : a ∈ Algebra.adjoin ℚ (s : Set (chartRing t)) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact hgen x hx
    | algebraMap q =>
      have : ((algebraMap ℚ (chartRing t) q : chartRing t) : K) = algebraMap ℚ K q := rfl
      rw [this, derivAlong_algebraMap]
      exact P.1.zero_mem
    | add x y _ _ hx hy =>
      rw [Subalgebra.coe_add, map_add]
      exact add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [Subalgebra.coe_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact add_mem (mul_mem (P.algebraMap_chartRing_mem t htP x) hy)
        (mul_mem (P.algebraMap_chartRing_mem t htP y) hx)
  -- `d/dt` maps `O_P` into `O_P`
  have hO : ∀ x ∈ P.1, derivAlong t x ∈ P.1 := by
    intro x hx
    have hx' : x ∈ (Place.ofChart t (P.toChart t htP)).1 := by
      rw [Place.ofChart_toChart]; exact hx
    rw [Place.ofChart_val] at hx'
    obtain ⟨a, b, hb, rfl⟩ := hx'
    have hbu : (algebraMap (chartRing t) K b)⁻¹ ∈ P.1 := by
      have hbn : algebraMap (chartRing t) K b ∉ P.1.nonunits := by
        exact fun h ↦ hb ((Place.mem_toChart_iff t P htP).mpr h)
      rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hbn
      exact hbn.2
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    refine add_mem (mul_mem (P.algebraMap_chartRing_mem t htP a) ?_) (mul_mem hbu (hA a))
    rw [Derivation.leibniz_inv, smul_eq_mul]
    exact mul_mem (neg_mem (pow_mem hbu 2)) (hA b)
  exact derivAlong_uniformizer_notMem ht htP hP (hO _ P.uniformizer_mem)

end Belyi.CurveField
