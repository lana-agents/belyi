/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.Rational

/-!
# The tripod `ℙ¹ ∖ {0, 1, ∞}`

Let `t` be a rational generator of `K` (`K = ℚ(t)`, `Belyi.CurveField.IsRationalGenerator`).
The *tripod* is the complement in `ℙ¹` of the three places `t = 0`, `t = 1`, `t = ∞`
(`Belyi.CurveField.tripodPlaces t`). Each of these places has degree one, and `t` (resp.
`t - 1`) has a simple zero at `t = 0` (resp. `t = 1`) and a simple pole at `∞`.

The algebraic points of the tripod correspond to `ℚ̄ ∖ {0, 1}` via `x ↦ t(x)`
(`Belyi.CurveField.QbarPoint.equivTripod`), and its coordinate ring, the ring of functions
regular away from the three places, is `ℚ[t, t⁻¹, (1 - t)⁻¹]`
(`Belyi.CurveField.forall_mem_iff_mem_adjoin_tripod`).

## Main definitions and results

* `Belyi.CurveField.zeroPlace t`, `Belyi.CurveField.onePlace t`: the places `t = 0`, `t = 1`
  (`Belyi.CurveField.eq_zeroPlace_iff`, `Belyi.CurveField.eq_onePlace_iff`).
* `Belyi.CurveField.tripodPlaces t : Finset (Place K)`, of cardinality `3`;
  `Belyi.CurveField.mem_tripodPlaces_iff_ord`: `P` is one of them iff
  `ord_P t ≠ 0 ∨ ord_P (t - 1) > 0`; `Belyi.CurveField.notMem_tripodPlaces_iff`: `P` is not
  one of them iff `t, t⁻¹, (1 - t)⁻¹ ∈ O_P`; `Belyi.CurveField.deg_of_mem_tripodPlaces`.
* `Belyi.CurveField.ord_self`: the divisor of `t` is `[0] - [∞]`.
* `Belyi.CurveField.QbarPoint.P_mem_tripodPlaces_iff`, `Belyi.CurveField.QbarPoint.equivTripod`.
* `Belyi.CurveField.setOf_forall_mem_eq_adjoin_tripod`: the coordinate ring of the tripod.
-/

open Polynomial
open scoped IntermediateField

local notation "Qbar" => AlgebraicClosure ℚ

namespace Belyi.CurveField

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-- The place `t = 0`. -/
noncomputable def zeroPlace (t : K) : Place K := infPlace t⁻¹

/-- The place `t = 1`. -/
noncomputable def onePlace (t : K) : Place K := infPlace (t - 1)⁻¹

open Classical in
/-- The three places `t = 0`, `t = 1`, `t = ∞` removed from `ℙ¹` to form the tripod. -/
noncomputable def tripodPlaces (t : K) : Finset (Place K) :=
  {zeroPlace t, onePlace t, infPlace t}

theorem mem_tripodPlaces {t : K} {P : Place K} :
    P ∈ tripodPlaces t ↔ P = zeroPlace t ∨ P = onePlace t ∨ P = infPlace t := by
  simp [tripodPlaces]

variable {t : K} (ht : IsRationalGenerator t)
include ht

/-! ### The places `t = 0` and `t = 1` -/

theorem eq_zeroPlace_iff {P : Place K} : P = zeroPlace t ↔ 0 < P.ord t := by
  rw [zeroPlace, eq_infPlace_iff_ord_neg ht.inv, Place.ord_inv, Left.neg_neg_iff]

/-- `t` has a simple zero at `t = 0`. -/
theorem ord_zeroPlace : (zeroPlace t).ord t = 1 := by
  have := ord_infPlace ht.inv
  rw [Place.ord_inv] at this
  change (infPlace t⁻¹).ord t = 1
  omega

theorem deg_zeroPlace : (zeroPlace t).deg = 1 := deg_infPlace ht.inv

theorem eq_onePlace_iff {P : Place K} : P = onePlace t ↔ 0 < P.ord (t - 1) := by
  rw [onePlace, eq_infPlace_iff_ord_neg ht.sub_one.inv, Place.ord_inv, Left.neg_neg_iff]

/-- `t - 1` has a simple zero at `t = 1`. -/
theorem ord_onePlace : (onePlace t).ord (t - 1) = 1 := by
  have := ord_infPlace ht.sub_one.inv
  rw [Place.ord_inv] at this
  change (infPlace (t - 1)⁻¹).ord (t - 1) = 1
  omega

theorem deg_onePlace : (onePlace t).deg = 1 := deg_infPlace ht.sub_one.inv

omit ht in
/-- `t` and `t - 1` have no common zero. -/
theorem not_ord_pos_and_ord_sub_one_pos (P : Place K) :
    ¬ (0 < P.ord t ∧ 0 < P.ord (t - 1)) := by
  rintro ⟨h1, h2⟩
  have h : t + -(t - 1) = 1 := by ring
  have := P.min_le_ord_add (f := t) (g := -(t - 1)) (by rw [h]; exact one_ne_zero)
  rw [Place.ord_neg, h, Place.ord_one] at this
  omega

theorem ord_onePlace_self : (onePlace t).ord t = 0 := by
  have h1 := ord_onePlace ht
  have hmem : t ∈ (onePlace t).1 := by
    have : t - 1 ∈ (onePlace t).1 := (onePlace t).mem_of_ord_nonneg (by omega)
    simpa using add_mem this (onePlace t).1.one_mem
  have h0 := (onePlace t).ord_nonneg_of_mem hmem
  have := not_ord_pos_and_ord_sub_one_pos (t := t) (onePlace t)
  omega

theorem ord_infPlace_sub_one : (infPlace t).ord (t - 1) = -1 := by
  have h : infPlace t = infPlace (t - 1) := by
    rw [eq_infPlace_iff ht.sub_one]
    intro hm
    exact notMem_infPlace ht (by simpa using add_mem hm (infPlace t).1.one_mem)
  rw [h, ord_infPlace ht.sub_one]

theorem zeroPlace_ne_onePlace : zeroPlace t ≠ onePlace t := fun h ↦ by
  have := ord_zeroPlace ht
  rw [h, ord_onePlace_self ht] at this
  exact zero_ne_one this

theorem zeroPlace_ne_infPlace : zeroPlace t ≠ infPlace t := fun h ↦ by
  have := ord_zeroPlace ht
  rw [h, ord_infPlace ht] at this
  omega

theorem onePlace_ne_infPlace : onePlace t ≠ infPlace t := fun h ↦ by
  have := ord_onePlace_self ht
  rw [h, ord_infPlace ht] at this
  omega

open Classical in
/-- The divisor of `t` is `[t = 0] - [t = ∞]`. -/
theorem ord_self (P : Place K) :
    P.ord t = if P = zeroPlace t then 1 else if P = infPlace t then -1 else 0 := by
  split_ifs with h0 hinf
  · rw [h0, ord_zeroPlace ht]
  · rw [hinf, ord_infPlace ht]
  · rw [eq_zeroPlace_iff ht] at h0
    rw [eq_infPlace_iff_ord_neg ht] at hinf
    omega

open Classical in
/-- The divisor of `t - 1` is `[t = 1] - [t = ∞]`. -/
theorem ord_sub_one (P : Place K) :
    P.ord (t - 1) = if P = onePlace t then 1 else if P = infPlace t then -1 else 0 := by
  split_ifs with h1 hinf
  · rw [h1, ord_onePlace ht]
  · rw [hinf, ord_infPlace_sub_one ht]
  · rw [eq_onePlace_iff ht] at h1
    have ht1 : t - 1 ∈ P.1 := sub_mem (mem_of_ne_infPlace ht hinf) P.1.one_mem
    have := P.ord_nonneg_of_mem ht1
    omega

/-! ### The three places -/

open Classical in
theorem card_tripodPlaces : (tripodPlaces t).card = 3 := by
  have h1 := zeroPlace_ne_onePlace ht
  have h2 := zeroPlace_ne_infPlace ht
  have h3 := onePlace_ne_infPlace ht
  exact Finset.card_eq_three.mpr ⟨_, _, _, h1, h2, h3, rfl⟩

theorem mem_tripodPlaces_iff_ord {P : Place K} :
    P ∈ tripodPlaces t ↔ P.ord t ≠ 0 ∨ 0 < P.ord (t - 1) := by
  rw [mem_tripodPlaces]
  constructor
  · rintro (rfl | rfl | rfl)
    · rw [ord_zeroPlace ht]; exact Or.inl one_ne_zero
    · rw [ord_onePlace ht]; exact Or.inr one_pos
    · rw [ord_infPlace ht]; exact Or.inl (by decide)
  · rintro (h | h)
    · rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr (Or.inr ((eq_infPlace_iff_ord_neg ht).mpr h))
      · exact Or.inl ((eq_zeroPlace_iff ht).mpr h)
    · exact Or.inr (Or.inl ((eq_onePlace_iff ht).mpr h))

/-- A place lies on the tripod iff `t`, `t⁻¹` and `(1 - t)⁻¹` are regular at it. -/
theorem notMem_tripodPlaces_iff {P : Place K} :
    P ∉ tripodPlaces t ↔ t ∈ P.1 ∧ t⁻¹ ∈ P.1 ∧ (1 - t)⁻¹ ∈ P.1 := by
  have h01 : t ∈ P.1 ∧ t⁻¹ ∈ P.1 ↔ P.ord t = 0 := (P.ord_eq_zero_iff ht.ne_zero).symm
  have h1t : (1 - t)⁻¹ ∈ P.1 ↔ P.ord (t - 1) ≤ 0 := by
    have hne : (1 - t)⁻¹ ≠ 0 := inv_ne_zero (by
      rw [show 1 - t = -(t - 1) by ring, neg_ne_zero]; exact ht.sub_one.ne_zero)
    rw [P.mem_iff_ord_nonneg]
    simp only [hne, false_or]
    rw [Place.ord_inv, show 1 - t = -(t - 1) by ring, Place.ord_neg]
    omega
  rw [mem_tripodPlaces_iff_ord ht, ← and_assoc, h01, h1t, not_or, not_not, not_lt]

theorem deg_of_mem_tripodPlaces {P : Place K} (hP : P ∈ tripodPlaces t) : P.deg = 1 := by
  rcases mem_tripodPlaces.mp hP with rfl | rfl | rfl
  exacts [deg_zeroPlace ht, deg_onePlace ht, deg_infPlace ht]

theorem mem_of_notMem_tripodPlaces {P : Place K} (hP : P ∉ tripodPlaces t) : t ∈ P.1 :=
  ((notMem_tripodPlaces_iff ht).mp hP).1

/-! ### Points of the tripod -/

namespace QbarPoint

/-- A point at which `t` is regular lies over one of the three places iff `t(x) ∈ {0, 1}`. -/
theorem P_mem_tripodPlaces_iff (x : QbarPoint K) (hx : t ∈ x.P.1) :
    x.P ∈ tripodPlaces t ↔ x.eval t hx = 0 ∨ x.eval t hx = 1 := by
  have hinf : x.P ≠ infPlace t := fun h ↦ notMem_infPlace ht (h ▸ hx)
  have h1 : x.eval t hx = 1 ↔ 0 < x.P.ord (t - 1) := by
    rw [← x.eval_eq_zero_iff (sub_mem hx x.P.1.one_mem) ht.sub_one.ne_zero,
      x.eval_sub hx x.P.1.one_mem, eval_one, sub_eq_zero]
  rw [mem_tripodPlaces, eq_zeroPlace_iff ht, eq_onePlace_iff ht, x.eval_eq_zero_iff hx ht.ne_zero,
    h1]
  simp [hinf]

theorem eval_ne_zero_of_notMem (x : QbarPoint K) (hx : x.P ∉ tripodPlaces t) :
    x.eval t (mem_of_notMem_tripodPlaces ht hx) ≠ 0 := fun h ↦
  hx ((P_mem_tripodPlaces_iff ht x _).mpr (Or.inl h))

theorem eval_ne_one_of_notMem (x : QbarPoint K) (hx : x.P ∉ tripodPlaces t) :
    x.eval t (mem_of_notMem_tripodPlaces ht hx) ≠ 1 := fun h ↦
  hx ((P_mem_tripodPlaces_iff ht x _).mpr (Or.inr h))

omit ht in
/-- The algebraic points of the tripod correspond to `ℚ̄ ∖ {0, 1}` via `x ↦ t(x)`. -/
noncomputable def equivTripod (ht : IsRationalGenerator t) :
    {x : QbarPoint K // x.P ∉ tripodPlaces t} ≃ {z : Qbar // z ≠ 0 ∧ z ≠ 1} where
  toFun x := ⟨x.1.eval t (mem_of_notMem_tripodPlaces ht x.2),
    eval_ne_zero_of_notMem ht x.1 x.2, eval_ne_one_of_notMem ht x.1 x.2⟩
  invFun z := ⟨((equivQbar ht).symm z.1).1, by
    rw [P_mem_tripodPlaces_iff ht _ ((equivQbar ht).symm z.1).2, eval_equivQbar_symm]
    exact fun h ↦ h.elim z.2.1 z.2.2⟩
  left_inv x := Subtype.ext <| by
    have := congrArg Subtype.val
      ((equivQbar ht).symm_apply_apply ⟨x.1, mem_of_notMem_tripodPlaces ht x.2⟩)
    exact this
  right_inv z := Subtype.ext (eval_equivQbar_symm ht z.1)

omit ht in
@[simp]
theorem equivTripod_apply (ht : IsRationalGenerator t)
    (x : {x : QbarPoint K // x.P ∉ tripodPlaces t}) :
    (equivTripod ht x : Qbar) = x.1.eval t (mem_of_notMem_tripodPlaces ht x.2) := rfl

/-- Every `z ∈ ℚ̄ ∖ {0, 1}` is `t(x)` for a unique point `x` of the tripod. -/
theorem existsUnique_eval_eq {z : Qbar} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    ∃! x : {x : QbarPoint K // x.P ∉ tripodPlaces t},
      x.1.eval t (mem_of_notMem_tripodPlaces ht x.2) = z := by
  refine ⟨(equivTripod ht).symm ⟨z, hz0, hz1⟩, ?_, fun y hy ↦ ?_⟩
  · exact congrArg Subtype.val ((equivTripod ht).apply_symm_apply ⟨z, hz0, hz1⟩)
  · rw [Equiv.eq_symm_apply]
    exact Subtype.ext hy

end QbarPoint

/-! ### The coordinate ring `ℚ[t, t⁻¹, (1 - t)⁻¹]` of the tripod -/

omit [IsCurveField K] in
private theorem div_mem_adjoin_tripod (n : ℕ) :
    ∀ q : ℚ[X], q.natDegree = n → q ≠ 0 →
      (∀ z : Qbar, aeval z q = 0 → z = 0 ∨ z = 1) →
      ∀ p : ℚ[X], aeval t p / aeval t q ∈ Algebra.adjoin ℚ {t, t⁻¹, (1 - t)⁻¹} := by
  set A := Algebra.adjoin ℚ ({t, t⁻¹, (1 - t)⁻¹} : Set K)
  have hpol : ∀ p : ℚ[X], aeval t p ∈ A := fun p ↦ by
    have : aeval t p ∈ Algebra.adjoin ℚ {t} := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨p, rfl⟩
    exact Algebra.adjoin_mono (by simp) this
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro q hn hq0 hroots p
  by_cases hdeg : q.degree = 0
  · rw [eq_C_of_degree_eq_zero hdeg, aeval_C, div_eq_mul_inv, ← map_inv₀]
    exact mul_mem (hpol p) (Subalgebra.algebraMap_mem _ _)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero (k := Qbar) q hdeg
  obtain ⟨a, ha, hqa⟩ : ∃ a : ℚ, (a = 0 ∨ a = 1) ∧ q.IsRoot a := by
    have key : ∀ a : ℚ, algebraMap ℚ Qbar a = z → q.IsRoot a := fun a haz ↦ by
      rw [← haz, aeval_algebraMap_apply, map_eq_zero_iff _ (algebraMap ℚ Qbar).injective,
        coe_aeval_eq_eval] at hz
      exact hz
    rcases hroots z hz with rfl | rfl
    · exact ⟨0, Or.inl rfl, key 0 (map_zero _)⟩
    · exact ⟨1, Or.inr rfl, key 1 (map_one _)⟩
  set q' := q /ₘ (X - C a)
  have hq : (X - C a) * q' = q := mul_divByMonic_eq_iff_isRoot.mpr hqa
  have hq'0 : q' ≠ 0 := by rintro h; rw [h, mul_zero] at hq; exact hq0 hq.symm
  have hdeg' : q'.natDegree < n := by
    rw [← hn, ← hq, natDegree_mul (X_sub_C_ne_zero a) hq'0, natDegree_X_sub_C]
    omega
  have hroots' : ∀ z : Qbar, aeval z q' = 0 → z = 0 ∨ z = 1 := fun z hz ↦
    hroots z (by rw [← hq, map_mul, hz, mul_zero])
  have hta : aeval t (X - C a) ≠ 0 := ht.aeval_ne_zero (X_sub_C_ne_zero a)
  have hinv : (aeval t (X - C a))⁻¹ ∈ A := by
    rcases ha with rfl | rfl
    · simpa using Algebra.subset_adjoin (by simp : t⁻¹ ∈ ({t, t⁻¹, (1 - t)⁻¹} : Set K))
    · have h := neg_mem (Algebra.subset_adjoin
        (by simp : (1 - t)⁻¹ ∈ ({t, t⁻¹, (1 - t)⁻¹} : Set K)) : (1 - t)⁻¹ ∈ A)
      rw [← inv_neg, neg_sub] at h
      simpa using h
  rw [← hq, map_mul, div_mul_eq_div_div_swap, div_eq_mul_inv]
  exact mul_mem (ih _ hdeg' q' rfl hq'0 hroots' p) hinv

/-- **The coordinate ring of the tripod.** A function is regular at every place other than
`t = 0, 1, ∞` iff it lies in `ℚ[t, t⁻¹, (1 - t)⁻¹]`. -/
theorem forall_mem_iff_mem_adjoin_tripod (f : K) :
    (∀ P : Place K, P ∉ tripodPlaces t → f ∈ P.1) ↔
      f ∈ Algebra.adjoin ℚ {t, t⁻¹, (1 - t)⁻¹} := by
  constructor
  · intro hf
    obtain ⟨p, q, hq0, hpq, rfl⟩ := ht.exists_coprime f
    refine div_mem_adjoin_tripod ht _ q rfl hq0 (fun z hz ↦ ?_) p
    by_contra hz01
    set x := (QbarPoint.equivQbar ht).symm z
    have hxz : x.1.eval t x.2 = z := QbarPoint.eval_equivQbar_symm ht z
    have hxP : x.1.P ∉ tripodPlaces t := by
      rw [QbarPoint.P_mem_tripodPlaces_iff ht x.1 x.2, hxz]
      exact hz01
    exact x.1.div_notMem x.2 ht.transcendental hq0 hpq (hxz ▸ hz) (hf _ hxP)
  · intro hf P hP
    obtain ⟨h1, h2, h3⟩ := (notMem_tripodPlaces_iff ht).mp hP
    induction hf using Algebra.adjoin_induction with
    | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      exacts [h1, h2, h3]
    | algebraMap q => exact P.algebraMap_mem q
    | add g h _ _ hg hh => exact add_mem hg hh
    | mul g h _ _ hg hh => exact mul_mem hg hh

/-- The coordinate ring of the tripod, as a set. -/
theorem setOf_forall_mem_eq_adjoin_tripod :
    {f : K | ∀ P : Place K, P ∉ tripodPlaces t → f ∈ P.1} =
      (Algebra.adjoin ℚ {t, t⁻¹, (1 - t)⁻¹} : Set K) :=
  Set.ext (forall_mem_iff_mem_adjoin_tripod ht)

end Belyi.CurveField
