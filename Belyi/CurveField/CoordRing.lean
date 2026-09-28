/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.Riemann

/-!
# Coordinate rings of affine curves

For a nonempty finite set `D` of places of a curve field `K`, the coordinate ring of the affine
curve `X ∖ D` is `𝒪(X ∖ D) = {f ∈ K | f ∈ 𝒪_P for all P ∉ D}` (`Belyi.CurveField.coordRing`).
It is the chart ring `A_t` (the integral closure of `ℚ[t]` in `K`) for any `t` whose poles are
exactly the places of `D` (such `t` exist by Riemann's theorem,
`Belyi.CurveField.exists_notMem_iff_mem`), hence a finitely generated `ℚ`-algebra; moreover any
finite set of regular functions on `X ∖ D` can be completed to a finite set of generators
(`Belyi.CurveField.exists_finset_adjoin_eq_coordRing`). Finite generating sets define the affine
integral models used for log-conductors ([GenEll], Definition 1.5 (iv)).
-/

namespace Belyi.CurveField

open Belyi.CurveField.Divisor

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-- The coordinate ring `𝒪(X ∖ D)` of the affine curve `X ∖ D`. -/
def coordRing (D : Finset (Place K)) : Subalgebra ℚ K where
  carrier := {f | ∀ P : Place K, P ∉ D → f ∈ P.1}
  mul_mem' hf hg P hP := mul_mem (hf P hP) (hg P hP)
  add_mem' hf hg P hP := add_mem (hf P hP) (hg P hP)
  algebraMap_mem' q P _ := P.algebraMap_mem q

theorem mem_coordRing {D : Finset (Place K)} {f : K} :
    f ∈ coordRing D ↔ ∀ P : Place K, P ∉ D → f ∈ P.1 := Iff.rfl

/-- The chart ring `A_t` consists of the functions regular at all places where `t` is. -/
theorem mem_chartRing_iff_forall {t : K} [Fact (Transcendental ℚ t)] (f : K) :
    f ∈ chartRing t ↔ ∀ P : Place K, t ∈ P.1 → f ∈ P.1 := by
  refine ⟨fun hf P hP => mem_of_mem_chartRing P.1 P.ratCast_mem hP hf, fun hf => ?_⟩
  set s : Set K := Set.range (algebraMap ℚ K) ∪ {t} with hs
  have hmem : f ∈ (⨅ V : {V : ValuationSubring K // s ⊆ V.toSubring}, V.1.toSubring) := by
    rw [Subring.mem_iInf]
    rintro ⟨V, hV⟩
    by_cases htop : V = ⊤
    · subst htop
      exact trivial
    · have hq : ∀ q : ℚ, (q : K) ∈ V := fun q => hV (Or.inl ⟨q, eq_ratCast _ q⟩)
      exact hf ⟨V, htop, hq⟩ (hV (Or.inr rfl))
  rw [iInf_valuationSubring_superset] at hmem
  have hint : IsIntegral (Subring.closure s) f := hmem
  have heq : (Algebra.adjoin ℚ {t}).toSubring = Subring.closure s := by
    rw [Algebra.adjoin_eq_ring_closure]
  let e : Subring.closure s →+* Algebra.adjoin ℚ {t} :=
    { toFun := fun a => ⟨a.1, by rw [← Subalgebra.mem_toSubring, heq]; exact a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact IsIntegral.map_of_comp_eq e (RingHom.id K) (by ext a; rfl) hint

/-- There is a function whose poles are exactly the places of a given nonempty finite set. -/
theorem exists_notMem_iff_mem (D : Finset (Place K)) (hD : D.Nonempty) :
    ∃ t : K, Transcendental ℚ t ∧ ∀ P : Place K, t ∉ P.1 ↔ P ∈ D := by
  classical
  obtain ⟨N1, hN1⟩ := exists_polarDivisor_eq (K := K)
  set A₀ : Divisor K := ∑ P ∈ D, Finsupp.single P 1 with hA₀
  have hA₀P : ∀ P, A₀ P = if P ∈ D then 1 else 0 := by
    intro P
    rw [hA₀, Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hA₀nonneg : 0 ≤ A₀ := fun P => by rw [hA₀P P]; split_ifs <;> simp
  have hdeg₀ : 0 < A₀.deg := by
    obtain ⟨P₀, hP₀⟩ := hD
    refine deg_pos_of_nonneg_of_ne_zero hA₀nonneg fun h => ?_
    have := congrArg (fun A : Divisor K => A P₀) h
    simp only [hA₀P, hP₀, if_true, Finsupp.coe_zero, Pi.zero_apply] at this
    exact one_ne_zero this
  set n : ℕ := N1.toNat + 1 with hn
  have hdeg : N1 ≤ (n • A₀).deg := by
    rw [deg_nsmul]
    have h1 : (N1 : ℤ) ≤ n := by
      rw [hn]
      push_cast
      have := Int.self_le_toNat N1
      omega
    nlinarith
  have hnonneg : 0 ≤ n • A₀ := fun P => by
    simp only [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (hA₀nonneg P)
  obtain ⟨t, ht⟩ := hN1 (n • A₀) hnonneg hdeg
  have hpole : ∀ P : Place K, t ∉ P.1 ↔ P ∈ D := by
    intro P
    rw [← P.ord_neg_iff]
    have h := congrArg (fun A : Divisor K => A P) ht
    simp only [polarDivisor_apply, Finsupp.smul_apply, smul_eq_mul, hA₀P] at h
    constructor
    · intro hlt
      by_contra hPD
      rw [if_neg hPD, smul_zero] at h
      have := le_max_right 0 (-P.ord t)
      omega
    · intro hPD
      rw [if_pos hPD, nsmul_eq_mul, mul_one] at h
      have hnpos : (0 : ℤ) < n := by rw [hn]; positivity
      by_contra hge
      push Not at hge
      rw [max_eq_left (by omega)] at h
      omega
  refine ⟨t, fun halg => ?_, hpole⟩
  obtain ⟨P₀, hP₀⟩ := hD
  have hmem : t ∈ P₀.1 := P₀.mem_of_isAlgebraic halg
  exact (hpole P₀).mpr hP₀ hmem

/-- The coordinate ring of `X ∖ D` is the chart ring of a function with poles exactly `D`. -/
theorem coordRing_eq_chartRing {D : Finset (Place K)} {t : K} [Fact (Transcendental ℚ t)]
    (ht : ∀ P : Place K, t ∉ P.1 ↔ P ∈ D) (f : K) : f ∈ coordRing D ↔ f ∈ chartRing t := by
  rw [mem_coordRing, mem_chartRing_iff_forall]
  refine forall_congr' fun P => ?_
  rw [← ht]
  exact ⟨fun h htP => h (not_not.mpr htP), fun h hn => h (not_not.mp hn)⟩

/-- **Generators of the coordinate ring**: any finite set of regular functions on `X ∖ D` extends
to a finite set of generators of `𝒪(X ∖ D)` as a `ℚ`-algebra. -/
theorem exists_finset_adjoin_eq_coordRing (D : Finset (Place K)) (hD : D.Nonempty)
    (S : Finset K) (hS : ∀ s ∈ S, s ∈ coordRing D) :
    ∃ G : Finset K, S ⊆ G ∧ Algebra.adjoin ℚ (G : Set K) = coordRing D := by
  classical
  obtain ⟨t, htr, ht⟩ := exists_notMem_iff_mem D hD
  haveI : Fact (Transcendental ℚ t) := ⟨htr⟩
  obtain ⟨s₀, hs₀⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℚ (chartRing t)).FG)
  set G₀ : Finset K := s₀.image Subtype.val with hG₀
  refine ⟨S ∪ G₀, Finset.subset_union_left, le_antisymm ?_ ?_⟩
  · rw [Algebra.adjoin_le_iff]
    intro g hg
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hg) with hgS | hgG
    · exact hS g hgS
    · rw [hG₀, Finset.mem_image] at hgG
      obtain ⟨a, -, rfl⟩ := hgG
      exact (coordRing_eq_chartRing ht a.1).mpr a.2
  · intro f hf
    have hfc : f ∈ chartRing t := (coordRing_eq_chartRing ht f).mp hf
    have h1 : (⟨f, hfc⟩ : chartRing t) ∈ Algebra.adjoin ℚ (s₀ : Set (chartRing t)) := by
      rw [hs₀]
      exact Algebra.mem_top
    have key : ∀ a : chartRing t, a ∈ Algebra.adjoin ℚ (s₀ : Set (chartRing t)) →
        (a : K) ∈ Algebra.adjoin ℚ ((S ∪ G₀ : Finset K) : Set K) := by
      intro a ha
      induction ha using Algebra.adjoin_induction with
      | mem x hx =>
        exact Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨x, hx, rfl⟩)))
      | algebraMap q =>
        have : ((algebraMap ℚ (chartRing t) q : chartRing t) : K) = algebraMap ℚ K q := by
          have h := RingHom.ext_rat (((chartRing t).val : chartRing t →+* K).comp
            (algebraMap ℚ (chartRing t))) (algebraMap ℚ K)
          exact congrFun (congrArg DFunLike.coe h) q
        rw [this]
        exact Subalgebra.algebraMap_mem _ q
      | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
      | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
    exact key _ h1

end Belyi.CurveField
