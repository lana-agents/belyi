/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.Place
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Zeros and poles of functions on a curve

For a curve field `K`:

* every element has only finitely many zeros and poles
  (`Belyi.CurveField.Place.finite_setOf_ord_ne_zero`,
  `Belyi.CurveField.Place.finite_setOf_notMem`);
* every nonconstant element (i.e. transcendental over `ℚ`) has a zero and a pole
  (`Belyi.CurveField.Place.exists_ord_pos`, `Belyi.CurveField.Place.exists_ord_neg`);
* consequently the elements lying in every place are exactly the constants, i.e. the
  elements algebraic over `ℚ` (`Belyi.CurveField.Place.isAlgebraic_iff_forall_mem`).

Both facts are read off the chart ring `A_f`: the zeros of `f` are the height-one primes of
`A_f` containing `f` (finitely many, and at least one since `f` is not a unit of `A_f`).
-/

open IsDedekindDomain

namespace Belyi.CurveField.Place

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-- A nonconstant function has a zero. -/
theorem exists_ord_pos {f : K} (hf : Transcendental ℚ f) : ∃ P : Place K, 0 < P.ord f := by
  have : Fact (Transcendental ℚ f) := ⟨hf⟩
  have hf0 : f ≠ 0 := ne_zero_of_transcendental hf
  let fB : chartRing f := ⟨f, self_mem_chartRing f⟩
  have hfB0 : fB ≠ 0 := fun h ↦ hf0 (congrArg Subtype.val h)
  have hnu : ¬ IsUnit fB := by
    rintro ⟨u, hu⟩
    apply inv_notMem_chartRing hf
    have h1 : f * ((u⁻¹ : (chartRing f)ˣ) : chartRing f) = 1 := by
      have := congrArg Subtype.val u.mul_inv
      rwa [hu] at this
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact ((u⁻¹ : (chartRing f)ˣ) : chartRing f).2
  obtain ⟨M, hM, hfM⟩ := Ideal.exists_le_maximal (Ideal.span {fB})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hMb : M ≠ ⊥ := by
    intro h
    apply hfB0
    rw [← Ideal.mem_bot, ← h]
    exact hfM (Ideal.mem_span_singleton_self fB)
  let v : HeightOneSpectrum (chartRing f) := ⟨M, hM.isPrime, hMb⟩
  refine ⟨ofChart f v, (ord_pos_iff _).mpr ⟨hf0, ?_⟩⟩
  have hv : fB ∈ ((ofChart f v).toChart f (self_mem_ofChart f v)).asIdeal := by
    rw [toChart_ofChart]
    exact hfM (Ideal.mem_span_singleton_self fB)
  exact (mem_toChart_iff f _ _).mp hv

/-- A nonconstant function has a pole. -/
theorem exists_ord_neg {f : K} (hf : Transcendental ℚ f) : ∃ P : Place K, P.ord f < 0 := by
  obtain ⟨P, hP⟩ := exists_ord_pos (transcendental_inv hf)
  exact ⟨P, by rw [ord_inv] at hP; omega⟩

theorem exists_notMem {f : K} (hf : Transcendental ℚ f) : ∃ P : Place K, f ∉ P.1 := by
  obtain ⟨P, hP⟩ := exists_ord_neg hf
  exact ⟨P, (ord_neg_iff P).mp hP⟩

variable (K) in
instance : Nonempty (Place K) :=
  let ⟨_, ht⟩ := exists_transcendental K
  let ⟨P, _⟩ := exists_ord_pos ht
  ⟨P⟩

/-- An element lying in every place is a constant (algebraic over `ℚ`). -/
theorem isAlgebraic_of_forall_mem {f : K} (h : ∀ P : Place K, f ∈ P.1) : IsAlgebraic ℚ f := by
  by_contra hf
  obtain ⟨P, hP⟩ := exists_notMem hf
  exact hP (h P)

theorem isAlgebraic_iff_forall_mem {f : K} : IsAlgebraic ℚ f ↔ ∀ P : Place K, f ∈ P.1 :=
  ⟨fun hf P ↦ P.mem_of_isAlgebraic hf, isAlgebraic_of_forall_mem⟩

/-- A nonzero element has order `0` everywhere iff it is a constant. -/
theorem isAlgebraic_iff_forall_ord_eq_zero {f : K} :
    IsAlgebraic ℚ f ↔ ∀ P : Place K, P.ord f = 0 := by
  refine ⟨fun hf P ↦ P.ord_eq_zero_of_isAlgebraic hf, fun h ↦ ?_⟩
  by_contra hf
  obtain ⟨P, hP⟩ := exists_ord_pos hf
  exact hP.ne' (h P)

/-- A function has only finitely many zeros. -/
theorem finite_setOf_ord_pos (f : K) : {P : Place K | 0 < P.ord f}.Finite := by
  by_cases hf : IsAlgebraic ℚ f
  · convert Set.finite_empty
    ext P
    simp [P.ord_eq_zero_of_isAlgebraic hf]
  have : Fact (Transcendental ℚ f) := ⟨hf⟩
  have hf0 : f ≠ 0 := ne_zero_of_transcendental hf
  let fB : chartRing f := ⟨f, self_mem_chartRing f⟩
  have hfB0 : fB ≠ 0 := fun h ↦ hf0 (congrArg Subtype.val h)
  have hfin := Ideal.finite_factors (I := Ideal.span {fB}) (by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hfB0)
  refine (hfin.image (ofChart f)).subset ?_
  intro P hP
  have hmem : f ∈ P.1 := P.mem_of_ord_nonneg (le_of_lt hP)
  refine ⟨P.toChart f hmem, ?_, ofChart_toChart f P hmem⟩
  rw [Set.mem_setOf_eq, Ideal.dvd_span_singleton, mem_toChart_iff]
  exact ((P.ord_pos_iff).mp hP).2

/-- A function has only finitely many poles. -/
theorem finite_setOf_ord_neg (f : K) : {P : Place K | P.ord f < 0}.Finite := by
  refine (finite_setOf_ord_pos f⁻¹).subset fun P hP ↦ ?_
  simp only [Set.mem_setOf_eq, ord_inv] at hP ⊢
  omega

/-- A function has only finitely many zeros and poles. -/
theorem finite_setOf_ord_ne_zero (f : K) : {P : Place K | P.ord f ≠ 0}.Finite := by
  refine ((finite_setOf_ord_pos f).union (finite_setOf_ord_neg f)).subset fun P hP ↦ ?_
  simp only [Set.mem_setOf_eq, Set.mem_union] at hP ⊢
  omega

/-- A function lies in all but finitely many places. -/
theorem finite_setOf_notMem (f : K) : {P : Place K | f ∉ P.1}.Finite :=
  (finite_setOf_ord_neg f).subset fun P hP ↦ (ord_neg_iff P).mpr hP

end Belyi.CurveField.Place
