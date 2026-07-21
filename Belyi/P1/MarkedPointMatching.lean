/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.BelyiMapBaseChange
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Marked-point matching for the base-change map of the projective line

This file supplies the reverse (fibre-singleton) direction of marked-point transport for the
base-change morphism `Belyi.P1.mapOfAlgebra k₀ K : ℙ¹_K ⟶ ℙ¹_{k₀}` (taxis issue #164, the
last input of the field-extension specialisation of **B2b**, parent #47).

The forward direction (`Belyi.P1.mapOfAlgebra_base_{zero,one,infty}`, issue #110) shows a
marked point maps to the corresponding marked point.  Here we prove the *reverse*: the fibre
of `mapOfAlgebra` over a `k₀`-rational marked point is exactly the corresponding `K`-point:

* `Belyi.P1.mapOfAlgebra_base_eq_zero`, `_one`, `_infty`.

The geometric content is a homogeneous-prime computation.  Writing `J` for the homogeneous
prime of `K[X₀, X₁]` cutting out `y : ℙ¹_K`, the hypothesis `(mapOfAlgebra k₀ K).base y = 0`
unfolds to `J.comap (map (algebraMap k₀ K)) = span {X₀}`, whence `X₀ ∈ J`, and the key
algebra lemma

* `Belyi.P1.eq_span_of_forall_dvd`: a homogeneous prime `J`, not containing the irrelevant
  ideal, that contains a linear form `ℓ` and is *divisible* by `ℓ` on each homogeneous
  component, equals `span {ℓ}`,

gives `J = span {X₀}`, i.e. `y = 0`.  The three marked points use the linear forms
`X₀`, `X₀ - X₁`, `X₁`; the `X₀ - X₁` case is reduced to `X₀` by the `shear` automorphism of
`Belyi/P1/PointsBaseChange.lean`.

Packaging:

* `Belyi.P1.mapsTo_markedPoints`: the marked-point matching hypothesis of
  `Belyi.isBelyiMap_baseChange_of_mapsTo`.
* `Belyi.isBelyiMap_baseChange`: the **unconditional** field-extension specialisation of B2b —
  the base change of a Belyi map along `k₀ ⊆ K` is a Belyi map.

This is the input the forward direction of Belyi's theorem (B8, #51) and the marked-curve API
(#54) consume.
-/

universe u

namespace MvPolynomial

variable {R : Type*} [CommRing R]

/-- Over `Fin 2`, the total degree of a monomial index is the sum of its two coordinates,
read off along any splitting `i ≠ j` of the index set. -/
lemma finTwo_degree_eq_add (e : Fin 2 →₀ ℕ) (i j : Fin 2) (hij : i ≠ j) :
    e.degree = e i + e j := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals omega

end MvPolynomial

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory Limits MvPolynomial ProjectiveSpectrum

attribute [local instance] MvPolynomial.gradedAlgebra

section Field

variable {K : Type u} [Field K]

/-- **Divisibility skeleton.** For a homogeneous polynomial `h` of degree `n` in `K[X₀, X₁]`
and two distinct variables `X i`, `X j`, the variable `X i` divides `h` after subtracting the
single monomial `X j ^ n` carrying its `X j ^ n`-coefficient: every monomial of the remainder
that is not divisible by `X i` must be `X j ^ n`, and there it cancels. -/
lemma X_dvd_sub {n : ℕ} {h : MvPolynomial (Fin 2) K} (hh : h.IsHomogeneous n)
    (i j : Fin 2) (hij : i ≠ j) :
    (X i : MvPolynomial (Fin 2) K) ∣ (h - C (h.coeff (Finsupp.single j n)) * X j ^ n) := by
  rw [show (X i : MvPolynomial (Fin 2) K) = monomial (Finsupp.single i 1) 1 by simp only [X],
    monomial_one_dvd_iff_forall_coeff]
  intro e he
  rw [Finsupp.single_le_iff] at he
  have hei : e i = 0 := by omega
  rw [coeff_sub, coeff_C_mul, coeff_X_pow]
  by_cases hcase : e = Finsupp.single j n
  · subst hcase; simp
  · have hdeg : e.degree ≠ n := by
      rw [finTwo_degree_eq_add e i j hij, hei, zero_add]
      intro hej
      apply hcase
      ext x
      rcases eq_or_ne x j with rfl | hxj
      · rw [Finsupp.single_eq_same, hej]
      · have hxi : x = i := by fin_cases i <;> fin_cases j <;> fin_cases x <;> simp_all
        rw [Finsupp.single_apply, if_neg (fun hjx => hxj hjx.symm), hxi]
        exact hei
    rw [hh.coeff_eq_zero hdeg, if_neg (fun h' => hcase h'.symm)]
    ring

end Field

section Ideal

variable {K : Type u} [Field K]

/-- A positive-degree homogeneous polynomial in `K[X₀, X₁]` lies in the ideal `(X₀, X₁)`:
each of its monomials has a nonzero exponent, hence is divisible by some variable. -/
lemma mem_span_X01 {i : ℕ} (hi : 0 < i) {x : MvPolynomial (Fin 2) K}
    (hx : x ∈ P1Grading K i) :
    x ∈ Ideal.span {(X 0 : MvPolynomial (Fin 2) K), X 1} := by
  have hxh : x.IsHomogeneous i := (mem_homogeneousSubmodule _ _).mp hx
  rw [show ({X 0, X 1} : Set (MvPolynomial (Fin 2) K)) = X '' {0, 1} from
      (Set.image_pair X 0 1).symm, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hmd : m.degree = i := by
    by_contra hne; exact (mem_support_iff.mp hm) (hxh.coeff_eq_zero hne)
  have hmne : m ≠ 0 := by
    rintro rfl; rw [map_zero] at hmd; omega
  obtain ⟨t, ht⟩ := Finsupp.ne_iff.mp hmne
  exact ⟨t, by fin_cases t <;> simp, by simpa using ht⟩

/-- Two variables cannot both lie in a relevant homogeneous prime: together they generate the
irrelevant ideal, contradicting `not_irrelevant_le`. -/
lemma X01_not_both_mem (y : P1 K)
    (h0 : (X 0 : MvPolynomial (Fin 2) K) ∈ y.asHomogeneousIdeal.toIdeal)
    (h1 : (X 1 : MvPolynomial (Fin 2) K) ∈ y.asHomogeneousIdeal.toIdeal) : False := by
  refine y.not_irrelevant_le ((HomogeneousIdeal.irrelevant_le (𝒜 := P1Grading K)).mpr
    fun n hn z hz => ?_)
  have hsub : Ideal.span {(X 0 : MvPolynomial (Fin 2) K), X 1} ≤ y.asHomogeneousIdeal.toIdeal :=
    Ideal.span_le.mpr (by rintro w (rfl | rfl) <;> assumption)
  exact HomogeneousIdeal.mem_iff.mp (hsub (mem_span_X01 hn hz))

/-- **Key algebra lemma.** A homogeneous prime `J ⊆ K[X₀, X₁]` containing the variable `X i`
but not `X j` (`i ≠ j`) is divisible by `X i` on every homogeneous element: from
`X_dvd_sub`, the leftover monomial `c · X j ^ n` lies in `J`, and primeness with `X j ∉ J`
forces `c = 0`. -/
lemma dvd_of_isHomog_mem {J : Ideal (MvPolynomial (Fin 2) K)} (hp : J.IsPrime)
    (i j : Fin 2) (hij : i ≠ j) (hXi : (X i : MvPolynomial (Fin 2) K) ∈ J)
    (hXj : (X j : MvPolynomial (Fin 2) K) ∉ J)
    {n : ℕ} {h : MvPolynomial (Fin 2) K} (hh : h.IsHomogeneous n) (hhJ : h ∈ J) :
    (X i : MvPolynomial (Fin 2) K) ∣ h := by
  set c := h.coeff (Finsupp.single j n) with hc
  obtain ⟨g, hg⟩ := X_dvd_sub hh i j hij
  rw [← hc] at hg
  have hmem : C c * X j ^ n ∈ J := by
    have hrw : C c * X j ^ n = h - X i * g := by rw [← hg]; ring
    rw [hrw]; exact J.sub_mem hhJ (J.mul_mem_right g hXi)
  have hc0 : c = 0 := by
    by_contra hcne
    have hunit : IsUnit (C c : MvPolynomial (Fin 2) K) :=
      (isUnit_iff_ne_zero.mpr hcne).map (C : K →+* MvPolynomial (Fin 2) K)
    rcases hp.mem_or_mem hmem with hCc | hXpow
    · exact hp.ne_top (Ideal.eq_top_of_isUnit_mem J hCc hunit)
    · exact hXj (hp.mem_of_pow_mem n hXpow)
  rw [hc0, map_zero, zero_mul, sub_zero] at hg
  exact ⟨g, hg⟩

/-- **Wrapper.** A homogeneous ideal `J` containing a degree-one form `ℓ` and divisible by `ℓ`
on every homogeneous component equals `span {ℓ}`: `⊇` is `ℓ ∈ J`, and `⊆` decomposes each
element into homogeneous components, each divisible by `ℓ`. -/
lemma eq_span_of_forall_dvd {ℓ : MvPolynomial (Fin 2) K} {J : Ideal (MvPolynomial (Fin 2) K)}
    (hhom : J.IsHomogeneous (P1Grading K)) (hℓ1 : ℓ.IsHomogeneous 1) (hℓJ : ℓ ∈ J)
    (hdvd : ∀ (n : ℕ) (h : MvPolynomial (Fin 2) K), h.IsHomogeneous n → h ∈ J → ℓ ∣ h) :
    J = Ideal.span {ℓ} := by
  have hspanhom : (Ideal.span {ℓ}).IsHomogeneous (P1Grading K) :=
    Ideal.homogeneous_span _ _ (by
      rintro x rfl; exact ⟨1, (mem_homogeneousSubmodule _ _).mpr hℓ1⟩)
  refine le_antisymm (fun f hf => ?_)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hℓJ))
  rw [MvPolynomial.mem_iff_homogeneousComponent_mem hspanhom]
  intro n
  exact Ideal.mem_span_singleton.mpr
    (hdvd n _ (homogeneousComponent_isHomogeneous n f)
      (MvPolynomial.homogeneousComponent_mem_of_mem hhom hf n))

/-!
### Vanishing loci of the linear forms: `V(ℓ) = {pt}`

Each marked point of `ℙ¹_K` is the unique point whose homogeneous prime contains the
corresponding linear form.  These `V(ℓ) = {pt}` lemmas are the geometric heart of the reverse
marked-point matching below, and are reusable on their own: e.g. `eq_infty_of_X1_mem` is the
`V(X₁) = {∞}` identification consumed by the branch-locus analysis of the polynomial self-map
(taxis issue #108, that `polynomialSelfMap g` fixes `∞`).
-/

/-- **`V(X₀) = {0}`.** A point of `ℙ¹_K` whose homogeneous prime contains `X₀` is the marked
point `0`. -/
lemma eq_zero_of_X0_mem {y : P1 K}
    (hX0 : (X 0 : MvPolynomial (Fin 2) K) ∈ y.asHomogeneousIdeal.toIdeal) :
    y = zero K := by
  have hX1 : (X 1 : MvPolynomial (Fin 2) K) ∉ y.asHomogeneousIdeal.toIdeal :=
    fun h1 => X01_not_both_mem y hX0 h1
  have hspan : y.asHomogeneousIdeal.toIdeal = Ideal.span {(X 0 : MvPolynomial (Fin 2) K)} :=
    eq_span_of_forall_dvd y.asHomogeneousIdeal.isHomogeneous (isHomogeneous_X K 0) hX0
      (fun _ _ hw hwJ => dvd_of_isHomog_mem y.isPrime 0 1 (by decide) hX0 hX1 hw hwJ)
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  rw [hspan, zero, mkPoint_asIdeal]

/-- **`V(X₁) = {∞}`.** A point of `ℙ¹_K` whose homogeneous prime contains `X₁` is the marked
point `∞`.  This is the `V(X₁) = {∞}` helper feeding the `polynomialSelfMap g` branch-locus
analysis (taxis issue #108). -/
lemma eq_infty_of_X1_mem {y : P1 K}
    (hX1 : (X 1 : MvPolynomial (Fin 2) K) ∈ y.asHomogeneousIdeal.toIdeal) :
    y = infty K := by
  have hX0 : (X 0 : MvPolynomial (Fin 2) K) ∉ y.asHomogeneousIdeal.toIdeal :=
    fun h0 => X01_not_both_mem y h0 hX1
  have hspan : y.asHomogeneousIdeal.toIdeal = Ideal.span {(X 1 : MvPolynomial (Fin 2) K)} :=
    eq_span_of_forall_dvd y.asHomogeneousIdeal.isHomogeneous (isHomogeneous_X K 1) hX1
      (fun _ _ hw hwJ => dvd_of_isHomog_mem y.isPrime 1 0 (by decide) hX1 hX0 hw hwJ)
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  rw [hspan, infty, mkPoint_asIdeal]

/-- **`V(X₀ - X₁) = {1}`.** A point of `ℙ¹_K` whose homogeneous prime contains `X₀ - X₁` is the
marked point `1`.  The divisibility skeleton for the linear form `X₀ - X₁` is reduced to the
`X₀` case by the `shear` automorphism (`shear (X₀ - X₁) = X₀`). -/
lemma eq_one_of_X0_sub_X1_mem {y : P1 K}
    (hℓ : (X 0 - X 1 : MvPolynomial (Fin 2) K) ∈ y.asHomogeneousIdeal.toIdeal) :
    y = one K := by
  have hX1 : (X 1 : MvPolynomial (Fin 2) K) ∉ y.asHomogeneousIdeal.toIdeal := by
    intro h1
    have hX0 : (X 0 : MvPolynomial (Fin 2) K) ∈ y.asHomogeneousIdeal.toIdeal := by
      have : (X 0 : MvPolynomial (Fin 2) K) = (X 0 - X 1) + X 1 := by ring
      rw [this]; exact y.asHomogeneousIdeal.toIdeal.add_mem hℓ h1
    exact X01_not_both_mem y hX0 h1
  have hdvd : ∀ (n : ℕ) (hh : MvPolynomial (Fin 2) K), hh.IsHomogeneous n →
      hh ∈ y.asHomogeneousIdeal.toIdeal → (X 0 - X 1 : MvPolynomial (Fin 2) K) ∣ hh := by
    intro n w hw hwJ
    have hsh : (shear K w).IsHomogeneous n := by
      have h1 : (shear K w).IsHomogeneous (1 * n) :=
        hw.aeval ![X 0 + X 1, X 1] (fun t => by
          fin_cases t
          · exact (isHomogeneous_X K 0).add (isHomogeneous_X K 1)
          · exact isHomogeneous_X K 1)
      rwa [one_mul] at h1
    set c := (shear K w).coeff (Finsupp.single 1 n) with hc
    obtain ⟨g, hg⟩ := X_dvd_sub hsh 0 1 (by decide)
    rw [← hc] at hg
    have hg' : w - C c * X 1 ^ n = (X 0 - X 1) * shearInv K g := by
      have hcong := congrArg (shearInv K) hg
      simp only [map_sub, map_mul, map_pow, shearInv_shear] at hcong
      rw [show shearInv K (X 1) = X 1 by simp [shearInv],
        show shearInv K (X 0) = X 0 - X 1 by simp [shearInv],
        show shearInv K (C c) = C c by simp [shearInv, algebraMap_eq]] at hcong
      exact hcong
    have hmem : C c * X 1 ^ n ∈ y.asHomogeneousIdeal.toIdeal := by
      have hrw : C c * X 1 ^ n = w - (X 0 - X 1) * shearInv K g := by rw [← hg']; ring
      rw [hrw]
      exact y.asHomogeneousIdeal.toIdeal.sub_mem hwJ
        (y.asHomogeneousIdeal.toIdeal.mul_mem_right _ hℓ)
    have hc0 : c = 0 := by
      by_contra hcne
      have hunit : IsUnit (C c : MvPolynomial (Fin 2) K) :=
        (isUnit_iff_ne_zero.mpr hcne).map (C : K →+* MvPolynomial (Fin 2) K)
      rcases y.isPrime.mem_or_mem hmem with hCc | hXpow
      · exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hCc hunit)
      · exact hX1 (y.isPrime.mem_of_pow_mem n hXpow)
    rw [hc0, map_zero, zero_mul, sub_zero] at hg'
    exact ⟨shearInv K g, hg'⟩
  have hspan : y.asHomogeneousIdeal.toIdeal = Ideal.span {(X 0 - X 1 : MvPolynomial (Fin 2) K)} :=
    eq_span_of_forall_dvd y.asHomogeneousIdeal.isHomogeneous
      ((isHomogeneous_X K 0).sub (isHomogeneous_X K 1)) hℓ hdvd
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  rw [hspan, one, mkPoint_asIdeal]

end Ideal

section Reverse

variable (k₀ K : Type u) [Field k₀] [Field K] [Algebra k₀ K]

/-- Extract, from `(mapOfAlgebra k₀ K).base y = pt k₀`, the ideal-level equality
`J.comap (map (algebraMap k₀ K)) = span {ℓ_{k₀}}` where `J` is the homogeneous ideal of `y`
and `ℓ` the linear form of the marked point. -/
private lemma comap_eq_of_base_eq {y : P1 K} {ℓ₀ : MvPolynomial (Fin 2) k₀} {p : P1 k₀}
    (hp : p.asHomogeneousIdeal.toIdeal = Ideal.span {ℓ₀})
    (h : (mapOfAlgebra k₀ K).base y = p) :
    Ideal.comap (MvPolynomial.map (algebraMap k₀ K)) y.asHomogeneousIdeal.toIdeal =
      Ideal.span {ℓ₀} := by
  have hb : (mapOfAlgebra k₀ K).base y =
      comap (gradedMapOfAlgebra k₀ K) (irrelevant_le_map_gradedMapOfAlgebra k₀ K) y := rfl
  rw [hb] at h
  have := congrArg (fun q : P1 k₀ => q.asHomogeneousIdeal.toIdeal) h
  rw [hp] at this
  rw [← this]
  change _ = (y.asHomogeneousIdeal.comap (gradedMapOfAlgebra k₀ K)).toIdeal
  rw [HomogeneousIdeal.toIdeal_comap]
  rfl

/-- Membership `X i ∈ J` from the comap equality `J.comap (map φ) = span {X i}`. -/
private lemma X_mem_of_comap_eq {y : P1 K} (i : Fin 2)
    (hcomap : Ideal.comap (MvPolynomial.map (algebraMap k₀ K)) y.asHomogeneousIdeal.toIdeal =
      Ideal.span {(X i : MvPolynomial (Fin 2) k₀)}) :
    (X i : MvPolynomial (Fin 2) K) ∈ y.asHomogeneousIdeal.toIdeal := by
  have hmem : (X i : MvPolynomial (Fin 2) k₀) ∈
      Ideal.comap (MvPolynomial.map (algebraMap k₀ K)) y.asHomogeneousIdeal.toIdeal := by
    rw [hcomap]; exact Ideal.mem_span_singleton_self _
  rw [Ideal.mem_comap] at hmem
  simpa using hmem

/-- **Reverse marked-point matching at `0`.** If the base change sends `y` to the marked point
`0` of `ℙ¹_{k₀}`, then `y` is the marked point `0` of `ℙ¹_K`. -/
lemma mapOfAlgebra_base_eq_zero {y : P1 K} (h : (mapOfAlgebra k₀ K).base y = zero k₀) :
    y = zero K := by
  have hcomap := comap_eq_of_base_eq k₀ K
    (ℓ₀ := X 0) (p := zero k₀) (by rw [zero, mkPoint_asIdeal]) h
  exact eq_zero_of_X0_mem (X_mem_of_comap_eq k₀ K 0 hcomap)

/-- **Reverse marked-point matching at `∞`.** -/
lemma mapOfAlgebra_base_eq_infty {y : P1 K} (h : (mapOfAlgebra k₀ K).base y = infty k₀) :
    y = infty K := by
  have hcomap := comap_eq_of_base_eq k₀ K
    (ℓ₀ := X 1) (p := infty k₀) (by rw [infty, mkPoint_asIdeal]) h
  exact eq_infty_of_X1_mem (X_mem_of_comap_eq k₀ K 1 hcomap)

/-- **Reverse marked-point matching at `1`.** The linear form is `X₀ - X₁`; the divisibility
skeleton is reduced to the `X₀` case by the `shear` automorphism (`shear (X₀ - X₁) = X₀`). -/
lemma mapOfAlgebra_base_eq_one {y : P1 K} (h : (mapOfAlgebra k₀ K).base y = one k₀) :
    y = one K := by
  have hcomap := comap_eq_of_base_eq k₀ K
    (ℓ₀ := X 0 - X 1) (p := one k₀) (by rw [one, mkPoint_asIdeal]) h
  -- `X₀ - X₁ ∈ J`
  have hℓ : (X 0 - X 1 : MvPolynomial (Fin 2) K) ∈ y.asHomogeneousIdeal.toIdeal := by
    have hmem : (X 0 - X 1 : MvPolynomial (Fin 2) k₀) ∈
        Ideal.comap (MvPolynomial.map (algebraMap k₀ K)) y.asHomogeneousIdeal.toIdeal := by
      rw [hcomap]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap] at hmem
    simpa using hmem
  exact eq_one_of_X0_sub_X1_mem hℓ

/-- **Marked-point matching.** Every point of `ℙ¹_K` lying over a marked point of `ℙ¹_{k₀}`
under the base-change map is itself a marked point of `ℙ¹_K`. This is the hypothesis of
`Belyi.isBelyiMap_baseChange_of_mapsTo`. -/
theorem mapsTo_markedPoints (y : P1 K) (hy : (mapOfAlgebra k₀ K).base y ∈ Belyi.markedPoints k₀) :
    y ∈ Belyi.markedPoints K := by
  simp only [Belyi.markedPoints, Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
  rcases hy with h | h | h
  · exact Or.inl (mapOfAlgebra_base_eq_zero k₀ K h)
  · exact Or.inr (Or.inl (mapOfAlgebra_base_eq_one k₀ K h))
  · exact Or.inr (Or.inr (mapOfAlgebra_base_eq_infty k₀ K h))

end Reverse

end Belyi.P1

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

variable (k₀ K : Type u) [Field k₀] [Field K] [Algebra k₀ K]

/-- **Field-extension specialisation of B2b for `IsBelyiMap`, unconditional.** The base change
of a Belyi map `f₀ : X₀ ⟶ ℙ¹_{k₀}` along a field extension `k₀ ⊆ K` is a Belyi map over `K`.

This discharges the marked-point-matching hypothesis of
`Belyi.isBelyiMap_baseChange_of_mapsTo` with `Belyi.P1.mapsTo_markedPoints`. It is the input
consumed by the forward direction of Belyi's theorem (B8, #51). -/
theorem isBelyiMap_baseChange {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ P1 k₀} (hf₀ : IsBelyiMap k₀ f₀) :
    IsBelyiMap K (Limits.pullback.snd f₀ (P1.mapOfAlgebra k₀ K)) :=
  isBelyiMap_baseChange_of_mapsTo k₀ K hf₀ (P1.mapsTo_markedPoints k₀ K)

end Belyi
