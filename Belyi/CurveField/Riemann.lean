/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.RiemannRochSpace
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.AlgebraTower

/-!
# Riemann's theorem

For a curve field `K` (with degrees and dimensions taken over `ℚ`), the function
`A ↦ deg A - ℓ(A)` on divisors is bounded above (*Riemann's inequality*); its maximum
`Belyi.CurveField.Divisor.riemannConst K` is attained, and `ℓ(A) = deg A - riemannConst K`
as soon as `deg A` is large (*Riemann's theorem*). (If `k` is the constant field of `K` and
`g` the genus, then `riemannConst K = [k : ℚ] (g - 1)`; we do not need this.)

We follow H. Stichtenoth, *Algebraic Function Fields and Codes*, Ch. 1 §1.4
(Proposition 1.4.14, Lemma 1.4.15, Proposition 1.4.16, Theorem 1.4.17), with the following
simplifications: for `x ∈ K` transcendental with divisor of poles `B = (x)_∞`, a basis
`u_1, …, u_n` of `K / ℚ(x)` and `C = ∑ (u_i)_∞`, the `(l + 1) n` elements `x^k u_i`
(`k ≤ l`) are `ℚ`-linearly independent elements of `L(l B + C)`; this bounds
`deg (l B) - ℓ(l B)` uniformly in `l`. Every divisor `A` is linearly equivalent to a divisor
`≤ l B` for some `l`: add the places one at a time, using `B` at the poles of `x` and the
function `p(x)`, `p` the minimal polynomial over `ℚ` of the residue of `x`, at the others.

Consequences:

* **Realisation of polar divisors** (`Belyi.CurveField.Divisor.exists_polarDivisor_eq`):
  every effective divisor of large degree is the divisor of poles of a function. Indeed for
  `P` in the support of `A` the subspace `L(A - P)` of `L(A)` is proper, and a `ℚ`-vector
  space is not a finite union of proper subspaces.
* every divisor is a difference of two polar divisors
  (`Belyi.CurveField.Divisor.exists_eq_polarDivisor_sub_polarDivisor`);
* a multiple of a divisor of positive degree is linearly equivalent to a polar divisor
  (`Belyi.CurveField.Divisor.exists_polarDivisor_eq_nsmul_add_div`).
-/

open Polynomial IsLocalRing
open scoped IntermediateField

namespace Belyi.CurveField

namespace Divisor

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-! ### Polynomials in a function -/

theorem pow_mem_L (x : K) (k : ℕ) : x ^ k ∈ L (k • polarDivisor x) := by
  refine Or.inr fun P ↦ ?_
  simp only [Finsupp.coe_smul, Pi.smul_apply, polarDivisor_apply, nsmul_eq_mul, Place.ord_pow]
  have h1 := le_max_right 0 (-P.ord x)
  have h2 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
  nlinarith

/-- A polynomial of degree `≤ d` in `x` lies in `L(d (x)_∞)`. -/
theorem aeval_mem_L (x : K) (p : ℚ[X]) : aeval x p ∈ L (p.natDegree • polarDivisor x) := by
  rw [aeval_eq_sum_range]
  refine Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _ (L_mono ?_ (pow_mem_L x i))
  exact nsmul_le_nsmul_left (polarDivisor_nonneg x)
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- At a place `P` where `x` is regular, `p(x)` vanishes for `p` the minimal polynomial of the
residue of `x`. -/
theorem exists_aeval_ord_pos {x : K} (hx : Transcendental ℚ x) (P : Place K) (hxP : x ∈ P.1) :
    ∃ p : ℚ[X], aeval x p ≠ 0 ∧ 0 < P.ord (aeval x p) := by
  set r := P.residue ⟨x, hxP⟩
  have hint : IsIntegral ℚ r := Algebra.IsIntegral.isIntegral r
  set p := minpoly ℚ r
  have hp0 : p ≠ 0 := minpoly.ne_zero hint
  have hy0 : aeval x p ≠ 0 := fun h ↦ hx ⟨p, hp0, h⟩
  refine ⟨p, hy0, ?_⟩
  set e : P.1 := p.eval₂ P.ratHom ⟨x, hxP⟩
  have hcomp : P.1.subtype.comp P.ratHom = algebraMap ℚ K := by
    ext q; simp [ValuationSubring.subtype]
  have he : (e : K) = aeval x p := by
    rw [aeval_def, ← hcomp]
    exact Polynomial.hom_eval₂ p P.ratHom P.1.subtype ⟨x, hxP⟩
  have hcomp' : P.residue.comp P.ratHom = algebraMap ℚ P.ResidueField := by
    ext q; simp
  have hres : P.residue e = 0 := by
    rw [Polynomial.hom_eval₂, hcomp', ← aeval_def]
    exact minpoly.aeval ℚ r
  rw [← he]
  refine (P.ord_pos_iff_mem_maximalIdeal (a := e) (by rw [he]; exact hy0)).mpr ?_
  exact P.residue_eq_zero_iff.mp hres

/-! ### Reduction to multiples of a polar divisor -/

section Reduction

variable {x : K} (hx : Transcendental ℚ x)
include hx

omit hx in
theorem single_le_polarDivisor {P : Place K} (hP : P.ord x < 0) :
    Finsupp.single P 1 ≤ polarDivisor x := by
  classical
  intro Q
  by_cases hQ : P = Q
  · subst hQ; simp only [Finsupp.single_eq_same, polarDivisor_apply]; omega
  · rw [Finsupp.single_apply, if_neg hQ]; exact polarDivisor_nonneg x Q

theorem exists_add_single_add_div_le {A : Divisor K} (P : Place K)
    (h : ∃ z : K, z ≠ 0 ∧ ∃ l : ℕ, A + div z ≤ l • polarDivisor x) :
    ∃ z : K, z ≠ 0 ∧ ∃ l : ℕ, A + Finsupp.single P 1 + div z ≤ l • polarDivisor x := by
  classical
  obtain ⟨z, hz, l, hl⟩ := h
  by_cases hP : P.ord x < 0
  · refine ⟨z, hz, l + 1, ?_⟩
    rw [succ_nsmul, show A + Finsupp.single P 1 + div z = (A + div z) + Finsupp.single P 1 by
      abel]
    exact add_le_add hl (single_le_polarDivisor hP)
  obtain ⟨p, hy0, hypos⟩ := exists_aeval_ord_pos hx P (P.mem_of_ord_nonneg (not_lt.mp hP))
  have hyL := (mem_L.mp (aeval_mem_L x p)).resolve_left hy0
  refine ⟨z / aeval x p, div_ne_zero hz hy0, l + p.natDegree, ?_⟩
  rw [div_div hz hy0, add_nsmul, show A + Finsupp.single P 1 + (div z - div (aeval x p)) =
    (A + div z) + (Finsupp.single P 1 - div (aeval x p)) by abel]
  refine add_le_add hl fun Q ↦ ?_
  have h1 := hyL Q
  have h2 := (nsmul_nonneg (polarDivisor_nonneg x) p.natDegree) Q
  simp only [Finsupp.coe_sub, Pi.sub_apply, div_apply, Finsupp.coe_zero,
    Pi.zero_apply] at h1 h2 ⊢
  by_cases hQ : P = Q
  · subst hQ; rw [Finsupp.single_eq_same]; omega
  · rw [Finsupp.single_apply, if_neg hQ]; omega

theorem exists_add_single_nat_add_div_le {A : Divisor K} (P : Place K) (m : ℕ)
    (h : ∃ z : K, z ≠ 0 ∧ ∃ l : ℕ, A + div z ≤ l • polarDivisor x) :
    ∃ z : K, z ≠ 0 ∧ ∃ l : ℕ, A + Finsupp.single P (m : ℤ) + div z ≤ l • polarDivisor x := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    have := exists_add_single_add_div_le hx P ih
    rwa [Nat.cast_succ, Finsupp.single_add, ← add_assoc]

/-- Every divisor is linearly equivalent to a divisor `≤ l (x)_∞` for some `l`
(Stichtenoth, proof of Proposition 1.4.14). -/
theorem exists_add_div_le (A : Divisor K) :
    ∃ z : K, z ≠ 0 ∧ ∃ l : ℕ, A + div z ≤ l • polarDivisor x := by
  classical
  induction A using Finsupp.induction with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | single_add P b f _ _ ih =>
    rcases le_or_gt b 0 with hb | hb
    · obtain ⟨z, hz, l, hl⟩ := ih
      refine ⟨z, hz, l, le_trans ?_ hl⟩
      rw [add_assoc]
      refine add_le_of_nonpos_left fun Q ↦ ?_
      rw [Finsupp.single_apply]
      split_ifs <;> simp [hb]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hb.le
      rw [add_comm]
      exact exists_add_single_nat_add_div_le hx P m ih

/-- For `B = (x)_∞`, `deg (l B) - ℓ(l B)` is bounded independently of `l`. -/
theorem exists_deg_sub_ell_nsmul_le :
    ∃ γ : ℤ, ∀ l : ℕ, (l • polarDivisor x).deg - ell (l • polarDivisor x) ≤ γ := by
  have := finiteDimensional_adjoin hx
  set n := Module.finrank ℚ⟮x⟯ K
  let u := Module.finBasis ℚ⟮x⟯ K
  set B := polarDivisor x
  set C : Divisor K := ∑ i, polarDivisor (u i : K)
  have hC : 0 ≤ C := fun Q ↦ by
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg fun i _ ↦ polarDivisor_nonneg _ Q
  have hx0 : x ≠ 0 := ne_zero_of_transcendental hx
  refine ⟨C.deg - n, fun l ↦ ?_⟩
  -- the elements `x^k u_i` lie in `L(l B + C)`
  have hmem : ∀ p : Fin (l + 1) × Fin n, x ^ (p.1 : ℕ) * u p.2 ∈ L (l • B + C) := by
    rintro ⟨k, i⟩
    refine Or.inr fun Q ↦ ?_
    rw [Q.ord_mul (pow_ne_zero _ hx0) (u.ne_zero i), Place.ord_pow]
    have hk : ((k : ℕ) : ℤ) ≤ l := by exact_mod_cast Nat.lt_succ_iff.mp k.2
    have hk0 : (0 : ℤ) ≤ (k : ℕ) := Int.natCast_nonneg _
    have h1 := le_max_right 0 (-Q.ord x)
    have h1' := le_max_left 0 (-Q.ord x)
    have h2 := le_max_right 0 (-Q.ord (u i))
    have h3 : max 0 (-Q.ord (u i)) ≤ C Q := by
      rw [Finsupp.finsetSum_apply]
      exact Finset.single_le_sum (f := fun j ↦ polarDivisor (u j : K) Q)
        (fun j _ ↦ polarDivisor_nonneg _ Q) (Finset.mem_univ i)
    simp only [B, Finsupp.coe_add, Pi.add_apply, Finsupp.smul_apply, polarDivisor_apply,
      nsmul_eq_mul]
    nlinarith
  -- they are linearly independent over `ℚ`
  have hpow : LinearIndependent ℚ (fun k : ℕ ↦ x ^ k) := by
    have := (Polynomial.basisMonomials ℚ).linearIndependent.map' (aeval x).toLinearMap
      (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hx))
    simpa [Function.comp_def, Polynomial.coe_basisMonomials] using this
  let b : Fin (l + 1) → ℚ⟮x⟯ := fun k ↦ (IntermediateField.AdjoinSimple.gen ℚ x) ^ (k : ℕ)
  have hb : LinearIndependent ℚ b := by
    refine LinearIndependent.of_comp (IsScalarTower.toAlgHom ℚ ℚ⟮x⟯ K).toLinearMap ?_
    convert hpow.comp (Fin.val) Fin.val_injective using 1
    ext k
    simp [b]
  have hli := linearIndependent_smul hb u.linearIndependent
  have hv : ∀ p : Fin (l + 1) × Fin n, b p.1 • (u p.2 : K) = x ^ (p.1 : ℕ) * u p.2 := by
    intro p
    simp [b, Algebra.smul_def]
  let w : Fin (l + 1) × Fin n → L (l • B + C) := fun p ↦ ⟨x ^ (p.1 : ℕ) * u p.2, hmem p⟩
  have hw : LinearIndependent ℚ w := by
    refine LinearIndependent.of_comp (L (l • B + C)).subtype ?_
    convert hli using 1
    ext p
    exact (hv p).symm
  have hcard := hw.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hcard
  have hdegD : (l • B + C).deg = l * n + C.deg := by
    rw [deg_add, deg_nsmul, deg_polarDivisor hx]
  have hmono := deg_sub_ell_mono (le_add_of_nonneg_right hC : l • B ≤ l • B + C)
  have hcard' : ((l : ℤ) + 1) * n ≤ ell (l • B + C) := by exact_mod_cast hcard
  have : ((l : ℤ) + 1) * n = l * n + n := by ring
  omega

end Reduction

/-! ### Riemann's theorem -/

/-- **Riemann's inequality** (Stichtenoth, Proposition 1.4.14): `deg A - ℓ(A)` is bounded
above. -/
theorem exists_deg_sub_ell_le : ∃ γ : ℤ, ∀ A : Divisor K, A.deg - ell A ≤ γ := by
  obtain ⟨x, hx⟩ := exists_transcendental K
  obtain ⟨γ, hγ⟩ := exists_deg_sub_ell_nsmul_le hx
  refine ⟨γ, fun A ↦ ?_⟩
  obtain ⟨z, hz, l, hl⟩ := exists_add_div_le hx A
  have h := deg_sub_ell_mono hl
  rw [deg_add, deg_div, add_zero, ell_add_div A hz] at h
  exact h.trans (hγ l)

variable (K) in
/-- The constant `max_A (deg A - ℓ(A))` of Riemann's theorem (it equals `[k : ℚ](g - 1)`,
for `k` the constant field and `g` the genus). -/
noncomputable def riemannConst : ℤ := sSup (Set.range fun A : Divisor K ↦ A.deg - (ell A : ℤ))

theorem bddAbove_range_deg_sub_ell :
    BddAbove (Set.range fun A : Divisor K ↦ A.deg - (ell A : ℤ)) := by
  obtain ⟨γ, hγ⟩ := exists_deg_sub_ell_le (K := K)
  exact ⟨γ, by rintro _ ⟨A, rfl⟩; exact hγ A⟩

theorem deg_sub_ell_le_riemannConst (A : Divisor K) : A.deg - ell A ≤ riemannConst K :=
  le_csSup bddAbove_range_deg_sub_ell ⟨A, rfl⟩

/-- **Riemann's inequality**: `ℓ(A) ≥ deg A - riemannConst K`. -/
theorem riemann_inequality (A : Divisor K) : A.deg - riemannConst K ≤ ell A := by
  have := deg_sub_ell_le_riemannConst A
  omega

theorem exists_deg_sub_ell_eq_riemannConst :
    ∃ A : Divisor K, A.deg - ell A = riemannConst K := by
  obtain ⟨A, hA⟩ := Int.csSup_mem (Set.range_nonempty _) (bddAbove_range_deg_sub_ell (K := K))
  exact ⟨A, hA⟩

/-- **Riemann's theorem** (Stichtenoth, Theorem 1.4.17, with `riemannConst K` in place of
`g - 1`): `ℓ(A) = deg A - riemannConst K` for all `A` of sufficiently large degree. -/
theorem riemann_equality :
    ∃ N0 : ℤ, ∀ A : Divisor K, N0 ≤ A.deg → (ell A : ℤ) = A.deg - riemannConst K := by
  obtain ⟨A0, hA0⟩ := exists_deg_sub_ell_eq_riemannConst (K := K)
  refine ⟨A0.deg + riemannConst K + 1, fun A hA ↦ ?_⟩
  have h1 := riemann_inequality (A - A0)
  rw [deg_sub] at h1
  obtain ⟨z, hz, hle⟩ := exists_nonneg_add_div (A := A - A0) (by omega)
  have hle' : A0 ≤ A + div z := by
    intro Q
    have := hle Q
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply, Finsupp.coe_zero,
      Pi.zero_apply] at this ⊢
    omega
  have h2 := deg_sub_ell_mono hle'
  rw [deg_add, deg_div, add_zero, ell_add_div A hz] at h2
  have h3 := deg_sub_ell_le_riemannConst A
  omega

/-- **Riemann's theorem**, existential form. -/
theorem exists_riemann :
    ∃ g0 N0 : ℤ, ∀ A : Divisor K, N0 ≤ A.deg → (ell A : ℤ) = A.deg - g0 :=
  ⟨riemannConst K, riemann_equality⟩

/-! ### Realisation of polar divisors -/

/-- **Realisation of polar divisors**: every effective divisor of sufficiently large degree is
the divisor of poles of a function. -/
theorem exists_polarDivisor_eq :
    ∃ N1 : ℤ, ∀ A : Divisor K, 0 ≤ A → N1 ≤ A.deg → ∃ f : K, polarDivisor f = A := by
  classical
  obtain ⟨N0, hN0⟩ := riemann_equality (K := K)
  set g0 := riemannConst K
  set M : ℤ := max 0 (N0 + ell (0 : Divisor K))
  refine ⟨max (max N0 1) (M + g0 + 1), fun A hA hdeg ↦ ?_⟩
  have hdN0 : N0 ≤ A.deg := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hdeg
  have hd1 : 1 ≤ A.deg := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hdeg
  have hdM : M + g0 + 1 ≤ A.deg := le_trans (le_max_right _ _) hdeg
  have hellA := hN0 A hdN0
  -- `L(A - P) ⊊ L(A)` for every place `P` in the support of `A`
  have hlt : ∀ P : Place K, ell (A - Finsupp.single P 1) < ell A := by
    intro P
    have hP := P.deg_pos
    by_cases hP' : N0 ≤ (A - Finsupp.single P 1).deg
    · have := hN0 _ hP'
      rw [deg_sub, deg_single] at this
      have : (ell (A - Finsupp.single P 1) : ℤ) < ell A := by
        rw [this, hellA]; omega
      exact_mod_cast this
    · have h1 := ell_le_max (A - Finsupp.single P 1)
      have h2 : max 0 ((A - Finsupp.single P 1).deg + (ell (0 : Divisor K) : ℤ)) ≤ M :=
        max_le_max le_rfl (by omega)
      have : (ell (A - Finsupp.single P 1) : ℤ) < ell A := by
        rw [hellA]; omega
      exact_mod_cast this
  let p : A.support → Submodule ℚ (L A) := fun P ↦
    (L (A - Finsupp.single P.1 1)).comap (L A).subtype
  have hp : ∀ P, p P ≠ ⊤ := by
    intro P h
    have hle : L A ≤ L (A - Finsupp.single P.1 1) := fun f hf ↦ by
      have : (⟨f, hf⟩ : L A) ∈ p P := h ▸ Submodule.mem_top
      exact this
    exact absurd (Submodule.finrank_mono hle) (not_le.mpr (hlt P.1))
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  have hA0 : A ≠ 0 := by rintro rfl; simp at hd1
  obtain ⟨P0, hP0⟩ := Finsupp.support_nonempty_iff.mpr hA0
  have hv0 : (v : K) ≠ 0 := by
    intro h
    apply hv ⟨P0, hP0⟩
    change (v : K) ∈ L _
    rw [h]; exact Submodule.zero_mem _
  have hvL := (mem_L.mp v.2).resolve_left hv0
  refine ⟨v, Finsupp.ext fun Q ↦ ?_⟩
  rw [polarDivisor_apply]
  by_cases hQ : Q ∈ A.support
  · have hnot : (v : K) ∉ L (A - Finsupp.single Q 1) := hv ⟨Q, hQ⟩
    rw [mem_L, not_or] at hnot
    obtain ⟨R, hR⟩ := not_forall.mp hnot.2
    have hRQ : R = Q := by
      by_contra hne
      apply hR
      simpa [Finsupp.single_apply, Ne.symm hne] using hvL R
    subst hRQ
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_eq_same, not_le] at hR
    have := hvL R
    have := hA R
    simp only [Finsupp.coe_zero, Pi.zero_apply] at this
    omega
  · rw [Finsupp.notMem_support_iff.mp hQ]
    have := hvL Q
    rw [Finsupp.notMem_support_iff.mp hQ] at this
    omega

/-- The positive part `∑ max(A(P), 0) P` of a divisor. -/
noncomputable def posPart (A : Divisor K) : Divisor K :=
  Finsupp.mapRange (fun n ↦ max n 0) (by simp) A

omit [CharZero K] [IsCurveField K] in
theorem posPart_apply (A : Divisor K) (P : Place K) : posPart A P = max (A P) 0 :=
  Finsupp.mapRange_apply ..

omit [CharZero K] [IsCurveField K] in
theorem posPart_nonneg (A : Divisor K) : 0 ≤ posPart A := fun P ↦ by
  simp [posPart_apply]

omit [CharZero K] [IsCurveField K] in
theorem posPart_sub_posPart_neg (A : Divisor K) : posPart A - posPart (-A) = A := by
  ext P
  simp only [Finsupp.coe_sub, Pi.sub_apply, posPart_apply, Finsupp.coe_neg, Pi.neg_apply]
  omega

/-- **Every divisor is a difference of two polar divisors.** -/
theorem exists_eq_polarDivisor_sub_polarDivisor (D : Divisor K) :
    ∃ f g : K, D = polarDivisor f - polarDivisor g := by
  obtain ⟨N1, hN1⟩ := exists_polarDivisor_eq (K := K)
  obtain P0 : Place K := Classical.arbitrary _
  set E : Divisor K := Finsupp.single P0 (N1.toNat : ℤ)
  have hE : 0 ≤ E := Finsupp.single_nonneg.mpr (Int.natCast_nonneg _)
  have hdegE : N1 ≤ E.deg := by
    rw [deg_single]
    have := P0.deg_pos
    have h1 : N1 ≤ (N1.toNat : ℤ) := Int.self_le_toNat N1
    have h2 : (0 : ℤ) ≤ N1.toNat := Int.natCast_nonneg _
    nlinarith
  have key : ∀ A : Divisor K, 0 ≤ A → ∃ f : K, polarDivisor f = A + E := fun A hA ↦
    hN1 _ (add_nonneg hA hE) (by rw [deg_add]; have := deg_nonneg hA; omega)
  obtain ⟨f, hf⟩ := key _ (posPart_nonneg D)
  obtain ⟨g, hg⟩ := key _ (posPart_nonneg (-D))
  refine ⟨f, g, ?_⟩
  rw [hf, hg, add_sub_add_right_eq_sub, posPart_sub_posPart_neg]

/-- **Divisors of positive degree**: a positive multiple of a divisor of positive degree is
linearly equivalent to a polar divisor. -/
theorem exists_polarDivisor_eq_nsmul_add_div {A : Divisor K} (hA : 0 < A.deg) :
    ∃ n : ℕ, 0 < n ∧ ∃ f r : K, r ≠ 0 ∧ polarDivisor f = n • A + div r := by
  obtain ⟨N1, hN1⟩ := exists_polarDivisor_eq (K := K)
  set n : ℕ := (max N1 (riemannConst K + 1)).toNat + 1
  have hn : max N1 (riemannConst K + 1) < n := by
    have := Int.self_le_toNat (max N1 (riemannConst K + 1))
    simp only [n]; push_cast; omega
  have hdeg : (n : ℤ) ≤ (n • A).deg := by
    rw [deg_nsmul]
    nlinarith
  have hell := riemann_inequality (n • A)
  obtain ⟨r, hr, hle⟩ := exists_nonneg_add_div (A := n • A) (by
    have := le_max_right N1 (riemannConst K + 1)
    omega)
  obtain ⟨f, hf⟩ := hN1 _ hle (by
    rw [deg_add, deg_div, add_zero]
    have := le_max_left N1 (riemannConst K + 1)
    omega)
  exact ⟨n, Nat.succ_pos _, f, r, hr, hf⟩

end Divisor

end Belyi.CurveField
