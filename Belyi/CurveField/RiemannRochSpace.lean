/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.Divisor
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Riemann–Roch spaces

For a divisor `A` of a curve field `K`, the Riemann–Roch space is the `ℚ`-vector space
`L(A) = {f ∈ K | f = 0 ∨ div f ≥ -A}` (`Belyi.CurveField.Divisor.L`), and
`ℓ(A) = dim_ℚ L(A)` (`Belyi.CurveField.Divisor.ell`).

Following H. Stichtenoth, *Algebraic Function Fields and Codes*, Ch. 1 §1.4
(Lemmas 1.4.8, 1.4.9, Proposition 1.4.14 in the non-constant-field-extended form): the map
`L(A + P) → κ(P)`, `f ↦ (π^{A(P)+1} f)(P)` for a uniformiser `π` at `P` is `ℚ`-linear with
kernel `L(A)`, so adding a place `P` increases the dimension by at most `deg P`; since
`L(A) = 0` when `deg A < 0`, every `L(A)` is finite-dimensional, and
`ℓ(B) ≤ ℓ(A) + deg B - deg A` for `A ≤ B`. Multiplication by `z ≠ 0` identifies
`L(A + div z)` with `L(A)`.

## Main definitions

* `Belyi.CurveField.Divisor.L A : Submodule ℚ K`, `Belyi.CurveField.Divisor.ell A : ℕ`.
* `Belyi.CurveField.Divisor.mulEquiv A hz : L (A + div z) ≃ₗ[ℚ] L A`.

## Main results

* `Belyi.CurveField.Divisor.L_mono`, `Belyi.CurveField.Divisor.L_eq_bot_of_deg_neg`.
* instance `FiniteDimensional ℚ (L A)`.
* `Belyi.CurveField.Divisor.ell_le_of_le`: `ℓ(B) ≤ ℓ(A) + (deg B - deg A)` for `A ≤ B`.
* `Belyi.CurveField.Divisor.ell_add_div`: `ℓ(A + div z) = ℓ(A)`.
* `Belyi.CurveField.Divisor.ell_le_max`: `ℓ(A) ≤ max 0 (deg A + ℓ(0))`.
-/

open IsLocalRing

namespace Belyi.CurveField

namespace Divisor

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]

/-! ### Definition -/

/-- The Riemann–Roch space `L(A) = {f | f = 0 ∨ ∀ P, ord_P f ≥ -A(P)}`, a `ℚ`-subspace
of `K`. -/
def L (A : Divisor K) : Submodule ℚ K where
  carrier := {f | f = 0 ∨ ∀ P : Place K, -A P ≤ P.ord f}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro f g (rfl | hf) (rfl | hg)
    · simp
    · simpa using Or.inr hg
    · simpa using Or.inr hf
    by_cases hfg : f + g = 0
    · exact Or.inl hfg
    exact Or.inr fun P ↦ (le_min (hf P) (hg P)).trans (P.min_le_ord_add hfg)
  smul_mem' := by
    rintro q f (rfl | hf)
    · simp
    by_cases h : q • f = 0
    · exact Or.inl h
    refine Or.inr fun P ↦ ?_
    rw [Rat.smul_def] at h ⊢
    have hq : (q : K) ≠ 0 := left_ne_zero_of_mul h
    have hf0 : f ≠ 0 := right_ne_zero_of_mul h
    rw [P.ord_mul hq hf0, P.ord_ratCast, zero_add]
    exact hf P

theorem mem_L {A : Divisor K} {f : K} : f ∈ L A ↔ f = 0 ∨ ∀ P : Place K, -A P ≤ P.ord f :=
  Iff.rfl

theorem mem_L_of_ne_zero {A : Divisor K} {f : K} (hf : f ≠ 0) :
    f ∈ L A ↔ 0 ≤ A + div f := by
  rw [mem_L, or_iff_right hf]
  refine forall_congr' fun P ↦ ?_
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, div_apply]
  omega

theorem L_mono {A B : Divisor K} (h : A ≤ B) : L A ≤ L B := by
  rintro f (rfl | hf)
  · exact Or.inl rfl
  exact Or.inr fun P ↦ (neg_le_neg (h P)).trans (hf P)

/-- `L(A) = 0` if `deg A < 0`. -/
theorem L_eq_bot_of_deg_neg {A : Divisor K} (hA : A.deg < 0) : L A = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  by_contra hf0
  have h := deg_nonneg ((mem_L_of_ne_zero hf0).mp hf)
  rw [deg_add, deg_div] at h
  omega

/-- `ℓ(A) = dim_ℚ L(A)`. -/
noncomputable def ell (A : Divisor K) : ℕ := Module.finrank ℚ (L A)

/-! ### Transport along principal divisors -/

theorem mul_mem_L {A : Divisor K} {z f : K} (hz : z ≠ 0) (hf : f ∈ L (A + div z)) :
    f * z ∈ L A := by
  rcases hf with rfl | hf
  · simp
  by_cases hf0 : f = 0
  · simp [hf0]
  refine Or.inr fun P ↦ ?_
  have := hf P
  simp only [Finsupp.coe_add, Pi.add_apply, div_apply] at this
  rw [P.ord_mul hf0 hz]
  omega

theorem mul_inv_mem_L {A : Divisor K} {z g : K} (hz : z ≠ 0) (hg : g ∈ L A) :
    g * z⁻¹ ∈ L (A + div z) := by
  rcases hg with rfl | hg
  · simp
  by_cases hg0 : g = 0
  · simp [hg0]
  refine Or.inr fun P ↦ ?_
  have := hg P
  simp only [Finsupp.coe_add, Pi.add_apply, div_apply]
  rw [P.ord_mul hg0 (inv_ne_zero hz), P.ord_inv]
  omega

/-- Multiplication by `z ≠ 0` identifies `L(A + div z)` with `L(A)`. -/
noncomputable def mulEquiv (A : Divisor K) {z : K} (hz : z ≠ 0) : L (A + div z) ≃ₗ[ℚ] L A where
  toFun f := ⟨f * z, mul_mem_L hz f.2⟩
  invFun g := ⟨g * z⁻¹, mul_inv_mem_L hz g.2⟩
  map_add' f g := Subtype.ext (add_mul _ _ _)
  map_smul' q f := Subtype.ext (smul_mul_assoc _ _ _)
  left_inv f := Subtype.ext (by simp [hz])
  right_inv g := Subtype.ext (by simp [hz])

/-- `ℓ` is invariant under linear equivalence. -/
theorem ell_add_div (A : Divisor K) {z : K} (hz : z ≠ 0) : ell (A + div z) = ell A :=
  (mulEquiv A hz).finrank_eq

/-! ### Adding a place -/

section Step

variable {A : Divisor K} {P : Place K} {π : K}

theorem ne_zero_of_ord_eq_one (hπ : P.ord π = 1) : π ≠ 0 := by
  rintro rfl; simp at hπ

theorem zpow_mul_mem (hπ : P.ord π = 1) {f : K} (hf : f ∈ L (A + Finsupp.single P 1)) :
    π ^ (A P + 1) * f ∈ P.1 := by
  rcases hf with rfl | hf
  · simp
  by_cases hf0 : f = 0
  · simp [hf0]
  apply P.mem_of_ord_nonneg
  rw [P.ord_mul (zpow_ne_zero _ (ne_zero_of_ord_eq_one hπ)) hf0, Place.ord_zpow, hπ]
  have := hf P
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same] at this
  omega

variable (A P) in
/-- The `ℚ`-linear map `L(A + P) → κ(P)`, `f ↦ (π^{A(P)+1} f)(P)`. -/
noncomputable def residueMap (hπ : P.ord π = 1) :
    L (A + Finsupp.single P 1) →ₗ[ℚ] P.ResidueField where
  toFun f := P.residue ⟨π ^ (A P + 1) * f, zpow_mul_mem hπ f.2⟩
  map_add' f g := by
    rw [← map_add]
    congr 1
    apply Subtype.ext
    simp [mul_add]
  map_smul' q f := by
    rw [RingHom.id_apply, Rat.smul_def q (P.residue _), ← P.residue_ratHom q, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [SetLike.val_smul, Rat.smul_def, MulMemClass.coe_mul, Place.coe_ratHom]
    ring

theorem mem_ker_residueMap (hπ : P.ord π = 1) (f : L (A + Finsupp.single P 1)) :
    f ∈ LinearMap.ker (residueMap A P hπ) ↔ (f : K) ∈ L A := by
  classical
  have hπ0 := ne_zero_of_ord_eq_one hπ
  rw [LinearMap.mem_ker]
  change P.residue _ = 0 ↔ _
  rw [P.residue_eq_zero_iff]
  by_cases hf0 : (f : K) = 0
  · simp only [hf0, mul_zero]
    exact ⟨fun _ ↦ Or.inl rfl, fun _ ↦ by
      rw [show (⟨0, _⟩ : P.1) = 0 from rfl]; exact Ideal.zero_mem _⟩
  have hne : π ^ (A P + 1) * (f : K) ≠ 0 := mul_ne_zero (zpow_ne_zero _ hπ0) hf0
  rw [← P.ord_pos_iff_mem_maximalIdeal (a := ⟨_, zpow_mul_mem hπ f.2⟩) hne]
  change 0 < P.ord (π ^ (A P + 1) * (f : K)) ↔ _
  rw [P.ord_mul (zpow_ne_zero _ hπ0) hf0, Place.ord_zpow, hπ, mem_L, or_iff_right hf0]
  have hf := f.2
  rw [mem_L, or_iff_right hf0] at hf
  constructor
  · intro h Q
    by_cases hQ : Q = P
    · subst hQ; omega
    · have := hf Q
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, if_neg (Ne.symm hQ),
        add_zero] at this
      exact this
  · intro h
    have := h P
    omega

/-- **Adding a place** (Stichtenoth, Lemma 1.4.8): if `L(A)` is finite-dimensional, so is
`L(A + P)`, and `ℓ(A + P) ≤ ℓ(A) + deg P`. -/
theorem step (A : Divisor K) (P : Place K) [FiniteDimensional ℚ (L A)] :
    FiniteDimensional ℚ (L (A + Finsupp.single P 1)) ∧
      ell (A + Finsupp.single P 1) ≤ ell A + P.deg := by
  obtain ⟨π, hπ⟩ := P.exists_ord_eq_one
  set φ := residueMap A P hπ
  have hle : L A ≤ L (A + Finsupp.single P 1) :=
    L_mono (le_add_of_nonneg_right (Finsupp.single_nonneg.mpr zero_le_one))
  have hker : LinearMap.ker φ = (L A).comap (L (A + Finsupp.single P 1)).subtype := by
    ext f
    exact mem_ker_residueMap hπ f
  let e : LinearMap.ker φ ≃ₗ[ℚ] L A :=
    (LinearEquiv.ofEq _ _ hker).trans (Submodule.comapSubtypeEquivOfLe hle)
  have hkerfin : FiniteDimensional ℚ (LinearMap.ker φ) := e.symm.finiteDimensional
  have hfin : FiniteDimensional ℚ (L (A + Finsupp.single P 1)) := by
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker φ ?_ ?_⟩
    · exact IsNoetherian.noetherian _
    · rw [top_inf_eq]
      exact Module.Finite.iff_fg.mp hkerfin
  refine ⟨hfin, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 : Module.finrank ℚ (LinearMap.range φ) ≤ P.deg := Submodule.finrank_le _
  rw [e.finrank_eq] at h1
  unfold ell
  omega

theorem step_nat (P : Place K) (m : ℕ) (A : Divisor K) [FiniteDimensional ℚ (L A)] :
    FiniteDimensional ℚ (L (A + Finsupp.single P (m : ℤ))) ∧
      (ell (A + Finsupp.single P (m : ℤ)) : ℤ) ≤ ell A + m * P.deg := by
  induction m with
  | zero =>
    rw [Nat.cast_zero, Finsupp.single_zero, add_zero]
    exact ⟨inferInstance, by simp⟩
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := step (A + Finsupp.single P (m : ℤ)) P
    rw [Nat.cast_succ, Finsupp.single_add, ← add_assoc]
    refine ⟨h3, ?_⟩
    have : ((m : ℤ) + 1) * P.deg = m * P.deg + P.deg := by ring
    omega

theorem aux (D : Divisor K) (hD : 0 ≤ D) (A : Divisor K) [FiniteDimensional ℚ (L A)] :
    FiniteDimensional ℚ (L (A + D)) ∧ (ell (A + D) : ℤ) ≤ ell A + D.deg := by
  classical
  induction D using Finsupp.induction generalizing A with
  | zero =>
    rw [add_zero]
    exact ⟨inferInstance, by simp⟩
  | single_add P b f hPf _ ih =>
    have hfP : f P = 0 := Finsupp.notMem_support_iff.mp hPf
    have hb : 0 ≤ b := by
      have := hD P
      simpa [hfP] using this
    have hf : 0 ≤ f := by
      intro Q
      by_cases hQ : Q = P
      · subst hQ; simp [hfP]
      · have := hD Q
        simpa [Finsupp.single_apply, Ne.symm hQ] using this
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hb
    obtain ⟨h1, h2⟩ := step_nat P m A
    obtain ⟨h3, h4⟩ := ih hf (A + Finsupp.single P (m : ℤ))
    rw [← add_assoc]
    refine ⟨h3, ?_⟩
    rw [deg_add, deg_single]
    omega

end Step

/-! ### Finite-dimensionality and the dimension estimate -/

/-- Every Riemann–Roch space is finite-dimensional (Stichtenoth, Proposition 1.4.9). -/
instance finiteDimensional_L (A : Divisor K) : FiniteDimensional ℚ (L A) := by
  obtain P0 : Place K := Classical.arbitrary _
  set n : ℤ := |A.deg| + 1
  have hn : 0 ≤ n := by positivity
  have hdeg : (A - Finsupp.single P0 n).deg < 0 := by
    rw [deg_sub, deg_single]
    have h1 : (1 : ℤ) ≤ P0.deg := by exact_mod_cast P0.deg_pos
    have h2 := le_abs_self A.deg
    nlinarith
  have hbot := L_eq_bot_of_deg_neg hdeg
  have : FiniteDimensional ℚ (L (A - Finsupp.single P0 n)) := by
    rw [hbot]; infer_instance
  have := (aux (Finsupp.single P0 n) (Finsupp.single_nonneg.mpr hn)
    (A - Finsupp.single P0 n)).1
  rwa [sub_add_cancel] at this

/-- **Dimension estimate** (Stichtenoth, Lemma 1.4.8): for `A ≤ B`,
`ℓ(B) ≤ ℓ(A) + (deg B - deg A)`. -/
theorem ell_le_of_le {A B : Divisor K} (h : A ≤ B) :
    (ell B : ℤ) ≤ ell A + (B.deg - A.deg) := by
  have := (aux (B - A) (sub_nonneg.mpr h) A).2
  rwa [add_sub_cancel, deg_sub] at this

/-- For `A ≤ B`, `deg A - ℓ(A) ≤ deg B - ℓ(B)`. -/
theorem deg_sub_ell_mono {A B : Divisor K} (h : A ≤ B) :
    A.deg - ell A ≤ B.deg - ell B := by
  have := ell_le_of_le h
  omega

theorem ell_mono {A B : Divisor K} (h : A ≤ B) : ell A ≤ ell B :=
  Submodule.finrank_mono (L_mono h)

theorem ell_eq_zero_of_deg_neg {A : Divisor K} (hA : A.deg < 0) : ell A = 0 := by
  rw [ell, L_eq_bot_of_deg_neg hA, finrank_bot]

theorem ell_eq_zero_iff {A : Divisor K} : ell A = 0 ↔ L A = ⊥ := Submodule.finrank_eq_zero

theorem exists_ne_zero_mem_L {A : Divisor K} (h : ell A ≠ 0) : ∃ f ∈ L A, f ≠ 0 :=
  (Submodule.ne_bot_iff _).mp (mt ell_eq_zero_iff.mpr h)

/-- If `L(A) ≠ 0`, then `A` is linearly equivalent to an effective divisor. -/
theorem exists_nonneg_add_div {A : Divisor K} (h : ell A ≠ 0) :
    ∃ z : K, z ≠ 0 ∧ 0 ≤ A + div z := by
  obtain ⟨z, hz, hz0⟩ := exists_ne_zero_mem_L h
  exact ⟨z, hz0, (mem_L_of_ne_zero hz0).mp hz⟩

/-- `ℓ(A) ≤ max 0 (deg A + ℓ(0))` (Stichtenoth, Lemma 1.4.10). -/
theorem ell_le_max (A : Divisor K) : (ell A : ℤ) ≤ max 0 (A.deg + ell (0 : Divisor K)) := by
  by_cases h : ell A = 0
  · rw [h]; exact le_max_left _ _
  obtain ⟨z, hz, hA⟩ := exists_nonneg_add_div h
  have := ell_le_of_le hA
  rw [ell_add_div A hz, deg_add, deg_div, deg_zero] at this
  exact (by omega : (ell A : ℤ) ≤ A.deg + ell (0 : Divisor K)).trans (le_max_right _ _)

end Divisor

end Belyi.CurveField
