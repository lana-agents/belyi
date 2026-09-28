/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.NoncriticalBasic

/-!
# Composing functions on a curve with elementary maps of `ℙ¹`

For a nonconstant function `φ` on a curve and an elementary map `h` of `ℙ¹` over `ℚ`
(a Möbius transformation or a polynomial, `Belyi.NoncriticalP1.ElemMap`), the composite
`h ∘ φ` is the element `applyK h φ` of the function field. We prove that values and
ramification indices are compatible with composition: at an algebraic point `x`,

* `(h ∘ φ)(x) = h(φ(x))`, and
* `e_P(h ∘ φ) = e_P(φ) · e_{φ(x)}(h)` (multiplicativity of ramification indices),

and the same for composites of lists of elementary maps
(`Belyi.CurveField.Noncritical.compK_spec`).

For a polynomial `p`, the multiplicativity comes from `ord_aeval_eq`: the minimal polynomial
`m` of the residue of `p(φ)` satisfies `m ∘ p = (p - p(φ(x))) · q` over `ℚ̄` with
`q(p(φ(x))) ≠ 0`. A Möbius transformation is decomposed into affine maps and the inversion
`φ ↦ φ⁻¹`, which preserves ramification indices.
-/

open Polynomial
open Belyi.NoncriticalP1 (Pt Qbar ElemMap evalComp ramIdxComp)

namespace Belyi.CurveField.Noncritical

/-! ### A lemma on root multiplicities -/

/-- If `M` is separable with root `b` and `Q(a) = b`, then the multiplicity of `a` as a root of
`M ∘ Q` is that of `a` as a root of `Q - b`. -/
theorem rootMultiplicity_comp_of_separable {F : Type*} [Field F] {M Q : F[X]} {a b : F}
    (hM : M.Separable) (hb : M.IsRoot b) (hQa : Q.eval a = b) (hQ : Q - C b ≠ 0) :
    (M.comp Q).rootMultiplicity a = (Q - C b).rootMultiplicity a := by
  set R := M /ₘ (X - C b)
  have hMR : (X - C b) * R = M := mul_divByMonic_eq_iff_isRoot.mpr hb
  have hM0 := hM.ne_zero
  have hR0 : R ≠ 0 := by rintro h; rw [h, mul_zero] at hMR; exact hM0 hMR.symm
  have hRb : ¬ R.IsRoot b := by
    intro hRb
    have h1 := rootMultiplicity_le_one_of_separable hM b
    rw [← hMR, rootMultiplicity_mul (by rw [hMR]; exact hM0), rootMultiplicity_X_sub_C_self]
      at h1
    have := (rootMultiplicity_pos hR0).mpr hRb
    omega
  have hRQ : ¬ (R.comp Q).IsRoot a := by
    rwa [IsRoot, eval_comp, hQa]
  have hRQ0 : R.comp Q ≠ 0 := by rintro h; apply hRQ; rw [h]; exact eval_zero
  have hcomp : M.comp Q = (Q - C b) * R.comp Q := by
    rw [← hMR, mul_comp, sub_comp, X_comp, C_comp]
  rw [hcomp, rootMultiplicity_mul (mul_ne_zero hQ hRQ0), rootMultiplicity_eq_zero hRQ, add_zero]

variable {K : Type*} [Field K] [CharZero K] [IsCurveField K] {φ : K}

/-! ### Polynomials -/

omit [IsCurveField K] in
theorem transcendental_aeval (hφ : Transcendental ℚ φ) {p : ℚ[X]} (hp : 0 < p.natDegree) :
    Transcendental ℚ (aeval φ p) :=
  hφ.aeval p hp.ne' (mem_nonZeroDivisors_of_ne_zero
    (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hp)))

/-- At a pole of `φ`, `ord_P (p(φ)) = deg p · ord_P φ`. -/
theorem ord_aeval_of_notMem (hφ : Transcendental ℚ φ) {P : Place K} (h : φ ∉ P.1) {p : ℚ[X]}
    (hp : p ≠ 0) : P.ord (aeval φ p) = p.natDegree * P.ord φ := by
  have hφ0 : φ ≠ 0 := ne_zero_of_transcendental hφ
  letI : Invertible φ := invertibleOfNonzero hφ0
  have key : aeval φ⁻¹ p.reverse * φ ^ p.natDegree = aeval φ p := by
    have := eval₂_reverse_mul_pow (algebraMap ℚ K) φ p
    rwa [invOf_eq_inv] at this
  have hneg := (P.ord_neg_iff).mpr h
  have hpos : 0 < P.ord φ⁻¹ := by rw [P.ord_inv]; omega
  have hinv : φ⁻¹ ∈ P.1 := P.mem_of_ord_nonneg hpos.le
  have hres : P.residue ⟨aeval φ⁻¹ p.reverse, P.aeval_mem hinv _⟩ ≠ 0 := by
    rw [P.residue_aeval hinv, P.residue_eq_zero_of_ord_pos hpos, ← coeff_zero_eq_aeval_zero',
      coeff_zero_reverse]
    exact (map_ne_zero_iff _ (algebraMap ℚ _).injective).mpr (leadingCoeff_ne_zero.mpr hp)
  have h0 : aeval φ⁻¹ p.reverse ≠ 0 := by
    rintro h0
    apply hres
    rw [show (⟨aeval φ⁻¹ p.reverse, P.aeval_mem hinv _⟩ : P.1) = 0 from Subtype.ext h0,
      map_zero]
  rw [← key, P.ord_mul h0 (pow_ne_zero _ hφ0), P.ord_eq_zero_of_residue_ne_zero _ hres,
    P.ord_pow, zero_add]

/-- The elementary polynomial step: values and ramification indices of `p(φ)`. -/
theorem poly_spec (hφ : Transcendental ℚ φ) (x : QbarPoint K) {p : ℚ[X]}
    (hp : 0 < p.natDegree) :
    val x (aeval φ p) = (ElemMap.poly p hp).apply (val x φ) ∧
      ramIdx x.P (aeval φ p) = ramIdx x.P φ * (ElemMap.poly p hp).ramIdx (val x φ) := by
  have hp0 : p ≠ 0 := ne_zero_of_natDegree_gt hp
  by_cases h : φ ∈ x.P.1
  · have h' := x.P.aeval_mem h p
    have hev := x.eval_aeval h p
    rw [val_of_mem h, val_of_mem h', hev]
    refine ⟨rfl, ?_⟩
    set m := minpoly ℚ (x.P.residue ⟨aeval φ p, h'⟩)
    have hr := x.P.isIntegral_residue ⟨aeval φ p, h'⟩
    have hm0 : m ≠ 0 := minpoly.ne_zero hr
    have hcomp0 : m.comp p ≠ 0 := by
      rw [Ne, comp_eq_zero_iff, not_or]
      refine ⟨hm0, fun ⟨_, h2⟩ ↦ ?_⟩
      have := congrArg natDegree h2
      rw [natDegree_C] at this
      omega
    rw [ramIdx_of_mem h', ← aeval_comp, ord_aeval_eq hφ x h hcomp0, Polynomial.map_comp]
    congr 2
    refine rootMultiplicity_comp_of_separable ((minpoly.irreducible hr).separable.map) ?_
      (by rw [eval_map_algebraMap]) ?_
    · rw [IsRoot, eval_map_algebraMap, ← hev]
      exact (aeval_algHom_apply x.σ.toRatAlgHom _ m).trans (by
        simp [m, minpoly.aeval])
    · intro h0
      have := congrArg natDegree h0
      rw [natDegree_sub_C, natDegree_map, natDegree_zero] at this
      omega
  · have hord := ord_aeval_of_notMem hφ h hp0
    have hneg := (x.P.ord_neg_iff).mpr h
    have h' : aeval φ p ∉ x.P.1 := by
      rw [← x.P.ord_neg_iff, hord]
      exact mul_neg_of_pos_of_neg (by exact_mod_cast hp) hneg
    rw [val_of_notMem h, val_of_notMem h', ramIdx_of_notMem h', ramIdx_of_notMem h, hord]
    refine ⟨rfl, ?_⟩
    change _ = _ * (p.natDegree : ℤ)
    ring

/-- A polynomial of degree one is unramified. -/
theorem ElemMap.ramIdx_poly_of_natDegree_eq_one {p : ℚ[X]} (hp : 0 < p.natDegree)
    (h1 : p.natDegree = 1) (z : Pt) : (ElemMap.poly p hp).ramIdx z = 1 := by
  cases z with
  | none => exact h1
  | some z =>
    have hq : (p.map (algebraMap ℚ Qbar)) - C (aeval z p) ≠ 0 := by
      intro h0
      have := congrArg natDegree h0
      rw [natDegree_sub_C, natDegree_map, natDegree_zero] at this
      omega
    refine le_antisymm (not_lt.mp fun hlt ↦ ?_) ?_
    · have := (ElemMap.one_lt_ramIdx_poly_some_iff hp z).mp hlt
      rw [eq_X_add_C_of_natDegree_le_one h1.le] at this
      simp only [derivative_add, derivative_C_mul_X, derivative_C, add_zero, aeval_C] at this
      have hc : p.coeff 1 ≠ 0 := by
        rw [← h1]; exact leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hp)
      exact hc ((map_eq_zero_iff _ (algebraMap ℚ Qbar).injective).mp this)
    · change 0 < ((p.map (algebraMap ℚ Qbar)) - C (aeval z p)).rootMultiplicity z
      rw [rootMultiplicity_pos hq]
      simp [IsRoot, eval_map_algebraMap]

/-! ### Inversion -/

/-- The inversion `z ↦ 1/z` of `ℙ¹(ℚ̄)`. -/
noncomputable def invPt : Pt → Pt
  | none => some 0
  | some a => if a = 0 then none else some a⁻¹

/-- If `ord_P φ = 0`, then `e_P(φ)` is a multiple of `e_P(φ⁻¹)`. -/
theorem exists_ramIdx_eq_mul_inv (hφ : Transcendental ℚ φ) (x : QbarPoint K)
    (h0 : x.P.ord φ = 0) : ∃ k : ℕ, ramIdx x.P φ = ramIdx x.P φ⁻¹ * k := by
  have hφ0 : φ ≠ 0 := ne_zero_of_transcendental hφ
  obtain ⟨h, hinv⟩ := (x.P.ord_eq_zero_iff hφ0).mp h0
  set m := minpoly ℚ (x.P.residue ⟨φ, h⟩)
  have hm0 : m ≠ 0 := minpoly.ne_zero (x.P.isIntegral_residue _)
  letI : Invertible φ := invertibleOfNonzero hφ0
  have key : aeval φ⁻¹ m.reverse * φ ^ m.natDegree = aeval φ m := by
    have := eval₂_reverse_mul_pow (algebraMap ℚ K) φ m
    rwa [invOf_eq_inv] at this
  have hr0 : m.reverse ≠ 0 := by rwa [Ne, reverse_eq_zero]
  have hne : aeval φ⁻¹ m.reverse ≠ 0 := fun h0 ↦
    transcendental_inv hφ ⟨_, hr0, h0⟩
  rw [ramIdx_of_mem h, ← key, x.P.ord_mul hne (pow_ne_zero _ hφ0), x.P.ord_pow, h0, mul_zero,
    add_zero, ord_aeval_eq (transcendental_inv hφ) x hinv hr0]
  exact ⟨_, rfl⟩

/-- The inversion step: values and ramification indices of `φ⁻¹`. -/
theorem inv_spec (hφ : Transcendental ℚ φ) (x : QbarPoint K) :
    val x φ⁻¹ = invPt (val x φ) ∧ ramIdx x.P φ⁻¹ = ramIdx x.P φ := by
  have hφ0 : φ ≠ 0 := ne_zero_of_transcendental hφ
  have hφi0 : φ⁻¹ ≠ 0 := inv_ne_zero hφ0
  rcases lt_trichotomy (x.P.ord φ) 0 with hlt | h0 | hgt
  · have hi : 0 < x.P.ord φ⁻¹ := by rw [x.P.ord_inv]; omega
    rw [val_of_notMem ((x.P.ord_neg_iff).mp hlt), (val_eq_some_zero_iff hφi0).mpr hi,
      ramIdx_of_ord_pos hi, ramIdx_of_ord_neg hlt, x.P.ord_inv]
    exact ⟨rfl, rfl⟩
  · obtain ⟨h, hinv⟩ := (x.P.ord_eq_zero_iff hφ0).mp h0
    have ha : x.eval φ h ≠ 0 := by
      rw [Ne, x.eval_eq_zero_iff h hφ0]; omega
    refine ⟨?_, ?_⟩
    · rw [val_of_mem h, val_of_mem hinv, x.eval_inv h hinv]
      simp [invPt, ha]
    · obtain ⟨k₁, hk₁⟩ := exists_ramIdx_eq_mul_inv hφ x h0
      obtain ⟨k₂, hk₂⟩ := exists_ramIdx_eq_mul_inv (transcendental_inv hφ) x
        (by rw [x.P.ord_inv, h0, neg_zero])
      rw [inv_inv] at hk₂
      have e₁ := ramIdx_pos hφ x.P
      have e₂ := ramIdx_pos (transcendental_inv hφ) x.P
      have hk₁' : (1 : ℤ) ≤ k₁ := by
        rcases Nat.eq_zero_or_pos k₁ with h | h
        · rw [h, Nat.cast_zero, mul_zero] at hk₁; omega
        · exact_mod_cast h
      have hk₂' : (1 : ℤ) ≤ k₂ := by
        rcases Nat.eq_zero_or_pos k₂ with h | h
        · rw [h, Nat.cast_zero, mul_zero] at hk₂; omega
        · exact_mod_cast h
      nlinarith
  · have hi : x.P.ord φ⁻¹ < 0 := by rw [x.P.ord_inv]; omega
    rw [(val_eq_some_zero_iff hφ0).mpr hgt, val_of_notMem ((x.P.ord_neg_iff).mp hi),
      ramIdx_of_ord_pos hgt, ramIdx_of_ord_neg hi, x.P.ord_inv, neg_neg]
    simp [invPt]

/-! ### Möbius transformations -/

/-- A Möbius transformation with `c = 0` is an affine polynomial map. -/
theorem mob_apply_eq_poly {a b d : ℚ} (hdet : a * d - b * 0 ≠ 0)
    (hp : 0 < (C (a / d) * X + C (b / d)).natDegree) (z : Pt) :
    (ElemMap.mob a b 0 d hdet).apply z = (ElemMap.poly _ hp).apply z := by
  have hd : (d : Qbar) ≠ 0 := by
    have : d ≠ 0 := by rintro rfl; simp at hdet
    exact_mod_cast this
  cases z with
  | none => simp [ElemMap.apply_mob_none]
  | some z =>
    rw [ElemMap.apply_mob_some_of_ne _ (by simpa using hd), ElemMap.apply_poly_some]
    simp only [Rat.cast_zero, zero_mul, zero_add, map_add, map_mul, aeval_C, aeval_X,
      eq_ratCast, Rat.cast_div, Option.some.injEq]
    field_simp

/-- A Möbius transformation with `c ≠ 0` is `z ↦ a/c + k/(cz + d)`, `k = (bc - ad)/c`. -/
theorem mob_apply_eq_comp {a b c d : ℚ} (hdet : a * d - b * c ≠ 0) (hc : c ≠ 0)
    (hp₁ : 0 < (C c * X + C d).natDegree)
    (hp₂ : 0 < (C ((b * c - a * d) / c) * X + C (a / c)).natDegree) (z : Pt) :
    (ElemMap.mob a b c d hdet).apply z =
      (ElemMap.poly _ hp₂).apply (invPt ((ElemMap.poly _ hp₁).apply z)) := by
  have hc' : (c : Qbar) ≠ 0 := by exact_mod_cast hc
  cases z with
  | none =>
    simp [ElemMap.apply_mob_none, hc, invPt]
  | some z =>
    rw [ElemMap.apply_mob_some, ElemMap.apply_poly_some]
    simp only [map_add, map_mul, aeval_C, aeval_X, eq_ratCast]
    by_cases hz : (c : Qbar) * z + d = 0
    · simp [hz, invPt]
    · rw [if_neg hz]
      simp only [invPt, hz, if_false, ElemMap.apply_poly_some, map_add, map_mul, aeval_C,
        aeval_X, eq_ratCast, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Option.some.injEq]
      have hz' : z * (c : Qbar) + d ≠ 0 := by rwa [mul_comm]
      field_simp
      ring

omit [IsCurveField K] in
/-- The composite `h ∘ φ` of a function `φ` with an elementary map `h`. -/
noncomputable def applyK : ElemMap → K → K
  | .mob a b c d _, f => ((a : K) * f + b) / ((c : K) * f + d)
  | .poly p _, f => aeval f p

omit [IsCurveField K] in
/-- The composite `hₙ ∘ ⋯ ∘ h₁ ∘ φ` (the head of the list is applied first). -/
noncomputable def compK : List ElemMap → K → K
  | [], f => f
  | h :: hs, f => compK hs (applyK h f)

/-- The Möbius step: values and ramification indices of `(aφ + b)/(cφ + d)`. -/
theorem mob_spec (hφ : Transcendental ℚ φ) (x : QbarPoint K) {a b c d : ℚ}
    (hdet : a * d - b * c ≠ 0) :
    Transcendental ℚ (applyK (.mob a b c d hdet) φ) ∧
      val x (applyK (.mob a b c d hdet) φ) = (ElemMap.mob a b c d hdet).apply (val x φ) ∧
      ramIdx x.P (applyK (.mob a b c d hdet) φ) = ramIdx x.P φ := by
  by_cases hc : c = 0
  · subst hc
    have hd : d ≠ 0 := by rintro rfl; simp at hdet
    have ha : a / d ≠ 0 := div_ne_zero (by rintro rfl; simp at hdet) hd
    have hp1 : (C (a / d) * X + C (b / d)).natDegree = 1 := natDegree_linear ha
    have hp : 0 < (C (a / d) * X + C (b / d)).natDegree := by omega
    have heq : applyK (.mob a b 0 d hdet) φ = aeval φ (C (a / d) * X + C (b / d)) := by
      have hd' : (d : K) ≠ 0 := by exact_mod_cast hd
      simp only [applyK, map_add, map_mul, aeval_C, aeval_X, eq_ratCast, Rat.cast_div,
        Rat.cast_zero, zero_mul, zero_add]
      field_simp
    obtain ⟨hv, he⟩ := poly_spec hφ x hp
    rw [heq, hv, he, ElemMap.ramIdx_poly_of_natDegree_eq_one hp hp1, Nat.cast_one, mul_one,
      mob_apply_eq_poly hdet hp]
    exact ⟨transcendental_aeval hφ hp, rfl, rfl⟩
  · have hk : (b * c - a * d) / c ≠ 0 :=
      div_ne_zero (fun h ↦ hdet (by linear_combination -h)) hc
    have hp₁1 : (C c * X + C d).natDegree = 1 := natDegree_linear hc
    have hp₂1 : (C ((b * c - a * d) / c) * X + C (a / c)).natDegree = 1 := natDegree_linear hk
    have hp₁ : 0 < (C c * X + C d).natDegree := by omega
    have hp₂ : 0 < (C ((b * c - a * d) / c) * X + C (a / c)).natDegree := by omega
    have hφ₁ := transcendental_aeval hφ hp₁
    have hφ₂ := transcendental_inv hφ₁
    have hden : (c : K) * φ + d ≠ 0 := by
      have := ne_zero_of_transcendental hφ₁
      simpa using this
    have heq : applyK (.mob a b c d hdet) φ =
        aeval (aeval φ (C c * X + C d))⁻¹ (C ((b * c - a * d) / c) * X + C (a / c)) := by
      have hc' : (c : K) ≠ 0 := by exact_mod_cast hc
      simp only [applyK, map_add, map_mul, aeval_C, aeval_X, eq_ratCast, Rat.cast_div,
        Rat.cast_sub, Rat.cast_mul]
      have hden' : φ * (c : K) + d ≠ 0 := by rwa [mul_comm]
      field_simp
      ring
    obtain ⟨hv₁, he₁⟩ := poly_spec hφ x hp₁
    obtain ⟨hv₂, he₂⟩ := inv_spec hφ₁ x
    obtain ⟨hv₃, he₃⟩ := poly_spec hφ₂ x hp₂
    rw [heq, hv₃, he₃, hv₂, he₂, hv₁, he₁, ElemMap.ramIdx_poly_of_natDegree_eq_one hp₁ hp₁1,
      ElemMap.ramIdx_poly_of_natDegree_eq_one hp₂ hp₂1, mob_apply_eq_comp hdet hc hp₁ hp₂]
    exact ⟨transcendental_aeval hφ₂ hp₂, rfl, by simp⟩

/-! ### Composites -/

/-- The elementary step: values and ramification indices of `h ∘ φ`. -/
theorem applyK_spec (hφ : Transcendental ℚ φ) (x : QbarPoint K) (h : ElemMap) :
    Transcendental ℚ (applyK h φ) ∧ val x (applyK h φ) = h.apply (val x φ) ∧
      ramIdx x.P (applyK h φ) = ramIdx x.P φ * h.ramIdx (val x φ) := by
  cases h with
  | mob a b c d hdet =>
    obtain ⟨h1, h2, h3⟩ := mob_spec hφ x hdet
    exact ⟨h1, h2, by rw [h3, ElemMap.ramIdx_mob, Nat.cast_one, mul_one]⟩
  | poly p hp =>
    obtain ⟨h2, h3⟩ := poly_spec hφ x hp
    exact ⟨transcendental_aeval hφ hp, h2, h3⟩

/-- **Composites**: for `H = hₙ ∘ ⋯ ∘ h₁`, the composite `H ∘ φ` is nonconstant, its value at
`x` is `H(φ(x))`, and `e_P(H ∘ φ) = e_P(φ) · e_{φ(x)}(H)`. -/
theorem compK_spec (x : QbarPoint K) (hs : List ElemMap) {φ : K} (hφ : Transcendental ℚ φ) :
    Transcendental ℚ (compK hs φ) ∧ val x (compK hs φ) = evalComp hs (val x φ) ∧
      ramIdx x.P (compK hs φ) = ramIdx x.P φ * ramIdxComp hs (val x φ) := by
  induction hs generalizing φ with
  | nil => exact ⟨hφ, rfl, by simp [compK]⟩
  | cons h hs ih =>
    obtain ⟨h1, h2, h3⟩ := applyK_spec hφ x h
    obtain ⟨i1, i2, i3⟩ := ih h1
    refine ⟨i1, ?_, ?_⟩
    · change val x (compK hs (applyK h φ)) = _
      rw [i2, h2]
      rfl
    · change ramIdx x.P (compK hs (applyK h φ)) = _
      rw [i3, h3, h2, NoncriticalP1.ramIdxComp_cons]
      push_cast
      ring

end Belyi.CurveField.Noncritical
