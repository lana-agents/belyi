/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib

/-!
# Elementary self-maps of `ℙ¹(ℚ̄)`

This file sets up the point-level framework for the `ℙ¹` part of
S. Mochizuki, *Noncritical Belyi maps*, Math. J. Okayama Univ. **46** (2004), §2
(Lemmas 2.1–2.4 and the `ℙ¹` case of Theorem 2.5).

The Belyi maps constructed there are composites of two kinds of *elementary maps* with
rational coefficients:

* Möbius transformations `x ↦ (a x + b)/(c x + d)` with `a d - b c ≠ 0`, and
* polynomials `p ∈ ℚ[X]` of positive degree.

We model the points of `ℙ¹(ℚ̄)` as `Pt := Option Qbar` (with `none = ∞`) and define, for an
elementary map `h`, its action `h.apply : Pt → Pt` and its ramification index
`h.ramIdx z` at a point `z` (identically `1` for a Möbius map; for a polynomial `p`, the
multiplicity of `z` as a root of `p - p(z)` at finite `z` and `deg p` at `∞`).

For a list `hs = [h₁, …, hₙ]` the composite `H = hₙ ∘ ⋯ ∘ h₁` is `evalComp hs` and its
ramification index is `ramIdxComp hs z = ∏ᵢ ramIdx hᵢ (H_{i-1} z)`.

The predicate `IsNoncriticalBelyi hs S τ` packages the three properties of Theorem 2.5:
`H(S) ⊆ {0, 1, ∞}`, `H(τ) ∉ {0, 1, ∞}`, and `H` is unramified over `ℙ¹ ∖ {0, 1, ∞}`.
The key bookkeeping lemma is `IsNoncriticalBelyi.cons`: to build a noncritical Belyi map
starting with `h`, it suffices to build one for any set `S'` containing `h(S)` and the
images of the ramification points of `h`.

## Main definitions

* `Belyi.NoncriticalP1.ElemMap`, `ElemMap.apply`, `ElemMap.ramIdx`, `ElemMap.degree`;
* `Belyi.NoncriticalP1.evalComp`, `ramIdxComp`, `degreeComp`;
* `Belyi.NoncriticalP1.IsNoncriticalBelyi`.

## Main results

* `ElemMap.one_lt_ramIdx_poly_some_iff`: a polynomial is ramified at a finite point exactly
  where its derivative vanishes;
* `ElemMap.apply_map`: elementary maps commute with `Gal(ℚ̄/ℚ)`;
* `ElemMap.apply_surjective`, `evalComp_surjective`: elementary maps (hence composites) are
  surjective on `ℙ¹(ℚ̄)`, in particular non-constant;
* `IsNoncriticalBelyi.cons`, `IsNoncriticalBelyi.mono`.
-/

namespace Belyi.NoncriticalP1

open Polynomial

/-- The algebraic closure `ℚ̄` of `ℚ`. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

/-- The points of `ℙ¹(ℚ̄)`: `none` is the point `∞`, `some x` is the finite point `x`. -/
abbrev Pt : Type := Option Qbar

/-- The rational point `q ∈ ℙ¹(ℚ) ⊆ ℙ¹(ℚ̄)`. -/
noncomputable def ofRat (q : ℚ) : Pt := some (q : Qbar)

lemma ofRat_injective : Function.Injective ofRat := by
  intro p q h
  simpa [ofRat] using h

/-- The set `{0, 1, ∞} ⊆ ℙ¹(ℚ̄)`. -/
def zeroOneInf : Set Pt := {none, some 0, some 1}

lemma mem_zeroOneInf {z : Pt} : z ∈ zeroOneInf ↔ z = none ∨ z = some 0 ∨ z = some 1 := by
  simp [zeroOneInf]

@[simp] lemma none_mem_zeroOneInf : (none : Pt) ∈ zeroOneInf := by simp [zeroOneInf]

lemma ofRat_mem_zeroOneInf {q : ℚ} : ofRat q ∈ zeroOneInf ↔ q = 0 ∨ q = 1 := by
  simp only [zeroOneInf, ofRat, Set.mem_insert_iff, reduceCtorEq, Option.some.injEq,
    Rat.cast_eq_zero, Set.mem_singleton_iff, false_or]
  norm_cast

/-- An elementary map of `ℙ¹` over `ℚ`: a Möbius transformation `x ↦ (a x + b)/(c x + d)`
with `a d - b c ≠ 0`, or a polynomial of positive degree. -/
inductive ElemMap
  /-- The Möbius transformation `x ↦ (a x + b)/(c x + d)`. -/
  | mob (a b c d : ℚ) (h : a * d - b * c ≠ 0)
  /-- The polynomial map `x ↦ p(x)`, `∞ ↦ ∞`. -/
  | poly (p : ℚ[X]) (h : 0 < p.natDegree)

namespace ElemMap

open Classical in
/-- The action of an elementary map on `ℙ¹(ℚ̄)`. -/
noncomputable def apply : ElemMap → Pt → Pt
  | mob a _ c _ _, none => if c = 0 then none else some ((a / c : ℚ) : Qbar)
  | mob a b c d _, some z =>
      if (c : Qbar) * z + d = 0 then none else some (((a : Qbar) * z + b) / ((c : Qbar) * z + d))
  | poly _ _, none => none
  | poly p _, some z => some (aeval z p)

/-- The ramification index of an elementary map at a point of `ℙ¹(ℚ̄)`: `1` for a Möbius
map; for a polynomial `p`, the multiplicity of `z` as a root of `p - p(z)` at a finite point
`z`, and `deg p` at `∞`. -/
noncomputable def ramIdx : ElemMap → Pt → ℕ
  | mob .., _ => 1
  | poly p _, none => p.natDegree
  | poly p _, some z => ((p.map (algebraMap ℚ Qbar)) - C (aeval z p)).rootMultiplicity z

/-- The degree of an elementary map (`1` for Möbius maps). -/
def degree : ElemMap → ℕ
  | mob .. => 1
  | poly p _ => p.natDegree

lemma degree_pos (h : ElemMap) : 0 < h.degree := by
  cases h with
  | mob => exact Nat.one_pos
  | poly p hp => exact hp

@[simp] lemma ramIdx_mob {a b c d : ℚ} (h : a * d - b * c ≠ 0) (z : Pt) :
    (mob a b c d h).ramIdx z = 1 := rfl

@[simp] lemma apply_poly_none {p : ℚ[X]} (hp : 0 < p.natDegree) :
    (poly p hp).apply none = none := rfl

@[simp] lemma apply_poly_some {p : ℚ[X]} (hp : 0 < p.natDegree) (z : Qbar) :
    (poly p hp).apply (some z) = some (aeval z p) := rfl

lemma apply_poly_ofRat {p : ℚ[X]} (hp : 0 < p.natDegree) (q : ℚ) :
    (poly p hp).apply (ofRat q) = ofRat (p.eval q) := by
  simp only [ofRat, apply_poly_some, Option.some.injEq]
  rw [← eq_ratCast (algebraMap ℚ Qbar), ← eq_ratCast (algebraMap ℚ Qbar),
    aeval_algebraMap_apply_eq_algebraMap_eval]

lemma apply_mob_none {a b c d : ℚ} (h : a * d - b * c ≠ 0) :
    (mob a b c d h).apply none = if c = 0 then none else some ((a / c : ℚ) : Qbar) := rfl

open Classical in
lemma apply_mob_some {a b c d : ℚ} (h : a * d - b * c ≠ 0) (z : Qbar) :
    (mob a b c d h).apply (some z) =
      if (c : Qbar) * z + d = 0 then none
      else some (((a : Qbar) * z + b) / ((c : Qbar) * z + d)) := rfl

lemma apply_mob_some_of_ne {a b c d : ℚ} (h : a * d - b * c ≠ 0) {z : Qbar}
    (hz : (c : Qbar) * z + d ≠ 0) :
    (mob a b c d h).apply (some z) = some (((a : Qbar) * z + b) / ((c : Qbar) * z + d)) := by
  rw [apply_mob_some, if_neg hz]

lemma apply_mob_ofRat {a b c d : ℚ} (h : a * d - b * c ≠ 0) {q : ℚ} (hq : c * q + d ≠ 0) :
    (mob a b c d h).apply (ofRat q) = ofRat ((a * q + b) / (c * q + d)) := by
  have hq' : (c : Qbar) * (q : Qbar) + d ≠ 0 := by exact_mod_cast hq
  rw [ofRat, apply_mob_some_of_ne h hq', ofRat]
  push_cast
  rfl

/-- A polynomial is ramified at a finite point exactly where its derivative vanishes. -/
lemma one_lt_ramIdx_poly_some_iff {p : ℚ[X]} (hp : 0 < p.natDegree) (z : Qbar) :
    1 < (poly p hp).ramIdx (some z) ↔ aeval z (derivative p) = 0 := by
  have hq : (p.map (algebraMap ℚ Qbar)) - C (aeval z p) ≠ 0 := by
    intro h0
    have := congrArg natDegree h0
    rw [natDegree_sub_C, natDegree_map] at this
    simp at this
    omega
  change 1 < ((p.map (algebraMap ℚ Qbar)) - C (aeval z p)).rootMultiplicity z ↔ _
  rw [one_lt_rootMultiplicity_iff_isRoot hq]
  simp [IsRoot, eval_map_algebraMap, derivative_map]

lemma one_lt_ramIdx_poly_some {p : ℚ[X]} {hp : 0 < p.natDegree} {z : Qbar}
    (h : 1 < (poly p hp).ramIdx (some z)) : aeval z (derivative p) = 0 :=
  (one_lt_ramIdx_poly_some_iff hp z).mp h

/-- Elementary maps are defined over `ℚ`: they commute with `Gal(ℚ̄/ℚ)`. -/
lemma apply_map (σ : Qbar ≃ₐ[ℚ] Qbar) (h : ElemMap) (z : Pt) :
    h.apply (z.map σ) = (h.apply z).map σ := by
  cases h with
  | mob a b c d hdet =>
    cases z with
    | none =>
      simp only [Option.map_none, apply_mob_none]
      split_ifs <;> simp [map_ratCast]
    | some z =>
      simp only [Option.map_some, apply_mob_some]
      have key : (c : Qbar) * σ z + d = σ ((c : Qbar) * z + d) := by
        simp [map_ratCast]
      rw [key, map_eq_zero_iff σ σ.injective]
      split_ifs
      · rfl
      · simp [map_ratCast, map_div₀]
  | poly p hp =>
    cases z with
    | none => rfl
    | some z =>
      simp [aeval_algHom_apply]

/-- A Möbius transformation is surjective on `ℙ¹(ℚ̄)`. -/
lemma apply_mob_surjective {a b c d : ℚ} (h : a * d - b * c ≠ 0) :
    Function.Surjective (mob a b c d h).apply := by
  intro w
  cases w with
  | none =>
    by_cases hc : c = 0
    · exact ⟨none, by simp [apply_mob_none, hc]⟩
    · refine ⟨some (-(d : Qbar) / c), ?_⟩
      have hc' : (c : Qbar) ≠ 0 := by exact_mod_cast hc
      rw [apply_mob_some, if_pos]
      field_simp
      ring
  | some v =>
    by_cases hv : c ≠ 0 ∧ v = ((a / c : ℚ) : Qbar)
    · exact ⟨none, by simp [apply_mob_none, hv.1, hv.2]⟩
    · have hden : (c : Qbar) * v - a ≠ 0 := by
        intro h0
        by_cases hc : c = 0
        · subst hc
          have ha : a ≠ 0 := by rintro rfl; simp at h
          have h0' : (a : Qbar) = 0 := by simpa using h0
          exact ha (by exact_mod_cast h0')
        · apply hv
          refine ⟨hc, ?_⟩
          have hc' : (c : Qbar) ≠ 0 := by exact_mod_cast hc
          push_cast
          field_simp
          linear_combination h0
      have hdet : (a : Qbar) * d - b * c ≠ 0 := by exact_mod_cast h
      obtain ⟨z, hz⟩ : ∃ z : Qbar, z * ((c : Qbar) * v - a) = b - d * v :=
        ⟨_, div_mul_cancel₀ _ hden⟩
      refine ⟨some z, ?_⟩
      have hne : (c : Qbar) * z + d ≠ 0 := by
        intro h0
        apply hdet
        linear_combination ((a : Qbar) - c * v) * h0 + (c : Qbar) * hz
      rw [apply_mob_some_of_ne h hne, Option.some.injEq, div_eq_iff hne]
      linear_combination (-1 : Qbar) * hz

/-- A polynomial of positive degree is surjective on `ℙ¹(ℚ̄)`. -/
lemma apply_poly_surjective {p : ℚ[X]} (hp : 0 < p.natDegree) :
    Function.Surjective (poly p hp).apply := by
  intro w
  cases w with
  | none => exact ⟨none, rfl⟩
  | some v =>
    have hdeg : (p.map (algebraMap ℚ Qbar) - C v).degree ≠ 0 := by
      rw [degree_sub_C (by rw [degree_map]; exact natDegree_pos_iff_degree_pos.mp hp),
        degree_map]
      exact (natDegree_pos_iff_degree_pos.mp hp).ne'
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨some z, ?_⟩
    simp only [IsRoot, eval_sub, eval_map_algebraMap, eval_C, sub_eq_zero] at hz
    simp [hz]

/-- Elementary maps are surjective on `ℙ¹(ℚ̄)`. -/
lemma apply_surjective (h : ElemMap) : Function.Surjective h.apply := by
  cases h with
  | mob a b c d hdet => exact apply_mob_surjective hdet
  | poly p hp => exact apply_poly_surjective hp

end ElemMap

/-- The composite `H = hₙ ∘ ⋯ ∘ h₁` of a list `[h₁, …, hₙ]` of elementary maps (the head of
the list is applied first). -/
noncomputable def evalComp : List ElemMap → Pt → Pt
  | [], z => z
  | h :: hs, z => evalComp hs (h.apply z)

/-- The ramification index of the composite `H = hₙ ∘ ⋯ ∘ h₁` at `z`:
`∏ᵢ ramIdx hᵢ (H_{i-1} z)` where `H_{i-1} = h_{i-1} ∘ ⋯ ∘ h₁`. -/
noncomputable def ramIdxComp : List ElemMap → Pt → ℕ
  | [], _ => 1
  | h :: hs, z => h.ramIdx z * ramIdxComp hs (h.apply z)

/-- The degree of the composite: the product of the degrees. -/
def degreeComp (hs : List ElemMap) : ℕ := (hs.map ElemMap.degree).prod

@[simp] lemma evalComp_nil (z : Pt) : evalComp [] z = z := rfl

@[simp] lemma evalComp_cons (h : ElemMap) (hs : List ElemMap) (z : Pt) :
    evalComp (h :: hs) z = evalComp hs (h.apply z) := rfl

@[simp] lemma ramIdxComp_nil (z : Pt) : ramIdxComp [] z = 1 := rfl

@[simp] lemma ramIdxComp_cons (h : ElemMap) (hs : List ElemMap) (z : Pt) :
    ramIdxComp (h :: hs) z = h.ramIdx z * ramIdxComp hs (h.apply z) := rfl

lemma evalComp_append (hs hs' : List ElemMap) (z : Pt) :
    evalComp (hs ++ hs') z = evalComp hs' (evalComp hs z) := by
  induction hs generalizing z with
  | nil => rfl
  | cons h hs ih => exact ih _

lemma degreeComp_pos (hs : List ElemMap) : 0 < degreeComp hs := by
  unfold degreeComp
  induction hs with
  | nil => simp
  | cons h hs ih =>
    rw [List.map_cons, List.prod_cons]
    exact Nat.mul_pos h.degree_pos ih

/-- Composites of elementary maps are surjective on `ℙ¹(ℚ̄)`; in particular non-constant. -/
lemma evalComp_surjective (hs : List ElemMap) : Function.Surjective (evalComp hs) := by
  induction hs with
  | nil => exact Function.surjective_id
  | cons h hs ih => exact ih.comp h.apply_surjective

lemma evalComp_map (σ : Qbar ≃ₐ[ℚ] Qbar) (hs : List ElemMap) (z : Pt) :
    evalComp hs (z.map σ) = (evalComp hs z).map σ := by
  induction hs generalizing z with
  | nil => rfl
  | cons h hs ih => simp [ElemMap.apply_map, ih]

/-- `H = hₙ ∘ ⋯ ∘ h₁` is a *noncritical Belyi map* for `(S, τ)`: it maps `S` into
`{0, 1, ∞}`, maps `τ` outside `{0, 1, ∞}`, and is unramified over `ℙ¹ ∖ {0, 1, ∞}`
(conditions (a)–(c) of Mochizuki's Theorem 2.5 for `X = ℙ¹`). -/
structure IsNoncriticalBelyi (hs : List ElemMap) (S : Set Pt) (τ : Pt) : Prop where
  maps_to : ∀ z ∈ S, evalComp hs z ∈ zeroOneInf
  tau_notMem : evalComp hs τ ∉ zeroOneInf
  unramified : ∀ z, 1 < ramIdxComp hs z → evalComp hs z ∈ zeroOneInf

namespace IsNoncriticalBelyi

variable {hs : List ElemMap} {S S' : Set Pt} {τ : Pt}

lemma mono (hg : IsNoncriticalBelyi hs S τ) (hS : S' ⊆ S) : IsNoncriticalBelyi hs S' τ :=
  ⟨fun z hz => hg.maps_to z (hS hz), hg.tau_notMem, hg.unramified⟩

lemma nil (hS : S ⊆ zeroOneInf) (hτ : τ ∉ zeroOneInf) : IsNoncriticalBelyi [] S τ :=
  ⟨hS, hτ, fun z hz => by simp at hz⟩

/-- The bookkeeping step: if `S'` contains `h(S)` and the images of all ramification points
of `h`, then a noncritical Belyi map for `(S', h(τ))` precomposed with `h` is one for
`(S, τ)`. -/
lemma cons (h : ElemMap) (hS : ∀ z ∈ S, h.apply z ∈ S')
    (hram : ∀ z, 1 < h.ramIdx z → h.apply z ∈ S')
    (hg : IsNoncriticalBelyi hs S' (h.apply τ)) : IsNoncriticalBelyi (h :: hs) S τ := by
  refine ⟨fun z hz => hg.maps_to _ (hS z hz), hg.tau_notMem, fun z hz => ?_⟩
  rw [ramIdxComp_cons] at hz
  by_cases h1 : 1 < h.ramIdx z
  · exact hg.maps_to _ (hram z h1)
  · by_cases h2 : 1 < ramIdxComp hs (h.apply z)
    · exact hg.unramified _ h2
    · exfalso
      push Not at h1 h2
      have : h.ramIdx z * ramIdxComp hs (h.apply z) ≤ 1 * 1 := Nat.mul_le_mul h1 h2
      omega

/-- The `cons` step for a Möbius transformation, which is unramified. -/
lemma cons_mob {a b c d : ℚ} (hdet : a * d - b * c ≠ 0)
    (hS : ∀ z ∈ S, (ElemMap.mob a b c d hdet).apply z ∈ S')
    (hg : IsNoncriticalBelyi hs S' ((ElemMap.mob a b c d hdet).apply τ)) :
    IsNoncriticalBelyi (ElemMap.mob a b c d hdet :: hs) S τ :=
  cons _ hS (fun z hz => by simp at hz) hg

/-- The `cons` step for a polynomial: `S'` must contain `∞`, `p(S)`, and the critical values
`p(z)` (`p'(z) = 0`). -/
lemma cons_poly {p : ℚ[X]} (hp : 0 < p.natDegree)
    (hS : ∀ z ∈ S, (ElemMap.poly p hp).apply z ∈ S') (hinf : (none : Pt) ∈ S')
    (hcrit : ∀ z : Qbar, aeval z (derivative p) = 0 → some (aeval z p) ∈ S')
    (hg : IsNoncriticalBelyi hs S' ((ElemMap.poly p hp).apply τ)) :
    IsNoncriticalBelyi (ElemMap.poly p hp :: hs) S τ := by
  refine cons _ hS (fun z hz => ?_) hg
  cases z with
  | none => exact hinf
  | some z => exact hcrit z (ElemMap.one_lt_ramIdx_poly_some hz)

end IsNoncriticalBelyi

end Belyi.NoncriticalP1
