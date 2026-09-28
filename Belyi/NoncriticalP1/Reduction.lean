/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.NoncriticalP1.Analytic
import Belyi.NoncriticalP1.Rational
import Belyi.Polynomial.CritVal

/-!
# Reduction to the rational case

This file provides the individual steps of the proof of
S. Mochizuki, *Noncritical Belyi maps*, Math. J. Okayama Univ. **46** (2004), Lemma 2.4
(reduction to the rational case), which are assembled into the nested induction on
`(m(S), d(S))` in `Belyi.NoncriticalP1.Main`.

Throughout, a branch set is `T ∪ {∞}` for a finite `T ⊆ ℚ̄` stable under `Gal(ℚ̄/ℚ)`
(`Belyi.NoncriticalP1.IsGalStable`), and the prescribed point is a rational `τ ∉ T`.

## Main results

* `Belyi.NoncriticalP1.normalize_step`: after the Möbius map of Lemma 2.3 (with `C = 9`) we may
  assume that `T` lies in the closed unit disc and `τ = 9`; degrees over `ℚ` do not grow and
  the number of points of top degree does not grow.
* `Belyi.NoncriticalP1.rational_step`: if moreover `T ⊆ ℚ`, Lemma 2.2
  (`Belyi.NoncriticalP1.exists_isNoncriticalBelyi_rat`) applies.
* `Belyi.NoncriticalP1.minpoly_step`: the induction step of Lemma 2.4: for `σ₀ ∈ T` of
  maximal degree `d ≥ 2` with minimal polynomial `f₀`, the new branch set is
  `f₀(T) ∪ f₀(crit f₀)`, which is Galois stable, has degrees `≤ d` and strictly fewer points
  of degree `d`, and does not contain `f₀(9)` (since `|f₀| ≤ 2ᵈ` there while `|f₀(9)| ≥ 8ᵈ`).
-/

namespace Belyi.NoncriticalP1

open Polynomial IntermediateField

/-- A finite set of algebraic numbers stable under `Gal(ℚ̄/ℚ)`. -/
def IsGalStable (T : Finset Qbar) : Prop := ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ t ∈ T, σ t ∈ T

/-- The degree `[ℚ(x) : ℚ]` of an algebraic number. -/
noncomputable abbrev deg (x : Qbar) : ℕ := (minpoly ℚ x).natDegree

/-- The branch set `T ∪ {∞}` as a subset of `ℙ¹(ℚ̄)`. -/
def withInf (T : Finset Qbar) : Set Pt := insert none (some '' (T : Set Qbar))

lemma mem_withInf {T : Finset Qbar} {z : Pt} : z ∈ withInf T ↔ z = none ∨ ∃ t ∈ T, z = some t := by
  simp only [withInf, Set.mem_insert_iff, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro (h | ⟨t, ht, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, rfl⟩
  · rintro (h | ⟨t, ht, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, rfl⟩

@[simp] lemma none_mem_withInf (T : Finset Qbar) : (none : Pt) ∈ withInf T :=
  Set.mem_insert _ _

lemma some_mem_withInf {T : Finset Qbar} {t : Qbar} (ht : t ∈ T) : some t ∈ withInf T :=
  Set.mem_insert_of_mem _ ⟨t, ht, rfl⟩

/-- Conjugates of a point of a Galois-stable set lie in the set. -/
lemma IsGalStable.mem_of_aeval_minpoly {T : Finset Qbar} (hT : IsGalStable T) {s ρ : Qbar}
    (hs : s ∈ T) (hρ : aeval ρ (minpoly ℚ s) = 0) : ρ ∈ T := by
  have hint : IsIntegral ℚ s := Algebra.IsIntegral.isIntegral s
  have h1 : minpoly ℚ s = minpoly ℚ ρ :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hρ (minpoly.monic hint)
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := Qbar)).mp h1.symm
  rw [← hσ]
  exact hT σ s hs

/-- An algebraic number of degree `≤ 1` is rational. -/
lemma exists_ratCast_of_deg_le_one {x : Qbar} (hx : deg x ≤ 1) : ∃ q : ℚ, x = q := by
  have h1 : 0 < deg x := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)
  obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.mp (le_antisymm hx h1)
  exact ⟨q, by rw [← hq, eq_ratCast]⟩

lemma deg_ratCast (q : ℚ) : deg (q : Qbar) = 1 := by
  rw [deg, ← eq_ratCast (algebraMap ℚ Qbar)]
  exact minpoly.natDegree_eq_one_iff.mpr ⟨q, rfl⟩

/-- Degrees do not grow inside `ℚ(x)`. -/
lemma deg_le_of_mem_adjoin {x y : Qbar} (h : y ∈ ℚ⟮x⟯) : deg y ≤ deg x := by
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hy : IsIntegral ℚ y := Algebra.IsIntegral.isIntegral y
  have : FiniteDimensional ℚ ℚ⟮x⟯ := adjoin.finiteDimensional hx
  rw [deg, deg, ← adjoin.finrank hx, ← adjoin.finrank hy]
  exact finrank_le_of_le_right (adjoin_simple_le_iff.mpr h)

/-- Elementary maps do not increase the degree of a finite point over `ℚ`. -/
lemma ElemMap.deg_le_of_apply_some (u : ElemMap) {t y : Qbar} (h : u.apply (some t) = some y) :
    deg y ≤ deg t := by
  have ht : t ∈ ℚ⟮t⟯ := mem_adjoin_simple_self ℚ t
  cases u with
  | mob a b c d hdet =>
    apply deg_le_of_mem_adjoin
    rw [ElemMap.apply_mob_some] at h
    split_ifs at h
    obtain rfl := Option.some.inj h
    have hq : ∀ q : ℚ, (q : Qbar) ∈ ℚ⟮t⟯ := fun q => by
      rw [← eq_ratCast (algebraMap ℚ Qbar)]; exact _root_.algebraMap_mem _ q
    exact div_mem (add_mem (mul_mem (hq a) ht) (hq b)) (add_mem (mul_mem (hq c) ht) (hq d))
  | poly p hp =>
    obtain rfl := Option.some.inj h
    exact natDegree_minpoly_aeval_le t p

/-- The finite part of the image of `T` under an elementary map. -/
noncomputable def pushFin (u : ElemMap) (T : Finset Qbar) : Finset Qbar :=
  letI := Classical.decEq Pt
  Finset.eraseNone (T.image fun t => u.apply (some t))

lemma mem_pushFin {u : ElemMap} {T : Finset Qbar} {y : Qbar} :
    y ∈ pushFin u T ↔ ∃ t ∈ T, u.apply (some t) = some y := by
  classical
  simp [pushFin]

lemma IsGalStable.pushFin {T : Finset Qbar} (hT : IsGalStable T) (u : ElemMap) :
    IsGalStable (pushFin u T) := by
  intro σ y hy
  obtain ⟨t, ht, hty⟩ := mem_pushFin.mp hy
  refine mem_pushFin.mpr ⟨σ t, hT σ t ht, ?_⟩
  have := u.apply_map σ (some t)
  rw [Option.map_some, hty, Option.map_some] at this
  exact this

lemma IsGalStable.image_aeval {T : Finset Qbar} (hT : IsGalStable T) (f : ℚ[X]) :
    IsGalStable (T.image fun t => aeval t f) := by
  intro σ y hy
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
  exact Finset.mem_image.mpr ⟨σ t, hT σ t ht, aeval_algHom_apply σ t f⟩

lemma isGalStable_critVal (f : ℚ[X]) : IsGalStable (critVal Qbar f) := by
  intro σ y hy
  obtain ⟨c, ⟨hd, hc⟩, rfl⟩ := mem_critVal_iff.mp hy
  refine mem_critVal_iff.mpr ⟨σ c, ⟨hd, ?_⟩, aeval_algHom_apply σ c f⟩
  rw [aeval_algHom_apply, hc, map_zero]

lemma IsGalStable.union {T T' : Finset Qbar} (hT : IsGalStable T) (hT' : IsGalStable T') :
    IsGalStable (T ∪ T') := by
  intro σ y hy
  rcases Finset.mem_union.mp hy with h | h
  · exact Finset.mem_union_left _ (hT σ y h)
  · exact Finset.mem_union_right _ (hT' σ y h)

lemma IsGalStable.insert_ratCast {T : Finset Qbar} (hT : IsGalStable T) (q : ℚ) :
    IsGalStable (insert (q : Qbar) T) := by
  intro σ y hy
  rcases Finset.mem_insert.mp hy with rfl | h
  · rw [map_ratCast]; exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (hT σ y h)

/-- **Normalisation** (Lemma 2.3 with `C = 9`): we may assume that `T` lies in the closed unit
disc and `τ = 9`. -/
theorem normalize_step (T : Finset Qbar) (hT : IsGalStable T) {τ : ℚ} (hτ : (τ : Qbar) ∉ T) :
    ∃ (u : ElemMap) (T₁ : Finset Qbar), IsGalStable T₁ ∧ (∀ y ∈ T₁, ‖ι y‖ ≤ 1) ∧
      (∀ d, 1 ≤ d → (∀ t ∈ T, deg t ≤ d) →
        (∀ y ∈ T₁, deg y ≤ d) ∧
        (2 ≤ d → (T₁.filter fun y => deg y = d).card ≤ (T.filter fun t => deg t = d).card)) ∧
      ∀ hs, IsNoncriticalBelyi hs (withInf T₁) (ofRat 9) →
        IsNoncriticalBelyi (u :: hs) (withInf T) (ofRat τ) := by
  classical
  obtain ⟨u, hram, hτu, hinf, hTu⟩ := exists_mob_normalize T hτ (C := 9) (by norm_num)
  refine ⟨u, insert ((0 : ℚ) : Qbar) (pushFin u T), (hT.pushFin u).insert_ratCast 0, ?_, ?_, ?_⟩
  · intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · simp
    · obtain ⟨t, ht, hty⟩ := mem_pushFin.mp hy
      obtain ⟨y', hy', hbd⟩ := hTu t ht
      rw [hty, Option.some.injEq] at hy'
      rwa [hy']
  · intro d hd hdeg
    refine ⟨fun y hy => ?_, fun hd2 => ?_⟩
    · rcases Finset.mem_insert.mp hy with rfl | hy
      · rw [deg_ratCast]; exact hd
      · obtain ⟨t, ht, hty⟩ := mem_pushFin.mp hy
        exact (u.deg_le_of_apply_some hty).trans (hdeg t ht)
    · refine le_trans (Finset.card_le_card (t := (T.filter fun t => deg t = d).image
        fun t => (u.apply (some t)).getD 0) ?_) Finset.card_image_le
      intro y hy
      obtain ⟨hy, hyd⟩ := Finset.mem_filter.mp hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · rw [deg_ratCast] at hyd; omega
      · obtain ⟨t, ht, hty⟩ := mem_pushFin.mp hy
        have h1 := u.deg_le_of_apply_some hty
        have h2 := hdeg t ht
        refine Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, by omega⟩, ?_⟩
        rw [hty]; rfl
  · intro hs hhs
    refine IsNoncriticalBelyi.cons u (S' := withInf (insert ((0 : ℚ) : Qbar) (pushFin u T)))
      ?_ (fun z hz => by rw [hram] at hz; exact absurd hz (lt_irrefl 1)) (by rwa [hτu])
    intro z hz
    rcases mem_withInf.mp hz with rfl | ⟨t, ht, rfl⟩
    · rw [hinf]; exact some_mem_withInf (Finset.mem_insert_self _ _)
    · obtain ⟨y, hy, -⟩ := hTu t ht
      rw [hy]
      exact some_mem_withInf (Finset.mem_insert_of_mem (mem_pushFin.mpr ⟨t, ht, hy⟩))

/-- **The rational case** (Lemma 2.2): if `T ⊆ ℚ` lies in the unit disc, there is a
noncritical Belyi map for `(T ∪ {∞}, 9)`. -/
theorem rational_step (T : Finset Qbar) (hbd : ∀ y ∈ T, ‖ι y‖ ≤ 1)
    (hdeg : ∀ y ∈ T, deg y ≤ 1) :
    ∃ hs, IsNoncriticalBelyi hs (withInf T) (ofRat 9) := by
  classical
  set T₀ : Finset ℚ := T.preimage (fun q : ℚ => (q : Qbar)) Rat.cast_injective.injOn with hT₀
  obtain ⟨hs, hhs⟩ := exists_isNoncriticalBelyi_rat T₀ 9 (fun q hq => by
    have := hbd _ (Finset.mem_preimage.mp hq)
    rw [norm_ι_ratCast] at this
    exact_mod_cast this) le_rfl
  refine ⟨hs, hhs.mono ?_⟩
  intro z hz
  rcases mem_withInf.mp hz with rfl | ⟨t, ht, rfl⟩
  · exact Set.mem_insert _ _
  · obtain ⟨q, rfl⟩ := exists_ratCast_of_deg_le_one (hdeg t ht)
    exact Set.mem_insert_of_mem _ ⟨q, Finset.mem_coe.mpr (Finset.mem_preimage.mpr ht), rfl⟩

/-- **The induction step of Lemma 2.4**: apply the minimal polynomial `f₀` of a point `σ₀ ∈ T`
of maximal degree `d ≥ 2`, where `T` lies in the unit disc. -/
theorem minpoly_step (T : Finset Qbar) (hT : IsGalStable T) (hbd : ∀ y ∈ T, ‖ι y‖ ≤ 1)
    {d n : ℕ} (hd : 2 ≤ d) (hdeg : ∀ y ∈ T, deg y ≤ d)
    (hcard : (T.filter fun y => deg y = d).card ≤ n + 1) {σ₀ : Qbar} (hσ₀ : σ₀ ∈ T)
    (hσ₀d : deg σ₀ = d) :
    ∃ (T₂ : Finset Qbar) (τ₂ : ℚ), IsGalStable T₂ ∧ (τ₂ : Qbar) ∉ T₂ ∧
      (∀ y ∈ T₂, deg y ≤ d) ∧ (T₂.filter fun y => deg y = d).card ≤ n ∧
      ∃ u : ElemMap, ∀ hs, IsNoncriticalBelyi hs (withInf T₂) (ofRat τ₂) →
        IsNoncriticalBelyi (u :: hs) (withInf T) (ofRat 9) := by
  classical
  set f := minpoly ℚ σ₀ with hf
  have hint : IsIntegral ℚ σ₀ := Algebra.IsIntegral.isIntegral σ₀
  have hmonic : f.Monic := minpoly.monic hint
  have hfdeg : f.natDegree = d := hσ₀d
  have hfpos : 0 < f.natDegree := by omega
  have hfder : derivative f ≠ 0 := fun h => by
    have := derivative_eq_zero.mp h; omega
  have hroots : ∀ ρ ∈ qroots f, ‖ι ρ‖ ≤ 1 := fun ρ hρ =>
    hbd ρ (hT.mem_of_aeval_minpoly hσ₀ ((mem_qroots (minpoly.ne_zero hint)).mp hρ))
  set T₂ : Finset Qbar := T.image (fun t => aeval t f) ∪ critVal Qbar f with hT₂
  have hbd₂ : ∀ y ∈ T₂, ‖ι y‖ ≤ 2 ^ d := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
      exact hfdeg ▸ norm_aeval_le hmonic hroots (hbd t ht)
    · obtain ⟨c, ⟨-, hc⟩, rfl⟩ := mem_critVal_iff.mp hy
      exact hfdeg ▸ norm_aeval_crit_le hmonic hfpos hroots hc
  refine ⟨T₂, f.eval 9, (hT.image_aeval f).union (isGalStable_critVal f), ?_, ?_, ?_,
    ElemMap.poly f hfpos, ?_⟩
  · -- `f(9)` is too large to lie in `T₂`
    intro hmem
    have h1 := hbd₂ _ hmem
    have h2 := pow_le_abs_eval_nine hmonic hroots
    rw [norm_ι_ratCast, hfdeg] at *
    have h3 : (2 : ℝ) ^ d < 8 ^ d := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    linarith
  · intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
      exact (natDegree_minpoly_aeval_le t f).trans (hdeg t ht)
    · exact le_of_lt (hfdeg ▸ natDegree_minpoly_critVal_lt (by omega) hy)
  · -- the number of points of degree `d` drops
    have hsub : (T₂.filter fun y => deg y = d) ⊆
        (T.filter fun t => deg t = d ∧ minpoly ℚ t ≠ f).image (fun t => aeval t f) := by
      intro y hy
      obtain ⟨hyT₂, hyd⟩ := Finset.mem_filter.mp hy
      rcases Finset.mem_union.mp hyT₂ with hy' | hy'
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy'
        have htd : deg t = d :=
          le_antisymm (hdeg t ht) (hyd ▸ natDegree_minpoly_aeval_le t f)
        have htm : minpoly ℚ t ≠ f := by
          intro h
          have h0 : aeval t f = 0 := h ▸ minpoly.aeval ℚ t
          have : deg (aeval t f) = 1 := by
            rw [h0, ← Rat.cast_zero]; exact deg_ratCast 0
          omega
        exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, htd, htm⟩, rfl⟩
      · have := natDegree_minpoly_critVal_lt (m := f) (by omega) hy'
        rw [hfdeg] at this
        exact absurd hyd (ne_of_lt this)
    have h1 : σ₀ ∈ (T.filter fun t => deg t = d).filter (fun t => minpoly ℚ t = f) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hσ₀, hσ₀d⟩, rfl⟩
    have h2 := Finset.card_filter_add_card_filter_not
      (p := fun t => minpoly ℚ t = f) (s := T.filter fun t => deg t = d)
    have h3 : (T.filter fun t => deg t = d ∧ minpoly ℚ t ≠ f) =
        (T.filter fun t => deg t = d).filter (fun t => ¬minpoly ℚ t = f) := by
      rw [Finset.filter_filter]
    have h4 : 0 < ((T.filter fun t => deg t = d).filter
        (fun t => minpoly ℚ t = f)).card := Finset.card_pos.mpr ⟨σ₀, h1⟩
    calc (T₂.filter fun y => deg y = d).card
        ≤ ((T.filter fun t => deg t = d ∧ minpoly ℚ t ≠ f).image
            (fun t => aeval t f)).card := Finset.card_le_card hsub
      _ ≤ (T.filter fun t => deg t = d ∧ minpoly ℚ t ≠ f).card := Finset.card_image_le
      _ ≤ n := by rw [h3]; omega
  · intro hs hhs
    refine IsNoncriticalBelyi.cons_poly hfpos (S' := withInf T₂) ?_ (none_mem_withInf _) ?_
      (by rwa [ElemMap.apply_poly_ofRat])
    · intro z hz
      rcases mem_withInf.mp hz with rfl | ⟨t, ht, rfl⟩
      · exact none_mem_withInf _
      · exact some_mem_withInf (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ht))
    · intro z hz
      exact some_mem_withInf (Finset.mem_union_right _ (aeval_mem_critVal hfder hz))

end Belyi.NoncriticalP1
