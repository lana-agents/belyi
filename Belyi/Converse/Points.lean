/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Algebra.Field.ULift
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Points of finitely generated algebras

Step (S4) of `references/converse-rie-design.md`.

## Main results

* `Belyi.Converse.nonempty_algHom_of_isAlgClosed`: a nontrivial finitely generated algebra over an
  algebraically closed field `k` has a `k`-point (Nullstellensatz).
* `Belyi.Converse.nonempty_ringHom_complex`: a field of characteristic zero algebraic over `ℚ`
  embeds into `ℂ`.
* `Belyi.Converse.countable_of_isAlgebraic_rat`: such a field is countable.
* `Belyi.Converse.exists_injective_algHom`: a finitely generated domain over a countable field `k`
  embeds into every uncountable algebraically closed field `Ω ⊇ k`.
* Instances `Uncountable ℂ`, `IsAlgClosed (ULift ℂ)`, so that the last result applies to
  `Ω := ULift ℂ`.
-/

universe u v

open Cardinal

namespace Belyi.Converse

/-- **Nullstellensatz**: a nontrivial finitely generated algebra over an algebraically closed field
has a rational point. -/
theorem nonempty_algHom_of_isAlgClosed (k : Type u) (A : Type v) [Field k] [IsAlgClosed k]
    [CommRing A] [Nontrivial A] [Algebra k A] [Algebra.FiniteType k A] :
    Nonempty (A →ₐ[k] k) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI := Ideal.Quotient.field m
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m)⟩

/-- A field of characteristic zero which is algebraic over `ℚ` embeds into `ℂ`. -/
theorem nonempty_ringHom_complex (k : Type u) [Field k] [CharZero k]
    [Algebra.IsAlgebraic ℚ k] : Nonempty (k →+* ℂ) :=
  ⟨(IsAlgClosed.lift : k →ₐ[ℚ] ℂ).toRingHom⟩

/-- A field of characteristic zero which is algebraic over `ℚ` is countable. -/
theorem countable_of_isAlgebraic_rat (k : Type u) [Field k] [CharZero k]
    [Algebra.IsAlgebraic ℚ k] : Countable k := by
  rw [← Cardinal.mk_le_aleph0_iff]
  have := Algebra.IsAlgebraic.lift_cardinalMk_le_max ℚ k
  simpa using this

instance : Uncountable ℂ := by
  rw [← not_countable_iff, ← Set.countable_univ_iff]
  exact not_countable_complex

/-- Being algebraically closed transfers along ring isomorphisms between fields in possibly
different universes (`IsAlgClosed.of_ringEquiv` requires equal universes). -/
theorem isAlgClosed_of_ringEquiv {k : Type u} {k' : Type v} [Field k] [Field k']
    (e : k ≃+* k') [IsAlgClosed k] : IsAlgClosed k' := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hpe : Polynomial.degree (p.map e.symm.toRingHom) ≠ 0 := by
    rw [Polynomial.degree_map]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hp)
  rcases IsAlgClosed.exists_root (k := k) (p.map e.symm.toRingHom) hpe with ⟨x, hx⟩
  use e x
  rw [Polynomial.IsRoot] at hx
  apply e.symm.injective
  rw [map_zero, ← hx]
  clear hx hpe hp hmp
  induction p using Polynomial.induction_on <;> simp_all

instance : IsAlgClosed (ULift.{u} ℂ) :=
  isAlgClosed_of_ringEquiv ULift.ringEquiv.symm

/-- An uncountable algebraically closed field over a countable field has an infinite transcendence
basis. -/
theorem infinite_of_isTranscendenceBasis {k Ω : Type u} [Field k] [Countable k] [Field Ω]
    [IsAlgClosed Ω] [Algebra k Ω] [Uncountable Ω] {t : Set Ω}
    (ht : IsTranscendenceBasis k ((↑) : t → Ω)) : Infinite t := by
  by_contra h
  rw [not_infinite_iff_finite] at h
  have hle := IsAlgClosed.cardinal_le_max_transcendence_basis' _ ht
  have : #Ω ≤ ℵ₀ := hle.trans (by simp [Cardinal.mk_le_aleph0])
  exact not_countable (α := Ω) (Cardinal.mk_le_aleph0_iff.mp this)

/-- A finitely generated domain over a countable field `k` admits an injective `k`-algebra map
into any uncountable algebraically closed field `Ω` over `k`. -/
theorem exists_injective_algHom (k Ω A : Type u) [Field k] [Countable k]
    [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] [Uncountable Ω]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ ι : A →ₐ[k] Ω, Function.Injective ι := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k A
  have hsfin : #s < ℵ₀ := by
    have h1 := hs.lift_cardinalMk_eq_trdeg
    have h2 := trdeg_lt_aleph0 (R := k) (S := A)
    simp only [lift_id] at h1
    rwa [h1]
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis k Ω
  have htinf := infinite_of_isTranscendenceBasis ht
  obtain ⟨emb⟩ : Nonempty (s ↪ t) := by
    rw [← Cardinal.le_def]
    exact hsfin.le.trans (Cardinal.infinite_iff.mp htinf)
  let y : s → Ω := fun i ↦ (emb i : Ω)
  have hy : AlgebraicIndependent k y := ht.1.comp emb emb.injective
  let R := Algebra.adjoin k (Set.range ((↑) : s → A))
  let φ : R →ₐ[k] Ω := (MvPolynomial.aeval y).comp hs.1.aevalEquiv.symm.toAlgHom
  have hφ : Function.Injective φ := 
    (algebraicIndependent_iff_injective_aeval.mp hy).comp hs.1.aevalEquiv.symm.injective
  letI : Algebra R Ω := φ.toAlgebra
  haveI : IsScalarTower k R Ω := IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  haveI : Algebra.IsAlgebraic R A := hs.isAlgebraic
  haveI : Module.IsTorsionFree R Ω := Module.isTorsionFree_iff_algebraMap_injective.mpr hφ
  let ψ : A →ₐ[R] Ω := IsAlgClosed.lift
  refine ⟨ψ.restrictScalars k, ?_⟩
  letI : Algebra A Ω := ψ.toAlgebra
  exact @Algebra.IsAlgebraic.injective_tower_top R A _ Ω _ _ _ _ _ _ _
    (IsScalarTower.of_algebraMap_eq fun x ↦ (ψ.commutes x).symm) hφ

end Belyi.Converse
