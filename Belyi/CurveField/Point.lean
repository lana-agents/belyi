/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.Residue
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Algebraic points of a curve

An algebraic point `x ∈ X(ℚ̄)` of the curve with function field `K` is a place `P` of `K`
together with a field embedding `σ : κ(P) → ℚ̄ := AlgebraicClosure ℚ`
(`Belyi.CurveField.QbarPoint`). This is `Hom(Spec ℚ̄, X)` for the regular proper model `X`
of the curve; it includes the embedding of the constant field of `K`.

The value of a function `f ∈ O_P` at `x` is `f(x) := σ(f mod 𝔪_P) ∈ ℚ̄`
(`Belyi.CurveField.QbarPoint.eval`), and the field of definition of `x` is the number field
`σ(κ(P)) ⊆ ℚ̄` (`Belyi.CurveField.QbarPoint.fieldOf`), of degree `deg x = deg P`.

## Main definitions and results

* `Belyi.CurveField.QbarPoint K`, `QbarPoint.eval`, `QbarPoint.fieldOf`, `QbarPoint.deg`.
* ring-homomorphism lemmas for `eval`; `QbarPoint.eval_eq_zero_iff`:
  `f(x) = 0 ↔ ord_P f > 0` for `f ≠ 0`.
* `QbarPoint.deg_eq : x.deg = x.P.deg`, `QbarPoint.eval_mem_fieldOf`.
* `QbarPoint.finite_setOf_mem`: finitely many points lie over a finite set of places.
* `QbarPoint.exists_P_eq`: every place carries a point.
-/

open IsLocalRing

namespace Belyi.CurveField

/-- An algebraic point of the curve with function field `K`: a place `P` of `K` together with
an embedding of its residue field into `ℚ̄ = AlgebraicClosure ℚ`. -/
structure QbarPoint (K : Type*) [Field K] [CharZero K] where
  /-- The place (closed point of the regular proper model) underlying the point. -/
  P : Place K
  /-- The embedding of the residue field `κ(P)` into `ℚ̄`. -/
  σ : P.ResidueField →+* AlgebraicClosure ℚ

namespace QbarPoint

variable {K : Type*} [Field K] [CharZero K] (x : QbarPoint K)

theorem ext' {x y : QbarPoint K} (hP : x.P = y.P)
    (hσ : ∀ a : x.P.1, x.σ (x.P.residue a) = y.σ (y.P.residue ⟨a.1, hP ▸ a.2⟩)) : x = y := by
  obtain ⟨P, σ⟩ := x
  obtain ⟨Q, τ⟩ := y
  obtain rfl : P = Q := hP
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext b
  obtain ⟨a, rfl⟩ := P.residue_surjective b
  exact hσ a

/-- The value `f(x) ∈ ℚ̄` of a function `f` regular at the point `x`. -/
noncomputable def eval (f : K) (hf : f ∈ x.P.1) : AlgebraicClosure ℚ :=
  x.σ (x.P.residue ⟨f, hf⟩)

variable {f g : K}

@[simp]
theorem eval_zero : x.eval 0 x.P.1.zero_mem = 0 := by
  simp [eval, show (⟨0, x.P.1.zero_mem⟩ : x.P.1) = 0 from rfl]

@[simp]
theorem eval_one : x.eval 1 x.P.1.one_mem = 1 := by
  simp [eval, show (⟨1, x.P.1.one_mem⟩ : x.P.1) = 1 from rfl]

theorem eval_add (hf : f ∈ x.P.1) (hg : g ∈ x.P.1) :
    x.eval (f + g) (x.P.1.add_mem _ _ hf hg) = x.eval f hf + x.eval g hg := by
  simp only [eval, ← map_add]
  rfl

theorem eval_mul (hf : f ∈ x.P.1) (hg : g ∈ x.P.1) :
    x.eval (f * g) (x.P.1.mul_mem _ _ hf hg) = x.eval f hf * x.eval g hg := by
  simp only [eval, ← map_mul]
  rfl

theorem eval_neg (hf : f ∈ x.P.1) : x.eval (-f) (x.P.1.neg_mem _ hf) = -x.eval f hf := by
  simp only [eval, ← map_neg]
  rfl

theorem eval_sub (hf : f ∈ x.P.1) (hg : g ∈ x.P.1) :
    x.eval (f - g) (sub_mem hf hg) = x.eval f hf - x.eval g hg := by
  simp only [eval, ← map_sub]
  rfl

theorem eval_pow (hf : f ∈ x.P.1) (n : ℕ) :
    x.eval (f ^ n) (pow_mem hf n) = x.eval f hf ^ n := by
  simp only [eval, ← map_pow]
  rfl

/-- The value only depends on the function (proof irrelevance, stated for rewriting). -/
theorem eval_congr {f g : K} (h : f = g) (hf : f ∈ x.P.1) :
    x.eval f hf = x.eval g (h ▸ hf) := by
  subst h; rfl

@[simp]
theorem eval_ratCast (q : ℚ) : x.eval (q : K) (x.P.ratCast_mem q) = (q : AlgebraicClosure ℚ) := by
  rw [eval, Place.residue_mk_ratCast, map_ratCast]

@[simp]
theorem eval_algebraMap (q : ℚ) :
    x.eval (algebraMap ℚ K q) (x.P.algebraMap_mem q) = algebraMap ℚ (AlgebraicClosure ℚ) q :=
  x.eval_ratCast q

theorem eval_eq_zero_iff_mem_maximalIdeal (hf : f ∈ x.P.1) :
    x.eval f hf = 0 ↔ (⟨f, hf⟩ : x.P.1) ∈ maximalIdeal x.P.1 := by
  rw [eval, map_eq_zero_iff _ x.σ.injective, Place.residue_eq_zero_iff]

section IsCurveField

variable [IsCurveField K]

/-- A nonzero regular function vanishes at `x` iff it has positive order at `x.P`. -/
theorem eval_eq_zero_iff (hf : f ∈ x.P.1) (hf0 : f ≠ 0) :
    x.eval f hf = 0 ↔ 0 < x.P.ord f := by
  rw [eval_eq_zero_iff_mem_maximalIdeal, x.P.ord_pos_iff_mem_maximalIdeal (a := ⟨f, hf⟩) hf0]

theorem eval_eq_zero_iff' (hf : f ∈ x.P.1) : x.eval f hf = 0 ↔ f = 0 ∨ 0 < x.P.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · simp [x.eval_eq_zero_iff hf hf0, hf0]

omit [IsCurveField K] in
theorem eval_inv (hf : f ∈ x.P.1) (hfi : f⁻¹ ∈ x.P.1) :
    x.eval f⁻¹ hfi = (x.eval f hf)⁻¹ := by
  rcases eq_or_ne f 0 with rfl | hf0
  · have h0 : ∀ h, x.eval 0 h = 0 := fun _ ↦ x.eval_zero
    simp only [inv_zero, h0]
  refine (eq_inv_of_mul_eq_one_left ?_)
  rw [← x.eval_mul hfi hf, x.eval_congr (inv_mul_cancel₀ hf0), eval_one]

end IsCurveField

/-- The field of definition `σ(κ(P)) ⊆ ℚ̄` of the point `x`. -/
noncomputable def fieldOf : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  x.σ.toRatAlgHom.fieldRange

theorem eval_mem_fieldOf (hf : f ∈ x.P.1) : x.eval f hf ∈ x.fieldOf :=
  ⟨x.P.residue ⟨f, hf⟩, rfl⟩

/-- The residue field of `x.P` is isomorphic to the field of definition of `x`. -/
noncomputable def residueFieldEquiv : x.P.ResidueField ≃ₐ[ℚ] x.fieldOf :=
  x.σ.toRatAlgHom.equivFieldRange

/-- The degree `[ℚ(x) : ℚ]` of the point `x`. -/
noncomputable def deg : ℕ := Module.finrank ℚ x.fieldOf

section IsCurveField

variable [IsCurveField K]

instance : FiniteDimensional ℚ x.fieldOf :=
  x.residueFieldEquiv.toLinearEquiv.finiteDimensional

omit [IsCurveField K] in
theorem deg_eq : x.deg = x.P.deg :=
  x.residueFieldEquiv.toLinearEquiv.finrank_eq.symm

theorem deg_pos : 0 < x.deg := x.deg_eq ▸ x.P.deg_pos

/-- Every place carries an algebraic point. -/
theorem exists_P_eq (P : Place K) : ∃ x : QbarPoint K, x.P = P :=
  ⟨⟨P, (IsAlgClosed.lift (R := ℚ) (S := P.ResidueField) (M := AlgebraicClosure ℚ)).toRingHom⟩,
    rfl⟩

instance (P : Place K) : Finite (P.ResidueField →+* AlgebraicClosure ℚ) :=
  Finite.of_equiv _ RingHom.equivRatAlgHom.symm

/-- Only finitely many points lie over a finite set of places. -/
theorem finite_setOf_mem {S : Set (Place K)} (hS : S.Finite) :
    {x : QbarPoint K | x.P ∈ S}.Finite := by
  have : Finite S := hS.to_subtype
  let g : (Σ P : S, P.1.ResidueField →+* AlgebraicClosure ℚ) → QbarPoint K :=
    fun p ↦ ⟨p.1.1, p.2⟩
  refine (Set.finite_range g).subset fun x hx ↦ ?_
  exact ⟨⟨⟨x.P, hx⟩, x.σ⟩, rfl⟩

end IsCurveField

end QbarPoint

end Belyi.CurveField
