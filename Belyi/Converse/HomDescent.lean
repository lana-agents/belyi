/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Descending isomorphisms of base changes to finitely generated subalgebras

Let `A` be a commutative ring, `P` an `A`-algebra and `B₁`, `B₂` finitely presented
`P`-algebras. For an `A`-algebra `L` we consider the base changes `L ⊗[A] Bᵢ`. The ring `Ω` is the
directed union of its finitely generated `A`-subalgebras `C`, and `Ω ⊗[A] Bᵢ` is the direct limit
of the `C ⊗[A] Bᵢ` (mathlib: `TensorProduct.Algebra.exists_of_fg`,
`TensorProduct.Algebra.eq_of_fg_of_subtype_eq`). Hence an isomorphism
`Ω ⊗[A] B₁ ≃ Ω ⊗[A] B₂` (of `Ω`-algebras compatible with `P`) is already defined over some
finitely generated `A`-subalgebra `C ⊆ Ω`, and can then be transported along any `A`-algebra map
`C → K`. This is the algebraic core of step (S2) of `references/converse-rie-design.md`.

A map `B₁ → L ⊗[A] B₂` is called *`P`-compatible* if it sends `algebraMap P B₁ p` to
`1 ⊗ₜ algebraMap P B₂ p`.

## Main results

* `Belyi.Converse.HomDescent.exists_fg_descent`: a `P`-compatible `A`-algebra map
  `B → Ω ⊗[A] N` out of a finitely presented `P`-algebra factors through `C ⊗[A] N` for a
  finitely generated `A`-subalgebra `C ⊆ Ω`.
* `Belyi.Converse.HomDescent.exists_fg_eq`: two `P`-compatible maps `B → C ⊗[A] N` out of a
  finite type `P`-algebra which agree in `Ω ⊗[A] N` agree in `D ⊗[A] N` for all large enough
  finitely generated `D ⊇ C`.
* `Belyi.Converse.HomDescent.exists_algEquiv_of_fg`: if every finitely generated
  `A`-subalgebra of `Ω` admits an `A`-algebra map to `K`, then a `P`-compatible isomorphism
  `Ω ⊗[A] B₁ ≃ₐ[Ω] Ω ⊗[A] B₂` yields a `P`-compatible isomorphism `K ⊗[A] B₁ ≃ₐ[K] K ⊗[A] B₂`.
-/

open TensorProduct Algebra.TensorProduct

namespace Belyi.Converse.HomDescent

section Subalgebras

variable {A : Type*} [CommRing A] {Ω : Type*} [CommRing Ω] [Algebra A Ω]
  {N : Type*} [CommRing N] [Algebra A N]

lemma map_id_eq_rTensor {D E : Type*} [CommRing D] [Algebra A D] [CommRing E] [Algebra A E]
    (f : D →ₐ[A] E) (t : D ⊗[A] N) :
    Algebra.TensorProduct.map f (AlgHom.id A N) t = LinearMap.rTensor N f.toLinearMap t := by
  induction t with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

lemma map_inclusion_inclusion {C D E : Subalgebra A Ω} (h₁ : C ≤ D) (h₂ : D ≤ E)
    (t : C ⊗[A] N) :
    Algebra.TensorProduct.map (Subalgebra.inclusion h₂) (AlgHom.id A N)
      (Algebra.TensorProduct.map (Subalgebra.inclusion h₁) (AlgHom.id A N) t) =
    Algebra.TensorProduct.map (Subalgebra.inclusion (h₁.trans h₂)) (AlgHom.id A N) t := by
  induction t with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

lemma map_val_inclusion {C D : Subalgebra A Ω} (h : C ≤ D) (t : C ⊗[A] N) :
    Algebra.TensorProduct.map D.val (AlgHom.id A N)
      (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id A N) t) =
    Algebra.TensorProduct.map C.val (AlgHom.id A N) t := by
  induction t with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- Finitely many properties, each of which holds for all subalgebras above some finitely
generated one, hold simultaneously for all subalgebras above some finitely generated `D ⊇ C`. -/
lemma exists_fg_forall {ι : Type*} (s : Finset ι) (Q : ι → Subalgebra A Ω → Prop)
    (hQ : ∀ i ∈ s, ∃ D : Subalgebra A Ω, D.FG ∧ ∀ E, D ≤ E → Q i E)
    {C : Subalgebra A Ω} (hC : C.FG) :
    ∃ D : Subalgebra A Ω, D.FG ∧ C ≤ D ∧ ∀ E, D ≤ E → ∀ i ∈ s, Q i E := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨C, hC, le_rfl, by simp⟩
  | insert i s _ ih =>
    obtain ⟨D, hD, hCD, hDQ⟩ := ih fun j hj ↦ hQ j (Finset.mem_insert_of_mem hj)
    obtain ⟨D', hD', hD'Q⟩ := hQ i (Finset.mem_insert_self i s)
    refine ⟨D ⊔ D', hD.sup hD', hCD.trans le_sup_left, fun E hE j hj ↦ ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hD'Q E (le_sup_right.trans hE)
    · exact hDQ E (le_sup_left.trans hE) j hj

variable {P : Type*} [CommRing P] [Algebra A P] [Algebra P N] [IsScalarTower A P N]
  {B : Type*} [CommRing B] [Algebra A B] [Algebra P B] [IsScalarTower A P B]

omit [Algebra A P] [IsScalarTower A P N] [IsScalarTower A P B] in
/-- Two `P`-compatible maps `B → C ⊗[A] N` out of a finite type `P`-algebra `B` which agree
after mapping to `Ω ⊗[A] N` agree after mapping to `E ⊗[A] N` for all `E ⊇ D`, for some finitely
generated `D ⊇ C`. -/
theorem exists_fg_eq [Algebra.FiniteType P B] {C : Subalgebra A Ω} (hC : C.FG)
    (F F' : B →ₐ[A] C ⊗[A] N)
    (hF : ∀ p : P, F (algebraMap P B p) = 1 ⊗ₜ algebraMap P N p)
    (hF' : ∀ p : P, F' (algebraMap P B p) = 1 ⊗ₜ algebraMap P N p)
    (h : (Algebra.TensorProduct.map C.val (AlgHom.id A N)).comp F =
      (Algebra.TensorProduct.map C.val (AlgHom.id A N)).comp F') :
    ∃ D : Subalgebra A Ω, D.FG ∧ C ≤ D ∧ ∀ (E : Subalgebra A Ω) (hCE : C ≤ E), D ≤ E →
      (Algebra.TensorProduct.map (Subalgebra.inclusion hCE) (AlgHom.id A N)).comp F =
      (Algebra.TensorProduct.map (Subalgebra.inclusion hCE) (AlgHom.id A N)).comp F' := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := P) (A := B)
  let Q : B → Subalgebra A Ω → Prop := fun x E ↦ ∀ hCE : C ≤ E,
    Algebra.TensorProduct.map (Subalgebra.inclusion hCE) (AlgHom.id A N) (F x) =
    Algebra.TensorProduct.map (Subalgebra.inclusion hCE) (AlgHom.id A N) (F' x)
  have hQ : ∀ x ∈ s, ∃ D : Subalgebra A Ω, D.FG ∧ ∀ E, D ≤ E → Q x E := by
    intro x _
    have hx := congr($h x)
    simp only [AlgHom.comp_apply, map_id_eq_rTensor] at hx
    obtain ⟨D₀, hCD₀, hD₀, hD₀x⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq hC hx
    refine ⟨D₀, hD₀, fun E hE hCE ↦ ?_⟩
    rw [← map_inclusion_inclusion hCD₀ hE, ← map_inclusion_inclusion hCD₀ hE]
    simp only [map_id_eq_rTensor] at hD₀x ⊢
    rw [hD₀x]
  obtain ⟨D, hD, hCD, hDQ⟩ := exists_fg_forall s Q hQ hC
  refine ⟨D, hD, hCD, fun E hCE hDE ↦ AlgHom.ext fun b ↦ ?_⟩
  have hb : b ∈ Algebra.adjoin P (s : Set B) := hs ▸ Algebra.mem_top
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hDQ E hDE x hx hCE
  | algebraMap p => simp [hF, hF']
  | add x y _ _ hx hy => simp only [AlgHom.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
  | mul x y _ _ hx hy => simp only [AlgHom.comp_apply, map_mul] at hx hy ⊢; rw [hx, hy]

/-- A `P`-compatible `A`-algebra map `B → Ω ⊗[A] N` out of a finitely presented `P`-algebra `B`
factors through `C ⊗[A] N` for some finitely generated `A`-subalgebra `C ⊆ Ω`. -/
theorem exists_fg_descent [Algebra.FinitePresentation P B] (F : B →ₐ[A] Ω ⊗[A] N)
    (hF : ∀ p : P, F (algebraMap P B p) = 1 ⊗ₜ algebraMap P N p) :
    ∃ C : Subalgebra A Ω, C.FG ∧ ∃ F' : B →ₐ[A] C ⊗[A] N,
      (∀ p : P, F' (algebraMap P B p) = 1 ⊗ₜ algebraMap P N p) ∧
      (Algebra.TensorProduct.map C.val (AlgHom.id A N)).comp F' = F := by
  classical
  obtain ⟨n, f, hf, t, ht⟩ := Algebra.FinitePresentation.out (R := P) (A := B)
  have hfC : ∀ p : P, f (MvPolynomial.C p) = algebraMap P B p := fun p ↦ by
    rw [← MvPolynomial.algebraMap_eq]; exact f.commutes p
  -- lift the images of the variables
  let Q : Fin n → Subalgebra A Ω → Prop := fun i E ↦
    ∃ y : E ⊗[A] N, Algebra.TensorProduct.map E.val (AlgHom.id A N) y = F (f (.X i))
  have hQ : ∀ i ∈ Finset.univ, ∃ D : Subalgebra A Ω, D.FG ∧ ∀ E, D ≤ E → Q i E := by
    intro i _
    obtain ⟨D, hD, y, hy⟩ := TensorProduct.Algebra.exists_of_fg (R := A) (N := N) (F (f (.X i)))
    refine ⟨D, hD, fun E hE ↦ ⟨Algebra.TensorProduct.map (Subalgebra.inclusion hE)
      (AlgHom.id A N) y, ?_⟩⟩
    rw [map_val_inclusion, map_id_eq_rTensor, ← hy]
  obtain ⟨C, hC, -, hCQ⟩ := exists_fg_forall Finset.univ Q hQ Subalgebra.fg_bot
  choose y hy using fun i ↦ hCQ C le_rfl i (Finset.mem_univ i)
  let G : MvPolynomial (Fin n) P →+* C ⊗[A] N := MvPolynomial.eval₂Hom
    ((Algebra.TensorProduct.includeRight : N →ₐ[A] C ⊗[A] N).toRingHom.comp (algebraMap P N)) y
  have hG : ((Algebra.TensorProduct.map C.val (AlgHom.id A N)).toRingHom.comp G) =
      F.toRingHom.comp f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro p
      simp [G, hfC, hF]
    · intro i
      simp [G, hy]
  -- make the relations vanish
  let Q' : MvPolynomial (Fin n) P → Subalgebra A Ω → Prop := fun r E ↦ ∀ hCE : C ≤ E,
    Algebra.TensorProduct.map (Subalgebra.inclusion hCE) (AlgHom.id A N) (G r) = 0
  have hQ' : ∀ r ∈ t, ∃ D : Subalgebra A Ω, D.FG ∧ ∀ E, D ≤ E → Q' r E := by
    intro r hr
    have hr0 : f r = 0 := by
      have : r ∈ RingHom.ker f.toRingHom := ht ▸ Ideal.subset_span hr
      simpa using this
    have hx : LinearMap.rTensor N C.val.toLinearMap (G r) =
        LinearMap.rTensor N C.val.toLinearMap 0 := by
      rw [← map_id_eq_rTensor, map_zero]
      simpa [hr0] using congr($hG r)
    obtain ⟨D₀, hCD₀, hD₀, hD₀x⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq hC hx
    refine ⟨D₀, hD₀, fun E hE hCE ↦ ?_⟩
    rw [← map_inclusion_inclusion hCD₀ hE, map_id_eq_rTensor (Subalgebra.inclusion hCD₀), hD₀x]
    simp
  obtain ⟨D, hD, hCD, hDQ'⟩ := exists_fg_forall t Q' hQ' hC
  let GD : MvPolynomial (Fin n) P →+* D ⊗[A] N :=
    (Algebra.TensorProduct.map (Subalgebra.inclusion hCD) (AlgHom.id A N)).toRingHom.comp G
  have hker : RingHom.ker f.toRingHom ≤ RingHom.ker GD := by
    rw [← ht, Ideal.span_le]
    intro r hr
    exact hDQ' D le_rfl r hr hCD
  let F₀ : B →+* D ⊗[A] N := f.toRingHom.liftOfSurjective hf ⟨GD, hker⟩
  have hF₀ : ∀ x, F₀ (f x) = GD x := fun x ↦
    RingHom.liftOfSurjective_comp_apply f.toRingHom hf ⟨GD, hker⟩ x
  have hF₀P : ∀ p : P, F₀ (algebraMap P B p) = 1 ⊗ₜ algebraMap P N p := fun p ↦ by
    rw [← hfC, hF₀]
    simp [GD, G]
  refine ⟨D, hD, { F₀ with commutes' := fun a ↦ ?_ }, hF₀P, ?_⟩
  · change F₀ (algebraMap A B a) = _
    rw [IsScalarTower.algebraMap_apply A P B, hF₀P, Algebra.TensorProduct.algebraMap_apply',
      ← IsScalarTower.algebraMap_apply]
  · ext b
    obtain ⟨x, rfl⟩ := hf b
    change Algebra.TensorProduct.map D.val (AlgHom.id A N) (F₀ (f x)) = F (f x)
    rw [hF₀]
    change Algebra.TensorProduct.map D.val (AlgHom.id A N)
      (Algebra.TensorProduct.map (Subalgebra.inclusion hCD) (AlgHom.id A N) (G x)) = _
    rw [map_val_inclusion]
    exact congr($hG x)

end Subalgebras

section BaseChange

variable {A : Type*} [CommRing A]
  {B₁ : Type*} [CommRing B₁] [Algebra A B₁] {B₂ : Type*} [CommRing B₂] [Algebra A B₂]
  {D : Type*} [CommRing D] [Algebra A D] {E : Type*} [CommRing E] [Algebra A E]

/-- The `D`-linear extension `D ⊗[A] B₁ → D ⊗[A] B₂` of an `A`-algebra map `B₁ → D ⊗[A] B₂`. -/
noncomputable def baseChangeHom (F : B₁ →ₐ[A] D ⊗[A] B₂) : D ⊗[A] B₁ →ₐ[D] D ⊗[A] B₂ :=
  Algebra.TensorProduct.lift (Algebra.ofId D _) F fun _ _ ↦ .all _ _

@[simp]
lemma baseChangeHom_tmul (F : B₁ →ₐ[A] D ⊗[A] B₂) (d : D) (b : B₁) :
    baseChangeHom F (d ⊗ₜ b) = (d ⊗ₜ 1) * F b := by
  simp [baseChangeHom]

@[simp]
lemma baseChangeHom_one_tmul (F : B₁ →ₐ[A] D ⊗[A] B₂) (b : B₁) :
    baseChangeHom F (1 ⊗ₜ b) = F b := by
  simp [← Algebra.TensorProduct.one_def]

/-- Transport of an `A`-algebra map `B₁ → D ⊗[A] B₂` along `σ : D → E`. -/
noncomputable def pushHom (σ : D →ₐ[A] E) (F : B₁ →ₐ[A] D ⊗[A] B₂) : B₁ →ₐ[A] E ⊗[A] B₂ :=
  (Algebra.TensorProduct.map σ (AlgHom.id A B₂)).comp F

@[simp]
lemma pushHom_apply (σ : D →ₐ[A] E) (F : B₁ →ₐ[A] D ⊗[A] B₂) (b : B₁) :
    pushHom σ F b = Algebra.TensorProduct.map σ (AlgHom.id A B₂) (F b) := rfl

lemma map_baseChangeHom (σ : D →ₐ[A] E) (F : B₁ →ₐ[A] D ⊗[A] B₂) (t : D ⊗[A] B₁) :
    Algebra.TensorProduct.map σ (AlgHom.id A B₂) (baseChangeHom F t) =
      baseChangeHom (pushHom σ F) (Algebra.TensorProduct.map σ (AlgHom.id A B₁) t) := by
  induction t with
  | zero => simp
  | tmul d b => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

/-- `F₁ : B₁ → D ⊗[A] B₂` and `F₂ : B₂ → D ⊗[A] B₁` induce mutually inverse maps. -/
def IsInverse (F₁ : B₁ →ₐ[A] D ⊗[A] B₂) (F₂ : B₂ →ₐ[A] D ⊗[A] B₁) : Prop :=
  (∀ b, baseChangeHom F₂ (F₁ b) = 1 ⊗ₜ b) ∧ (∀ b, baseChangeHom F₁ (F₂ b) = 1 ⊗ₜ b)

lemma IsInverse.pushHom {F₁ : B₁ →ₐ[A] D ⊗[A] B₂} {F₂ : B₂ →ₐ[A] D ⊗[A] B₁}
    (h : IsInverse F₁ F₂) (σ : D →ₐ[A] E) : IsInverse (pushHom σ F₁) (pushHom σ F₂) := by
  constructor <;> intro b
  · rw [pushHom_apply, ← map_baseChangeHom, h.1]; simp
  · rw [pushHom_apply, ← map_baseChangeHom, h.2]; simp

/-- The isomorphism `D ⊗[A] B₁ ≃ₐ[D] D ⊗[A] B₂` induced by mutually inverse maps. -/
noncomputable def IsInverse.algEquiv {F₁ : B₁ →ₐ[A] D ⊗[A] B₂} {F₂ : B₂ →ₐ[A] D ⊗[A] B₁}
    (h : IsInverse F₁ F₂) : D ⊗[A] B₁ ≃ₐ[D] D ⊗[A] B₂ :=
  AlgEquiv.ofAlgHom (baseChangeHom F₁) (baseChangeHom F₂)
    (Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun b ↦ by simp [h.2]))
    (Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun b ↦ by simp [h.1]))

@[simp]
lemma IsInverse.algEquiv_one_tmul {F₁ : B₁ →ₐ[A] D ⊗[A] B₂} {F₂ : B₂ →ₐ[A] D ⊗[A] B₁}
    (h : IsInverse F₁ F₂) (b : B₁) : h.algEquiv (1 ⊗ₜ b) = F₁ b :=
  baseChangeHom_one_tmul F₁ b

end BaseChange

section Main

variable {A : Type*} [CommRing A] {P : Type*} [CommRing P] [Algebra A P]
  {B₁ : Type*} [CommRing B₁] [Algebra A B₁] [Algebra P B₁] [IsScalarTower A P B₁]
  {B₂ : Type*} [CommRing B₂] [Algebra A B₂] [Algebra P B₂] [IsScalarTower A P B₂]
  {Ω : Type*} [CommRing Ω] [Algebra A Ω] {K : Type*} [CommRing K] [Algebra A K]

/-- **Descent of isomorphisms**: if every finitely generated `A`-subalgebra of `Ω` admits an
`A`-algebra map to `K`, then a `P`-compatible isomorphism `Ω ⊗[A] B₁ ≃ₐ[Ω] Ω ⊗[A] B₂` of base
changes of finitely presented `P`-algebras yields a `P`-compatible isomorphism
`K ⊗[A] B₁ ≃ₐ[K] K ⊗[A] B₂`. -/
theorem exists_algEquiv_of_fg [Algebra.FinitePresentation P B₁]
    [Algebra.FinitePresentation P B₂]
    (hK : ∀ C : Subalgebra A Ω, C.FG → Nonempty (C →ₐ[A] K))
    (e : Ω ⊗[A] B₁ ≃ₐ[Ω] Ω ⊗[A] B₂)
    (he : ∀ p : P, e (1 ⊗ₜ algebraMap P B₁ p) = 1 ⊗ₜ algebraMap P B₂ p) :
    ∃ e' : K ⊗[A] B₁ ≃ₐ[K] K ⊗[A] B₂,
      ∀ p : P, e' (1 ⊗ₜ algebraMap P B₁ p) = 1 ⊗ₜ algebraMap P B₂ p := by
  have he' : ∀ p : P, e.symm (1 ⊗ₜ algebraMap P B₂ p) = 1 ⊗ₜ algebraMap P B₁ p := fun p ↦ by
    rw [AlgEquiv.symm_apply_eq, he]
  let F₁ : B₁ →ₐ[A] Ω ⊗[A] B₂ :=
    (e.toAlgHom.restrictScalars A).comp Algebra.TensorProduct.includeRight
  let F₂ : B₂ →ₐ[A] Ω ⊗[A] B₁ :=
    (e.symm.toAlgHom.restrictScalars A).comp Algebra.TensorProduct.includeRight
  obtain ⟨C₁, hC₁, F₁', hF₁'P, hF₁'⟩ := exists_fg_descent (P := P) F₁ (by simpa [F₁] using he)
  obtain ⟨C₂, hC₂, F₂', hF₂'P, hF₂'⟩ := exists_fg_descent (P := P) F₂ (by simpa [F₂] using he')
  set C := C₁ ⊔ C₂
  let G₁ := pushHom (Subalgebra.inclusion (le_sup_left : C₁ ≤ C)) F₁'
  let G₂ := pushHom (Subalgebra.inclusion (le_sup_right : C₂ ≤ C)) F₂'
  have hG₁P : ∀ p : P, G₁ (algebraMap P B₁ p) = 1 ⊗ₜ algebraMap P B₂ p := fun p ↦ by
    simp [G₁, hF₁'P]
  have hG₂P : ∀ p : P, G₂ (algebraMap P B₂ p) = 1 ⊗ₜ algebraMap P B₁ p := fun p ↦ by
    simp [G₂, hF₂'P]
  have hG₁ : pushHom C.val G₁ = F₁ := by
    rw [← hF₁']; ext b; exact map_val_inclusion _ _
  have hG₂ : pushHom C.val G₂ = F₂ := by
    rw [← hF₂']; ext b; exact map_val_inclusion _ _
  have hbc₁ : ∀ t, baseChangeHom F₁ t = e t := by
    intro t
    induction t with
    | zero => simp
    | tmul ω b =>
      have : (ω ⊗ₜ[A] b : Ω ⊗[A] _) = algebraMap Ω _ ω * (1 ⊗ₜ b) := by simp
      rw [baseChangeHom_tmul, this, map_mul, AlgEquiv.commutes]
      simp [F₁]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hbc₂ : ∀ t, baseChangeHom F₂ t = e.symm t := by
    intro t
    induction t with
    | zero => simp
    | tmul ω b =>
      have : (ω ⊗ₜ[A] b : Ω ⊗[A] _) = algebraMap Ω _ ω * (1 ⊗ₜ b) := by simp
      rw [baseChangeHom_tmul, this, map_mul, AlgEquiv.commutes]
      simp [F₂]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  -- the two identities, over `C`
  let X₁ := ((baseChangeHom G₂).restrictScalars A).comp G₁
  let X₂ := ((baseChangeHom G₁).restrictScalars A).comp G₂
  obtain ⟨D₁, hD₁, hCD₁, hD₁X⟩ := exists_fg_eq (Ω := Ω) (P := P) (hC₁.sup hC₂) X₁
    Algebra.TensorProduct.includeRight (fun p ↦ by simp [X₁, hG₁P, hG₂P]) (fun p ↦ rfl) <| by
      ext b
      simp only [X₁, AlgHom.comp_apply, AlgHom.coe_restrictScalars', map_baseChangeHom]
      rw [← pushHom_apply, hG₁, hG₂, hbc₂]
      simp [F₁]
  obtain ⟨D₂, hD₂, hCD₂, hD₂X⟩ := exists_fg_eq (Ω := Ω) (P := P) (hC₁.sup hC₂) X₂
    Algebra.TensorProduct.includeRight (fun p ↦ by simp [X₂, hG₁P, hG₂P]) (fun p ↦ rfl) <| by
      ext b
      simp only [X₂, AlgHom.comp_apply, AlgHom.coe_restrictScalars', map_baseChangeHom]
      rw [← pushHom_apply, hG₁, hG₂, hbc₁]
      simp [F₂]
  set C' := D₁ ⊔ D₂
  have hCC' : C ≤ C' := hCD₁.trans le_sup_left
  let H₁ := pushHom (Subalgebra.inclusion hCC') G₁
  let H₂ := pushHom (Subalgebra.inclusion hCC') G₂
  have hH : IsInverse H₁ H₂ := by
    constructor <;> intro b
    · have := congr($(hD₁X C' hCC' le_sup_left) b)
      simp only [X₁, AlgHom.comp_apply, AlgHom.coe_restrictScalars', map_baseChangeHom] at this
      simpa [H₁, H₂] using this
    · have := congr($(hD₂X C' hCC' le_sup_right) b)
      simp only [X₂, AlgHom.comp_apply, AlgHom.coe_restrictScalars', map_baseChangeHom] at this
      simpa [H₁, H₂] using this
  obtain ⟨ψ⟩ := hK C' ((hD₁.sup hD₂))
  refine ⟨(hH.pushHom ψ).algEquiv, fun p ↦ ?_⟩
  rw [IsInverse.algEquiv_one_tmul]
  simp [H₁, hG₁P]

end Main

end Belyi.Converse.HomDescent
