/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Converse.Basic
import Mathlib.RingTheory.Etale.Basic

/-!
# Base changes along `A → L`: existence and inherited properties

API around `Belyi.Converse.IsBaseChangeAlong` (see `Belyi/Converse/Basic.lean`).

## Main results

* `Belyi.Converse.IsBaseChangeAlong.of_equiv`: an isomorphism
  `(L ⊗[k] R) ⊗[A ⊗[k] R] B ≃ₐ[L ⊗[k] R] B'` compatible with `g` exhibits `B'` as base change.
* `Belyi.Converse.isBaseChangeAlong_includeRight`: the canonical base change
  `(L ⊗[k] R) ⊗[A ⊗[k] R] B` with `Algebra.TensorProduct.includeRight`.
* `Belyi.Converse.IsBaseChangeAlong.equiv`: conversely, the comparison isomorphism.
* `Belyi.Converse.IsBaseChangeAlong.finite`, `Belyi.Converse.IsBaseChangeAlong.etale`: finiteness
  and étaleness are inherited by base changes.
* `Belyi.Converse.exists_isBaseChangeAlong`: base changes exist and inherit finite and étale.
-/

universe u

open TensorProduct

namespace Belyi.Converse

variable {k : Type u} [CommRing k] {R : Type u} [CommRing R] [Algebra k R]
  {A : Type u} [CommRing A] [Algebra k A] {L : Type u} [CommRing L] [Algebra k L]

/-- An isomorphism `e : (L ⊗[k] R) ⊗[A ⊗[k] R] B ≃ₐ[L ⊗[k] R] B'` with `e (1 ⊗ b) = g b` exhibits
`B'` as the base change of `B` along `φ ⊗ id_R`. -/
theorem IsBaseChangeAlong.of_equiv (φ : A →ₐ[k] L) {B : Type u} [CommRing B]
    [Algebra (A ⊗[k] R) B] {B' : Type u} [CommRing B'] [Algebra (L ⊗[k] R) B'] (g : B →+* B')
    (e : letI := tensorMapAlgebra R φ; ((L ⊗[k] R) ⊗[A ⊗[k] R] B) ≃ₐ[L ⊗[k] R] B')
    (he : letI := tensorMapAlgebra R φ; ∀ b, e (1 ⊗ₜ b) = g b) :
    IsBaseChangeAlong (R := R) φ g := by
  letI := tensorMapAlgebra R φ
  letI : Algebra B B' := g.toAlgebra
  letI : Algebra (A ⊗[k] R) B' := ((algebraMap B B').comp (algebraMap (A ⊗[k] R) B)).toAlgebra
  haveI : IsScalarTower (A ⊗[k] R) B B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hT : IsScalarTower (A ⊗[k] R) (L ⊗[k] R) B' := by
    refine IsScalarTower.of_algebraMap_eq fun a ↦ ?_
    change g (algebraMap _ B a) = algebraMap (L ⊗[k] R) B' (algebraMap (A ⊗[k] R) (L ⊗[k] R) a)
    rw [← he, ← e.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one a, Algebra.algebraMap_self, RingHom.id_apply,
      TensorProduct.smul_tmul]
  refine ⟨hT, ?_⟩
  rw [Algebra.isPushout_iff]
  exact IsBaseChange.of_equiv e.toLinearEquiv fun b ↦ he b

/-- The canonical base change `(L ⊗[k] R) ⊗[A ⊗[k] R] B` (with `tensorMapAlgebra R φ`), together
with `Algebra.TensorProduct.includeRight`, is a base change along `φ`. -/
theorem isBaseChangeAlong_includeRight (φ : A →ₐ[k] L) (B : Type u) [CommRing B]
    [Algebra (A ⊗[k] R) B] :
    letI := tensorMapAlgebra R φ
    IsBaseChangeAlong (R := R) φ
      (Algebra.TensorProduct.includeRight (R := A ⊗[k] R) (A := L ⊗[k] R) (B := B)).toRingHom :=
  letI := tensorMapAlgebra R φ
  IsBaseChangeAlong.of_equiv φ _ AlgEquiv.refl fun _ ↦ rfl

/-- The comparison isomorphism `(L ⊗[k] R) ⊗[A ⊗[k] R] B ≃ₐ[L ⊗[k] R] B'` of a base change. -/
noncomputable def IsBaseChangeAlong.equiv {φ : A →ₐ[k] L} {B : Type u} [CommRing B]
    [Algebra (A ⊗[k] R) B] {B' : Type u} [CommRing B'] [Algebra (L ⊗[k] R) B'] {g : B →+* B'}
    (h : IsBaseChangeAlong (R := R) φ g) :
    letI := tensorMapAlgebra R φ; ((L ⊗[k] R) ⊗[A ⊗[k] R] B) ≃ₐ[L ⊗[k] R] B' :=
  letI := tensorMapAlgebra R φ
  letI : Algebra B B' := g.toAlgebra
  letI : Algebra (A ⊗[k] R) B' := ((algebraMap B B').comp (algebraMap (A ⊗[k] R) B)).toAlgebra
  haveI : IsScalarTower (A ⊗[k] R) B B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := h.1
  haveI := h.2
  Algebra.IsPushout.equiv (A ⊗[k] R) (L ⊗[k] R) B B'

/-- The comparison isomorphism of a base change on pure tensors. -/
theorem IsBaseChangeAlong.equiv_tmul {φ : A →ₐ[k] L} {B : Type u} [CommRing B]
    [Algebra (A ⊗[k] R) B] {B' : Type u} [CommRing B'] [Algebra (L ⊗[k] R) B'] {g : B →+* B'}
    (h : IsBaseChangeAlong (R := R) φ g) (x : L ⊗[k] R) (b : B) :
    letI := tensorMapAlgebra R φ; h.equiv (x ⊗ₜ b) = algebraMap (L ⊗[k] R) B' x * g b :=
  letI := tensorMapAlgebra R φ
  letI : Algebra B B' := g.toAlgebra
  letI : Algebra (A ⊗[k] R) B' := ((algebraMap B B').comp (algebraMap (A ⊗[k] R) B)).toAlgebra
  haveI : IsScalarTower (A ⊗[k] R) B B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := h.1
  haveI := h.2
  Algebra.IsPushout.equiv_tmul (A ⊗[k] R) (L ⊗[k] R) B B' x b

/-- The base change of a finite algebra is finite. -/
theorem IsBaseChangeAlong.finite {φ : A →ₐ[k] L} {B : Type u} [CommRing B]
    [Algebra (A ⊗[k] R) B] {B' : Type u} [CommRing B'] [Algebra (L ⊗[k] R) B'] {g : B →+* B'}
    (h : IsBaseChangeAlong (R := R) φ g) [Module.Finite (A ⊗[k] R) B] :
    Module.Finite (L ⊗[k] R) B' :=
  letI := tensorMapAlgebra R φ
  .equiv h.equiv.toLinearEquiv

/-- The base change of an étale algebra is étale. -/
theorem IsBaseChangeAlong.etale {φ : A →ₐ[k] L} {B : Type u} [CommRing B]
    [Algebra (A ⊗[k] R) B] {B' : Type u} [CommRing B'] [Algebra (L ⊗[k] R) B'] {g : B →+* B'}
    (h : IsBaseChangeAlong (R := R) φ g) [Algebra.Etale (A ⊗[k] R) B] :
    Algebra.Etale (L ⊗[k] R) B' :=
  letI := tensorMapAlgebra R φ
  .of_equiv h.equiv

/-- Base changes along `φ ⊗ id_R` exist, and they are finite, resp. étale, if the original algebra
is. -/
theorem exists_isBaseChangeAlong (φ : A →ₐ[k] L) (B : Type u) [CommRing B]
    [Algebra (A ⊗[k] R) B] :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra (L ⊗[k] R) B') (g : B →+* B'),
      IsBaseChangeAlong (R := R) φ g ∧
      (Module.Finite (A ⊗[k] R) B → Module.Finite (L ⊗[k] R) B') ∧
      (Algebra.Etale (A ⊗[k] R) B → Algebra.Etale (L ⊗[k] R) B') := by
  letI := tensorMapAlgebra R φ
  have h := isBaseChangeAlong_includeRight (R := R) φ B
  exact ⟨_, _, _, _, h, fun _ ↦ h.finite, fun _ ↦ h.etale⟩

end Belyi.Converse
