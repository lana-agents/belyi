/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Converse.BaseChange

/-!
# Base changes of constant families and of fibres

API around `Belyi.Converse.IsBaseChangeAlong` (see `Belyi/Converse/Basic.lean`) for the two kinds
of base changes needed to assemble the descent of finite étale covers
(`Belyi/Converse/FEtDescent.lean`).

For an `R`-algebra `B₀` (over `k`), `M ⊗[k] B₀` is an `M ⊗[k] R`-algebra via `id ⊗ (R → B₀)`
(`Belyi.Converse.tensorRightAlgebra`); this is the constant family with fibre `B₀`.

## Main results

* `Belyi.Converse.isPushout_tensorRight`: `M ⊗[k] B₀` is the base change of `B₀` along
  `R → M ⊗[k] R`.
* `Belyi.Converse.etale_tensorRight`, `Belyi.Converse.finite_tensorRight`: hence `M ⊗[k] B₀` is
  étale, resp. finite, over `M ⊗[k] R` if `B₀` is so over `R`.
* `Belyi.Converse.isBaseChangeAlong_map`: the base change of the constant family `A ⊗[k] B₀`
  along `φ : A → L` is the constant family `L ⊗[k] B₀`.
* `Belyi.Converse.isBaseChangeAlong_fibre`: for a `k`-point `s` of `A` and an
  `A ⊗[k] R`-algebra `B` with fibre `B₀ := R ⊗[A ⊗[k] R] B` at `s`, the base change of `B` along
  `A → k → M` is the constant family `M ⊗[k] B₀`.
-/

universe u

open TensorProduct

namespace Belyi.Converse

variable {k : Type u} [CommRing k] {R : Type u} [CommRing R] [Algebra k R]
  {A : Type u} [CommRing A] [Algebra k A] {L : Type u} [CommRing L] [Algebra k L]

variable (k R) in
/-- The `M ⊗[k] R`-algebra structure on `M ⊗[k] B₀` induced by `id_M ⊗ (R → B₀)`, for an
`R`-algebra `B₀`: the constant family over `M` with fibre `B₀`. -/
noncomputable abbrev tensorRightAlgebra (M : Type u) [CommRing M] [Algebra k M] (B₀ : Type u)
    [CommRing B₀] [Algebra k B₀] [Algebra R B₀] [IsScalarTower k R B₀] :
    Algebra (M ⊗[k] R) (M ⊗[k] B₀) :=
  (Algebra.TensorProduct.map (AlgHom.id k M) (IsScalarTower.toAlgHom k R B₀)).toRingHom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- `M ⊗[k] B₀` is the base change of the `R`-algebra `B₀` along `R → M ⊗[k] R`. -/
theorem isPushout_tensorRight (M : Type u) [CommRing M] [Algebra k M] (B₀ : Type u)
    [CommRing B₀] [Algebra k B₀] [Algebra R B₀] [IsScalarTower k R B₀] :
    letI := tensorRightAlgebra k R M B₀
    letI : Algebra R (M ⊗[k] B₀) := ((algebraMap B₀ (M ⊗[k] B₀)).comp (algebraMap R B₀)).toAlgebra
    haveI : IsScalarTower R B₀ (M ⊗[k] B₀) := .of_algebraMap_eq fun _ ↦ rfl
    haveI : IsScalarTower R (M ⊗[k] R) (M ⊗[k] B₀) := .of_algebraMap_eq fun _ ↦ rfl
    Algebra.IsPushout R (M ⊗[k] R) B₀ (M ⊗[k] B₀) := by
  letI := tensorRightAlgebra k R M B₀
  letI : Algebra R (M ⊗[k] B₀) := ((algebraMap B₀ (M ⊗[k] B₀)).comp (algebraMap R B₀)).toAlgebra
  haveI : IsScalarTower R B₀ (M ⊗[k] B₀) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R (M ⊗[k] R) (M ⊗[k] B₀) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower k B₀ (M ⊗[k] B₀) := inferInstance
  haveI : IsScalarTower k M (M ⊗[k] B₀) := inferInstance
  haveI : IsScalarTower k (M ⊗[k] R) (M ⊗[k] B₀) := .of_algebraMap_eq fun c ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  haveI : IsScalarTower M (M ⊗[k] R) (M ⊗[k] B₀) := .of_algebraMap_eq fun m ↦ by
    change m ⊗ₜ 1 = Algebra.TensorProduct.map _ _ (m ⊗ₜ 1); simp
  have H : Algebra.IsPushout k B₀ M (M ⊗[k] B₀) := inferInstance
  exact ((Algebra.IsPushout.comp_iff k R M (M ⊗[k] R) (T := B₀) (T' := M ⊗[k] B₀)).mp H).symm

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The comparison isomorphism `(M ⊗[k] R) ⊗[R] B₀ ≃ₐ[M ⊗[k] R] M ⊗[k] B₀`. -/
noncomputable def tensorRightEquiv (M : Type u) [CommRing M] [Algebra k M] (B₀ : Type u)
    [CommRing B₀] [Algebra k B₀] [Algebra R B₀] [IsScalarTower k R B₀] :
    letI := tensorRightAlgebra k R M B₀
    (M ⊗[k] R) ⊗[R] B₀ ≃ₐ[M ⊗[k] R] M ⊗[k] B₀ :=
  letI := tensorRightAlgebra k R M B₀
  letI : Algebra R (M ⊗[k] B₀) := ((algebraMap B₀ (M ⊗[k] B₀)).comp (algebraMap R B₀)).toAlgebra
  haveI : IsScalarTower R B₀ (M ⊗[k] B₀) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R (M ⊗[k] R) (M ⊗[k] B₀) := .of_algebraMap_eq fun _ ↦ rfl
  haveI := isPushout_tensorRight (k := k) (R := R) M B₀
  Algebra.IsPushout.equiv R (M ⊗[k] R) B₀ (M ⊗[k] B₀)

/-- The constant family `M ⊗[k] B₀` is étale over `M ⊗[k] R` if `B₀` is étale over `R`. -/
theorem etale_tensorRight (M : Type u) [CommRing M] [Algebra k M] (B₀ : Type u)
    [CommRing B₀] [Algebra k B₀] [Algebra R B₀] [IsScalarTower k R B₀] [Algebra.Etale R B₀] :
    letI := tensorRightAlgebra k R M B₀
    Algebra.Etale (M ⊗[k] R) (M ⊗[k] B₀) :=
  letI := tensorRightAlgebra k R M B₀
  .of_equiv (tensorRightEquiv M B₀)

/-- The constant family `M ⊗[k] B₀` is finite over `M ⊗[k] R` if `B₀` is finite over `R`. -/
theorem finite_tensorRight (M : Type u) [CommRing M] [Algebra k M] (B₀ : Type u)
    [CommRing B₀] [Algebra k B₀] [Algebra R B₀] [IsScalarTower k R B₀] [Module.Finite R B₀] :
    letI := tensorRightAlgebra k R M B₀
    Module.Finite (M ⊗[k] R) (M ⊗[k] B₀) :=
  letI := tensorRightAlgebra k R M B₀
  .equiv (tensorRightEquiv M B₀).toLinearEquiv


variable (R) in
/-- The `k`-algebra map `A ⊗[k] R → R` induced by a `k`-point `s` of `A`. -/
noncomputable abbrev evalTensor (s : A →ₐ[k] k) : A ⊗[k] R →ₐ[k] R :=
  (Algebra.TensorProduct.lid k R).toAlgHom.comp (Algebra.TensorProduct.map s (AlgHom.id k R))

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Let `s` be a `k`-point of `A`, `B` an `A ⊗[k] R`-algebra and `B₀ := R ⊗[A ⊗[k] R] B` its fibre
at `s` (with `R` an `A ⊗[k] R`-algebra via `evalTensor R s`). Then the base change of `B` along
`A → k → M` is the constant family `M ⊗[k] B₀`, via `b ↦ 1 ⊗ (1 ⊗ b)`. -/
theorem isBaseChangeAlong_fibre (s : A →ₐ[k] k) (M : Type u) [CommRing M] [Algebra k M]
    (B : Type u) [CommRing B] [Algebra (A ⊗[k] R) B] :
    letI := (evalTensor R s).toRingHom.toAlgebra
    letI := tensorRightAlgebra k R M (R ⊗[A ⊗[k] R] B)
    IsBaseChangeAlong (R := R) ((Algebra.ofId k M).comp s)
      (Algebra.TensorProduct.includeRight.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := A ⊗[k] R) (A := R) (B := B)).toRingHom :
        B →+* M ⊗[k] (R ⊗[A ⊗[k] R] B)) := by
  letI := (evalTensor R s).toRingHom.toAlgebra
  set B₀ := R ⊗[A ⊗[k] R] B
  letI := tensorRightAlgebra k R M B₀
  set g : B →+* M ⊗[k] B₀ := Algebra.TensorProduct.includeRight.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := A ⊗[k] R) (A := R) (B := B)).toRingHom
  letI := tensorMapAlgebra R ((Algebra.ofId k M).comp s)
  letI : Algebra B (M ⊗[k] B₀) := g.toAlgebra
  letI : Algebra (A ⊗[k] R) (M ⊗[k] B₀) :=
    ((algebraMap B (M ⊗[k] B₀)).comp (algebraMap (A ⊗[k] R) B)).toAlgebra
  haveI : IsScalarTower (A ⊗[k] R) B (M ⊗[k] B₀) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hfib : ∀ x : A ⊗[k] R, ((1 : R) ⊗ₜ algebraMap (A ⊗[k] R) B x : B₀) =
      algebraMap (A ⊗[k] R) R x ⊗ₜ 1 := fun x ↦ by
    rw [Algebra.algebraMap_eq_smul_one (A := B), ← TensorProduct.smul_tmul, Algebra.smul_def,
      mul_one]
  haveI : IsScalarTower (A ⊗[k] R) R (M ⊗[k] R) := .of_algebraMap_eq fun x ↦ by
    induction x with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a r =>
      change algebraMap k M (s a) ⊗ₜ r = 1 ⊗ₜ (s a • r)
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hT : IsScalarTower (A ⊗[k] R) (M ⊗[k] R) (M ⊗[k] B₀) := by
    refine .of_algebraMap_eq fun x ↦ ?_
    induction x with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a r =>
      change (1 : M) ⊗ₜ ((1 : R) ⊗ₜ algebraMap (A ⊗[k] R) B (a ⊗ₜ r) : B₀) =
        algebraMap k M (s a) ⊗ₜ (r ⊗ₜ 1 : B₀)
      rw [hfib]
      change (1 : M) ⊗ₜ ((s a • r) ⊗ₜ 1 : B₀) = _
      rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one,
        ← TensorProduct.smul_tmul']
  refine ⟨hT, ?_⟩
  letI : Algebra R (M ⊗[k] B₀) := ((algebraMap B₀ (M ⊗[k] B₀)).comp (algebraMap R B₀)).toAlgebra
  haveI : IsScalarTower R B₀ (M ⊗[k] B₀) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R (M ⊗[k] R) (M ⊗[k] B₀) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower B B₀ (M ⊗[k] B₀) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (A ⊗[k] R) B₀ (M ⊗[k] B₀) := .of_algebraMap_eq fun x ↦ by
    change (1 : M) ⊗ₜ ((1 : R) ⊗ₜ algebraMap (A ⊗[k] R) B x : B₀) = _
    rw [hfib]
    rfl
  have H := isPushout_tensorRight (k := k) (R := R) M B₀
  exact (Algebra.IsPushout.comp_iff (A ⊗[k] R) R B B₀ (T := M ⊗[k] R) (T' := M ⊗[k] B₀)).mpr H


/-- The base change of the constant family `A ⊗[k] B₀` along `φ : A → L` is the constant family
`L ⊗[k] B₀`, via `φ ⊗ id`. -/
theorem isBaseChangeAlong_map (φ : A →ₐ[k] L) (B₀ : Type u) [CommRing B₀] [Algebra k B₀]
    [Algebra R B₀] [IsScalarTower k R B₀] :
    letI := tensorRightAlgebra k R A B₀
    letI := tensorRightAlgebra k R L B₀
    IsBaseChangeAlong (R := R) φ (Algebra.TensorProduct.map φ (AlgHom.id k B₀)).toRingHom := by
  letI := tensorRightAlgebra k R A B₀
  letI := tensorRightAlgebra k R L B₀
  letI := tensorMapAlgebra R φ
  letI : Algebra (A ⊗[k] B₀) (L ⊗[k] B₀) :=
    (Algebra.TensorProduct.map φ (AlgHom.id k B₀)).toRingHom.toAlgebra
  letI : Algebra (A ⊗[k] R) (L ⊗[k] B₀) :=
    ((algebraMap (A ⊗[k] B₀) (L ⊗[k] B₀)).comp (algebraMap (A ⊗[k] R) (A ⊗[k] B₀))).toAlgebra
  haveI : IsScalarTower (A ⊗[k] R) (A ⊗[k] B₀) (L ⊗[k] B₀) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hT : IsScalarTower (A ⊗[k] R) (L ⊗[k] R) (L ⊗[k] B₀) := by
    refine .of_algebraMap_eq fun x ↦ ?_
    induction x with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a r => rfl
  refine ⟨hT, ?_⟩
  letI : Algebra A L := φ.toAlgebra
  haveI : IsScalarTower k A L := .of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  haveI : IsScalarTower A (A ⊗[k] R) (L ⊗[k] R) := .of_algebraMap_eq fun a ↦ by
    change φ a ⊗ₜ 1 = _; simp [RingHom.algebraMap_toAlgebra]
  haveI : IsScalarTower A L (L ⊗[k] R) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower A (A ⊗[k] B₀) (L ⊗[k] B₀) := .of_algebraMap_eq fun a ↦ by
    change φ a ⊗ₜ 1 = _; simp [RingHom.algebraMap_toAlgebra]
  haveI : IsScalarTower A L (L ⊗[k] B₀) := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower A (A ⊗[k] R) (L ⊗[k] B₀) := .of_algebraMap_eq fun a ↦ by
    change φ a ⊗ₜ 1 = _; simp [RingHom.algebraMap_toAlgebra]
  haveI : IsScalarTower A (L ⊗[k] R) (L ⊗[k] B₀) := .of_algebraMap_eq fun a ↦ by
    change φ a ⊗ₜ 1 = _; simp [RingHom.algebraMap_toAlgebra]
  haveI : IsScalarTower L (L ⊗[k] R) (L ⊗[k] B₀) := .of_algebraMap_eq fun l ↦ by
    change l ⊗ₜ 1 = Algebra.TensorProduct.map _ _ (l ⊗ₜ 1); simp
  haveI : IsScalarTower A (A ⊗[k] R) (A ⊗[k] B₀) := .of_algebraMap_eq fun a ↦ by
    change a ⊗ₜ 1 = Algebra.TensorProduct.map _ _ (a ⊗ₜ 1); simp
  haveI : Algebra.IsPushout A (A ⊗[k] R) L (L ⊗[k] R) :=
    (Algebra.IsPushout.tensorProduct_tensorProduct k R A L <| by
      ext; simp [RingHom.algebraMap_toAlgebra]).symm
  have H : Algebra.IsPushout A (A ⊗[k] B₀) L (L ⊗[k] B₀) :=
    (Algebra.IsPushout.tensorProduct_tensorProduct k B₀ A L <| by
      ext; simp [RingHom.algebraMap_toAlgebra]).symm
  exact ((Algebra.IsPushout.comp_iff A (A ⊗[k] R) L (L ⊗[k] R) (T := A ⊗[k] B₀)
    (T' := L ⊗[k] B₀)).mp H).symm

end Belyi.Converse
