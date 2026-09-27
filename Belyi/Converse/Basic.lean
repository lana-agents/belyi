/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Base change of algebras over `A ⊗[k] R` along a map `A → L`

The converse direction of Belyi's theorem (`references/converse-rie-design.md`) moves finite
étale algebras over `A ⊗[k] R` (a family over `Spec A` of finite étale covers of `Spec R`) along
`k`-algebra maps `φ : A →ₐ[k] L`, landing in algebras over `L ⊗[k] R`. This file fixes the
common interface used for this by all packages of the converse.

## Main definitions

* `Belyi.Converse.tensorMapAlgebra φ`: the `A ⊗[k] R`-algebra structure on `L ⊗[k] R` induced
  by `φ : A →ₐ[k] L`, i.e. by `φ ⊗ id_R`.
* `Belyi.Converse.IsBaseChangeAlong φ g`: the `L ⊗[k] R`-algebra `B'` is the base change of the
  `A ⊗[k] R`-algebra `B` along `φ ⊗ id_R`, witnessed by the ring map `g : B →+* B'`: `g` is
  compatible with the structure maps and the square is a pushout (`Algebra.IsPushout`).
-/

universe u

open TensorProduct

namespace Belyi.Converse

variable {k : Type u} [CommRing k] {R : Type u} [CommRing R] [Algebra k R]
  {A : Type u} [CommRing A] [Algebra k A] {L : Type u} [CommRing L] [Algebra k L]

variable (R) in
/-- The `A ⊗[k] R`-algebra structure on `L ⊗[k] R` induced by `φ ⊗ id_R` for a `k`-algebra map
`φ : A →ₐ[k] L`. -/
noncomputable abbrev tensorMapAlgebra (φ : A →ₐ[k] L) : Algebra (A ⊗[k] R) (L ⊗[k] R) :=
  (Algebra.TensorProduct.map φ (AlgHom.id k R)).toRingHom.toAlgebra

/-- `IsBaseChangeAlong φ g` says that the `L ⊗[k] R`-algebra `B'` is the base change of the
`A ⊗[k] R`-algebra `B` along `φ ⊗ id_R : A ⊗[k] R → L ⊗[k] R`, the comparison being the ring map
`g : B →+* B'`. Concretely: with the algebra structures `tensorMapAlgebra R φ` on `L ⊗[k] R` and
`g.toAlgebra` on `B'`, both squares of scalar towers commute and the square
```
A ⊗[k] R ──→ B
   │          │ g
   ▼          ▼
L ⊗[k] R ──→ B'
```
is a pushout (`Algebra.IsPushout`). -/
def IsBaseChangeAlong (φ : A →ₐ[k] L) {B : Type u} [CommRing B] [Algebra (A ⊗[k] R) B]
    {B' : Type u} [CommRing B'] [Algebra (L ⊗[k] R) B'] (g : B →+* B') : Prop :=
  letI := tensorMapAlgebra R φ
  letI : Algebra B B' := g.toAlgebra
  letI : Algebra (A ⊗[k] R) B' := ((algebraMap B B').comp (algebraMap (A ⊗[k] R) B)).toAlgebra
  haveI : IsScalarTower (A ⊗[k] R) B B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  ∃ _ : IsScalarTower (A ⊗[k] R) (L ⊗[k] R) B', Algebra.IsPushout (A ⊗[k] R) (L ⊗[k] R) B B'

end Belyi.Converse
