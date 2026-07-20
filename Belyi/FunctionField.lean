/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Stalk

/-!
# The function field of a scheme over a field as an algebra over the base

For an irreducible scheme `X` over `Spec k`, the function field `K(X)` is a `k`-algebra:
pull back a constant along the structure morphism and take its germ at the generic
point. This file provides that (scoped) instance together with the key compatibility
(taxis issue #46, input to B1): under `Spec`, the algebra map `k → K(X)` becomes the
canonical morphism `Spec K(X) ⟶ Spec k`, i.e. the composition of
`X.fromSpecStalk (genericPoint X)` with the structure morphism. Consequently a
morphism `Spec K(X) ⟶ Y` of `k`-schemes constructed from the algebra structure is a
morphism over `Spec k` in the sense of mathlib's `Over`/`IsOver` framework.

The instance is scoped to `Belyi` to avoid clashing with mathlib's
`Algebra R (Spec R).functionField` instance in the (unused) overlap case.

## Main definitions

* `Belyi.instAlgebraFunctionField`: `Algebra k X.functionField` (scoped).
* `Belyi.specMap_algebraMap_functionField`:
  `Spec.map (algebraMap k K(X)) = X.fromSpecStalk (genericPoint X) ≫ (X ↘ Spec k)`,
  the right-hand side being the canonical `Over`-structure of `Spec K(X)` over `Spec k`.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [IrreducibleSpace X]
  [X.Over (Spec (CommRingCat.of k))]

/-- The function field of an irreducible scheme over `Spec k` is a `k`-algebra: pull a
constant back along the structure morphism and take the germ at the generic point. -/
noncomputable scoped instance instAlgebraFunctionField : Algebra k X.functionField :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop ≫
    X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra

lemma ofHom_algebraMap_functionField :
    CommRingCat.ofHom (algebraMap k X.functionField) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial :=
  rfl

/-- Under `Spec`, the algebra map `k → K(X)` is the canonical morphism
`Spec K(X) ⟶ Spec k` through `Spec 𝒪_{X,η} ⟶ X`. -/
lemma specMap_algebraMap_functionField :
    Spec.map (CommRingCat.ofHom (algebraMap k X.functionField)) =
      X.fromSpecStalk (genericPoint X) ≫ (X ↘ Spec (CommRingCat.of k)) := by
  rw [ofHom_algebraMap_functionField, Spec.map_comp, Spec.map_comp,
    ← Scheme.fromSpecStalk_toSpecΓ_assoc]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The `Over`-structure morphism of `Spec K(X)` over `Spec k` is `Spec` of the
algebra map. -/
lemma functionField_over_eq :
    (Spec X.functionField ↘ Spec (CommRingCat.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k X.functionField)) :=
  (specMap_algebraMap_functionField k X).symm

end Belyi
