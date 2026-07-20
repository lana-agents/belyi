/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.FunctionField
import Belyi.P1.AffineChart
import Belyi.RationalMap

/-!
# The morphism to `ℙ¹` attached to a rational function

Assembly of the construction part of B1 (taxis issue #46): for an integral scheme `X`
over `Spec k` and a rational function `t ∈ K(X)`,

* `t` gives a `K(X)`-valued point `Spec K(X) ⟶ P1 k` over `Spec k`
  (`Belyi.functionFieldPoint`, from `Belyi.P1.point` and the `k`-algebra structure on
  `K(X)`);
* hence a rational map `X ⤏ P1 k` over `Spec k`
  (`Belyi.ratMapOfFunctionField`, via `RationalMap.equivFunctionFieldOver`);
* which extends to a morphism `X ⟶ P1 k` over `Spec k` whenever the local rings of `X`
  are valuation rings (`Belyi.homOfFunctionField`, via `RationalMap.toHom` and
  properness of `ℙ¹`).

For a curve `X/k` (`Belyi.IsCurveOver`), integrality holds by
`IsCurveOver.isIntegral`, and the valuation-ring hypothesis will be discharged once
"stalks of a smooth curve are discrete valuation rings" lands (remaining part of #46);
until then it is threaded as an explicit hypothesis `hX`.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Scheme

variable (k : Type u) [CommRing k] (X : Scheme.{u}) [IrreducibleSpace X]
  [X.Over (Spec (CommRingCat.of k))]

/-- The `K(X)`-valued point of `ℙ¹` with affine coordinate a rational function `t`. -/
noncomputable def functionFieldPoint (t : X.functionField) :
    Spec X.functionField ⟶ P1 k :=
  P1.point (R := X.functionField) k t

/-- The point of `ℙ¹` attached to a rational function is a morphism over `Spec k`. -/
instance (t : X.functionField) :
    (functionFieldPoint k X t).IsOver (Spec (CommRingCat.of k)) where
  comp_over := by
    rw [functionFieldPoint, P1.structMap_eq, P1.point_structMap,
      functionField_over_eq]

variable [IsIntegral X]

/-- The rational map `X ⤏ ℙ¹` attached to a rational function `t ∈ K(X)`. -/
noncomputable def ratMapOfFunctionField (t : X.functionField) : X ⤏ P1 k :=
  ((RationalMap.equivFunctionFieldOver (S := Spec (CommRingCat.of k)) (X := X)
    (Y := P1 k)) ⟨functionFieldPoint k X t, inferInstance⟩).1

instance (t : X.functionField) :
    (ratMapOfFunctionField k X t).IsOver (Spec (CommRingCat.of k)) :=
  ((RationalMap.equivFunctionFieldOver (S := Spec (CommRingCat.of k)) (X := X)
    (Y := P1 k)) ⟨functionFieldPoint k X t, inferInstance⟩).2

/-- The projective line over a base ring is separated (as an abstract scheme). -/
lemma isSeparated_P1 : (P1 k).IsSeparated :=
  isSeparated_of_isSeparated_over (Spec (CommRingCat.of k)) (P1 k)

/-- The morphism `X ⟶ ℙ¹` attached to a rational function `t ∈ K(X)`, for `X`
integral over `k` with valuation-ring local rings (e.g. a smooth curve): the
extension of `ratMapOfFunctionField` over the proper target `ℙ¹`.

This is the construction underlying B1; finiteness of this morphism for
non-constant `t` is the remaining statement of B1. -/
noncomputable def homOfFunctionField
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (t : X.functionField) :
    X ⟶ P1 k :=
  haveI : (P1 k).IsSeparated := isSeparated_P1 k
  (ratMapOfFunctionField k X t).toHom (Spec (CommRingCat.of k)) hX

@[simp]
lemma toRationalMap_homOfFunctionField
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (t : X.functionField) :
    (homOfFunctionField k X hX t).toRationalMap = ratMapOfFunctionField k X t :=
  haveI : (P1 k).IsSeparated := isSeparated_P1 k
  RationalMap.toHom_toRationalMap (Spec (CommRingCat.of k)) _ hX

/-- The morphism attached to a rational function is a morphism of `k`-schemes. -/
instance (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (t : X.functionField) :
    (homOfFunctionField k X hX t).IsOver (Spec (CommRingCat.of k)) :=
  haveI : (P1 k).IsSeparated := isSeparated_P1 k
  RationalMap.isOver_toHom (Spec (CommRingCat.of k)) _ hX

/-- A morphism over `S` from a scheme proper over `S` to a scheme separated over `S`
is proper. -/
lemma isProper_of_isOver {X Y S : Scheme.{u}} [X.Over S] [Y.Over S] (f : X ⟶ Y)
    [f.IsOver S] [IsProper (X ↘ S)] [IsSeparated (Y ↘ S)] : IsProper f :=
  have h : IsProper (f ≫ (Y ↘ S)) := by rw [comp_over]; infer_instance
  IsProper.of_comp f (Y ↘ S)

/-- If `X` is proper over `k` (e.g. a curve), the morphism to `ℙ¹` attached to a
rational function is proper. Together with quasi-finiteness (which needs the
dimension-1 hypothesis and non-constancy of `t`) this will give B1 via Zariski's
main theorem (`IsFinite.of_isProper_of_locallyQuasiFinite`). -/
lemma isProper_homOfFunctionField [IsProper (X ↘ Spec (CommRingCat.of k))]
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (t : X.functionField) :
    IsProper (homOfFunctionField k X hX t) :=
  isProper_of_isOver (S := Spec (CommRingCat.of k)) _

end Belyi
