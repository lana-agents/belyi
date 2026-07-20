/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Extension of rational maps into proper schemes

This file proves the extension theorem needed for B1 (taxis issue #46): a rational map
from an integral scheme whose local rings are valuation rings (e.g. a regular integral
scheme of dimension `≤ 1`, such as a smooth curve) into a scheme proper over the base
extends to a morphism.

The proof is the classical one: for a point `x`, the generic point specializes to `x`,
so the stalk `𝒪_{X,x}` is a valuation ring with fraction field `K(X)`; the valuative
criterion of properness lifts `Spec K(X) ⟶ Y` (the germ of the rational map) to
`Spec 𝒪_{X,x} ⟶ Y`, and spreading out (`PartialMap.ofFromSpecStalk`) turns the lift
into a partial map defined at `x` and equivalent to the original rational map.

Everything in this file is general algebraic geometry with no Belyi-specific content;
it is a candidate for a mathlib PR, hence the mathlib namespaces.

## Main results

* `AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem_specializes`,
  `AlgebraicGeometry.Scheme.PartialMap.fromSpecStalkOfMem_specializes`:
  compatibility of `fromSpecStalkOfMem` with specialization.
* `AlgebraicGeometry.Scheme.RationalMap.mem_domain_of_valuationRing`: a rational map
  over `S` into a scheme proper over `S` is defined at every point whose stalk is a
  valuation ring.
* `AlgebraicGeometry.Scheme.RationalMap.toHom`: the extension of such a rational map
  to a morphism, together with `toHom_toRationalMap` and `isOver_toHom`.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

variable {X Y S : Scheme.{u}}

section Specializes

/-- `Opens.fromSpecStalkOfMem` is compatible with specialization: the canonical maps
`Spec 𝒪_{X,x} ⟶ Spec 𝒪_{X,y} ⟶ U` and `Spec 𝒪_{X,x} ⟶ U` agree for `x ⤳ y ∈ U`. -/
lemma Opens.fromSpecStalkOfMem_specializes (U : X.Opens) {x y : X} (h : x ⤳ y)
    (hy : y ∈ U) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ U.fromSpecStalkOfMem y hy =
      U.fromSpecStalkOfMem x (h.mem_open U.2 hy) := by
  rw [← cancel_mono U.ι, Category.assoc, Opens.fromSpecStalkOfMem_ι,
    Opens.fromSpecStalkOfMem_ι, SpecMap_stalkSpecializes_fromSpecStalk]

/-- `PartialMap.fromSpecStalkOfMem` is compatible with specialization. -/
lemma PartialMap.fromSpecStalkOfMem_specializes (f : X.PartialMap Y) {x y : X}
    (h : x ⤳ y) (hy : y ∈ f.domain) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ f.fromSpecStalkOfMem hy =
      f.fromSpecStalkOfMem (h.mem_open f.domain.2 hy) := by
  dsimp only [PartialMap.fromSpecStalkOfMem]
  rw [← Category.assoc, Opens.fromSpecStalkOfMem_specializes]

/-- The germ of a partial map at the generic point factors through the germ at any
point of its domain. -/
lemma PartialMap.fromFunctionField_eq [IrreducibleSpace X] (f : X.PartialMap Y) {x : X}
    (hx : x ∈ f.domain) :
    f.fromFunctionField =
      Spec.map (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)) ≫
        f.fromSpecStalkOfMem hx :=
  (f.fromSpecStalkOfMem_specializes ((genericPoint_spec X).specializes trivial) hx).symm

end Specializes

section Extend

variable [X.Over S] [Y.Over S]

/-- A rational map over `S` from an integral scheme into a scheme proper over `S` is
defined at every point whose local ring is a valuation ring (for instance at every
point of a regular integral scheme of dimension `≤ 1`).

This is the classical extension theorem for rational maps into proper schemes, via the
valuative criterion applied to the stalk. -/
theorem RationalMap.mem_domain_of_valuationRing [IsIntegral X] [IsProper (Y ↘ S)]
    (f : X ⤏ Y) [f.IsOver S] (x : X) [ValuationRing (X.presheaf.stalk x)] :
    x ∈ f.domain := by
  have hη : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hf : f.fromFunctionField ≫ (Y ↘ S) =
      X.fromSpecStalk (genericPoint X) ≫ (X ↘ S) :=
    ((RationalMap.equivFunctionField (X ↘ S) (Y ↘ S)).symm
      ⟨f, RationalMap.isOver_iff.mp inferInstance⟩).2
  have hvc : ValuativeCriterion (Y ↘ S) := by
    have h : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓
        @LocallyOfFiniteType) (Y ↘ S) := by
      rw [← IsProper.eq_valuativeCriterion]
      exact inferInstance
    exact h.1.1.1
  have w : f.fromFunctionField ≫ (Y ↘ S) =
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        X.fromSpecStalk x ≫ (X ↘ S) := by
    rw [hf, show CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
        X.presheaf.stalkSpecializes hη from rfl,
      SpecMap_stalkSpecializes_fromSpecStalk_assoc]
  let sq : ValuativeCommSq (Y ↘ S) :=
    { R := X.presheaf.stalk x
      commRing := inferInstance
      domain := inferInstance
      valuationRing := inferInstance
      K := X.functionField
      field := inferInstance
      algebra := inferInstance
      isFractionRing := inferInstance
      i₁ := f.fromFunctionField
      i₂ := X.fromSpecStalk x ≫ (X ↘ S)
      commSq := ⟨w⟩ }
  obtain ⟨l₀, hl₁, hl₂⟩ := (hvc sq).some.default
  let l : Spec (X.presheaf.stalk x) ⟶ Y := l₀
  have hl₁' : Spec.map (X.presheaf.stalkSpecializes hη) ≫ l = f.fromFunctionField := hl₁
  have hl₂' : l ≫ (Y ↘ S) = X.fromSpecStalk x ≫ (X ↘ S) := hl₂
  let g : X.PartialMap Y := PartialMap.ofFromSpecStalk (X ↘ S) (Y ↘ S) l hl₂'
  have hxg : x ∈ g.domain := PartialMap.mem_domain_ofFromSpecStalk (X ↘ S) (Y ↘ S) l hl₂'
  have hg : g.toRationalMap = f := by
    refine RationalMap.eq_of_fromFunctionField_eq _ _ ?_
    rw [RationalMap.fromFunctionField_toRationalMap,
      PartialMap.fromFunctionField_eq g hxg,
      PartialMap.fromSpecStalkOfMem_ofFromSpecStalk (X ↘ S) (Y ↘ S) l hl₂']
    exact hl₁'
  exact hg ▸ g.le_domain_toRationalMap hxg

variable (S) in
/-- A rational map over `S` from an integral scheme all of whose local rings are
valuation rings into a scheme proper over `S` is defined everywhere. -/
theorem RationalMap.domain_eq_top_of_valuationRing [IsIntegral X] [IsProper (Y ↘ S)]
    (f : X ⤏ Y) [f.IsOver S] (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) :
    f.domain = ⊤ :=
  eq_top_iff.mpr fun x _ ↦
    letI := hX x
    f.mem_domain_of_valuationRing (S := S) x

/-- A scheme separated over a separated scheme is separated. -/
lemma _root_.AlgebraicGeometry.Scheme.isSeparated_of_isSeparated_over (S : Scheme.{u})
    [S.IsSeparated] (Y : Scheme.{u}) [Y.Over S] [IsSeparated (Y ↘ S)] : Y.IsSeparated :=
  ⟨by rw [← terminal.comp_from (Y ↘ S)]; infer_instance⟩

variable (S) in
/-- The extension of a rational map over `S` from an integral scheme all of whose local
rings are valuation rings into a scheme proper over `S` to a morphism. -/
noncomputable def RationalMap.toHom [IsIntegral X] [IsProper (Y ↘ S)] [Y.IsSeparated]
    (f : X ⤏ Y) [f.IsOver S] (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) :
    X ⟶ Y :=
  (X.isoOfEq (f.domain_eq_top_of_valuationRing S hX) ≪≫ X.topIso).inv ≫ f.toPartialMap.hom

variable (S) in
lemma RationalMap.ι_toHom [IsIntegral X] [IsProper (Y ↘ S)] [Y.IsSeparated]
    (f : X ⤏ Y) [f.IsOver S] (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) :
    f.domain.ι ≫ f.toHom S hX = f.toPartialMap.hom := by
  have h : (X.isoOfEq (f.domain_eq_top_of_valuationRing S hX) ≪≫ X.topIso).hom =
      f.domain.ι := by
    simp only [Iso.trans_hom, Scheme.topIso_hom, Scheme.isoOfEq_hom_ι]
  rw [RationalMap.toHom, ← h, Iso.hom_inv_id_assoc]

variable (S) in
@[simp]
lemma RationalMap.toHom_toRationalMap [IsIntegral X] [IsProper (Y ↘ S)] [Y.IsSeparated]
    (f : X ⤏ Y) [f.IsOver S] (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) :
    (f.toHom S hX).toRationalMap = f := by
  have hη : genericPoint X ∈ f.domain :=
    (genericPoint_specializes _).mem_open f.domain.2 f.dense_domain.nonempty.choose_spec
  refine RationalMap.eq_of_fromFunctionField_eq _ _ ?_
  rw [RationalMap.fromFunctionField_toRationalMap, PartialMap.fromFunctionField,
    PartialMap.fromSpecStalkOfMem_toPartialMap,
    ← Opens.fromSpecStalkOfMem_ι f.domain _ hη, Category.assoc, f.ι_toHom S hX]
  conv_rhs => rw [← f.toRationalMap_toPartialMap, RationalMap.fromFunctionField_toRationalMap]
  rfl

variable (S) in
/-- The extension of a rational map over `S` is a morphism over `S`. -/
lemma RationalMap.isOver_toHom [IsIntegral X] [IsProper (Y ↘ S)] [Y.IsSeparated]
    [S.IsSeparated] (f : X ⤏ Y) [f.IsOver S]
    (hX : ∀ x : X, ValuationRing (X.presheaf.stalk x)) :
    (f.toHom S hX).IsOver S := by
  rw [Hom.isOver_iff]
  have h : (X.isoOfEq (f.domain_eq_top_of_valuationRing S hX) ≪≫ X.topIso).hom =
      f.domain.ι := by
    simp only [Iso.trans_hom, Scheme.topIso_hom, Scheme.isoOfEq_hom_ι]
  have hι : IsIso f.domain.ι := h ▸ inferInstance
  rw [← cancel_epi f.domain.ι, ← Category.assoc, f.ι_toHom S hX]
  have h2 : f.toPartialMap.hom.IsOver S := inferInstance
  rw [Hom.isOver_iff] at h2
  rw [Opens.ι_comp_over]
  exact h2

end Extend

end AlgebraicGeometry.Scheme
