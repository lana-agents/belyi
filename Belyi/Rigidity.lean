/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.BelyiMap
import Belyi.Curve.Basic
import Belyi.FunctionField
import Belyi.P1.Curve
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Rigidity input (B9): the sanctioned axiom of the project

This file states statement **B9** of `references/proof-outline.md` — the deep external
input to the *converse* direction of Belyi's theorem — as the **single, isolated
`axiom`** of the whole project. See `references/rigidity-design.md` for the full design
decision: the geometry-to-group-theory bridge (Riemann existence + finite generation of
the étale fundamental group of the thrice-punctured line) is genuinely far from mathlib
v4.32, so it is axiomatized here, in one clearly-named place, and nothing on the *forward*
direction depends on this file.

## Main definitions

* `Belyi.Scheme.Hom.base_genericPoint`: a dominant morphism of irreducible schemes sends
  the generic point to the generic point.
* `Belyi.functionFieldAlgebra`: the induced extension `K(Y) → K(X)` of function fields of
  a dominant morphism `f : X ⟶ Y`.
* `Belyi.degree f`: the function-field degree `[K(X) : K(Y)]` (base-field-invariant,
  matching the classical degree; `0` when the extension is infinite, which never occurs
  for a finite morphism but is harmless for the statement).
* `Belyi.BelyiCover k d`: a degree-`≤ d` Belyi cover of `ℙ¹_k` — a curve `X/k` with a
  finite dominant Belyi map `f : X ⟶ ℙ¹_k` of function-field degree `≤ d`.
* `Belyi.BelyiCover.Iso k d`: the quotient of `BelyiCover k d` by isomorphism over `ℙ¹_k`.

## Main statement

* `Belyi.rigidity_finiteness`: **the** axiom — for `k` algebraically closed of
  characteristic `0`, there are only finitely many degree-`≤ d` Belyi covers of `ℙ¹_k` up
  to isomorphism over `ℙ¹_k`.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory

/-- A dominant morphism of irreducible schemes sends the generic point to the generic
point. (Both spaces are sober, being schemes, so the generic point is unique.) -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.base_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace X] [IrreducibleSpace Y] [IsDominant f] :
    f.base (genericPoint X) = genericPoint Y := by
  refine ((genericPoint_spec Y).eq ?_).symm
  have h := (genericPoint_spec X).image f.continuous
  rwa [Set.image_univ, f.denseRange.closure_range] at h

/-- The function-field extension `K(Y) → K(X)` induced by a dominant morphism
`f : X ⟶ Y` of irreducible schemes: the stalk map of `f` at the generic point of `X`,
whose source `𝒪_{Y, f η_X} = 𝒪_{Y, η_Y} = K(Y)` is identified with `K(Y)` via
`Scheme.Hom.base_genericPoint`. -/
@[reducible] noncomputable def functionFieldAlgebra {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace X] [IrreducibleSpace Y] [IsDominant f] :
    Algebra Y.functionField X.functionField :=
  (eqToHom (show Y.functionField = Y.presheaf.stalk (f.base (genericPoint X)) by
      rw [f.base_genericPoint]) ≫ f.stalkMap (genericPoint X)).hom.toAlgebra

/-- The **degree** of a dominant morphism `f : X ⟶ Y` of irreducible schemes: the degree
`[K(X) : K(Y)]` of the induced extension of function fields. It is `0` when the extension
is infinite; for a finite morphism it is the classical degree. -/
noncomputable def degree {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace X] [IrreducibleSpace Y] [IsDominant f] : ℕ :=
  letI := functionFieldAlgebra f
  Module.finrank Y.functionField X.functionField

/-- A degree-`≤ d` **Belyi cover** of `ℙ¹_k`: a curve `X/k` with a finite dominant
`f : X ⟶ ℙ¹_k` branched only over `{0, 1, ∞}`, of function-field degree `≤ d`. -/
structure BelyiCover (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (d : ℕ) where
  /-- The total space of the cover. -/
  carrier : Scheme.{u}
  [over : carrier.Over (Spec (CommRingCat.of k))]
  [curve : IsCurveOver k carrier]
  /-- The finite dominant map to `ℙ¹_k`. -/
  map : carrier ⟶ P1 k
  /-- The map is a Belyi map: finite with branch locus in `{0, 1, ∞}`. -/
  belyi : IsBelyiMap k map
  /-- The map is dominant. -/
  dominant : IsDominant map
  /-- The function-field degree is at most `d`. -/
  deg_le :
    haveI := IsCurveOver.isIntegral k carrier
    haveI := dominant
    degree map ≤ d

namespace BelyiCover

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (d : ℕ)

/-- Two Belyi covers are isomorphic over `ℙ¹_k` when there is an isomorphism of the
carriers commuting with the maps to `ℙ¹_k`. -/
def IsoRel : BelyiCover k d → BelyiCover k d → Prop :=
  fun A B => ∃ e : A.carrier ≅ B.carrier, e.hom ≫ B.map = A.map

lemma isoRel_refl (A : BelyiCover k d) : IsoRel k d A A :=
  ⟨Iso.refl A.carrier, by simp⟩

lemma isoRel_symm {A B : BelyiCover k d} (h : IsoRel k d A B) : IsoRel k d B A := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, by rw [Iso.symm_hom, ← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]⟩

lemma isoRel_trans {A B C : BelyiCover k d} (hAB : IsoRel k d A B) (hBC : IsoRel k d B C) :
    IsoRel k d A C := by
  obtain ⟨e, he⟩ := hAB
  obtain ⟨g, hg⟩ := hBC
  exact ⟨e ≪≫ g, by rw [Iso.trans_hom, Category.assoc, hg, he]⟩

/-- The setoid of Belyi covers modulo isomorphism over `ℙ¹_k`. -/
def isoSetoid : Setoid (BelyiCover k d) where
  r := IsoRel k d
  iseqv := ⟨isoRel_refl k d, isoRel_symm k d, isoRel_trans k d⟩

/-- Isomorphism classes of degree-`≤ d` Belyi covers of `ℙ¹_k` over `ℙ¹_k`. -/
def Iso : Type (u + 1) := Quotient (isoSetoid k d)

end BelyiCover

/-- **B9 (rigidity input), axiomatized.** For `k` algebraically closed of characteristic
`0` and any `d`, there are only finitely many degree-`≤ d` Belyi covers of `ℙ¹_k` up to
isomorphism over `ℙ¹_k`.

Justification (NOT formalized — this is the Riemann-existence content the project declines
to build against mathlib v4.32, see `references/rigidity-design.md`): such covers
correspond to finite `F₂`-sets of cardinality `≤ d`, and a finitely generated group has
only finitely many subgroups of bounded index
(`Belyi.finite_boundedIndex_subgroups_freeGroupTwo`, issue #52b).

Per taxis #201 this is stated as a `theorem` with `sorry` rather than an `axiom`, so that
the outstanding proof obligation is surfaced honestly (it shows up as `sorryAx` in
`#print axioms` and as a `sorry` warning) and tracked as a concrete goal. The proof is the
research-grade rigidity content scoped in issue #194 (de-axiomatize B9); see
`references/rigidity-design.md`. -/
theorem rigidity_finiteness (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (d : ℕ) :
    Finite (BelyiCover.Iso k d) := sorry

end Belyi
