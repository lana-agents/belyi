/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Rigidity
import Belyi.Ramification
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# A Belyi cover restricts to a finite smooth cover of `ℙ¹ ∖ {0, 1, ∞}`

This file provides the **`pi1`-free geometric half** of the compactification bridge behind the
rigidity input **B9** (taxis issue **#215**, parent survey **#210**; the `pi1`-gated packaging as
`FiniteEtale` is the sibling issue **#212**). For a degree-`≤ d` Belyi cover
`A : Belyi.BelyiCover k d` — a curve `X/k` with a finite dominant map `f := A.map : X ⟶ ℙ¹_k`
whose branch locus lies in `{0, 1, ∞}` — the restriction of `f` over the open thrice-punctured
line `ℙ¹_k ∖ {0, 1, ∞}` is finite and smooth (of relative dimension `0`, i.e. étale on the
mathematics; see the note on `Etale` below). This is the geometric object the rigidity finiteness
statement counts.

Everything here is stated in mathlib's own morphism-property vocabulary (`IsFinite`, `Smooth`); it
needs neither `chrisflav/pi1` nor the abstract Galois-category engine
of `Belyi/GaloisCoverFiniteness.lean` (taxis #211).

## Main definitions and results

* `Belyi.P1.zero_ne_genericPoint` / `one_ne_genericPoint` / `infty_ne_genericPoint`: the marked
  points are not the generic point of `ℙ¹` (their homogeneous ideals `(X₀)`, `(X₀ - X₁)`, `(X₁)`
  are nonzero, whereas the generic point has ideal `⊥`).
* `Belyi.isClosed_markedPoints`: `{0, 1, ∞} ⊆ ℙ¹_k` is closed — reusable infrastructure.
* `Belyi.puncturedLine k`: the open subscheme `ℙ¹_k ∖ {0, 1, ∞}`.
* `Belyi.BelyiCover.isFinite_restrict`: `f` restricted over the punctured line is finite.
* `Belyi.BelyiCover.smooth_restrict`: `f` restricted over the punctured line is smooth.

## The étale gap

The restriction is *finite* and *smooth*, hence mathematically étale (a finite morphism has relative
dimension `0`, so a smooth finite morphism is `SmoothOfRelativeDimension 0 = Etale`). mathlib v4.32
provides no lemma promoting `Smooth` + `IsFinite` (via quasi-finiteness) to `Etale`
(`SmoothOfRelativeDimension 0`); once such a lemma lands (or the relative-dimension-`0` fact for
finite morphisms is available), `Etale (A.map ∣_ puncturedLine k)` follows immediately from
`smooth_restrict` and `Etale.iff_smoothOfRelativeDimension_zero`.

## References

`references/rigidity-design.md`; the merged B2c `Belyi.smooth_morphismRestrict_of_disjoint_branch`
(`Belyi/Ramification.lean`); the survey on taxis **#210**.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

namespace P1

/-- The generic point of `ℙ¹` has homogeneous ideal `⊥`. -/
lemma genericPoint_toIdeal_eq_bot :
    (P1.genericPoint k).asHomogeneousIdeal.toIdeal = (⊥ : Ideal (MvPolynomial (Fin 2) k)) := by
  rw [show (P1.genericPoint k).asHomogeneousIdeal = ⊥ from rfl, HomogeneousIdeal.toIdeal_bot]

/-- The topological generic point of `ℙ¹` is the homogeneous prime `⟨0⟩`. -/
lemma genericPoint_eq :
    _root_.genericPoint (P1 k) = P1.genericPoint k :=
  (genericPoint_spec (P1 k)).eq (isGenericPoint_genericPoint k)

/-- The marked point `0 = [0:1]` is not the generic point of `ℙ¹`: its homogeneous ideal is
`(X₀) ≠ ⊥`, whereas the generic point has ideal `⊥`. -/
lemma zero_ne_genericPoint : P1.zero k ≠ _root_.genericPoint (P1 k) := by
  intro h
  have hId : Ideal.span {(X 0 : MvPolynomial (Fin 2) k)} =
      (P1.genericPoint k).asHomogeneousIdeal.toIdeal :=
    congrArg (fun x : ProjectiveSpectrum (P1Grading k) => x.asHomogeneousIdeal.toIdeal)
      (h.trans (genericPoint_eq k))
  rw [genericPoint_toIdeal_eq_bot] at hId
  have hmem : (X 0 : MvPolynomial (Fin 2) k) ∈ (⊥ : Ideal (MvPolynomial (Fin 2) k)) :=
    hId ▸ Ideal.subset_span rfl
  exact X_ne_zero (R := k) 0 (Ideal.mem_bot.mp hmem)

/-- The marked point `1 = [1:1]` is not the generic point of `ℙ¹`. -/
lemma one_ne_genericPoint : P1.one k ≠ _root_.genericPoint (P1 k) := by
  intro h
  have hId : Ideal.span {(X 0 - X 1 : MvPolynomial (Fin 2) k)} =
      (P1.genericPoint k).asHomogeneousIdeal.toIdeal :=
    congrArg (fun x : ProjectiveSpectrum (P1Grading k) => x.asHomogeneousIdeal.toIdeal)
      (h.trans (genericPoint_eq k))
  rw [genericPoint_toIdeal_eq_bot] at hId
  have hmem : (X 0 - X 1 : MvPolynomial (Fin 2) k) ∈ (⊥ : Ideal (MvPolynomial (Fin 2) k)) :=
    hId ▸ Ideal.subset_span rfl
  have hzero : (X 0 - X 1 : MvPolynomial (Fin 2) k) = 0 := Ideal.mem_bot.mp hmem
  have := congrArg (MvPolynomial.eval ![(1 : k), 0]) hzero
  simp at this

/-- The marked point `∞ = [1:0]` is not the generic point of `ℙ¹`. -/
lemma infty_ne_genericPoint : P1.infty k ≠ _root_.genericPoint (P1 k) := by
  intro h
  have hId : Ideal.span {(X 1 : MvPolynomial (Fin 2) k)} =
      (P1.genericPoint k).asHomogeneousIdeal.toIdeal :=
    congrArg (fun x : ProjectiveSpectrum (P1Grading k) => x.asHomogeneousIdeal.toIdeal)
      (h.trans (genericPoint_eq k))
  rw [genericPoint_toIdeal_eq_bot] at hId
  have hmem : (X 1 : MvPolynomial (Fin 2) k) ∈ (⊥ : Ideal (MvPolynomial (Fin 2) k)) :=
    hId ▸ Ideal.subset_span rfl
  exact X_ne_zero (R := k) 1 (Ideal.mem_bot.mp hmem)

end P1

/-- Each marked point has a closed singleton (it is a non-generic point of the one-dimensional
integral scheme `ℙ¹`). -/
lemma isClosed_singleton_markedPoint {x : P1 k} (hx : x ∈ markedPoints k) :
    IsClosed ({x} : Set (P1 k)) := by
  have hdim : ∀ z : P1 k, Ring.KrullDimLE 1 ((P1 k).presheaf.stalk z) :=
    fun z => P1.krullDimLE_one_stalk_P1 k z
  simp only [markedPoints, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact isClosed_singleton_of_ne_genericPoint hdim (P1.zero_ne_genericPoint k)
  · exact isClosed_singleton_of_ne_genericPoint hdim (P1.one_ne_genericPoint k)
  · exact isClosed_singleton_of_ne_genericPoint hdim (P1.infty_ne_genericPoint k)

/-- **The marked points `{0, 1, ∞}` form a closed subset of `ℙ¹_k`.** -/
lemma isClosed_markedPoints : IsClosed (markedPoints k) := by
  have h : markedPoints k = {P1.zero k} ∪ ({P1.one k} ∪ {P1.infty k}) := by
    ext x
    simp only [markedPoints, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  rw [h]
  refine (isClosed_singleton_markedPoint k (by simp)).union
    ((isClosed_singleton_markedPoint k (by simp)).union
      (isClosed_singleton_markedPoint k (by simp)))

/-- The open thrice-punctured projective line `ℙ¹_k ∖ {0, 1, ∞}`. -/
def puncturedLine : (P1 k).Opens where
  carrier := (markedPoints k)ᶜ
  is_open' := (isClosed_markedPoints k).isOpen_compl

@[simp] lemma coe_puncturedLine : (puncturedLine k : Set (P1 k)) = (markedPoints k)ᶜ := rfl

namespace BelyiCover

variable {k} [IsAlgClosed k] [CharZero k] {d : ℕ}

/-- The restriction of a Belyi cover over the punctured line is **finite**. -/
theorem isFinite_restrict (A : BelyiCover k d) :
    IsFinite (A.map ∣_ puncturedLine k) := by
  have := A.belyi.isFinite
  exact MorphismProperty.of_isPullback (P := @IsFinite)
    (isPullback_morphismRestrict A.map (puncturedLine k)).flip A.belyi.isFinite

/-- The restriction of a Belyi cover over the punctured line is **smooth** (B2c): the punctured
line avoids the branch locus `Branch f ⊆ {0, 1, ∞}`, so `f` is unramified — indeed smooth — there.
Since the restriction is also finite (`isFinite_restrict`), it is a finite smooth, hence étale,
cover; see the module docstring on the `Etale` gap. -/
theorem smooth_restrict (A : BelyiCover k d) :
    Smooth (A.map ∣_ puncturedLine k) := by
  have := A.belyi.locallyOfFinitePresentation
  haveI : LocallyOfFinitePresentation (A.map ∣_ puncturedLine k) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (isPullback_morphismRestrict A.map (puncturedLine k)).flip A.belyi.locallyOfFinitePresentation
  refine smooth_morphismRestrict_of_disjoint_branch A.map (puncturedLine k) ?_
  rw [coe_puncturedLine]
  refine Set.disjoint_left.mpr fun x hxU hxB => ?_
  exact hxU (A.belyi.branch_subset hxB)

end BelyiCover

end Belyi
