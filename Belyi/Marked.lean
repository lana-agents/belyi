/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Curve.Existence
import Belyi.Curve.SmoothStalk
import Belyi.Dimension
import Belyi.P1.BranchExtraction
import Belyi.P1.PolynomialBranchLocus
import Belyi.P1.PolynomialMarkedBranch
import Belyi.P1.MarkedPointMatching
import Belyi.Polynomial.ReductionCombined

/-!
# Marked curves (B13): a Belyi map carrying prescribed points into `{0, 1, ∞}`

This file delivers the **model form** of statement **B13** of `references/proof-outline.md`:
the strengthening of the forward direction in which a prescribed finite set of closed points is
folded into the branch data, so that it lands inside the fibre over `{0, 1, ∞}`.

Working over an algebraically closed field `k` of characteristic zero that is algebraic over `ℚ`
(a copy of `ℚ̄`), the main result

* `Belyi.exists_isBelyiMap_marked_of_isCurveOver` : for a curve `X` over `k` and any finite set
  `S` of closed points of `X`, there is a Belyi map `f : X ⟶ ℙ¹_k` with `f '' S ⊆ {0, 1, ∞}`,

is proved by rerunning the forward-direction assembly (`Belyi/Forward.lean`, #188) with the marked
set folded into the coordinates fed to the polynomial reduction:

1. **B1** gives a finite surjective `f₀ : X ⟶ ℙ¹_k`.
2. Besides the affine branch coordinates `branchFinset f₀` (**B2**), we also collect the affine
   coordinates of the images `f₀ '' S` of the marked points (`markCoords`, finite because `S` is).
3. **B6∘B7** produces `g : ℚ[X]` sending *both* coordinate sets into `{0, 1}` and with all critical
   values in `{0, 1}`.
4. **B4/B5** then makes `f₀ ≫ polynomialSelfMap ĝ` a Belyi map
   (`isBelyiMap_comp_polynomialSelfMap`), and the extra `markCoords` control forces
   `polynomialSelfMap ĝ` to carry `f₀ '' S` into
   `{0, 1, ∞}`, i.e. `S ⊆ (f₀ ≫ polynomialSelfMap ĝ)⁻¹({0, 1, ∞})`.

The image-side control is factored through
`Belyi.P1.polynomialSelfMap_image_subset_markedPoints`, a common generalisation of the branch
version `Belyi.P1.polynomialSelfMap_image_branch_subset_markedPoints` (#187) to an arbitrary set of
non-generic points whose affine coordinates `g` sends into `{0, 1}`.

Base-changing to `ℂ` and packaging the pair `(X, f)` as definable over `ℚ̄` — together with the
`MarkedBelyiPair` structure the Belyi-cuspidalization consumers expect — is the natural follow-up,
on the same footing as the base-change/pair layer of the forward direction; see the note on the
issue.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory
open scoped Polynomial Belyi

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}

/-- **Marked image containment.** If a non-constant `g : k[X]` sends the affine coordinate of every
affine point of a set `Z ⊆ ℙ¹_k` into `{0, 1}` and `Z` avoids the generic point, then the
polynomial self-map `x ↦ g(x)` carries `Z` into the marked set `{0, 1, ∞}`.

This is the common core of the branch-image containment
`Belyi.P1.polynomialSelfMap_image_branch_subset_markedPoints` (where `Z = Branch f`) and the
marked-point containment used by the marked forward direction (where `Z = f₀ '' S`). -/
theorem polynomialSelfMap_image_subset_markedPoints
    (g : k[X]) (hd : 0 < g.natDegree) (Z : Set (P1 k))
    (hgen : _root_.genericPoint (P1 k) ∉ Z)
    (hcoord : ∀ a : k,
      (point k a).base (IsLocalRing.closedPoint (CommRingCat.of k)) ∈ Z →
        Polynomial.aeval a g = 0 ∨ Polynomial.aeval a g = 1) :
    (polynomialSelfMap k g hd) '' Z ⊆ Belyi.markedPoints k := by
  rintro z ⟨y, hy, rfl⟩
  have hyne : y ≠ _root_.genericPoint (P1 k) := fun h => hgen (h ▸ hy)
  rcases exists_eq_point_or_eq_infty_of_ne_genericPoint k y hyne with ⟨a, hya⟩ | hyinf
  · have himg : (polynomialSelfMap k g hd).base y =
        (point k (Polynomial.aeval a g)).base (IsLocalRing.closedPoint (CommRingCat.of k)) := by
      rw [hya]
      exact polynomialSelfMap_point_closedPoint k g hd a
    rw [himg]
    rcases hcoord a (hya ▸ hy) with h0 | h1
    · rw [h0, point_base_eq_zero]; exact Belyi.zero_mem_markedPoints k
    · rw [h1, point_base_eq_one]; exact Belyi.one_mem_markedPoints k
  · have himg : (polynomialSelfMap k g hd).base y = infty k := by
      rw [hyinf]; exact polynomialSelfMap_infty k g hd
    rw [himg]; exact Belyi.infty_mem_markedPoints k

end Belyi.P1

namespace Belyi

open AlgebraicGeometry CategoryTheory
open scoped Polynomial

/-- **Marked forward direction of Belyi's theorem, model form (B13).** Let `X` be a curve over an
algebraically closed field `k` of characteristic zero that is algebraic over `ℚ` — i.e. over `ℚ̄` —
and let `S` be a finite set of closed points of `X`. Then there is a Belyi map `f : X ⟶ ℙ¹_k`
carrying `S` into the fibre over the marked set: `∀ s ∈ S, f s ∈ {0, 1, ∞}`.

The map is `f₀ ≫ polynomialSelfMap ĝ` for a B1 cover `f₀` and the reduction polynomial
`ĝ = g.map (algebraMap ℚ k)`, where `g` is produced by B6∘B7 fed with *both* the affine branch
coordinates of `f₀` and the affine coordinates of the images `f₀ '' S` of the marked points. -/
theorem exists_isBelyiMap_marked_of_isCurveOver
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X]
    (S : Set X) (hSfin : S.Finite) (hScl : ∀ s ∈ S, IsClosed ({s} : Set X)) :
    ∃ f : X ⟶ P1 k, IsBelyiMap k f ∧ ∀ s ∈ S, f.base s ∈ Belyi.markedPoints k := by
  classical
  -- B1: a finite surjective cover `f₀ : X ⟶ ℙ¹_k`.
  haveI : IsIntegral X := IsCurveOver.isIntegral k X
  obtain ⟨f₀, hf₀fin, hf₀surj⟩ := exists_isFinite_surjective_hom_to_P1 k X
  haveI : IsFinite f₀ := hf₀fin
  haveI : IsDominant f₀ := ⟨hf₀surj.denseRange⟩
  haveI : IsNoetherian (P1 k) := isNoetherian_of_over (P1 k) (Spec (CommRingCat.of k))
  haveI : LocallyOfFinitePresentation f₀ := inferInstance
  haveI : IsNoetherian X := isNoetherian_of_over X (Spec (CommRingCat.of k))
  have hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
    fun x => krullDimLE_one_stalk_of_isCurveOver k X x
  -- The images of the marked points avoid the generic point (they are closed points and `f₀` is a
  -- closed map, while the generic point of `ℙ¹` is not closed).
  have hSgen : _root_.genericPoint (P1 k) ∉ f₀.base '' S := by
    rintro ⟨s, hs, hseq⟩
    have hcl : IsClosed (f₀.base '' ({s} : Set X)) := f₀.isClosedMap _ (hScl s hs)
    rw [Set.image_singleton, hseq] at hcl
    exact P1.not_isClosed_singleton_genericPoint k hcl
  -- B2 plus the marked coordinates: the affine coordinates of `f₀ '' S`.
  have hmarkFin :
      {a : k | (P1.point k a).base (IsLocalRing.closedPoint (CommRingCat.of k)) ∈
        f₀.base '' S}.Finite :=
    (hSfin.image f₀.base).preimage (P1.point_base_injective k).injOn
  set S₀ : Finset k := P1.branchFinset k f₀ hdim ∪ hmarkFin.toFinset with hS₀
  -- B6∘B7: a reduction polynomial `g : ℚ[X]` sending `S₀` into `{0,1}`, critical values in `{0,1}`.
  obtain ⟨g, hgne, hgS, hgcrit⟩ := exists_aeval_mem_and_critVal_mem_zeroOne (K := k) S₀
  have hinj : Function.Injective (algebraMap ℚ k) := (algebraMap ℚ k).injective
  have hd : 0 < (g.map (algebraMap ℚ k)).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective hinj]
    exact Nat.pos_of_ne_zero hgne
  -- The values of `ĝ = g.map (algebraMap ℚ k)` on both coordinate sets lie in `{0,1}`.
  have hval : ∀ a ∈ S₀,
      Polynomial.aeval a (g.map (algebraMap ℚ k)) = 0 ∨
        Polynomial.aeval a (g.map (algebraMap ℚ k)) = 1 := by
    intro a ha
    rw [Polynomial.aeval_map_algebraMap]
    exact hgS a ha
  refine ⟨f₀ ≫ P1.polynomialSelfMap k (g.map (algebraMap ℚ k)) hd, ?_, ?_⟩
  · -- B4/B5: the composite is a Belyi map.
    refine P1.isBelyiMap_comp_polynomialSelfMap k (g.map (algebraMap ℚ k)) hd f₀ ?_ ?_
    · refine P1.polynomialSelfMap_image_branch_subset_markedPoints k f₀ hdim
        (g.map (algebraMap ℚ k)) hd ?_
      intro s hs
      exact hval s (Finset.mem_union_left _ hs)
    · exact branch_map_polynomialSelfMap_subset_markedPoints hgne hgcrit hd
  · -- The marked points land in the fibre over `{0,1,∞}`.
    have himg : (P1.polynomialSelfMap k (g.map (algebraMap ℚ k)) hd) '' (f₀.base '' S) ⊆
        Belyi.markedPoints k := by
      refine P1.polynomialSelfMap_image_subset_markedPoints
        (g.map (algebraMap ℚ k)) hd _ hSgen ?_
      intro a ha
      exact hval a (Finset.mem_union_right _ (hmarkFin.mem_toFinset.mpr ha))
    intro s hs
    show (f₀ ≫ P1.polynomialSelfMap k (g.map (algebraMap ℚ k)) hd) s ∈ Belyi.markedPoints k
    rw [Scheme.Hom.comp_apply]
    exact himg ⟨f₀.base s, ⟨s, hs, rfl⟩, rfl⟩

end Belyi
