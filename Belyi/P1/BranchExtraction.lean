/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.PolynomialBranchLocus
import Belyi.P1.AffineMarkedPoint
import Belyi.Ramification
import Belyi.FunctionField
import Belyi.Dimension
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Perfect

/-!
# Forward B2: extracting the branch locus of a finite cover as `ℙ¹`-coordinates

For a finite, dominant morphism `f : X ⟶ ℙ¹_k` out of a curve `X` over an algebraically
closed field `k` of characteristic zero, this file packages the scheme-theoretic branch
locus `Branch f` into the data the forward direction of Belyi's theorem (taxis #51, the
assembly #188) consumes:

* **Finiteness + closed-point form.** `Branch f` is finite (`Belyi.finite_branch_of_isDominant`,
  the perfectness of `(ℙ¹_k).functionField` being automatic in characteristic zero), and every
  branch point is an affine `k`-point `[a : 1]` or `∞` — because a branch point is never the
  generic point (`genericPoint_notMem_branch`). The affine coordinates form a finite set
  `branchFinset f`, and `branch_subset_branchFinset` states the closed-point inclusion.
* **Image containment.** Given `g : k[X]` whose values on `branchFinset f` lie in `{0, 1}`, the
  polynomial self-map carries every branch point into the marked set:
  `polynomialSelfMap_image_branch_subset_markedPoints`. This is exactly the image-side hypothesis
  `hbf` of `isBelyiMap_comp_polynomialSelfMap`.

## Main results

* `Belyi.P1.genericPoint_notMem_branch`: a branch point of a finite dominant cover is not the
  generic point.
* `Belyi.P1.branchFinset`: the finite set of affine coordinates of the branch points.
* `Belyi.P1.branch_subset_branchFinset`: `Branch f ⊆ {[s:1] : s ∈ branchFinset f} ∪ {∞}`.
* `Belyi.P1.polynomialSelfMap_image_branch_subset_markedPoints`: the image containment.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open scoped Polynomial Belyi

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- In characteristic zero the function field of `ℙ¹_k` is a characteristic-zero field: it is a
`k`-algebra (`Belyi.instAlgebraFunctionField`) and the algebra map from the field `k` is
injective. Hence it is perfect, which discharges the `PerfectField` hypothesis of the
generic-étaleness / finite-branch machinery. -/
noncomputable instance instCharZeroFunctionField [CharZero k] :
    CharZero (P1 k).functionField :=
  charZero_of_injective_algebraMap (algebraMap k (P1 k).functionField).injective

/-- The generic point of `ℙ¹_k` has a non-closed singleton: its closure is the whole (irreducible)
space, so if `{η}` were closed it would be all of `ℙ¹`, forcing the distinct marked points `0` and
`1` to coincide. -/
theorem not_isClosed_singleton_genericPoint :
    ¬ IsClosed ({_root_.genericPoint (P1 k)} : Set (P1 k)) := by
  intro hcl
  have h1 : closure ({_root_.genericPoint (P1 k)} : Set (P1 k)) = Set.univ := by
    have h := genericPoint_spec (P1 k)
    simpa [IsGenericPoint, Set.top_eq_univ] using h
  rw [hcl.closure_eq] at h1
  have hz : zero k ∈ ({_root_.genericPoint (P1 k)} : Set (P1 k)) := by rw [h1]; trivial
  have ho : one k ∈ ({_root_.genericPoint (P1 k)} : Set (P1 k)) := by rw [h1]; trivial
  rw [Set.mem_singleton_iff] at hz ho
  exact zero_ne_one k (hz.trans ho.symm)

/-- The affine-point map `a ↦ [a : 1]` is injective: the homogeneous linear form `X₀ - a·X₁`
vanishes at `[a : 1]`, so equality of two such points forces the coordinates to agree. -/
lemma point_base_injective :
    Function.Injective
      (fun a : k => (point k a).base (IsLocalRing.closedPoint (CommRingCat.of k))) := by
  intro a b hab
  simp only [] at hab
  have hhom : (X 0 - C a * X 1 : MvPolynomial (Fin 2) k) ∈ P1Grading k 1 := by
    refine Submodule.sub_mem _ (X_mem_P1Grading k 0) ?_
    have hCa : (C a : MvPolynomial (Fin 2) k) ∈ P1Grading k 0 :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_C _ _)
    simpa using SetLike.mul_mem_graded hCa (X_mem_P1Grading k 1)
  have ha : (aeval ![a, 1] (X 0 - C a * X 1 : MvPolynomial (Fin 2) k)) = 0 := by simp
  have hmem : (X 0 - C a * X 1 : MvPolynomial (Fin 2) k) ∈
      ((point k a).base (IsLocalRing.closedPoint (CommRingCat.of k))).asHomogeneousIdeal.toIdeal :=
    (mem_affinePoint_iff k hhom).mpr ha
  rw [hab] at hmem
  have hb := (mem_affinePoint_iff k hhom).mp hmem
  have hba : b = a := by simpa [sub_eq_zero] using hb
  exact hba.symm

section Extraction

variable {X : Scheme.{u}} [CharZero k]

/-- **A branch point is never the generic point.** For a finite dominant morphism `f : X ⟶ ℙ¹` of
curves in characteristic zero, the generic point of `ℙ¹` is not a branch point: its only preimage
is the generic point of `X` (which is unramified by generic étaleness), because a non-generic point
of `X` is closed and its image under the closed map `f` would then make `{η}` closed in `ℙ¹`. -/
theorem genericPoint_notMem_branch (f : X ⟶ P1 k)
    [IsIntegral X] [NoetherianSpace X] [IsDominant f] [IsFinite f]
    [LocallyOfFinitePresentation f]
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x)) :
    _root_.genericPoint (P1 k) ∉ Branch f := by
  intro hmem
  rw [Belyi.mem_branch_iff] at hmem
  obtain ⟨x, hxram, hxeq⟩ := hmem
  have hgs : _root_.genericPoint X ∈ f.smoothLocus := Belyi.genericPoint_mem_smoothLocus f
  have hxg : x = _root_.genericPoint X := by
    by_contra hne
    have h1 : IsClosed ({x} : Set X) :=
      isClosed_singleton_of_ne_genericPoint hdim hne
    have h2 : IsClosed (f.base '' ({x} : Set X)) := f.isClosedMap _ h1
    rw [Set.image_singleton] at h2
    rw [show f.base x = _root_.genericPoint (P1 k) from hxeq] at h2
    exact not_isClosed_singleton_genericPoint k h2
  have hnr : _root_.genericPoint X ∉ Ram f := by
    rw [Belyi.mem_ram_iff, not_not, ← Scheme.Hom.mem_smoothLocus]; exact hgs
  exact hnr (hxg ▸ hxram)

/-- The set of affine coordinates of the branch points of a finite dominant cover is finite: it
injects into the finite branch locus via `a ↦ [a : 1]`. -/
theorem finite_branchCoords (f : X ⟶ P1 k)
    [IsIntegral X] [NoetherianSpace X] [IsDominant f] [IsFinite f]
    [LocallyOfFinitePresentation f]
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x)) :
    {a : k | (point k a).base (IsLocalRing.closedPoint (CommRingCat.of k)) ∈ Branch f}.Finite :=
  (Belyi.finite_branch_of_isDominant f hdim).preimage (point_base_injective k).injOn

/-- The **finite set of affine branch coordinates** of a finite dominant cover `f : X ⟶ ℙ¹`. This
is the `Finset k` the combined polynomial reduction (taxis #185) consumes. -/
noncomputable def branchFinset (f : X ⟶ P1 k)
    [IsIntegral X] [NoetherianSpace X] [IsDominant f] [IsFinite f]
    [LocallyOfFinitePresentation f]
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x)) : Finset k :=
  (finite_branchCoords k f hdim).toFinset

@[simp]
lemma mem_branchFinset (f : X ⟶ P1 k)
    [IsIntegral X] [NoetherianSpace X] [IsDominant f] [IsFinite f]
    [LocallyOfFinitePresentation f]
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x)) {a : k} :
    a ∈ branchFinset k f hdim ↔
      (point k a).base (IsLocalRing.closedPoint (CommRingCat.of k)) ∈ Branch f :=
  Set.Finite.mem_toFinset _

/-- **Closed-point form of the branch locus (Forward B2, part 1).** Every branch point of a finite
dominant cover `f : X ⟶ ℙ¹` is an affine point `[s : 1]` with `s` in the finite coordinate set
`branchFinset f`, or the point at infinity. -/
theorem branch_subset_branchFinset [IsAlgClosed k] (f : X ⟶ P1 k)
    [IsIntegral X] [NoetherianSpace X] [IsDominant f] [IsFinite f]
    [LocallyOfFinitePresentation f]
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x)) :
    Branch f ⊆
      {y : P1 k | ∃ s ∈ branchFinset k f hdim,
        y = (point k s).base (IsLocalRing.closedPoint (CommRingCat.of k))} ∪ {infty k} := by
  intro y hy
  have hyne : y ≠ _root_.genericPoint (P1 k) :=
    fun h => genericPoint_notMem_branch k f hdim (h ▸ hy)
  rcases exists_eq_point_or_eq_infty_of_ne_genericPoint k y hyne with ⟨a, hya⟩ | hyinf
  · refine Or.inl ⟨a, ?_, hya⟩
    rw [mem_branchFinset]
    exact hya ▸ hy
  · exact Or.inr hyinf

/-- **Image containment (Forward B2, part 2).** If a non-constant `g : k[X]` sends every affine
branch coordinate of `f` into `{0, 1}`, then the polynomial self-map `x ↦ g(x)` carries the whole
branch locus of `f` into the marked set `{0, 1, ∞}`. This is the image-side hypothesis `hbf` of
`Belyi.P1.isBelyiMap_comp_polynomialSelfMap`. -/
theorem polynomialSelfMap_image_branch_subset_markedPoints [IsAlgClosed k] (f : X ⟶ P1 k)
    [IsIntegral X] [NoetherianSpace X] [IsDominant f] [IsFinite f]
    [LocallyOfFinitePresentation f]
    (hdim : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x))
    (g : k[X]) (hg_deg : 0 < g.natDegree)
    (hg : ∀ s ∈ branchFinset k f hdim,
      Polynomial.aeval s g = 0 ∨ Polynomial.aeval s g = 1) :
    (polynomialSelfMap k g hg_deg) '' Branch f ⊆ Belyi.markedPoints k := by
  rintro z ⟨y, hy, rfl⟩
  have hyne : y ≠ _root_.genericPoint (P1 k) :=
    fun h => genericPoint_notMem_branch k f hdim (h ▸ hy)
  rcases exists_eq_point_or_eq_infty_of_ne_genericPoint k y hyne with ⟨a, hya⟩ | hyinf
  · have ha_mem : a ∈ branchFinset k f hdim := by rw [mem_branchFinset]; exact hya ▸ hy
    have himg : (polynomialSelfMap k g hg_deg).base y =
        (point k (Polynomial.aeval a g)).base (IsLocalRing.closedPoint (CommRingCat.of k)) := by
      rw [hya]
      exact polynomialSelfMap_point_closedPoint k g hg_deg a
    rw [himg]
    rcases hg a ha_mem with h0 | h1
    · rw [h0, point_base_eq_zero]; exact Belyi.zero_mem_markedPoints k
    · rw [h1, point_base_eq_one]; exact Belyi.one_mem_markedPoints k
  · have himg : (polynomialSelfMap k g hg_deg).base y = infty k := by
      rw [hyinf]; exact polynomialSelfMap_infty k g hg_deg
    rw [himg]; exact Belyi.infty_mem_markedPoints k

end Extraction

end Belyi.P1
