/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.ChartCoord
import Belyi.P1.BaseChangeIso
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.PID

/-!
# `ℙ¹` is an integral curve

Reusable curve facts about the projective line `Belyi.P1 k = Proj (P1Grading k)` over a
field `k`:

* `Belyi.P1.instIrreducibleSpace : IrreducibleSpace (P1 k)` — the homogeneous prime `⟨0⟩`
  is a generic point, so `ℙ¹` is irreducible;
* `Belyi.P1.instIsReduced : IsReduced (P1 k)` — each standard chart `Spec (Away (Xᵢ))` is
  reduced because `Away (Xᵢ) ≅ k[T]` is a domain;
* `Belyi.P1.instIsIntegral : IsIntegral (P1 k)` — integral = irreducible + reduced;
* `Belyi.P1.krullDimLE_one_stalk_P1 (x : P1 k) : Ring.KrullDimLE 1 ((P1 k).presheaf.stalk x)`
  — the stalk at `x` is a localization of the chart ring `Away (Xᵢ) ≅ k[T]` (Krull dimension
  one), so it has Krull dimension at most one.

These are the topological/dimension-theoretic inputs required by the downstream
fiber-finiteness lemma for finite maps out of `ℙ¹`.

The standard charts and the identification of their coordinate rings with `k[T]` are supplied
by `Belyi/P1/ChartCoord.lean` (`awayChartEquivOne`, `awayChartEquivZero`); the two-chart cover
`{D₊(X₀), D₊(X₁)}` and the containment of the irrelevant ideal in `⟨X₀, X₁⟩` are supplied by
`Belyi/P1/BaseChangeIso.lean` (`coordCover`, `irrelevant_le_span_X`).
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open scoped Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-! ### Krull dimension of the stalks -/

/-- The coordinate ring of the standard chart `D₊(Xᵢ)` of `ℙ¹` has Krull dimension one:
`Γ(ℙ¹, D₊(Xᵢ)) ≅ Away (Xᵢ) ≅ k[T]`, and `k[T]` is a one-dimensional principal ideal domain. -/
lemma chart_ringKrullDim_eq_one (i : Fin 2) :
    ringKrullDim Γ(Proj (P1Grading k), Proj.basicOpen (P1Grading k) (X i)) = 1 := by
  match i with
  | 0 =>
    rw [ringKrullDim_eq_of_ringEquiv ((Proj.basicOpenIsoAway (P1Grading k) (X 0)
        (X_mem_P1Grading k 0) one_pos).commRingCatIsoToRingEquiv.symm.trans
        (awayChartEquivZero k).toRingEquiv),
      IsPrincipalIdealRing.ringKrullDim_eq_one (Polynomial k) (Polynomial.not_isField k)]
  | 1 =>
    rw [ringKrullDim_eq_of_ringEquiv ((Proj.basicOpenIsoAway (P1Grading k) (X 1)
        (X_mem_P1Grading k 1) one_pos).commRingCatIsoToRingEquiv.symm.trans
        (awayChartEquivOne k).toRingEquiv),
      IsPrincipalIdealRing.ringKrullDim_eq_one (Polynomial k) (Polynomial.not_isField k)]

/-- Every point of `ℙ¹` lies in one of the two standard charts `D₊(X₀)`, `D₊(X₁)`: a homogeneous
prime containing both `X₀` and `X₁` would contain the irrelevant ideal. -/
lemma exists_mem_basicOpen_X (x : Proj (P1Grading k)) :
    ∃ i : Fin 2, x ∈ Proj.basicOpen (P1Grading k) (X i) := by
  have htop := Proj.iSup_basicOpen_eq_top (P1Grading k)
    (fun i : Fin 2 => (X i : MvPolynomial (Fin 2) k)) (irrelevant_le_span_X k)
  have hx : x ∈ ⨆ i, Proj.basicOpen (P1Grading k) (X i) := by
    rw [htop]; exact TopologicalSpace.Opens.mem_top x
  exact TopologicalSpace.Opens.mem_iSup.mp hx

/-- **The stalks of `ℙ¹` have Krull dimension at most one.**  For `x : ℙ¹`, the stalk
`𝒪_{ℙ¹, x}` is a localization of the chart ring `Γ(ℙ¹, D₊(Xᵢ)) ≅ k[T]` at the prime of `x`;
its Krull dimension equals the height of that prime, which is bounded by
`ringKrullDim k[T] = 1`. -/
theorem krullDimLE_one_stalk_P1 (x : P1 k) :
    Ring.KrullDimLE 1 ((P1 k).presheaf.stalk x) := by
  obtain ⟨i, hxi⟩ := exists_mem_basicOpen_X k x
  have hV : IsAffineOpen (X := P1 k) (Proj.basicOpen (P1Grading k) (X i)) :=
    Proj.isAffineOpen_basicOpen (P1Grading k) (X i) (X_mem_P1Grading k i) one_pos
  letI : Algebra Γ(P1 k, Proj.basicOpen (P1Grading k) (X i)) ((P1 k).presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk (P1 k).presheaf ⟨x, hxi⟩
  set I := (hV.primeIdealOf ⟨x, hxi⟩).asIdeal with hI
  haveI : I.IsPrime := (hV.primeIdealOf ⟨x, hxi⟩).isPrime
  haveI : IsLocalization.AtPrime ((P1 k).presheaf.stalk x) I :=
    hV.isLocalization_stalk ⟨x, hxi⟩
  rw [Ring.krullDimLE_iff, Nat.cast_one]
  calc ringKrullDim ((P1 k).presheaf.stalk x)
      = (I.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height I ((P1 k).presheaf.stalk x)
    _ ≤ ringKrullDim Γ(P1 k, Proj.basicOpen (P1Grading k) (X i)) :=
        Ideal.height_le_ringKrullDim_of_isPrime
    _ = 1 := chart_ringKrullDim_eq_one k i

/-! ### Reducedness -/

/-- The chart coordinate rings `Away (Xᵢ) ≅ k[T]` are reduced (they are integral domains). -/
lemma isReduced_away_X (i : Fin 2) : _root_.IsReduced (Away (P1Grading k) (X i)) := by
  fin_cases i
  · exact isReduced_of_injective (awayChartEquivZero k).toRingHom (awayChartEquivZero k).injective
  · exact isReduced_of_injective (awayChartEquivOne k).toRingHom (awayChartEquivOne k).injective

/-- **`ℙ¹` is reduced.**  Reducedness is local, and each standard chart `Spec (Away (Xᵢ))` is
reduced because `Away (Xᵢ) ≅ k[T]` is a domain. -/
instance instIsReduced : IsReduced (P1 k) := by
  haveI : ∀ i, IsReduced ((coordCover k).openCover.X i) := by
    intro i
    exact (affine_isReduced_iff ((coordCover k).X i)).mpr (isReduced_away_X k i)
  exact IsReduced.of_openCover (P1 k) (coordCover k).openCover

/-! ### Irreducibility -/

/-- The generic point of `ℙ¹`: the homogeneous prime `⟨0⟩` of `k[X₀, X₁]`, which is a valid
point of `Proj` since it does not contain the irrelevant ideal (`X₀ ≠ 0`). -/
noncomputable def genericPoint : ProjectiveSpectrum (P1Grading k) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    rw [HomogeneousIdeal.toIdeal_bot]
    infer_instance
  not_irrelevant_le := fun h => by
    apply X_ne_zero (0 : Fin 2) (R := k)
    have hx0 : (X 0 : MvPolynomial (Fin 2) k) ∈ HomogeneousIdeal.irrelevant (P1Grading k) :=
      HomogeneousIdeal.mem_irrelevant_of_mem (P1Grading k) one_pos (X_mem_P1Grading k 0)
    have hmem : (X 0 : MvPolynomial (Fin 2) k) ∈ (⊥ : HomogeneousIdeal (P1Grading k)).toIdeal :=
      toIdeal_le_toIdeal_iff.mpr h hx0
    rwa [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at hmem

/-- The closure of the generic point `⟨0⟩` is all of `ℙ¹`: it is the zero locus of `⟨0⟩`, which
is everything. -/
lemma isGenericPoint_genericPoint :
    IsGenericPoint (genericPoint k) (Set.univ : Set (Proj (P1Grading k))) := by
  rw [isGenericPoint_def, ← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    ProjectiveSpectrum.vanishingIdeal_singleton,
    show (genericPoint k).asHomogeneousIdeal = ⊥ from rfl, HomogeneousIdeal.coe_bot]
  exact ProjectiveSpectrum.zeroLocus_singleton_zero (P1Grading k)

/-- **`ℙ¹` is irreducible.**  It has the generic point `⟨0⟩`, whose closure is the whole space. -/
instance instIrreducibleSpace : IrreducibleSpace (P1 k) := by
  rw [irreducibleSpace_def]
  exact (isGenericPoint_genericPoint k).isIrreducible

/-! ### Integrality -/

/-- **`ℙ¹` is integral**: it is irreducible and reduced. -/
instance instIsIntegral : IsIntegral (P1 k) :=
  isIntegral_of_irreducibleSpace_of_isReduced (P1 k)

end Belyi.P1
