/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Anabelian.LocAn
import Belyi.Marked
import Belyi.Converse.PuncturedLineBelyi

/-!
# The Belyi input of Belyi cuspidalisation ([AbsTopII] Example 3.6 (i))

[AbsTopII] Example 3.6 (i) (`Topics in Absolute Anabelian Geometry II.txt` l.4620–4636): "Let `P`
be a copy of the projective line minus three points …; `V` an arbitrary hyperbolic curve …;
`U ⊆ V` a nonempty open subscheme … Suppose that `U` [hence also `V`] is defined over a number
field. Then it follows from the existence of Belyi maps [cf. [Belyi]; [Mzk7]] that, for some
nonempty open subscheme `W ⊆ U`, there exists a diagram `W → U → V`, `β : W → P` [where the
`→`'s are the natural open immersions; the "Belyi map" `β` is finite étale]."

We prove this over an algebraically closed field `k` algebraic over `ℚ` (i.e. `k = ℚ̄`), from the
marked form of Belyi's theorem (`Belyi.exists_isBelyiMap_marked_of_isCurveOver`, the points of
`X̄ ∖ U` are sent into `{0, 1, ∞}`) and the étaleness of a Belyi map over the thrice-punctured
line (`Belyi.IsBelyiMap.etale_morphismRestrict_puncturedLine`):

* `Belyi.Anabelian.finite_compl_of_isCurveOver`: a nonempty open of a curve has finite
  complement;
* `Belyi.Anabelian.exists_belyi_open_le`: for a curve `X̄` over `k` and a nonempty open `U ⊆ X̄`,
  there is a Belyi map `f : X̄ ⟶ ℙ¹` such that
  `W = f⁻¹(ℙ¹ ∖ {0, 1, ∞})` is a nonempty open contained in `U` and `f|_W : W ⟶ ℙ¹ ∖ {0, 1, ∞}` is
  finite étale;
* `Belyi.Anabelian.HypCurve.exists_belyi_open_le`: the same for a hyperbolic curve.

The version over a number field `k'` ("by replacing `k'` by some finite extension", l.4636)
is `Belyi.Anabelian.exists_belyi_open_le_finSub` (`Belyi/Anabelian/BelyiInputNumberField.lean`).
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace Belyi.Anabelian

/-- On a curve `X` over a field, a nonempty open subscheme has finite complement: the complement
is a closed set avoiding the generic point, hence (`X` being noetherian of dimension one) a finite
union of closed points. -/
theorem finite_compl_of_isCurveOver {k : Type u} [Field k] [PerfectField k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsCurveOver k X] (U : X.Opens) (hU : (U : Set X).Nonempty) :
    (U : Set X)ᶜ.Finite := by
  haveI := IsCurveOver.isIntegral k X
  haveI : IsNoetherian X := isNoetherian_of_over X (Spec (CommRingCat.of k))
  have hgen : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  have hcl : ∀ s ∈ (U : Set X)ᶜ, IsClosed ({s} : Set X) := fun s hs ↦
    isClosed_singleton_of_ne_genericPoint (krullDimLE_one_stalk_of_isCurveOver k X)
      fun h ↦ hs (h ▸ hgen)
  obtain ⟨S, hSfin, hScl, hSirr, hSeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  rw [hSeq]
  refine hSfin.sUnion fun T hT ↦ ?_
  have hη := IsIrreducible.isGenericPoint_genericPoint (hSirr T hT) (hScl T hT)
  have hηT : (hSirr T hT).genericPoint ∈ (U : Set X)ᶜ :=
    hSeq ▸ Set.mem_sUnion_of_mem hη.mem hT
  rw [← hη.def, (hcl _ hηT).closure_eq]
  exact Set.finite_singleton _

variable (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]

/-- **[AbsTopII] Example 3.6 (i) over `ℚ̄`.** For a curve `X̄` over `k = ℚ̄` and a nonempty open
`U ⊆ X̄` (its complement is automatically finite, `finite_compl_of_isCurveOver`), there is a Belyi
map `f : X̄ ⟶ ℙ¹_k` over `k` such that `W = f⁻¹(ℙ¹ ∖ {0, 1, ∞})` is a nonempty open subscheme of
`U` and `f|_W : W ⟶ ℙ¹ ∖ {0, 1, ∞}` is finite étale. -/
theorem exists_belyi_open_le (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsCurveOver k X]
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    ∃ f : X ⟶ P1 k, IsBelyiMap k f ∧ f ≫ (P1 k ↘ Spec (.of k)) = X ↘ Spec (.of k) ∧
      f ⁻¹ᵁ puncturedLine k ≤ U ∧
      ((f ⁻¹ᵁ puncturedLine k : X.Opens) : Set X).Nonempty ∧
      IsFinite (f ∣_ puncturedLine k) ∧ Etale (f ∣_ puncturedLine k) := by
  haveI := IsCurveOver.isIntegral k X
  have hgen : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  have hcl : ∀ s ∈ (U : Set X)ᶜ, IsClosed ({s} : Set X) := fun s hs ↦
    isClosed_singleton_of_ne_genericPoint (krullDimLE_one_stalk_of_isCurveOver k X)
      fun h ↦ hs (h ▸ hgen)
  obtain ⟨f, hf, hmark, hover⟩ := exists_isBelyiMap_marked_isOver_of_isCurveOver k X _
    (finite_compl_of_isCurveOver (k := k) X U hU) hcl
  haveI := hf.isFinite
  refine ⟨f, hf, hover, fun x hx ↦ ?_,
    ⟨genericPoint X, genericPoint_mem_preimage_puncturedLine hf⟩,
    inferInstance, hf.etale_morphismRestrict_puncturedLine⟩
  by_contra hxU
  exact hx (hmark x hxU)

/-- **[AbsTopII] Example 3.6 (i) for hyperbolic curves over `ℚ̄`**: for `U ⊆ X̄` a hyperbolic curve
there is a Belyi map `f : X̄ ⟶ ℙ¹` over `k` with `W = f⁻¹(ℙ¹ ∖ {0, 1, ∞}) ⊆ U` nonempty and `f|_W`
finite étale onto `ℙ¹ ∖ {0, 1, ∞}`. -/
theorem HypCurve.exists_belyi_open_le (C : HypCurve k) :
    ∃ f : C.Xbar ⟶ P1 k, IsBelyiMap k f ∧
      f ≫ (P1 k ↘ Spec (.of k)) = C.Xbar ↘ Spec (.of k) ∧ f ⁻¹ᵁ puncturedLine k ≤ C.U ∧
      ((f ⁻¹ᵁ puncturedLine k : C.Xbar.Opens) : Set C.Xbar).Nonempty ∧
      IsFinite (f ∣_ puncturedLine k) ∧ Etale (f ∣_ puncturedLine k) :=
  Belyi.Anabelian.exists_belyi_open_le k C.Xbar C.U C.nonempty

end Belyi.Anabelian
