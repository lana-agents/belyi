/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Curve.SmoothStalk
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.Perfect

/-!
# Every curve admits a finite surjective morphism to `ℙ¹` (existence, B1)

The morphism `Belyi.homOfFunctionField` and its finiteness/surjectivity
(`Belyi.isFinite_and_surjective_homOfFunctionField_of_isCurveOver`) are stated for a
*chosen* transcendental element `t ∈ K(X)`.  This file supplies the last missing input
to the headline **B1** existence statement — that such a `t` exists — and assembles the
existence theorem.

## Strategy

The only content is: for a curve `X` over a perfect field `k`, the function field `K(X)`
is **not** algebraic over `k`.  We prove this at the generic point, entirely through
Kähler differentials, reusing the machinery of `Belyi/KaehlerRank.lean`:

* the generic-point stalk `𝒪_{X,η} = K(X)` is a localization of an affine chart ring
  `A = Γ(X, V)` that is standard smooth of relative dimension `1` over `k` (the chart
  extraction of `Belyi/Curve/SmoothStalk.lean`), so `Ω[K(X)⁄k]` is free of rank `1` over
  `K(X)` (`Belyi.finrank_kaehler_localization` + `Belyi.finrank_kaehler_of_standardSmooth`),
  in particular **nontrivial**;
* if `K(X)` were algebraic over the *perfect* field `k`, it would be separable, hence
  formally étale, forcing `Ω[K(X)⁄k]` to be **subsingleton**
  (`Algebra.FormallyEtale.of_isSeparable`,
  `Algebra.FormallyEtale.subsingleton_kaehlerDifferential`) — a contradiction.

Feeding the resulting transcendental element to
`Belyi.isFinite_and_surjective_homOfFunctionField_of_isCurveOver` gives the existence
statement `Belyi.exists_isFinite_surjective_hom_to_P1`.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory IsLocalRing Module TensorProduct

section

variable (k : Type u) [Field k] [PerfectField k] (X : Scheme.{u})
  [inst_over : X.Over (Spec (CommRingCat.of k))]
  [inst_smooth : SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  [IsIntegral X]

include inst_over inst_smooth

omit [PerfectField k] in
/-- **`Ω[K(X)⁄k]` is nontrivial** for a smooth curve over a field.  Computed at the
generic point, where the stalk is `K(X)` and is a localization of a standard smooth
chart of relative dimension `1`, so `Ω[K(X)⁄k]` is free of rank `1`. -/
theorem nontrivial_kaehler_functionField :
    Nontrivial (Ω[X.functionField ⁄ k]) := by
  obtain ⟨U, hU, V, hV, hxV, hVU, hss⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 1) (f := X ↘ Spec (CommRingCat.of k)) (genericPoint X)
  have hfx : (X ↘ Spec (CommRingCat.of k)).base (genericPoint X) ∈ U := hVU hxV
  have hUtop : U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true, SetLike.mem_coe]
    rw [Subsingleton.elim y ((X ↘ Spec (CommRingCat.of k)).base (genericPoint X))]
    exact hfx
  subst hUtop
  set φ := ((X ↘ Spec (CommRingCat.of k)).appLE ⊤ V hVU).hom with hφ
  let e : Γ(Spec (CommRingCat.of k), ⊤) ≃+* k :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  letI algA : Algebra k Γ(X, V) := (φ.comp (e.symm : k →+* _)).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 k Γ(X, V) := by
    have he0 := RingHom.IsStandardSmoothOfRelativeDimension.equiv e.symm
    have hc := hss.comp he0
    rw [Nat.add_zero] at hc
    exact hc
  haveI : Algebra.IsStandardSmooth k Γ(X, V) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  -- The generic-point stalk is `K(X)` and is the localization of `A` at the prime of `x`.
  letI algAB : Algebra Γ(X, V) X.functionField :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨genericPoint X, hxV⟩
  set M := (hV.primeIdealOf ⟨genericPoint X, hxV⟩).asIdeal.primeCompl with hM
  haveI hlocB : IsLocalization M X.functionField :=
    hV.isLocalization_stalk ⟨genericPoint X, hxV⟩
  haveI : Nontrivial Γ(X, V) := by
    refine ⟨1, 0, fun h => one_ne_zero (α := X.functionField) ?_⟩
    rw [← map_one (algebraMap Γ(X, V) X.functionField),
      ← map_zero (algebraMap Γ(X, V) X.functionField), h]
  -- The scalar tower `k → Γ(X, V) → K(X)`, matching the scoped `Algebra k K(X)`.
  haveI tower : IsScalarTower k Γ(X, V) X.functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    -- The generic-point stalk map factors the scoped structure map through the chart.
    have hmor :
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (X ↘ Spec (CommRingCat.of k)).appLE ⊤ V hVU ≫
            X.presheaf.germ V (genericPoint X) hxV =
          CommRingCat.ofHom (algebraMap k X.functionField) := by
      rw [ofHom_algebraMap_functionField, Scheme.Hom.appLE, Scheme.Hom.appTop,
        Category.assoc]
      congr 1
      congr 1
      exact X.presheaf.map_germ_eq_Γgerm (i := homOfLE hVU) (genericPoint X) hxV
    have hcomp :
        (algebraMap (Γ(X, V)) X.functionField).comp (algebraMap k Γ(X, V)) =
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
            (X ↘ Spec (CommRingCat.of k)).appLE ⊤ V hVU ≫
            X.presheaf.germ V (genericPoint X) hxV).hom := by
      rfl
    rw [hcomp, hmor]
    rfl
  -- `Ω[K(X)⁄k]` is free of rank `1`, hence nontrivial.
  have hfr : finrank X.functionField Ω[X.functionField ⁄ k] = 1 := by
    rw [finrank_kaehler_localization k Γ(X, V) M X.functionField,
      finrank_kaehler_of_standardSmooth k Γ(X, V) 1]
  exact Module.nontrivial_of_finrank_pos (by rw [hfr]; exact one_pos)

/-- **The function field of a smooth curve over a perfect field is not algebraic over the
base.**  Hence there is a transcendental element `t ∈ K(X)` — the input needed to build a
finite morphism `X ⟶ ℙ¹` via `Belyi.homOfFunctionField`.

If `K(X)` were algebraic over the perfect field `k`, it would be separable, hence formally
étale, forcing `Ω[K(X)⁄k]` to be subsingleton — contradicting
`Belyi.nontrivial_kaehler_functionField`. -/
theorem exists_transcendental_functionField :
    ∃ t : X.functionField, Transcendental k t := by
  rw [← Algebra.transcendental_def, Algebra.transcendental_iff_not_isAlgebraic]
  intro halg
  haveI : Algebra.IsAlgebraic k X.functionField := halg
  haveI : Algebra.IsSeparable k X.functionField := inferInstance
  haveI : Algebra.FormallyEtale k X.functionField :=
    Algebra.FormallyEtale.of_isSeparable k X.functionField
  haveI : Subsingleton (Ω[X.functionField ⁄ k]) :=
    Algebra.FormallyEtale.subsingleton_kaehlerDifferential
  haveI := nontrivial_kaehler_functionField k X
  exact absurd ‹Subsingleton (Ω[X.functionField ⁄ k])› (not_subsingleton _)

end

section Curve

variable (k : Type u) [Field k] [PerfectField k] (X : Scheme.{u})
  [inst_over : X.Over (Spec (CommRingCat.of k))] [inst_curve : IsCurveOver k X]

include inst_over inst_curve

/-- **B1, existence.**  Every curve over a perfect field admits a finite surjective
morphism to `ℙ¹`.  Combine `Belyi.exists_transcendental_functionField` (a transcendental
element of `K(X)` exists) with
`Belyi.isFinite_and_surjective_homOfFunctionField_of_isCurveOver`. -/
theorem exists_isFinite_surjective_hom_to_P1 :
    ∃ f : X ⟶ P1 k, IsFinite f ∧ Function.Surjective f.base := by
  haveI : IsIntegral X := IsCurveOver.isIntegral k X
  obtain ⟨t, ht⟩ := exists_transcendental_functionField k X
  exact ⟨homOfFunctionField k X (valuationRing_stalk_of_isCurveOver k X) t,
    isFinite_and_surjective_homOfFunctionField_of_isCurveOver k X ht⟩

end Curve

end Belyi
