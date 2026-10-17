/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.FundamentalGroup.HomotopyExactQcqs

/-!
# Spreading out morphisms to a finite subextension (MR8.4b, first step)

[AbsTopII] Example 3.6 (i) uses Belyi maps of curves over a number field `k'` "by replacing `k'`
by some finite extension of `k'`" (`Topics in Absolute Anabelian Geometry II.txt` l.4636). A
Belyi map is first produced over an algebraic closure `Ω` (`Belyi.Anabelian.exists_belyi_open_le`);
this file provides the descent of the *morphism* to a finite subextension `K ⊆ Ω`.

Let `X` be a quasi-compact quasi-separated `k`-scheme, `Ω / k` algebraic and `Z` a `k`-scheme
locally of finite presentation (e.g. `ℙ¹_k`). Every morphism `φ : X_Ω ⟶ Z` over `Spec k` factors
through `X_Ω ⟶ X_K` for a finite subextension `K` of `Ω / k`
(`Belyi.Anabelian.exists_baseChange_model`). The proof applies pi1's descent of sections along
`X_Ω = lim_K X_K` (`AlgebraicGeometry.FiniteEtale.exists_section_descent_of_qcqs`, built on
Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`, EGA IV 8.14.2) to the
graph `X_Ω ⟶ X ×_k Z` of `φ`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale IntermediateField

namespace Belyi.Anabelian

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [CompactSpace X] [QuasiSeparatedSpace X]

/-- **Spreading out a morphism to a finite subextension.** For `X` quasi-compact quasi-separated
over `k`, `Ω / k` algebraic and `Z ⟶ Spec k` locally of finite presentation, every morphism
`φ : X_Ω ⟶ Z` over `Spec k` is the composite `X_Ω ⟶ X_K ⟶ Z` of the projection with a morphism
`ψ : X_K ⟶ Z` over `Spec k`, for some finite subextension `K` of `Ω / k`. -/
theorem exists_baseChange_model {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k))
    [LocallyOfFinitePresentation g]
    (φ : Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) f ⟶ Z)
    (hφ : φ ≫ g = pullback.snd _ f ≫ f) :
    ∃ (K : (FinSub k Ω)ᵒᵖ) (ψ : (baseChangeDiagram (Ω := Ω) f).obj K ⟶ Z),
      (baseChangeCone (Ω := Ω) f).π.app K ≫ ψ = φ ∧
      ψ ≫ g = (baseChangeDiagramπ (Ω := Ω) f).app K ≫ f := by
  obtain ⟨K, ψ, hψq, hψσ⟩ := exists_section_descent_of_qcqs (Ω := Ω) f
    (pullback.fst f g) (pullback.lift (pullback.snd _ f) φ hφ.symm) (pullback.lift_fst _ _ _)
  refine ⟨K, ψ ≫ pullback.snd f g, ?_, ?_⟩
  · rw [← Category.assoc]
    exact (congrArg (· ≫ pullback.snd f g) hψσ).trans (pullback.lift_snd _ _ _)
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc, hψq]
    rfl

end Belyi.Anabelian
