/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.DefinablePairBranch
import Belyi.P1.SmoothLocusChartGlue

/-!
# Concrete `ℙ¹` branch-locus matching for a pair model (B3d, converse input)

This file wires the ℙ¹ chart-glue core (taxis #220,
`Belyi.P1.ram_baseChange_p1_eq`/`smoothLocus_baseChange_p1_eq`) into the pair-definability
repackaging (taxis #221, `Belyi.branch_definableOverPair_eq`), discharging the ramification
hypothesis of the latter and thereby closing the **branch-locus-matching** part of statement
**B3d** (taxis issue #48) for a finite dominant curve cover of `ℙ¹`.

Two levels are provided:

* `Belyi.branch_baseChange_p1_eq` — the concrete `Branch` equality for the ℙ¹ base-change
  square `pullback.snd f₀ (mapOfAlgebra k₀ K)`, upgrading the merged forward inclusion
  `Belyi.branch_subset_preimage` to an equality (a one-liner from `branch_preimage_eq` fed the
  core `Ram` equality).
* `Belyi.ram_baseChangeModelHom_eq` — the ramification equality
  `Ram (baseChangeModelHom …) = pr⁻¹ (Ram f₀)` for the *model* base-change square
  (`pr = pullback.fst p₀ (specAlgebraMap …)`), obtained from the core ℙ¹ equality by
  transporting across the comparison isomorphism `Belyi.P1.toPullback`. This is exactly the
  hypothesis of `branch_definableOverPair_eq`.
* `Belyi.branch_eq_of_definableOverPair_data` — the packaged B3d branch matching: for a
  pair-definable `f : X ⟶ ℙ¹_K` whose model `f₀` is a finite surjective l.f.p. curve cover,
  `Branch f = mapOfAlgebra k₀ K ⁻¹' Branch f₀`, with the ramification hypothesis discharged
  internally.

## The `toPullback` transport

The core proves the `Ram` equality for the square `pullback f₀ (mapOfAlgebra k₀ K)` (base
change of `f₀` along `mapOfAlgebra`), while `branch_definableOverPair_eq` needs it for
`baseChangeModelHom` (base change of `f₀` along `pullback.fst (ℙ¹_{k₀} ↘ Spec k₀)
(specAlgebraMap …)`). Both are base changes of the *same* `f₀`; `Belyi.P1.toPullback`
identifies the two base bases (`mapOfAlgebra = toPullback ≫ pullback.fst …`,
`Belyi.P1.toPullback_fst`), so the two total spaces are canonically isomorphic over `X₀`
(`IsPullback.isoIsPullback`), and the `Ram` locus transports through the iso-cancellation
lemmas `Belyi.ram_isIso_comp` / `Belyi.ram_comp_isIso`.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

-- The base change of an l.f.p. model is l.f.p.; register it locally so that `Ram` and `Branch`
-- of `baseChangeModelHom` (which carry a `LocallyOfFinitePresentation` instance argument) can be
-- stated without threading the instance through every signature.
attribute [local instance] locallyOfFinitePresentation_baseChangeModelHom

variable {k₀ K : Type u} [Field k₀] [Field K] [CharZero k₀] [CharZero K] [Algebra k₀ K]
variable {X₀ : Scheme.{u}} [X₀.Over (Spec (CommRingCat.of k₀))] [IsCurveOver k₀ X₀]

/-- **Concrete branch-locus base change for the `ℙ¹` square (equality).** For a finite
surjective l.f.p. curve cover `f₀ : X₀ ⟶ ℙ¹_{k₀}` over a characteristic-zero field
`k₀ ⊆ K`, the branch locus of the base change `pullback.snd f₀ (mapOfAlgebra k₀ K)` is the
preimage of `Branch f₀` under `mapOfAlgebra k₀ K`. Upgrades the merged forward inclusion
`Belyi.branch_subset_preimage` to an equality; a one-liner from `Belyi.branch_preimage_eq`
fed the core `Belyi.P1.ram_baseChange_p1_eq`. -/
theorem branch_baseChange_p1_eq (f₀ : X₀ ⟶ P1 k₀) [IsFinite f₀]
    [LocallyOfFinitePresentation f₀] [Surjective f₀]
    [f₀.IsOver (Spec (CommRingCat.of k₀))] :
    Branch (pullback.snd f₀ (P1.mapOfAlgebra k₀ K))
      = ⇑(P1.mapOfAlgebra k₀ K) ⁻¹' Branch f₀ := by
  haveI : LocallyOfFinitePresentation (pullback.snd f₀ (P1.mapOfAlgebra k₀ K)) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  exact branch_preimage_eq (IsPullback.of_hasPullback f₀ (P1.mapOfAlgebra k₀ K))
    (P1.ram_baseChange_p1_eq f₀)

/-- **Ramification-locus base change for the model square.** For a finite surjective l.f.p.
curve cover `f₀ : X₀ ⟶ ℙ¹_{k₀}` over a characteristic-zero field `k₀ ⊆ K`, the ramification
locus of the model base change `baseChangeModelHom k₀ K p₀ f₀ hf₀` is the preimage of
`Ram f₀` under `pullback.fst p₀ (specAlgebraMap k₀ K)`.

This discharges the ramification hypothesis of `Belyi.branch_definableOverPair_eq`. It is
obtained from the ℙ¹ chart-glue core `Belyi.P1.ram_baseChange_p1_eq` (which lives on the
square `pullback f₀ (mapOfAlgebra k₀ K)`) by transporting across the canonical isomorphism
`Belyi.P1.toPullback` comparing the two base changes of `f₀`. -/
theorem ram_baseChangeModelHom_eq {p₀ : X₀ ⟶ Spec (CommRingCat.of k₀)} (f₀ : X₀ ⟶ P1 k₀)
    (hf₀ : f₀ ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)) = p₀) [IsFinite f₀]
    [LocallyOfFinitePresentation f₀] [Surjective f₀]
    [f₀.IsOver (Spec (CommRingCat.of k₀))] :
    Ram (baseChangeModelHom k₀ K p₀ f₀ hf₀)
      = ⇑(pullback.fst p₀ (specAlgebraMap k₀ K)) ⁻¹' Ram f₀ := by
  haveI hlofp_snd : LocallyOfFinitePresentation (pullback.snd f₀ (P1.mapOfAlgebra k₀ K)) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  haveI hlofp_sndc : LocallyOfFinitePresentation
      (pullback.snd f₀ (P1.mapOfAlgebra k₀ K) ≫ P1.toPullback k₀ K) :=
    MorphismProperty.comp_mem _ _ _ hlofp_snd inferInstance
  -- The model base-change square, over the cospan `(f₀, base_B)` with
  -- `base_B = pullback.fst (ℙ¹_{k₀} ↘ Spec k₀) (specAlgebraMap …)`.
  have hB := isPullback_baseChangeModelHom k₀ K p₀ f₀ hf₀
  -- The iso square identifying `ℙ¹_K` with the base base of the model square via `toPullback`.
  have hIsoSq : IsPullback (P1.mapOfAlgebra k₀ K) (P1.toPullback k₀ K)
      (𝟙 (P1 k₀))
      (pullback.fst (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)) :=
    IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, P1.toPullback_fst]⟩
  -- The core ℙ¹ square, transported by `toPullback` to the same cospan `(f₀, base_B)`.
  have hS220 : IsPullback (pullback.fst f₀ (P1.mapOfAlgebra k₀ K))
      (pullback.snd f₀ (P1.mapOfAlgebra k₀ K) ≫ P1.toPullback k₀ K) f₀
      (pullback.fst (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)) := by
    have h := (IsPullback.of_hasPullback f₀ (P1.mapOfAlgebra k₀ K)).paste_vert hIsoSq
    rwa [Category.comp_id] at h
  -- The comparison iso of the two total spaces over the shared cospan.
  set σ := hS220.isoIsPullback _ _ hB with hσ
  have hσ_fst : σ.hom ≫ pullback.fst p₀ (specAlgebraMap k₀ K)
      = pullback.fst f₀ (P1.mapOfAlgebra k₀ K) := hS220.isoIsPullback_hom_fst _ _ hB
  have hσ_snd : σ.hom ≫ baseChangeModelHom k₀ K p₀ f₀ hf₀
      = pullback.snd f₀ (P1.mapOfAlgebra k₀ K) ≫ P1.toPullback k₀ K :=
    hS220.isoIsPullback_hom_snd _ _ hB
  -- `baseChangeModelHom = σ⁻¹ ≫ (snd ≫ toPullback)`.
  have hbcm : baseChangeModelHom k₀ K p₀ f₀ hf₀
      = σ.inv ≫ (pullback.snd f₀ (P1.mapOfAlgebra k₀ K) ≫ P1.toPullback k₀ K) := by
    rw [← hσ_snd, Iso.inv_hom_id_assoc]
  -- Transport `Ram` across the two isos and apply the core equality. (Rewriting the morphism
  -- *under* `Ram` is blocked by its `LocallyOfFinitePresentation` instance argument, so bridge
  -- with `congr 1`; the instances match by proof irrelevance.)
  have step : Ram (baseChangeModelHom k₀ K p₀ f₀ hf₀)
      = ⇑σ.inv ⁻¹' Ram (pullback.snd f₀ (P1.mapOfAlgebra k₀ K) ≫ P1.toPullback k₀ K) := by
    rw [← ram_isIso_comp (pullback.snd f₀ (P1.mapOfAlgebra k₀ K) ≫ P1.toPullback k₀ K) σ.inv]
    congr 1
  rw [step, ram_comp_isIso (pullback.snd f₀ (P1.mapOfAlgebra k₀ K)) (P1.toPullback k₀ K),
    P1.ram_baseChange_p1_eq f₀]
  -- Goal: `σ⁻¹ ⁻¹' (fst f₀ q ⁻¹' Ram f₀) = fst p₀ sA ⁻¹' Ram f₀`.
  have hcancel : ⇑(pullback.fst f₀ (P1.mapOfAlgebra k₀ K))
      = ⇑(pullback.fst p₀ (specAlgebraMap k₀ K)) ∘ ⇑σ.hom := by
    rw [← hσ_fst, Scheme.Hom.comp_base, TopCat.coe_comp]
  rw [hcancel, Set.preimage_comp, ← Set.preimage_comp]
  have hcomp : (⇑σ.hom ∘ ⇑σ.inv) = id := by
    rw [← TopCat.coe_comp, ← Scheme.Hom.comp_base, σ.inv_hom_id, Scheme.Hom.id_base,
      TopCat.coe_id]
  rw [hcomp, Set.preimage_id]

/-- **Branch-locus matching of B3d for a finite pair model.** Given a pair-definable
`f : X ⟶ ℙ¹_K` — a model `f₀ : X₀ ⟶ ℙ¹_{k₀}` that is a finite surjective l.f.p. curve cover,
an identification `e` of `X` with the base change of the model source, and the pair condition
`f ≫ toPullback = e.hom ≫ baseChangeModelHom …` — the branch locus of `f` is the preimage of
`Branch f₀` under the canonical model map `mapOfAlgebra k₀ K`.

This is the packaged B3d branch-locus item of taxis issue #48, consumed by the converse
direction (#53): the ramification hypothesis of `Belyi.branch_definableOverPair_eq` is
discharged internally via `Belyi.ram_baseChangeModelHom_eq`. -/
theorem branch_eq_of_definableOverPair_data {p₀ : X₀ ⟶ Spec (CommRingCat.of k₀)}
    (f₀ : X₀ ⟶ P1 k₀) (hf₀ : f₀ ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)) = p₀) [IsFinite f₀]
    [LocallyOfFinitePresentation f₀] [Surjective f₀]
    [f₀.IsOver (Spec (CommRingCat.of k₀))]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {f : X ⟶ P1 K}
    [LocallyOfFinitePresentation f]
    (e : X ≅ pullback p₀ (specAlgebraMap k₀ K))
    (hfe : f ≫ P1.toPullback k₀ K = e.hom ≫ baseChangeModelHom k₀ K p₀ f₀ hf₀) :
    Branch f = ⇑(P1.mapOfAlgebra k₀ K) ⁻¹' Branch f₀ :=
  branch_definableOverPair_eq hf₀ e hfe (ram_baseChangeModelHom_eq (K := K) f₀ hf₀)

end Belyi
