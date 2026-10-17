/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Anabelian.BelyiInput
import Belyi.Anabelian.SpreadOut
import Belyi.QuasiFiniteDescent
import Belyi.Curve.BaseChange

/-!
# The Belyi input over a number field ([AbsTopII] Example 3.6 (i), MR8.4b)

[AbsTopII] Example 3.6 (i) (`Topics in Absolute Anabelian Geometry II.txt` l.4628–4636): "Suppose
that `U` [hence also `V`] is defined over a number field. Then it follows from the existence of
Belyi maps … that, for some nonempty open subscheme `W ⊆ U`, there exists a diagram
`W → U → V`, `β : W → P` [where the `→`'s are the natural open immersions; the "Belyi map" `β` is
finite étale]. Here, we think of `P`, `W` as being defined over a number field `k'` (by replacing
`k'` by some finite extension of `k'`)."

We prove this for a curve `X₀` over a field `F` algebraic over `ℚ` (e.g. a number field) and a
nonempty open `U₀ ⊆ X₀`: for an algebraic closure `Ω` of `F` there are a finite subextension
`K ⊆ Ω` and a finite morphism `f : X_K ⟶ ℙ¹_K` over `K` such that `W = f⁻¹(ℙ¹ ∖ {0, 1, ∞})` is a
nonempty open contained in `U_K` and `f|_W : W ⟶ ℙ¹_K ∖ {0, 1, ∞}` is finite étale
(`Belyi.Anabelian.exists_belyi_open_le_finSub`).

Proof. The Belyi map `f_Ω` of `X_Ω` (`Belyi.Anabelian.exists_belyi_open_le`) spreads out to some
finite `K` (`Belyi.Anabelian.exists_baseChange_model` applied to `X_Ω ⟶ ℙ¹_Ω ⟶ ℙ¹_F`), giving
`f_K` with a cartesian square `X_Ω = X_K ×_{ℙ¹_K} ℙ¹_Ω`. The base change `ℙ¹_Ω ⟶ ℙ¹_K` is
surjective, flat and quasi-compact, so finiteness (`Belyi.isFinite_of_isPullback_of_faithfullyFlat`)
and, over the punctured line, étaleness (fpqc descent of `Etale`, Mathlib
`AlgebraicGeometry.LocalFlatDescent`) descend from `f_Ω` to `f_K`; the inclusion `W_K ⊆ U_K` and
nonemptiness are checked on points via the surjection `X_Ω ⟶ X_K`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.FiniteEtale IntermediateField

namespace Belyi.Anabelian

/-! ### Descent of properties of a restriction along a cartesian square -/

section Descent

variable {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y} {m : X ⟶ Z} {g : Y ⟶ Z}

/-- Restricting a cartesian square `A = Y ×_Z X` (with `m : X ⟶ Z`) to an open `V ⊆ Z` gives a
cartesian square `(fst ⁻¹ᵁ m ⁻¹ᵁ V) = (g ⁻¹ᵁ V) ×_V (m ⁻¹ᵁ V)`. -/
lemma isPullback_morphismRestrict_of_isPullback (h : IsPullback fst snd m g) (V : Z.Opens) :
    ∃ a : (fst ⁻¹ᵁ m ⁻¹ᵁ V).toScheme ⟶ (g ⁻¹ᵁ V).toScheme,
      IsPullback (fst ∣_ m ⁻¹ᵁ V) a (m ∣_ V) (g ∣_ V) := by
  have hbot := isPullback_morphismRestrict g V
  have hc : ((fst ∣_ m ⁻¹ᵁ V) ≫ m ∣_ V) ≫ V.ι = ((fst ⁻¹ᵁ m ⁻¹ᵁ V).ι ≫ snd) ≫ g := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι,
      Category.assoc, Category.assoc, h.w]
  refine ⟨hbot.lift _ _ hc, IsPullback.of_bot ?_ (hbot.lift_fst _ _ hc).symm hbot⟩
  rw [hbot.lift_snd, morphismRestrict_ι]
  exact (isPullback_morphismRestrict fst (m ⁻¹ᵁ V)).paste_vert h

/-- **fpqc descent of a property of a restriction.** Given a cartesian square
`A = Y ×_Z X` with `m : X ⟶ Z` surjective, flat and quasi-compact, and an open `V ⊆ Z`, a property
`P` descending along `Surjective ⊓ Flat ⊓ QuasiCompact` (e.g. `Etale`) passes from `fst|_{m⁻¹V}`
to `g|_V`. -/
lemma of_morphismRestrict_of_isPullback (P : MorphismProperty Scheme.{u})
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] (h : IsPullback fst snd m g)
    [Surjective m] [Flat m] [QuasiCompact m] (V : Z.Opens) (hP : P (fst ∣_ m ⁻¹ᵁ V)) :
    P (g ∣_ V) := by
  obtain ⟨a, ha⟩ := isPullback_morphismRestrict_of_isPullback h V
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) (m ∣_ V) :=
    ⟨⟨IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› V, inferInstance⟩, inferInstance⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong ha hQ hP

end Descent

/-! ### Transitivity of the base change of `ℙ¹` -/

section P1Tower

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Algebra A C] [IsScalarTower A B C]

/-- The base-change morphisms of `ℙ¹` compose: `ℙ¹_C ⟶ ℙ¹_B ⟶ ℙ¹_A` is `ℙ¹_C ⟶ ℙ¹_A`. -/
lemma P1.mapOfAlgebra_comp_mapOfAlgebra :
    P1.mapOfAlgebra B C ≫ P1.mapOfAlgebra A B = P1.mapOfAlgebra A C := by
  change (Proj.map (P1.gradedMapOfAlgebra B C) (P1.irrelevant_le_map_gradedMapOfAlgebra B C) :
      Proj (P1Grading C) ⟶ Proj (P1Grading B)) ≫
    (Proj.map (P1.gradedMapOfAlgebra A B) (P1.irrelevant_le_map_gradedMapOfAlgebra A B) :
      Proj (P1Grading B) ⟶ Proj (P1Grading A)) =
    Proj.map (P1.gradedMapOfAlgebra A C) (P1.irrelevant_le_map_gradedMapOfAlgebra A C)
  rw [← Proj.map_comp]
  congr 1
  ext p
  simp [P1.gradedMapOfAlgebra_apply, MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]

/-- `Spec C ⟶ Spec B ⟶ Spec A` is `Spec C ⟶ Spec A`. -/
lemma specAlgebraMap_comp_specAlgebraMap :
    specAlgebraMap B C ≫ specAlgebraMap A B = specAlgebraMap A C := by
  rw [specAlgebraMap, specAlgebraMap, specAlgebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq]

end P1Tower

/-! ### The Belyi input over a finite extension -/

variable (F Ω : Type u) [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
  [IsAlgClosed Ω] [CharZero F] [Algebra.IsAlgebraic ℚ F]

/-- **[AbsTopII] Example 3.6 (i) over a finite extension of the field of definition.** Let `X₀`
be a curve over a field `F` algebraic over `ℚ` (e.g. a number field), `U₀ ⊆ X₀` a nonempty open
subscheme and `Ω` an algebraic closure of `F`. Then for some finite subextension `K` of `Ω / F`
there is a finite morphism `f : X_K ⟶ ℙ¹_K` over `K` (`X_K = Spec K ×_F X₀`) such that
`W = f⁻¹(ℙ¹_K ∖ {0, 1, ∞})` is a nonempty open subscheme of `U_K` and
`f|_W : W ⟶ ℙ¹_K ∖ {0, 1, ∞}` is finite étale. -/
theorem exists_belyi_open_le_finSub (X₀ : Scheme.{u}) [X₀.Over (Spec (.of F))]
    [IsCurveOver F X₀] (U₀ : X₀.Opens) (hU₀ : (U₀ : Set X₀).Nonempty) :
    ∃ (K : FinSub F Ω) (f : pullback (specAlgebraMap F K.1) (X₀ ↘ Spec (.of F)) ⟶ P1 K.1),
      f ≫ (P1 K.1 ↘ Spec (.of K.1)) = pullback.fst _ _ ∧ IsFinite f ∧
      f ⁻¹ᵁ puncturedLine K.1 ≤ pullback.snd (specAlgebraMap F K.1) (X₀ ↘ Spec (.of F)) ⁻¹ᵁ U₀ ∧
      (SetLike.coe (f ⁻¹ᵁ puncturedLine K.1)).Nonempty ∧
      IsFinite (f ∣_ puncturedLine K.1) ∧ Etale (f ∣_ puncturedLine K.1) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  set p₀ := X₀ ↘ Spec (.of F) with hp₀
  haveI : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace p₀
  haveI : QuasiSeparatedSpace X₀ := quasiSeparatedSpace_of_quasiSeparated p₀
  -- The curve `X_Ω = Spec Ω ×_F X₀` over `Spec Ω`.
  letI : (pullback (specAlgebraMap F Ω) p₀).Over (Spec (.of Ω)) := ⟨pullback.fst _ _⟩
  haveI : IsCurveOver Ω (pullback (specAlgebraMap F Ω) p₀) :=
    IsCurveOver.of_iso (pullbackSymmetry p₀ (specAlgebraMap F Ω))
      (pullbackSymmetry_hom_comp_fst _ _)
  have hUΩ : (SetLike.coe (pullback.snd (specAlgebraMap F Ω) p₀ ⁻¹ᵁ U₀)).Nonempty := by
    obtain ⟨x, hx⟩ := hU₀
    obtain ⟨y, rfl⟩ := (pullback.snd (specAlgebraMap F Ω) p₀).surjective x
    exact ⟨y, hx⟩
  -- The Belyi map over `Ω`.
  obtain ⟨fΩ, hBel, hover, hWU, hWne, -, hWet⟩ :=
    exists_belyi_open_le Ω (pullback (specAlgebraMap F Ω) p₀) _ hUΩ
  haveI := hBel.isFinite
  -- Spread out `X_Ω ⟶ ℙ¹_Ω ⟶ ℙ¹_F` to a finite subextension `K`.
  have hφ : (fΩ ≫ P1.mapOfAlgebra F Ω) ≫ (P1 F ↘ Spec (.of F)) =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap F Ω))) p₀ ≫ p₀ := by
    rw [Category.assoc, P1.mapOfAlgebra_comp_structMap, ← Category.assoc, hover]
    exact pullback.condition
  obtain ⟨K', ψ, hψ, hψover⟩ := exists_baseChange_model (Ω := Ω) p₀
    (P1 F ↘ Spec (.of F)) (fΩ ≫ P1.mapOfAlgebra F Ω) hφ
  set K := K'.unop with hK
  let πX : pullback (specAlgebraMap F Ω) p₀ ⟶ pullback (specAlgebraMap F K.1) p₀ :=
    (baseChangeCone (Ω := Ω) p₀).π.app K'
  have hπfst : πX ≫ pullback.fst _ _ = pullback.fst _ _ ≫ specAlgebraMap K.1 Ω :=
    pullback.lift_fst _ _ _
  have hπsnd : πX ≫ pullback.snd _ _ = pullback.snd _ _ := baseChangeCone_π_app_snd p₀ K'
  let ψ' : pullback (specAlgebraMap F K.1) p₀ ⟶ P1 F := ψ
  have hψ' : πX ≫ ψ' = fΩ ≫ P1.mapOfAlgebra F Ω := hψ
  have hcomm : ψ' ≫ (P1 F ↘ Spec (.of F)) = pullback.fst _ _ ≫ specAlgebraMap F K.1 :=
    hψover.trans pullback.condition.symm
  -- The descended map `f_K : X_K ⟶ ℙ¹_K`.
  let fK : pullback (specAlgebraMap F K.1) p₀ ⟶ P1 K.1 :=
    pullback.lift ψ' (pullback.fst _ _) hcomm ≫ inv (P1.toPullback F K.1)
  have hfKmap : fK ≫ P1.mapOfAlgebra F K.1 = ψ' := by
    rw [← P1.toPullback_fst, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  have hfKstr : fK ≫ (P1 K.1 ↘ Spec (.of K.1)) = pullback.fst _ _ := by
    rw [← P1.toPullback_snd F K.1, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_snd]
  -- The cartesian square `X_Ω = X_K ×_{ℙ¹_K} ℙ¹_Ω`.
  have hP1 := P1.isPullback_mapOfAlgebra K.1 Ω
  have houter : IsPullback (pullback.fst (specAlgebraMap F Ω) p₀) πX (specAlgebraMap K.1 Ω)
      (pullback.fst (specAlgebraMap F K.1) p₀) := by
    refine IsPullback.of_bot ?_ hπfst.symm (IsPullback.of_hasPullback (specAlgebraMap F K.1) p₀)
    rw [hπsnd, specAlgebraMap_comp_specAlgebraMap]
    exact IsPullback.of_hasPullback _ _
  have hw : fΩ ≫ P1.mapOfAlgebra K.1 Ω = πX ≫ fK := by
    rw [← cancel_mono (P1.toPullback F K.1)]
    apply pullback.hom_ext
    · simp only [Category.assoc, P1.toPullback_fst]
      rw [P1.mapOfAlgebra_comp_mapOfAlgebra, hfKmap, hψ']
    · simp only [Category.assoc, P1.toPullback_snd]
      rw [hfKstr, hπfst, hP1.w, ← Category.assoc, hover]
      rfl
  have hS0 : IsPullback fΩ πX (P1.mapOfAlgebra K.1 Ω) fK := by
    refine IsPullback.of_right ?_ hw hP1.flip
    rw [hover, hfKstr]
    exact houter
  haveI : Surjective (P1.mapOfAlgebra K.1 Ω) :=
    MorphismProperty.of_isPullback (P := @Surjective) hP1.flip inferInstance
  haveI : Flat (P1.mapOfAlgebra K.1 Ω) :=
    MorphismProperty.of_isPullback (P := @Flat) hP1.flip inferInstance
  haveI : QuasiCompact (P1.mapOfAlgebra K.1 Ω) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hP1.flip inferInstance
  haveI : Surjective πX := MorphismProperty.of_isPullback (P := @Surjective) houter
    inferInstance
  -- Finiteness descends.
  letI : (pullback (specAlgebraMap F K.1) p₀).Over (Spec (.of K.1)) := ⟨pullback.fst _ _⟩
  haveI : fK.IsOver (Spec (.of K.1)) := ⟨hfKstr⟩
  haveI : IsProper (pullback (specAlgebraMap F K.1) p₀ ↘ Spec (.of K.1)) :=
    MorphismProperty.pullback_fst (P := @IsProper) _ _ inferInstance
  haveI : IsProper fK := isProper_of_isOver fK (S := Spec (.of K.1))
  haveI : IsFinite fK := isFinite_of_isPullback_of_faithfullyFlat hS0
  -- The punctured lines correspond.
  have hpre : P1.mapOfAlgebra K.1 Ω ⁻¹ᵁ puncturedLine K.1 = puncturedLine Ω := by
    rw [← opensRange_puncturedι, ← opensRange_puncturedι]
    exact mapOfAlgebra_preimage_opensRange_puncturedι K.1 Ω
  have hpt : ∀ y, P1.mapOfAlgebra K.1 Ω (fΩ y) = fK (πX y) := fun y ↦ by
    rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
  refine ⟨K, fK, hfKstr, inferInstance, fun x hx ↦ ?_, ?_, inferInstance, ?_⟩
  · obtain ⟨y, rfl⟩ := πX.surjective x
    have hy : y ∈ fΩ ⁻¹ᵁ puncturedLine Ω := by
      rw [← hpre]
      simpa [Scheme.Hom.mem_preimage, hpt] using hx
    have := hWU hy
    simp only [Scheme.Hom.mem_preimage] at this ⊢
    rwa [← Scheme.Hom.comp_apply, hπsnd]
  · obtain ⟨y, hy⟩ := hWne
    refine ⟨πX y, ?_⟩
    have hy' : y ∈ fΩ ⁻¹ᵁ (P1.mapOfAlgebra K.1 Ω ⁻¹ᵁ puncturedLine K.1) := by
      rw [hpre]; exact hy
    simp only [Scheme.Hom.mem_preimage, SetLike.mem_coe] at hy' ⊢
    rwa [← hpt]
  · refine of_morphismRestrict_of_isPullback @Etale hS0 (puncturedLine K.1) ?_
    rw [hpre]
    exact hWet

end Belyi.Anabelian
