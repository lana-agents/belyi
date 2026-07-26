/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.SmoothLocusBaseChangeAffineBase
import Belyi.RamificationBaseChange
import Belyi.P1.BaseChangeIso
import Belyi.P1.ChartCoord
import Belyi.P1.PolynomialMap
import Belyi.P1.BelyiMapBaseChange
import Belyi.Curve.Basic
import Belyi.Curve.BaseChange
import Mathlib.Algebra.CharZero.AddMonoidHom

/-!
# Smooth-locus base change for the non-affine `ℙ¹` square (descent, taxis #220)

This file upgrades the affine-base engine `Belyi.smoothLocus_baseChange_affineBase_eq`
(`Belyi/SmoothLocusBaseChangeAffineBase.lean`) to the concrete non-affine `ℙ¹` base-change
square, proving the *reverse* (descent) inclusion — hence the **equality** — of the smooth
locus under base change of a finite dominant curve cover `f₀ : X₀ ⟶ ℙ¹_{k₀}` along the field
extension `k₀ ⊆ K`.

The forward inclusion `pr ⁻¹ᵁ f₀.smoothLocus ⊆ f'.smoothLocus` is free
(`Belyi.smoothLocus_preimage_subset`). For the reverse inclusion the smooth locus is
transported chart-by-chart over the two standard charts of `ℙ¹_K`: on the chart `D₊(Xᵢ)`
the base-change square `Belyi.P1.isPullback_chartSquare` identifies the model morphism with
`Spec` of the coefficient extension `chartMap`, and pasting `f₀` onto this affine chart square
reduces the equality on that chart to the merged affine-base engine.

## Main results

* `Belyi.P1.smoothLocus_baseChange_p1_eq` — the opens equality of smooth loci.
* `Belyi.P1.ram_baseChange_p1_eq` — the complementary ramification-locus equality.
-/

open AlgebraicGeometry CategoryTheory Limits TensorProduct TopologicalSpace

universe u

namespace Belyi

/-- **Composing with an open immersion on the target does not change the smooth locus.**
For `h : X ⟶ Y` locally of finite presentation and an open immersion `ι : Y ⟶ Z`, the smooth
locus of `h ≫ ι` equals that of `h`, since `ι` has isomorphisms as stalk maps. -/
lemma smoothLocus_comp_isOpenImmersion {X Y Z : Scheme.{u}} (h : X ⟶ Y) (ι : Y ⟶ Z)
    [IsOpenImmersion ι] [LocallyOfFinitePresentation h] [LocallyOfFinitePresentation (h ≫ ι)] :
    (h ≫ ι).smoothLocus = h.smoothLocus := by
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_smoothLocus, Scheme.Hom.mem_smoothLocus,
    Scheme.Hom.stalkMap_comp]
  exact RingHom.FormallySmooth.respectsIso.cancel_left_isIso (ι.stalkMap (h.base x))
    (h.stalkMap x)

/-- Equal morphisms have equal smooth loci. -/
lemma smoothLocus_congr {Y Z : Scheme.{u}} {g h : Y ⟶ Z}
    [LocallyOfFinitePresentation g] [LocallyOfFinitePresentation h] (hgh : g = h) :
    g.smoothLocus = h.smoothLocus := by
  subst hgh; rfl

/-- **Any affine morphism to a `Spec` is `Spec` of the induced map on global sections.**
For `X` affine and `g : X ⟶ Spec A`, `g` factors as `X.isoSpec.hom` followed by `Spec.map` of the
composite `A ≅ Γ(Spec A) → Γ(X)`. -/
lemma eq_isoSpec_hom_comp {A : CommRingCat.{u}} {X : Scheme.{u}} [IsAffine X] (g : X ⟶ Spec A) :
    g = X.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso A).inv ≫ g.appTop) := by
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
    Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- **A surjective `Spec.map` over a domain base gives an injective ring map**, hence a faithful
scalar action. If `Spec.map (algebraMap A B)` is surjective and `A` is a domain, the structure map
`A → B` is injective. -/
lemma faithfulSMul_of_specMap_surjective {A B : Type u} [CommRing A] [CommRing B] [IsDomain A]
    [Algebra A B] (h : Surjective (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    FaithfulSMul A B := by
  rw [faithfulSMul_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot]
  have hdense : DenseRange (PrimeSpectrum.comap (algebraMap A B)) := h.surj.denseRange
  have hker := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap A B)).mp hdense
  rw [nilradical_eq_zero] at hker
  simpa using hker

end Belyi

namespace Belyi.P1

open MvPolynomial HomogeneousLocalization ProjectiveSpectrum

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Chart-ring instances (`IsDomain`, `CharZero`, `IsNoetherianRing`, flatness) -/

/-- The chart ring `(k[X₀,X₁]_{Xᵢ})₀` is an integral domain (it is `k[T]`). -/
lemma isDomain_away (k : Type u) [Field k] (i : Fin 2) :
    IsDomain (Away (P1Grading k) (X i : MvPolynomial (Fin 2) k)) := by
  fin_cases i
  · exact MulEquiv.isDomain (Polynomial k) (awayChartEquivZero k).toRingEquiv.toMulEquiv
  · exact MulEquiv.isDomain (Polynomial k) (awayChartEquivOne k).toRingEquiv.toMulEquiv

/-- The chart ring `(k[X₀,X₁]_{Xᵢ})₀` has characteristic zero (it is `k[T]`). -/
lemma charZero_away (k : Type u) [Field k] [CharZero k] (i : Fin 2) :
    CharZero (Away (P1Grading k) (X i : MvPolynomial (Fin 2) k)) := by
  fin_cases i
  · exact CharZero.of_addMonoidHom
      ((awayChartEquivZero k).symm.toRingEquiv.toRingHom.toAddMonoidHom)
      (map_one ((awayChartEquivZero k).symm.toRingEquiv.toRingHom))
      (awayChartEquivZero k).symm.injective
  · exact CharZero.of_addMonoidHom
      ((awayChartEquivOne k).symm.toRingEquiv.toRingHom.toAddMonoidHom)
      (map_one ((awayChartEquivOne k).symm.toRingEquiv.toRingHom))
      (awayChartEquivOne k).symm.injective

/-- The chart ring `(k[X₀,X₁]_{Xᵢ})₀` is Noetherian (it is `k[T]`). -/
lemma isNoetherianRing_away (k : Type u) [Field k] (i : Fin 2) :
    IsNoetherianRing (Away (P1Grading k) (X i : MvPolynomial (Fin 2) k)) := by
  match i with
  | 0 => exact isNoetherianRing_awayZero
  | 1 => infer_instance

/-- `Spec` of the coefficient-extension chart map is flat: it is a base change of the flat
structural leg `specAlgebraMap k₀ K` (through `mapOfAlgebra`). -/
lemma flat_specMap_chartMap (k₀ K : Type u) [Field k₀] [Field K] [Algebra k₀ K] (i : Fin 2) :
    Flat (Spec.map (CommRingCat.ofHom (chartMap k₀ K i))) := by
  have hsa : Flat (specAlgebraMap k₀ K) :=
    (Flat.SpecMap_iff (f := CommRingCat.ofHom (algebraMap k₀ K))).mpr
      (by rw [CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff]; infer_instance)
  have hmap : Flat (mapOfAlgebra k₀ K) :=
    MorphismProperty.of_isPullback (isPullback_mapOfAlgebra k₀ K).flip hsa
  exact MorphismProperty.of_isPullback (isPullback_chartSquare k₀ K i).flip hmap

/-! ### The per-chart smooth-locus equality -/

set_option maxHeartbeats 1200000 in
-- Raised budgets: this chart-by-chart transport bundles the affine-base engine, a large family of
-- domain/flatness/finiteness instances, and several pullback pastings.
set_option synthInstance.maxHeartbeats 800000 in
/-- **Per-chart smooth-locus equality.** Restricted to the chart `D₊(Xᵢ)` of `ℙ¹_K`, the smooth
locus of the base change `f' = pullback.snd f₀ (mapOfAlgebra k₀ K)` agrees with the
`pullback.fst`-preimage of the smooth locus of `f₀`. Obtained by pasting `f₀` onto the chart
base-change square and applying the affine-base engine. -/
private lemma per_chart_smoothLocus
    {k₀ K : Type u} [Field k₀] [Field K] [CharZero k₀] [CharZero K] [Algebra k₀ K]
    {X₀ : Scheme.{u}} [X₀.Over (Spec (CommRingCat.of k₀))] [IsCurveOver k₀ X₀]
    (f₀ : X₀ ⟶ P1 k₀) [IsFinite f₀] [LocallyOfFinitePresentation f₀] [Surjective f₀]
    [f₀.IsOver (Spec (CommRingCat.of k₀))] (i : Fin 2) :
    (pullback.fst (pullback.snd f₀ (mapOfAlgebra k₀ K))
          (Proj.awayι (P1Grading K) (X i) (X_mem_P1Grading K i) one_pos))
        ⁻¹ᵁ (pullback.snd f₀ (mapOfAlgebra k₀ K)).smoothLocus =
      (pullback.fst (pullback.snd f₀ (mapOfAlgebra k₀ K))
          (Proj.awayι (P1Grading K) (X i) (X_mem_P1Grading K i) one_pos))
        ⁻¹ᵁ (pullback.fst f₀ (mapOfAlgebra k₀ K) ⁻¹ᵁ f₀.smoothLocus) := by
  classical
  -- The chart rings and the two chart inclusions.
  set A : Type u := Away (P1Grading k₀) (X i : MvPolynomial (Fin 2) k₀) with hA
  set A' : Type u := Away (P1Grading K) (X i : MvPolynomial (Fin 2) K) with hA'
  set q := mapOfAlgebra k₀ K with hq
  set ι := Proj.awayι (P1Grading k₀) (X i) (X_mem_P1Grading k₀ i) one_pos with hι
  set ι' := Proj.awayι (P1Grading K) (X i) (X_mem_P1Grading K i) one_pos with hι'
  set m := Spec.map (CommRingCat.ofHom (chartMap k₀ K i)) with hm
  -- Basic morphism-property instances.
  haveI : IsOpenImmersion ι := inferInstance
  haveI : IsOpenImmersion ι' := inferInstance
  haveI : LocallyOfFinitePresentation ι := inferInstance
  haveI : LocallyOfFinitePresentation ι' := inferInstance
  haveI : LocallyOfFinitePresentation (pullback.snd f₀ q) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  haveI : LocallyOfFinitePresentation (pullback.snd f₀ ι) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  haveI : IsFinite (pullback.snd f₀ ι) :=
    MorphismProperty.pullback_snd (P := @IsFinite) _ _ inferInstance
  haveI : IsAffine (pullback f₀ ι) := inferInstance
  haveI : IsOpenImmersion (pullback.fst f₀ ι) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (IsPullback.of_hasPullback f₀ ι).flip
      ‹IsOpenImmersion ι›
  haveI : IsOpenImmersion (pullback.fst (pullback.snd f₀ q) ι') :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (IsPullback.of_hasPullback (pullback.snd f₀ q) ι').flip ‹IsOpenImmersion ι'›
  haveI : LocallyOfFinitePresentation (pullback.snd (pullback.snd f₀ q) ι') :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  -- Composite `LocallyOfFinitePresentation` instances (established in the clean context).
  haveI hlofp1 : LocallyOfFinitePresentation (pullback.fst f₀ ι ≫ f₀) := inferInstance
  haveI hlofp2 : LocallyOfFinitePresentation (pullback.snd f₀ ι ≫ ι) := inferInstance
  haveI hlofp3 :
      LocallyOfFinitePresentation (pullback.fst (pullback.snd f₀ q) ι' ≫ pullback.snd f₀ q) :=
    inferInstance
  haveI hlofp4 : LocallyOfFinitePresentation (pullback.snd (pullback.snd f₀ q) ι' ≫ ι') :=
    inferInstance
  haveI hlofp5 : LocallyOfFinitePresentation (pullback.snd (pullback.snd f₀ ι) m) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  -- Chart-ring algebra instances.
  letI algAA' : Algebra A A' := (chartMap k₀ K i).toAlgebra
  haveI : IsDomain A := isDomain_away k₀ i
  haveI : IsDomain A' := isDomain_away K i
  haveI : CharZero A := charZero_away k₀ i
  haveI : CharZero A' := charZero_away K i
  haveI : IsNoetherianRing A := isNoetherianRing_away k₀ i
  have hAA' : (algebraMap A A' : A →+* A') = chartMap k₀ K i := RingHom.algebraMap_toAlgebra _
  haveI : Module.Flat A A' := by
    have hcf : (chartMap k₀ K i).Flat := by
      have h := (Flat.SpecMap_iff (f := CommRingCat.ofHom (chartMap k₀ K i))).mp
        (flat_specMap_chartMap k₀ K i)
      rwa [CommRingCat.hom_ofHom] at h
    rw [← RingHom.flat_algebraMap_iff, hAA']
    exact hcf
  -- Present `pullback.snd f₀ ι` over the chart ring `A` as `Spec` of the sections map.
  set B : Type u := ↑Γ(pullback f₀ ι, ⊤) with hB
  set φ : A →+* B :=
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (pullback.snd f₀ ι).appTop).hom with hφ
  letI algAB : Algebra A B := φ.toAlgebra
  have hφeq : (algebraMap A B : A →+* B) = φ := RingHom.algebraMap_toAlgebra _
  have he : pullback.snd f₀ ι =
      (pullback f₀ ι).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
    have hofhom : CommRingCat.ofHom (algebraMap A B) =
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (pullback.snd f₀ ι).appTop := by
      rw [hφeq, hφ, CommRingCat.ofHom_hom]
    rw [hofhom]
    exact eq_isoSpec_hom_comp (pullback.snd f₀ ι)
  -- Domain / finiteness / faithfulness of the sections `B`.
  have hgsurj : Surjective (pullback.snd f₀ ι) :=
    MorphismProperty.pullback_snd (P := @Surjective) _ _ inferInstance
  haveI : Nonempty ↥(pullback f₀ ι) := by
    haveI : Nonempty ↥(Spec (CommRingCat.of A)) := inferInstance
    exact ⟨(hgsurj.surj (Classical.arbitrary _)).choose⟩
  haveI : IsIntegral X₀ := IsCurveOver.isIntegral k₀ X₀
  haveI : IsIntegral (pullback f₀ ι) := isIntegral_of_isOpenImmersion (pullback.fst f₀ ι)
  haveI : IsDomain B := by
    haveI : IsIntegral (Spec (CommRingCat.of B)) :=
      IsIntegral.of_isIso (pullback f₀ ι).isoSpec.hom
    exact (affine_isIntegral_iff (CommRingCat.of B)).mp ‹_›
  have hφsurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
    rw [he] at hgsurj
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Surjective)
      (pullback f₀ ι).isoSpec.hom _).mp hgsurj
  haveI : FaithfulSMul A B := faithfulSMul_of_specMap_surjective hφsurj
  haveI : Module.Finite A B := by
    have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
      have hgf := ‹IsFinite (pullback.snd f₀ ι)›
      rw [he] at hgf
      exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)
        (pullback f₀ ι).isoSpec.hom _).mp hgf
    exact (IsFinite.SpecMap_iff (CommRingCat.ofHom (algebraMap A B))).mp hfin
  -- The comparison iso `Θ : pullback (snd f₀ ι) m ≅ pullback (snd f₀ q) ι'`, built as the
  -- unique iso between two pastings of the chart square that share the cospan `(f₀, ι' ≫ q)`.
  have hcomm : m ≫ ι = ι' ≫ q := (isPullback_chartSquare k₀ K i).w
  have S1 : IsPullback (pullback.fst (pullback.snd f₀ ι) m ≫ pullback.fst f₀ ι)
      (pullback.snd (pullback.snd f₀ ι) m) f₀ (ι' ≫ q) :=
    hcomm ▸ (IsPullback.of_hasPullback (pullback.snd f₀ ι) m).paste_horiz
      (IsPullback.of_hasPullback f₀ ι)
  have S2 : IsPullback (pullback.fst (pullback.snd f₀ q) ι' ≫ pullback.fst f₀ q)
      (pullback.snd (pullback.snd f₀ q) ι') f₀ (ι' ≫ q) :=
    (IsPullback.of_hasPullback (pullback.snd f₀ q) ι').paste_horiz
      (IsPullback.of_hasPullback f₀ q)
  set Θ : pullback (pullback.snd f₀ ι) m ≅ pullback (pullback.snd f₀ q) ι' :=
    S1.isoIsPullback _ _ S2 with hΘ
  have hΘsnd : Θ.hom ≫ pullback.snd (pullback.snd f₀ q) ι' =
      pullback.snd (pullback.snd f₀ ι) m := by
    rw [hΘ]; exact S1.isoIsPullback_hom_snd _ _ S2
  have hΘfst : Θ.hom ≫ (pullback.fst (pullback.snd f₀ q) ι' ≫ pullback.fst f₀ q) =
      pullback.fst (pullback.snd f₀ ι) m ≫ pullback.fst f₀ ι := by
    rw [hΘ]; exact S1.isoIsPullback_hom_fst _ _ S2
  haveI hΘlofp : LocallyOfFinitePresentation (Θ.hom ≫ pullback.snd (pullback.snd f₀ q) ι') :=
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  -- Integrality of the total base change `X' = pullback f₀ q`.
  haveI hX'int : IsIntegral (pullback f₀ q) := by
    have hover : f₀ ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)) = X₀ ↘ Spec (CommRingCat.of k₀) :=
      (Scheme.Hom.isOver_iff (S := Spec (CommRingCat.of k₀))).mp inferInstance
    have hbig := (IsPullback.of_hasPullback f₀ q).paste_vert (isPullback_mapOfAlgebra k₀ K)
    rw [hover] at hbig
    haveI : IsIntegral (pullback (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)) :=
      IsCurveOver.isIntegral K _
    exact IsIntegral.of_isIso hbig.isoPullback.inv
  -- Integrality of the chart of the base change, hence of `pullback (snd f₀ ι) m` and `A' ⊗[A] B`.
  haveI : Nonempty ↥(pullback (pullback.snd f₀ q) ι') := by
    have hfs' : Surjective (pullback.snd f₀ q) :=
      MorphismProperty.pullback_snd (P := @Surjective) _ _ inferInstance
    have hsurj : Function.Surjective (pullback.snd (pullback.snd f₀ q) ι').base :=
      (MorphismProperty.pullback_snd (P := @Surjective) _ _ hfs').surj
    haveI : Nonempty ↥(Spec (CommRingCat.of A')) := inferInstance
    exact ⟨(hsurj (Classical.arbitrary _)).choose⟩
  haveI : IsIntegral (pullback (pullback.snd f₀ q) ι') :=
    isIntegral_of_isOpenImmersion (pullback.fst (pullback.snd f₀ q) ι')
  haveI : IsIntegral (pullback (pullback.snd f₀ ι) m) := IsIntegral.of_isIso Θ.inv
  -- `Φ : pullback (snd f₀ ι) m ≅ Spec (A' ⊗[A] B)`, mirroring the affine-base engine.
  set μ : pullback (pullback.snd f₀ ι) m ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) m :=
    pullback.map (pullback.snd f₀ ι) m (Spec.map (CommRingCat.ofHom (algebraMap A B))) m
      (pullback f₀ ι).isoSpec.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact he) (by simp)
      with hμ
  haveI : IsIso μ := by rw [hμ]; exact inferInstance
  have hmA' : (CommRingCat.ofHom (algebraMap A A')) = CommRingCat.ofHom (chartMap k₀ K i) := by
    rw [hAA']
  set Φ : pullback (pullback.snd f₀ ι) m ≅ Spec (CommRingCat.of (A' ⊗[A] B)) :=
    asIso μ ≪≫ pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap A B))) m ≪≫
      (by rw [hm, ← hmA']; exact pullbackSpecIso A A' B) with hΦ
  haveI : IsDomain (A' ⊗[A] B) := by
    haveI : IsIntegral (Spec (CommRingCat.of (A' ⊗[A] B))) := IsIntegral.of_isIso Φ.hom
    exact (affine_isIntegral_iff (CommRingCat.of (A' ⊗[A] B))).mp ‹_›
  haveI : FaithfulSMul A' (A' ⊗[A] B) := by
    haveI hfstsurj : Surjective (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A A')))
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))) := by
      rw [hmA']
      exact MorphismProperty.pullback_fst (P := @Surjective) _ _ hφsurj
    have hrw : Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] B))) =
        (pullbackSpecIso A A' B).inv ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A A')))
          (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
      rw [← pullbackSpecIso_hom_fst' A A' B, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    have hsurj' : Surjective (Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] B)))) := by
      rw [hrw]; infer_instance
    exact faithfulSMul_of_specMap_surjective hsurj'
  -- Apply the affine-base engine on the chart.
  have heng := smoothLocus_baseChange_affineBase_eq (A := A) (A' := A') (B := B)
    (f := pullback.snd f₀ ι) (pullback f₀ ι).isoSpec he
  -- `(snd f₀ ι).smoothLocus = (fst f₀ ι) ⁻¹ᵁ f₀.smoothLocus` (open-immersion restriction).
  have hgsl : (pullback.snd f₀ ι).smoothLocus = (pullback.fst f₀ ι) ⁻¹ᵁ f₀.smoothLocus := by
    rw [Scheme.Hom.preimage_smoothLocus_eq (pullback.fst f₀ ι) f₀]
    exact (@smoothLocus_comp_isOpenImmersion _ _ _ (pullback.snd f₀ ι) ι _ _ hlofp2).symm.trans
      (@smoothLocus_congr _ _ _ _ hlofp2 hlofp1 (pullback.condition (f := f₀) (g := ι)).symm)
  -- Transport the engine equality to the chart of the base change.
  have hcancel : ∀ U : (pullback (pullback.snd f₀ q) ι').Opens, Θ.inv ⁻¹ᵁ (Θ.hom ⁻¹ᵁ U) = U :=
    fun U => by rw [← Scheme.Hom.comp_preimage, Θ.inv_hom_id, Scheme.Hom.id_preimage]
  have hstep : (pullback.fst (pullback.snd f₀ q) ι') ⁻¹ᵁ (pullback.snd f₀ q).smoothLocus =
      (pullback.snd (pullback.snd f₀ q) ι').smoothLocus :=
    (Scheme.Hom.preimage_smoothLocus_eq (pullback.fst (pullback.snd f₀ q) ι')
        (pullback.snd f₀ q)).trans
      ((@smoothLocus_congr _ _ _ _ hlofp3 hlofp4
          (pullback.condition (f := pullback.snd f₀ q) (g := ι'))).trans
        (@smoothLocus_comp_isOpenImmersion _ _ _ (pullback.snd (pullback.snd f₀ q) ι') ι' _ _
          hlofp4))
  have hLHS : Θ.hom ⁻¹ᵁ ((pullback.fst (pullback.snd f₀ q) ι') ⁻¹ᵁ
        (pullback.snd f₀ q).smoothLocus) =
      (pullback.snd (pullback.snd f₀ ι) m).smoothLocus := by
    rw [hstep]
    exact (Scheme.Hom.preimage_smoothLocus_eq Θ.hom (pullback.snd (pullback.snd f₀ q) ι')).trans
      (@smoothLocus_congr _ _ _ _ hΘlofp hlofp5 hΘsnd)
  have hRHS : Θ.hom ⁻¹ᵁ ((pullback.fst (pullback.snd f₀ q) ι') ⁻¹ᵁ
        ((pullback.fst f₀ q) ⁻¹ᵁ f₀.smoothLocus)) =
      (pullback.snd (pullback.snd f₀ ι) m).smoothLocus := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, Category.assoc, hΘfst,
      Scheme.Hom.comp_preimage, ← hgsl]
    exact heng.symm
  rw [← hcancel ((pullback.fst (pullback.snd f₀ q) ι') ⁻¹ᵁ (pullback.snd f₀ q).smoothLocus),
    hLHS, ← hRHS, hcancel]

/-! ### Global gluing -/

set_option maxHeartbeats 800000 in
-- Raised budget: the pointwise reverse inclusion invokes the heavy `per_chart_smoothLocus` and
-- unfolds several pullback-cover memberships.
/-- **Smooth-locus base change for the `ℙ¹` square (equality).** For a finite dominant curve cover
`f₀ : X₀ ⟶ ℙ¹_{k₀}` over a field `k₀ ⊆ K` of characteristic zero, the smooth locus of the base
change `pullback.snd f₀ (mapOfAlgebra k₀ K)` equals the `pullback.fst`-preimage of the smooth locus
of `f₀`. The reverse inclusion is proved chart-by-chart via `per_chart_smoothLocus`; the forward
inclusion is `Belyi.smoothLocus_preimage_subset`. -/
theorem smoothLocus_baseChange_p1_eq
    {k₀ K : Type u} [Field k₀] [Field K] [CharZero k₀] [CharZero K] [Algebra k₀ K]
    {X₀ : Scheme.{u}} [X₀.Over (Spec (CommRingCat.of k₀))] [IsCurveOver k₀ X₀]
    (f₀ : X₀ ⟶ P1 k₀) [IsFinite f₀] [LocallyOfFinitePresentation f₀] [Surjective f₀]
    [f₀.IsOver (Spec (CommRingCat.of k₀))] :
    (pullback.snd f₀ (mapOfAlgebra k₀ K)).smoothLocus =
      pullback.fst f₀ (mapOfAlgebra k₀ K) ⁻¹ᵁ f₀.smoothLocus := by
  haveI : LocallyOfFinitePresentation (pullback.snd f₀ (mapOfAlgebra k₀ K)) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  refine le_antisymm (fun z hz => ?_) ?_
  · -- Reverse inclusion: pointwise via the chart cover.
    obtain ⟨i, hi⟩ : ∃ i : Fin 2, (pullback.snd f₀ (mapOfAlgebra k₀ K)).base z ∈
        Set.range (Proj.awayι (P1Grading K) (X i) (X_mem_P1Grading K i) one_pos) := by
      refine ⟨(coordCover K).openCover.idx ((pullback.snd f₀ (mapOfAlgebra k₀ K)).base z), ?_⟩
      have := (coordCover K).openCover.covers ((pullback.snd f₀ (mapOfAlgebra k₀ K)).base z)
      rwa [coordCover_f] at this
    have hzr : z ∈ Set.range (pullback.fst (pullback.snd f₀ (mapOfAlgebra k₀ K))
        (Proj.awayι (P1Grading K) (X i) (X_mem_P1Grading K i) one_pos)) := by
      rw [Scheme.Pullback.range_fst]; exact hi
    obtain ⟨w, rfl⟩ := hzr
    have hmem : w ∈ (pullback.fst (pullback.snd f₀ (mapOfAlgebra k₀ K))
        (Proj.awayι (P1Grading K) (X i) (X_mem_P1Grading K i) one_pos))
          ⁻¹ᵁ (pullback.snd f₀ (mapOfAlgebra k₀ K)).smoothLocus := hz
    rw [per_chart_smoothLocus f₀ i] at hmem
    exact hmem
  · -- Forward inclusion (free).
    intro z hz
    exact smoothLocus_preimage_subset (IsPullback.of_hasPullback f₀ (mapOfAlgebra k₀ K)) hz

/-- **Ramification-locus base change for the `ℙ¹` square.** The complement of
`smoothLocus_baseChange_p1_eq`. -/
theorem ram_baseChange_p1_eq
    {k₀ K : Type u} [Field k₀] [Field K] [CharZero k₀] [CharZero K] [Algebra k₀ K]
    {X₀ : Scheme.{u}} [X₀.Over (Spec (CommRingCat.of k₀))] [IsCurveOver k₀ X₀]
    (f₀ : X₀ ⟶ P1 k₀) [IsFinite f₀] [LocallyOfFinitePresentation f₀] [Surjective f₀]
    [f₀.IsOver (Spec (CommRingCat.of k₀))] :
    Ram (pullback.snd f₀ (mapOfAlgebra k₀ K)) =
      pullback.fst f₀ (mapOfAlgebra k₀ K) ⁻¹' Ram f₀ := by
  haveI : LocallyOfFinitePresentation (pullback.snd f₀ (mapOfAlgebra k₀ K)) :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ inferInstance
  rw [Ram, Ram, Set.preimage_compl, ← Scheme.Hom.coe_preimage, ← smoothLocus_baseChange_p1_eq f₀]

end Belyi.P1
