/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Converse.BranchedPi1
import Belyi.Converse.PuncturedLineBelyi

/-!
# The affine part of a Belyi map

Let `f : X → ℙ¹_k` be a Belyi map on a curve `X` over an algebraically closed field `k` of
characteristic zero. Its affine part `X ∖ f⁻¹(∞) = X ×_{ℙ¹} 𝔸¹` (`Belyi.lineCover f`, the pullback
along the chart `Belyi.lineι k : 𝔸¹_k = Spec k[X] ≅ D₊(X₁) ⊆ ℙ¹_k`) is affine, with ring of
functions `B = Γ(X ×_{ℙ¹} 𝔸¹, ⊤)` (`Belyi.lineCoverRing f`), and the coordinate `t ∈ B` of `𝔸¹`
satisfies the hypotheses of `Belyi.Converse.BranchedData`:

* `k[t] → B` is finite (`f` is finite);
* `k[t] → B[(t(t-1))⁻¹]` is étale: `Spec B[(t(t-1))⁻¹] = Spec (B ⊗_{k[t]} k[t][(t(t-1))⁻¹])` is
  the part of `X` over the thrice-punctured line, over which `f` is étale
  (`Belyi.etale_puncturedCover_snd`), by pasting of pullbacks;
* `B` is a domain, finitely generated over `k`, and `Spec B → Spec k` is smooth of relative
  dimension one (an open subscheme of the curve `X`).

Hence (`Belyi.IsBelyiMap.exists_etaleFundamentalGroup_equiv_completion_freeGroup`)
`π₁ᵉᵗ(Spec B)` is the profinite completion of a free group of rank `d + 1 - c₀ - c₁`.
-/

open CategoryTheory Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open scoped TensorProduct

universe u

namespace Belyi

open scoped P1

attribute [local instance] MvPolynomial.gradedAlgebra

section Chart

variable (k : Type u) [CommRing k]

/-- **The affine line as the chart `D₊(X₁)` of `ℙ¹`**: `Spec k[X] ≅ D₊(X₁) ⊆ ℙ¹_k`, with
coordinate `X₀/X₁`. -/
noncomputable def lineι : Spec (CommRingCat.of (Polynomial k)) ⟶ P1 k :=
  Spec.map (CommRingCat.ofHom (P1.awayChartEquivOne k).toRingEquiv.toRingHom) ≫
    Proj.awayι (P1Grading k) (X 1) (P1.X_mem_P1Grading k 1) one_pos

instance : IsOpenImmersion (lineι k) := by
  haveI : IsIso (CommRingCat.ofHom (P1.awayChartEquivOne k).toRingEquiv.toRingHom) :=
    (P1.awayChartEquivOne k).toRingEquiv.toCommRingCatIso.isIso_hom
  haveI : IsIso (Spec.map (CommRingCat.ofHom (P1.awayChartEquivOne k).toRingEquiv.toRingHom)) :=
    inferInstance
  haveI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (P1.awayChartEquivOne k).toRingEquiv.toRingHom)) :=
    IsOpenImmersion.of_isIso _
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (P1.awayChartEquivOne k).toRingEquiv.toRingHom) ≫
      Proj.awayι (P1Grading k) (X 1) (P1.X_mem_P1Grading k 1) one_pos)
  infer_instance

/-- The thrice-punctured line inside the affine line. -/
lemma puncturedι_eq_comp_lineι :
    puncturedι k = Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (puncturedRing k))) ≫
      lineι k := by
  rw [lineι, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The chart followed by the structure morphism of `ℙ¹` is `Spec` of `k → k[X]`. -/
lemma lineι_structMap :
    lineι k ≫ (P1 k ↘ Spec (CommRingCat.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) := by
  change Spec.map (CommRingCat.ofHom (P1.awayChartEquivOne k).toRingEquiv.toRingHom) ≫
      (Proj.awayι (P1Grading k) (X 1) (P1.X_mem_P1Grading k 1) one_pos ≫ P1.structMap k) = _
  rw [P1.awayι_comp_structMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext1
  refine RingHom.ext fun c ↦ ?_
  change P1.awayChartEquivOne k (P1.chartAlgHom k 1 c) = _
  rw [show P1.chartAlgHom k 1 c = algebraMap k _ c from rfl, AlgEquiv.commutes]
  rfl

end Chart

section Cover

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ P1 k)

/-- The affine part `X ×_{ℙ¹} 𝔸¹ = X ∖ f⁻¹(∞)` of a morphism to `ℙ¹`. -/
noncomputable abbrev lineCover : Scheme.{u} :=
  pullback f (lineι k)

/-- The ring of functions on the affine part of `f`. -/
abbrev lineCoverRing : Type u :=
  Γ(lineCover f, ⊤)

/-- `B = Γ(X ×_{ℙ¹} 𝔸¹, ⊤)` is a `k[X]`-algebra through the second projection. -/
noncomputable instance : Algebra (Polynomial k) (lineCoverRing f) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv ≫
    (pullback.snd f (lineι k)).appTop).hom.toAlgebra

/-- `B` is a `k`-algebra through `k[X]`. -/
noncomputable instance : Algebra k (lineCoverRing f) :=
  ((algebraMap (Polynomial k) (lineCoverRing f)).comp (algebraMap k (Polynomial k))).toAlgebra

instance : IsScalarTower k (Polynomial k) (lineCoverRing f) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

lemma algebraMap_lineCoverRing :
    algebraMap (Polynomial k) (lineCoverRing f) =
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv ≫
        (pullback.snd f (lineι k)).appTop).hom :=
  rfl

variable {f}

/-- `X ×_{ℙ¹} 𝔸¹ ⟶ 𝔸¹` is finite. -/
theorem isFinite_lineCover_snd [IsFinite f] : IsFinite (pullback.snd f (lineι k)) :=
  MorphismProperty.pullback_snd _ _ inferInstance

theorem isAffine_lineCover [IsFinite f] : IsAffine (lineCover f) :=
  haveI := isFinite_lineCover_snd (f := f)
  isAffine_of_isAffineHom (pullback.snd f (lineι k))

/-- **`B` is a finite `k[X]`-algebra.** -/
theorem lineCoverRing_finite [IsFinite f] : Module.Finite (Polynomial k) (lineCoverRing f) := by
  haveI := isFinite_lineCover_snd (f := f)
  have h := (pullback.snd f (lineι k)).finite_appTop
  have hiso : ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv).hom.Finite :=
    RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv).2
  exact h.comp hiso

/-- **`X ×_{ℙ¹} 𝔸¹ ≅ Spec B` over `𝔸¹`.** -/
theorem lineCover_isoSpec_hom_comp [IsFinite f] :
    haveI := isAffine_lineCover (f := f)
    (lineCover f).isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (lineCoverRing f))) =
      pullback.snd f (lineι k) := by
  haveI := isAffine_lineCover (f := f)
  rw [algebraMap_lineCoverRing, CommRingCat.ofHom_hom, Spec.map_comp,
    Scheme.isoSpec_hom_naturality_assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.comp_id]

end Cover

section Etale

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ P1 k}

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **`k[X] → B[(t(t-1))⁻¹]` is étale** if `f` is étale over the thrice-punctured line:
`Spec (B ⊗_{k[X]} k[X][(X(X-1))⁻¹])` is the part of `X` over the punctured line (pasting of
pullbacks along `puncturedι = Spec (k[X] → R_k) ≫ lineι`), and `B ⊗_{k[X]} R_k = B[(t(t-1))⁻¹]`. -/
theorem etale_lineCoverRing_localization [IsFinite f]
    (het : Etale (pullback.snd f (puncturedι k))) :
    ((algebraMap (lineCoverRing f) (Localization.Away
      (algebraMap (Polynomial k) (lineCoverRing f) (puncturedPoly k)))).comp
        (algebraMap (Polynomial k) (lineCoverRing f))).Etale := by
  haveI := isAffine_lineCover (f := f)
  let B := lineCoverRing f
  let Rk := puncturedRing k
  let A := Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) Rk))
  let e1 : pullback f (puncturedι k) ≅ pullback f (A ≫ lineι k) :=
    pullback.congrHom rfl (puncturedι_eq_comp_lineι k)
  let e2 := (pullbackLeftPullbackSndIso f (lineι k) A).symm
  let e3 : pullback (pullback.snd f (lineι k)) A ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) B))) A :=
    asIso (pullback.map _ _ _ _ (lineCover f).isoSpec.hom (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, lineCover_isoSpec_hom_comp]) (by simp))
  let e4 := pullbackSpecIso (Polynomial k) B Rk
  have h4 := pullbackSpecIso_hom_snd (Polynomial k) B Rk
  have h3 : e3.hom ≫ pullback.snd _ _ = pullback.snd _ _ :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have h2 : e2.hom ≫ pullback.snd _ _ = pullback.snd _ _ :=
    pullbackLeftPullbackSndIso_inv_snd_snd f (lineι k) A
  have h1 : e1.hom ≫ pullback.snd _ _ = pullback.snd _ _ :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hcomp : (e1 ≪≫ e2 ≪≫ e3 ≪≫ e4).hom ≫
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
        Rk →ₐ[Polynomial k] B ⊗[Polynomial k] Rk) : Rk →+* B ⊗[Polynomial k] Rk)) =
        pullback.snd f (puncturedι k) := by
    simp only [Iso.trans_hom, Category.assoc]
    rw [h4, h3, h2, h1]
  have hE : Etale (Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
      Rk →ₐ[Polynomial k] B ⊗[Polynomial k] Rk) : Rk →+* B ⊗[Polynomial k] Rk))) := by
    rw [← hcomp] at het
    exact (MorphismProperty.cancel_left_of_respectsIso @Etale _ _).mp het
  have hR : ((Algebra.TensorProduct.includeRight :
      Rk →ₐ[Polynomial k] B ⊗[Polynomial k] Rk) : Rk →+* B ⊗[Polynomial k] Rk).Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hE
  haveI : Algebra.Etale (Polynomial k) Rk := Algebra.Etale.of_isLocalizationAway (puncturedPoly k)
  have hloc : (algebraMap (Polynomial k) Rk).Etale := RingHom.etale_algebraMap.2 inferInstance
  have hT : (algebraMap (Polynomial k) (B ⊗[Polynomial k] Rk)).Etale := by
    have := RingHom.Etale.stableUnderComposition _ _ hloc hR
    convert this using 1
    refine RingHom.ext fun p ↦ ?_
    change algebraMap (Polynomial k) (B ⊗[Polynomial k] Rk) p = (1 : B) ⊗ₜ algebraMap _ Rk p
    rw [Algebra.TensorProduct.algebraMap_apply']
  -- `B ⊗_{k[X]} R_k` is the localisation of `B` at `t (t - 1)`
  haveI : Algebra.IsPushout (Polynomial k) B Rk (B ⊗[Polynomial k] Rk) := TensorProduct.isPushout
  haveI hl : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers (puncturedPoly k)))
      (B ⊗[Polynomial k] Rk) :=
    (Algebra.isLocalization_iff_isPushout (Submonoid.powers (puncturedPoly k)) (A := Rk)).2
      inferInstance
  rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at hl
  let ψ := IsLocalization.algEquiv
    (Submonoid.powers (algebraMap (Polynomial k) B (puncturedPoly k)))
    (B ⊗[Polynomial k] Rk) (Localization.Away (algebraMap (Polynomial k) B (puncturedPoly k)))
  have e : (algebraMap B (Localization.Away (algebraMap (Polynomial k) B (puncturedPoly k)))).comp
      (algebraMap (Polynomial k) B) =
      ψ.toRingEquiv.toRingHom.comp (algebraMap (Polynomial k) (B ⊗[Polynomial k] Rk)) := by
    refine RingHom.ext fun p ↦ ?_
    change _ = ψ (algebraMap B (B ⊗[Polynomial k] Rk) (algebraMap (Polynomial k) B p))
    rw [ψ.commutes]
    rfl
  rw [e]
  exact RingHom.Etale.respectsIso.1 _ ψ.toRingEquiv hT

end Etale

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ P1 k}

/-- **The affine part of a finite morphism from a curve is smooth of relative dimension one**:
it is an open subscheme of the curve. -/
theorem smoothOfRelativeDimension_lineCoverRing [X.Over (Spec (CommRingCat.of k))]
    [IsCurveOver k X] [IsFinite f]
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap k (lineCoverRing f)))) := by
  haveI := isAffine_lineCover (f := f)
  have e : Spec.map (CommRingCat.ofHom (algebraMap k (lineCoverRing f))) =
      (lineCover f).isoSpec.inv ≫ pullback.fst f (lineι k) ≫ (X ↘ Spec (CommRingCat.of k)) := by
    rw [Iso.eq_inv_comp, show algebraMap k (lineCoverRing f) =
        (algebraMap (Polynomial k) (lineCoverRing f)).comp (algebraMap k (Polynomial k)) from rfl,
      CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc, lineCover_isoSpec_hom_comp,
      ← lineι_structMap, ← pullback.condition_assoc, hfk]
  rw [e]
  haveI h1 : SmoothOfRelativeDimension (0 + 1)
      (pullback.fst f (lineι k) ≫ (X ↘ Spec (CommRingCat.of k))) :=
    smoothOfRelativeDimension_comp 0 1 (pullback.fst f (lineι k)) (X ↘ Spec (CommRingCat.of k))
  rw [zero_add] at h1
  haveI h2 := smoothOfRelativeDimension_comp 0 1 (lineCover f).isoSpec.inv
    (pullback.fst f (lineι k) ≫ (X ↘ Spec (CommRingCat.of k)))
  rw [zero_add] at h2
  exact h2

/-- The affine part of a Belyi map is nonempty. -/
theorem nonempty_lineCover [CharZero k] [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X]
    (hf : IsBelyiMap k f) : Nonempty (lineCover f) := by
  obtain ⟨x⟩ := nonempty_puncturedCover (K := k) hf
  let e : puncturedCover f ⟶ lineCover f :=
    (pullback.congrHom rfl (puncturedι_eq_comp_lineι k)).hom ≫
      (pullbackLeftPullbackSndIso f (lineι k) _).inv ≫ pullback.fst _ _
  exact ⟨e x⟩

theorem isIntegral_lineCover [CharZero k] [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X]
    (hf : IsBelyiMap k f) : IsIntegral (lineCover f) := by
  haveI := IsCurveOver.isIntegral k X
  haveI := nonempty_lineCover hf
  exact isIntegral_of_isOpenImmersion (pullback.fst f (lineι k))

theorem isDomain_lineCoverRing [CharZero k] [X.Over (Spec (CommRingCat.of k))]
    [IsCurveOver k X] (hf : IsBelyiMap k f) : IsDomain (lineCoverRing f) := by
  haveI := isIntegral_lineCover hf
  infer_instance

instance finiteType_lineCoverRing [IsFinite f] :
    Algebra.FiniteType k (lineCoverRing f) := by
  haveI := lineCoverRing_finite (f := f)
  exact Algebra.FiniteType.trans (S := Polynomial k) inferInstance inferInstance

/-- `MvPolynomial (Fin 1) k ≃ k[X]`, `X₀ ↦ X`. -/
noncomputable def finOnePolyEquiv (k : Type u) [CommRing k] :
    MvPolynomial (Fin 1) k ≃ₐ[k] Polynomial k :=
  MvPolynomial.uniqueAlgEquiv k (Fin 1)

lemma finOnePolyEquiv_eq (k : Type u) [CommRing k] :
    (finOnePolyEquiv k : MvPolynomial (Fin 1) k →ₐ[k] Polynomial k) =
      MvPolynomial.aeval fun _ ↦ Polynomial.X :=
  MvPolynomial.algHom_ext fun i ↦ by simp [finOnePolyEquiv]

/-- **The branched data of the affine part of a Belyi map**: the coordinate `t` of `𝔸¹`. -/
noncomputable def IsBelyiMap.branchedData [CharZero k] [IsAlgClosed k]
    [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] (hf : IsBelyiMap k f) :
    Converse.BranchedData k (lineCoverRing f) where
  t := algebraMap (Polynomial k) (lineCoverRing f) Polynomial.X
  finite := by
    haveI := hf.isFinite
    haveI := lineCoverRing_finite (f := f)
    have e : (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦
        algebraMap (Polynomial k) (lineCoverRing f) Polynomial.X) =
        (IsScalarTower.toAlgHom k (Polynomial k) (lineCoverRing f)).comp
          (finOnePolyEquiv k : MvPolynomial (Fin 1) k →ₐ[k] Polynomial k) :=
      MvPolynomial.algHom_ext fun i ↦ by simp [finOnePolyEquiv_eq]
    rw [AlgHom.Finite, e]
    exact RingHom.Finite.comp (RingHom.finite_algebraMap.2 inferInstance)
      (RingHom.Finite.of_surjective _ (finOnePolyEquiv k).surjective)
  etale := by
    haveI := hf.isFinite
    have hh : MvPolynomial.aeval (R := k) (fun _ : Fin 1 ↦
        algebraMap (Polynomial k) (lineCoverRing f) Polynomial.X)
          (Converse.branchPolyZeroOne k) =
        algebraMap (Polynomial k) (lineCoverRing f) (puncturedPoly k) := by
      simp [Converse.branchPolyZeroOne, puncturedPoly]
    rw [hh]
    have e : (algebraMap (lineCoverRing f) (Localization.Away
        (algebraMap (Polynomial k) (lineCoverRing f) (puncturedPoly k)))).comp
          (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦
            algebraMap (Polynomial k) (lineCoverRing f) Polynomial.X).toRingHom =
        ((algebraMap (lineCoverRing f) (Localization.Away
          (algebraMap (Polynomial k) (lineCoverRing f) (puncturedPoly k)))).comp
            (algebraMap (Polynomial k) (lineCoverRing f))).comp
              (finOnePolyEquiv k).toRingEquiv.toRingHom := by
      refine MvPolynomial.ringHom_ext (fun c ↦ ?_) fun i ↦ ?_
      · simp [finOnePolyEquiv]
        rfl
      · simp [finOnePolyEquiv]
    rw [e]
    exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (finOnePolyEquiv k).bijective)
      (etale_lineCoverRing_localization (etale_puncturedCover_snd hf))

end Curve

section Pi1

open ComplexAnalytic Converse

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
  [Algebra k (ULift.{u} ℂ)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X]
  {f : X ⟶ P1 k} [IsFinite f]

/-- **`π₁ᵉᵗ` of the affine part of a Belyi map**: for a Belyi map `f : X → ℙ¹` over `k`
(algebraically closed, characteristic zero, algebraic over `ℚ`, `k ⊆ ℂ`), `π₁ᵉᵗ` of
`X ∖ f⁻¹(∞) = Spec B` is the profinite completion of a free group of rank `d + 1 - c₀ - c₁`, where
`d`, `c₀`, `c₁` are the numbers of maximal ideals of `ℂ ⊗ B` containing `t - c` (`c ∉ {0, 1}`),
`t`, `t - 1` (`t` the coordinate of `𝔸¹`). The geometric point is the one given by any point `x`
of the analytification of `Spec (ℂ ⊗ B)`. -/
theorem IsBelyiMap.exists_etaleFundamentalGroup_equiv_completion_freeGroup (hf : IsBelyiMap k f)
    (hfk : f ≫ (P1 k ↘ Spec (CommRingCat.of k)) = X ↘ Spec (CommRingCat.of k)) {c : ℂ}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) (x : analytification.obj (baseChangeSpec k (lineCoverRing f))) :
    ∃ (ι : Type u) (_ : Finite ι),
      Nonempty (π₁ᵉᵗ(geometricPoint (baseChangeSpec k (lineCoverRing f)) x ≫
          FiniteEtale.baseChangeSpec k (ULift.{u} ℂ) (lineCoverRing f)) ≃ₜ*
        ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FreeGroup ι))) ∧
      Nat.card ι + fiberCard (ULift.{u} ℂ ⊗[k] lineCoverRing f) (1 ⊗ₜ hf.branchedData.t) c +
          (fiberCard (ULift.{u} ℂ ⊗[k] lineCoverRing f) (1 ⊗ₜ hf.branchedData.t) 0 +
            fiberCard (ULift.{u} ℂ ⊗[k] lineCoverRing f) (1 ⊗ₜ hf.branchedData.t) 1) =
        2 * fiberCard (ULift.{u} ℂ ⊗[k] lineCoverRing f) (1 ⊗ₜ hf.branchedData.t) c + 1 := by
  haveI := isDomain_lineCoverRing hf
  haveI := smoothOfRelativeDimension_lineCoverRing hfk
  exact hf.branchedData.exists_etaleFundamentalGroup_equiv_completion_freeGroup hc0 hc1 x

end Pi1

end Belyi
