/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Converse.AnalyticProduct
import Belyi.Converse.CoveringHomotopy
import Oka.Analytification.RET.FullyFaithful
import Oka.Analytification.RET.Pullback
import Oka.Analytification.RET.Separated
import Oka.AnalyticSpace.FiniteEtaleBaseChange

/-!
# Topological rigidity of families of finite étale covers (S3c)

Step (S3c) of the converse direction of Belyi's theorem (`references/converse-rie-design.md`):
let `Z`, `T` be affine schemes of finite type over `ℂ`, `P = Z ×_ℂ T` and `𝒴 ⟶ P` finite étale.
If `T^an` is path connected, then for any two `ℂ`-points `t₀, t₁` of `T` the fibres
`𝒴_{t₀}` and `𝒴_{t₁}` (finite étale covers of `Z`) are isomorphic.

Proof: `𝒴^an ⟶ P^an ≅ Z^an × T^an` (`Belyi.Converse.isHomeomorph_analytificationProdMk`) is a
covering map (oka `isCoveringMap_base_of_isFiniteEtale`, `𝒴^an` is Hausdorff since `𝒴` is affine).
By the covering homotopy lemma (`Belyi.Converse.exists_homeomorph_fiber`) its restrictions to
`Z^an × {t₀}` and `Z^an × {t₁}` are homeomorphic over `Z^an`. These restrictions are the
analytifications of `𝒴_{t₀}`, `𝒴_{t₁}`: analytification preserves fibre products
(`Belyi.Converse.isPullback_analytification_map`, from oka's
`isPullback_analytification_map_fibreProd`), and a fibre product along a finite étale map of
analytic spaces has the topological fibre product as underlying space (oka's
`AnalyticSpace.baseChange`). A homeomorphism over the base between finite étale analytic covers
is an isomorphism of covers (oka `AnalyticSpace.FiniteEtaleOver.isoOfHomeomorph`), and
analytification is fully faithful on finite étale covers (oka
`fullyFaithfulAnalytificationFiniteEtaleOver`, the Riemann existence theorem's full faithfulness
half).

## Main results

* `Belyi.Converse.isPullback_analytification_map`: analytification sends pullback squares of
  schemes locally of finite type over `ℂ` to pullback squares of analytic spaces.
* `Belyi.Converse.nonempty_iso_fiberCover`: the rigidity statement, as an isomorphism in
  `SchemeLFTℂ.FiniteEtaleOver Z`.
* `Belyi.Converse.exists_iso_of_isPullback_fiber`: the same, as an isomorphism of schemes over
  `Z`.

## Phrasing

The product `P = Z ×_ℂ T` and the fibres `𝒴_{tᵢ} = 𝒴 ×_P Z` (pulled back along the sections
`jᵢ = (id, tᵢ) : Z ⟶ P`) are given by arbitrary pullback squares of the underlying schemes, and the
sections `jᵢ` by their two components. The `ℂ`-points are morphisms from
`Belyi.Converse.pointLFT = Spec ℂ`. `Z` and `T` are assumed affine (this is where we identify
`P^an` with the topological product); this is all that the converse needs.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Topology ComplexAnalytic

namespace Belyi.Converse

noncomputable section

/-! ### Analytification preserves pullbacks -/

section Pullback

variable {W Y Z P : SchemeLFTℂ.{u}} {h : W ⟶ Y} {g : W ⟶ Z} {f : Y ⟶ P} {j : Z ⟶ P}

/-- A pullback square of underlying schemes identifies `W` with oka's fibre product
`SchemeLFTℂ.fibreProd f j`. -/
def isoFibreProdOfIsPullback (hsq : IsPullback h.hom.left g.hom.left f.hom.left j.hom.left) :
    W ≅ SchemeLFTℂ.fibreProd f j :=
  ObjectProperty.isoMk _ (Over.isoMk hsq.isoPullback (by
    change hsq.isoPullback.hom ≫ pullback.fst f.hom.left j.hom.left ≫ Y.obj.hom = W.obj.hom
    rw [IsPullback.isoPullback_hom_fst_assoc, Over.w h.hom]))

lemma isoFibreProdOfIsPullback_hom_fst
    (hsq : IsPullback h.hom.left g.hom.left f.hom.left j.hom.left) :
    (isoFibreProdOfIsPullback hsq).hom ≫ SchemeLFTℂ.fibreProdFst f j = h := by
  ext1
  exact Over.OverMorphism.ext (IsPullback.isoPullback_hom_fst hsq)

lemma isoFibreProdOfIsPullback_hom_snd
    (hsq : IsPullback h.hom.left g.hom.left f.hom.left j.hom.left) :
    (isoFibreProdOfIsPullback hsq).hom ≫ SchemeLFTℂ.fibreProdSnd f j = g := by
  ext1
  exact Over.OverMorphism.ext (IsPullback.isoPullback_hom_snd hsq)

/-- **Analytification preserves pullback squares.** -/
theorem isPullback_analytification_map
    (hsq : IsPullback h.hom.left g.hom.left f.hom.left j.hom.left) :
    IsPullback (analytification.map h) (analytification.map g) (analytification.map f)
      (analytification.map j) := by
  refine (isPullback_analytification_map_fibreProd f j).of_iso
    (analytification.mapIso (isoFibreProdOfIsPullback hsq)).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp only [Iso.symm_hom, Functor.mapIso_inv, Iso.refl_hom, Category.comp_id]
    rw [← Functor.map_comp]
    congr 1
    rw [Iso.eq_inv_comp]
    exact isoFibreProdOfIsPullback_hom_fst hsq
  · simp only [Iso.symm_hom, Functor.mapIso_inv, Iso.refl_hom, Category.comp_id]
    rw [← Functor.map_comp]
    congr 1
    rw [Iso.eq_inv_comp]
    exact isoFibreProdOfIsPullback_hom_snd hsq

end Pullback

/-! ### Fibres of a finite étale family over a `ℂ`-point -/

section Fiber

variable {Z T P Y : SchemeLFTℂ.{u}} {pZ : P ⟶ Z} {pT : P ⟶ T}

lemma analytificationProdMk_section {t : pointLFT.{u} ⟶ T} {j : Z ⟶ P}
    (hjZ : j ≫ pZ = 𝟙 Z) (hjT : j ≫ pT = toPointLFT Z ≫ t)
    (p : analytification.obj pointLFT.{u}) (z : analytification.obj Z) :
    analytificationProdMk pZ pT ((analytification.map j).toLRSHom.base z) =
      (z, (analytification.map t).toLRSHom.base p) := by
  refine Prod.ext ?_ ?_
  · change (analytification.map pZ).toLRSHom.base _ = z
    rw [← analytification_base_comp_apply, hjZ, analytification.map_id]
    rfl
  · change (analytification.map pT).toLRSHom.base _ = _
    rw [← analytification_base_comp_apply, hjT, analytification_base_comp_apply]
    exact analytification_map_apply_eq_of_subsingleton _ _ _

/-- The topological fibre of `𝒴^an ⟶ Z^an × T^an` over `Z^an × {t}` is the topological fibre
product of `𝒴^an ⟶ P^an` and the section `j^an : Z^an ⟶ P^an`. -/
def pullbackHomeomorphFiber (f : Y ⟶ P) {t : pointLFT.{u} ⟶ T} {j : Z ⟶ P}
    (hjZ : j ≫ pZ = 𝟙 Z) (hjT : j ≫ pT = toPointLFT Z ≫ t)
    (p : analytification.obj pointLFT.{u})
    (hc : Function.Injective (analytificationProdMk pZ pT)) :
    Function.Pullback (analytification.map f).toLRSHom.base (analytification.map j).toLRSHom.base
      ≃ₜ {e : analytification.obj Y //
        (analytificationProdMk pZ pT ((analytification.map f).toLRSHom.base e)).2 =
          (analytification.map t).toLRSHom.base p} :=
  { toFun x := ⟨x.fst, by
      have hx : (analytification.map f).toLRSHom.base x.fst =
        (analytification.map j).toLRSHom.base x.snd := x.2
      rw [hx, analytificationProdMk_section hjZ hjT p]⟩
    invFun e := ⟨(e.1, (analytificationProdMk pZ pT ((analytification.map f).toLRSHom.base e.1)).1),
      hc (((Prod.ext rfl e.2 : analytificationProdMk pZ pT
          ((analytification.map f).toLRSHom.base e.1) =
            ((analytificationProdMk pZ pT ((analytification.map f).toLRSHom.base e.1)).1,
              (analytification.map t).toLRSHom.base p))).trans
          (analytificationProdMk_section hjZ hjT p _).symm)⟩
    left_inv x := by
      refine Subtype.ext (Prod.ext rfl ?_)
      change (analytificationProdMk pZ pT ((analytification.map f).toLRSHom.base x.fst)).1 = x.snd
      have hx : (analytification.map f).toLRSHom.base x.fst =
        (analytification.map j).toLRSHom.base x.snd := x.2
      rw [hx, analytificationProdMk_section hjZ hjT p]
    right_inv e := rfl
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ _
      exact continuous_fst.comp continuous_subtype_val
    continuous_invFun := by
      refine Continuous.subtype_mk (continuous_subtype_val.prodMk ?_) _
      exact continuous_fst.comp ((continuous_analytificationProdMk pZ pT).comp
        ((analytification.map f).toLRSHom.base.hom.continuous.comp continuous_subtype_val)) }

variable {W : SchemeLFTℂ.{u}} {g : W ⟶ Z} {h : W ⟶ Y} (f : Y ⟶ P) {j : Z ⟶ P}
  (hW : IsPullback h.hom.left g.hom.left f.hom.left j.hom.left)

/-- The map from the analytification of a fibre product to the topological fibre product. -/
def analytificationPullbackMap : analytification.obj W →
    Function.Pullback (analytification.map f).toLRSHom.base
      (analytification.map j).toLRSHom.base := fun w ↦
  ⟨((analytification.map h).toLRSHom.base w, (analytification.map g).toLRSHom.base w),
    congrArg (fun φ : analytification.obj W ⟶ analytification.obj P ↦ φ.toLRSHom.base w)
      (isPullback_analytification_map hW).w⟩

/-- The analytification of a fibre product along the finite étale `𝒴 ⟶ P` has the topological
fibre product as underlying space. -/
lemma isHomeomorph_analytificationPullbackMap
    [AnalyticSpace.IsFiniteEtale (analytification.map f)] :
    IsHomeomorph (analytificationPullbackMap f hW) := by
  have hA := isPullback_analytification_map hW
  have hB := AnalyticSpace.isPullback_baseChange (analytification.map f) (analytification.map j)
  let e := hA.isoIsPullback _ _ hB
  have H := AnalyticSpace.isHomeomorph_base_of_isIso e.hom
  have key : analytificationPullbackMap f hW = fun w ↦
      (e.hom.toLRSHom.base w : Function.Pullback (analytification.map f).toLRSHom.base
        (analytification.map j).toLRSHom.base) := by
    funext w
    refine Subtype.ext (Prod.ext ?_ ?_)
    · have h1 := congrArg (fun φ : analytification.obj W ⟶ analytification.obj Y ↦
        φ.toLRSHom.base w) (hA.isoIsPullback_hom_fst _ _ hB)
      have h2 : (AnalyticSpace.baseChangeFst (analytification.map f)
          (analytification.map j)).toLRSHom.base (e.hom.toLRSHom.base w) =
          (e.hom.toLRSHom.base w : Function.Pullback (analytification.map f).toLRSHom.base
            (analytification.map j).toLRSHom.base).fst := by
        rw [AnalyticSpace.base_baseChangeFst]
        rfl
      exact h1.symm.trans h2
    · have h1 := congrArg (fun φ : analytification.obj W ⟶ analytification.obj Z ↦
        φ.toLRSHom.base w) (hA.isoIsPullback_hom_snd _ _ hB)
      have h2 : (AnalyticSpace.baseChangeSnd (analytification.map f)
          (analytification.map j)).toLRSHom.base (e.hom.toLRSHom.base w) =
          (e.hom.toLRSHom.base w : Function.Pullback (analytification.map f).toLRSHom.base
            (analytification.map j).toLRSHom.base).snd := by
        rw [AnalyticSpace.base_baseChangeSnd]
        rfl
      exact h1.symm.trans h2
  rw [key]
  exact H

/-- **The analytification of the fibre `𝒴_t` is the topological fibre of `𝒴^an ⟶ Z^an × T^an`
over `Z^an × {t}`.** -/
def fiberHomeomorph {t : pointLFT.{u} ⟶ T} (hjZ : j ≫ pZ = 𝟙 Z)
    (hjT : j ≫ pT = toPointLFT Z ≫ t) (p : analytification.obj pointLFT.{u})
    [AnalyticSpace.IsFiniteEtale (analytification.map f)]
    (hc : Function.Injective (analytificationProdMk pZ pT)) :
    analytification.obj W ≃ₜ {e : analytification.obj Y //
        (analytificationProdMk pZ pT ((analytification.map f).toLRSHom.base e)).2 =
          (analytification.map t).toLRSHom.base p} :=
  ((isHomeomorph_analytificationPullbackMap f hW).homeomorph _).trans
    (pullbackHomeomorphFiber f hjZ hjT p hc)

lemma fiberHomeomorph_fst {t : pointLFT.{u} ⟶ T} (hjZ : j ≫ pZ = 𝟙 Z)
    (hjT : j ≫ pT = toPointLFT Z ≫ t) (p : analytification.obj pointLFT.{u})
    [AnalyticSpace.IsFiniteEtale (analytification.map f)]
    (hc : Function.Injective (analytificationProdMk pZ pT)) (w : analytification.obj W) :
    (analytificationProdMk pZ pT ((analytification.map f).toLRSHom.base
      (fiberHomeomorph f hW hjZ hjT p hc w).1)).1 = (analytification.map g).toLRSHom.base w := by
  change (analytificationProdMk pZ pT
    ((analytification.map h ≫ analytification.map f).toLRSHom.base w)).1 = _
  rw [(isPullback_analytification_map hW).w]
  change (analytificationProdMk pZ pT ((analytification.map j).toLRSHom.base
    ((analytification.map g).toLRSHom.base w))).1 = _
  rw [analytificationProdMk_section hjZ hjT p]

end Fiber

/-! ### Rigidity -/

section Rigidity

variable {Z T P Y : SchemeLFTℂ.{u}} {pZ : P ⟶ Z} {pT : P ⟶ T} {f : Y ⟶ P}
  {j : Z ⟶ P} {W : SchemeLFTℂ.{u}} {g : W ⟶ Z} {h : W ⟶ Y}

/-- The base change `g : W ⟶ Z` of a finite étale `f : 𝒴 ⟶ P` along `j : Z ⟶ P` is finite
étale. -/
lemma isFiniteEtale_of_isPullback (hf : SchemeLFTℂ.isFiniteEtale f)
    (hW : IsPullback h.hom.left g.hom.left f.hom.left j.hom.left) :
    SchemeLFTℂ.isFiniteEtale g := by
  haveI := hf.1
  haveI := hf.2
  exact ⟨MorphismProperty.of_isPullback (P := @IsFinite) hW hf.1,
    MorphismProperty.of_isPullback (P := @Etale) hW hf.2⟩

/-- The fibre `g : W ⟶ Z` of a finite étale `f : 𝒴 ⟶ P`, as a finite étale cover of `Z`. -/
abbrev fiberCover (hf : SchemeLFTℂ.isFiniteEtale f)
    (hW : IsPullback h.hom.left g.hom.left f.hom.left j.hom.left) :
    SchemeLFTℂ.FiniteEtaleOver Z :=
  MorphismProperty.Over.mk ⊤ g (isFiniteEtale_of_isPullback hf hW)

variable [IsAffine Z.obj.left] [IsAffine T.obj.left] [PathConnectedSpace (analytification.obj T)]
  (hP : IsPullback pZ.hom.left pT.hom.left Z.obj.hom T.obj.hom)
  (hf : SchemeLFTℂ.isFiniteEtale f)
  {t₀ t₁ : pointLFT.{u} ⟶ T} {j₀ j₁ : Z ⟶ P}
  (hj₀Z : j₀ ≫ pZ = 𝟙 Z) (hj₀T : j₀ ≫ pT = toPointLFT Z ≫ t₀)
  (hj₁Z : j₁ ≫ pZ = 𝟙 Z) (hj₁T : j₁ ≫ pT = toPointLFT Z ≫ t₁)
  {W₀ W₁ : SchemeLFTℂ.{u}} {g₀ : W₀ ⟶ Z} {h₀ : W₀ ⟶ Y} {g₁ : W₁ ⟶ Z} {h₁ : W₁ ⟶ Y}
  (hW₀ : IsPullback h₀.hom.left g₀.hom.left f.hom.left j₀.hom.left)
  (hW₁ : IsPullback h₁.hom.left g₁.hom.left f.hom.left j₁.hom.left)

include hP hj₀Z hj₀T hj₁Z hj₁T in
/-- **Topological rigidity (S3c).** Let `Z`, `T` be affine schemes of finite type over `ℂ` with
`T^an` path connected, `P = Z ×_ℂ T` and `f : 𝒴 ⟶ P` finite étale. Then the fibres of `𝒴`
over any two `ℂ`-points `t₀`, `t₁` of `T` are isomorphic finite étale covers of `Z`. Here the
fibre over `tᵢ` is any pullback `Wᵢ` of `f` along the section `jᵢ = (id, tᵢ) : Z ⟶ P`. -/
theorem nonempty_iso_fiberCover :
    Nonempty (fiberCover hf hW₀ ≅ fiberCover hf hW₁) := by
  haveI := hf.1
  haveI : IsAffine P.obj.left := IsAffine.of_isPullback hP
  haveI : IsAffine Y.obj.left := isAffine_of_isAffineHom f.hom.left
  haveI := t2Space_analytification_of_isAffine Y
  haveI := isFiniteEtale_analytification_map f hf
  have hc := isHomeomorph_analytificationProdMk hP
  obtain ⟨p⟩ := (inferInstance : Nonempty (analytification.obj pointLFT.{u}))
  let q : analytification.obj Y → analytification.obj Z × analytification.obj T :=
    analytificationProdMk pZ pT ∘ (analytification.map f).toLRSHom.base
  have hq : IsCoveringMap q :=
    (AnalyticSpace.isCoveringMap_base_of_isFiniteEtale (analytification.map f)).homeomorph_comp
      (hc.homeomorph _)
  obtain ⟨H, hH⟩ := exists_homeomorph_fiber hq ((analytification.map t₀).toLRSHom.base p)
    ((analytification.map t₁).toLRSHom.base p)
  let Φ₀ := fiberHomeomorph f hW₀ hj₀Z hj₀T p hc.injective
  let Φ₁ := fiberHomeomorph f hW₁ hj₁Z hj₁T p hc.injective
  let Ψ : analytification.obj W₀ ≃ₜ analytification.obj W₁ := (Φ₀.trans H).trans Φ₁.symm
  have hΨ (w : analytification.obj W₀) :
      (analytification.map g₁).toLRSHom.base (Ψ w) = (analytification.map g₀).toLRSHom.base w := by
    rw [← fiberHomeomorph_fst f hW₁ hj₁Z hj₁T p hc.injective,
      ← fiberHomeomorph_fst f hW₀ hj₀Z hj₀T p hc.injective]
    change (q (Φ₁ (Φ₁.symm (H (Φ₀ w)))).1).1 = (q (Φ₀ w).1).1
    rw [Homeomorph.apply_symm_apply]
    exact hH _
  let e := AnalyticSpace.FiniteEtaleOver.isoOfHomeomorph
    ((analytificationFiniteEtaleOver Z).obj (fiberCover hf hW₀))
    ((analytificationFiniteEtaleOver Z).obj (fiberCover hf hW₁)) Ψ hΨ
  exact ⟨(fullyFaithfulAnalytificationFiniteEtaleOver Z).preimageIso e⟩

include hP hf hj₀Z hj₀T hj₁Z hj₁T hW₀ hW₁ in
/-- **Topological rigidity (S3c)**, as an isomorphism of schemes over `Z`. -/
theorem exists_iso_of_isPullback_fiber :
    ∃ e : W₀.obj.left ≅ W₁.obj.left, e.hom ≫ g₁.hom.left = g₀.hom.left := by
  obtain ⟨e⟩ := nonempty_iso_fiberCover hP hf hj₀Z hj₀T hj₁Z hj₁T hW₀ hW₁
  let e' := (MorphismProperty.Over.forget _ _ _ ⋙ CategoryTheory.Over.forget _ ⋙
    ObjectProperty.ι _ ⋙ CategoryTheory.Over.forget _).mapIso e
  refine ⟨e', ?_⟩
  change e.hom.left.hom.left ≫ g₁.hom.left = g₀.hom.left
  rw [← Over.comp_left, ← ObjectProperty.FullSubcategory.comp_hom]
  exact congrArg (fun φ : W₀ ⟶ Z ↦ φ.hom.left) (MorphismProperty.Over.w e.hom)

end Rigidity

end

end Belyi.Converse
