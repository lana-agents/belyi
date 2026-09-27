/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.AlgebraicGeometry.Normalization
import Belyi.Converse.IntegralClosureBaseChange
import Belyi.Definable

/-!
# Normalization commutes with base change along a field extension (P2b)

Package P2b of `references/converse-rie-design.md`. For a qcqs morphism `f : X ⟶ S` of schemes
over a field `k` of characteristic zero (more generally, a perfect field) and a field extension
`K / k`, the relative normalization commutes with the base change `S ×ₖ K ⟶ S`:
`Scheme.Hom.normalizationPullback f (pullback.fst p (specAlgebraMap k K))` is an isomorphism.

The proof follows mathlib's proof that normalization commutes with smooth base change
(the instance `IsIso (f.normalizationPullback g)` for smooth `g`, Stacks 03GV), with the
ring-theoretic input replaced by `Belyi.toIntegralClosure_bijective_of_isPushout`
(integral closure commutes with base change along `k → K`, via generic smoothness).

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_normalizationPullback_of_bijective`: for a flat affine
  morphism `g : Y ⟶ S` such that for every affine open `U ⊆ S` the ring map
  `Γ(S, U) → Γ(Y, g⁻¹ U)` commutes with integral closures, normalization commutes with the base
  change along `g`.
* `Belyi.isIso_normalizationPullback_specAlgebraMap`: the case `g = S ×ₖ Spec K ⟶ S`.
-/

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry.Scheme.Hom

variable {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Normalization commutes with base change along a flat affine morphism `g : Y ⟶ S` for which,
for every affine open `U ⊆ S`, the ring map `Γ(S, U) → Γ(Y, g⁻¹ U)` commutes with integral
closures (i.e. `TensorProduct.toIntegralClosure` is bijective). This is mathlib's proof of the
smooth case (Stacks 03GV) with the ring-theoretic input made a hypothesis. -/
theorem isIso_normalizationPullback_of_bijective [Flat g] [IsAffineHom g]
    (H : ∀ U : S.Opens, IsAffineOpen U → ∀ (B : Type u) [CommRing B] [Algebra Γ(S, U) B],
      letI := (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom.toAlgebra
      Function.Bijective (toIntegralClosure Γ(S, U) Γ(Y, g ⁻¹ᵁ U) B)) :
    IsIso (f.normalizationPullback g) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := .isomorphisms _) fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((pullback.snd _ g ≫ g) x)) isOpen_univ
  set V := g ⁻¹ᵁ U with hVdef
  have hV : IsAffineOpen V := hU.preimage g
  have hxV : pullback.snd _ g x ∈ V := hxU
  have hVU : V ≤ g ⁻¹ᵁ U := le_rfl
  let W := pullback.snd (Scheme.Hom.fromNormalization f) g ⁻¹ᵁ V
  refine ⟨W, hxV, (isIso_morphismRestrict_iff_isIso_app _ (U := W) (hV.preimage _)).mpr ?_⟩
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback f.fromNormalization g) hVU le_rfl (UY := W)
    (by simp_rw [W, ← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV
    (hU.preimage f.fromNormalization).isCompact (hU.preimage f.fromNormalization).isQuasiSeparated
  rw [← @isIso_comp_left_iff _ _ _ _ _ _ _ this,
    ← isIso_comp_left_iff (pushout.congrHom f.fromNormalization.app_eq_appLE rfl).hom]
  algebraize [(f.app U).hom, (g.appLE U V hVU).hom, ((pullback.snd f g).app V).hom]
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback f g) hVU le_rfl (UY := pullback.snd f g ⁻¹ᵁ V)
    (by simp_rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV (f.isCompact_preimage hU.isCompact)
    (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  let e₀ := (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout ≪≫
    (pushout.congrHom f.app_eq_appLE rfl ≪≫ @asIso _ _ _ _ _ this :)
  let e : Γ(Y, V) ⊗[Γ(S, U)] Γ(X, f ⁻¹ᵁ U) ≃ₐ[Γ(Y, V)] Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    { toRingEquiv := e₀.commRingCatIsoToRingEquiv,
      commutes' r := by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e₀.hom) r =
          (pullback.snd f g).app V r
        congr 2
        simp [e₀, pushout.inr_desc_assoc, Scheme.Hom.app_eq_appLE] }
  let ψ : Γ(Y, V) ⊗[Γ(S, U)] integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, V)]
      integralClosure Γ(Y, V) Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    e.mapIntegralClosure.toAlgHom.comp (TensorProduct.toIntegralClosure _ _ _)
  have hψ : Function.Bijective ψ := e.mapIntegralClosure.bijective.comp
    (H U hU Γ(X, f ⁻¹ᵁ U))
  let φ : pushout (f.fromNormalization.app U) (g.appLE U V hVU) ⟶
      Γ((pullback.snd f g).normalization, f.normalizationPullback g ⁻¹ᵁ W) :=
    pushout.map _ _ (CommRingCat.ofHom (algebraMap Γ(S, U) (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U))))
      (g.appLE U V hVU) (f.normalizationObjIso hU).hom (𝟙 _) (𝟙 _)
      (by simp [Scheme.Hom.fromNormalization_app _ hU]) (by simp) ≫
    (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout.inv ≫
    (RingEquiv.ofBijective ψ.toRingHom hψ).toCommRingCatIso.hom ≫
    ((pullback.snd f g).normalizationObjIso hV).inv ≫
    (pullback.snd f g).normalization.presheaf.map (eqToHom
      (by simp only [W, ← Scheme.Hom.comp_preimage, Scheme.Hom.normalizationPullback_snd])).op
  convert! show IsIso φ by dsimp only [φ]; infer_instance using 1
  ext1
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_left, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE, eqToHom_op,
      Category.assoc, IsPushout.inl_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, inv_eqToHom, Scheme.Hom.appLE_map, IsIso.Iso.inv_inv,
      Category.assoc]
    have : Mono (CommRingCat.ofHom (integralClosure Γ(Y, V)
        Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V)).val.toRingHom) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    rw [← cancel_mono (CommRingCat.ofHom (Subalgebra.val _).toRingHom)]
    simp only [Category.assoc, Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.toNormalization_normalizationPullback_fst, ← CommRingCat.ofHom_comp]
    have H : pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ f ⁻¹ᵁ U := by
      rw [hVdef, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
    trans (f.normalizationObjIso hU).hom ≫ CommRingCat.ofHom
        (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U)).val.toRingHom ≫ (pullback.fst f g).appLE _ _ H
    · rw [reassoc_of% Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE]
    · congr 1
      ext x
      change (pullback.fst f g).appLE _ _ H x = _
      trans (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e₀.hom) x
      · congr 2; simp [e₀, pushout.inl_desc_assoc]
      · simp [ψ, toIntegralClosure, e]; rfl
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_right, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.normalizationPullback_snd, eqToHom_op, IsPushout.inr_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, inv_eqToHom, Scheme.Hom.appLE_map, ← Scheme.Hom.app_eq_appLE,
      Scheme.Hom.fromNormalization_app _ hV, IsIso.Iso.inv_inv, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    exact congr(CommRingCat.ofHom $(ψ.comp_algebraMap.symm))

end AlgebraicGeometry.Scheme.Hom

namespace Belyi

open AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- **P2b.** Relative normalization commutes with base change along a field extension `K / k`
of a perfect field `k` (e.g. of characteristic zero): for `f : X ⟶ S` qcqs with `S` over `k`,
the comparison map from the normalization of `S ×ₖ K` in `X ×ₖ K` to the base change of the
normalization of `S` in `X` is an isomorphism. -/
theorem isIso_normalizationPullback_specAlgebraMap (k K : Type u) [Field k] [PerfectField k]
    [Field K] [Algebra k K] {X S : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k))
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] :
    IsIso (f.normalizationPullback (pullback.fst p (specAlgebraMap k K))) := by
  haveI : Flat (specAlgebraMap k K) := by
    rw [specAlgebraMap, Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : IsAffineHom (pullback.fst p (specAlgebraMap k K)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  refine Scheme.Hom.isIso_normalizationPullback_of_bijective f _ fun U hU B _ _ ↦ ?_
  set s := specAlgebraMap k K with hs
  set g := pullback.fst p s with hg
  -- The pushout square of sections `Γ(S, U) ⊗[Γ(Spec k)] Γ(Spec K) ≅ Γ(S ×ₖ K, g⁻¹ U)`.
  have h₁ := (isIso_pushoutSection_iff (IsPullback.of_hasPullback p s) (US := ⊤) (UT := ⊤)
    (UX := U) (UY := g ⁻¹ᵁ U) le_top le_top (by rw [hg]; simp)).mp
    (isIso_pushoutSection_of_isAffineOpen _ _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hU)
  have h₀ : IsPushout (Scheme.ΓSpecIso (CommRingCat.of k)).inv
      (CommRingCat.ofHom (algebraMap k K)) (s.appLE ⊤ ⊤ le_top)
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv := by
    refine IsPushout.of_horiz_isIso ⟨?_⟩
    rw [Scheme.ΓSpecIso_inv_naturality, hs, specAlgebraMap, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    rfl
  have h₂ := h₀.paste_horiz h₁
  letI : Algebra k Γ(S, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U le_top).hom.toAlgebra
  letI : Algebra Γ(S, U) Γ(pullback p s, g ⁻¹ᵁ U) := (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  letI : Algebra K Γ(pullback p s, g ⁻¹ᵁ U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (pullback.snd p s).appLE ⊤ (g ⁻¹ᵁ U) le_top).hom.toAlgebra
  letI : Algebra k Γ(pullback p s, g ⁻¹ᵁ U) :=
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U le_top) ≫
      g.appLE U (g ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  haveI : IsScalarTower k Γ(S, U) Γ(pullback p s, g ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  haveI : IsScalarTower k K Γ(pullback p s, g ⁻¹ᵁ U) :=
    .of_algebraMap_eq fun x ↦ congrArg (fun φ ↦ φ.hom x) h₂.w
  haveI : Algebra.IsPushout k Γ(S, U) K Γ(pullback p s, g ⁻¹ᵁ U) :=
    CommRingCat.isPushout_iff_isPushout.mp h₂
  exact toIntegralClosure_bijective_of_isPushout k Γ(S, U) B K Γ(pullback p s, g ⁻¹ᵁ U)

end Belyi
