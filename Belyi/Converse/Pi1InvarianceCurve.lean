/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Converse.Pi1InvarianceCharts
import Belyi.Converse.NormalizationOpen
import Belyi.Curve.BaseChange
import Belyi.Curve.Existence
import Belyi.P1.BaseChangeIso

/-!
# Invariance of `π₁ᵉᵗ` of a curve under extension of algebraically closed fields (INV-2)

Let `k` be algebraically closed of characteristic `0` and countable (e.g. `ℚ̄`), let `Ω ⊇ k` be
algebraically closed, and let `X` be a curve over `k` (`Belyi.IsCurveOver`: smooth, proper,
geometrically integral of relative dimension one). Write `X_Ω = X ×_k Ω` and `g : X_Ω ⟶ X` for
the projection. Then `π₁ᵉᵗ(X_Ω) → π₁ᵉᵗ(X)` is bijective
(`AlgebraicGeometry.FiniteEtale.fundamentalGroupMap_curve_baseChange_bijective`).

The proof feeds `FiniteEtale.fundamentalGroupMap_bijective_of_charts` with two affine charts
`U, U'` of `X` (`IsCurveOver.exists_two_affine_cover`: preimages of the two standard charts of
`ℙ¹` under a finite morphism `X ⟶ ℙ¹`) and their preimages in `X_Ω`; on the affine pieces
`U`, `U'`, `U ∩ U'` the comparison maps are bijective by INV-1
(`FiniteEtale.fundamentalGroupMap_bijective_of_isPullback`). The hypotheses of the étale van
Kampen theorem on `X` and `X_Ω` hold because curves are integral, locally Noetherian and have
integrally closed (valuation ring) stalks.

The base point is a geometric point of `X_Ω` over `U ∩ U'`; every geometric point over the
dense open `U ∩ U'` is allowed (`fundamentalGroupMap_curve_baseChange_bijective'`), and such a
cover exists for every curve (`exists_fundamentalGroupMap_curve_baseChange_bijective`).

## Main results

* `Belyi.IsCurveOver.isIntegrallyClosed_stalk`, `Belyi.IsCurveOver.exists_two_affine_cover`.
* `AlgebraicGeometry.FiniteEtale.fundamentalGroupMap_resLE_bijective`: INV-1 for the restriction
  of `X_Ω ⟶ X` over an affine open of `X`.
* `AlgebraicGeometry.FiniteEtale.fundamentalGroupMap_curve_baseChange_bijective`: INV-2.
-/

universe u

open CategoryTheory Limits

namespace Belyi

open AlgebraicGeometry

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [IsCurveOver k X]

include k in
/-- A curve is locally Noetherian (it is of finite type over a field). -/
theorem IsCurveOver.isLocallyNoetherian : IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k))

include k in
/-- In a curve, the intersection of two affine opens is affine (curves are separated). -/
theorem IsCurveOver.isAffineOpen_inf {U V : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) :=
  isAffineHom_diagonal_iff.mp (inferInstance :
    IsAffineHom (pullback.diagonal (X ↘ Spec (CommRingCat.of k)))) ⊤ (isAffineOpen_top _) U
    (by simp) V (by simp) hU hV

section Perfect

variable [PerfectField k]

include k in
/-- The stalks of a curve over a perfect field are integrally closed (they are valuation
rings). -/
theorem IsCurveOver.isIntegrallyClosed_stalk (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  classical
  haveI := IsCurveOver.isIntegral k X
  haveI := valuationRing_stalk_of_isCurveOver k X x
  letI := IsBezout.toGCDDomain (X.presheaf.stalk x)
  infer_instance

include k in
/-- A curve over a perfect field is covered by two affine opens (the preimages of the two
standard charts of `ℙ¹` under a finite morphism `X ⟶ ℙ¹`); their intersection is affine by
`IsCurveOver.isAffineOpen_inf`. -/
theorem IsCurveOver.exists_two_affine_cover :
    ∃ U V : X.affineOpens, U.1 ⊔ V.1 = ⊤ := by
  obtain ⟨π, hπ, -, -⟩ := exists_isFinite_surjective_hom_to_P1 k X
  have hcov : ∀ x : P1 k, x ∈ ((P1.coordCover k).openCover.f (0 : Fin 2)).opensRange ∨
      x ∈ ((P1.coordCover k).openCover.f (1 : Fin 2)).opensRange := by
    intro x
    obtain ⟨i, y, rfl⟩ := (P1.coordCover k).openCover.exists_eq x
    have hi : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    rcases hi i with rfl | rfl
    · exact Or.inl ⟨y, rfl⟩
    · exact Or.inr ⟨y, rfl⟩
  refine ⟨⟨π ⁻¹ᵁ ((P1.coordCover k).openCover.f (0 : Fin 2)).opensRange,
      (isAffineOpen_opensRange _).preimage π⟩,
    ⟨π ⁻¹ᵁ ((P1.coordCover k).openCover.f (1 : Fin 2)).opensRange,
      (isAffineOpen_opensRange _).preimage π⟩, ?_⟩
  ext x
  simp only [TopologicalSpace.Opens.coe_sup, Set.mem_union, SetLike.mem_coe,
    TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  exact hcov (π x)

end Perfect

end Belyi

namespace AlgebraicGeometry

/-- A nonempty open subscheme of an integral scheme is connected. -/
lemma connectedSpace_opens_of_isIntegral {X : Scheme.{u}} [IsIntegral X] (U : X.Opens)
    [Nonempty U] : ConnectedSpace U :=
  haveI : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
  inferInstance

/-- An open immersion with nonempty source into an integral scheme has dense range. -/
lemma denseRange_of_isOpenImmersion {X Y : Scheme.{u}} [IsIntegral X] (j : Y ⟶ X)
    [IsOpenImmersion j] [Nonempty Y] : DenseRange j.base :=
  j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

namespace FiniteEtale

open Belyi

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed k] [CharZero k]
  [Countable k] [IsAlgClosed Ω]

/-- Change of the base point along an equality of geometric points. -/
lemma fundamentalGroupMap_bijective_of_eq {X Y : Scheme.{u}} {L : Type u} [Field L]
    [IsSepClosed L] (f : Y ⟶ X) {x₁ x₂ : Spec (.of L) ⟶ Y} (e : x₁ = x₂)
    {η η' : Spec (.of L) ⟶ X} (h : x₁ ≫ f = η) (h' : x₂ ≫ f = η')
    (H : Function.Bijective (fundamentalGroupMap f h)) :
    Function.Bijective (fundamentalGroupMap f h') := by
  subst e
  obtain rfl : η = η' := h.symm.trans h'
  exact H

/-- **INV-1 for an affine scheme with a chosen presentation.** If `g : Y' ⟶ Y` is the base
change of `Spec Ω ⟶ Spec k` along `q : Y ⟶ Spec k` of finite type, with `Y ≅ Spec R`
connected, then `π₁ᵉᵗ(Y') → π₁ᵉᵗ(Y)` is bijective at every geometric point. -/
theorem fundamentalGroupMap_bijective_of_isPullback_of_iso {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (p : Y' ⟶ Spec (.of Ω)) (q : Y ⟶ Spec (.of k))
    (H : IsPullback g p q (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))
    [LocallyOfFiniteType q] [ConnectedSpace Y] (R : CommRingCat.{u}) (e : Y ≅ Spec R)
    {L : Type u} [Field L] [IsSepClosed L] (x : Spec (.of L) ⟶ Y') :
    Function.Bijective (fundamentalGroupMap g (rfl : x ≫ g = _)) := by
  set φ : CommRingCat.of k ⟶ R := Spec.preimage (e.inv ≫ q) with hφ
  have hSφ : Spec.map φ = e.inv ≫ q := Spec.map_preimage _
  letI : Algebra k R := φ.hom.toAlgebra
  have hft : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp (by rw [hSφ]; infer_instance)
  haveI : Algebra.FiniteType k R := hft
  haveI : ConnectedSpace (Spec (CommRingCat.of R)) :=
    (e.hom.homeomorph.surjective).connectedSpace e.hom.homeomorph.continuous
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = q := by
    change e.hom ≫ Spec.map φ = q
    rw [hSφ, Iso.hom_inv_id_assoc]
  exact fundamentalGroupMap_bijective_of_isPullback g p q H R e he x

/-- **INV-1 over an affine open.** Let `q : X ⟶ Spec k` be a `k`-scheme with base change
`g : X' ⟶ X` along `Spec Ω ⟶ Spec k` (a pullback square), and let `W ⊆ X` be a connected
affine open with `q|_W` of finite type. Then the restriction `g⁻¹ W ⟶ W` of `g` induces
bijections on `π₁ᵉᵗ` at every geometric point. -/
theorem fundamentalGroupMap_resLE_bijective {X X' : Scheme.{u}} (g : X' ⟶ X)
    (p : X' ⟶ Spec (.of Ω)) (q : X ⟶ Spec (.of k))
    (H : IsPullback g p q (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))
    (W : X.Opens) (hW : IsAffineOpen W) [ConnectedSpace W] [LocallyOfFiniteType (W.ι ≫ q)]
    (W' : X'.Opens) (hW' : W' = g ⁻¹ᵁ W) {L : Type u} [Field L] [IsSepClosed L]
    (x : Spec (.of L) ⟶ W') :
    Function.Bijective (fundamentalGroupMap (g.resLE W W' hW'.le) (rfl : x ≫ _ = _)) := by
  subst hW'
  haveI : IsAffine W := hW
  have H' : IsPullback (g.resLE W (g ⁻¹ᵁ W) le_rfl) ((g ⁻¹ᵁ W).ι ≫ p) (W.ι ≫ q)
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact (isPullback_morphismRestrict g W).paste_vert H
  exact fundamentalGroupMap_bijective_of_isPullback_of_iso _ _ _ H' _ W.toScheme.isoSpec x

/-- **INV-2, general form.** Let `X` be a curve over `k` (algebraically closed, characteristic
`0`, countable) and `g : X' ⟶ X` its base change along `Spec Ω ⟶ Spec k`
(`Ω ⊇ k` algebraically closed; `X'` a curve over `Ω`), let `U, U'` be affine opens covering
`X`, and `ζ` a geometric point of `X'` over `U ∩ U'`. Then `π₁ᵉᵗ(X', ζ) → π₁ᵉᵗ(X, ζ)` is
bijective. -/
theorem fundamentalGroupMap_bijective_of_isPullback_curve {X X' : Scheme.{u}} (g : X' ⟶ X)
    (p : X' ⟶ Spec (.of Ω)) (q : X ⟶ Spec (.of k))
    (H : IsPullback g p q (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))
    [X.Over (Spec (.of k))] [IsCurveOver k X] (hq : q = X ↘ Spec (.of k))
    [X'.Over (Spec (.of Ω))] [IsCurveOver Ω X']
    (U U' : X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hUU' : U ⊔ U' = ⊤)
    {L : Type u} [Field L] [IsSepClosed L]
    (ζ : Spec (.of L) ⟶ ((g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ U' : X'.Opens) : Scheme.{u})) :
    Function.Bijective (fundamentalGroupMap g (rfl : (ζ ≫ Scheme.Opens.ι _) ≫ g = _)) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI := IsCurveOver.isIntegral k X
  haveI := IsCurveOver.isLocallyNoetherian k X
  haveI := IsCurveOver.isIntegral Ω X'
  haveI := IsCurveOver.isLocallyNoetherian Ω X'
  have hX := IsCurveOver.isIntegrallyClosed_stalk k X
  have hX' := IsCurveOver.isIntegrallyClosed_stalk Ω X'
  subst hq
  -- nonemptiness of the charts
  haveI hVV : Nonempty ((g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ U' : X'.Opens) : Scheme.{u}) :=
    ⟨ζ.base (Classical.arbitrary _)⟩
  obtain ⟨y⟩ := hVV
  haveI : Nonempty ((U ⊓ U' : X.Opens) : Scheme.{u}) := ⟨⟨g.base y.1, y.2⟩⟩
  haveI : Nonempty (U : Scheme.{u}) := ⟨⟨g.base y.1, y.2.1⟩⟩
  haveI : Nonempty (U' : Scheme.{u}) := ⟨⟨g.base y.1, y.2.2⟩⟩
  haveI : Nonempty (g ⁻¹ᵁ U : Scheme.{u}) := ⟨⟨y.1, y.2.1⟩⟩
  haveI := connectedSpace_opens_of_isIntegral U
  haveI := connectedSpace_opens_of_isIntegral U'
  haveI := connectedSpace_opens_of_isIntegral (U ⊓ U')
  haveI := connectedSpace_opens_of_isIntegral (g ⁻¹ᵁ U)
  haveI : IsIso U.ι.fromNormalization :=
    isIso_fromNormalization_of_isIntegrallyClosed U.ι (denseRange_of_isOpenImmersion _) hX
  haveI : IsIso (g ⁻¹ᵁ U).ι.fromNormalization :=
    isIso_fromNormalization_of_isIntegrallyClosed (g ⁻¹ᵁ U).ι
      (denseRange_of_isOpenImmersion _) hX'
  haveI : IsIso (incl₂ U U').fromNormalization :=
    haveI : IsIntegral (U' : Scheme.{u}) := isIntegral_of_isOpenImmersion U'.ι
    isIso_fromNormalization_of_isIntegrallyClosed_opens U' (incl₂ U U')
      (denseRange_of_isOpenImmersion _) hX
  have hI : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ U' ≤ g ⁻¹ᵁ (U ⊓ U') := le_rfl
  have hI₁ : incl₁ (g ⁻¹ᵁ U) (g ⁻¹ᵁ U') ≫ g.resLE U (g ⁻¹ᵁ U) le_rfl =
      g.resLE (U ⊓ U') _ hI ≫ incl₁ U U' := by
    simp [incl₁]
  have hI₂ : incl₂ (g ⁻¹ᵁ U) (g ⁻¹ᵁ U') ≫ g.resLE U' (g ⁻¹ᵁ U') le_rfl =
      g.resLE (U ⊓ U') _ hI ≫ incl₂ U U' := by
    simp [incl₂]
  have hP := fundamentalGroupMap_resLE_bijective g _ _ H (U ⊓ U')
    (IsCurveOver.isAffineOpen_inf k X hU hU') (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ U') rfl ζ
  have hA := fundamentalGroupMap_resLE_bijective g _ _ H U hU (g ⁻¹ᵁ U) rfl
    (ζ ≫ incl₁ (g ⁻¹ᵁ U) (g ⁻¹ᵁ U'))
  have hB := fundamentalGroupMap_resLE_bijective g _ _ H U' hU' (g ⁻¹ᵁ U') rfl
    (ζ ≫ incl₂ (g ⁻¹ᵁ U) (g ⁻¹ᵁ U'))
  have key := fundamentalGroupMap_bijective_of_charts g U U' (g ⁻¹ᵁ U) (g ⁻¹ᵁ U')
    (g.resLE U (g ⁻¹ᵁ U) le_rfl) (g.resLE U' (g ⁻¹ᵁ U') le_rfl) (g.resLE (U ⊓ U') _ hI) hUU'
    (Scheme.Hom.resLE_comp_ι _ _).symm hI₁ hI₂ ζ hP.2
    (fundamentalGroupMap_bijective_of_eq _ rfl _ _ hA)
    (fundamentalGroupMap_bijective_of_eq _ rfl _ _ hB).1
  exact fundamentalGroupMap_bijective_of_eq g (by simp [incl₁]) _ _ key

variable (k Ω) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X]

/-- **INV-2.** For a curve `X` over `k` (algebraically closed, characteristic `0`,
countable), `Ω ⊇ k` algebraically closed, affine opens `U, U'` covering `X` and a geometric point
`ζ` of `X_Ω = X ×_k Ω` over `U ∩ U'`, the projection `X_Ω ⟶ X` induces a bijection
`π₁ᵉᵗ(X_Ω, ζ) → π₁ᵉᵗ(X, ζ)`. -/
theorem fundamentalGroupMap_curve_baseChange_bijective (U U' : X.Opens) (hU : IsAffineOpen U)
    (hU' : IsAffineOpen U') (hUU' : U ⊔ U' = ⊤) {L : Type u} [Field L] [IsSepClosed L]
    (ζ : Spec (.of L) ⟶ ((Limits.pullback.fst (X ↘ Spec (CommRingCat.of k))
      (specAlgebraMap k Ω) ⁻¹ᵁ U ⊓ Limits.pullback.fst (X ↘ Spec (CommRingCat.of k))
      (specAlgebraMap k Ω) ⁻¹ᵁ U' : Scheme.Opens _) : Scheme.{u})) :
    Function.Bijective (fundamentalGroupMap (Limits.pullback.fst _ _)
      (rfl : (ζ ≫ Scheme.Opens.ι _) ≫ Limits.pullback.fst (X ↘ Spec (CommRingCat.of k))
        (specAlgebraMap k Ω) = _)) :=
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  fundamentalGroupMap_bijective_of_isPullback_curve _ _ _
    (IsPullback.of_hasPullback (X ↘ Spec (CommRingCat.of k)) (specAlgebraMap k Ω)) rfl
    U U' hU hU' hUU' ζ

/-- **INV-2, geometric points over the dense open `U ∩ U'`.** -/
theorem fundamentalGroupMap_curve_baseChange_bijective' (U U' : X.Opens) (hU : IsAffineOpen U)
    (hU' : IsAffineOpen U') (hUU' : U ⊔ U' = ⊤) {L : Type u} [Field L] [IsSepClosed L]
    (x : Spec (.of L) ⟶ Limits.pullback (X ↘ Spec (CommRingCat.of k)) (specAlgebraMap k Ω))
    (hx : ∀ z, (x ≫ Limits.pullback.fst _ _).base z ∈ U ⊓ U') :
    Function.Bijective (fundamentalGroupMap (Limits.pullback.fst _ _) (rfl : x ≫ _ = _)) := by
  set g := Limits.pullback.fst (X ↘ Spec (CommRingCat.of k)) (specAlgebraMap k Ω)
  have hr : Set.range x.base ⊆ Set.range (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ U').ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hx z
  exact fundamentalGroupMap_bijective_of_eq g (IsOpenImmersion.lift_fac _ _ hr) _ _
    (fundamentalGroupMap_curve_baseChange_bijective k Ω X U U' hU hU' hUU'
      (IsOpenImmersion.lift _ _ hr))

/-- **INV-2, existence of the base points.** Every curve `X` has a dense open `W` (the
intersection of two affine charts) such that `π₁ᵉᵗ(X_Ω, x) → π₁ᵉᵗ(X, x)` is bijective at every
geometric point `x` of `X_Ω` over `W`. -/
theorem exists_fundamentalGroupMap_curve_baseChange_bijective :
    ∃ W : X.Opens, IsAffineOpen W ∧ ∀ {L : Type u} [Field L] [IsSepClosed L]
      (x : Spec (.of L) ⟶ Limits.pullback (X ↘ Spec (CommRingCat.of k)) (specAlgebraMap k Ω)),
      (∀ z, (x ≫ Limits.pullback.fst _ _).base z ∈ W) →
      Function.Bijective (fundamentalGroupMap (Limits.pullback.fst _ _) (rfl : x ≫ _ = _)) := by
  obtain ⟨⟨U, hU⟩, ⟨U', hU'⟩, hUU'⟩ := IsCurveOver.exists_two_affine_cover k X
  exact ⟨U ⊓ U', IsCurveOver.isAffineOpen_inf k X hU hU', fun x hx =>
    fundamentalGroupMap_curve_baseChange_bijective' k Ω X U U' hU hU' hUU' x hx⟩

end FiniteEtale

end AlgebraicGeometry
