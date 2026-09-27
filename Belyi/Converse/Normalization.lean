/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Belyi.Curve.SmoothStalk

/-!
# A normal scheme finite over `S` is the normalization of `S` in a dense open (P2a)

Package P2a of `references/converse-rie-design.md`. Let `f : X ⟶ S` be an integral morphism
from an integral scheme `X` all of whose stalks are integrally closed, and let `j : Y ⟶ X` be a
quasi-compact open immersion with dense range. Then `X` is the relative normalization of `S`
in `Y` (via `j ≫ f`): the canonical map `(j ≫ f).normalization ⟶ X` given by the universal
property of the normalization is an isomorphism.

Affine-locally over `S`, with `U ⊆ S` affine, this is the commutative algebra statement: the
sections `A = Γ(X, f⁻¹ U)` form an integrally closed domain (its localizations are stalks of
`X`), `Γ(Y, j⁻¹ f⁻¹ U)` embeds into the fraction field `K(X)` of `A`, and the integral closure of
`Γ(S, U)` in `Γ(Y, j⁻¹ f⁻¹ U)` is contained in the integral closure of `A` in `K(X)`, i.e. in `A`.

## Main results

* `AlgebraicGeometry.isIntegrallyClosed_of_isAffineOpen`: sections of an integral scheme with
  integrally closed stalks over a nonempty affine open are integrally closed.
* `AlgebraicGeometry.isIso_normalizationDesc_of_isIntegrallyClosed`: the general statement.
* `Belyi.isIso_normalizationDesc_of_isCurveOver`: the application to a curve `X` over a perfect
  field with a finite morphism `X ⟶ ℙ¹` and a dense open `Y ⊆ X`.
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The sections of an integral scheme with integrally closed stalks over a nonempty affine
open are an integrally closed domain. -/
theorem isIntegrallyClosed_of_isAffineOpen {X : Scheme.{u}} [IsIntegral X] {W : X.Opens}
    (hW : IsAffineOpen W) [Nonempty W]
    (h : ∀ x ∈ W, IsIntegrallyClosed (X.presheaf.stalk x)) : IsIntegrallyClosed Γ(X, W) := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ _ ↦ ?_
  let y : PrimeSpectrum Γ(X, W) := ⟨p, inferInstance⟩
  have hy : hW.fromSpec y ∈ W := hW.range_fromSpec.subset ⟨y, rfl⟩
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hW.fromSpec y, hy⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk (hW.fromSpec y)) p :=
    hW.isLocalization_stalk' y hy
  haveI := h _ hy
  exact IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv p.primeCompl
    (X.presheaf.stalk (hW.fromSpec y)) (Localization.AtPrime p)).toRingEquiv

/-- The commutative-algebra core of P2a: if `A` is an integrally closed domain with fraction
field `K`, `φ : A → L` is a ring map and `ψ : L → K` is an injective ring map with
`ψ ∘ φ = algebraMap A K`, then any element of `L` integral over some ring `R` (via `φ ∘ ρ`) lies
in the image of `φ`. -/
theorem mem_range_of_isIntegralElem_of_isIntegrallyClosed {R A L K : Type*} [CommRing R]
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing L] [Field K] [Algebra A K]
    [IsFractionRing A K] (ρ : R →+* A) (φ : A →+* L) (ψ : L →+* K)
    (hψ : Function.Injective ψ) (hcomp : ψ.comp φ = algebraMap A K) {t : L}
    (ht : (φ.comp ρ).IsIntegralElem t) : t ∈ φ.range := by
  obtain ⟨p, hp, hpt⟩ := ht
  have hint : _root_.IsIntegral A (ψ t) := by
    refine ⟨p.map ρ, hp.map ρ, ?_⟩
    rw [Polynomial.eval₂_map, ← hcomp, RingHom.comp_assoc, ← Polynomial.hom_eval₂, hpt,
      map_zero]
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨a, hψ ?_⟩
  rw [← ha, ← hcomp, RingHom.comp_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **P2a.** Let `f : X ⟶ S` be an integral morphism from an integral scheme `X` with
integrally closed stalks, and `j : Y ⟶ X` a quasi-compact open immersion with dense range.
Then the canonical map `(j ≫ f).normalization ⟶ X` (from the universal property of the relative
normalization of `S` in `Y`) is an isomorphism, i.e. `X` is the normalization of `S` in `Y`. -/
theorem isIso_normalizationDesc_of_isIntegrallyClosed
    {X S Y : Scheme.{u}} [IsIntegral X] (f : X ⟶ S) [IsIntegralHom f]
    (j : Y ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (hj : DenseRange j.base)
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIso ((j ≫ f).normalizationDesc j f rfl) := by
  set φ := (j ≫ f).normalizationDesc j f rfl with hφ
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := .isomorphisms _)
    fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  refine ⟨f ⁻¹ᵁ U, hxU, (isIso_morphismRestrict_iff_isIso_app _ (hU.preimage f)).mpr ?_⟩
  -- Notation.
  set W : X.Opens := f ⁻¹ᵁ U with hW
  set V : Y.Opens := (j ≫ f) ⁻¹ᵁ U with hV
  set Nw := (j ≫ f).fromNormalization ⁻¹ᵁ U with hNw
  have hφW : φ ⁻¹ᵁ W = Nw := by
    rw [hW, hNw, ← Scheme.Hom.comp_preimage, hφ, Scheme.Hom.normalizationDesc_comp]
  have hVW : V ≤ j ⁻¹ᵁ W := by rw [hV, hW, Scheme.Hom.comp_preimage]
  haveI : Nonempty W := ⟨⟨x, hxU⟩⟩
  obtain ⟨y, hy⟩ := hj.exists_mem_open W.isOpen ⟨x, hxU⟩
  haveI : Nonempty (j ''ᵁ V) := ⟨⟨j y, ⟨y, by simpa [hV, hW] using hy, rfl⟩⟩⟩
  haveI := isIntegrallyClosed_of_isAffineOpen (hU.preimage f) fun x _ ↦ hX x
  have := functionField_isFractionRing_of_isAffineOpen X W (hU.preimage f)
  -- The comparison maps.
  let χ : Γ(X, W) ⟶ Γ((j ≫ f).normalization, Nw) := φ.appLE W Nw hφW.ge
  let ψ : Γ((j ≫ f).normalization, Nw) ⟶ Γ(Y, V) :=
    (j ≫ f).toNormalization.appLE Nw V (by
      rw [hNw, hV, ← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization])
  let κ : Γ(Y, V) ⟶ X.functionField := (j.appIso V).inv ≫ X.germToFunctionField (j ''ᵁ V)
  have hχψ : χ ≫ ψ = j.appLE W V hVW := by
    simp only [χ, ψ, Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact Scheme.Hom.toNormalization_normalizationDesc _ _ _ _
  letI := ((j ≫ f).app U).hom.toAlgebra
  have hψ : ψ = ((j ≫ f).normalizationObjIso hU).hom ≫
      CommRingCat.ofHom (Subalgebra.val _).toRingHom :=
    ((j ≫ f).normalizationObjIso_hom_val hU).symm
  have hκ : j.appLE W V hVW ≫ κ = X.germToFunctionField W := by
    simp only [κ, Scheme.Hom.appLE_appIso_inv_assoc]
    exact X.presheaf.germ_res _ _ _
  have hκinj : Function.Injective κ :=
    (X.germToFunctionField_injective (j ''ᵁ V)).comp
      (j.appIso V).commRingCatIsoToRingEquiv.symm.injective
  have hjinj : Function.Injective (j.appLE W V hVW) := by
    have h := X.germToFunctionField_injective W
    rw [← hκ] at h
    exact Function.Injective.of_comp (f := ⇑κ.hom) h
  have hψinj : Function.Injective ψ := by
    rw [hψ]
    exact Subtype.val_injective.comp
      ((j ≫ f).normalizationObjIso hU).commRingCatIsoToRingEquiv.injective
  have hρ : f.app U ≫ j.appLE W V hVW = (j ≫ f).app U := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE]
  have hbij : Function.Bijective χ := by
    refine ⟨?_, fun s ↦ ?_⟩
    · have h := hjinj
      rw [← hχψ] at h
      exact Function.Injective.of_comp (f := ⇑ψ.hom) h
    · have ht : ψ s ∈ integralClosure Γ(S, U) Γ(Y, V) := by
        rw [hψ]
        exact (((j ≫ f).normalizationObjIso hU).hom s).2
      obtain ⟨a, ha⟩ := mem_range_of_isIntegralElem_of_isIntegrallyClosed (f.app U).hom
        (j.appLE W V hVW).hom κ.hom hκinj (congrArg CommRingCat.Hom.hom hκ)
        (t := ψ s) (by
          rw [← CommRingCat.hom_comp, hρ]
          exact ht)
      refine ⟨a, hψinj ?_⟩
      rw [← ha]
      exact congrArg (fun g ↦ g.hom a) hχψ
  have hχ : IsIso χ := (ConcreteCategory.isIso_iff_bijective χ).mpr hbij
  have e : χ = φ.app W ≫ (j ≫ f).normalization.presheaf.map (eqToHom hφW.symm).op := rfl
  rw [e] at hχ
  exact IsIso.of_isIso_comp_right _ ((j ≫ f).normalization.presheaf.map (eqToHom hφW.symm).op)

end AlgebraicGeometry

namespace Belyi

open AlgebraicGeometry

/-- Every open immersion into a curve is quasi-compact (a curve is Noetherian). -/
theorem quasiCompact_of_isCurveOver (K : Type u) [Field K]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X]
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] : QuasiCompact j := by
  haveI : IsNoetherian X := isNoetherian_of_over X (Spec (CommRingCat.of K))
  infer_instance

/-- **P2a for curves.** Let `X` be a curve over a perfect field `K`, `f : X ⟶ ℙ¹_K` a finite
morphism and `j : Y ⟶ X` an open immersion with dense range. Then `X` is the relative
normalization of `ℙ¹_K` in `Y`: the canonical map `(j ≫ f).normalization ⟶ X` is an
isomorphism. (The stalks of `X` are valuation rings, hence integrally closed.) The
quasi-compactness of `j`, needed to form the normalization, is automatic:
see `Belyi.quasiCompact_of_isCurveOver`. -/
theorem isIso_normalizationDesc_of_isCurveOver (K : Type u) [Field K] [PerfectField K]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X]
    (f : X ⟶ P1 K) [IsFinite f] {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (hj : DenseRange j.base) :
    IsIso ((j ≫ f).normalizationDesc j f rfl) := by
  haveI : IsIntegral X := IsCurveOver.isIntegral K X
  exact isIso_normalizationDesc_of_isIntegrallyClosed f j hj fun x ↦
    haveI := valuationRing_stalk_of_isCurveOver K X x
    inferInstance

end Belyi
