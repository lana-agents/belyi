/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Polynomial.DerivativeSmoothLocus
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.Localization.Basic

/-!
# The affine chart of the polynomial self-map is étale away from the critical points

The polynomial self-map `x ↦ g(x)` of `ℙ¹` is, on the affine chart `𝔸¹ → 𝔸¹`, the map of
coordinate rings `k[Y] → k[X]`, `Y ↦ g(X)`.  This file proves the ring-theoretic heart of the
branch-locus identification (statement **B4c**, issue #108 goal 2): that map is *smooth* (indeed
étale) at every prime of `k[X]` avoiding the derivative `g'(X)`.

The affine chart algebra `k[X]` over `k[Y]` cannot be phrased directly as
`Algebra (Polynomial k) (Polynomial k)` — that clashes with the identity algebra structure — so
the statement is given abstractly for a `k`-algebra `S ≃ₐ[k] k[X]` carrying an `R`-algebra
structure (`R ≃ₐ[k] k[X]`) whose action is `Y ↦ g(X)` (`hstruct`).  In the downstream scheme
threading (still on #108) one instantiates `R = S = Γ(D₊(X₁))` via the chart equivalence
`awayChartEquivOne`, and the `R`-algebra structure is the one supplied by
`AlgebraicGeometry.formallySmooth_stalkMap_iff`.

The proof reduces to the merged ring core `Belyi.smooth_localizationAway_mk_derivative` (issue
#182) by exhibiting `S` as `AdjoinRoot F` over `R`, where `F = C(lc⁻¹)·(g(X) − Y)` is the monic
model of `g(X) − Y`.  Its derivative maps to a unit multiple of `t = g'(X)`, so the smooth locus
transports.
-/

open Polynomial

namespace Belyi

variable {k : Type*} [Field k]

/-- Two `k`-algebra homomorphisms out of an algebra `R` that is `k`-isomorphic to `k[X]` agree as
soon as they agree on the generator `eR.symm X`. -/
private lemma algHom_ext_of_algEquiv_polynomial
    {K A R : Type*} [Field K] [CommRing R] [CommRing A] [Algebra K R] [Algebra K A]
    (eR : R ≃ₐ[K] K[X]) {φ ψ : R →ₐ[K] A} (h : φ (eR.symm X) = ψ (eR.symm X)) : φ = ψ := by
  have hΦ : φ.comp eR.symm.toAlgHom = ψ.comp eR.symm.toAlgHom :=
    Polynomial.algHom_ext (by simpa using h)
  ext r
  obtain ⟨p, rfl⟩ := eR.symm.surjective r
  simpa using DFunLike.congr_fun hΦ p

/-- **B4c ring core (affine chart).**  Let `R, S` be `k`-algebras each `k`-isomorphic to the
polynomial ring `k[X]`, with `S` an `R`-algebra whose structure map is `Y ↦ g(X)` (encoded by
`hstruct` through the chosen isomorphisms `eR, eS`).  If `t : S` corresponds to the derivative
`g'` under `eS`, then the localization of `S` away from `t` is smooth over `R`.

Concretely: the affine chart map `k[Y] → k[X]`, `Y ↦ g(X)`, is smooth away from `g'(X) = 0`. -/
theorem smooth_localizationAway_derivative
    {R S : Type*} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    (eR : R ≃ₐ[k] k[X]) (eS : S ≃ₐ[k] k[X]) (g : k[X]) (hg : 0 < g.natDegree)
    (hstruct : ∀ r : R, eS (algebraMap R S r) = aeval g (eR r))
    {t : S} (ht : eS t = derivative g) :
    Algebra.Smooth R (Localization.Away t) := by
  -- `g ≠ 0` and its leading coefficient is a unit of `k`.
  have hg0 : g ≠ 0 := fun h => by simp [h] at hg
  have hlc : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
  -- `algebraMap k R` is injective (it factors as `eR.symm ∘ C`).
  have hRinj : Function.Injective (algebraMap k R) := by
    intro a b hab
    have h1 : algebraMap k k[X] a = algebraMap k k[X] b := by
      rw [← AlgEquiv.commutes eR a, ← AlgEquiv.commutes eR b, hab]
    rwa [Polynomial.algebraMap_eq, Polynomial.C_injective.eq_iff] at h1
  -- Degree/leading-coefficient bookkeeping for `gR = g.map (algebraMap k R)`.
  have hgRdeg : (g.map (algebraMap k R)).natDegree = g.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hRinj g
  have hgRlc : (g.map (algebraMap k R)).leadingCoeff = algebraMap k R g.leadingCoeff :=
    Polynomial.leadingCoeff_map_of_injective hRinj g
  -- The monic model `F` of `g(X) - Y` in `R[X]`.
  set F : R[X] :=
      C (algebraMap k R (g.leadingCoeff)⁻¹) * (g.map (algebraMap k R) - C (eR.symm X)) with hF_def
  have hLC : (g.map (algebraMap k R) - C (eR.symm X)).leadingCoeff
      = algebraMap k R g.leadingCoeff := by
    have hnd : (g.map (algebraMap k R) - C (eR.symm X)).natDegree = g.natDegree := by
      rw [Polynomial.natDegree_sub_C, hgRdeg]
    have h1 : (g.map (algebraMap k R) - C (eR.symm X)).leadingCoeff
        = (g.map (algebraMap k R) - C (eR.symm X)).coeff g.natDegree := by
      rw [← hnd]; rfl
    rw [h1, Polynomial.coeff_sub, Polynomial.coeff_C, if_neg hg.ne', sub_zero, ← hgRdeg]
    exact hgRlc
  have hFmonic : Polynomial.Monic F := by
    rw [hF_def]
    refine Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    rw [hLC, ← map_mul, inv_mul_cancel₀ hlc, map_one]
  -- Evaluation points corresponding to `X` on either side.
  have hex : eS (eS.symm X) = X := eS.apply_symm_apply X
  have herX : eR (eR.symm X) = X := eR.apply_symm_apply X
  -- `g` evaluated at `x = eS.symm X` matches the image of the generator `ρ = eR.symm X`.
  have hxg : Polynomial.aeval (eS.symm X) g = algebraMap R S (eR.symm X) := by
    apply eS.injective
    rw [hstruct (eR.symm X), ← Polynomial.aeval_algHom_apply, hex, herX,
      Polynomial.aeval_X_left_apply, Polynomial.aeval_X]
  -- `F` vanishes at `x`.
  have haev : Polynomial.aeval (eS.symm X) F = 0 := by
    rw [hF_def, map_mul, map_sub, Polynomial.aeval_C, Polynomial.aeval_C,
      Polynomial.aeval_map_algebraMap, hxg, sub_self, mul_zero]
  -- The lift `AdjoinRoot F →ₐ[R] S`, `root F ↦ x`.
  let Ψ₀ : AdjoinRoot F →ₐ[R] S := AdjoinRoot.liftAlgHom F (Algebra.ofId R S) (eS.symm X) haev
  have hΨroot : Ψ₀ (AdjoinRoot.root F) = eS.symm X :=
    AdjoinRoot.liftAlgHom_root F (Algebra.ofId R S) (eS.symm X) haev
  have hΨof : ∀ r : R, Ψ₀ (AdjoinRoot.of F r) = algebraMap R S r :=
    fun r => AdjoinRoot.liftAlgHom_of F (Algebra.ofId R S) (eS.symm X) haev r
  have hΨmk : ∀ q : R[X], Ψ₀ (AdjoinRoot.mk F q) = Polynomial.aeval (eS.symm X) q :=
    fun q => AdjoinRoot.liftAlgHom_mk F (Algebra.ofId R S) (eS.symm X) haev q
  -- Key identity: `g` evaluated at `root F` equals the image of `ρ` in `AdjoinRoot F`.
  have hbc : (C (algebraMap k R (g.leadingCoeff)⁻¹) : R[X]) * C (algebraMap k R g.leadingCoeff)
      = 1 := by
    rw [← C_mul, ← map_mul, inv_mul_cancel₀ hlc, map_one, C_1]
  have haux0 : Polynomial.aeval (AdjoinRoot.root F) g = AdjoinRoot.of F (eR.symm X) := by
    have hdvd : F ∣ (g.map (algebraMap k R) - C (eR.symm X)) := by
      refine ⟨C (algebraMap k R g.leadingCoeff), ?_⟩
      rw [hF_def, mul_right_comm, hbc, one_mul]
    have key : AdjoinRoot.mk F (g.map (algebraMap k R)) = AdjoinRoot.mk F (C (eR.symm X)) :=
      AdjoinRoot.mk_eq_mk.mpr hdvd
    rw [← Polynomial.aeval_map_algebraMap R, AdjoinRoot.aeval_eq, key]
    rfl
  -- The two `k`-algebra homs `R → AdjoinRoot F`, `r ↦ aeval (root F) (aeval g (eR r))` and
  -- `algebraMap R (AdjoinRoot F)`, coincide.
  have hcond : (Polynomial.aeval (AdjoinRoot.root F)).comp
        ((Polynomial.aeval g).comp eR.toAlgHom) (eR.symm X)
      = IsScalarTower.toAlgHom k R (AdjoinRoot F) (eR.symm X) := by
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, herX, Polynomial.aeval_X,
      haux0, IsScalarTower.toAlgHom_apply, AdjoinRoot.algebraMap_eq]
  have haux1 : ∀ r : R, Polynomial.aeval (AdjoinRoot.root F) (Polynomial.aeval g (eR r))
      = AdjoinRoot.of F r := by
    intro r
    have h := DFunLike.congr_fun (algHom_ext_of_algEquiv_polynomial eR hcond) r
    simpa [IsScalarTower.toAlgHom_apply, AdjoinRoot.algebraMap_eq] using h
  -- A left inverse of `Ψ₀`, hence `Ψ₀` is injective.
  let σ : S →+* AdjoinRoot F :=
    (Polynomial.aeval (AdjoinRoot.root F) : k[X] →ₐ[k] AdjoinRoot F).toRingHom.comp
      (eS : S ≃ₐ[k] k[X]).toRingHom
  have hσ : ∀ s : S, σ s = Polynomial.aeval (AdjoinRoot.root F) (eS s) := fun s => rfl
  have hσΨ : σ.comp Ψ₀.toRingHom = RingHom.id (AdjoinRoot F) := by
    apply AdjoinRoot.ringHom_ext
    · refine RingHom.ext fun r => ?_
      simp only [RingHom.comp_apply, RingHom.id_comp, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      rw [hΨof, hσ, hstruct r]
      exact haux1 r
    · simp only [RingHom.comp_apply, RingHom.id_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom]
      rw [hΨroot, hσ, hex, Polynomial.aeval_X]
  have hinj : Function.Injective Ψ₀ := by
    have hli : Function.LeftInverse σ Ψ₀ := fun z => by
      have hz := DFunLike.congr_fun hσΨ z
      simpa using hz
    exact hli.injective
  -- `Ψ₀` is surjective: `x` generates `S` over `k`.
  have hmap : ∀ q : k[X], Ψ₀ (Polynomial.aeval (AdjoinRoot.root F) q)
      = Polynomial.aeval (eS.symm X) q := by
    intro q
    rw [← hΨroot]
    exact (Polynomial.aeval_algHom_apply (Ψ₀.restrictScalars k) (AdjoinRoot.root F) q).symm
  have hsurj : Function.Surjective Ψ₀ := by
    have hadj : Algebra.adjoin k ({eS.symm X} : Set S) = ⊤ := by
      rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
      intro s
      refine ⟨eS s, ?_⟩
      rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_X_left_apply, AlgEquiv.symm_apply_apply]
    intro s
    have hs : s ∈ Algebra.adjoin k ({eS.symm X} : Set S) := by rw [hadj]; exact Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hs
    obtain ⟨q, hq⟩ := hs
    exact ⟨Polynomial.aeval (AdjoinRoot.root F) q, by rw [hmap]; exact hq⟩
  -- The `R`-algebra isomorphism `AdjoinRoot F ≃ₐ[R] S`.
  let Ψ : AdjoinRoot F ≃ₐ[R] S := AlgEquiv.ofBijective Ψ₀ ⟨hinj, hsurj⟩
  -- The derivative of `F` and its image under `Ψ`.
  have hderF : derivative F
      = C (algebraMap k R (g.leadingCoeff)⁻¹) * derivative (g.map (algebraMap k R)) := by
    rw [hF_def, Polynomial.derivative_C_mul, Polynomial.derivative_sub, Polynomial.derivative_C,
      sub_zero]
  have htder : Polynomial.aeval (eS.symm X) (derivative g) = t := by
    apply eS.injective
    rw [← Polynomial.aeval_algHom_apply, hex, Polynomial.aeval_X_left_apply, ht]
  have hΨw : Ψ₀ (AdjoinRoot.mk F (derivative F))
      = algebraMap R S (algebraMap k R (g.leadingCoeff)⁻¹) * t := by
    rw [hΨmk, hderF, map_mul, Polynomial.aeval_C, Polynomial.derivative_map,
      Polynomial.aeval_map_algebraMap, htder]
  -- `Ψ (mk F (derivative F))` is a unit multiple of `t`, hence associated to it.
  have hu : IsUnit (algebraMap R S (algebraMap k R (g.leadingCoeff)⁻¹)) :=
    ((isUnit_iff_ne_zero.mpr (inv_ne_zero hlc)).map (algebraMap k R)).map (algebraMap R S)
  have hΨweq : Ψ (AdjoinRoot.mk F (derivative F))
      = algebraMap R S (algebraMap k R (g.leadingCoeff)⁻¹) * t := hΨw
  have hassoc : Associated (Ψ (AdjoinRoot.mk F (derivative F))) t := by
    rw [hΨweq]
    exact associated_unit_mul_left t _ hu
  -- Transport smoothness of `Localization.Away (mk F (derivative F))` (issue #182).
  haveI hsm : Algebra.Smooth R (Localization.Away (AdjoinRoot.mk F (derivative F))) :=
    smooth_localizationAway_mk_derivative hFmonic
  haveI hawayt : IsLocalization.Away t (Localization.Away (Ψ (AdjoinRoot.mk F (derivative F)))) :=
    IsLocalization.Away.of_associated hassoc
  haveI hawayΨ : IsLocalization.Away (Ψ.toAlgHom (AdjoinRoot.mk F (derivative F)))
      (Localization.Away (Ψ (AdjoinRoot.mk F (derivative F)))) :=
    (inferInstance : IsLocalization.Away (Ψ (AdjoinRoot.mk F (derivative F))) _)
  let e1 : Localization.Away (AdjoinRoot.mk F (derivative F))
      ≃ₐ[R] Localization.Away (Ψ (AdjoinRoot.mk F (derivative F))) :=
    AlgEquiv.ofBijective
      (IsLocalization.Away.mapₐ (Localization.Away (AdjoinRoot.mk F (derivative F)))
        (Localization.Away (Ψ (AdjoinRoot.mk F (derivative F)))) Ψ.toAlgHom
        (AdjoinRoot.mk F (derivative F)))
      ⟨IsLocalization.Away.mapₐ_injective_of_injective _ Ψ.injective,
       IsLocalization.Away.mapₐ_surjective_of_surjective _ Ψ.surjective⟩
  let e2 : Localization.Away (Ψ (AdjoinRoot.mk F (derivative F))) ≃ₐ[R] Localization.Away t :=
    (IsLocalization.algEquiv (Submonoid.powers t)
        (Localization.Away (Ψ (AdjoinRoot.mk F (derivative F))))
        (Localization.Away t)).restrictScalars R
  exact Algebra.Smooth.of_equiv (e1.trans e2)

/-- The smooth-locus form of `smooth_localizationAway_derivative`: away from the derivative
`t = g'(X)`, the affine chart algebra `S ≃ k[X]` lies in the smooth locus over `R ≃ k[Y]`. -/
theorem basicOpen_derivative_subset_smoothLocus
    {R S : Type*} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    [Algebra.FinitePresentation R S]
    (eR : R ≃ₐ[k] k[X]) (eS : S ≃ₐ[k] k[X]) (g : k[X]) (hg : 0 < g.natDegree)
    (hstruct : ∀ r : R, eS (algebraMap R S r) = aeval g (eR r))
    {t : S} (ht : eS t = derivative g) :
    (PrimeSpectrum.basicOpen t : Set (PrimeSpectrum S)) ⊆ Algebra.smoothLocus R S := by
  rw [Algebra.basicOpen_subset_smoothLocus_iff_smooth]
  exact smooth_localizationAway_derivative eR eS g hg hstruct ht

end Belyi
