/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.PolynomialMapImage
import Belyi.Polynomial.ChartEtale
import Belyi.Ramification

/-!
# B4c (branch locus): the polynomial self-map is étale at affine non-critical points

For a non-constant `g : k[X]` the self-map `Belyi.P1.polynomialSelfMap g : ℙ¹ ⟶ ℙ¹`
(realizing `x ↦ g(x)` on the affine chart `D₊(X₁)`, taxis issue #106) is *smooth* (indeed
étale) at every affine closed point `[a : 1]` with `g'(a) ≠ 0`. Equivalently such a point does
not lie in the ramification locus `Ram (polynomialSelfMap g)`.

This is the scheme-level per-point half of statement **B4c** goal 2 (taxis issue #108): it
threads the merged abstract ring bridge `Belyi.basicOpen_derivative_subset_smoothLocus`
(`Belyi/Polynomial/ChartEtale.lean`, issue #30) through the source chart `D₊(X₁)`.

## Main results

* `Belyi.P1.mem_smoothLocus_polynomialSelfMap`: `[a : 1] ∈ (polynomialSelfMap g).smoothLocus`
  when `g'(a) ≠ 0`.
* `Belyi.P1.point_notMem_ram_polynomialSelfMap`: the ramification-locus phrasing.

The remaining B4c goal-2 work — the closed-point classification of `ℙ¹` over an algebraically
closed field (every ramification point is affine or `∞`), and the assembled inclusion
`Branch (polynomialSelfMap g) ⊆ {[g(a):1] : g'(a) = 0} ∪ {∞}` — is follow-up on issue #108.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open scoped Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (g : k[X]) (hd : 0 < g.natDegree)

noncomputable local instance instLOFP_polynomialSelfMap :
    LocallyOfFinitePresentation (polynomialSelfMap k g hd) :=
  locallyOfFinitePresentation_polynomialSelfMap k g hd

/-- Two `k`-algebra homomorphisms out of the affine chart ring `(k[X₀,X₁]_{X₁})₀` agree as soon
as they agree on the affine coordinate `X₀/X₁` (which is the generator of the chart ring, mapping
to `Polynomial.X` under `awayChartEquivOne`). -/
private lemma algHom_ext_affineCoord {A : Type u} [CommRing A] [Algebra k A]
    {φ ψ : Away (P1Grading k) (X 1 : MvPolynomial (Fin 2) k) →ₐ[k] A}
    (h : φ (affineCoord k) = ψ (affineCoord k)) : φ = ψ := by
  have hsymm : (awayChartEquivOne k).symm (Polynomial.X) = affineCoord k := by
    rw [AlgEquiv.symm_apply_eq]
    exact (awayChartEquivOne_affineCoord k).symm
  have hΦ : φ.comp (awayChartEquivOne k).symm.toAlgHom
      = ψ.comp (awayChartEquivOne k).symm.toAlgHom := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, hsymm]
    exact h
  ext r
  obtain ⟨p, rfl⟩ := (awayChartEquivOne k).symm.surjective r
  have := DFunLike.congr_fun hΦ p
  simpa using this

/-- The affine-chart form of the ring-theoretic core: for `k`-algebras `R, S` each `k`-isomorphic
to `k[X]` with the `R`-algebra structure on `S` given by `Y ↦ g(X)`, the composite ring map
`R → S → Sₜ` (localizing away the derivative `t = g'`) is smooth. This packages
`Belyi.smooth_localizationAway_derivative` as a `RingHom.Smooth` statement, ready to be transported
through `Spec`. -/
theorem smooth_specMap_comp_localizationAway_derivative
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra R S]
    (hcom : ∀ c : k, algebraMap R S (algebraMap k R c) = algebraMap k S c)
    (eR : R ≃ₐ[k] Polynomial k) (eS : S ≃ₐ[k] Polynomial k) (g : Polynomial k)
    (hg : 0 < g.natDegree)
    (hstruct : ∀ r : R, eS (algebraMap R S r) = Polynomial.aeval g (eR r))
    {t : S} (ht : eS t = Polynomial.derivative g) :
    RingHom.Smooth ((algebraMap S (Localization.Away t)).comp (algebraMap R S)) := by
  haveI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq fun c => (hcom c).symm
  have hsm : Algebra.Smooth R (Localization.Away t) :=
    Belyi.smooth_localizationAway_derivative eR eS g hg hstruct ht
  rw [← IsScalarTower.algebraMap_eq R S (Localization.Away t)]
  exact RingHom.smooth_algebraMap.mpr hsm

set_option backward.isDefEq.respectTransparency false in
/-- **B4c (affine non-critical points are smooth).** The polynomial self-map `x ↦ g(x)` of `ℙ¹`
is smooth at the affine closed point `[a : 1]` whenever the derivative `g'(a)` is nonzero. -/
theorem mem_smoothLocus_polynomialSelfMap (a : k)
    (ha : Polynomial.aeval a (Polynomial.derivative g) ≠ 0) :
    point k a (IsLocalRing.closedPoint k) ∈ (polynomialSelfMap k g hd).smoothLocus := by
  classical
  -- Affine coordinate of the image and the derivative locus.
  set s : Away (P1Grading k) (X 1) := Polynomial.aeval (affineCoord k) g with hs_def
  set t : Away (P1Grading k) (X 1) :=
    (awayChartEquivOne k).symm (Polynomial.derivative g) with ht_def
  -- The source chart point `x'` under `Spec k → Spec (chart ring)`.
  set x' := (Spec.map (CommRingCat.ofHom (awayEval k a))).base (IsLocalRing.closedPoint k)
    with hx'_def
  -- **Step A.** The point factors through the source chart `D₊(X₁)`.
  have hpt : point k a (IsLocalRing.closedPoint k) =
      (Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos).base x' := by
    rw [point, Scheme.Hom.comp_apply]
    rfl
  rw [hpt]
  -- **Step B.** Reduce to the composite `ι ≫ f` on the source chart.
  suffices h : x' ∈ (Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos) ⁻¹ᵁ
      (polynomialSelfMap k g hd).smoothLocus from h
  rw [Scheme.Hom.preimage_smoothLocus_eq]
  -- **Step C.** `ι ≫ f = point k s = Spec.map (awayEval k s) ≫ ι`.
  have hchart : Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos ≫
      polynomialSelfMap k g hd = point k s := ι_polynomialSelfMap k g hd false
  have hcomp : Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos ≫
      polynomialSelfMap k g hd = Spec.map (CommRingCat.ofHom (awayEval k s)) ≫
        Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos := by
    rw [hchart, point]
  -- Finite presentation of the affine chart map, to feed the smooth-locus lemmas.
  haveI hft_k : Algebra.FiniteType k (Away (P1Grading k) (X 1)) := finiteType_away k
  haveI hlofp_phi :
      LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (awayEval k s))) := by
    rw [LocallyOfFinitePresentation.SpecMap_iff, CommRingCat.hom_ofHom]
    refine RingHom.FinitePresentation.of_finiteType.mp ?_
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k (Away (P1Grading k) (X 1)))
    rw [show (awayEval k s).comp (algebraMap k (Away (P1Grading k) (X 1)))
        = algebraMap k (Away (P1Grading k) (X 1)) from
          RingHom.ext fun c => (awayEvalₐ k s).commutes c,
      RingHom.finiteType_algebraMap]
    exact hft_k
  haveI hlofp_point : LocallyOfFinitePresentation (point k s) :=
    locallyOfFinitePresentation_point s
  -- **Step D.** Cancel the target chart open immersion.
  rw [Scheme.Hom.mem_smoothLocus, hcomp, ← Scheme.Hom.mem_smoothLocus,
    Belyi.smoothLocus_comp_of_isOpenImmersion]
  -- Goal: `x' ∈ (Spec.map (awayEval k s)).smoothLocus`.
  -- **Step E.** Smoothness of the affine chart map away from `t = g'`, via localization.
  -- The `R`-algebra structure `Y ↦ g(X)` on the chart ring; kept out of the ambient instance
  -- cache (passed explicitly below) to avoid polluting `Algebra … (Localization.Away t)`.
  have hstruct : ∀ r : Away (P1Grading k) (X 1),
      awayChartEquivOne k (awayEval k s r) = Polynomial.aeval g (awayChartEquivOne k r) := by
    have hcomp2 : (awayChartEquivOne k).toAlgHom.comp (awayEvalₐ k s)
        = (Polynomial.aeval g).comp (awayChartEquivOne k).toAlgHom := by
      apply algHom_ext_affineCoord
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply]
      rw [show awayEvalₐ k s (affineCoord k) = s from awayEval_affineCoord k s, hs_def,
        ← Polynomial.aeval_algHom_apply, awayChartEquivOne_affineCoord,
        Polynomial.aeval_X_left_apply, Polynomial.aeval_X]
    intro r
    have h := DFunLike.congr_fun hcomp2 r
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] at h
    exact h
  have ht_eq : awayChartEquivOne k t = Polynomial.derivative g := by
    rw [ht_def]; exact (awayChartEquivOne k).apply_symm_apply _
  -- Smoothness of the composite ring hom `A → A → Localization.Away t`.
  have hsmoothRing : RingHom.Smooth
      ((algebraMap (Away (P1Grading k) (X 1)) (Localization.Away t)).comp (awayEval k s)) :=
    @smooth_specMap_comp_localizationAway_derivative k _
      (Away (P1Grading k) (X 1)) (Away (P1Grading k) (X 1)) _ _ _ _
      ((awayEvalₐ k s).toRingHom.toAlgebra)
      (fun c => (awayEvalₐ k s).commutes c)
      (awayChartEquivOne k) (awayChartEquivOne k) g hd hstruct t ht_eq
  have hSmoothScheme : Smooth (Spec.map (CommRingCat.ofHom
      ((algebraMap (Away (P1Grading k) (X 1)) (Localization.Away t)).comp (awayEval k s)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth), CommRingCat.hom_ofHom]
    exact hsmoothRing
  have hcompeq : Spec.map (CommRingCat.ofHom
        (algebraMap (Away (P1Grading k) (X 1)) (Localization.Away t)))
        ≫ Spec.map (CommRingCat.ofHom (awayEval k s))
      = Spec.map (CommRingCat.ofHom
        ((algebraMap (Away (P1Grading k) (X 1)) (Localization.Away t)).comp (awayEval k s))) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  haveI hSmoothComp : Smooth (Spec.map (CommRingCat.ofHom
        (algebraMap (Away (P1Grading k) (X 1)) (Localization.Away t)))
        ≫ Spec.map (CommRingCat.ofHom (awayEval k s))) := by
    rw [hcompeq]; exact hSmoothScheme
  -- `awayEval k a t = g'(a) ≠ 0`, so `x'` avoids `t`.
  have hval : awayEval k a t = Polynomial.aeval a (Polynomial.derivative g) := by
    have hcong : awayEvalₐ k a = (Polynomial.aeval a).comp (awayChartEquivOne k).toAlgHom := by
      apply algHom_ext_affineCoord
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, awayChartEquivOne_affineCoord,
        Polynomial.aeval_X]
      exact awayEval_affineCoord k a
    have hrfl : awayEval k a t = awayEvalₐ k a t := rfl
    rw [hrfl, hcong]
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply]
    rw [ht_eq]
  have hxker : x'.asIdeal = RingHom.ker (awayEval k a) := by
    have hbot : (IsLocalRing.closedPoint k).asIdeal = ⊥ := IsLocalRing.maximalIdeal_eq_bot
    change (PrimeSpectrum.comap (awayEval k a) (IsLocalRing.closedPoint k)).asIdeal = _
    rw [PrimeSpectrum.comap_asIdeal, hbot]
    rfl
  have hmem : x' ∈ (Spec.map (CommRingCat.ofHom
      (algebraMap (Away (P1Grading k) (X 1)) (Localization.Away t)))).opensRange := by
    rw [show (Spec.map (CommRingCat.ofHom
          (algebraMap (Away (P1Grading k) (X 1)) (Localization.Away t)))).opensRange
        = PrimeSpectrum.basicOpen t from
        Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (Away (P1Grading k) (X 1))) t,
      PrimeSpectrum.mem_basicOpen, hxker, RingHom.mem_ker, hval]
    exact ha
  obtain ⟨w, hw⟩ := hmem
  have hwmem : w ∈ (Spec.map (CommRingCat.ofHom
      (algebraMap (Away (P1Grading k) (X 1)) (Localization.Away t)))) ⁻¹ᵁ
      (Spec.map (CommRingCat.ofHom (awayEval k s))).smoothLocus := by
    rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top]
    exact TopologicalSpace.Opens.mem_top w
  rw [← hw]
  exact hwmem

/-- The affine closed point `[a : 1]` does not lie in the ramification locus of the polynomial
self-map when `g'(a) ≠ 0`. -/
theorem point_notMem_ram_polynomialSelfMap (a : k)
    (ha : Polynomial.aeval a (Polynomial.derivative g) ≠ 0) :
    point k a (IsLocalRing.closedPoint k) ∉ Ram (polynomialSelfMap k g hd) := by
  rw [Belyi.mem_ram_iff, not_not]
  exact mem_smoothLocus_polynomialSelfMap k g hd a ha

end Belyi.P1
