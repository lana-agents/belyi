/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Nilpotent.Lemmas
import Belyi.Definable

/-!
# Descent of `SmoothOfRelativeDimension 1` along a field extension

This file provides the smoothness-of-relative-dimension half of the descent step **B3c**
(taxis #205): if the base change `X₀ ×_{Spec k₀} Spec K` of a scheme `X₀ / k₀` along a field
extension `k₀ ⊆ K` is smooth of relative dimension `1` over `K`, then `X₀` is smooth of relative
dimension `1` over `k₀`.

The general `MorphismProperty.DescendsAlong (@SmoothOfRelativeDimension 1)` instance is a genuine
mathlib gap. Instead we prove the field-specific statement by the *forward* argument: `Smooth`
descends for free along the faithfully-flat cover, and on each affine chart of `X₀` the relative
dimension is pinned to `1` by a rank computation for Kähler differentials, transported across the
base change `A ↦ K ⊗[k₀] A`.

## Main results

* `Belyi.smoothOfRelativeDimension_of_baseChange`: the headline descent statement.
-/

universe u

open CategoryTheory Limits MorphismProperty AlgebraicGeometry TensorProduct

namespace Belyi

/-- **Base change of the relative dimension** (pure algebra core). If `A` is a nontrivial
`k`-standard-smooth algebra and its base change `K ⊗[k] A` is standard smooth of relative
dimension `1` over `K`, then `A` is standard smooth of relative dimension `1` over `k`.

The two relative dimensions are read off as ranks of Kähler differentials, and the ranks agree
because `Ω[(K ⊗[k] A)⁄K] ≃ (K ⊗[k] A) ⊗[A] Ω[A⁄k]` is the base change of `Ω[A⁄k]`. -/
private lemma issrd_one_of_baseChange {k K A : Type u} [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] [Nontrivial A] [Algebra.IsStandardSmooth k A]
    (h : Algebra.IsStandardSmoothOfRelativeDimension 1 K (K ⊗[k] A)) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 k A := by
  letI : Algebra A (K ⊗[k] A) := Algebra.TensorProduct.rightAlgebra
  haveI : Algebra.IsStandardSmooth K (K ⊗[k] A) := Algebra.IsStandardSmooth.baseChange _
  haveI : Nontrivial (K ⊗[k] A) := inferInstance
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth 1] at h ⊢
  have e : (K ⊗[k] A) ⊗[A] Ω[A⁄k] ≃ₗ[K ⊗[k] A] Ω[(K ⊗[k] A)⁄K] :=
    KaehlerDifferential.tensorKaehlerEquiv k K A (K ⊗[k] A)
  have hb : Module.rank (K ⊗[k] A) ((K ⊗[k] A) ⊗[A] Ω[A⁄k])
      = Cardinal.lift.{u, u} (Module.rank A Ω[A⁄k]) := Module.rank_baseChange
  rw [← e.rank_eq, hb, Cardinal.lift_id] at h
  exact h

/-- **Upgrading a local relative-dimension bound to a global one.** If the structure map
`K → B` is *locally* standard smooth of relative dimension `1` (i.e. after localizing at a cover)
and `B` is already `K`-standard-smooth (so `Ω[B⁄K]` is free), then `B` is standard smooth of
relative dimension `1` over `K`.

The rank of the free module `Ω[B⁄K]` is computed at one nontrivial localization `B_t` (found from
the cover, using that `B` is nontrivial), where it equals `1`; localization of a free module
preserves the rank. -/
private lemma issrd_one_of_locally {K B : Type u} [Field K] [CommRing B] [Algebra K B]
    [Nontrivial B] [Algebra.IsStandardSmooth K B]
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap K B)) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 K B := by
  obtain ⟨s, hspan, hs⟩ := h
  have hex : ∃ t ∈ s, ¬ IsNilpotent t := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hsub : (s : Set B) ⊆ (nilradical B : Set B) := fun t ht => hcon t ht
    have hle : Ideal.span s ≤ nilradical B := Ideal.span_le.mpr hsub
    rw [hspan, top_le_iff] at hle
    have h1 : (1 : B) ∈ nilradical B := by rw [hle]; trivial
    obtain ⟨n, hn⟩ := (mem_nilradical.mp h1)
    simp at hn
  obtain ⟨t, hts, htnil⟩ := hex
  haveI : Nontrivial (Localization.Away t) := by
    rw [← not_subsingleton_iff_nontrivial,
      IsLocalization.subsingleton_iff (M := Submonoid.powers t), Submonoid.mem_powers_iff]
    exact htnil
  have hP := hs t hts
  rw [← IsScalarTower.algebraMap_eq K B (Localization.Away t),
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hP
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 K (Localization.Away t) := hP
  haveI : Algebra.IsStandardSmooth K (Localization.Away t) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth 1]
  have hrk1 : Module.rank (Localization.Away t) Ω[(Localization.Away t)⁄K] = 1 :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 1
  have hloc : Cardinal.lift.{u, u} (Module.rank (Localization.Away t) Ω[(Localization.Away t)⁄K])
      = Cardinal.lift.{u, u} (Module.rank B Ω[B⁄K]) :=
    Module.lift_rank_of_isLocalizedModule_of_free _ (Submonoid.powers t)
      (KaehlerDifferential.map K K B (Localization.Away t))
  rw [hrk1, Cardinal.lift_one, Cardinal.lift_id] at hloc
  exact hloc.symm

variable {k₀ K : Type u} [Field k₀] [Field K] [Algebra k₀ K]

/-- **Base change of an open-immersion restriction of `f₀`.** The base change along
`specAlgebraMap k₀ K` of `hV.fromSpec ≫ f₀` (an affine chart of `X₀` composed into the structure
morphism) is smooth of relative dimension `1`, being an open-immersion restriction of the base
change of `f₀`. -/
private lemma smoothOfRelativeDimension_pullback_snd_fromSpec {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (CommRingCat.of k₀)) {V : X₀.Opens} (hV : IsAffineOpen V)
    (h : SmoothOfRelativeDimension 1 (pullback.snd f₀ (specAlgebraMap k₀ K))) :
    SmoothOfRelativeDimension 1
      (pullback.snd (hV.fromSpec ≫ f₀) (specAlgebraMap k₀ K)) := by
  set g := specAlgebraMap k₀ K
  set j := hV.fromSpec with hj
  haveI : IsOpenImmersion j := hV.isOpenImmersion_fromSpec
  set i₀ : pullback j (pullback.fst f₀ g) ⟶ pullback f₀ g :=
    pullback.snd j (pullback.fst f₀ g) with hi₀
  haveI : IsOpenImmersion i₀ := inferInstance
  have hkey : (pullbackRightPullbackFstIso f₀ g j).hom ≫ pullback.snd (j ≫ f₀) g
      = i₀ ≫ pullback.snd f₀ g := pullbackRightPullbackFstIso_hom_snd f₀ g j
  have hcomp : SmoothOfRelativeDimension 1 (i₀ ≫ pullback.snd f₀ g) :=
    HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension 1) i₀ _ h
  rw [← hkey] at hcomp
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1)
    (pullbackRightPullbackFstIso f₀ g j).hom _).mp hcomp

/-- **Per-chart step.** On an affine chart `V` of `X₀` on which the structure map is standard
smooth (an ordinary smoothness chart), the relative dimension is pinned to `1`. -/
private lemma chart_issrd_one {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (CommRingCat.of k₀)) {V : X₀.Opens} (hV : IsAffineOpen V) [Nonempty V]
    (e : V ≤ f₀ ⁻¹ᵁ ⊤) (hss : (f₀.appLE ⊤ V e).hom.IsStandardSmooth)
    (h : SmoothOfRelativeDimension 1 (pullback.snd f₀ (specAlgebraMap k₀ K))) :
    RingHom.IsStandardSmoothOfRelativeDimension 1 (f₀.appLE ⊤ V e).hom := by
  -- The ring isomorphism `k₀ ≅ Γ(Spec k₀, ⊤)`.
  letI eqk₀ : (CommRingCat.of k₀) ≃+* ↑Γ(Spec (CommRingCat.of k₀), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k₀)).symm.commRingCatIsoToRingEquiv
  -- The affine chart ring `A = Γ(X₀, V)`, a `k₀`-algebra via the chart map precomposed with `eqk₀`.
  letI A : Type u := ↑Γ(X₀, V)
  letI algA : Algebra k₀ A :=
    ((f₀.appLE ⊤ V e).hom.comp eqk₀.toRingHom).toAlgebra
  haveI : Algebra.IsStandardSmooth k₀ A :=
    RingHom.isStandardSmooth_respectsIso.2 (f₀.appLE ⊤ V e).hom eqk₀ hss
  haveI : Nontrivial A := Scheme.component_nontrivial X₀ V
  -- `★`: the chart map identifies with `hV.fromSpec ≫ f₀`.
  have hstar : hV.fromSpec ≫ f₀
      = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k₀)).inv ≫ f₀.appLE ⊤ V e) := by
    rw [Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec f₀ (isAffineOpen_top _) hV e,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  -- The crux base-change / open-immersion fact.
  have hcrux : SmoothOfRelativeDimension 1
      (pullback.snd (hV.fromSpec ≫ f₀) (specAlgebraMap k₀ K)) :=
    smoothOfRelativeDimension_pullback_snd_fromSpec f₀ hV h
  -- Transport `hcrux` across `pullbackSpecIso` to `Locally (ISSRD 1) (algebraMap K (K ⊗[k₀] A))`.
  set mA : Spec Γ(X₀, V) ⟶ Spec (CommRingCat.of k₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap k₀ A)) with hmAdef
  have hmA : hV.fromSpec ≫ f₀ = mA := hstar
  rw [hmA] at hcrux
  have hfst : SmoothOfRelativeDimension 1 (pullback.fst (specAlgebraMap k₀ K) mA) := by
    rw [show pullback.snd mA (specAlgebraMap k₀ K)
      = (pullbackSymmetry mA (specAlgebraMap k₀ K)).hom
          ≫ pullback.fst (specAlgebraMap k₀ K) mA from
      (pullbackSymmetry_hom_comp_fst mA (specAlgebraMap k₀ K)).symm] at hcrux
    exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) _ _).mp hcrux
  have hgoalSpec : SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k₀] A)))) := by
    rw [show Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k₀] A)))
        = (pullbackSpecIso k₀ K A).inv ≫ pullback.fst (specAlgebraMap k₀ K) mA from
      (pullbackSpecIso_inv_fst k₀ K A).symm]
    exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) _ _).mpr hfst
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap K (K ⊗[k₀] A)) :=
    (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mp hgoalSpec
  -- Upgrade to `ISSRD 1 K (K ⊗[k₀] A)`, then descend to `ISSRD 1 k₀ A`.
  haveI : Nontrivial (K ⊗[k₀] A) := inferInstance
  haveI : Algebra.IsStandardSmooth K (K ⊗[k₀] A) := Algebra.IsStandardSmooth.baseChange _
  have hKB : Algebra.IsStandardSmoothOfRelativeDimension 1 K (K ⊗[k₀] A) :=
    issrd_one_of_locally hloc
  have hcore : Algebra.IsStandardSmoothOfRelativeDimension 1 k₀ A :=
    issrd_one_of_baseChange hKB
  -- Transport `ISSRD 1 k₀ A` back to the chart ring map via `eqk₀`.
  have htrans := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 1)).2
    (algebraMap k₀ A) eqk₀.symm hcore
  have hfinal : (algebraMap k₀ A).comp eqk₀.symm.toRingHom = (f₀.appLE ⊤ V e).hom := by
    ext x
    simp [algA, RingHom.algebraMap_toAlgebra]
  rw [hfinal] at htrans
  exact htrans

/-- **Descent of `SmoothOfRelativeDimension 1` along a field extension** (B3c, taxis #205).
If the base change of `X₀ / k₀` along a field extension `k₀ ⊆ K` is smooth of relative dimension
`1` over `K`, then `X₀` is smooth of relative dimension `1` over `k₀`. -/
theorem smoothOfRelativeDimension_of_baseChange {X₀ : Scheme.{u}}
    [X₀.Over (Spec (CommRingCat.of k₀))]
    (h : SmoothOfRelativeDimension 1
      (pullback.snd (X₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K))) :
    SmoothOfRelativeDimension 1 (X₀ ↘ Spec (CommRingCat.of k₀)) := by
  set f₀ := X₀ ↘ Spec (CommRingCat.of k₀) with hf₀
  haveI : SmoothOfRelativeDimension 1 (pullback.snd f₀ (specAlgebraMap k₀ K)) := h
  -- Step 1: `Smooth f₀` descends for free along the faithfully-flat cover.
  haveI hsmf₀ : Smooth f₀ := by
    have hsm : Smooth (pullback.snd f₀ (specAlgebraMap k₀ K)) :=
      SmoothOfRelativeDimension.smooth 1 _
    exact of_pullback_snd_of_descendsAlong
      (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}))
      (g := specAlgebraMap k₀ K) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsm
  rw [smoothOfRelativeDimension_iff]
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hss⟩ := Smooth.exists_isStandardSmooth f₀ x
  -- The base is `Spec` of a field, so its only nonempty affine open is `⊤`.
  obtain rfl : U = ⊤ := by
    have hsub : Subsingleton ↥(Spec (CommRingCat.of k₀)) := inferInstance
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun p => ?_)
    rw [Subsingleton.elim p (f₀.base x)]
    exact e hx
  haveI : Nonempty V := ⟨⟨x, hx⟩⟩
  exact ⟨⊤, hU, V, hV, hx, e, chart_issrd_one f₀ hV e hss h⟩

end Belyi
