/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Converse.PuncturedLine
import Belyi.BelyiCoverEtale
import Belyi.Curve.Existence

/-!
# The finite étale algebra of a Belyi map

Package (P1) of the converse of Belyi's theorem (`references/converse-rie-design.md`), second
half. For a curve `X` over an algebraically closed field `K` of characteristic zero and a Belyi
map `f : X ⟶ ℙ¹_K`, the restriction of `f` over the thrice-punctured line,
```
Y := X ×_{ℙ¹_K} Spec R_K ⟶ Spec R_K,    R_K = puncturedRing K,
```
is finite étale. Hence `Y` is affine, `Y ≅ Spec B` with `B := Γ(Y, ⊤)`, and `B` is a finite
étale `R_K`-algebra. Moreover `Y ⟶ X` is an open immersion with dense image.

## Main definitions

* `Belyi.puncturedCover f`: the scheme `Y = X ×_{ℙ¹_K} Spec R_K` (`pullback f (puncturedι K)`).
* `Belyi.puncturedCoverRing f`: its ring of global sections `B = Γ(Y, ⊤)`, an
  `R_K`-algebra through `pullback.snd`.

## Main results

* `Belyi.not_subsingleton_of_isCurveOver`: a curve has at least two points.
* `Belyi.isDominant_of_isFinite`: every finite morphism from a curve to `ℙ¹_K` is dominant.
* `Belyi.IsBelyiMap.etale_morphismRestrict_puncturedLine`: a Belyi map is étale over the
  punctured line.
* `Belyi.isFinite_puncturedCover_snd`, `Belyi.etale_puncturedCover_snd`,
  `Belyi.isAffine_puncturedCover`.
* `Belyi.puncturedCoverRing_finite`, `Belyi.puncturedCoverRing_etale`: `B` is a finite étale
  `R_K`-algebra.
* `Belyi.puncturedCover_isoSpec_hom_comp`: `Y ≅ Spec B` over `Spec R_K`.
* `Belyi.denseRange_puncturedCover_fst`: `Y ⟶ X` has dense range.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace Belyi

section Curve

variable (K : Type u) [Field K] [PerfectField K] (X : Scheme.{u})
  [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X]

include K in
/-- **A curve has at least two points**: it admits a surjection onto `ℙ¹`
(`exists_isFinite_surjective_hom_to_P1`), and `0 ≠ 1` in `ℙ¹`. -/
theorem not_subsingleton_of_isCurveOver : ¬ Subsingleton X := by
  intro hX
  obtain ⟨g, -, hsurj, -⟩ := exists_isFinite_surjective_hom_to_P1 K X
  obtain ⟨x₀, hx₀⟩ := hsurj (P1.zero K)
  obtain ⟨x₁, hx₁⟩ := hsurj (P1.one K)
  exact P1.zero_ne_one K (hx₀.symm.trans ((congrArg g.base (Subsingleton.elim x₀ x₁)).trans hx₁))

variable {K X}

/-- **Finite morphisms from a curve to `ℙ¹` are dominant.** Otherwise the generic point of `X`
maps to a closed point `p` of `ℙ¹` (non-generic points of `ℙ¹` are closed), so all of `X` maps
to `p`; the fibre of the finite (hence quasi-finite) morphism over `p` is discrete, so `X` would
be an irreducible discrete space, i.e. a point, contradicting
`not_subsingleton_of_isCurveOver`. -/
theorem isDominant_of_isFinite (f : X ⟶ P1 K) [IsFinite f] : IsDominant f := by
  haveI : IsIntegral X := IsCurveOver.isIntegral K X
  have hgen : f.base (genericPoint X) = genericPoint (P1 K) := by
    by_contra hne
    have hcl : IsClosed ({f.base (genericPoint X)} : Set (P1 K)) :=
      isClosed_singleton_of_ne_genericPoint (fun z => P1.krullDimLE_one_stalk_P1 K z) hne
    have hall : ∀ x : X, f.base x = f.base (genericPoint X) := by
      intro x
      have hx : x ∈ closure ({genericPoint X} : Set X) := by
        rw [(genericPoint_spec X).def]; trivial
      have := image_closure_subset_closure_image (f := f.base) f.base.hom.continuous
        (Set.mem_image_of_mem _ hx)
      rwa [Set.image_singleton, hcl.closure_eq] at this
    have hdisc := f.isDiscrete_preimage_singleton (f.base (genericPoint X))
    have huniv : f.base ⁻¹' {f.base (genericPoint X)} = Set.univ :=
      Set.eq_univ_of_forall fun x => hall x
    rw [huniv] at hdisc
    have hopen : ∀ x : X, IsOpen ({x} : Set X) := by
      intro x
      haveI := hdisc.to_subtype
      have h1 : IsOpen ({⟨x, trivial⟩} : Set (Set.univ : Set X)) := isOpen_discrete _
      have h2 := (Homeomorph.Set.univ X).isOpenMap _ h1
      simpa using h2
    refine not_subsingleton_of_isCurveOver K X ⟨fun x y => ?_⟩
    obtain ⟨z, -, hzx, hzy⟩ := (IrreducibleSpace.isIrreducible_univ X).isPreirreducible _ _
      (hopen x) (hopen y) ⟨x, trivial, rfl⟩ ⟨y, trivial, rfl⟩
    exact (Set.mem_singleton_iff.mp hzx).symm.trans (Set.mem_singleton_iff.mp hzy)
  refine ⟨denseRange_iff_closure_range.mpr (Set.eq_univ_of_univ_subset ?_)⟩
  rw [← (genericPoint_spec (P1 K)).def, ← hgen]
  exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self _))

end Curve

section General

variable {K : Type u} [Field K] {X : Scheme.{u}} {f : X ⟶ P1 K}

variable (f) in
/-- The part `Y = X ×_{ℙ¹_K} Spec R_K` of `X` over the thrice-punctured line. -/
noncomputable abbrev puncturedCover : Scheme.{u} :=
  pullback f (puncturedι K)

variable (f) in
/-- The ring of global sections `B = Γ(Y, ⊤)` of the part of `X` over the punctured line. -/
abbrev puncturedCoverRing : Type u :=
  Γ(puncturedCover f, ⊤)

/-- `B = Γ(Y, ⊤)` is an `R_K`-algebra through `pullback.snd : Y ⟶ Spec R_K`. -/
noncomputable instance : Algebra (puncturedRing K) (puncturedCoverRing f) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (puncturedRing K))).inv ≫
    (pullback.snd f (puncturedι K)).appTop).hom.toAlgebra

lemma algebraMap_puncturedCoverRing :
    algebraMap (puncturedRing K) (puncturedCoverRing f) =
      ((Scheme.ΓSpecIso (CommRingCat.of (puncturedRing K))).inv ≫
        (pullback.snd f (puncturedι K)).appTop).hom :=
  rfl

/-- `Y ⟶ Spec R_K` is finite (base change of the finite `f`). -/
theorem isFinite_puncturedCover_snd (hf : IsBelyiMap K f) :
    IsFinite (pullback.snd f (puncturedι K)) :=
  MorphismProperty.pullback_snd _ _ hf.isFinite

/-- `Y` is affine (finite over the affine `Spec R_K`). -/
theorem isAffine_puncturedCover (hf : IsBelyiMap K f) : IsAffine (puncturedCover f) :=
  haveI := isFinite_puncturedCover_snd hf
  isAffine_of_isAffineHom (pullback.snd f (puncturedι K))

/-- **`B` is a finite `R_K`-algebra.** -/
theorem puncturedCoverRing_finite (hf : IsBelyiMap K f) :
    Module.Finite (puncturedRing K) (puncturedCoverRing f) := by
  haveI := isFinite_puncturedCover_snd hf
  have h := (pullback.snd f (puncturedι K)).finite_appTop
  have hiso : ((Scheme.ΓSpecIso (CommRingCat.of (puncturedRing K))).inv).hom.Finite :=
    RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (puncturedRing K))).inv).2
  exact h.comp hiso

/-- **`Y ≅ Spec B` over `Spec R_K`**: under the canonical isomorphism `Y.isoSpec`, the
projection `Y ⟶ Spec R_K` is `Spec` of the structure map `R_K → B`. -/
theorem puncturedCover_isoSpec_hom_comp (hf : IsBelyiMap K f) :
    haveI := isAffine_puncturedCover hf
    (puncturedCover f).isoSpec.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (puncturedRing K) (puncturedCoverRing f))) =
      pullback.snd f (puncturedι K) := by
  haveI := isAffine_puncturedCover hf
  rw [algebraMap_puncturedCoverRing, CommRingCat.ofHom_hom, Spec.map_comp,
    Scheme.isoSpec_hom_naturality_assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.comp_id]

end General

section CharZero

variable {K : Type u} [Field K] [CharZero K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X] {f : X ⟶ P1 K}

/-- The generic point of `X` lies over the punctured line. -/
lemma genericPoint_mem_preimage_puncturedLine (hf : IsBelyiMap K f) :
    haveI := IsCurveOver.isIntegral K X
    f.base (genericPoint X) ∈ puncturedLine K := by
  haveI := IsCurveOver.isIntegral K X
  haveI := hf.isFinite
  haveI := isDominant_of_isFinite f
  rw [f.base_genericPoint]
  exact genericPoint_mem_puncturedLine K

/-- **`Y ⟶ X` has dense range**: its image `f⁻¹(ℙ¹ ∖ {0, 1, ∞})` is an open subset of the
irreducible `X` containing the generic point. -/
theorem denseRange_puncturedCover_fst (hf : IsBelyiMap K f) :
    DenseRange (pullback.fst f (puncturedι K)).base := by
  haveI := IsCurveOver.isIntegral K X
  have hmem : genericPoint X ∈ Set.range (pullback.fst f (puncturedι K)).base := by
    rw [IsOpenImmersion.range_pullbackFst, opensRange_puncturedι]
    exact genericPoint_mem_preimage_puncturedLine hf
  refine denseRange_iff_closure_range.mpr (Set.eq_univ_of_univ_subset ?_)
  rw [← (genericPoint_spec X).def]
  exact closure_mono (Set.singleton_subset_iff.mpr hmem)

/-- The open immersion `Y ⟶ X` is dominant. -/
theorem isDominant_puncturedCover_fst (hf : IsBelyiMap K f) :
    IsDominant (pullback.fst f (puncturedι K)) :=
  ⟨denseRange_puncturedCover_fst hf⟩

/-- `Y` is nonempty. -/
theorem nonempty_puncturedCover (hf : IsBelyiMap K f) : Nonempty (puncturedCover f) := by
  haveI := IsCurveOver.isIntegral K X
  exact (denseRange_puncturedCover_fst hf).nonempty_iff.mpr inferInstance

end CharZero

section AlgClosed

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X] {f : X ⟶ P1 K}

/-- A Belyi map on a curve is a Belyi cover (of degree its function-field degree). -/
noncomputable def IsBelyiMap.toBelyiCover (hf : IsBelyiMap K f) :
    haveI := IsCurveOver.isIntegral K X
    haveI := hf.isFinite
    haveI := isDominant_of_isFinite f
    BelyiCover K (degree f) :=
  haveI := IsCurveOver.isIntegral K X
  haveI := hf.isFinite
  haveI := isDominant_of_isFinite f
  { carrier := X
    map := f
    belyi := hf
    dominant := isDominant_of_isFinite f
    deg_le := le_rfl }

/-- **A Belyi map on a curve is étale over the thrice-punctured line.** -/
theorem IsBelyiMap.etale_morphismRestrict_puncturedLine (hf : IsBelyiMap K f) :
    Etale (f ∣_ puncturedLine K) :=
  (hf.toBelyiCover).etale_restrict

/-- `Y ⟶ Spec R_K` is étale: it is the restriction of `f` over the punctured line. -/
theorem etale_puncturedCover_snd (hf : IsBelyiMap K f) :
    Etale (pullback.snd f (puncturedι K)) := by
  have h := hf.etale_morphismRestrict_puncturedLine
  rw [← opensRange_puncturedι] at h
  exact (MorphismProperty.arrow_mk_iso_iff @Etale (morphismRestrictOpensRange f _)).mp h

/-- **`B` is an étale `R_K`-algebra.** -/
theorem puncturedCoverRing_etale (hf : IsBelyiMap K f) :
    Algebra.Etale (puncturedRing K) (puncturedCoverRing f) := by
  haveI := isAffine_puncturedCover hf
  haveI := etale_puncturedCover_snd hf
  have h : (pullback.snd f (puncturedι K)).appTop.hom.Etale :=
    HasRingHomProperty.iff_of_isAffine (P := @Etale).mp inferInstance
  have hiso : ((Scheme.ΓSpecIso (CommRingCat.of (puncturedRing K))).inv).hom.Etale :=
    RingHom.Etale.of_bijective
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (puncturedRing K))).inv)
  rw [← RingHom.etale_algebraMap, algebraMap_puncturedCoverRing]
  exact RingHom.Etale.stableUnderComposition _ _ hiso h

end AlgClosed

end Belyi
