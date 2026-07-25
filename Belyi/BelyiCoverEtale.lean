/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.BelyiCoverRestrict
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# A Belyi cover restricts to an étale cover of `ℙ¹ ∖ {0, 1, ∞}`

Building on `Belyi.BelyiCover.isFinite_restrict` and `Belyi.BelyiCover.smooth_restrict`
(`Belyi/BelyiCoverRestrict.lean`), this file closes the *étale gap* documented there: the
restriction of a Belyi cover over the thrice-punctured line `ℙ¹_k ∖ {0, 1, ∞}` is **étale**.

## Proof route

`AlgebraicGeometry.Etale.of_formallyUnramified_of_flat` reduces `Etale` to
`FormallyUnramified` given `Flat` and `LocallyOfFinitePresentation`; the latter two are free
from `Smooth`. So the only real content is `FormallyUnramified (A.map ∣_ puncturedLine k)`.

Since `FormallyUnramified` is affine-local (a `HasRingHomProperty` for
`RingHom.FormallyUnramified = Algebra.FormallyUnramified`), it suffices to prove the algebra
statement on each affine chart: an `R`-algebra `S` that is module-finite, formally smooth, and
whose induced generic-fibre extension is separable, is formally unramified. The novel content is
the reusable

* `Algebra.FormallyUnramified.of_formallySmooth_of_finite_charZero`.
-/

universe u

open scoped nonZeroDivisors

open Algebra IsLocalization in
/-- **Algebra core.** A module-finite, formally smooth `R`-algebra `S` between characteristic-zero
integral domains, with `R ↪ S`, is formally unramified.

Mathematically: `Ω[S⁄R]` is projective (formal smoothness), hence flat, hence torsion-free over the
domain `S`. Localizing at the nonzero divisors of `R` turns `Ω[S⁄R]` into `Ω[L⁄K]` where
`K = Frac R` and `L = S ⊗_R K` is a finite domain over the field `K`, hence itself a field; the
finite extension `L / K` is algebraic, so separable in characteristic zero, so `Ω[L⁄K] = 0`. A
torsion-free module that vanishes after localization at nonzero divisors of the domain is zero. -/
theorem Algebra.FormallyUnramified.of_formallySmooth_of_finite_charZero
    {R : Type u} {S : Type u} [CommRing R] [IsDomain R] [CharZero R]
    [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S]
    [Module.Finite R S] [Algebra.FormallySmooth R S] :
    Algebra.FormallyUnramified R S := by
  classical
  -- `M' = algebraMapSubmonoid S R⁰ ≤ S⁰` since `R ↪ S`.
  have hM'le : Algebra.algebraMapSubmonoid S (nonZeroDivisors R) ≤ nonZeroDivisors S :=
    map_le_nonZeroDivisors_of_injective (algebraMap R S)
      (FaithfulSMul.algebraMap_injective R S) le_rfl
  -- `B = Localization M'` is a domain and a field (finite over the field `K = Frac R`).
  haveI hBdom : IsDomain (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ hM'le
  haveI : CharZero (FractionRing R) := Algebra.charZero_of_charZero (R := R) (A := FractionRing R)
  haveI : PerfectField (FractionRing R) := PerfectField.ofCharZero
  have hBfield : IsField (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))) :=
    isField_of_isIntegral_of_isField' (R := FractionRing R) (Field.toIsField (FractionRing R))
  letI : Field (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))) :=
    hBfield.toField
  -- Generic extension `L / K` is separable (algebraic + char 0), so `Ω[L⁄K] = 0`.
  haveI : Algebra.FormallyUnramified (FractionRing R)
      (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))) :=
    Algebra.FormallyUnramified.of_isSeparable (FractionRing R) _
  haveI hsub : Subsingleton
      (Ω[Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))⁄FractionRing R]) :=
    Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  -- The comparison map is a localization of `S`-modules at `R⁰`.
  haveI hloc : IsLocalizedModule (nonZeroDivisors R)
      ((KaehlerDifferential.map R (FractionRing R) S
        (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)))).restrictScalars R) :=
    KaehlerDifferential.isLocalizedModule _ (FractionRing R) S _ (nonZeroDivisors R)
  -- `Ω[S⁄R]` is flat over `S` (projective by formal smoothness), hence torsion-free.
  have htor : Submodule.torsion S (Ω[S⁄R]) = ⊥ := Module.Flat.torsion_eq_bot
  -- Conclude `Ω[S⁄R]` is subsingleton.
  refine ⟨subsingleton_of_forall_eq 0 fun m => ?_⟩
  have hzero :
      (KaehlerDifferential.map R (FractionRing R) S
        (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)))).restrictScalars R m
        = 0 :=
    Subsingleton.elim _ _
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors R) _).mp hzero
  -- `s • m = 0` with `s ∈ R⁰`, and `algebraMap R S s ∈ S⁰`, so `m ∈ torsion S Ω = ⊥`.
  have hsS : (algebraMap R S s : S) ∈ nonZeroDivisors S :=
    hM'le ⟨s, s.2, rfl⟩
  have h1 : (algebraMap R S (s : R)) • m = 0 := by
    rw [algebraMap_smul]
    exact hs
  have hmem : m ∈ Submodule.torsion S (Ω[S⁄R]) := ⟨⟨algebraMap R S s, hsS⟩, h1⟩
  rw [htor] at hmem
  exact hmem

namespace AlgebraicGeometry

open CategoryTheory

variable {X Y : Scheme.{u}}

/-- **Per-chart algebra input.** For a finite, smooth, dominant morphism `f : X ⟶ Y` of integral
schemes with function field of characteristic zero, the section ring map over an affine open `W` of
the target is formally unramified. This packages the algebra core
`Algebra.FormallyUnramified.of_formallySmooth_of_finite_charZero` with the geometric instances. -/
private lemma formallyUnramified_app_of_isFinite_smooth (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [Smooth f] [IsFinite f]
    [CharZero Y.functionField] (W : Y.Opens) (hW : IsAffineOpen W) :
    RingHom.FormallyUnramified (f.app W).hom := by
  rcases (f ⁻¹ᵁ W).1.eq_empty_or_nonempty with hemp | hne
  · -- Empty preimage: the target section ring is trivial, so `Ω` vanishes.
    have hbot : (f ⁻¹ᵁ W) = ⊥ := SetLike.ext' hemp
    haveI : Subsingleton Γ(X, f ⁻¹ᵁ W) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hbot)
    letI := (f.app W).hom.toAlgebra
    exact ⟨inferInstance⟩
  · haveI : IsSchemeTheoreticallyDominant f := .of_isDominant f
    haveI hVne : Nonempty (f ⁻¹ᵁ W) := hne.to_subtype
    haveI hWne : Nonempty W := ⟨⟨f.base hne.choose, hne.choose_spec⟩⟩
    have hpre : IsAffineOpen (f ⁻¹ᵁ W) := hW.preimage f
    letI := (f.app W).hom.toAlgebra
    haveI : IsDomain Γ(Y, W) := inferInstance
    haveI : IsDomain Γ(X, f ⁻¹ᵁ W) := inferInstance
    haveI : Module.Finite Γ(Y, W) Γ(X, f ⁻¹ᵁ W) := IsFinite.finite_app f W hW
    haveI : Algebra.FormallySmooth Γ(Y, W) Γ(X, f ⁻¹ᵁ W) := by
      have h := HasRingHomProperty.appLE (P := @Smooth) (f := f) ‹Smooth f› ⟨W, hW⟩
        ⟨f ⁻¹ᵁ W, hpre⟩ le_rfl
      rw [← Scheme.Hom.app_eq_appLE] at h
      exact h.formallySmooth
    haveI : FaithfulSMul Γ(Y, W) Γ(X, f ⁻¹ᵁ W) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (f.app_injective W)
    haveI : CharZero Γ(Y, W) := (Y.germToFunctionField W).hom.charZero
    exact Algebra.FormallyUnramified.of_formallySmooth_of_finite_charZero

set_option backward.isDefEq.respectTransparency false in
/-- **Scheme assembly.** A finite, smooth, dominant morphism of integral schemes whose target has a
characteristic-zero function field is formally unramified. Reduces target-locally to the affine
charts handled by `formallyUnramified_app_of_isFinite_smooth`. -/
theorem FormallyUnramified.of_isFinite_of_smooth_of_isDominant (f : X ⟶ Y)
    [IsIntegral X] [IsIntegral Y] [IsDominant f] [Smooth f] [IsFinite f]
    [CharZero Y.functionField] :
    FormallyUnramified f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @FormallyUnramified)
    (fun W : Y.affineOpens => (W : Y.Opens)) (iSup_affineOpens_eq_top Y)]
  intro W
  haveI hWaff : IsAffine (W : Y.Opens).toScheme := W.2
  haveI hpreaff : IsAffine (f ⁻¹ᵁ (W : Y.Opens)).toScheme := W.2.preimage f
  rw [HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified), morphismRestrict_appTop,
    CommRingCat.hom_comp, RingHom.FormallyUnramified.respectsIso.cancel_right_isIso _ _]
  exact formallyUnramified_app_of_isFinite_smooth f _
    (by rw [Scheme.Opens.ι_image_top]; exact W.2)

end AlgebraicGeometry

namespace Belyi

open AlgebraicGeometry CategoryTheory
open scoped Belyi

/-- The generic point of `ℙ¹_k` lies in the punctured line (it is none of the three marked
points). -/
lemma genericPoint_mem_puncturedLine (k : Type u) [Field k] :
    _root_.genericPoint (P1 k) ∈ puncturedLine k := by
  have hnot : _root_.genericPoint (P1 k) ∉ markedPoints k := by
    simp only [markedPoints, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => P1.zero_ne_genericPoint k h.symm,
      fun h => P1.one_ne_genericPoint k h.symm,
      fun h => P1.infty_ne_genericPoint k h.symm⟩
  exact hnot

namespace BelyiCover

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {d : ℕ}

/-- **The restriction of a Belyi cover over the thrice-punctured line is étale.** This closes the
étale gap of `Belyi/BelyiCoverRestrict.lean`: from `isFinite_restrict` and `smooth_restrict`, the
morphism is finite and smooth, so flat and locally of finite presentation for free; the remaining
`FormallyUnramified` obligation is discharged by
`AlgebraicGeometry.FormallyUnramified.of_isFinite_of_smooth_of_isDominant`. -/
theorem etale_restrict (A : BelyiCover k d) :
    Etale (A.map ∣_ puncturedLine k) := by
  letI := A.over
  haveI := A.curve
  haveI : IsIntegral A.carrier := IsCurveOver.isIntegral k A.carrier
  haveI : IsDominant A.map := A.dominant
  haveI : IsFinite A.map := A.belyi.isFinite
  haveI := A.isFinite_restrict
  haveI := A.smooth_restrict
  -- The generic point of `P1` lies in the punctured line and is the image of the generic point.
  have hgenU : _root_.genericPoint (P1 k) ∈ puncturedLine k := genericPoint_mem_puncturedLine k
  -- The punctured line is a nonempty open of the integral `P1`, hence integral.
  haveI hUne : Nonempty (puncturedLine k : (P1 k).Opens) := ⟨⟨_, hgenU⟩⟩
  haveI hYint : IsIntegral (puncturedLine k).toScheme :=
    isIntegral_of_isOpenImmersion (puncturedLine k).ι
  -- The preimage contains the generic point of the carrier, hence is nonempty and integral.
  have hgenX : A.map.base (_root_.genericPoint A.carrier) ∈ puncturedLine k := by
    rw [A.map.base_genericPoint]
    exact hgenU
  haveI hXne : Nonempty (A.map ⁻¹ᵁ puncturedLine k : A.carrier.Opens) := ⟨⟨_, hgenX⟩⟩
  haveI hXint : IsIntegral (A.map ⁻¹ᵁ puncturedLine k).toScheme :=
    isIntegral_of_isOpenImmersion (A.map ⁻¹ᵁ puncturedLine k).ι
  -- The restriction is surjective (finite dominant → surjective, stable under base change),
  -- hence dominant.
  haveI : Surjective A.map := Surjective.of_universallyClosed_of_isDominant A.map
  haveI : Surjective (A.map ∣_ puncturedLine k) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (isPullback_morphismRestrict A.map (puncturedLine k)).flip ‹Surjective A.map›
  haveI : IsDominant (A.map ∣_ puncturedLine k) := inferInstance
  -- The target function field is characteristic zero.
  haveI : (puncturedLine k).toScheme.Over (Spec (CommRingCat.of k)) :=
    ⟨(puncturedLine k).ι ≫ P1 k ↘ Spec (CommRingCat.of k)⟩
  haveI : CharZero (puncturedLine k).toScheme.functionField :=
    charZero_of_injective_algebraMap
      (algebraMap k (puncturedLine k).toScheme.functionField).injective
  -- Assemble: formally unramified + flat + locally of finite presentation ⇒ étale.
  haveI : FormallyUnramified (A.map ∣_ puncturedLine k) :=
    AlgebraicGeometry.FormallyUnramified.of_isFinite_of_smooth_of_isDominant _
  exact Etale.of_formallyUnramified_of_flat _

end BelyiCover

end Belyi
