/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.FieldTheory.Perfect

/-!
# The smooth locus equals the étale locus for a finite characteristic-zero extension

This file provides the **ring-level bridge** `smoothLocus R A = etaleLocus R A` for a
finite (module-finite) morphism of characteristic-zero domains — follow-up piece (1) of
issue #168. Combined with the base-change descent of the étale locus
(`Belyi/EtaleLocusBaseChange.lean`) it lets the reverse inclusion of B2b, phrased for the
étale locus, be read back as a statement about the *smooth* locus (whence `Ram`, whose
definition is `(smoothLocus)ᶜ`).

## Why the étale and smooth loci coincide here

For a general finite-type algebra the smooth locus can be strictly larger than the étale
locus (positive relative dimension). What forces equality for a **finite** (relative
dimension `0`) morphism in characteristic zero is that the module of Kähler differentials
`Ω[A⁄R]` is a **torsion** `A`-module: the residue extension is generically separable, so
`Ω` vanishes after inverting the nonzero divisors of `R`. On the smooth locus `Ω` is
moreover locally free (`Module.freeLocus`); a module that is both free and torsion over a
domain is zero, so the smooth locus lands inside the *unramified* locus, hence inside the
étale locus.

## Main results

* `Belyi.subsingleton_localizedModule_of_free_of_isTorsion` — a torsion module that is free
  at a prime of a domain localizes to `0` there.
* `Algebra.smoothLocus_eq_etaleLocus_of_isTorsion_kaehler` — the bridge under the abstract
  hypothesis `Module.IsTorsion A Ω[A⁄R]`.
* `Belyi.isTorsion_kaehlerDifferential_of_finite_charZero` — `Ω[S⁄R]` is torsion for a
  module-finite extension of characteristic-zero domains with `R ↪ S`.
* `Belyi.smoothLocus_eq_etaleLocus_of_finite_charZero` — the combined statement.
-/

universe u

open TensorProduct

namespace Belyi

open scoped nonZeroDivisors

/-- **Free + torsion ⟹ zero, locally.** If a finite... (no finiteness needed) `A`-module `M`
over a domain `A` is torsion and is free after localizing at a prime `p`, then it localizes to
`0` at `p`: a nonzero free module over the domain `Aₚ` is torsion-free, contradicting torsion. -/
lemma subsingleton_localizedModule_of_free_of_isTorsion
    {A : Type*} [CommRing A] [IsDomain A] {M : Type*} [AddCommGroup M] [Module A M]
    (htor : Module.IsTorsion A M) (p : PrimeSpectrum A)
    (hfree : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M)) :
    Subsingleton (LocalizedModule p.asIdeal.primeCompl M) := by
  set Ap := Localization.AtPrime p.asIdeal
  set Mp := LocalizedModule p.asIdeal.primeCompl M
  haveI : IsDomain Ap :=
    IsLocalization.isDomain_of_le_nonZeroDivisors Ap p.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : Module.Free Ap Mp := hfree
  haveI : Module.Flat Ap Mp := Module.Flat.of_free
  haveI : Module.IsTorsionFree Ap Mp := Module.Flat.isTorsionFree
  have hinj : Function.Injective (algebraMap A Ap) :=
    IsLocalization.injective Ap p.asIdeal.primeCompl_le_nonZeroDivisors
  -- Every element of the localized module is zero.
  have h0 : ∀ z : Mp, z = 0 := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨a, ha⟩ := htor (x := m)
      have ha' : (a : A) • m = 0 := ha
      have hsmul : (a : A) • (LocalizedModule.mk m s : Mp) = 0 := by
        rw [LocalizedModule.smul'_mk, ha', LocalizedModule.zero_mk]
      have hAp : (algebraMap A Ap (a : A)) • (LocalizedModule.mk m s : Mp) = 0 := by
        rwa [IsScalarTower.algebraMap_smul]
      have hane : algebraMap A Ap (a : A) ≠ 0 := by
        rw [Ne, ← map_zero (algebraMap A Ap)]
        exact fun h => nonZeroDivisors.ne_zero a.2 (hinj h)
      rcases smul_eq_zero.mp hAp with h | h
      · exact absurd h hane
      · exact h
  exact subsingleton_of_forall_eq 0 fun z => h0 z

/-- A torsion module over a domain is supported nowhere it is free: `freeLocus ⊆ (support)ᶜ`. -/
lemma freeLocus_subset_compl_support_of_isTorsion
    {A : Type*} [CommRing A] [IsDomain A] {M : Type*} [AddCommGroup M] [Module A M]
    (htor : Module.IsTorsion A M) :
    Module.freeLocus A M ⊆ (Module.support A M)ᶜ := by
  intro p hp
  rw [Set.mem_compl_iff, Module.notMem_support_iff]
  exact subsingleton_localizedModule_of_free_of_isTorsion htor p (Module.mem_freeLocus.mp hp)

end Belyi

namespace Algebra

/-- **The smooth locus is the étale locus when `Ω` is torsion.** For an essentially-finite-type
algebra `A` over `R` with `A` a domain, if the module of Kähler differentials `Ω[A⁄R]` is a
torsion `A`-module then the smooth and étale loci coincide.

`etaleLocus ⊆ smoothLocus` is formal (étale = unramified ∧ smooth). For the reverse: on the
smooth locus `Ω` is locally free (`smoothLocus_eq_compl_support_inter`), and a free torsion
module over the domain `Aₚ` vanishes, so `Ω` has empty support there — landing the point in the
étale locus (`etaleLocus_eq_compl_support`). -/
theorem smoothLocus_eq_etaleLocus_of_isTorsion_kaehler
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsDomain A] [EssFiniteType R A]
    (htor : Module.IsTorsion A Ω[A⁄R]) :
    smoothLocus R A = etaleLocus R A := by
  apply le_antisymm
  · rw [etaleLocus_eq_compl_support]
    intro p hp
    rw [smoothLocus_eq_compl_support_inter, Set.mem_inter_iff] at hp
    obtain ⟨hH1, hfree⟩ := hp
    exact ⟨Belyi.freeLocus_subset_compl_support_of_isTorsion htor hfree, hH1⟩
  · rw [etaleLocus_eq_unramfiedLocus_inter_smoothLocus]
    exact Set.inter_subset_right

end Algebra

namespace Belyi

open Algebra IsLocalization

/-- **`Ω[S⁄R]` is torsion for a finite characteristic-zero extension.** Let `R ↪ S` be a
module-finite extension of characteristic-zero integral domains. Then `Ω[S⁄R]` is a torsion
`S`-module: after inverting the nonzero divisors of `R` the extension becomes the finite field
extension `L / K` with `K = Frac R` and `L = S ⊗_R K` (itself a field), which is separable in
characteristic zero, so `Ω[L⁄K] = 0`; hence every element of `Ω[S⁄R]` is killed by (the image
of) a nonzero element of `R`.

This is the torsion input to `smoothLocus_eq_etaleLocus_of_isTorsion_kaehler`. Unlike
`Algebra.FormallyUnramified.of_formallySmooth_of_finite_charZero`, it needs **no** global
formal-smoothness hypothesis: the smooth locus supplies local freeness pointwise. -/
theorem isTorsion_kaehlerDifferential_of_finite_charZero
    {R S : Type u} [CommRing R] [IsDomain R] [CharZero R]
    [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S] [Module.Finite R S] :
    Module.IsTorsion S (Ω[S⁄R]) := by
  classical
  -- `M' = algebraMapSubmonoid S R⁰ ≤ S⁰` since `R ↪ S`.
  have hM'le : Algebra.algebraMapSubmonoid S (nonZeroDivisors R) ≤ nonZeroDivisors S :=
    map_le_nonZeroDivisors_of_injective (algebraMap R S)
      (FaithfulSMul.algebraMap_injective R S) le_rfl
  -- `L = Localization M'` is a domain, and a field (finite over the field `K = Frac R`).
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
  -- Torsion: each `m` is killed by (the image of) a nonzero element of `R`.
  intro m
  have hzero :
      (KaehlerDifferential.map R (FractionRing R) S
        (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)))).restrictScalars R m
        = 0 :=
    Subsingleton.elim _ _
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors R) _).mp hzero
  -- `s • m = 0` with `s ∈ R⁰`, and `algebraMap R S s ∈ S⁰`.
  refine ⟨⟨algebraMap R S s, hM'le ⟨s, s.2, rfl⟩⟩, ?_⟩
  have h1 : (algebraMap R S (s : R)) • m = 0 := by rw [algebraMap_smul]; exact hs
  exact h1

/-- **The smooth locus equals the étale locus for a finite characteristic-zero extension.**
Combines `Algebra.smoothLocus_eq_etaleLocus_of_isTorsion_kaehler` with the torsion of `Ω`
(`isTorsion_kaehlerDifferential_of_finite_charZero`). This is the ring-level content of
follow-up piece (1) of issue #168: for a finite (relative dimension `0`) morphism in
characteristic zero, smoothness at a point is the same as étaleness at a point. -/
theorem smoothLocus_eq_etaleLocus_of_finite_charZero
    {R S : Type u} [CommRing R] [IsDomain R] [CharZero R]
    [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S] [Module.Finite R S]
    [EssFiniteType R S] :
    Algebra.smoothLocus R S = Algebra.etaleLocus R S :=
  Algebra.smoothLocus_eq_etaleLocus_of_isTorsion_kaehler
    isTorsion_kaehlerDifferential_of_finite_charZero

end Belyi
