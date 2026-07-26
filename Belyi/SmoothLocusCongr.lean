/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.RingHom.Smooth

/-!
# Congruence of the smooth locus under compatible ring equivalences (#168 piece (2b) infra)

The scheme lift of issue #168 (transferring `Scheme.Hom.smoothLocus` on affine charts to the
ring-level `Algebra.smoothLocus`) needs to transport `Algebra.smoothLocus`/`Algebra.IsSmoothAt`
across the `ΓSpecIso` ring isomorphisms `Γ(Spec R, ⊤) ≃+* R` (and the corresponding one for the
total ring). Mathlib v4.32 has no congruence lemma for `Algebra.smoothLocus` under a ring iso —
only `Algebra.smoothLocus_comap_of_isLocalization` for a localization map. This file provides the
missing piece: `Algebra.smoothLocus` is invariant under a pair of compatible ring equivalences of
the base ring and the total ring.

## Main results

* `Belyi.formallySmooth_localizationAtPrime_congr` — the pointwise statement: for compatible ring
  equivalences `eR : R ≃+* R'`, `eA : A ≃+* A'` and a prime `p` of `A'`, the localization
  `A`-algebra `Aₚ'` (at `p.comap eA`) is formally smooth over `R` iff `A'ₚ` is formally smooth
  over `R'`.
* `Belyi.smoothLocus_congr` — the set-level statement:
  `PrimeSpectrum.comap eA ⁻¹' smoothLocus R A = smoothLocus R' A'`.

The proof identifies the two localizations via `IsLocalization.ringEquivOfRingEquiv` and transports
formal smoothness across the resulting arrow isomorphism (`RingHom.FormallySmooth.respectsIso`).
-/

open TensorProduct CategoryTheory

namespace Belyi

universe u

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing R'] [CommRing A'] [Algebra R' A']

/-- The prime compl of `p.comap eA` maps, under the ring equivalence `eA`, onto the prime compl
of `p`. This is the submonoid-matching hypothesis of `IsLocalization.ringEquivOfRingEquiv`. -/
private lemma primeCompl_comap_map (eA : A ≃+* A') (p : Ideal A') [p.IsPrime] :
    Submonoid.map (eA : A →+* A').toMonoidHom (p.comap (eA : A →+* A')).primeCompl =
      p.primeCompl := by
  ext y
  simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, Ideal.mem_comap]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨eA.symm y, by simpa using hy, by simp⟩

/-- **Pointwise congruence of formal smoothness at a prime under compatible ring equivalences.**

If `eR : R ≃+* R'` and `eA : A ≃+* A'` are ring equivalences making the square
`algebraMap R' A' ∘ eR = eA ∘ algebraMap R A` commute, then for a prime `p` of `A'` the
localization of `A` at `p.comap eA`, viewed as an `R`-algebra, is formally smooth over `R` iff the
localization of `A'` at `p`, viewed as an `R'`-algebra, is formally smooth over `R'`. -/
lemma formallySmooth_localizationAtPrime_congr (eR : R ≃+* R') (eA : A ≃+* A')
    (h : (algebraMap R' A').comp (eR : R →+* R') = (eA : A →+* A').comp (algebraMap R A))
    (p : Ideal A') [p.IsPrime] :
    Algebra.FormallySmooth R (Localization.AtPrime (p.comap (eA : A →+* A'))) ↔
      Algebra.FormallySmooth R' (Localization.AtPrime p) := by
  -- The ring equivalence of localizations induced by `eA`.
  let L : Localization.AtPrime (p.comap (eA : A →+* A')) ≃+* Localization.AtPrime p :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (p.comap (eA : A →+* A')))
      (Localization.AtPrime p) eA (primeCompl_comap_map eA p)
  -- `L` intertwines the two structure maps from `R` and `R'` via `eR`.
  have hcompat : (algebraMap R' (Localization.AtPrime p)).comp (eR : R →+* R') =
      (L : _ →+* _).comp (algebraMap R (Localization.AtPrime (p.comap (eA : A →+* A')))) := by
    ext r
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply R A (Localization.AtPrime (p.comap (eA : A →+* A'))) r]
    change algebraMap R' (Localization.AtPrime p) (eR r) =
      IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime (p.comap (eA : A →+* A')))
        (Localization.AtPrime p) eA (primeCompl_comap_map eA p)
        (algebraMap A (Localization.AtPrime (p.comap (eA : A →+* A'))) (algebraMap R A r))
    rw [IsLocalization.ringEquivOfRingEquiv_eq,
      IsScalarTower.algebraMap_apply R' A' (Localization.AtPrime p) (eR r)]
    congr 1
    exact congr($h r)
  -- Package the square as an isomorphism of arrows in `CommRingCat` and transport smoothness.
  have e : Arrow.mk (CommRingCat.ofHom (algebraMap R (Localization.AtPrime (p.comap
      (eA : A →+* A'))))) ≅
        Arrow.mk (CommRingCat.ofHom (algebraMap R' (Localization.AtPrime p))) :=
    Arrow.isoMk' _ _ eR.toCommRingCatIso L.toCommRingCatIso
      (by
        apply CommRingCat.hom_ext
        simp only [CommRingCat.hom_comp, RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_ofHom]
        exact hcompat)
  rw [← RingHom.formallySmooth_algebraMap (R := R),
    ← RingHom.formallySmooth_algebraMap (R := R')]
  exact RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff e

/-- **Congruence of the smooth locus under compatible ring equivalences.**

If `eR : R ≃+* R'` and `eA : A ≃+* A'` are ring equivalences with
`algebraMap R' A' ∘ eR = eA ∘ algebraMap R A`, then the smooth locus of `A/R` pulls back, along the
spectrum map of `eA`, to the smooth locus of `A'/R'`. In particular the homeomorphism
`PrimeSpectrum.comap eA` identifies the two smooth loci. -/
theorem smoothLocus_congr (eR : R ≃+* R') (eA : A ≃+* A')
    (h : (algebraMap R' A').comp (eR : R →+* R') = (eA : A →+* A').comp (algebraMap R A)) :
    PrimeSpectrum.comap (eA : A →+* A') ⁻¹' Algebra.smoothLocus R A =
      Algebra.smoothLocus R' A' := by
  ext p
  simp only [Set.mem_preimage, Algebra.smoothLocus, Set.mem_setOf_eq]
  exact formallySmooth_localizationAtPrime_congr eR eA h p.asIdeal

end Belyi
