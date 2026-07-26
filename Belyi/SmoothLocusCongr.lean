/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Etale.Basic

/-!
# Congruence of the smooth locus under compatible ring isomorphisms (#168 piece (2b) brick)

The scheme-level lift of the base-change descent inclusion of `Scheme.Hom.smoothLocus`
(issue #168) proceeds through the affine bridge `formallySmooth_stalkMap_iff`, which lands in
`Algebra.smoothLocus Γ(Spec R, ⊤) Γ(Spec S, ⊤)` with the `appLE`-algebra structure. To identify
this with `Algebra.smoothLocus R S` one must transport `Algebra.smoothLocus` across the two
`ΓSpecIso` ring isomorphisms of the base and the total ring. Mathlib v4.32 has **no** congruence
lemma for `Algebra.smoothLocus`/`Algebra.IsSmoothAt` under ring isomorphisms
(`RingTheory/Smooth/Locus.lean` only has `smoothLocus_comap_of_isLocalization`), so we build it
here.

## Main results

* `Algebra.FormallySmooth.congr` : formal smoothness is invariant under a compatible pair of ring
  isomorphisms of the base and the total ring.
* `Algebra.smoothLocus_comap_ringEquiv` : `smoothLocus R' A'` is the preimage of `smoothLocus R A`
  under `PrimeSpectrum.comap eA`, for a compatible pair of ring isomorphisms `eR : R ≃+* R'`,
  `eA : A ≃+* A'`.

These are general commutative-algebra statements, upstreamable to mathlib.
-/

open scoped TensorProduct

namespace Algebra

universe u v

variable {R R' A A' : Type*} [CommRing R] [CommRing R'] [CommRing A] [CommRing A']
  [Algebra R A] [Algebra R' A']

/-- Formal smoothness is invariant under a compatible pair of ring isomorphisms of the base
and the total ring: if `eR : R ≃+* R'`, `eA : A ≃+* A'` intertwine the two structure maps
(`eA (algebraMap R A r) = algebraMap R' A' (eR r)`), then `A` is formally smooth over `R`
iff `A'` is formally smooth over `R'`. -/
theorem FormallySmooth.congr (eR : R ≃+* R') (eA : A ≃+* A')
    (h : ∀ r, eA (algebraMap R A r) = algebraMap R' A' (eR r)) :
    FormallySmooth R A ↔ FormallySmooth R' A' := by
  -- Give `A'` the `R`-algebra structure obtained by restricting scalars along `eR`.
  letI iRA' : Algebra R A' := ((algebraMap R' A').comp (eR : R →+* R')).toAlgebra
  have hRA' : ∀ r : R, algebraMap R A' r = algebraMap R' A' (eR r) := fun _ => rfl
  -- Step 1: `eA` is an `R`-algebra isomorphism `A ≃ₐ[R] A'` (with the structure above).
  let eAalg : A ≃ₐ[R] A' :=
    { eA with commutes' := fun r => by rw [hRA']; exact h r }
  -- Step 2: restricting scalars from `R'` to `R` along the isomorphism `eR` preserves
  -- formal smoothness of `A'`.
  letI iRR' : Algebra R R' := (eR : R →+* R').toAlgebra
  haveI : IsScalarTower R R' A' :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  haveI : FormallyEtale R R' := by
    rw [FormallyEtale.iff_of_surjective
      (show Function.Surjective (algebraMap R R') from eR.surjective)]
    have hker : RingHom.ker (algebraMap R R') = ⊥ := by
      rw [RingHom.ker_eq_bot_iff_eq_zero]
      intro x hx
      apply eR.injective
      rw [map_zero]
      exact hx
    rw [hker]
    exact Ideal.mul_bot ⊥
  rw [FormallySmooth.iff_of_equiv eAalg,
    FormallySmooth.iff_restrictScalars (R := R) (A := R') (B := A')]

/-- `smoothLocus R' A'` is the preimage of `smoothLocus R A` under the map of prime spectra
`Spec A' → Spec A` induced by `eA`, for a compatible pair of ring isomorphisms
`eR : R ≃+* R'`, `eA : A ≃+* A'`. -/
theorem smoothLocus_comap_ringEquiv (eR : R ≃+* R') (eA : A ≃+* A')
    (h : ∀ r, eA (algebraMap R A r) = algebraMap R' A' (eR r)) :
    PrimeSpectrum.comap (eA : A →+* A') ⁻¹' smoothLocus R A = smoothLocus R' A' := by
  ext p'
  simp only [Set.mem_preimage, smoothLocus, Set.mem_setOf_eq, PrimeSpectrum.comap_asIdeal]
  set q : Ideal A := p'.asIdeal.comap (eA : A →+* A') with hq
  haveI : q.IsPrime := hq ▸ inferInstance
  -- localization isomorphism induced by `eA`
  have hmap : Submonoid.map (eA : A →+* A') q.primeCompl = p'.asIdeal.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective (f := (eA : A →+* A'))
      (EquivLike.surjective eA) p'.asIdeal
  let eLoc : Localization.AtPrime q ≃+* Localization.AtPrime p'.asIdeal :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime q) (Localization.AtPrime p'.asIdeal)
      eA (by simpa using hmap)
  refine FormallySmooth.congr eR eLoc ?_
  intro r
  rw [IsScalarTower.algebraMap_apply R A (Localization.AtPrime q) r,
    IsLocalization.ringEquivOfRingEquiv_eq, h r,
    ← IsScalarTower.algebraMap_apply R' A' (Localization.AtPrime p'.asIdeal) (eR r)]

end Algebra
