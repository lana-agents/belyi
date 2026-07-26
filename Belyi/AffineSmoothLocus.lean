/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.SmoothLocusCongr
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Affine bridge: scheme smooth locus of `Spec.map φ` vs the ring-level `Algebra.smoothLocus`
(#168 piece (2b) brick)

For an `R`-algebra `S`, the scheme-level `Scheme.Hom.smoothLocus (Spec.map (algebraMap R S))`
(a set of points of `Spec S`, i.e. `PrimeSpectrum S`) coincides with the ring-level
`Algebra.smoothLocus R S`.

This is the affine bridge the #168 scheme lift needs: `formallySmooth_stalkMap_iff` at the ⊤/⊤
charts lands in `Algebra.smoothLocus Γ(Spec R, ⊤) Γ(Spec S, ⊤)` with the `appLE`-algebra
structure, and `Algebra.smoothLocus_comap_ringEquiv` (from `Belyi/SmoothLocusCongr.lean`)
transports it across the two `ΓSpecIso` ring isomorphisms of the base and total ring.

## Main results

* `Belyi.mem_smoothLocus_specMap_iff` — pointwise: `x ∈ (Spec.map (algebraMap R S)).smoothLocus ↔
  x ∈ Algebra.smoothLocus R S`.
-/

open AlgebraicGeometry CategoryTheory

namespace Belyi

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- **Affine bridge.** For an `R`-algebra `S`, a prime `x` of `S` lies in the scheme-level smooth
locus of `Spec.map (algebraMap R S)` iff it lies in the ring-level `Algebra.smoothLocus R S`. -/
theorem mem_smoothLocus_specMap_iff
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (x : PrimeSpectrum S) :
    x ∈ (Spec.map (CommRingCat.ofHom (algebraMap R S))).smoothLocus ↔
      x ∈ Algebra.smoothLocus R S := by
  have hVU : (⊤ : (Spec (CommRingCat.of S)).Opens) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) ⁻¹ᵁ ⊤ := le_top
  letI algI : Algebra Γ(Spec (CommRingCat.of R), ⊤) Γ(Spec (CommRingCat.of S), ⊤) :=
    ((Spec.map (CommRingCat.ofHom (algebraMap R S))).appLE ⊤ ⊤ hVU).hom.toAlgebra
  -- The two `ΓSpecIso` ring isomorphisms of the base and the total ring.
  let eR : Γ(Spec (CommRingCat.of R), ⊤) ≃+* R :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let eA : Γ(Spec (CommRingCat.of S), ⊤) ≃+* S :=
    (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv
  -- Compatibility of `eR`, `eA` with the two structure maps: the `appLE`-algebra map on the left
  -- and the canonical `algebraMap R S` on the right (`ΓSpecIso` naturality).
  have h : ∀ r, eA (algebraMap Γ(Spec (CommRingCat.of R), ⊤) Γ(Spec (CommRingCat.of S), ⊤) r)
      = algebraMap R S (eR r) := by
    intro r
    have hnat := congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R S)))
    rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at hnat
    have e3 := RingHom.congr_fun hnat r
    have happ : (Spec.map (CommRingCat.ofHom (algebraMap R S))).appLE ⊤ ⊤ hVU
        = (Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop :=
      (Scheme.Hom.app_eq_appLE _).symm
    rw [RingHom.algebraMap_toAlgebra, happ]
    simpa only [eR, eA, CategoryTheory.Iso.commRingCatIsoToRingEquiv, RingEquiv.ofRingHom_apply,
      RingHom.comp_apply, CommRingCat.hom_ofHom] using e3
  -- Step C: the affine chart's prime `primeIdealOf ⟨x, _⟩` is `comap eA x`.
  have stepC : (isAffineOpen_top (Spec (CommRingCat.of S))).primeIdealOf ⟨x, trivial⟩
      = PrimeSpectrum.comap (eA : Γ(Spec (CommRingCat.of S), ⊤) →+* S) x := by
    rw [IsAffineOpen.primeIdealOf, IsAffineOpen.isoSpec_hom, Scheme.Opens.toSpecΓ_top,
      Scheme.Hom.comp_apply, ← Scheme.isoSpec_hom, Scheme.isoSpec_Spec_hom, Spec.map_base]
    rfl
  suffices hiff :
      ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap x).hom.FormallySmooth ↔
        x ∈ Algebra.smoothLocus R S by
    exact hiff
  rw [formallySmooth_stalkMap_iff ⊤ (isAffineOpen_top _) ⊤ (isAffineOpen_top _) hVU trivial,
    stepC, ← Algebra.smoothLocus_comap_ringEquiv eR eA h, Set.mem_preimage]

end Belyi
