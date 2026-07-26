/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.AffineSmoothLocus
import Belyi.SmoothLocusBaseChange
import Belyi.RamificationBaseChange

/-!
# Scheme-level smooth-locus base change for the affine `Spec.map` square (#168 piece (2b))

This file lifts the ring-level reverse (descent) inclusion of the smooth locus,
`Belyi.smoothLocus_baseChange_subset` (`Belyi/SmoothLocusBaseChange.lean`), to the
**scheme level** for the affine base-change square of `Spec.map`s attached to a tensor product
`A' ⊗[A] B`:

```
  Spec (A' ⊗[A] B) --pr--> Spec B
        f' |                   | f
       Spec A'   ----q---->  Spec A
```

with `f = Spec.map (algebraMap A B)`, `f' = Spec.map (algebraMap A' (A' ⊗[A] B))`,
`pr = Spec.map (algebraMap B (A' ⊗[A] B))` and `q = Spec.map (algebraMap A A')`.

The bridge is entirely pointwise: `Belyi.mem_smoothLocus_specMap_iff`
(`Belyi/AffineSmoothLocus.lean`) identifies the scheme-level `Scheme.Hom.smoothLocus` of each
`Spec.map (algebraMap R S)` with the ring-level `Algebra.smoothLocus R S`, and the base of a
`Spec.map` is `PrimeSpectrum.comap`, so `pr` transports `z` to exactly the prime the ring-level
inclusion `smoothLocus_baseChange_subset` acts on.

Combining the reverse inclusion with the already-merged **forward** inclusion
`Belyi.smoothLocus_preimage_subset` (which holds for any pullback square, with the affine square
supplied by `CommRingCat.isPushout_tensorProduct` +
`AlgebraicGeometry.isPullback_SpecMap_of_isPushout`)
gives the scheme-level **equality** `smoothLocus f' = pr ⁻¹ᵁ smoothLocus f`, hence
`Ram f' = pr ⁻¹' Ram f`, for the affine base-change square.

## Main results

* `Belyi.smoothLocus_specMap_baseChange_subset` — the reverse (descent) inclusion at scheme level.
* `Belyi.isPullback_specMap_tensor` — the affine base-change square is a pullback of schemes.
* `Belyi.smoothLocus_specMap_baseChange_eq` — the scheme-level equality of smooth loci.
* `Belyi.ram_specMap_baseChange_eq` — the corresponding equality of ramification loci
  `Ram f' = pr ⁻¹' Ram f`.
* `Belyi.branch_specMap_baseChange_eq` — the corresponding equality of branch loci
  `Branch f' = q ⁻¹' Branch f`, upgrading the forward inclusion `Belyi.branch_subset_preimage`
  to an equality at ring/affine level (the B2b/B3d branch-locus matching for this square).
-/

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace Belyi

universe u

variable {A A' B : Type u} [CommRing A] [IsDomain A] [CharZero A] [IsNoetherianRing A]
  [CommRing A'] [IsDomain A'] [CharZero A'] [Algebra A A'] [Module.Flat A A']
  [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Module.Finite A B]
  [IsDomain (A' ⊗[A] B)] [FaithfulSMul A' (A' ⊗[A] B)]

/-- `A → B` is finitely presented (finite over the Noetherian base `A`). -/
private instance : Algebra.FinitePresentation A B :=
  (Algebra.FinitePresentation.of_finiteType (R := A) (A := B)).mp inferInstance

/-- `A' → A' ⊗[A] B` is finitely presented (base change of the finitely presented `A → B`). -/
private instance : Algebra.FinitePresentation A' (A' ⊗[A] B) :=
  inferInstance

private instance : LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  rw [LocallyOfFinitePresentation.SpecMap_iff, CommRingCat.hom_ofHom]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

private instance : LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] B)))) := by
  rw [LocallyOfFinitePresentation.SpecMap_iff, CommRingCat.hom_ofHom]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- **Reverse (descent) inclusion of the smooth locus under base change, scheme level (affine
square).** For the affine base-change square of a tensor product `A' ⊗[A] B` (finite
characteristic-zero domain data, see the file header), the scheme-level smooth locus of the base
change `f' = Spec.map (algebraMap A' (A' ⊗[A] B))` is contained in the `pr`-preimage of the smooth
locus of `f = Spec.map (algebraMap A B)`, where `pr = Spec.map (algebraMap B (A' ⊗[A] B))`.

Pointwise: a prime `z` at which `f'` is smooth maps under `pr` (= `PrimeSpectrum.comap`) to a prime
at which `f` is smooth. This is the affine-bridge lift of the ring-level
`Belyi.smoothLocus_baseChange_subset`. -/
theorem smoothLocus_specMap_baseChange_subset :
    letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    ((Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] B)))).smoothLocus :
        Set (Spec (CommRingCat.of (A' ⊗[A] B)))) ⊆
      ((Spec.map (CommRingCat.ofHom (algebraMap B (A' ⊗[A] B))) ⁻¹ᵁ
        (Spec.map (CommRingCat.ofHom (algebraMap A B))).smoothLocus :
        (Spec (CommRingCat.of (A' ⊗[A] B))).Opens) :
        Set (Spec (CommRingCat.of (A' ⊗[A] B)))) := by
  letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  intro z hz
  -- Membership in the `pr`-preimage is membership of `pr.base z` in `smoothLocus f`.
  rw [Scheme.Hom.coe_preimage, Set.mem_preimage]
  -- `pr.base z = PrimeSpectrum.comap (algebraMap B (A' ⊗[A] B)) z`.
  change PrimeSpectrum.comap (algebraMap B (A' ⊗[A] B)) z ∈
    (Spec.map (CommRingCat.ofHom (algebraMap A B))).smoothLocus
  rw [mem_smoothLocus_specMap_iff]
  -- Ring-level descent inclusion, fed the affine-bridge form of `hz`.
  refine smoothLocus_baseChange_subset (A := A) (A' := A') (B := B) ?_
  rwa [← mem_smoothLocus_specMap_iff]

omit [IsDomain A] [CharZero A] [IsNoetherianRing A] [IsDomain A'] [CharZero A'] [Module.Flat A A']
  [IsDomain B] [FaithfulSMul A B] [Module.Finite A B] [IsDomain (A' ⊗[A] B)]
  [FaithfulSMul A' (A' ⊗[A] B)] in
/-- The affine base-change square of the tensor product `A' ⊗[A] B` is a pullback of schemes:
```
  Spec (A' ⊗[A] B) --pr--> Spec B
        f' |                   | f
       Spec A'   ----q---->  Spec A
```
with `pr = Spec.map (algebraMap B (A' ⊗[A] B))`, `f' = Spec.map (algebraMap A' (A' ⊗[A] B))`,
`f = Spec.map (algebraMap A B)` and `q = Spec.map (algebraMap A A')`. This is `Spec` applied to the
pushout square `CommRingCat.isPushout_tensorProduct`. -/
theorem isPullback_specMap_tensor :
    letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap B (A' ⊗[A] B))))
      (Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] B))))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A A'))) := by
  letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A A' B)).flip

/-- **Scheme-level equality of smooth loci under base change (affine square).** Combining the
reverse inclusion `smoothLocus_specMap_baseChange_subset` with the forward inclusion
`Belyi.smoothLocus_preimage_subset` (applied to the pullback square `isPullback_specMap_tensor`)
gives `smoothLocus f' = pr ⁻¹ᵁ smoothLocus f` for the affine base-change square. -/
theorem smoothLocus_specMap_baseChange_eq :
    letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    ((Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] B)))).smoothLocus :
        Set (Spec (CommRingCat.of (A' ⊗[A] B)))) =
      ((Spec.map (CommRingCat.ofHom (algebraMap B (A' ⊗[A] B))) ⁻¹ᵁ
        (Spec.map (CommRingCat.ofHom (algebraMap A B))).smoothLocus :
        (Spec (CommRingCat.of (A' ⊗[A] B))).Opens) :
        Set (Spec (CommRingCat.of (A' ⊗[A] B)))) := by
  letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  refine Set.Subset.antisymm smoothLocus_specMap_baseChange_subset ?_
  exact smoothLocus_preimage_subset isPullback_specMap_tensor

/-- **Ramification locus equality under base change (affine square).** `Ram f' = pr ⁻¹' Ram f` for
the affine base-change square, obtained by taking complements in
`smoothLocus_specMap_baseChange_eq`. This is the B2b/B3d branch-locus matching, at ring/affine
level. -/
theorem ram_specMap_baseChange_eq :
    letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    Ram (Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] B)))) =
      (Spec.map (CommRingCat.ofHom (algebraMap B (A' ⊗[A] B)))) ⁻¹'
        Ram (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  rw [Ram, Ram, Set.preimage_compl, ← Scheme.Hom.coe_preimage,
    ← smoothLocus_specMap_baseChange_eq]

/-- **Branch locus equality under base change (affine square).** `Branch f' = q ⁻¹' Branch f`
for the affine base-change square, with `f' = Spec.map (algebraMap A' (A' ⊗[A] B))`,
`f = Spec.map (algebraMap A B)` and `q = Spec.map (algebraMap A A')`. Obtained from the
ramification equality `ram_specMap_baseChange_eq` through the unconditional
`Belyi.branch_preimage_eq`, applied to the pullback square `isPullback_specMap_tensor`. This
upgrades the forward inclusion `Belyi.branch_subset_preimage` to an equality — the B2b/B3d
branch-locus matching, at ring/affine level. -/
theorem branch_specMap_baseChange_eq :
    Branch (Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] B)))) =
      (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ⁻¹'
        Branch (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  branch_preimage_eq isPullback_specMap_tensor ram_specMap_baseChange_eq

end Belyi
