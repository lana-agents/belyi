/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.AffineSmoothLocus
import Belyi.SmoothLocusBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Reverse inclusion of the smooth locus under base change — affine scheme level (#168 piece (2b))

This file lifts the ring-level descent inclusion `Belyi.smoothLocus_baseChange_subset`
(`Belyi/SmoothLocusBaseChange.lean`, PR #76) to the **scheme level on the affine base-change
square**, using the affine bridge `Belyi.mem_smoothLocus_specMap_iff`
(`Belyi/AffineSmoothLocus.lean`, PR #79).

For a module-finite characteristic-zero domain extension `A → B` (`A` Noetherian) and a flat
characteristic-zero domain `A → A'`, the base-change square of affine schemes
```
  Spec (A' ⊗[A] B) --Spec.map (B → A'⊗B)--> Spec B
        |                                      |
  Spec.map (A' → A'⊗B)                  Spec.map (A → B)
        v                                      v
      Spec A'  ----------Spec.map (A → A')---> Spec A
```
has its smooth locus satisfy the **reverse (descent) inclusion**
```
  (Spec.map (A' → A' ⊗[A] B)).smoothLocus ⊆
    (Spec.map (B → A' ⊗[A] B)).base ⁻¹' (Spec.map (A → B)).smoothLocus,
```
the scheme-level analogue of the ring statement. Combined with the already-merged forward
inclusion `Belyi.smoothLocus_preimage_subset` (`Belyi/RamificationBaseChange.lean`) — once the
concrete pullback square is identified with this `Spec`-of-tensor-product square via
`pullbackSpecIso` — this yields the scheme-level equality `Ram f' = pr⁻¹ (Ram f)` of B2b (#168)
that the B3d branch-locus matching (#48) and the converse direction (#53) consume.

## Main result

* `Belyi.smoothLocus_specMap_baseChange_subset` — the reverse inclusion of the scheme smooth
  locus under the affine base-change square.
-/

open AlgebraicGeometry CategoryTheory TensorProduct

namespace Belyi

universe u

/-- **Reverse (descent) inclusion of the scheme smooth locus, affine base-change square.**

For `A → B` a module-finite extension of characteristic-zero integral domains with `A` Noetherian
and `A ↪ B`, `A → A'` flat with `A'` a characteristic-zero integral domain, and `A' ⊗[A] B` again an
integral domain with `A' ↪ A' ⊗[A] B`, a point of `Spec (A' ⊗[A] B)` in the scheme smooth locus of
the base change `Spec.map (A' → A' ⊗[A] B)` maps, under `Spec.map (B → A' ⊗[A] B)`, into the scheme
smooth locus of `Spec.map (A → B)`.

The scheme-level lift of the ring statement `Belyi.smoothLocus_baseChange_subset` (#76): apply the
affine bridge `mem_smoothLocus_specMap_iff` on both `Spec.map`s to pass to `Algebra.smoothLocus`,
run the ring descent, and identify the point map of `Spec.map (B → A' ⊗[A] B)` with
`PrimeSpectrum.comap (algebraMap B (A' ⊗[A] B))`. -/
theorem smoothLocus_specMap_baseChange_subset
    {A A' B : Type u} [CommRing A] [IsDomain A] [CharZero A] [IsNoetherianRing A]
    [CommRing A'] [IsDomain A'] [CharZero A'] [Algebra A A'] [Module.Flat A A']
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Module.Finite A B]
    [IsDomain (A' ⊗[A] B)] [FaithfulSMul A' (A' ⊗[A] B)]
    [LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    [LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] B))))] :
    letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    (((Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] B)))).smoothLocus :
        Set (Spec (CommRingCat.of (A' ⊗[A] B)))) ⊆
      (Spec.map (CommRingCat.ofHom (algebraMap B (A' ⊗[A] B)))).base ⁻¹'
        ((Spec.map (CommRingCat.ofHom (algebraMap A B))).smoothLocus :
          Set (Spec (CommRingCat.of B)))) := by
  letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  intro x hx
  -- Affine bridge on the base change `A' → A' ⊗[A] B`.
  have h1 : x ∈ Algebra.smoothLocus A' (A' ⊗[A] B) :=
    (mem_smoothLocus_specMap_iff (R := A') (S := A' ⊗[A] B) x).mp hx
  -- Ring-level descent (PR #76).
  have h2 := smoothLocus_baseChange_subset (A := A) (A' := A') (B := B) h1
  rw [Set.mem_preimage] at h2
  -- Affine bridge on `A → B` (reverse direction), at the image prime `comap (B → A'⊗B) x`.
  have h3 : PrimeSpectrum.comap (algebraMap B (A' ⊗[A] B)) x ∈
      (Spec.map (CommRingCat.ofHom (algebraMap A B))).smoothLocus :=
    (mem_smoothLocus_specMap_iff (R := A) (S := B) _).mpr h2
  -- The point map of `Spec.map (B → A'⊗B)` is `PrimeSpectrum.comap` of the ring map.
  rw [Set.mem_preimage]
  exact h3

end Belyi
