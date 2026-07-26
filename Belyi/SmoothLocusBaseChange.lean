/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.EtaleLocusBaseChange
import Belyi.SmoothLocusEtaleLocus

/-!
# Base change of the smooth locus (descent inclusion — ring level, #168 piece (2))

This file combines the two ring-level cores of issue #168 —

* `Belyi.etaleLocus_baseChange_subset` (`Belyi/EtaleLocusBaseChange.lean`, PR #74): the reverse
  (descent) inclusion of the **étale** locus under base change, and
* `Belyi.smoothLocus_eq_etaleLocus_of_finite_charZero` (`Belyi/SmoothLocusEtaleLocus.lean`,
  PR #75): the identification of the smooth and étale loci for a finite characteristic-zero
  domain extension —

into the reverse inclusion of the **smooth** locus under base change:

```
Algebra.smoothLocus A' (A' ⊗[A] B) ⊆ comap (B → A' ⊗[A] B)⁻¹ (Algebra.smoothLocus A B).
```

This is the ring-level content that the scheme-level statement `Ram (f') = pr⁻¹ (Ram f)` of B2b
(#168) reduces to for a finite morphism, `Ram` being the complement of the smooth locus. The
smooth locus (not the étale locus) is the relevant object because `Scheme.Hom.smoothLocus` — hence
`Ram` — is defined pointwise through formal *smoothness* of the stalk map; there is no scheme-side
`etaleLocus`. The équality of smooth loci under base change then follows by combining this reverse
inclusion with the already-merged forward inclusion (`Belyi.smoothLocus_preimage_subset`).

## Hypotheses

The union of the hypotheses of the two inputs, plus the domain/characteristic-zero data on the
base-changed side that the smooth = étale bridge needs on `A' → A' ⊗[A] B`:

* `A` : a Noetherian characteristic-zero integral domain, `A → B` module-finite with `A ↪ B`
  (`FaithfulSMul`) and finitely presented (automatic over the Noetherian `A`);
* `A'` : a characteristic-zero integral domain, flat over `A` (a field extension `A → A'` is the
  intended case);
* `A' ⊗[A] B` : an integral domain with `A' ↪ A' ⊗[A] B` (geometric integrality of the base change,
  the scheme-side `GeometricallyIntegral` hypothesis of `IsCurveOver`).

## Main result

* `Belyi.smoothLocus_baseChange_subset` — the reverse inclusion of the smooth locus under base
  change.
-/

open TensorProduct

namespace Belyi

universe u

/-- **Reverse (descent) inclusion of the smooth locus under base change, ring level.**

For `A → B` a module-finite extension of characteristic-zero integral domains with `A` Noetherian
and `A ↪ B`, `A → A'` flat with `A'` a characteristic-zero integral domain, and `A' ⊗[A] B` again
an integral domain with `A' ↪ A' ⊗[A] B`, a prime of `A' ⊗[A] B` at which the base change
`A' → A' ⊗[A] B` is smooth lies over a prime of `B` at which `A → B` is smooth.

Assembly: rewrite the smooth locus as the étale locus on both sides via
`smoothLocus_eq_etaleLocus_of_finite_charZero` (finite characteristic-zero domain extensions
`A' → A' ⊗[A] B` and `A → B`), then apply the étale-locus descent
`etaleLocus_baseChange_subset`. -/
theorem smoothLocus_baseChange_subset
    {A A' B : Type u} [CommRing A] [IsDomain A] [CharZero A] [IsNoetherianRing A]
    [CommRing A'] [IsDomain A'] [CharZero A'] [Algebra A A'] [Module.Flat A A']
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Module.Finite A B]
    [IsDomain (A' ⊗[A] B)] [FaithfulSMul A' (A' ⊗[A] B)] :
    letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    Algebra.smoothLocus A' (A' ⊗[A] B) ⊆
      PrimeSpectrum.comap (algebraMap B (A' ⊗[A] B)) ⁻¹' Algebra.smoothLocus A B := by
  letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  -- `A → B` finitely presented over the Noetherian `A`.
  haveI : Algebra.FinitePresentation A B :=
    (Algebra.FinitePresentation.of_finiteType (R := A) (A := B)).mp inferInstance
  -- `A' → A' ⊗[A] B` is module-finite (base change of the finite `A → B`).
  haveI : Module.Finite A' (A' ⊗[A] B) := inferInstance
  -- Smooth = étale on both finite characteristic-zero domain extensions.
  rw [Belyi.smoothLocus_eq_etaleLocus_of_finite_charZero (R := A') (S := A' ⊗[A] B),
    Belyi.smoothLocus_eq_etaleLocus_of_finite_charZero (R := A) (S := B)]
  exact Belyi.etaleLocus_baseChange_subset

end Belyi
