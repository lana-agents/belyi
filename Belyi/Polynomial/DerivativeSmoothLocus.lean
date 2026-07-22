/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Smooth.Locus

/-!
# The derivative-away locus of a monic quotient is smooth

For a commutative ring `R` and a monic polynomial `f : R[X]`, the algebra
`AdjoinRoot f = R[X] ⧸ (f)` is smooth over `R` at every prime avoiding the image of the
derivative `f'`.  Equivalently, the basic open `D(f')` of `Spec (AdjoinRoot f)` is contained
in the smooth locus `Algebra.smoothLocus R (AdjoinRoot f)`.

This is the pure ring-theoretic core of statement **B4** in `references/proof-outline.md`
(the branch locus of the polynomial self-map of `ℙ¹` is the set of critical values): away from
the vanishing of the derivative, the map `x ↦ g(x)` is étale.  Concretely, presenting the
affine chart map `k[y] → k[x]`, `y ↦ g(x)` as `k[y] → AdjoinRoot (g(X) - y)`, this lemma shows
the chart is smooth at every point where `g'` does not vanish; the bridge from here to the
scheme-level `Scheme.Hom.smoothLocus` of the `ℙ¹` self-map lives downstream.

The proof packages `(f, f')` as a `StandardEtalePair` — the standard-étale condition
`∃ p₁ p₂ n, f' · p₁ + f · p₂ = (f')^n` holds trivially with `p₁ = 1`, `p₂ = 0`, `n = 1` — whose
associated algebra `R[X][Y]/⟨f, Y·f' − 1⟩` is unconditionally étale over `R` and identified by
`StandardEtalePair.equivAwayAdjoinRoot` with `(AdjoinRoot f)[1/f']`.  Étale ⇒ smooth, and
`Algebra.basicOpen_subset_smoothLocus_iff_smooth` turns smoothness of the localization into the
locus inclusion.
-/

open Polynomial

namespace Belyi

variable {R : Type*} [CommRing R]

/-- For a monic `f : R[X]`, the localization of `AdjoinRoot f` away from the image of the
derivative `f'` is smooth over `R`: it is the standard-étale algebra attached to the pair
`(f, f')`, whose standard-étale condition holds trivially since `f' = (f')^1`. -/
theorem smooth_localizationAway_mk_derivative {f : R[X]} (hf : f.Monic) :
    Algebra.Smooth R (Localization.Away (AdjoinRoot.mk f (derivative f))) :=
  let P : StandardEtalePair R := ⟨f, hf, derivative f, ⟨1, 0, 1, by ring⟩⟩
  Algebra.Smooth.of_equiv P.equivAwayAdjoinRoot

/-- **B4 ring-core.**  For a monic polynomial `f : R[X]`, the basic open of the image of the
derivative `f'` in `AdjoinRoot f = R[X]/(f)` is contained in the smooth locus of `AdjoinRoot f`
over `R`.  In other words `AdjoinRoot f` is smooth over `R` at every prime not containing `f'`. -/
theorem basicOpen_mk_derivative_subset_smoothLocus {f : R[X]} (hf : f.Monic) :
    (PrimeSpectrum.basicOpen (AdjoinRoot.mk f (derivative f))
        : Set (PrimeSpectrum (AdjoinRoot f)))
      ⊆ Algebra.smoothLocus R (AdjoinRoot f) := by
  rw [Algebra.basicOpen_subset_smoothLocus_iff_smooth]
  exact smooth_localizationAway_mk_derivative hf

end Belyi
