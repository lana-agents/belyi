/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Extension.Cotangent.BaseChange
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Base change of the étale locus (descent inclusion — ring-level core of B2b #168)

This file provides the **reverse (descent) inclusion** of the base-change compatibility of the
étale locus, at the ring level. It is the reusable mathematical core needed for issue #168
(`Ram (f') = pr⁻¹ (Ram f)` under base change), and it deliberately **sidesteps** the
`proof_wanted Algebra.FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat`
(`Mathlib/RingTheory/Etale/Descent.lean:56`) that earlier analyses of #168 pinned as an
impassable wall.

## Key idea (why the FormallySmooth ff-descent wall is avoidable)

For a **finite** (rel. dim. 0) morphism the ramification locus is the complement of the étale
locus, and mathlib characterises the étale locus purely through the **supports of `Ω` and
`H¹Cotangent`**:

* `Algebra.etaleLocus_eq_compl_support` :
  `etaleLocus R A = (support A Ω[A⁄R])ᶜ ∩ (support A (H1Cotangent R A))ᶜ`.

Both `Ω` and `H¹Cotangent` base-change compatibly:

* `KaehlerDifferential.tensorKaehlerEquiv` : `B' ⊗[B] Ω[B⁄A] ≃ₗ[B'] Ω[B'⁄A']` (a pushout iso,
  needs no flatness);
* `Algebra.tensorH1CotangentOfFlat` : `A' ⊗[A] H1Cotangent A B ≃ₗ H1Cotangent A' B'` (needs
  `A → A'` flat).

and the *support* of a base-changed finite module ascends along `comap`
(`comap_support_subset_support_baseChange` below). Chaining these gives the reverse inclusion
`etaleLocus A' B' ⊆ comap⁻¹ (etaleLocus A B)`.

The flatness of `A → A'` holds for a field extension `k ⊆ K` (the case #168 needs), where
`A' = K ⊗_k A`.

## Main results

* `Belyi.comap_support_subset_support_baseChange` — support ascends under base change.
* `Belyi.etaleLocus_baseChange_subset` — the reverse inclusion of the étale locus.
-/

open TensorProduct

namespace Belyi

universe u

/-- **Support ascends under base change.** For a ring map `B → B'` and a finite `B`-module `M`,
the preimage under `comap (B → B')` of `Module.support B M` is contained in
`Module.support B' (B' ⊗[B] M)`.

Proof sketch: `p' ∈ support B' (B'⊗M) ↔ Nontrivial (κ(p') ⊗_{B'} (B'⊗M)) = Nontrivial (κ(p') ⊗_B M)`
via `Module.mem_support_iff_nontrivial_residueField_tensorProduct` and `cancelBaseChange`; and
`κ(p') ⊗_B M = κ(p') ⊗_{κ(p)} (κ(p) ⊗_B M)` where `p = comap p'`, with `κ(p) → κ(p')` a field
extension (faithfully flat), so nontriviality of `κ(p) ⊗_B M` (i.e. `p ∈ support B M`) transfers
up. -/
lemma comap_support_subset_support_baseChange
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra B B']
    (M : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M] :
    PrimeSpectrum.comap (algebraMap B B') ⁻¹' Module.support B M ⊆
      Module.support B' (B' ⊗[B] M) := by
  intro p' hp'
  rw [Set.mem_preimage, Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp'
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
  -- `κ` = residue field of `p := comap p'` (a `B`-algebra); `K` = residue field of `p'`.
  -- The residue-field functoriality gives a ring hom `g : κ → K`; make `K` a `κ`-algebra
  -- and a `B`-algebra compatibly.
  -- Mathlib already provides the natural `Algebra B K` and `IsScalarTower B B' K`
  -- (via `IsLocalRing.instIsScalarTowerResidueField`); we only add the `κ`-algebra structure
  -- on `K` from residue-field functoriality, and the compatible tower `B → κ → K`.
  letI g : (PrimeSpectrum.comap (algebraMap B B') p').asIdeal.ResidueField →+*
      p'.asIdeal.ResidueField :=
    Ideal.ResidueField.map _ p'.asIdeal (algebraMap B B') rfl
  letI : Algebra (PrimeSpectrum.comap (algebraMap B B') p').asIdeal.ResidueField
      p'.asIdeal.ResidueField := g.toAlgebra
  haveI : IsScalarTower B (PrimeSpectrum.comap (algebraMap B B') p').asIdeal.ResidueField
      p'.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun b =>
      (IsScalarTower.algebraMap_apply B B' p'.asIdeal.ResidueField b).trans
        (Ideal.ResidueField.map_algebraMap _ p'.asIdeal (algebraMap B B') rfl b).symm
  -- `Nontrivial (κ ⊗[B] M)` is exactly the hypothesis `p ∈ support B M`.
  haveI : Nontrivial ((PrimeSpectrum.comap (algebraMap B B') p').asIdeal.ResidueField ⊗[B] M) := hp'
  -- `K ⊗[B'] (B' ⊗[B] M) ≃ₗ[K] K ⊗[B] M ≃ₗ[K] K ⊗[κ] (κ ⊗[B] M)`, and the last is nontrivial
  -- since `K` is a nontrivial free (hence faithfully flat) `κ`-vector space.
  have e1 := AlgebraTensorModule.cancelBaseChange B B' p'.asIdeal.ResidueField
      p'.asIdeal.ResidueField M
  have e2 := AlgebraTensorModule.cancelBaseChange B
      (PrimeSpectrum.comap (algebraMap B B') p').asIdeal.ResidueField
      p'.asIdeal.ResidueField p'.asIdeal.ResidueField M
  rw [e1.nontrivial_congr, ← e2.nontrivial_congr]
  infer_instance

/-- Over a Noetherian base, `H1Cotangent` of a finitely presented algebra is a finite module.
This bypasses the mathlib instance (`Extension/Cotangent/Basic.lean:624`), which requires
`Module.Projective B Ω[B⁄A]`; here `B` is Noetherian (as `A` is Noetherian and `B` is of finite
type over `A`), so the subquotient `H1Cotangent A B` of the finite `Cotangent` module is finite. -/
private lemma finite_h1Cotangent_of_noetherian
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FinitePresentation A B] :
    Module.Finite B (Algebra.H1Cotangent A B) := by
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let P := Algebra.Presentation.ofFinitePresentation A B
  haveI : Module.Finite B P.toExtension.Cotangent := Algebra.Extension.Cotangent.finite P.fg_ker
  haveI : Module.Finite B P.toExtension.H1Cotangent :=
    Module.Finite.of_injective P.toExtension.h1Cotangentι P.toExtension.h1Cotangentι_injective
  exact Module.Finite.of_surjective P.equivH1Cotangent.toLinearMap P.equivH1Cotangent.surjective

/-- **Reverse (descent) inclusion of B2b for the étale locus, ring level.**

Let `A → B` be a finitely presented algebra with `A` Noetherian, `A → A'` flat, and
`B' := A' ⊗[A] B` (a `B`-algebra via the canonical `rightAlgebra`, an `A'`-algebra via
`leftAlgebra`). Then `etaleLocus A' B' ⊆ comap (B → B')⁻¹ (etaleLocus A B)`: a prime at which the
base change is étale lies over a prime at which the original is étale.

Combined with the already-merged forward inclusion (`Belyi.smoothLocus_preimage_subset`) this gives
the equality of étale loci under base change; specialised to a field extension `A' = K ⊗_k A` it is
the ring-level content that `Ram (f') = pr⁻¹ (Ram f)` (#168) reduces to for a finite morphism.

Assembly:
* `Algebra.etaleLocus_eq_compl_support` on both sides reduces the goal to two support-ascent
  inclusions (for `Ω` and for `H1Cotangent`);
* `KaehlerDifferential.tensorKaehlerEquiv A A' B B' : B' ⊗[B] Ω[B⁄A] ≃ₗ[B'] Ω[B'⁄A']` (a pushout
  iso, no flatness) transports the `Ω` support;
* `Algebra.tensorH1CotangentOfFlat A B A'` (needs `Module.Flat A A'`) transported to a `B'`-linear
  map on `B' ⊗[B] H1Cotangent A B` transports the `H1Cotangent` support;
* `comap_support_subset_support_baseChange` for `M = Ω[B⁄A]` and `M = H1Cotangent A B` (both finite
  `B`-modules: `Ω` since `B` is f.p. over `A`; `H1Cotangent` since `B` is Noetherian, see
  `finite_h1Cotangent_of_noetherian`). -/
theorem etaleLocus_baseChange_subset
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B]
    [IsNoetherianRing A] [Algebra.FinitePresentation A B] [Module.Flat A A'] :
    letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    Algebra.etaleLocus A' (A' ⊗[A] B) ⊆
      PrimeSpectrum.comap (algebraMap B (A' ⊗[A] B)) ⁻¹' Algebra.etaleLocus A B := by
  letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  haveI : Algebra.IsPushout A A' B (A' ⊗[A] B) := TensorProduct.isPushout
  haveI : Module.Finite B (Algebra.H1Cotangent A B) := finite_h1Cotangent_of_noetherian
  -- Support ascent for the Kähler differentials, via `Ω[B'⁄A'] ≃ B' ⊗[B] Ω[B⁄A]`.
  have hΩ : PrimeSpectrum.comap (algebraMap B (A' ⊗[A] B)) ⁻¹' Module.support B Ω[B⁄A]
      ⊆ Module.support (A' ⊗[A] B) Ω[(A' ⊗[A] B)⁄A'] := by
    refine (comap_support_subset_support_baseChange (B' := A' ⊗[A] B) Ω[B⁄A]).trans ?_
    exact Module.support_subset_of_injective
      (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)).toLinearMap
      (KaehlerDifferential.tensorKaehlerEquiv A A' B (A' ⊗[A] B)).injective
  -- Support ascent for `H1Cotangent`. The mathlib base-change equivalence is `A'`-linear; we
  -- transport it to a `B'`-linear map `L` on `B' ⊗[B] H1Cotangent A B` (which computes support
  -- over `B'`) and show `L` is bijective by comparing with the `A'`-linear equivalences.
  let hmap := Algebra.H1Cotangent.map A A' B (A' ⊗[A] B)
  let L := hmap.liftBaseChange (A' ⊗[A] B)
  let cbc := Algebra.IsPushout.cancelBaseChange A A' B (A' ⊗[A] B) (Algebra.H1Cotangent A B)
  have key : (L.restrictScalars A') ∘ₗ cbc.symm.toLinearMap
      = (Algebra.tensorH1CotangentOfFlat A B A').toLinearMap := by
    refine LinearMap.ext fun y => ?_
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a' x =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_restrictScalars,
        cbc, Algebra.IsPushout.cancelBaseChange_symm_tmul, L, hmap,
        LinearMap.liftBaseChange_tmul, Algebra.tensorH1CotangentOfFlat_tmul]
      rw [IsScalarTower.algebraMap_smul]
    | add p q hp hq => simp only [map_add, hp, hq]
  have hfun : ∀ z, L z = Algebra.tensorH1CotangentOfFlat A B A' (cbc z) := by
    intro z
    have := LinearMap.congr_fun key (cbc z)
    simpa using this
  have hbij : Function.Bijective L := by
    have hcomp : (L : _ → _) = (Algebra.tensorH1CotangentOfFlat A B A') ∘ (cbc : _ → _) :=
      funext hfun
    rw [hcomp]
    exact (Algebra.tensorH1CotangentOfFlat A B A').bijective.comp cbc.bijective
  have hH1 : PrimeSpectrum.comap (algebraMap B (A' ⊗[A] B)) ⁻¹'
        Module.support B (Algebra.H1Cotangent A B)
      ⊆ Module.support (A' ⊗[A] B) (Algebra.H1Cotangent A' (A' ⊗[A] B)) := by
    refine (comap_support_subset_support_baseChange (B' := A' ⊗[A] B)
      (Algebra.H1Cotangent A B)).trans ?_
    exact Module.support_subset_of_injective L hbij.injective
  rw [Algebra.etaleLocus_eq_compl_support, Algebra.etaleLocus_eq_compl_support,
    Set.preimage_inter, Set.preimage_compl, Set.preimage_compl]
  exact Set.inter_subset_inter (Set.compl_subset_compl.2 hΩ) (Set.compl_subset_compl.2 hH1)

end Belyi
