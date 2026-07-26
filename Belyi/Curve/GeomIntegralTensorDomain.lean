/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Geometric integrality gives domain base-change of affine sections (#218, B2b support)

This file provides the geometric-integrality → tensor-product-domain bridge that discharges the
`IsDomain (A' ⊗[A] B)` instance required by the affine-base engine
`Belyi.smoothLocus_baseChange_affineBase_eq` / `ram_baseChange_affineBase_eq`
(`Belyi/SmoothLocusBaseChangeAffineBase.lean`, PR #82) when it is applied chart-by-chart to the
`ℙ¹` base-change square (sibling brick #219).

For a scheme `X₀` whose structure morphism `s : X₀ ⟶ Spec k₀` to a field `k₀` is geometrically
integral (`[GeometricallyIntegral s]`, in particular for a curve, `IsCurveOver k₀ X₀`), any field
extension `k₀ ⊆ K`, and an affine open of `X₀` presented as an open immersion
`j : Spec B ⟶ X₀` whose composite with `s` is `Spec.map (algebraMap k₀ B)`, the base change to `K`
of the sections `B` is an integral domain:
```
  IsDomain (K ⊗[k₀] B).
```

## Strategy

`GeometricallyIntegral s` means the base change `Spec K ×_{Spec k₀} X₀` is integral for the field
`K`. The affine open `Spec B ↪ X₀` pulls back to an open subscheme of that integral base change
(`pullbackLeftPullbackSndIso` pastes the affine chart into the field base-change square), and an
open subscheme of an integral scheme is integral. That open subscheme is `Spec (K ⊗[k₀] B)`
(`pullbackSpecIso`), and an affine scheme is integral iff its ring of global sections is a domain
(`AlgebraicGeometry.affine_isIntegral_iff`).

No characteristic-zero hypothesis is needed: the content is pure geometric integrality.

## Main results

* `Belyi.isDomain_tensorProduct_of_geometricallyIntegral` — `IsDomain (K ⊗[k₀] B)`.
* `Belyi.faithfulSMul_tensorProduct_of_geometricallyIntegral` — `FaithfulSMul K (K ⊗[k₀] B)`.
-/

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace Belyi

universe u

variable {k₀ K B : Type u} [Field k₀] [Field K] [Algebra k₀ K]
  [CommRing B] [Algebra k₀ B]
  {X₀ : Scheme.{u}} (s : X₀ ⟶ Spec (CommRingCat.of k₀)) [GeometricallyIntegral s]
  (j : Spec (CommRingCat.of B) ⟶ X₀) [IsOpenImmersion j]
  [Nonempty (Spec (CommRingCat.of B))]
  (hj : j ≫ s = Spec.map (CommRingCat.ofHom (algebraMap k₀ B)))

include s in
/-- The total space of a geometrically integral morphism to `Spec` of a field is integral. -/
private lemma isIntegral_source_of_geometricallyIntegral : IsIntegral X₀ :=
  GeometricallyIntegral.isIntegral_of_subsingleton s

omit [Algebra k₀ B] in
include s j in
/-- The ring of sections `B` on the affine open `Spec B ↪ X₀` is an integral domain. -/
private lemma isDomain_of_geometricallyIntegral : IsDomain B := by
  haveI : IsIntegral X₀ := isIntegral_source_of_geometricallyIntegral s
  haveI : IsIntegral (Spec (CommRingCat.of B)) := isIntegral_of_isOpenImmersion j
  exact (affine_isIntegral_iff (CommRingCat.of B)).mp ‹_›

include s j hj in
/-- **Geometric integrality gives a domain base change of affine sections.** For a geometrically
integral `s : X₀ ⟶ Spec k₀` (field `k₀`), a field extension `k₀ ⊆ K`, and an affine open
`j : Spec B ⟶ X₀` with `j ≫ s = Spec.map (algebraMap k₀ B)`, the base change `K ⊗[k₀] B` is an
integral domain. -/
theorem isDomain_tensorProduct_of_geometricallyIntegral : IsDomain (K ⊗[k₀] B) := by
  -- Abbreviations for the two structure `Spec.map`s.
  set sK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap k₀ K)) with hsK
  set mB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k₀) :=
    Spec.map (CommRingCat.ofHom (algebraMap k₀ B)) with hmB
  -- `B` is a domain, and `K ⊗[k₀] B` is nontrivial.
  haveI : IsDomain B := isDomain_of_geometricallyIntegral s j
  haveI : Nontrivial (K ⊗[k₀] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k₀ K B
      (algebraMap k₀ K).injective (algebraMap k₀ B).injective
  -- The field base change `Spec K ×_{Spec k₀} X₀` is integral.
  haveI hP : IsIntegral (pullback sK s) :=
    AlgebraicGeometry.pullback_of_geometrically'
      (GeometricallyIntegral.geometrically_isIntegral (f := s)) K sK
  -- `W`: the affine open chart of the base change over `Spec B ↪ X₀`.
  set W : Scheme.{u} := pullback (pullback.snd sK s) j with hW
  haveI : IsOpenImmersion (pullback.fst (pullback.snd sK s) j) := inferInstance
  -- `Ψ : W ≅ Spec (K ⊗[k₀] B)`, pasting the chart square then identifying via `pullbackSpecIso`.
  set Ψ : W ≅ Spec (CommRingCat.of (K ⊗[k₀] B)) :=
    pullbackLeftPullbackSndIso sK s j ≪≫ pullback.congrHom rfl hj ≪≫ pullbackSpecIso k₀ K B with hΨ
  -- `W` is nonempty (it is `Spec` of the nontrivial ring `K ⊗[k₀] B`).
  haveI : Nonempty ↥(Spec (CommRingCat.of (K ⊗[k₀] B))) := inferInstance
  haveI : Nonempty W := Nonempty.map Ψ.inv.base inferInstance
  -- Open subscheme of an integral scheme is integral, transported to the affine chart.
  haveI : IsIntegral W := isIntegral_of_isOpenImmersion (pullback.fst (pullback.snd sK s) j)
  haveI : IsIntegral (Spec (CommRingCat.of (K ⊗[k₀] B))) := IsIntegral.of_isIso Ψ.hom
  exact (affine_isIntegral_iff (CommRingCat.of (K ⊗[k₀] B))).mp ‹_›

include s j hj in
/-- **The field base change of affine sections is a faithful `K`-algebra.** Companion to
`isDomain_tensorProduct_of_geometricallyIntegral`: the algebra map `K → K ⊗[k₀] B` is injective. -/
theorem faithfulSMul_tensorProduct_of_geometricallyIntegral :
    FaithfulSMul K (K ⊗[k₀] B) := by
  haveI : IsDomain (K ⊗[k₀] B) := isDomain_tensorProduct_of_geometricallyIntegral s j hj
  exact (faithfulSMul_iff_algebraMap_injective K (K ⊗[k₀] B)).mpr
    (algebraMap K (K ⊗[k₀] B)).injective

end Belyi
