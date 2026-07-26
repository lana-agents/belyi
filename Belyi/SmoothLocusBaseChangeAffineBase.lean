/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.SmoothLocusSpecBaseChange

/-!
# Scheme-level smooth-locus base change for a finite morphism over an affine base (#168 piece (2b))

This file generalises the affine `Spec.map`-square result
`Belyi.smoothLocus_specMap_baseChange_eq` (`Belyi/SmoothLocusSpecBaseChange.lean`, PR #81), in
which the total space is literally `Spec B`, to a **general finite morphism**
`f : X ⟶ Spec (CommRingCat.of A)` whose source `X` is affine, base changed along the affine flat
leg `q = Spec.map (algebraMap A A')`:

```
  pullback f q --pullback.fst--> X
   pullback.snd |               | f
        Spec A' -------q------> Spec (CommRingCat.of A)
```

The source `X` is presented as `Spec (CommRingCat.of B)` through an isomorphism `e : X ≅ Spec B`
identifying `f` with `Spec.map (algebraMap A B)` (hypothesis `he`), where `B` carries the
char-0/domain/finite/flat data required by #81. Transporting the affine-square equality across the
isomorphisms `e`, `pullbackSymmetry` and `pullbackSpecIso` (which identify `pullback f q` with
`Spec (A' ⊗[A] B)`) gives the smooth-locus equality, and hence the ramification-locus equality, for
the categorical pullback square.

## Main results

* `Belyi.smoothLocus_baseChange_affineBase_eq` —
  `(pullback.snd f q).smoothLocus = pullback.fst f q ⁻¹ᵁ f.smoothLocus`.
* `Belyi.ram_baseChange_affineBase_eq` —
  `Ram (pullback.snd f q) = pullback.fst f q ⁻¹' Ram f`.
-/

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace Belyi

universe u

section

variable {A A' B : Type u} [CommRing A] [IsDomain A] [CharZero A] [IsNoetherianRing A]
  [CommRing A'] [IsDomain A'] [CharZero A'] [Algebra A A'] [Module.Flat A A']
  [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Module.Finite A B]
  [IsDomain (A' ⊗[A] B)] [FaithfulSMul A' (A' ⊗[A] B)]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFinitePresentation f]

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

/-- The base change `pullback.snd f q` of the locally-of-finite-presentation `f` along the affine
leg `q = Spec.map (algebraMap A A')` is again locally of finite presentation. -/
private instance : LocallyOfFinitePresentation
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A A')))) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- Equal morphisms have equal smooth loci. -/
private lemma smoothLocus_congr {Y Z : Scheme.{u}} {g h : Y ⟶ Z}
    [LocallyOfFinitePresentation g] [LocallyOfFinitePresentation h] (hgh : g = h) :
    g.smoothLocus = h.smoothLocus := by
  subst hgh; rfl

/-- **Scheme-level equality of smooth loci under base change over an affine base.** For a finite
morphism `f : X ⟶ Spec A` with affine source `X ≅ Spec B` identifying `f` with
`Spec.map (algebraMap A B)` (the char-0/domain/finite/flat data of #81 living on `A, A', B`), and
the affine flat leg `q = Spec.map (algebraMap A A')`, the smooth locus of the base change
`pullback.snd f q` equals the `pullback.fst f q`-preimage of the smooth locus of `f`.

This is obtained by transporting the affine `Spec.map`-square equality
`Belyi.smoothLocus_specMap_baseChange_eq` (#81) across the isomorphisms `e`, `pullbackSymmetry` and
`pullbackSpecIso`, which together identify `pullback f q` with `Spec (A' ⊗[A] B)`. -/
theorem smoothLocus_baseChange_affineBase_eq
    (e : X ≅ Spec (CommRingCat.of B))
    (he : f = e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) :
    ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A A')))).smoothLocus :
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A A')))).Opens) =
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A A')))) ⁻¹ᵁ f.smoothLocus := by
  letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  -- The comparison iso `pullback f q ≅ pullback mB q` coming from `f = e.hom ≫ mB`.
  set μ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom (algebraMap A A'))) :=
    pullback.map f (Spec.map (CommRingCat.ofHom (algebraMap A A')))
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A A'))) e.hom (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id]; exact he) (by simp) with hμ
  haveI : IsIso μ := by rw [hμ]; exact inferInstance
  have hμ_fst : μ ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A A')))
      = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ≫ e.hom := by
    rw [hμ]; exact pullback.lift_fst _ _ _
  have hμ_snd : μ ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A A')))
      = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A A'))) := by
    rw [hμ, pullback.lift_snd, Category.comp_id]
  -- The full comparison iso `Φ : pullback f q ≅ Spec (A' ⊗[A] B)`.
  set Φ : pullback f (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ≅
      Spec (CommRingCat.of (A' ⊗[A] B)) :=
    asIso μ ≪≫ pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ≪≫ pullbackSpecIso A A' B with hΦ
  -- The `pullbackSpecIso` projection identities.
  have hpsi_fst : (pullbackSpecIso A A' B).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] B))) = pullback.fst _ _ :=
    pullbackSpecIso_hom_fst' A A' B
  have hpsi_snd : (pullbackSpecIso A A' B).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap B (A' ⊗[A] B))) = pullback.snd _ _ :=
    pullbackSpecIso_hom_snd A A' B
  -- `Φ.hom` intertwines `pullback.snd f q` with the base-change projection `f'`.
  have hI : Φ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] B)))
      = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A A'))) := by
    simp only [hΦ, Iso.trans_hom, asIso_hom, Category.assoc, hpsi_fst,
      pullbackSymmetry_hom_comp_fst, hμ_snd]
  -- `Φ.hom` intertwines `pullback.fst f q ≫ e.hom` with the projection `pr`.
  have hII : Φ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B (A' ⊗[A] B)))
      = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ≫ e.hom := by
    simp only [hΦ, Iso.trans_hom, asIso_hom, Category.assoc, hpsi_snd,
      pullbackSymmetry_hom_comp_snd, hμ_fst]
  have hII' : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A A')))
      = Φ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B (A' ⊗[A] B))) ≫ e.inv := by
    rw [← Category.assoc, hII, Category.assoc, e.hom_inv_id, Category.comp_id]
  -- `f`'s smooth locus is the `e.hom`-preimage of `mB`'s smooth locus.
  have hfsl : f.smoothLocus =
      e.hom ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap A B))).smoothLocus := by
    rw [smoothLocus_congr he, ← Scheme.Hom.preimage_smoothLocus_eq e.hom]
  -- `e.inv ⁻¹ᵁ e.hom ⁻¹ᵁ` cancels.
  have hee : ∀ U : (Spec (CommRingCat.of B)).Opens, e.inv ⁻¹ᵁ (e.hom ⁻¹ᵁ U) = U := fun U => by
    rw [← Scheme.Hom.comp_preimage, e.inv_hom_id, Scheme.Hom.id_preimage]
  -- The affine `Spec.map`-square equality from #81 (as an equality of opens).
  have h81 : (Spec.map (CommRingCat.ofHom (algebraMap A' (A' ⊗[A] B)))).smoothLocus =
      Spec.map (CommRingCat.ofHom (algebraMap B (A' ⊗[A] B))) ⁻¹ᵁ
        (Spec.map (CommRingCat.ofHom (algebraMap A B))).smoothLocus :=
    TopologicalSpace.Opens.ext smoothLocus_specMap_baseChange_eq
  -- Both sides reduce to `Φ.hom ⁻¹ᵁ (pr ⁻¹ᵁ mB.smoothLocus)`.
  have hLHS : (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A A')))).smoothLocus =
      Φ.hom ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap B (A' ⊗[A] B))) ⁻¹ᵁ
        (Spec.map (CommRingCat.ofHom (algebraMap A B))).smoothLocus) := by
    rw [smoothLocus_congr hI.symm, ← Scheme.Hom.preimage_smoothLocus_eq Φ.hom, h81]
  have hRHS : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ⁻¹ᵁ f.smoothLocus =
      Φ.hom ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap B (A' ⊗[A] B))) ⁻¹ᵁ
        (Spec.map (CommRingCat.ofHom (algebraMap A B))).smoothLocus) := by
    rw [hII', Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, hfsl, hee]
  rw [hLHS, hRHS]

/-- **Ramification-locus equality under base change over an affine base.**
`Ram (pullback.snd f q) = pullback.fst f q ⁻¹' Ram f`, obtained by taking complements in
`smoothLocus_baseChange_affineBase_eq`. -/
theorem ram_baseChange_affineBase_eq
    (e : X ≅ Spec (CommRingCat.of B))
    (he : f = e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) :
    Ram (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A A')))) =
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A A')))) ⁻¹'
        Ram f := by
  rw [Ram, Ram, Set.preimage_compl, ← Scheme.Hom.coe_preimage,
    ← smoothLocus_baseChange_affineBase_eq f e he]

end

end Belyi
