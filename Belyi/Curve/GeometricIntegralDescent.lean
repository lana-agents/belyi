/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Belyi.Definable

/-!
# Descent of geometric integrality along a field extension

This file provides the geometric-integrality half of the descent step **B3c** (taxis #167,
child #204): if the base change `X₀ ×_{Spec k} Spec K` of a scheme `X₀ / k` along a field
extension `k ⊆ K` is geometrically integral over `K`, then `X₀` is geometrically integral
over `k`.

The mathematical content is packaged as two reusable statements:

* `AlgebraicGeometry.IsIntegral.of_flat_surjective`: integrality of the source of a flat
  surjective morphism of schemes descends to the target. (Reducedness descends because the
  stalk maps are faithfully flat, hence injective; irreducibility descends because a
  surjective continuous image of an irreducible space is irreducible.)
* `Belyi.geometricallyIntegral_of_baseChange`: geometric integrality of the base change of
  `X₀ / k` along `k ⊆ K` descends to `X₀ / k`. Given a field `L / k` to test against, one
  builds a common field extension `M` of `L` and `K` over `k` (a residue field of the
  tensor product `L ⊗[k] K`); the fibre `X₀ ×_k L` becomes integral after base change to
  `M`, and integrality then descends from `X₀ ×_k M` to `X₀ ×_k L` by
  `IsIntegral.of_flat_surjective`.
-/

universe u

open CategoryTheory Limits MorphismProperty TensorProduct

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **Integrality descends along a flat surjective morphism of schemes.** If `p : X ⟶ Y` is
flat and surjective and `X` is integral, then `Y` is integral.

Reducedness descends because each stalk map `𝒪_{Y, p x} ⟶ 𝒪_{X, x}` is a flat local
homomorphism of local rings, hence faithfully flat and injective, so a reduced stalk of `X`
forces the corresponding stalk of `Y` to be reduced. Irreducibility descends because `Y` is
the continuous surjective image of the irreducible space `X`. -/
theorem IsIntegral.of_flat_surjective (p : X ⟶ Y) [Flat p] [Surjective p] [IsIntegral X] :
    IsIntegral Y := by
  have hsurj : Function.Surjective p.base := ‹Surjective p›.surj
  haveI : Nonempty X := IrreducibleSpace.toNonempty
  -- `Y` is irreducible: it is the surjective continuous image of the irreducible space `X`.
  haveI : IrreducibleSpace Y := by
    have himg : p.base '' Set.univ = Set.univ := by
      rw [Set.image_univ, Set.range_eq_univ.mpr hsurj]
    have hpre : IsPreirreducible (Set.univ : Set Y) := by
      have := (PreirreducibleSpace.isPreirreducible_univ (X := X)).image p.base
        p.continuous.continuousOn
      rwa [himg] at this
    exact { toPreirreducibleSpace := ⟨hpre⟩, toNonempty := ⟨p.base (Classical.arbitrary X)⟩ }
  -- `Y` is reduced: each stalk map is faithfully flat, hence injective.
  haveI : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    algebraize [(p.stalkMap x).hom]
    have : Module.FaithfullyFlat (Y.presheaf.stalk (p.base x)) (X.presheaf.stalk x) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap p x) (p.toLRSHom.prop x)
    exact isReduced_of_injective (p.stalkMap x).hom ‹RingHom.FaithfullyFlat _›.injective
  haveI : IsReduced Y := isReduced_of_isReduced_stalk (X := Y)
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) (IsIntegral ·) :=
  ⟨fun e hX => by haveI := hX; exact IsIntegral.of_isIso e.hom⟩

end AlgebraicGeometry

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- **Descent of geometric integrality along a field extension** (part of B3c, taxis #204).
If the base change of `X₀ / k` along a field extension `k ⊆ K` is geometrically integral over
`K`, then `X₀` is geometrically integral over `k`.

Given a field `L / k` to test against, one forms a common extension `M` of `L` and `K` over `k`
(a residue field of `L ⊗[k] K`). The fibre `X₀ ×_k L` becomes integral after base change to `M`
(via the `K`-side hypothesis), and integrality then descends from `X₀ ×_k M` to `X₀ ×_k L` along
the faithfully flat `Spec M ⟶ Spec L` by `AlgebraicGeometry.IsIntegral.of_flat_surjective`. -/
theorem geometricallyIntegral_of_baseChange (X₀ : Scheme.{u})
    [X₀.Over (Spec (CommRingCat.of k))]
    (h : GeometricallyIntegral
      (pullback.snd (X₀ ↘ Spec (CommRingCat.of k)) (specAlgebraMap k K))) :
    GeometricallyIntegral (X₀ ↘ Spec (CommRingCat.of k)) := by
  set f₀ : X₀ ⟶ Spec (CommRingCat.of k) := X₀ ↘ Spec (CommRingCat.of k) with hf₀
  rw [geometricallyIntegral_iff] at h ⊢
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms] at h ⊢
  intro L _ _
  -- The common field `M`: a residue field of the tensor product `L ⊗[k] K`.
  haveI hT : Nontrivial (L ⊗[k] K) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (L ⊗[k] K)
  letI M := (L ⊗[k] K) ⧸ m
  letI : Field M := Ideal.Quotient.field m
  -- The two structure maps `L ⟶ M` and `K ⟶ M`.
  letI incL : L →ₐ[k] (L ⊗[k] K) := Algebra.TensorProduct.includeLeft
  letI incR : K →ₐ[k] (L ⊗[k] K) := Algebra.TensorProduct.includeRight
  letI a : L →+* M := (Ideal.Quotient.mk m).comp incL.toRingHom
  letI b : K →+* M := (Ideal.Quotient.mk m).comp incR.toRingHom
  letI : Algebra L M := a.toAlgebra
  letI : Algebra K M := b.toAlgebra
  -- Compatibility of the two structure maps over `k`.
  have ha_hb : a.comp (algebraMap k L) = b.comp (algebraMap k K) := by
    ext c
    change (Ideal.Quotient.mk m) (incL (algebraMap k L c)) =
      (Ideal.Quotient.mk m) (incR (algebraMap k K c))
    rw [incL.commutes, incR.commutes]
  -- `w = Spec M ⟶ Spec L` and `z = Spec M ⟶ Spec K`, agreeing over `Spec k`.
  have hcompat : specAlgebraMap L M ≫ specAlgebraMap k L =
      specAlgebraMap K M ≫ specAlgebraMap k K := by
    rw [specAlgebraMap, specAlgebraMap, specAlgebraMap, specAlgebraMap, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    change Spec.map (CommRingCat.ofHom (a.comp (algebraMap k L))) =
      Spec.map (CommRingCat.ofHom (b.comp (algebraMap k K)))
    rw [ha_hb]
  -- Integrality of the base change to `M`, from the `K`-side hypothesis.
  have hInt : IsIntegral (pullback (pullback.snd f₀ (specAlgebraMap k K)) (specAlgebraMap K M)) :=
    h M
  -- Transport it, via the pasting isomorphisms and the compatibility, to a base change of
  -- `X₀ ×_k L` along `Spec M ⟶ Spec L`.
  have E : pullback (pullback.snd f₀ (specAlgebraMap k K)) (specAlgebraMap K M) ≅
      pullback (pullback.snd f₀ (specAlgebraMap k L)) (specAlgebraMap L M) :=
    pullbackLeftPullbackSndIso f₀ (specAlgebraMap k K) (specAlgebraMap K M) ≪≫
      pullback.congrHom rfl hcompat.symm ≪≫
      (pullbackLeftPullbackSndIso f₀ (specAlgebraMap k L) (specAlgebraMap L M)).symm
  have hInt2 : IsIntegral (pullback (pullback.snd f₀ (specAlgebraMap k L)) (specAlgebraMap L M)) :=
    IsIntegral.of_isIso E.hom
  -- `Spec M ⟶ Spec L` is faithfully flat, so integrality descends.
  haveI : Module.FaithfullyFlat L M := inferInstance
  have hff : (algebraMap L M).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  obtain ⟨hflat, hsurj⟩ :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap L M))).mpr hff
  have hpf : Flat
      (pullback.fst (pullback.snd f₀ (specAlgebraMap k L)) (specAlgebraMap L M)) :=
    MorphismProperty.pullback_fst _ _ hflat
  have hps : Surjective
      (pullback.fst (pullback.snd f₀ (specAlgebraMap k L)) (specAlgebraMap L M)) :=
    MorphismProperty.pullback_fst _ _ hsurj
  exact @IsIntegral.of_flat_surjective _ _
    (pullback.fst (pullback.snd f₀ (specAlgebraMap k L)) (specAlgebraMap L M)) hpf hps hInt2

end Belyi
