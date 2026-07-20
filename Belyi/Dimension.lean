/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Topology.NoetherianSpace

/-!
# Schemes with one-dimensional stalks

Topological consequences of the hypothesis that the local rings of a scheme have Krull
dimension `≤ 1`, feeding into the finiteness statement of B1 (taxis issue #46):

* on an irreducible such scheme, every non-generic point is closed;
* closed subsets avoiding the generic point are finite (if the space is Noetherian);
* fibers of a closed non-constant morphism out of such a scheme are finite.

The dimension hypothesis is stated stalkwise as `Ring.KrullDimLE 1 (X.presheaf.stalk x)`;
for a smooth curve it will eventually be discharged by "stalks are DVRs or fields"
(remaining part of #46), and `IsDiscreteValuationRing → KrullDimLE 1` is in mathlib.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {X : Scheme.{u}}

/-- In a scheme, a strict two-step specialization chain `x ⤳ y ⤳ z` forces the stalk
at `z` to have Krull dimension at least `2`; contrapositively, if the stalk at `z` has
dimension `≤ 1` and `x ⤳ y ⤳ z` with `x ≠ y`, then `y = z`. -/
lemma eq_of_specializes_of_specializes {x y z : X}
    (hdim : Ring.KrullDimLE 1 (X.presheaf.stalk z))
    (hxy : x ⤳ y) (hyz : y ⤳ z) (hne : x ≠ y) : y = z := by
  by_contra hne'
  obtain ⟨p, hp⟩ : x ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact hxy.trans hyz
  obtain ⟨q, hq⟩ : y ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact hyz
  have hemb : Topology.IsEmbedding (X.fromSpecStalk z).base :=
    (Scheme.Hom.isEmbedding _)
  have hzq : X.fromSpecStalk z (IsLocalRing.closedPoint _) = z :=
    Scheme.fromSpecStalk_closedPoint
  let p' : PrimeSpectrum (X.presheaf.stalk z) := p
  let q' : PrimeSpectrum (X.presheaf.stalk z) := q
  let c' : PrimeSpectrum (X.presheaf.stalk z) := IsLocalRing.closedPoint _
  have hpq : p' < q' := by
    refine lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes _ _).mpr ?_) fun h => hne ?_
    · exact hemb.toIsInducing.specializes_iff.mp (by rw [hp, hq]; exact hxy)
    · rw [← hp, ← hq]
      exact congrArg (X.fromSpecStalk z) h
  have hqc : q' < c' := by
    refine lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes _ _).mpr ?_) fun h => hne' ?_
    · exact hemb.toIsInducing.specializes_iff.mp (by rw [hq, hzq]; exact hyz)
    · calc y = (X.fromSpecStalk z) q := hq.symm
        _ = (X.fromSpecStalk z) (IsLocalRing.closedPoint _) := congrArg _ h
        _ = z := hzq
  rcases Order.krullDim_le_one_iff.mp hdim.krullDim_le q' with h | h
  · exact h.not_lt hpq
  · exact h.not_lt hqc

/-- On an irreducible scheme with one-dimensional stalks, every non-generic point is
closed. -/
lemma isClosed_singleton_of_ne_genericPoint [IrreducibleSpace X]
    (hdim : ∀ z : X, Ring.KrullDimLE 1 (X.presheaf.stalk z)) {x : X}
    (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) := by
  have h : closure {x} = {x} := by
    refine subset_antisymm (fun z hz => ?_) subset_closure
    have hxz : x ⤳ z := specializes_iff_mem_closure.mpr hz
    have hgx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
    exact (eq_of_specializes_of_specializes (hdim z) hgx hxz (Ne.symm hx)) ▸ rfl
  rw [← h]
  exact isClosed_closure

/-- A Noetherian quasi-sober T1 space is finite: its finitely many irreducible
components are singletons and cover it. -/
lemma finite_of_t1Space {α : Type*} [TopologicalSpace α] [NoetherianSpace α]
    [QuasiSober α] [T1Space α] : Finite α := by
  have hsing : ∀ x : α, irreducibleComponent x = {x} := by
    intro x
    obtain ⟨ξ, hξ⟩ := QuasiSober.sober (S := irreducibleComponent x)
      isIrreducible_irreducibleComponent isClosed_irreducibleComponent
    have h : irreducibleComponent x = {ξ} := by
      rw [← hξ.def, closure_singleton]
    have hx : x ∈ irreducibleComponent x := mem_irreducibleComponent
    rw [h] at hx ⊢
    rw [Set.mem_singleton_iff.mp hx]
  have : Finite (irreducibleComponents α) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  refine Finite.of_injective
    (fun x : α => (⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩ :
      irreducibleComponents α)) fun a b hab => ?_
  have h : irreducibleComponent a = irreducibleComponent b := congrArg Subtype.val hab
  rw [hsing a, hsing b] at h
  exact Set.singleton_eq_singleton_iff.mp h

/-- On an irreducible Noetherian scheme with one-dimensional stalks, a closed subset
avoiding the generic point is finite. -/
lemma finite_of_isClosed_of_genericPoint_notMem [IrreducibleSpace X] [NoetherianSpace X]
    (hdim : ∀ z : X, Ring.KrullDimLE 1 (X.presheaf.stalk z)) {Z : Set X}
    (hZ : IsClosed Z) (hη : genericPoint X ∉ Z) : Z.Finite := by
  have hQS : QuasiSober Z := hZ.isClosedEmbedding_subtypeVal.quasiSober
  have hT1 : T1Space Z := by
    refine ⟨fun z => ?_⟩
    have hcl : IsClosed ({(z : X)} : Set X) :=
      isClosed_singleton_of_ne_genericPoint hdim fun h => hη (h ▸ z.2)
    have h : (Subtype.val ⁻¹' {(z : X)} : Set Z) = {z} := by
      ext w
      simp [Subtype.ext_iff]
    exact h ▸ hcl.preimage continuous_subtype_val
  rw [← Set.finite_coe_iff]
  exact finite_of_t1Space

/-- Fibers of a closed, non-constant morphism out of an irreducible Noetherian scheme
with one-dimensional stalks are finite. Non-constancy is expressed as: the image of
the generic point is not a closed point. -/
lemma finite_preimage_singleton_of_isClosedMap {Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace X] [NoetherianSpace X]
    (hdim : ∀ z : X, Ring.KrullDimLE 1 (X.presheaf.stalk z))
    (hf : IsClosedMap f.base) (hnc : ¬ IsClosed ({f (genericPoint X)} : Set Y)) (y : Y) :
    (f.base ⁻¹' {y}).Finite := by
  by_cases hy : genericPoint X ∈ f.base ⁻¹' {y}
  · -- the fiber through the generic point is just the generic point
    have h : f.base ⁻¹' {y} = {genericPoint X} := by
      refine subset_antisymm (fun x hx => ?_) (by simpa using hy)
      by_contra hne
      have h1 : IsClosed ({x} : Set X) :=
        isClosed_singleton_of_ne_genericPoint hdim (by simpa using hne)
      have h2 : IsClosed ({y} : Set Y) := by
        have := hf _ h1
        rwa [Set.image_singleton, show f.base x = y from hx] at this
      exact hnc (by rwa [show f (genericPoint X) = y from hy])
    rw [h]
    exact Set.finite_singleton _
  · rcases Set.eq_empty_or_nonempty (f.base ⁻¹' {y}) with h | ⟨x, hx⟩
    · simp [h]
    have hxne : x ≠ genericPoint X := fun h => hy (h ▸ hx)
    have h1 : IsClosed ({x} : Set X) := isClosed_singleton_of_ne_genericPoint hdim hxne
    have h2 : IsClosed ({y} : Set Y) := by
      have := hf _ h1
      rwa [Set.image_singleton, show f.base x = y from hx] at this
    exact finite_of_isClosed_of_genericPoint_notMem hdim
      (h2.preimage f.base.hom.continuous) hy

end Belyi
