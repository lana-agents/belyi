/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.GaloisCoverFiniteness
import Mathlib.CategoryTheory.Galois.Full
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Finitely many bounded-degree objects of a Galois category with top. f.g. fundamental group

This file is the **Galois-category top layer** of piece (1) of the survey-scoped reduction of the
rigidity input **B9** (taxis issue **#211**, parent **#210**), sitting directly on top of the
group-theoretic core `Belyi.finite_continuousMonoidHom_of_topFG` established in
`Belyi/GaloisCoverFiniteness.lean`.

Let `C` be a `CategoryTheory.GaloisCategory` with fiber functor `F : C ⥤ FintypeCat` and
fundamental group `G := Aut F` (a compact Hausdorff topological group via mathlib
`CategoryTheory/Galois/Topology.lean`). We prove:

* `Belyi.PreGaloisCategory.finite_isoClasses_of_card_le`: **if `Aut F` is topologically finitely
  generated, then for every `d : ℕ` there are only finitely many isomorphism classes of objects
  `X : C` with `Nat.card (F.obj X) ≤ d`.**

## Strategy

An object `X` of a Galois category is determined, up to isomorphism, by the finite `Aut F`-set
`F.obj X` (the fiber functor `C ⥤ Action FintypeCat (Aut F)` is fully faithful). A finite
`Aut F`-set of cardinality `n` is a permutation representation `Aut F →* Equiv.Perm (Fin n)`, and
the representation is *continuous* because the action on the discrete finite fiber is continuous.

We assign to each bounded object `X` a **continuous perm-representation on a fixed finite set**
`Fin (d + 1)`: choose an embedding `F.obj X ↪ Fin (d + 1)` (possible as `card ≤ d`), and transport
the action by `Equiv.Perm.viaEmbeddingHom` (extend by the identity on the complement). This lands
in the type

```
Fin (d + 1) × ContinuousMonoidHom (Aut F) (Equiv.Perm (Fin (d + 1)))
```

whose second factor is **finite** by `Belyi.finite_continuousMonoidHom_of_topFG`. Two objects with
equal invariant have `Aut F`-equivariantly bijective fibers, hence are isomorphic. Passing to
representatives via `Quotient.out`, this exhibits the iso-class quotient as `Finite`.

## References

`references/rigidity-design.md` (label **B9**); the group-theory core
`Belyi/GaloisCoverFiniteness.lean`; taxis **#210**/#211 survey; [Szamuely2009] §3.4, §4.6;
mathlib `CategoryTheory/Galois/*`.
-/

universe u₁ u₂ w

open CategoryTheory Limits Functor Equiv
open scoped CategoryTheory.PreGaloisCategory

namespace Belyi

namespace PreGaloisCategory

open CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w})

-- Finite permutation groups carry the discrete topology, locally within this file.
local instance discreteTopologyPerm (X : Type*) [Finite X] :
    TopologicalSpace (Equiv.Perm X) := ⊥

local instance (X : Type*) [Finite X] : DiscreteTopology (Equiv.Perm X) := ⟨rfl⟩

variable (d : ℕ)

/-- An embedding of the (bounded) fiber of `X` into the fixed finite set `Fin (d + 1)`. -/
noncomputable def fiberEmb (X : C) (hX : Nat.card (F.obj X) ≤ d) : (F.obj X) ↪ Fin (d + 1) :=
  (Finite.equivFin (F.obj X)).toEmbedding.trans (Fin.castLEEmb (Nat.le_succ_of_le hX))

@[simp]
lemma fiberEmb_coe_apply (X : C) (hX : Nat.card (F.obj X) ≤ d) (x : F.obj X) :
    ((fiberEmb F d X hX x : Fin (d + 1)) : ℕ) = (Finite.equivFin (F.obj X) x : ℕ) := by
  simp [fiberEmb]

/-- The continuous permutation representation of `Aut F` on `Fin (d + 1)` attached to a bounded
object `X`: extend the fiber action along `fiberEmb` by the identity on the complement. -/
noncomputable def fiberPermHom (X : C) (hX : Nat.card (F.obj X) ≤ d) :
    Aut F →* Equiv.Perm (Fin (d + 1)) :=
  (Equiv.Perm.viaEmbeddingHom (fiberEmb F d X hX)).comp (MulAction.toPermHom (Aut F) (F.obj X))

lemma continuous_fiberPermHom (X : C) (hX : Nat.card (F.obj X) ≤ d) :
    Continuous ⇑(fiberPermHom F d X hX) := by
  rw [fiberPermHom, MonoidHom.coe_comp]
  exact continuous_of_discreteTopology.comp Belyi.continuous_toPermHom

lemma fiberPermHom_emb (X : C) (hX : Nat.card (F.obj X) ≤ d) (σ : Aut F) (x : F.obj X) :
    fiberPermHom F d X hX σ (fiberEmb F d X hX x) = fiberEmb F d X hX (σ • x) := by
  simp only [fiberPermHom, MonoidHom.coe_comp, Function.comp_apply,
    Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply,
    MulAction.toPermHom_apply, MulAction.toPerm_apply]

/-- The complete iso-invariant of a bounded object: its fiber cardinality (as an element of
`Fin (d + 1)`) together with the padded continuous perm-representation on `Fin (d + 1)`. -/
noncomputable def invEl (X : C) (hX : Nat.card (F.obj X) ≤ d) :
    Fin (d + 1) × ContinuousMonoidHom (Aut F) (Equiv.Perm (Fin (d + 1))) :=
  (⟨Nat.card (F.obj X), Nat.lt_succ_of_le hX⟩,
    { toMonoidHom := fiberPermHom F d X hX
      continuous_toFun := continuous_fiberPermHom F d X hX })

variable [GaloisCategory C] [FiberFunctor F]

/-- **Injectivity up to isomorphism.** Two bounded objects with the same invariant are isomorphic:
their fibers are `Aut F`-equivariantly bijective, and the fiber functor is fully faithful. -/
theorem iso_of_invEl_eq {X Y : C} (hX : Nat.card (F.obj X) ≤ d) (hY : Nat.card (F.obj Y) ≤ d)
    (h : invEl F d X hX = invEl F d Y hY) : Nonempty (X ≅ Y) := by
  obtain ⟨hfst, hsnd⟩ := Prod.ext_iff.mp h
  have hn : Nat.card (F.obj X) = Nat.card (F.obj Y) := by
    simpa [invEl] using congrArg Fin.val hfst
  have hρ : ∀ σ : Aut F, fiberPermHom F d X hX σ = fiberPermHom F d Y hY σ := by
    intro σ
    exact congrFun (congrArg (fun (φ : ContinuousMonoidHom _ _) => (φ : _ → _)) hsnd) σ
  -- The transported bijection between the two fibers.
  let ψ : (F.obj X) ≃ (F.obj Y) :=
    (Finite.equivFin (F.obj X)).trans ((finCongr hn).trans (Finite.equivFin (F.obj Y)).symm)
  have hψ : ∀ x, ψ x =
      (Finite.equivFin (F.obj Y)).symm (finCongr hn (Finite.equivFin (F.obj X) x)) :=
    fun _ => rfl
  -- `fiberEmb` of `x` on the `X` side equals `fiberEmb` of `ψ x` on the `Y` side (same value).
  have keyEmb : ∀ x : F.obj X, fiberEmb F d X hX x = fiberEmb F d Y hY (ψ x) := by
    intro x
    apply Fin.ext
    rw [fiberEmb_coe_apply, fiberEmb_coe_apply, hψ, Equiv.apply_symm_apply]
    simp
  -- Equivariance of `ψ`.
  have equiv : ∀ (σ : Aut F) (x : F.obj X), ψ (σ • x) = σ • ψ x := by
    intro σ x
    apply (fiberEmb F d Y hY).injective
    rw [← keyEmb, ← fiberPermHom_emb, hρ σ, keyEmb, fiberPermHom_emb]
  -- Package as an isomorphism of `Aut F`-sets, then reflect through the fiber functor.
  let actIso : (functorToAction F).obj X ≅ (functorToAction F).obj Y :=
    Action.mkIso (FintypeCat.equivEquivIso ψ) (fun σ => by
      ext x
      simp only [FintypeCat.comp_apply]
      exact equiv σ x)
  exact ⟨(functorToAction F).preimageIso actIso⟩

/-- **Bounded-degree finiteness for Galois categories.** If the fundamental group `Aut F` of a
Galois category `C` is topologically finitely generated, then for every `d` there are only finitely
many isomorphism classes of objects `X : C` with `Nat.card (F.obj X) ≤ d`.

This is the abstract engine (route step 2 of taxis #211) that, instantiated at
`C := FiniteEtale (ℙ¹_k ∖ {0,1,∞})`, feeds the finiteness of bounded-degree Belyi covers. -/
theorem finite_isoClasses_of_card_le
    (hFG : Belyi.TopologicallyFinitelyGenerated (Aut F)) (d : ℕ) :
    Finite (Quotient (isIsomorphicSetoid
      (ObjectProperty.FullSubcategory (fun X : C => Nat.card (F.obj X) ≤ d)))) := by
  set P : ObjectProperty C := fun X => Nat.card (F.obj X) ≤ d with hP
  haveI : Finite (ContinuousMonoidHom (Aut F) (Equiv.Perm (Fin (d + 1)))) :=
    Belyi.finite_continuousMonoidHom_of_topFG hFG
  refine Finite.of_injective
    (fun q : Quotient (isIsomorphicSetoid P.FullSubcategory) =>
      invEl F d q.out.obj q.out.property) ?_
  intro q₁ q₂ hq
  obtain ⟨e⟩ := iso_of_invEl_eq F d q₁.out.property q₂.out.property hq
  have hiso : (isIsomorphicSetoid P.FullSubcategory).r q₁.out q₂.out := ⟨P.ι.preimageIso e⟩
  calc q₁ = Quotient.mk _ q₁.out := (Quotient.out_eq q₁).symm
    _ = Quotient.mk _ q₂.out := Quotient.sound hiso
    _ = q₂ := Quotient.out_eq q₂

end PreGaloisCategory

end Belyi
