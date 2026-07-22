/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Basic

/-!
# Finitely many bounded-index subgroups of a finitely generated group

This file proves the elementary group-theoretic core of the **rigidity input B9**
(taxis issue **#52**, see `references/rigidity-design.md` §3b): a finitely generated
group has only finitely many subgroups of index `≤ d`, and in particular the rank-2
free group `F₂ = FreeGroup (Fin 2)` — the topological fundamental group of the
thrice-punctured line `ℙ¹ ∖ {0,1,∞}` — does.

Via Riemann existence, connected finite covers of `ℙ¹_ℂ ∖ {0,1,∞}` of degree `n`
correspond to index-`n` subgroups of `F₂`, and general degree-`≤ d` covers to finite
`F₂`-sets of cardinality `≤ d`. The finiteness of such combinatorial data is exactly
the statement `Belyi.finite_boundedIndex_subgroups_freeGroupTwo` below. This lemma is
recorded as verified *evidence* for the (separately axiomatized) geometric rigidity
statement `Belyi.rigidity_finiteness`; it is deliberately geometry-free and
upstreamable to Mathlib.

## Main results

* `Belyi.finite_boundedIndex_subgroups`: a finitely generated group has finitely many
  subgroups of index `≤ d` (excluding index `0`, i.e. the infinite-index ones).
* `Belyi.finite_boundedIndex_subgroups_freeGroupTwo`: the specialization to `F₂`.

## Proof strategy

A subgroup `H` of index `1 ≤ n ≤ d` gives the coset action
`G →* Equiv.Perm (G ⧸ H)`; transporting along a bijection `e : G ⧸ H ≃ Fin n`
yields `φ_H : G →* Equiv.Perm (Fin n)` and a distinguished point `i_H = e 1`, and `H`
is recovered as the stabilizer of `i_H`. This exhibits an injection of the set of
bounded-index subgroups into `Σ (n : Fin (d+1)), (G →* Equiv.Perm (Fin n)) × Fin n`,
which is finite: the crux is that `G →* N` is finite for finitely generated `G` and
finite `N`, because a homomorphism is determined by its values on a finite generating
set.

## References

* `references/rigidity-design.md` (label **B9**, taxis issue **#52**).
-/

namespace Belyi

/-- A monoid homomorphism from a finitely generated group into a finite group ranges
over a finite type: it is determined by its values on a finite generating set. -/
instance finite_monoidHom_of_fg {G N : Type*} [Group G] [Group.FG G] [Group N]
    [Finite N] : Finite (G →* N) := by
  obtain ⟨S, hS⟩ := (‹Group.FG G›).out
  refine Finite.of_injective (fun (φ : G →* N) => fun (s : S) => φ s) ?_
  intro φ ψ h
  ext x
  have hx : x ∈ Subgroup.closure (S : Set G) := by rw [hS]; exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact congrFun h ⟨y, Finset.mem_coe.mp hy⟩
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
  | inv a _ ha => rw [map_inv, map_inv, ha]

/-- The permutation of `Equiv.Perm β` induced, by conjugation, from `Equiv.Perm α`
along a bijection `e : α ≃ β`, packaged as a group homomorphism. -/
def permCongrHom {α β : Type*} (e : α ≃ β) : Equiv.Perm α →* Equiv.Perm β where
  toFun := e.permCongr
  map_one' := by
    ext x
    simp
  map_mul' p q := by
    ext x
    simp [Equiv.Perm.mul_apply]

@[simp]
theorem permCongrHom_apply {α β : Type*} (e : α ≃ β) (p : Equiv.Perm α) :
    permCongrHom e p = e.permCongr p := rfl

/-- The stabilizer of a point `i` under the `G`-action on `X` induced by a
homomorphism `φ : G →* Equiv.Perm X`. -/
def stabOfHom {G X : Type*} [Group G] (φ : G →* Equiv.Perm X) (i : X) : Subgroup G :=
  (MulAction.stabilizer (Equiv.Perm X) i).comap φ

@[simp]
theorem mem_stabOfHom {G X : Type*} [Group G] {φ : G →* Equiv.Perm X} {i : X} {g : G} :
    g ∈ stabOfHom φ i ↔ φ g i = i := by
  simp [stabOfHom, MulAction.mem_stabilizer_iff]

/-- The subgroup `H` is exactly the stabilizer of the base point `e 1` for the
`G`-action on `Fin H.index` obtained from the coset action along `e`. -/
theorem stabOfHom_permCongrHom {G : Type*} [Group G] (H : Subgroup G) [Finite (G ⧸ H)]
    (e : G ⧸ H ≃ Fin H.index) :
    stabOfHom ((permCongrHom e).comp (MulAction.toPermHom G (G ⧸ H)))
      (e ((1 : G) : G ⧸ H)) = H := by
  ext g
  rw [mem_stabOfHom, MonoidHom.comp_apply, permCongrHom_apply, Equiv.permCongr_apply,
    Equiv.symm_apply_apply, MulAction.toPermHom_apply, MulAction.toPerm_apply,
    Equiv.apply_eq_iff_eq, ← MulAction.mem_stabilizer_iff, MulAction.stabilizer_quotient]

/-- The finite invariant `⟨index, φ_H, i_H⟩` assigned to a bounded-index subgroup `H`:
its index (as an element of `Fin (d+1)`), the coset action transported to
`Equiv.Perm (Fin H.index)`, and the base point `e 1`. -/
noncomputable def boundedIndexInvariant (G : Type*) [Group G] (d : ℕ)
    (H : {H : Subgroup G // H.index ≤ d ∧ H.index ≠ 0}) :
    Σ n : Fin (d + 1), (G →* Equiv.Perm (Fin (n : ℕ))) × Fin (n : ℕ) :=
  haveI : Finite (G ⧸ H.1) := Subgroup.index_ne_zero_iff_finite.mp H.2.2
  ⟨⟨H.1.index, Nat.lt_succ_of_le H.2.1⟩,
    (permCongrHom (Finite.equivFinOfCardEq (α := G ⧸ H.1) (n := H.1.index) rfl)).comp
      (MulAction.toPermHom G (G ⧸ H.1)),
    Finite.equivFinOfCardEq (α := G ⧸ H.1) (n := H.1.index) rfl ((1 : G) : G ⧸ H.1)⟩

/-- The subgroup `H` is recovered from `boundedIndexInvariant G d H` as the stabilizer
of its base point; hence the invariant is injective. -/
theorem boundedIndexInvariant_recover (G : Type*) [Group G] (d : ℕ)
    (H : {H : Subgroup G // H.index ≤ d ∧ H.index ≠ 0}) :
    stabOfHom (boundedIndexInvariant G d H).2.1 (boundedIndexInvariant G d H).2.2 = H.1 := by
  haveI : Finite (G ⧸ H.1) := Subgroup.index_ne_zero_iff_finite.mp H.2.2
  exact stabOfHom_permCongrHom H.1 (Finite.equivFinOfCardEq (α := G ⧸ H.1) (n := H.1.index) rfl)

/-- A finitely generated group has only finitely many subgroups of index `≤ d`. -/
theorem finite_boundedIndex_subgroups (G : Type*) [Group G] [Group.FG G] (d : ℕ) :
    {H : Subgroup G | H.index ≤ d ∧ H.index ≠ 0}.Finite := by
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective (boundedIndexInvariant G d) ?_
  intro a b hab
  apply Subtype.ext
  rw [← boundedIndexInvariant_recover G d a, ← boundedIndexInvariant_recover G d b, hab]

/-- Specialization to the rank-2 free group `F₂`, the fundamental group of the
thrice-punctured line — the combinatorial core of the rigidity input B9. -/
theorem finite_boundedIndex_subgroups_freeGroupTwo (d : ℕ) :
    {H : Subgroup (FreeGroup (Fin 2)) | H.index ≤ d ∧ H.index ≠ 0}.Finite :=
  finite_boundedIndex_subgroups (FreeGroup (Fin 2)) d

end Belyi
