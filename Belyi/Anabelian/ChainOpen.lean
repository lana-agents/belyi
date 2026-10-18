/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Anabelian.Chain

/-!
# Chain objects of open subgroups (the `⋏` objects, [AbsTopI] Definition 4.2 (iii) (a))

A finite étale covering `X_{j+1} → X_j` corresponds to an open subgroup of `Π_j`. For the first
step of a chain this is an open subgroup `H ⊆ Π`, which is a chain object with rigidifying
homomorphism the identity of `H`:

* `Belyi.Anabelian.IsSlim.subgroupOf`: `Δ ∩ H` is slim for `Δ` slim and `H` open;
* `Belyi.Anabelian.IsSlim.subgroupOf_ne_bot`: and nontrivial if `Δ` is nontrivial
  (a slim group in which `1` is open is trivial);
* `Belyi.Anabelian.ChainObj.ofOpenSubgroup E H : ChainObj E`, with `Δ_H = Δ ∩ H`.
-/

universe u

namespace Belyi.Anabelian

open Pi1.Profinite

section Slim

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- **An open subgroup of a slim subgroup is slim**: `Δ ∩ H` is slim for `Δ` slim, `H` open. -/
theorem IsSlim.subgroupOf {Δ H : Subgroup G} (hΔ : IsSlim Δ) (hH : IsOpen (H : Set G)) :
    IsSlim (Δ.subgroupOf H) := by
  intro U z hz
  -- `V = {d ∈ Δ | d ∈ H, d ∈ U}` is an open subgroup of `Δ`
  let f : Δ.subgroupOf H →* Δ :=
    { toFun := fun x ↦ ⟨x.1.1, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hf : Function.Injective f := fun x y h ↦
    Subtype.ext (Subtype.ext (congrArg (fun d : Δ ↦ (d : G)) h))
  have hfU : IsOpen ((U.toSubgroup.map f : Subgroup Δ) : Set Δ) := by
    have hS : IsOpen {d : Δ | (d : G) ∈ H} := hH.preimage continuous_subtype_val
    let r : {d : Δ | (d : G) ∈ H} → Δ.subgroupOf H := fun d ↦ ⟨⟨d.1, d.2⟩, d.1.2⟩
    have hr : Continuous r := by
      refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
      exact continuous_subtype_val.comp continuous_subtype_val
    have hpre : IsOpen (r ⁻¹' (U : Set (Δ.subgroupOf H))) := U.isOpen.preimage hr
    have hset : ((U.toSubgroup.map f : Subgroup Δ) : Set Δ) =
        Subtype.val '' (r ⁻¹' (U : Set (Δ.subgroupOf H))) := by
      ext d
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨f x, x.1.2⟩, show r ⟨f x, x.1.2⟩ ∈ U from hx, rfl⟩
      · rintro ⟨d', hd', rfl⟩
        exact ⟨r d', hd', rfl⟩
    rw [hset]
    exact hS.isOpenMap_subtype_val _ hpre
  let V : OpenSubgroup Δ := ⟨U.toSubgroup.map f, hfU⟩
  have : f z = 1 := hΔ V (f z) fun v hv ↦ by
    obtain ⟨u, hu, rfl⟩ := hv
    rw [← map_mul, ← map_mul, hz u hu]
  exact hf (this.trans (map_one f).symm)

/-- **An open subgroup of a nontrivial slim subgroup is nontrivial.** -/
theorem IsSlim.subgroupOf_ne_bot {Δ H : Subgroup G} (hΔ : IsSlim Δ) (hne : Δ ≠ ⊥)
    (hH : IsOpen (H : Set G)) : Δ.subgroupOf H ≠ ⊥ := by
  intro hbot
  apply hne
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  -- `Δ ∩ H = 1` is open in `Δ`, so slimness of `Δ` forces `x = 1`
  have hS : IsOpen ((H.comap Δ.subtype : Subgroup Δ) : Set Δ) :=
    hH.preimage continuous_subtype_val
  let V : OpenSubgroup Δ := ⟨H.comap Δ.subtype, hS⟩
  have hV : ∀ v ∈ V, v = 1 := fun v hv ↦ by
    have hmem : (⟨v.1, hv⟩ : H) ∈ Δ.subgroupOf H := v.2
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext (congrArg (fun y : H ↦ (y : G)) hmem)
  have := hΔ V ⟨x, hx⟩ fun v hv ↦ by rw [hV v hv, mul_one, one_mul]
  exact congrArg Subtype.val this

end Slim

namespace ChainObj

variable (E : CuspidalExt.{u}) (H : OpenSubgroup E.Pi)

/-- An open subgroup of `Π` has finite index. -/
lemma finiteIndex_openSubgroup : (H : Subgroup E.Pi).FiniteIndex := by
  haveI : DiscreteTopology (E.Pi ⧸ (H : Subgroup E.Pi)) :=
    QuotientGroup.discreteTopology_iff.2 H.isOpen
  haveI : Finite (E.Pi ⧸ (H : Subgroup E.Pi)) := finite_of_compact_of_discrete
  exact Subgroup.finiteIndex_of_finite_quotient

/-- The image of an open subgroup of `Π` in `G` is open. -/
lemma isOpen_map_pr : IsOpen (((H : Subgroup E.Pi).map (E.pr : E.Pi →* E.G) : Subgroup E.G) :
    Set E.G) := by
  haveI := finiteIndex_openSubgroup E H
  haveI : ((H : Subgroup E.Pi).map (E.pr : E.Pi →* E.G)).FiniteIndex :=
    ⟨fun h ↦ (H : Subgroup E.Pi).index_ne_zero_of_finite
      (Nat.eq_zero_of_zero_dvd (h ▸ (H : Subgroup E.Pi).index_map_dvd E.pr_surjective))⟩
  refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
  have hc : IsCompact ((H : Subgroup E.Pi) : Set E.Pi) := H.isClosed.isCompact
  have := (hc.image E.pr.continuous).isClosed
  simpa using this

/-- **The chain object of an open subgroup `H ⊆ Π`** (a finite étale covering of `X`, the target of
an operation of type `⋏` from the trivial object): `Π_j = H`, `ρ_j = id_H`, `Δ_j = Δ ∩ H`. -/
noncomputable def ofOpenSubgroup : ChainObj E where
  grp := ProfiniteGrp.ofClosedSubgroup (⟨(H : Subgroup E.Pi), H.isClosed⟩ : ClosedSubgroup E.Pi)
  dom := H
  rho := ContinuousMonoidHom.id _
  isOpen_range_rho := by
    convert isOpen_univ
    exact Set.eq_univ_of_forall fun x ↦ ⟨x, rfl⟩
  toG := E.pr.comp ⟨(H : Subgroup E.Pi).subtype, continuous_subtype_val⟩
  isOpen_range_toG := by
    convert isOpen_map_pr E H using 1
    ext g
    simp only [Set.mem_range, SetLike.mem_coe, Subgroup.mem_map]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨y.1, y.2, hy⟩, fun ⟨x, hx, hxg⟩ ↦ ⟨⟨x, hx⟩, hxg⟩⟩
  toG_rho _ := rfl
  slim_delta := by
    have h : ((E.pr.comp ⟨(H : Subgroup E.Pi).subtype, continuous_subtype_val⟩ :
        (H : Subgroup E.Pi) →ₜ* E.G) : (H : Subgroup E.Pi) →* E.G).ker =
        E.Delta.subgroupOf H := rfl
    exact h ▸ IsSlim.subgroupOf E.slim_delta H.isOpen
  nontrivial_delta := by
    have h : ((E.pr.comp ⟨(H : Subgroup E.Pi).subtype, continuous_subtype_val⟩ :
        (H : Subgroup E.Pi) →ₜ* E.G) : (H : Subgroup E.Pi) →* E.G).ker =
        E.Delta.subgroupOf H := rfl
    exact h ▸ IsSlim.subgroupOf_ne_bot E.slim_delta E.nontrivial_delta H.isOpen

end ChainObj

end Belyi.Anabelian
