/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.Topology.Homotopy.Lifting

/-!
# Covering maps over a product are constant along paths in the second factor

Let `p : E → Z × T` be a covering map. For `t : T` write `E_t := {e : E // (p e).2 = t}` for the
restriction of `E` to the slice `Z × {t}`. This file shows that a path `γ` from `t₀` to `t₁` in
`T` induces a homeomorphism `E_{t₀} ≃ₜ E_{t₁}` over `Z`: it is obtained by lifting the homotopy
`(τ, e) ↦ ((p e).1, γ τ)` through `p` (the homotopy lifting property of covering maps,
`IsCoveringMap.liftHomotopy`), and its inverse comes from the reversed path `γ.symm`; the two
composites are the identity because lifts of paths homotopic relative to the endpoints have the
same endpoint (`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`) and `γ ⬝ γ⁻¹` is homotopic
to the constant path.

This is step (S3b) of `references/converse-rie-design.md`.

## Main results

* `Belyi.Converse.exists_homeomorph_fiber_of_path`: a path `γ : Path t₀ t₁` in `T` gives a
  homeomorphism `{e // (p e).2 = t₀} ≃ₜ {e // (p e).2 = t₁}` commuting with `Prod.fst ∘ p`.
* `Belyi.Converse.exists_homeomorph_fiber`: the same for arbitrary `t₀ t₁` when `T` is path
  connected.
-/

noncomputable section

open unitInterval

namespace Belyi.Converse

variable {E Z T : Type*} [TopologicalSpace E] [TopologicalSpace Z] [TopologicalSpace T]
  {p : E → Z × T}

/-- The inclusion `t ↦ (z, t)` of `T` as the slice `{z} × T` of `Z × T`. -/
def sliceIncl (z : Z) : C(T, Z × T) := ⟨fun t ↦ (z, t), by fun_prop⟩

@[simp] lemma sliceIncl_apply (z : Z) (t : T) : sliceIncl z t = (z, t) := rfl

namespace CoveringHomotopy

lemma liftPath_congr (hp : IsCoveringMap p) {γ γ' : C(I, Z × T)} {e e' : E} (hγ : γ = γ')
    (he : e = e') (h : γ 0 = p e) (h' : γ' 0 = p e') :
    hp.liftPath γ e h = hp.liftPath γ' e' h' := by
  subst hγ he; rfl

omit [TopologicalSpace E] [TopologicalSpace Z] [TopologicalSpace T] in
lemma source_eq {t₀ : T} (e : {e : E // (p e).2 = t₀}) : ((p e.1).1, t₀) = p e.1 :=
  Prod.ext rfl e.2.symm

omit [TopologicalSpace E] in
lemma map_zero_eq {t₀ t₁ : T} (γ : Path t₀ t₁) (e : {e : E // (p e).2 = t₀}) :
    (γ.map (sliceIncl (p e.1).1).continuous).toContinuousMap 0 = p e.1 :=
  (congrArg (fun t ↦ ((p e.1).1, t)) γ.source).trans (source_eq e)

/-- Transport of a point of `E_{t₀}` along a path `γ` from `t₀` to `t₁`: the endpoint of the lift
starting at `e` of the path `τ ↦ ((p e).1, γ τ)`. -/
def transport (hp : IsCoveringMap p) {t₀ t₁ : T} (γ : Path t₀ t₁)
    (e : {e : E // (p e).2 = t₀}) : E :=
  hp.liftPath (γ.map (sliceIncl (p e.1).1).continuous).toContinuousMap e.1 (map_zero_eq γ e) 1

lemma p_transport (hp : IsCoveringMap p) {t₀ t₁ : T} (γ : Path t₀ t₁)
    (e : {e : E // (p e).2 = t₀}) : p (transport hp γ e) = ((p e.1).1, t₁) := by
  have := congr_fun (hp.liftPath_lifts (γ.map (sliceIncl (p e.1).1).continuous).toContinuousMap
    e.1 (map_zero_eq γ e)) 1
  exact this.trans (congrArg (fun t ↦ ((p e.1).1, t)) γ.target)

lemma fst_transport (hp : IsCoveringMap p) {t₀ t₁ : T} (γ : Path t₀ t₁)
    (e : {e : E // (p e).2 = t₀}) : (p (transport hp γ e)).1 = (p e.1).1 := by
  rw [p_transport hp γ e]

lemma snd_transport (hp : IsCoveringMap p) {t₀ t₁ : T} (γ : Path t₀ t₁)
    (e : {e : E // (p e).2 = t₀}) : (p (transport hp γ e)).2 = t₁ := by
  rw [p_transport hp γ e]

lemma continuous_transport (hp : IsCoveringMap p) {t₀ t₁ : T} (γ : Path t₀ t₁) :
    Continuous (transport (p := p) hp γ) := by
  let H : C(I × {e : E // (p e).2 = t₀}, Z × T) :=
    ⟨fun q ↦ ((p q.2.1).1, γ q.1), by have := hp.continuous; fun_prop⟩
  let f : C({e : E // (p e).2 = t₀}, E) := ⟨Subtype.val, continuous_subtype_val⟩
  have H_0 : ∀ a, H (0, a) = p (f a) := fun a ↦ map_zero_eq γ a
  have : transport hp γ = fun e ↦ hp.liftHomotopy H f H_0 (1, e) := by
    funext e
    rw [IsCoveringMap.liftHomotopy_apply]
    exact congrArg (· 1) (liftPath_congr hp (by ext <;> rfl) rfl _ _)
  rw [this]
  fun_prop

lemma transport_symm_transport (hp : IsCoveringMap p) {t₀ t₁ : T} (γ : Path t₀ t₁)
    (e : {e : E // (p e).2 = t₀}) :
    transport hp γ.symm ⟨transport hp γ e, snd_transport hp γ e⟩ = e.1 := by
  set z := (p e.1).1
  set f := sliceIncl (T := T) z
  have h0 : ((γ.trans γ.symm).map f.continuous).toContinuousMap 0 = p e.1 :=
    ((γ.trans γ.symm).map f.continuous).source.trans (source_eq e)
  have h0' : ((Path.refl t₀).map f.continuous).toContinuousMap 0 = p e.1 := source_eq e
  -- the lift of the null-homotopic loop `(z, γ ⬝ γ⁻¹)` ends at `e`
  have hnull : ((γ.trans γ.symm).map f.continuous).Homotopic ((Path.refl t₀).map f.continuous) :=
    Path.Homotopic.map ⟨(Path.Homotopy.reflTransSymm γ).symm⟩ f
  have h1 := hp.liftPath_apply_one_eq_of_homotopicRel hnull e.1 h0 h0'
  have h3 : hp.liftPath ((Path.refl t₀).map f.continuous).toContinuousMap e.1 h0' =
      ContinuousMap.const I e.1 :=
    (liftPath_congr hp (by ext <;> rfl) rfl _ (source_eq e)).trans (hp.liftPath_const (source_eq e))
  rw [h3] at h1
  refine Eq.trans ?_ h1
  -- the lift of `(z, γ ⬝ γ⁻¹)` is the concatenation of the lifts
  have h2 := congr_arg (fun Γ : C(I, E) ↦ Γ 1)
    (hp.liftPath_trans (source_eq e) (γ.map f.continuous) (γ.symm.map f.continuous))
  rw [liftPath_congr hp
    (γ' := ((γ.map f.continuous).trans (γ.symm.map f.continuous)).toContinuousMap)
    (by rw [Path.map_trans]) rfl h0 ((Path.source _).trans (source_eq e))]
  refine Eq.trans ?_ (h2.trans (Path.target _)).symm
  refine congrArg (· 1) (liftPath_congr hp ?_ rfl _ _)
  ext τ
  · exact fst_transport hp γ e
  · rfl

/-- The homeomorphism `E_{t₀} ≃ₜ E_{t₁}` over `Z` induced by a path `γ` from `t₀` to `t₁`. -/
def fiberHomeomorph (hp : IsCoveringMap p) {t₀ t₁ : T} (γ : Path t₀ t₁) :
    {e : E // (p e).2 = t₀} ≃ₜ {e : E // (p e).2 = t₁} where
  toFun e := ⟨transport hp γ e, snd_transport hp γ e⟩
  invFun e := ⟨transport hp γ.symm e, snd_transport hp γ.symm e⟩
  left_inv e := Subtype.ext (transport_symm_transport hp γ e)
  right_inv e := Subtype.ext <| by
    simpa using transport_symm_transport hp γ.symm e
  continuous_toFun := (continuous_transport hp γ).subtype_mk _
  continuous_invFun := (continuous_transport hp γ.symm).subtype_mk _

lemma fst_fiberHomeomorph (hp : IsCoveringMap p) {t₀ t₁ : T} (γ : Path t₀ t₁)
    (e : {e : E // (p e).2 = t₀}) : (p (fiberHomeomorph hp γ e)).1 = (p e).1 :=
  fst_transport hp γ e

end CoveringHomotopy

open CoveringHomotopy in
/-- **Covering homotopy lemma.** If `p : E → Z × T` is a covering map and `γ` is a path in `T`
from `t₀` to `t₁`, then the restrictions of `E` to `Z × {t₀}` and `Z × {t₁}` are homeomorphic
over `Z`. -/
theorem exists_homeomorph_fiber_of_path (hp : IsCoveringMap p) {t₀ t₁ : T} (γ : Path t₀ t₁) :
    ∃ h : {e : E // (p e).2 = t₀} ≃ₜ {e : E // (p e).2 = t₁}, ∀ e, (p (h e)).1 = (p e).1 :=
  ⟨fiberHomeomorph hp γ, fst_fiberHomeomorph hp γ⟩

/-- If `p : E → Z × T` is a covering map and `T` is path connected, then the restrictions of `E`
to any two slices `Z × {t₀}` and `Z × {t₁}` are homeomorphic over `Z`. -/
theorem exists_homeomorph_fiber [PathConnectedSpace T] (hp : IsCoveringMap p) (t₀ t₁ : T) :
    ∃ h : {e : E // (p e).2 = t₀} ≃ₜ {e : E // (p e).2 = t₁}, ∀ e, (p (h e)).1 = (p e).1 :=
  exists_homeomorph_fiber_of_path hp (PathConnectedSpace.somePath t₀ t₁)

end Belyi.Converse
