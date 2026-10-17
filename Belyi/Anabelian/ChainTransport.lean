/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Anabelian.Chain

/-!
# Transport of `Π`-chains along isomorphisms ([AbsTopI] Theorem 4.7 (ii), group-theoretic part)

[AbsTopI] Theorem 4.7 (ii) (`Topics in Absolute Anabelian Geometry I.txt` l.3466–3470): an
isomorphism `φ : Π₁ ≅ Π₂` (inducing `Δ₁ ≅ Δ₂`, `G₁ ≅ G₂`) "induces equivalences of categories
`Chain(Π₁) ≅ Chain(Π₂)`, `Chain^{iso-trm}(Π₁) ≅ Chain^{iso-trm}(Π₂)`, `ÉtLoc(Π₁) ≅ ÉtLoc(Π₂)` that
are compatible with passing to type-chains and functorial in `φ`". Its proof (l.3537) observes
"that the definitions of the various categories involved are entirely group-theoretic"; for the
operations of type `•` this uses that `φ` preserves the cuspidal decomposition groups, which is
[AbsTopI] Lemma 4.5 (v) under the cyclotomic-fullness assumption (b). Here this preservation is
part of the notion of an isomorphism of cuspidal extensions (`CuspidalExt.Iso`), and we carry out
the transport of structure.

## Main definitions and results

* `Belyi.Anabelian.CuspidalExt.Iso`, `CuspidalExt.Iso.symm`;
* `Belyi.Anabelian.ChainObj.transport`, `ElemOp.transport`, `PiChain.transport`;
* `PiChain.typeChain_transport`: transport preserves type-chains;
* `PiChain.Iso.transport`, `PiChain.TerminalIso.transport`: transport of morphisms of `Chain(Π)`
  and of `Chain^{iso-trm}(Π)`; `PiChain.IsEtLoc.transport`;
* `PiChain.transportSymmIso`: transporting back along `φ⁻¹` gives an isomorphic chain (so the
  transport functors are mutually quasi-inverse).
-/

universe u

namespace Belyi.Anabelian

/-- An **isomorphism of cuspidal extensions**: continuous isomorphisms `Π ≅ Π'`, `G ≅ G'`
compatible with the projections, carrying the cuspidal decomposition groups of `Π` exactly onto
those of `Π'`. -/
structure CuspidalExt.Iso (E E' : CuspidalExt.{u}) where
  /-- The isomorphism `Π ≅ Π'`. -/
  pi : E.Pi ≃ₜ* E'.Pi
  /-- The isomorphism `G ≅ G'`. -/
  g : E.G ≃ₜ* E'.G
  pr_comm : ∀ x, E'.pr (pi x) = g (E.pr x)
  cusps_map : ∀ I : Subgroup E.Pi, I ∈ E.cusps ↔ I.map pi.toMulEquiv.toMonoidHom ∈ E'.cusps

namespace CuspidalExt.Iso

variable {E E' : CuspidalExt.{u}}

/-- The inverse isomorphism. -/
def symm (Φ : E.Iso E') : E'.Iso E where
  pi := Φ.pi.symm
  g := Φ.g.symm
  pr_comm x := by
    apply Φ.g.injective
    rw [ContinuousMulEquiv.apply_symm_apply, ← Φ.pr_comm, ContinuousMulEquiv.apply_symm_apply]
  cusps_map I := by
    rw [Φ.cusps_map, Subgroup.map_map]
    convert Iff.rfl using 2
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      convert hy
      exact Φ.pi.apply_symm_apply y
    · intro hx
      exact ⟨x, hx, Φ.pi.apply_symm_apply x⟩

end CuspidalExt.Iso

namespace ChainObj

variable {E E' : CuspidalExt.{u}} (Φ : E.Iso E')

/-- The image `φ(H)` of an open subgroup `H ⊆ Π` under `φ : Π ≅ Π'`. -/
def mapOpen (H : OpenSubgroup E.Pi) : OpenSubgroup E'.Pi where
  toSubgroup := (H : Subgroup E.Pi).map Φ.pi.toMulEquiv.toMonoidHom
  isOpen' := Φ.pi.toHomeomorph.isOpenMap _ H.isOpen

theorem mem_mapOpen {H : OpenSubgroup E.Pi} {h : E'.Pi} : h ∈ mapOpen Φ H ↔ Φ.pi.symm h ∈ H := by
  change h ∈ (H : Subgroup E.Pi).map Φ.pi.toMulEquiv.toMonoidHom ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change Φ.pi.symm (Φ.pi x) ∈ H
    rwa [ContinuousMulEquiv.symm_apply_apply]
  · intro hh
    exact ⟨_, hh, Φ.pi.apply_symm_apply h⟩

theorem mapOpen_mono {H K : OpenSubgroup E.Pi} (hHK : H ≤ K) : mapOpen Φ H ≤ mapOpen Φ K :=
  fun _ hh ↦ (mem_mapOpen Φ).2 (hHK ((mem_mapOpen Φ).1 hh))

/-- `φ⁻¹ : φ(H) → H`, for an open subgroup `H ⊆ Π`. -/
def restrictSymm (H : OpenSubgroup E.Pi) :
    ((mapOpen Φ H : OpenSubgroup E'.Pi) : Subgroup E'.Pi) →ₜ* (H : Subgroup E.Pi) where
  toFun h := ⟨Φ.pi.symm h, (mem_mapOpen Φ).1 h.2⟩
  map_one' := Subtype.ext (map_one Φ.pi.symm)
  map_mul' x y := Subtype.ext (map_mul Φ.pi.symm (x : E'.Pi) y)
  continuous_toFun := (Φ.pi.symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem coe_restrictSymm_apply (H : OpenSubgroup E.Pi)
    (h : ((mapOpen Φ H : OpenSubgroup E'.Pi) : Subgroup E'.Pi)) :
    ((restrictSymm Φ H h : (H : Subgroup E.Pi)) : E.Pi) = Φ.pi.symm h := rfl

theorem restrictSymm_surjective (H : OpenSubgroup E.Pi) :
    Function.Surjective (restrictSymm Φ H) := fun h ↦
  ⟨⟨Φ.pi h, (mem_mapOpen Φ).2 (by rw [ContinuousMulEquiv.symm_apply_apply]; exact h.2)⟩,
    Subtype.ext (by simp)⟩

theorem ker_comp (A : ChainObj E) :
    (((Φ.g : E.G →ₜ* E'.G).comp A.toG : A.grp →ₜ* E'.G) : A.grp →* E'.G).ker = A.Delta := by
  ext x
  rw [Delta, MonoidHom.mem_ker, MonoidHom.mem_ker]
  change Φ.g (A.toG x) = 1 ↔ A.toG x = 1
  exact map_eq_one_iff _ Φ.g.injective

/-- **Transport of a chain object** along `Φ : E ≅ E'`: the same group, with rigidifying
homomorphism `ρ ∘ φ⁻¹` on `φ(H)` and projection `φ_G ∘ (Π_j → G)`. -/
def transport (A : ChainObj E) : ChainObj E' where
  grp := A.grp
  dom := mapOpen Φ A.dom
  rho := A.rho.comp (restrictSymm Φ A.dom)
  isOpen_range_rho := by
    rw [ContinuousMonoidHom.coe_comp, Set.range_comp, (restrictSymm_surjective Φ A.dom).range_eq,
      Set.image_univ]
    exact A.isOpen_range_rho
  toG := (Φ.g : E.G →ₜ* E'.G).comp A.toG
  isOpen_range_toG := by
    rw [ContinuousMonoidHom.coe_comp, Set.range_comp]
    exact Φ.g.toHomeomorph.isOpenMap _ A.isOpen_range_toG
  toG_rho h := by
    simp only [ContinuousMonoidHom.comp_toFun]
    rw [A.toG_rho]
    change Φ.g (E.pr (Φ.pi.symm h)) = E'.pr h
    rw [← Φ.pr_comm, ContinuousMulEquiv.apply_symm_apply]
  slim_delta := (ker_comp Φ A).symm ▸ A.slim_delta
  nontrivial_delta := (ker_comp Φ A).symm ▸ A.nontrivial_delta

variable {Φ}

@[simp] theorem transport_grp (A : ChainObj E) : (A.transport Φ).grp = A.grp := rfl

theorem transport_Delta (A : ChainObj E) : (A.transport Φ).Delta = A.Delta :=
  ker_comp Φ A

theorem transport_image (A : ChainObj E) (I : Subgroup E.Pi) :
    (A.transport Φ).image (I.map Φ.pi.toMulEquiv.toMonoidHom) = A.image I := by
  ext y
  simp only [image, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨h', ⟨i, hi, hi'⟩, rfl⟩
    refine ⟨restrictSymm Φ A.dom h', ?_, rfl⟩
    change Φ.pi.symm (h' : E'.Pi) ∈ I
    rw [← hi']
    change Φ.pi.symm (Φ.pi i) ∈ I
    rwa [ContinuousMulEquiv.symm_apply_apply]
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨h', rfl⟩ := restrictSymm_surjective Φ A.dom h
    refine ⟨h', ⟨_, hh, ?_⟩, rfl⟩
    change Φ.pi (Φ.pi.symm h') = h'
    exact Φ.pi.apply_symm_apply _

theorem IsCuspidal.transport {A : ChainObj E} {C : Subgroup A.grp} (h : A.IsCuspidal C) :
    (A.transport Φ).IsCuspidal C := by
  obtain ⟨I, hI, hne, rfl⟩ := h
  refine ⟨I.map Φ.pi.toMulEquiv.toMonoidHom, (Φ.cusps_map I).1 hI, ?_, ?_⟩
  · rwa [transport_image]
  · rw [transport_image, transport_Delta]
    rfl

theorem InTorsionFreeNormalOpen.transport {A : ChainObj E} {C : Subgroup A.grp}
    (h : A.InTorsionFreeNormalOpen C) : (A.transport Φ).InTorsionFreeNormalOpen C := by
  unfold InTorsionFreeNormalOpen at h ⊢
  rw [transport_Delta]
  exact h

theorem Compat.transport {A B : ChainObj E} {φ : A.grp →ₜ* B.grp} (h : Compat A B φ) :
    Compat (A.transport Φ) (B.transport Φ) φ := by
  obtain ⟨H, hA, hB, hφ⟩ := h
  refine ⟨mapOpen Φ H, mapOpen_mono Φ hA, mapOpen_mono Φ hB, fun h hh ↦ ?_⟩
  exact hφ (Φ.pi.symm h) ((mem_mapOpen Φ).1 hh)

end ChainObj

namespace ElemOp

variable {E E' : CuspidalExt.{u}} {Φ : E.Iso E'} {A B : ChainObj E}

/-- **Transport of an elementary operation** along `Φ` (same operation homomorphism). -/
def transport (Φ : E.Iso E') : ElemOp A B → ElemOp (A.transport Φ) (B.transport Φ)
  | cover φ inj isOpen compat => cover φ inj isOpen compat.transport
  | quot φ inj isOpen compat => quot φ inj isOpen compat.transport
  | decusp φ surj C cusp tf ker compat =>
      decusp φ surj C cusp.transport tf.transport ker compat.transport
  | deorb φ surj F le finite ker compat =>
      deorb φ surj F (by rw [ChainObj.transport_Delta]; exact le) finite ker compat.transport

@[simp] theorem kind_transport (o : ElemOp A B) : (o.transport Φ).kind = o.kind := by
  cases o <;> rfl

end ElemOp

namespace PiChain

variable {E E' : CuspidalExt.{u}}

/-- **Transport of a `Π`-chain** along `Φ : E ≅ E'` ([AbsTopI] Theorem 4.7 (ii)). -/
def transport (Φ : E.Iso E') (c : PiChain E) : PiChain E' where
  len := c.len
  obj j := (c.obj j).transport Φ
  obj_zero := by
    obtain ⟨e, H, hA, hB, he⟩ := c.obj_zero
    refine ⟨e.trans Φ.pi, ChainObj.mapOpen Φ H, ChainObj.mapOpen_mono Φ hA, le_top,
      fun h hh ↦ ?_⟩
    have := congrArg Φ.pi (he (Φ.pi.symm h) ((ChainObj.mem_mapOpen Φ).1 hh))
    exact this.trans (Φ.pi.apply_symm_apply h)
  op j := (c.op j).transport Φ

variable {Φ : E.Iso E'}

@[simp] theorem typeChain_transport (c : PiChain E) : (c.transport Φ).typeChain = c.typeChain := by
  simp [typeChain, transport]

@[simp] theorem len_transport (c : PiChain E) : (c.transport Φ).len = c.len := rfl

/-- Transport of isomorphisms of `Π`-chains (morphisms of `Chain(Π)`). -/
def Iso.transport {c c' : PiChain E} (i : c.Iso c') : (c.transport Φ).Iso (c'.transport Φ) where
  len_eq := i.len_eq
  typeChain_eq := by simp [i.typeChain_eq]
  iso j := i.iso j
  compat j := (i.compat j).transport

/-- Transport of terminal isomorphisms (morphisms of `Chain^{iso-trm}(Π)`). -/
def TerminalIso.transport {c c' : PiChain E} (i : c.TerminalIso c') :
    (c.transport Φ).TerminalIso (c'.transport Φ) where
  iso := i.iso
  over := by
    obtain ⟨g, hg⟩ := i.over
    refine ⟨Φ.g g, fun x ↦ ?_⟩
    change Φ.g ((c'.last).toG (i.iso x)) = Φ.g g * Φ.g ((c.last).toG x) * (Φ.g g)⁻¹
    rw [hg, map_mul, map_mul, map_inv]

theorem IsEtLoc.transport {c : PiChain E} (h : c.IsEtLoc) : (c.transport Φ).IsEtLoc := by
  unfold IsEtLoc at h ⊢
  rwa [typeChain_transport]

/-- Transporting along `Φ` and back along `Φ⁻¹` gives a chain isomorphic to the original one
(identity maps on the groups). -/
def transportSymmIso (c : PiChain E) : ((c.transport Φ).transport Φ.symm).Iso c where
  len_eq := rfl
  typeChain_eq := by simp
  iso j := ContinuousMulEquiv.refl _
  compat j := by
    refine ⟨(c.obj j).dom, fun h hh ↦ ?_, le_rfl, fun h hh ↦ ?_⟩
    · refine (ChainObj.mem_mapOpen Φ.symm).2 ((ChainObj.mem_mapOpen Φ).2 ?_)
      change Φ.pi.symm (Φ.pi.symm.symm h) ∈ _
      rwa [ContinuousMulEquiv.symm_symm, ContinuousMulEquiv.symm_apply_apply]
    · change (c.obj j).rho (ChainObj.restrictSymm Φ _ (ChainObj.restrictSymm Φ.symm _ _)) = _
      congr 1
      ext
      change Φ.pi.symm (Φ.pi.symm.symm h) = h
      rw [ContinuousMulEquiv.symm_symm, ContinuousMulEquiv.symm_apply_apply]

end PiChain

end Belyi.Anabelian
