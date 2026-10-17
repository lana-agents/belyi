/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Anabelian.BelyiChain

/-!
# Elliptic-type `Π`-chains and the cuspidalisations they produce ([AbsTopII] Cor 3.3 (iii)(a))

[AbsTopII] Corollary 3.3 (iii) (a) (`Topics in Absolute Anabelian Geometry II.txt` l.4481–4491):
"There exists a [not necessarily unique] `Π`-chain, which admits an entirely "group-theoretic"
description, with associated type-chain

  `⋏, ⋎, ⋏, •, …, •, ⋏, ⋎`

— cf. Example 3.2, (ii) — that admits a terminal isomorphism with the trivial `Π`-chain [of length
`0`], and whose final three groups consist of `Π_D ⇝ Π_V (→ Π_D) ⇝ (Π_V →) Π` such that the
natural surjection `Π_U ↠ Π_D` may be recovered from the chain of "`•`'s" terminating at the
third to last group of the above-mentioned `Π`-chain; the natural surjection `Π_{U_V} ↠ Π_V` may
then be recovered from `Π_U ↠ Π_D` by forming the fiber product with the inclusion `Π_V ↪ Π_D`."

The geometric chain is `X ⇝ V ⇝ D ⇝ U ⇝ U_n ⇝ … ⇝ U_1 = D ⇝ V ⇝ X* = X` (Ex 3.2 (ii),
l.4384–4391). This file is the **group-theoretic** half of step (a), parallel to
`Belyi/Anabelian/BelyiChain.lean`:

* `ElemOp.coverHom`: the open immersion `Π_{j+1} ↪ Π_j` of an operation of type `⋏`;
* `PiChain.IsEllipticType c n`: the type-chain of `c` is `⋏, ⋎, ⋏, •^n, ⋏, ⋎`;
* `EllCandidate`: data `Π_U ↠ Π_D ↩ Π_V ↪ Π` (surjection, open immersion, open embedding);
  `EllCandidate.fibre`: the fibre product `Π_{U_V} = Π_U ×_{Π_D} Π_V`, a profinite group, with
  the surjection `Π_{U_V} ↠ Π_V` (`EllCandidate.fibreProj_surjective`);
  `EllCandidate.toCuspCandidate`: the resulting candidate `Π_{U_V} ↠ Π_V ↪ Π`;
* `PiChain.ellipticCandidate`: the candidate read off from an elliptic-type chain with a terminal
  isomorphism to the trivial chain; `ellipticCusp E`: the set of all of them, a purely
  group-theoretic function of the cuspidal extension `E`;
* `ellipticCusp_transport`: functoriality in isomorphisms of cuspidal extensions
  ([AbsTopI] Theorem 4.7 (ii)).

That the candidates are the cuspidalisations `U_V ⊆ V` of Ex 3.2 (the specification) is the
geometric half (MR8.3: `Chain(X̃/X) ≃ Chain(Π)`, [AbsTopI] Theorem 4.7 (i), via the rel-isom-DGC).
-/

universe u

namespace Belyi.Anabelian

variable {E : CuspidalExt.{u}}

namespace ElemOp

variable {A B : ChainObj E}

/-- The operation homomorphism `Π_{j+1} ↪ Π_j` of an operation of type `⋏`. -/
def coverHom : (o : ElemOp A B) → o.kind = .cover → (B.grp →ₜ* A.grp)
  | cover φ .., _ => φ
  | quot .., h => absurd h (by simp [kind])
  | decusp .., h => absurd h (by simp [kind])
  | deorb .., h => absurd h (by simp [kind])

theorem coverHom_injective : ∀ (o : ElemOp A B) (h : o.kind = .cover),
    Function.Injective (o.coverHom h)
  | cover _ inj .., _ => inj
  | quot .., h => absurd h (by simp [kind])
  | decusp .., h => absurd h (by simp [kind])
  | deorb .., h => absurd h (by simp [kind])

theorem isOpen_range_coverHom : ∀ (o : ElemOp A B) (h : o.kind = .cover),
    IsOpen (Set.range (o.coverHom h))
  | cover _ _ isOpen _, _ => isOpen
  | quot .., h => absurd h (by simp [kind])
  | decusp .., h => absurd h (by simp [kind])
  | deorb .., h => absurd h (by simp [kind])

variable {E' : CuspidalExt.{u}} {Φ : E.Iso E'}

theorem coverHom_transport : ∀ (o : ElemOp A B) (h : o.kind = .cover),
    (o.transport Φ).coverHom (by rw [kind_transport]; exact h) = o.coverHom h
  | cover .., _ => rfl
  | quot .., h => absurd h (by simp [kind])
  | decusp .., h => absurd h (by simp [kind])
  | deorb .., h => absurd h (by simp [kind])

end ElemOp

namespace PiChain

variable (c : PiChain E)

/-- **Elliptic-type chains** ([AbsTopII] Ex 3.2 (ii), Cor 3.3 (iii)(a)): the type-chain of `c`
is `⋏, ⋎, ⋏, •^n, ⋏, ⋎` (so `len = n + 5`). -/
def IsEllipticType (n : ℕ) : Prop :=
  ∃ hlen : c.len = n + 5,
    (c.opN 0 (by omega)).kind = .cover ∧ (c.opN 1 (by omega)).kind = .quot ∧
    (c.opN 2 (by omega)).kind = .cover ∧
    (∀ s (hs : s < n), (c.opN (3 + s) (by omega)).kind = .decusp) ∧
    (c.opN (n + 3) (by omega)).kind = .cover ∧ (c.opN (n + 4) (by omega)).kind = .quot

variable {c}

theorem IsEllipticType.len_eq {n : ℕ} (hc : c.IsEllipticType n) : c.len = n + 5 := hc.1

/-- The `•`'s of an elliptic-type chain form a run `Π_3 ↠ Π_{n+3}`. -/
theorem IsEllipticType.isDecuspRun {n : ℕ} (hc : c.IsEllipticType n) :
    c.IsDecuspRun 3 n (by have := hc.len_eq; omega) :=
  hc.2.2.2.2.1

end PiChain

/-- An **elliptic cuspidalisation candidate** for `Π`: a surjection `Π_U ↠ Π_D`, an open immersion
`Π_V ↪ Π_D` and an open embedding `Π_V ↪ Π` of profinite groups. -/
structure EllCandidate (E : CuspidalExt.{u}) where
  /-- The group `Π_U`. -/
  PiU : ProfiniteGrp.{u}
  /-- The group `Π_D`. -/
  PiD : ProfiniteGrp.{u}
  /-- The group `Π_V`. -/
  PiV : ProfiniteGrp.{u}
  /-- The surjection `Π_U ↠ Π_D`. -/
  surj : PiU →ₜ* PiD
  surj_surjective : Function.Surjective surj
  /-- The open immersion `Π_V ↪ Π_D`. -/
  incl : PiV →ₜ* PiD
  incl_injective : Function.Injective incl
  isOpen_range_incl : IsOpen (Set.range incl)
  /-- The open embedding `Π_V ↪ Π`. -/
  emb : PiV →ₜ* E.Pi
  emb_injective : Function.Injective emb
  isOpen_range_emb : IsOpen (Set.range emb)

namespace EllCandidate

variable (x : EllCandidate E)

/-- The fibre product `Π_{U_V} = Π_U ×_{Π_D} Π_V`, as a closed subgroup of `Π_U × Π_V`. -/
def fibreSubgroup : ClosedSubgroup (ProfiniteGrp.of (x.PiU × x.PiV)) where
  toSubgroup :=
    { carrier := {p | x.surj p.1 = x.incl p.2}
      mul_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        change x.surj (a.1 * b.1) = x.incl (a.2 * b.2)
        rw [map_mul, map_mul, ha, hb]
      one_mem' := by
        change x.surj 1 = x.incl 1
        rw [map_one, map_one]
      inv_mem' := fun {a} ha ↦ by
        simp only [Set.mem_setOf_eq] at ha ⊢
        change x.surj a.1⁻¹ = x.incl a.2⁻¹
        rw [map_inv, map_inv, ha] }
  isClosed' := isClosed_eq (x.surj.continuous.comp (continuous_fst (X := x.PiU) (Y := x.PiV)))
    (x.incl.continuous.comp (continuous_snd (X := x.PiU) (Y := x.PiV)))

/-- **The fibre product `Π_{U_V} = Π_U ×_{Π_D} Π_V`** ([AbsTopII] Cor 3.3 (iii)(a)), a profinite
group. -/
def fibre : ProfiniteGrp.{u} := ProfiniteGrp.ofClosedSubgroup x.fibreSubgroup

/-- The projection `Π_{U_V} ↠ Π_V`. -/
def fibreProj : x.fibre →ₜ* x.PiV where
  toFun p := (p.1 : x.PiU × x.PiV).2
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val

/-- The projection `Π_{U_V} ↠ Π_U`. -/
def fibreFst : x.fibre →ₜ* x.PiU where
  toFun p := (p.1 : x.PiU × x.PiV).1
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_fst.comp continuous_subtype_val

theorem surj_fibreFst (p : x.fibre) : x.surj (x.fibreFst p) = x.incl (x.fibreProj p) := p.2

/-- `Π_{U_V} ↠ Π_V` is surjective, since `Π_U ↠ Π_D` is. -/
theorem fibreProj_surjective : Function.Surjective x.fibreProj := fun v ↦ by
  obtain ⟨u, hu⟩ := x.surj_surjective (x.incl v)
  exact ⟨⟨(u, v), hu⟩, rfl⟩

/-- The square `Π_{U_V} ⟶ Π_U`, `Π_V ⟶ Π_D` is cartesian: an element of `Π_{U_V}` is determined
by its images in `Π_U` and `Π_V`. -/
theorem fibre_ext {p q : x.fibre} (h₁ : x.fibreFst p = x.fibreFst q)
    (h₂ : x.fibreProj p = x.fibreProj q) : p = q :=
  Subtype.ext (Prod.ext h₁ h₂)

/-- `Π_{U_V} ↪ Π_U` is injective (as `Π_V ↪ Π_D` is). -/
theorem fibreFst_injective : Function.Injective x.fibreFst := fun p q h ↦
  x.fibre_ext h (x.incl_injective (by rw [← surj_fibreFst, ← surj_fibreFst, h]))

/-- The cuspidalisation candidate `Π_{U_V} ↠ Π_V ↪ Π`. -/
def toCuspCandidate : CuspCandidate E where
  PiU := x.fibre
  PiV := x.PiV
  surj := x.fibreProj
  surj_surjective := x.fibreProj_surjective
  emb := x.emb
  emb_injective := x.emb_injective
  isOpen_range_emb := x.isOpen_range_emb

variable {E' : CuspidalExt.{u}}

/-- Transport of a candidate along `Φ : E ≅ E'`: compose the embedding with `Π ≅ Π'`. -/
def transport (Φ : E.Iso E') : EllCandidate E' where
  PiU := x.PiU
  PiD := x.PiD
  PiV := x.PiV
  surj := x.surj
  surj_surjective := x.surj_surjective
  incl := x.incl
  incl_injective := x.incl_injective
  isOpen_range_incl := x.isOpen_range_incl
  emb := (ContinuousMonoidHom.toContinuousMonoidHom Φ.pi).comp x.emb
  emb_injective := by
    rw [ContinuousMonoidHom.coe_comp]
    exact Φ.pi.injective.comp x.emb_injective
  isOpen_range_emb := by
    rw [ContinuousMonoidHom.coe_comp, Set.range_comp]
    exact Φ.pi.toHomeomorph.isOpenMap _ x.isOpen_range_emb

theorem toCuspCandidate_transport (Φ : E.Iso E') :
    (x.transport Φ).toCuspCandidate = x.toCuspCandidate.transport Φ := rfl

end EllCandidate

namespace PiChain

variable {c : PiChain E} {n : ℕ}

/-- The open embedding `Π_V = Π_{n+4} ↪ Π_{n+5} ≅ Π` of an elliptic-type chain with a terminal
isomorphism to the trivial chain. -/
def ellipticEmb (hc : c.IsEllipticType n) (t : c.TerminalIso (trivial E)) :
    (c.objN (n + 4) (by have := hc.len_eq; omega)).grp →ₜ* E.Pi :=
  (ContinuousMonoidHom.toContinuousMonoidHom t.toPi).comp
    ((ContinuousMonoidHom.toContinuousMonoidHom
        (c.objCongr (a := n + 4 + 1) (b := c.len) (by have := hc.len_eq; omega)
          (by have := hc.len_eq; omega) le_rfl)).comp
      ((c.opN (n + 4) (by have := hc.len_eq; omega)).quotHom hc.2.2.2.2.2.2))

theorem ellipticEmb_injective (hc : c.IsEllipticType n) (t : c.TerminalIso (trivial E)) :
    Function.Injective (ellipticEmb hc t) := by
  rw [ellipticEmb, ContinuousMonoidHom.coe_comp, ContinuousMonoidHom.coe_comp]
  exact t.toPi.injective.comp ((ContinuousMulEquiv.injective _).comp
    (ElemOp.quotHom_injective _ _))

theorem isOpen_range_ellipticEmb (hc : c.IsEllipticType n) (t : c.TerminalIso (trivial E)) :
    IsOpen (Set.range (ellipticEmb hc t)) := by
  rw [ellipticEmb, ContinuousMonoidHom.coe_comp, ContinuousMonoidHom.coe_comp, Set.range_comp,
    Set.range_comp]
  exact t.toPi.toHomeomorph.isOpenMap _
    ((ContinuousMulEquiv.toHomeomorph _).isOpenMap _ (ElemOp.isOpen_range_quotHom _ _))

/-- The open immersion `Π_V = Π_{n+4} ↪ Π_{n+3} = Π_D` (the operation `⋏` before the last). -/
def ellipticIncl (hc : c.IsEllipticType n) :
    (c.objN (n + 4) (by have := hc.len_eq; omega)).grp →ₜ*
      (c.objN (n + 3) (by have := hc.len_eq; omega)).grp :=
  (c.opN (n + 3) (by have := hc.len_eq; omega)).coverHom hc.2.2.2.2.2.1

/-- **The candidate produced by an elliptic-type chain** ([AbsTopII] Cor 3.3 (iii)(a)): `Π_U ↠ Π_D`
is the composite of the `•`'s (from `Π_3` to the third to last group `Π_{n+3}`), `Π_V ↪ Π_D` is the
operation `⋏` before the last, and `Π_V ↪ Π` is the last operation `⋎` followed by `t`. -/
def ellipticCandidate (hc : c.IsEllipticType n) (t : c.TerminalIso (trivial E)) :
    EllCandidate E where
  PiU := (c.objN 3 (by have := hc.len_eq; omega)).grp
  PiD := (c.objN (n + 3) (by have := hc.len_eq; omega)).grp
  PiV := (c.objN (n + 4) (by have := hc.len_eq; omega)).grp
  surj := (ContinuousMonoidHom.toContinuousMonoidHom
      (c.objCongr (a := 3 + n) (b := n + 3) (by omega)
        (by have := hc.len_eq; omega) (by have := hc.len_eq; omega))).comp
    (c.runHom 3 n _ hc.isDecuspRun)
  surj_surjective := by
    rw [ContinuousMonoidHom.coe_comp]
    exact (ContinuousMulEquiv.surjective _).comp (c.runHom_surjective _ _ _ _)
  incl := ellipticIncl hc
  incl_injective := ElemOp.coverHom_injective _ _
  isOpen_range_incl := ElemOp.isOpen_range_coverHom _ _
  emb := ellipticEmb hc t
  emb_injective := ellipticEmb_injective hc t
  isOpen_range_emb := isOpen_range_ellipticEmb hc t

variable {E' : CuspidalExt.{u}} {Φ : E.Iso E'}

theorem IsEllipticType.transport (hc : c.IsEllipticType n) :
    (c.transport Φ).IsEllipticType n := by
  obtain ⟨hlen, h0, h1, h2, h3, h4, h5⟩ := hc
  exact ⟨hlen, (ElemOp.kind_transport _).trans h0, (ElemOp.kind_transport _).trans h1,
    (ElemOp.kind_transport _).trans h2, fun s hs ↦ (ElemOp.kind_transport _).trans (h3 s hs),
    (ElemOp.kind_transport _).trans h4, (ElemOp.kind_transport _).trans h5⟩

end PiChain

/-- **Elliptic cuspidalisation candidates of `Π`** ([AbsTopII] Cor 3.3 (iii)(a)): all
`Π_U ↠ Π_D ↩ Π_V ↪ Π` produced by elliptic-type `Π`-chains with a terminal isomorphism to the
trivial chain. This is defined from the cuspidal extension `E` alone. -/
def ellipticCusp (E : CuspidalExt.{u}) : Set (EllCandidate E) :=
  {x | ∃ (c : PiChain E) (n : ℕ) (hc : c.IsEllipticType n)
    (t : c.TerminalIso (PiChain.trivial E)), PiChain.ellipticCandidate hc t = x}

/-- **Functoriality of the elliptic cuspidalisation candidates** in isomorphisms of cuspidal
extensions ([AbsTopI] Theorem 4.7 (ii)). -/
theorem ellipticCusp_transport {E' : CuspidalExt.{u}} (Φ : E.Iso E') {x : EllCandidate E}
    (hx : x ∈ ellipticCusp E) : x.transport Φ ∈ ellipticCusp E' := by
  obtain ⟨c, n, hc, t, rfl⟩ := hx
  refine ⟨c.transport Φ, n, hc.transport, t.transportTrivial, ?_⟩
  simp only [PiChain.ellipticCandidate, EllCandidate.transport]
  congr 1
  · ext y
    simp only [ContinuousMonoidHom.comp_toFun]
    rw [PiChain.runHom_transport]
    rfl
  · exact ElemOp.coverHom_transport (Φ := Φ) _ _
  · ext y
    have hq := DFunLike.congr_fun (ElemOp.quotHom_transport (Φ := Φ)
      (c.opN (n + 4) (by have := hc.len_eq; omega)) hc.2.2.2.2.2.2) y
    simp only [PiChain.ellipticEmb, ContinuousMonoidHom.comp_toFun]
    erw [hq, PiChain.objCongr_transport]
    rfl

end Belyi.Anabelian
