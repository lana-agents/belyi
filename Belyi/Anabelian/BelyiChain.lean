/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Anabelian.ChainTransport

/-!
# Belyi-type `Π`-chains and the cuspidalisations they produce ([AbsTopII] Cor 3.7 (a))

[AbsTopII] Corollary 3.7 (a) (`Topics in Absolute Anabelian Geometry II.txt` l.4743–4753): for
some normal open `Π_V ⊆ Π` "there exists a [not necessarily unique] `Π`-chain, which admits an
entirely group-theoretic description, with associated type-chain

  `⋏, ⋎, •, …, •, ⋏, •, …, •, ⋎`

— cf. Example 3.6 (ii) — that admits a terminal isomorphism with the trivial `Π`-chain [of length
`0`] such that if we write `U = V ×_X U_X`, `Π_U = Π_V ×_Π Π_{U_X}`, then the natural surjection
`Π_U ↠ Π_V` may be recovered from the chain of `•`'s terminating at the second to last group of
the above-mentioned `Π`-chain."

The geometric chain is `X ⇝ V ⇝ Q ⇝ Q_l ⇝ … ⇝ P ⇝ W ⇝ W_n ⇝ … ⇝ U ⇝ U_m ⇝ … ⇝ V ⇝ X* = X`
(Ex 3.6 (ii), l.4669–4680). This file is the **group-theoretic** half of step (a):

* `PiChain.IsBelyiType c l r`: the type-chain of `c` is `⋏, ⋎, •^l, ⋏, •^r, ⋎`;
* `PiChain.runHom`: the composite `Π_i ↠ Π_{i+r}` of the operation homomorphisms along a run of
  `•`'s (surjective, `PiChain.runHom_surjective`);
* `PiChain.belyiCandidate`: for such a chain, a terminal isomorphism `t` with the trivial chain
  and `m ≤ r`, the composite `Π_U ↠ Π_V` of the last `m` operations of the final `•`-run,
  together with the open embedding `Π_V ↪ Π` given by the last operation `⋎` followed by `t`;
* `belyiCusp E`: the set of all these candidates — a purely group-theoretic function of the
  cuspidal extension `E`;
* `belyiCusp_transport`: it is functorial in isomorphisms of cuspidal extensions
  ([AbsTopI] Theorem 4.7 (ii)).

That every candidate arises from a cuspidalisation `U ⊆ V` of curves over a number field, and
conversely (the specification of the algorithm), is the geometric half of MR8; it uses the
equivalence `Chain(X̃/X) ≃ Chain(Π)` of [AbsTopI] Theorem 4.7 (i) and hence the rel-isom-DGC.
-/

universe u

namespace Belyi.Anabelian

variable {E : CuspidalExt.{u}}

namespace ElemOp

variable {A B : ChainObj E}

/-- The operation homomorphism `Π_j ↠ Π_{j+1}` of an operation of type `•`. -/
def decuspHom : (o : ElemOp A B) → o.kind = .decusp → (A.grp →ₜ* B.grp)
  | decusp φ .., _ => φ
  | cover .., h => absurd h (by simp [kind])
  | quot .., h => absurd h (by simp [kind])
  | deorb .., h => absurd h (by simp [kind])

theorem decuspHom_surjective : ∀ (o : ElemOp A B) (h : o.kind = .decusp),
    Function.Surjective (o.decuspHom h)
  | decusp _ surj .., _ => surj
  | cover .., h => absurd h (by simp [kind])
  | quot .., h => absurd h (by simp [kind])
  | deorb .., h => absurd h (by simp [kind])

/-- The operation homomorphism `Π_j ↪ Π_{j+1}` of an operation of type `⋎`. -/
def quotHom : (o : ElemOp A B) → o.kind = .quot → (A.grp →ₜ* B.grp)
  | quot φ .., _ => φ
  | cover .., h => absurd h (by simp [kind])
  | decusp .., h => absurd h (by simp [kind])
  | deorb .., h => absurd h (by simp [kind])

theorem quotHom_injective : ∀ (o : ElemOp A B) (h : o.kind = .quot),
    Function.Injective (o.quotHom h)
  | quot _ inj .., _ => inj
  | cover .., h => absurd h (by simp [kind])
  | decusp .., h => absurd h (by simp [kind])
  | deorb .., h => absurd h (by simp [kind])

theorem isOpen_range_quotHom : ∀ (o : ElemOp A B) (h : o.kind = .quot),
    IsOpen (Set.range (o.quotHom h))
  | quot _ _ isOpen _, _ => isOpen
  | cover .., h => absurd h (by simp [kind])
  | decusp .., h => absurd h (by simp [kind])
  | deorb .., h => absurd h (by simp [kind])

variable {E' : CuspidalExt.{u}} {Φ : E.Iso E'}

theorem decuspHom_transport : ∀ (o : ElemOp A B) (h : o.kind = .decusp),
    (o.transport Φ).decuspHom (by rw [kind_transport]; exact h) = o.decuspHom h
  | decusp .., _ => rfl
  | cover .., h => absurd h (by simp [kind])
  | quot .., h => absurd h (by simp [kind])
  | deorb .., h => absurd h (by simp [kind])

theorem quotHom_transport : ∀ (o : ElemOp A B) (h : o.kind = .quot),
    (o.transport Φ).quotHom (by rw [kind_transport]; exact h) = o.quotHom h
  | quot .., _ => rfl
  | cover .., h => absurd h (by simp [kind])
  | decusp .., h => absurd h (by simp [kind])
  | deorb .., h => absurd h (by simp [kind])

end ElemOp

namespace PiChain

variable (c : PiChain E)

/-- The object `Π_n` of a chain, indexed by a natural number `n ≤ len`. -/
abbrev objN (n : ℕ) (h : n ≤ c.len) : ChainObj E := c.obj ⟨n, Nat.lt_succ_of_le h⟩

/-- The identification `Π_a = Π_b` for equal indices. -/
def objCongr {a b : ℕ} (hab : a = b) (ha : a ≤ c.len) (hb : b ≤ c.len) :
    (c.objN a ha).grp ≃ₜ* (c.objN b hb).grp := by
  subst hab
  exact ContinuousMulEquiv.refl _

/-- The `j`-th operation `Π_j ⇝ Π_{j+1}`, indexed by a natural number. -/
abbrev opN (j : ℕ) (h : j < c.len) :
    ElemOp (c.objN j h.le) (c.objN (j + 1) (Nat.succ_le_of_lt h)) :=
  c.op ⟨j, h⟩

theorem kind_opN_congr {a b : ℕ} (hab : a = b) (ha : a < c.len) (hb : b < c.len) :
    (c.opN a ha).kind = (c.opN b hb).kind := by
  subst hab
  rfl

/-- `r` consecutive operations of type `•`, starting at `Π_i`. -/
def IsDecuspRun (i r : ℕ) (h : i + r ≤ c.len) : Prop :=
  ∀ s (hs : s < r), (c.opN (i + s) (by omega)).kind = .decusp

/-- **The composite along a run of `•`'s**: `Π_i ↠ Π_{i+r}`. -/
def runHom (i : ℕ) : (r : ℕ) → (h : i + r ≤ c.len) → c.IsDecuspRun i r h →
    ((c.objN i (by omega)).grp →ₜ* (c.objN (i + r) h).grp)
  | 0, _, _ => ContinuousMonoidHom.id _
  | r + 1, h, hrun =>
      ((c.opN (i + r) (by omega)).decuspHom (hrun r (by omega))).comp
        (runHom i r (by omega) fun s hs ↦ hrun s (by omega))

theorem runHom_surjective (i : ℕ) : ∀ (r : ℕ) (h : i + r ≤ c.len) (hrun : c.IsDecuspRun i r h),
    Function.Surjective (c.runHom i r h hrun)
  | 0, _, _ => Function.surjective_id
  | r + 1, h, hrun =>
      (ElemOp.decuspHom_surjective _ _).comp (runHom_surjective i r (by omega) _)

/-- **Belyi-type chains** ([AbsTopII] Ex 3.6 (ii), Cor 3.7 (a)): the type-chain of `c` is
`⋏, ⋎, •^l, ⋏, •^r, ⋎` (so `len = l + r + 4`). -/
def IsBelyiType (l r : ℕ) : Prop :=
  ∃ hlen : c.len = l + r + 4,
    (c.opN 0 (by omega)).kind = .cover ∧ (c.opN 1 (by omega)).kind = .quot ∧
    (∀ s (hs : s < l), (c.opN (2 + s) (by omega)).kind = .decusp) ∧
    (c.opN (l + 2) (by omega)).kind = .cover ∧
    (∀ s (hs : s < r), (c.opN (l + 3 + s) (by omega)).kind = .decusp) ∧
    (c.opN (l + r + 3) (by omega)).kind = .quot

variable {c}

theorem IsBelyiType.len_eq {l r : ℕ} (hc : c.IsBelyiType l r) : c.len = l + r + 4 := hc.1

/-- The last `m ≤ r` operations of the final `•`-run of a Belyi-type chain form a run. -/
theorem IsBelyiType.isDecuspRun {l r : ℕ} (hc : c.IsBelyiType l r) (m : ℕ) (hm : m ≤ r) :
    c.IsDecuspRun (l + 3 + (r - m)) m (by have := hc.len_eq; omega) := by
  obtain ⟨hlen, -, -, -, -, hrun, -⟩ := hc
  intro s hs
  rw [c.kind_opN_congr (b := l + 3 + (r - m + s)) (by omega) _ (by omega)]
  exact hrun (r - m + s) (by omega)

end PiChain

/-- A **cuspidalisation candidate** for `Π`: a surjection `Π_U ↠ Π_V` of profinite groups together
with an open embedding `Π_V ↪ Π`. -/
structure CuspCandidate (E : CuspidalExt.{u}) where
  /-- The group `Π_U`. -/
  PiU : ProfiniteGrp.{u}
  /-- The group `Π_V`. -/
  PiV : ProfiniteGrp.{u}
  /-- The surjection `Π_U ↠ Π_V`. -/
  surj : PiU →ₜ* PiV
  surj_surjective : Function.Surjective surj
  /-- The open embedding `Π_V ↪ Π`. -/
  emb : PiV →ₜ* E.Pi
  emb_injective : Function.Injective emb
  isOpen_range_emb : IsOpen (Set.range emb)

namespace PiChain

variable {c : PiChain E} {l r : ℕ}

/-- A terminal isomorphism with the trivial chain, as an isomorphism `Πₙ ≅ Π`. -/
def TerminalIso.toPi (t : c.TerminalIso (trivial E)) : (c.objN c.len le_rfl).grp ≃ₜ* E.Pi :=
  t.iso

/-- The open embedding `Π_V = Π_{len-1} ↪ Π_len ≅ Π` of a Belyi-type chain with a terminal
isomorphism to the trivial chain. -/
def belyiEmb (hc : c.IsBelyiType l r) (t : c.TerminalIso (trivial E)) :
    (c.objN (l + r + 3) (by have := hc.len_eq; omega)).grp →ₜ* E.Pi :=
  (ContinuousMonoidHom.toContinuousMonoidHom t.toPi).comp
    ((ContinuousMonoidHom.toContinuousMonoidHom
        (c.objCongr (a := l + r + 3 + 1) (b := c.len) (by have := hc.len_eq; omega)
          (by have := hc.len_eq; omega) le_rfl)).comp
      ((c.opN (l + r + 3) (by have := hc.len_eq; omega)).quotHom hc.2.2.2.2.2.2))

theorem belyiEmb_injective (hc : c.IsBelyiType l r) (t : c.TerminalIso (trivial E)) :
    Function.Injective (belyiEmb hc t) := by
  rw [belyiEmb, ContinuousMonoidHom.coe_comp, ContinuousMonoidHom.coe_comp]
  exact t.toPi.injective.comp ((ContinuousMulEquiv.injective _).comp
    (ElemOp.quotHom_injective _ _))

theorem isOpen_range_belyiEmb (hc : c.IsBelyiType l r) (t : c.TerminalIso (trivial E)) :
    IsOpen (Set.range (belyiEmb hc t)) := by
  rw [belyiEmb, ContinuousMonoidHom.coe_comp, ContinuousMonoidHom.coe_comp, Set.range_comp,
    Set.range_comp]
  exact t.toPi.toHomeomorph.isOpenMap _
    ((ContinuousMulEquiv.toHomeomorph _).isOpenMap _ (ElemOp.isOpen_range_quotHom _ _))

/-- **The candidate produced by a Belyi-type chain** ([AbsTopII] Cor 3.7 (a)): `Π_U ↠ Π_V` is
the composite of the last `m ≤ r` operations `•` (ending at the second to last group `Π_V`), and
`Π_V ↪ Π` is the last operation `⋎` followed by the terminal isomorphism. -/
def belyiCandidate (hc : c.IsBelyiType l r) (t : c.TerminalIso (trivial E)) (m : ℕ)
    (hm : m ≤ r) : CuspCandidate E where
  PiU := (c.objN (l + 3 + (r - m)) (by have := hc.len_eq; omega)).grp
  PiV := (c.objN (l + r + 3) (by have := hc.len_eq; omega)).grp
  surj := (ContinuousMonoidHom.toContinuousMonoidHom
      (c.objCongr (a := l + 3 + (r - m) + m) (b := l + r + 3) (by omega)
        (by have := hc.len_eq; omega) (by have := hc.len_eq; omega))).comp
    (c.runHom (l + 3 + (r - m)) m _ (hc.isDecuspRun m hm))
  surj_surjective := by
    rw [ContinuousMonoidHom.coe_comp]
    exact (ContinuousMulEquiv.surjective _).comp (c.runHom_surjective _ _ _ _)
  emb := belyiEmb hc t
  emb_injective := belyiEmb_injective hc t
  isOpen_range_emb := isOpen_range_belyiEmb hc t

end PiChain

/-- **Belyi cuspidalisation candidates of `Π`** ([AbsTopII] Cor 3.7 (a)): all `Π_U ↠ Π_V ↪ Π`
produced by Belyi-type `Π`-chains with a terminal isomorphism to the trivial chain. This is
defined from the cuspidal extension `E` alone. -/
def belyiCusp (E : CuspidalExt.{u}) : Set (CuspCandidate E) :=
  {x | ∃ (c : PiChain E) (l r : ℕ) (hc : c.IsBelyiType l r)
    (t : c.TerminalIso (PiChain.trivial E)) (m : ℕ) (hm : m ≤ r),
    PiChain.belyiCandidate hc t m hm = x}

/-! ### Functoriality ([AbsTopI] Theorem 4.7 (ii)) -/

namespace CuspCandidate

variable {E' : CuspidalExt.{u}}

/-- Transport of a candidate along `Φ : E ≅ E'`: compose the embedding with `Π ≅ Π'`. -/
def transport (Φ : E.Iso E') (x : CuspCandidate E) : CuspCandidate E' where
  PiU := x.PiU
  PiV := x.PiV
  surj := x.surj
  surj_surjective := x.surj_surjective
  emb := (ContinuousMonoidHom.toContinuousMonoidHom Φ.pi).comp x.emb
  emb_injective := by
    rw [ContinuousMonoidHom.coe_comp]
    exact Φ.pi.injective.comp x.emb_injective
  isOpen_range_emb := by
    rw [ContinuousMonoidHom.coe_comp, Set.range_comp]
    exact Φ.pi.toHomeomorph.isOpenMap _ x.isOpen_range_emb

end CuspCandidate

namespace PiChain

variable {E' : CuspidalExt.{u}} {Φ : E.Iso E'} (c : PiChain E)

theorem objCongr_transport {a b : ℕ} (hab : a = b) (ha : a ≤ c.len) (hb : b ≤ c.len) :
    (c.transport Φ).objCongr hab ha hb = c.objCongr hab ha hb := by
  subst hab
  rfl

theorem runHom_transport (i : ℕ) : ∀ (r : ℕ) (h : i + r ≤ c.len) (hrun : c.IsDecuspRun i r h)
    (hrun' : (c.transport Φ).IsDecuspRun i r h),
    (c.transport Φ).runHom i r h hrun' = c.runHom i r h hrun
  | 0, _, _, _ => rfl
  | r + 1, h, hrun, hrun' => by
      simp only [runHom]
      rw [runHom_transport i r (by omega) _ _]
      exact congrArg (fun φ ↦ ContinuousMonoidHom.comp φ
          (c.runHom i r (by omega) fun s hs ↦ hrun s (by omega)))
        (ElemOp.decuspHom_transport (Φ := Φ) (c.opN (i + r) (by omega)) (hrun r (by omega)))

variable {c}

theorem IsBelyiType.transport {l r : ℕ} (hc : c.IsBelyiType l r) :
    (c.transport Φ).IsBelyiType l r := by
  obtain ⟨hlen, h0, h1, h2, h3, h4, h5⟩ := hc
  exact ⟨hlen, (ElemOp.kind_transport _).trans h0, (ElemOp.kind_transport _).trans h1,
    fun s hs ↦ (ElemOp.kind_transport _).trans (h2 s hs), (ElemOp.kind_transport _).trans h3,
    fun s hs ↦ (ElemOp.kind_transport _).trans (h4 s hs), (ElemOp.kind_transport _).trans h5⟩

/-- Transport of a terminal isomorphism with the trivial chain. -/
def TerminalIso.transportTrivial (t : c.TerminalIso (trivial E)) :
    (c.transport Φ).TerminalIso (trivial E') where
  iso := (TerminalIso.toPi t).trans Φ.pi
  over := by
    obtain ⟨g, hg⟩ := t.over
    refine ⟨Φ.g g, fun x ↦ ?_⟩
    change E'.pr (Φ.pi (t.iso x)) = Φ.g g * Φ.g (c.last.toG x) * (Φ.g g)⁻¹
    rw [Φ.pr_comm]
    change Φ.g ((trivial E).last.toG (t.iso x)) = _
    rw [hg, map_mul, map_mul, map_inv]

end PiChain

/-- **Functoriality of the Belyi cuspidalisation candidates** in isomorphisms of cuspidal
extensions ([AbsTopI] Theorem 4.7 (ii)): transporting a candidate of `Π` along `Φ : Π ≅ Π'` gives
a candidate of `Π'`. -/
theorem belyiCusp_transport {E' : CuspidalExt.{u}} (Φ : E.Iso E') {x : CuspCandidate E}
    (hx : x ∈ belyiCusp E) : x.transport Φ ∈ belyiCusp E' := by
  obtain ⟨c, l, r, hc, t, m, hm, rfl⟩ := hx
  refine ⟨c.transport Φ, l, r, hc.transport, t.transportTrivial, m, hm, ?_⟩
  simp only [PiChain.belyiCandidate, CuspCandidate.transport]
  congr 1
  · ext y
    simp only [ContinuousMonoidHom.comp_toFun]
    rw [PiChain.runHom_transport]
    rfl
  · ext y
    have hq := DFunLike.congr_fun (ElemOp.quotHom_transport (Φ := Φ)
      (c.opN (l + r + 3) (by have := hc.len_eq; omega)) hc.2.2.2.2.2.2) y
    simp only [PiChain.belyiEmb, ContinuousMonoidHom.comp_toFun]
    erw [hq, PiChain.objCongr_transport]
    rfl

end Belyi.Anabelian
