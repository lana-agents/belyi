/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Rigidity
import Mathlib.Algebra.Algebra.Rat

/-!
# Spreading out a Belyi pair (B10(ii)): the `SpreadOut` structure and its sanctioned axiom

This file packages statement **B10(ii)** of `references/proof-outline.md` — the
spreading-out step of the *converse* direction of Belyi's theorem — as a Lean `structure`
bundling the output of spreading a Belyi pair out to a family, together with **one
clearly-named sanctioned axiom** producing such a structure. See
`references/converse-design.md` §3a for the full design decision; this mirrors exactly how
`Belyi/Rigidity.lean` isolates the Riemann-existence input **B9** as the single axiom
`Belyi.rigidity_finiteness`.

## The mathematical content (B10, [Koeck2004] §2, [Szamuely2009] §4.8)

Let `(X, f : X ⟶ ℙ¹_K)` be a Belyi pair over `K = ℂ` (an algebraically closed
characteristic-zero field containing `ℚ̄ = k`). Being of finite presentation, `(X, f)` is
definable over a subfield `L ⊆ K` finitely generated over `ℚ̄` (this first sub-step,
**B10(i)**, is genuinely provable against mathlib v4.32 and is handled separately in
taxis #196). Writing `L = ℚ̄(V)` for a smooth affine `ℚ̄`-variety `V`, one spreads
`(X_L, f_L)` out to a family `𝒳 ⟶ ℙ¹_U ⟶ U` over a dense open `U ⊆ V` such that:

* every closed `ℚ̄`-point `u ∈ U(ℚ̄)` has fibre `(𝒳_u, f_u)` a degree-`≤ d` Belyi cover of
  `ℙ¹` over `ℚ̄`, and
* the generic fibre, base-changed to `K`, recovers `(X, f)`.

Propagating the Belyi-pair property from the generic fibre to a dense open of closed
`ℚ̄`-fibres (openness/constructibility of the good-fibre locus) is EGA IV limit formalism
and is **absent from mathlib v4.32** (see `references/converse-design.md` §4). We therefore
package the output as `Belyi.SpreadOut` and axiomatize its existence as
`Belyi.belyi_spreadOut`, exactly as B9 is axiomatized in `Belyi/Rigidity.lean`.

## Main definitions

* `Belyi.SpreadOut k K X f`: the data produced by spreading `(X, f)` out — the base `U`
  (a `ℚ̄`-scheme), a distinguished `ℚ̄`-point, the degree bound `d`, and the assignment of
  a degree-`≤ d` Belyi cover `BelyiCover k d` (the fibre `(𝒳_u, f_u)`) to each `ℚ̄`-point
  `u ∈ U(ℚ̄)`.

## Main statement

* `Belyi.belyi_spreadOut`: **the sanctioned axiom** — every Belyi pair over `K = ℂ`
  spreads out, i.e. gives rise to a `SpreadOut` datum. This is one of the two converse
  axioms (alongside `Belyi.spreadOut_isotrivial_point` of `Belyi/Descent.lean`, taxis
  #198), enumerated for the main theorem's `#print axioms` next to `rigidity_finiteness`.

## Interface notes

The degree bound `d` is carried so that B9 (`rigidity_finiteness k d`) is applicable to
the family in the rigidity/isotriviality step **B11** (`Belyi/Descent.lean`, taxis #198),
which consumes this structure. The generic-fibre-recovers-`(X, f)` identification is *not*
stored as a field here — a `ℚ̄`-model of `(X, f)` is precisely the converse's conclusion,
which the family does *not* directly supply (the generic fibre lives over `L = ℚ̄(V)`, not
over `ℚ̄`). That identification is produced only by the isotriviality argument, and is
delivered by `spreadOut_isotrivial_point` in `Belyi/Descent.lean`. Nothing on the *forward*
direction imports this file.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory

/-- **The data produced by spreading out a Belyi pair (B10(ii)).**

For a Belyi pair `(X, f : X ⟶ ℙ¹_K)` over `K = ℂ` (with `k = ℚ̄`), `SpreadOut k K X f`
bundles the output of spreading `(X, f)` out to a family over a dense open `U` of a smooth
affine `ℚ̄`-variety: the base `U`, a `ℚ̄`-point of it, a degree bound `d`, and, for every
`ℚ̄`-point `u ∈ U(ℚ̄)`, the fibre `(𝒳_u, f_u)` as a degree-`≤ d` Belyi cover of `ℙ¹_k`.

The existence of such a datum is the sanctioned axiom `Belyi.belyi_spreadOut`; the
rigidity/isotriviality step (`Belyi/Descent.lean`, B11) consumes it together with
`rigidity_finiteness k d` (B9). -/
structure SpreadOut (k K : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    [Field K] [Algebra k K] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))]
    (_f : X ⟶ P1 K) : Type (u + 1) where
  /-- The degree bound: every fibre is a degree-`≤ d` Belyi cover, so B9
  (`rigidity_finiteness k d`) applies to the family. -/
  d : ℕ
  /-- The base `U` of the family: a dense open of a smooth affine `ℚ̄`-variety `V` with
  function field `L = ℚ̄(V)`. -/
  base : Scheme.{u}
  /-- The base is a scheme over `ℚ̄`. -/
  [baseOver : base.Over (Spec (CommRingCat.of k))]
  /-- A distinguished `ℚ̄`-point of the base (`U` is a nonempty `ℚ̄`-variety). -/
  basePoint : Spec (CommRingCat.of k) ⟶ base
  /-- Every `ℚ̄`-point `u ∈ U(ℚ̄)` gives the fibre `(𝒳_u, f_u)` as a degree-`≤ d` Belyi
  cover of `ℙ¹_k` over `ℚ̄`. -/
  fibre : (Spec (CommRingCat.of k) ⟶ base) → BelyiCover k d

attribute [instance] SpreadOut.baseOver

/-- **B10(ii) (spreading out), axiomatized.** Every Belyi pair `(X, f)` over `K = ℂ`
(an algebraically closed characteristic-zero field containing `ℚ̄ = k`), with `X` a curve,
spreads out to a family over a dense open of a smooth affine `ℚ̄`-variety with degree-`≤ d`
Belyi fibres, i.e. gives rise to a `SpreadOut k K X f`.

Justification (NOT formalized — this is the EGA IV limit-formalism content the project
declines to build against mathlib v4.32; see `references/converse-design.md` §3a, §4):
finite presentation of `(X, f)` gives definability over a finitely generated subfield
`L = ℚ̄(V)` (taxis #196), and spreading `(X_L, f_L)` out over a dense open where all fibres
stay smooth proper curves with finite maps to `ℙ¹` branched only over `{0, 1, ∞}`
(openness of the good-fibre locus) produces the family. This is one of the two sanctioned
axioms of the converse direction, isolated in this file, alongside `rigidity_finiteness`
(B9) and `spreadOut_isotrivial_point` (B11, `Belyi/Descent.lean`). Nothing on the forward
direction depends on this file.

Per taxis #201 this is stated as a `theorem` with `sorry` rather than an `axiom`, so that
the outstanding proof obligation is surfaced honestly (`sorryAx` in `#print axioms`, a
`sorry` warning at build) and tracked as a concrete goal. The proof is the research-grade
EGA IV spreading-out content scoped in issue #200 (de-axiomatize B10(ii)/B11). -/
theorem belyi_spreadOut (k K : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    [Algebra.IsAlgebraic ℚ k] [Field K] [IsAlgClosed K] [CharZero K] [Algebra k K]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X]
    (f : X ⟶ P1 K) (hf : IsBelyiMap K f) : Nonempty (SpreadOut k K X f) := sorry

end Belyi
