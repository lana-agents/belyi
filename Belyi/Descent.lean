/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.SpreadOut
import Belyi.DefinablePair

/-!
# Converse direction of Belyi's theorem (B11 + B12): descent to `ℚ̄`

This file assembles the **converse** direction of Belyi's theorem — statements **B11**
(rigidity/isotriviality) and **B12** (descent) of `references/proof-outline.md` — against
the sanctioned interface fixed in `references/converse-design.md`. It consumes:

* `Belyi.belyi_spreadOut` (B10(ii), `Belyi/SpreadOut.lean`) — spreading a Belyi pair out to
  a family with degree-`≤ d` Belyi fibres over a `ℚ̄`-variety;
* `Belyi.rigidity_finiteness` (B9, `Belyi/Rigidity.lean`) — finiteness of iso-classes of
  degree-`≤ d` Belyi covers;

and it introduces the last of the three sanctioned converse axioms,
`Belyi.spreadOut_isotrivial_point` (the B11 isom-scheme/isotriviality input).

## The rigidity argument (B11, [Koeck2004] Thm 2.2)

Given a `SpreadOut` family `𝒳/U` whose closed `ℚ̄`-fibres are degree-`≤ d` Belyi covers,
B9 says these fall into only finitely many iso-classes over `ℚ̄`. Köck's Theorem 2.2 then
forces the family to be **isotrivial on a dense open**: the isomorphism scheme
`Isom_U(𝒳, 𝒳')` is of finite type over `U`, its image is constructible (Chevalley), and,
being dominant, contains a dense open with a `ℚ̄`-point `u ∈ U(ℚ̄)` whose fibre realises the
geometric generic fibre — hence `(X, f)` after base change. So `(X, f)` descends to `ℚ̄`.

Finiteness of type of `Isom_U` and Chevalley constructibility of its image, at the required
generality, are **absent from mathlib v4.32** (see `references/converse-design.md` §4). We
therefore isolate the single clean consequence B11 needs as the sanctioned axiom
`spreadOut_isotrivial_point`, stated **taking the finiteness of iso-classes as an explicit
hypothesis** so that B9 (`rigidity_finiteness`) genuinely feeds it — and prove the wrapper
`definableOverPair_of_spreadOut` around it. (Whether the pigeonhole `Finite (BelyiCover.Iso)`
⇒ isotriviality is itself formalizable — promoting this axiom to a theorem — is the scoped
attempt of taxis #199; de-axiomatizing the full isom-scheme input is the research-grade
tracker #200.)

## Main statements

* `Belyi.spreadOut_isotrivial_point`: **sanctioned axiom** (B11 input) — a `SpreadOut`
  family with finitely many fibre iso-classes descends its pair to `ℚ̄`.
* `Belyi.definableOverPair_of_spreadOut` (B11): the proved wrapper feeding
  `rigidity_finiteness` into the axiom.
* `Belyi.definableOverPair_of_isBelyiMap` (**B12**, pair version): a Belyi pair over `ℂ` is
  definable over `ℚ̄`.
* `Belyi.definableOver_of_exists_isBelyiMap` (**B12**, scheme version): a curve over `ℂ`
  admitting a Belyi map is definable over `ℚ̄`.

Together with the forward direction (`Belyi/Forward.lean`, `Belyi/ForwardPair.lean`) these
are the two halves the main theorem (taxis #55) assembles into `belyi_iff`. By design,
`#print axioms definableOverPair_of_isBelyiMap` lists exactly the three sanctioned axioms
`rigidity_finiteness`, `belyi_spreadOut`, `spreadOut_isotrivial_point` (plus the classical
`propext`/`Classical.choice`/`Quot.sound`) — nothing else.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory

/-- **B11 input (isom-scheme / isotriviality), axiomatized.** Given a `SpreadOut` family
for a Belyi pair `(X, f)` over `K = ℂ`, together with the finiteness of iso-classes of its
degree-`≤ d` Belyi fibres (supplied by B9, `rigidity_finiteness k S.d`), the family is
isotrivial on a dense open, so a closed `ℚ̄`-point realises the geometric generic fibre and
`(X, f)` descends to `ℚ̄`: it is `DefinableOverPair k K X f`.

This isolates the single consequence of [Koeck2004, Thm 2.2] that B11 needs — the
finite-type isomorphism scheme with constructible (Chevalley) image — which is absent from
mathlib v4.32 (`references/converse-design.md` §4). It is the third and last sanctioned
axiom of the converse direction, alongside `rigidity_finiteness` (B9) and `belyi_spreadOut`
(B10(ii)). The finiteness hypothesis `hfin` is stated explicitly so that removing this axiom
reduces exactly to the pigeonhole `Finite (BelyiCover.Iso k d) ⇒ isotriviality` (taxis
#199). -/
axiom spreadOut_isotrivial_point (k K : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    [Algebra.IsAlgebraic ℚ k] [Field K] [IsAlgClosed K] [CharZero K] [Algebra k K]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {f : X ⟶ P1 K}
    (S : SpreadOut k K X f) (hfin : Finite (BelyiCover.Iso k S.d)) :
    DefinableOverPair k K X f

/-- **B11 (rigidity/isotriviality), proved wrapper.** A spread-out Belyi pair is definable
over `ℚ̄`, obtained by feeding the finiteness of iso-classes of degree-`≤ d` Belyi covers
(B9, `rigidity_finiteness`) into `spreadOut_isotrivial_point`. -/
theorem definableOverPair_of_spreadOut (k K : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    [Algebra.IsAlgebraic ℚ k] [Field K] [IsAlgClosed K] [CharZero K] [Algebra k K]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {f : X ⟶ P1 K}
    (S : SpreadOut k K X f) : DefinableOverPair k K X f :=
  spreadOut_isotrivial_point k K S (rigidity_finiteness k S.d)

/-- **B12 (converse of Belyi's theorem), pair version.** A Belyi pair `(X, f)` over `K = ℂ`
(with `X` a curve) is definable over `ℚ̄ = k`: there is a model `f₀ : X₀ ⟶ ℙ¹_{ℚ̄}` whose
base change to `K` recovers `(X, f)`.

Assembled from `belyi_spreadOut` (B10(ii)) and `definableOverPair_of_spreadOut` (B11).
This produces the **same** `DefinableOverPair` predicate the forward direction produces
(`Belyi/ForwardPair.lean`) and the main theorem (taxis #55) consumes. -/
theorem definableOverPair_of_isBelyiMap (k K : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    [Algebra.IsAlgebraic ℚ k] [Field K] [IsAlgClosed K] [CharZero K] [Algebra k K]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X]
    (f : X ⟶ P1 K) (hf : IsBelyiMap K f) : DefinableOverPair k K X f := by
  obtain ⟨S⟩ := belyi_spreadOut k K X f hf
  exact definableOverPair_of_spreadOut k K S

/-- **B12 (converse of Belyi's theorem), scheme version.** A curve `X` over `K = ℂ` that
admits a Belyi map is definable over `ℚ̄ = k`.

Follows from the pair version via `DefinableOverPair.definableOver` (merged). -/
theorem definableOver_of_exists_isBelyiMap (k K : Type u) [Field k] [IsAlgClosed k]
    [CharZero k] [Algebra.IsAlgebraic ℚ k] [Field K] [IsAlgClosed K] [CharZero K]
    [Algebra k K] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X]
    (h : ∃ f : X ⟶ P1 K, IsBelyiMap K f) : DefinableOver k K X := by
  obtain ⟨f, hf⟩ := h
  exact (definableOverPair_of_isBelyiMap k K X f hf).definableOver

end Belyi
