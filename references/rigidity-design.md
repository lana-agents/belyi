# Rigidity input (B9): design decision

Taxis issue **#52** — *Finiteness of covers of `ℙ¹` étale outside `{0, 1, ∞}`*.
This is the deepest external input to the **converse** direction of Belyi's theorem
(`references/proof-outline.md`, statements **B9 → B11 → B12**). This document is the
issue's first deliverable: it fixes *what is proved vs. what is axiomatized*, the exact
Lean statement of the axiomatized core, and the split into child issues. It is a
proposal for maintainer sign-off before any large-scale proof work begins.

## 0. TL;DR of the decision

* **Axiomatize** the geometry-to-group-theory bridge (Riemann existence + finite
  generation of the étale fundamental group of the thrice-punctured line + invariance
  under extension of algebraically closed fields of char 0). This is genuinely far from
  mathlib v4.32 (no analytification, no GAGA, no computation of `π₁^ét`), and the whole
  project's converse rests on it. It becomes **one clearly-named axiom in one file**,
  exactly as the definition-of-done of the main-theorem issue (#55) anticipates:
  *"no axioms beyond what the rigidity issue's design document explicitly sanctioned;
  if any remain, they must be isolated in one clearly named file."*
* **Prove** the elementary group-theoretic half: a rank-2 free group has only finitely
  many subgroups of index `≤ d`. Mathlib has all the ingredients (`FreeGroup`, `Schreier`,
  `Subgroup.index`, `Equiv.Perm (Fin n)` finiteness). This is a self-contained, reusable,
  upstreamable lemma with **no** geometric prerequisites.
* The **consumer** (B11, issue #53) needs finiteness of isomorphism classes of covers,
  *not* the group-theory statement directly. So the axiom is stated on the geometric side
  (finiteness of iso-classes of degree-`≤ d` Belyi-type covers), and the group-theory
  lemma is the intended *evidence* that the axiom is true — recorded here, formalized as a
  standalone lemma, but not logically wired into the axiom (that wiring is the Riemann-
  existence content we are declining to formalize).

This keeps the *provable* mathematics honest and in Lean, isolates the *one* deep analytic
input, and gives B11 a clean hypothesis to consume.

## 1. The mathematical statement (B9)

Fix `d ≥ 1` and an algebraically closed field `k` of characteristic 0.

> Up to isomorphism over `ℙ¹_k`, there are only finitely many finite morphisms
> `f : X ⟶ ℙ¹_k` of degree `≤ d`, with `X` a curve over `k`, that are étale outside
> `{0, 1, ∞}` (equivalently — in the project's vocabulary — Belyi maps of degree `≤ d`).

Two classical routes (see [Szamuely2009, §4.6, §4.8], [Guillot2014, §1–4], SGA 1 XIII):

1. **Riemann existence (over `ℂ`).** Finite étale covers of `ℙ¹_ℂ ∖ {0,1,∞}` correspond
   to finite `π₁^top`-sets, and `π₁^top(ℙ¹_ℂ ∖ {0,1,∞}) ≅ F₂` (free of rank 2, the loops
   around two of the three punctures). Connected covers of degree `n` ↔ conjugacy classes
   of index-`n` subgroups of `F₂`; general degree-`≤ d` covers ↔ finite `F₂`-sets of
   cardinality `≤ d`. A finitely generated group has finitely many subgroups of each
   finite index, so there are finitely many such covers. The smooth compactification (the
   normalization of `ℙ¹` in the cover's function field) recovers the *curve* `X` and the
   *finite* map `f`, with the branch locus inside `{0,1,∞}`.
2. **Étale `π₁` (arbitrary `k`).** `π₁^ét(ℙ¹_k ∖ {0,1,∞})` for `k` algebraically closed of
   char 0 is the profinite completion `F̂₂` (SGA 1 XIII, again resting on Riemann existence
   through the Lefschetz-principle / char-0 comparison), and the category of finite étale
   covers is the category of finite continuous `F̂₂`-sets; degree `≤ d` ⇒ finitely many.
   Invariance under extension of algebraically closed fields of char 0 (SGA 1 XIII 4.6)
   transfers the count from `ℂ` to `ℚ̄` and to `ℚ̄(V)‾` (the field B11 actually works over).

Both routes have the same **formalization boundary**: everything reduces to the free group
`F₂`, and the reduction is exactly the content mathlib lacks.

## 2. What mathlib v4.32 has, and where the wall is

Present and usable:

* `Mathlib/CategoryTheory/Galois/` — Galois categories, fiber functors, the automorphism
  group of the fiber functor as fundamental group (`Galois/IsFundamentalgroup.lean`,
  `Prorepresentability.lean`), the equivalence of a Galois category with finite
  `Aut(fiber)`-sets. This is the *categorical* target of both routes.
* `Mathlib/AlgebraicGeometry/Morphisms/Etale.lean`, finite morphisms, and
  `Mathlib/AlgebraicGeometry/Normalization.lean` (compactification: normalization of `ℙ¹`
  in a function field), `ZariskisMainTheorem.lean`.
* `Mathlib/GroupTheory/FreeGroup/…`, `Schreier.lean` (Schreier's lemma: finite-index
  subgroup of a f.g. group is f.g.), `Index.lean` (`Subgroup.index`, `FiniteIndex`),
  `Equiv.Perm (Fin n)` and its finiteness.

The wall (not in mathlib v4.32, not close):

* **Analytification / GAGA / Riemann existence.** No comparison between finite étale covers
  of a `ℂ`-variety and topological covers of its analytification. No `π₁^top` of an
  algebraic variety, no Riemann existence theorem. `AlgebraicTopology/FundamentalGroupoid`
  is purely topological and unconnected to schemes.
* **Computation of `π₁^ét(ℙ¹_k ∖ {0,1,∞})`.** The Galois-category framework can *define*
  the étale fundamental group as `Aut` of a fiber functor, but there is no theorem
  identifying it (even its finite quotients) with `F₂`/`F̂₂`. That identification is the
  Riemann-existence content.
* **Invariance under extension of algebraically closed base fields.** No base-change
  invariance theorem for the category of finite étale covers in char 0.

Conclusion: the reduction "covers of `ℙ¹∖{0,1,∞}` ↔ `F₂`-data" cannot be formalized against
mathlib v4.32 without importing a very large body of analytic/étale-homotopy theory. It is
the correct axiomatization boundary.

## 3. The Lean plan

### 3a. The axiom (sanctioned, isolated) — `Belyi/Rigidity.lean`

State B9 directly on the geometric side, in the project's own vocabulary
(`Belyi.IsBelyiMap`, `Belyi.IsCurveOver`, degree), so that B11 consumes it with no
group-theory in sight. Proposed shape (final types to be pinned when B10/B11 fix the
consumer interface — see §4):

```text
/-- **B9 (rigidity input), axiomatized.**  For `k` algebraically closed of characteristic
0 and `d ≥ 1`, there are — up to isomorphism over `ℙ¹_k` — only finitely many curves `X/k`
with a finite morphism `f : X ⟶ ℙ¹_k` of degree `≤ d` étale outside `{0,1,∞}` (i.e. only
finitely many isomorphism classes of degree-`≤ d` Belyi maps).

Justification (NOT formalized): Riemann existence identifies such covers with finite
`F₂`-sets of cardinality `≤ d`; `Belyi.finite_boundedIndex_subgroups_freeGroupTwo` (§3b)
is the finite-group-theory core.  See `references/rigidity-design.md`. -/
axiom Belyi.rigidity_finiteness (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (d : ℕ) : Finite (BelyiCover.Iso k d)
```

where `BelyiCover k d` bundles `(X, f, curve/finite/degree≤d/branch⊆{0,1,∞})` and
`BelyiCover.Iso k d` is its quotient by isomorphism over `ℙ¹_k`. The bundling structure and
the "degree" field are the concrete design work of the child issue #52a (§4); a
`Setoid`/`Quotient` or a `Quot` by the "iso over `ℙ¹`" relation is the natural encoding of
"finitely many up to isomorphism".

**Degree.** Use the function-field degree: for a finite dominant `f : X ⟶ ℙ¹_k` of integral
curves, `deg f := Module.finrank (ℙ¹_k).functionField X.functionField` via the induced
finite extension of function fields (`Belyi/FunctionField.lean` already provides the algebra
instances). This is base-field-invariant and matches the classical `deg`. Alternative
(equivalent, heavier): the constant rank of the finite locally free sheaf `f_* 𝒪_X`.

This file must be the **only** `axiom` in the project (checked with `#print axioms` on the
main theorem in #55).

### 3b. The provable core — `Belyi/RigidityGroupTheory.lean`

A standalone, geometry-free lemma (upstreamable to mathlib):

```text
/-- A finitely generated group has only finitely many subgroups of index `≤ d`; in
particular the rank-2 free group `F₂ = FreeGroup (Fin 2)` does.  This is the finite
combinatorial fact underlying the rigidity axiom `Belyi.rigidity_finiteness`. -/
theorem finite_boundedIndex_subgroups (G : Type*) [Group G] [Group.FG G] (d : ℕ) :
    {H : Subgroup G // H.index ≤ d ∧ H.index ≠ 0}.Finite
```

Proof strategy (elementary, ~100–200 lines):

* A subgroup `H ≤ G` of index `n` (`1 ≤ n ≤ d`) gives the coset action
  `G →* Equiv.Perm (G ⧸ H)`; transporting along any bijection `G ⧸ H ≃ Fin n` yields a
  homomorphism `φ_H : G →* Equiv.Perm (Fin n)` and a distinguished point `i_H : Fin n`
  (the image of the coset `H`) with `H = (φ_H.comp …).stabilizer i_H` (the point
  stabilizer). So `H ↦ (n, φ_H, i_H)` is well-defined into `Σ n ≤ d, (G →* Perm (Fin n)) × Fin n`
  after fixing, for each `H`, one such bijection.
* `G →* Equiv.Perm (Fin n)` is a finite type: `G` is finitely generated, so a hom is
  determined by the images of a finite generating set, giving an injection into
  `(Equiv.Perm (Fin n)) ^ (generators)`, a finite type. (Mathlib: `Group.FG` gives a finite
  generating `Finset`; `MonoidHom.ext` + evaluation on generators is the injection.)
* `H` is recovered from `(n, φ_H, i_H)` as the point stabilizer, so the map `H ↦ (n,φ_H,i_H)`
  is injective; the codomain is finite, hence the domain is finite.

Specialize to `G = FreeGroup (Fin 2)` (which is `Group.FG` — `FreeGroup.instFG`/generated by
the image of `Fin 2`) to get `finite_boundedIndex_subgroups_freeGroupTwo`.

This lemma is **not** imported by `Belyi/Rigidity.lean` (the axiom does not depend on it);
it is the mathematical justification, kept in the library as verified evidence and as the
piece a future full formalization of B9 would build on.

### 3c. Wiring

`Belyi/Rigidity.lean` and `Belyi/RigidityGroupTheory.lean` are added to the `Belyi.lean`
root import. B11 (issue #53) imports `Belyi/Rigidity.lean` and consumes
`Belyi.rigidity_finiteness`. Nothing on the **forward** direction (#51) depends on either
file, so the forward half of the theorem remains fully axiom-free.

## 4. Child-issue split (proposed)

* **#52a — Bundled Belyi cover + degree + iso-quotient, and the axiom.**
  Deliver `Belyi/Rigidity.lean`: the `BelyiCover k d` structure (curve `X`, finite
  `f : X ⟶ ℙ¹_k`, `deg f ≤ d`, `Branch f ⊆ {0,1,∞}` — reuse `IsBelyiMap`), the "isomorphism
  over `ℙ¹_k`" setoid, the quotient `BelyiCover.Iso k d`, the `deg` definition via
  `functionField`, and the single `axiom rigidity_finiteness`. Depends on #46/#47 (curve +
  branch API, both merged). This is the **second deliverable** of #52 (the Lean statement).
  *Pin the exact structure fields against B11's needs — coordinate with #53 before finalize.*

* **#52b — `finite_boundedIndex_subgroups` (provable core).**
  Deliver `Belyi/RigidityGroupTheory.lean` with the group-theory lemma of §3b and its `F₂`
  specialization. No geometric dependency; fully sorry-free and axiom-free; upstreamable.
  Can proceed **immediately and in parallel**, independent of everything else in the project.

* **#52c — (optional, research-grade) toward de-axiomatizing.**
  A placeholder/tracking issue for the eventual replacement of the axiom by a real proof
  (Riemann existence + `π₁^ét` computation), gated on major mathlib additions. Off critical
  path; record the wall from §2 so future scanners do not re-scope it. Analogous to the
  already-`[BLOCKED — research-grade]`-tagged descent issue #183.

## 5. Interaction with the rest of the converse

The converse chain is **B9 → B11 → B12** with **B10** (spreading out) feeding B11. Status:

* **B10** (spreading out, issue #53) is *also* largely absent from mathlib (EGA IV limit
  formalism), though `Mathlib/AlgebraicGeometry/SpreadingOut.lean`,
  `AffineTransitionLimit.lean`, `Morphisms/Descent.lean`, `FlatDescent.lean` give a
  starting toolkit (noted on #53). B10 must be scoped separately.
* **Descent infra** for B3c/B3d/B2b (issues #167/#168/#183) is a *different* mathlib gap
  (faithfully-flat descent of `Smooth`/`SurjectiveOnStalks` at the locus level, and the
  stalk-of-base-change comparison) and is likewise research-grade. It is orthogonal to B9:
  landing B9 does not need it and vice versa.

**Honest overall assessment.** Even with the B9 axiom in place, a *complete* converse still
requires B10 (spreading out) and the descent infrastructure, several pieces of which are
research-grade against mathlib v4.32. So this design does **not** by itself close the
converse; it removes the single deepest input (B9) as a blocker by giving it a clean,
sanctioned, isolated axiom and a proved combinatorial core, and it makes the remaining
converse work (B10/B11/B12) buildable against a fixed B9 interface. The forward direction
(#51) is unaffected and remains the axiom-free half.

## References

* [Szamuely2009] *Galois Groups and Fundamental Groups*, §4.6, §4.8 (Cor. 4.8.11 area).
* [Guillot2014] *An elementary approach to dessins d'enfants and the Grothendieck–Teichmüller
  group*, §1–4.
* SGA 1, Exp. XIII (finite generation of `π₁^ét`; 4.6 base-field invariance).
* [Koeck2004] *Belyi's theorem revisited* (`references/sources/koeck-belyi-revisited.pdf`),
  §2 (the rigidity/isotriviality argument that consumes B9).
