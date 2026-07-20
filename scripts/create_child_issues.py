#!/usr/bin/env python3
"""Create the child issues of taxis issue #18 (Belyi's theorem).

Usage:
  ./scripts/create_child_issues.py --dry-run        # list what would be created
  ./scripts/create_child_issues.py --emit-markdown  # print the specs as markdown
  TAXIS_TOKEN=... ./scripts/create_child_issues.py  # actually file the issues

Requires a taxis API token (bearer) with permission to create issues on
https://taxis.lana.merten.dev. The issue bodies are the single source of truth
for references/tasks.md, which is generated with --emit-markdown.
"""
import json
import os
import sys
import urllib.request

BASE = "https://taxis.lana.merten.dev/api"
TOKEN = os.environ.get("TAXIS_TOKEN", "")
PARENT = 18

OUTLINE = "`references/proof-outline.md`"

issues = []


def issue(title, deps, body):
    issues.append({"title": title, "deps": deps, "body": body})


issue(
    "Curve API: smooth projective curves over a field and finite morphisms to ℙ¹",
    [],
    f"""Foundational layer for the Belyi project (statement **B1** in {OUTLINE}).

### Goal

Fix the working notion of *curve over a field `k`* and provide the two basic existence results everything else consumes:

1. a predicate/class `IsCurveOver k X` for schemes `X` over `Spec k`: smooth, proper (equivalently projective in this situation), geometrically connected, of pure dimension 1 — hence geometrically integral. Check what mathlib already has (`AlgebraicGeometry.Morphisms.Smooth`, `IsProper`, finite-type conditions) and build the missing glue (geometric connectedness/integrality over a field, dimension of a scheme over a field).
2. a concrete model of `ℙ¹_k` with usable API: its closed points over an algebraically closed field are identified with `k ∪ {{∞}}`, and there is an evaluation-style interface for rational maps. Decide between `Proj k[X,Y]` and gluing two affine lines; this decision is part of the issue and should be recorded in the module docstring.

### Main theorem to prove

For a curve `X/k` and a non-constant element `t` of the function field `k(X)` (mathlib: `Scheme.functionField`), the induced morphism `X ⟶ ℙ¹_k` is finite and surjective. In particular every curve admits a finite morphism to `ℙ¹_k`.

Suggested route: `t` defines a morphism from a dense open of `X` to `ℙ¹_k`; extend over all of `X` by properness/valuative criterion in dimension 1 (smooth curve = regular, local rings are DVRs), then show the extension is proper + quasi-finite, hence finite (`IsFinite` iff proper and quasi-finite — check what mathlib has; if the quasi-finite+proper ⇒ finite implication is missing, prove it in the generality needed here or coordinate with mathlib).

### Deliverables

* `Belyi/Curve/Basic.lean` — the curve predicate and its stability lemmas.
* `Belyi/P1.lean` — the chosen model of `ℙ¹` and its point/Möbius API (Möbius maps can be a stub here; they are only seriously needed in the polynomial-reduction issues).
* `Belyi/Curve/FiniteToP1.lean` — the main theorem.

All of Part 0–3 of the outline depends on this issue, so keep the API small and stable. References: [Szamuely2009] §4.1, Stacks project 0A99 ff.""",
)

issue(
    "Ramification and branch locus of finite morphisms of curves",
    [1],
    f"""Statement **B2** (with **B2a–B2c**) in {OUTLINE}.

### Goal

For a finite morphism `f : X ⟶ Y` of curves over a field `k` of characteristic 0, define and develop:

* the **ramification locus** `Ram f ⊆ X`: the (closed) complement of the largest open on which `f` is étale. Mathlib has `IsEtale`/unramifiedness for morphisms; what is likely missing is the *étale locus* as an open subscheme/set and its behaviour. Consider defining `Ram f` via the support of the different/Kähler differentials `Ω_{{X/Y}}` (mathlib has relative differentials for schemes), which makes closedness immediate.
* the **branch locus** `Branch f := f '' Ram f ⊆ Y`, a finite set of closed points.

### Statements to prove

1. `Ram f` is closed and, in characteristic 0 (more generally when `f` is generically étale), finite; hence `Branch f` is a finite set of closed points. Key input: generic étaleness — the function-field extension `k(Y) ⊆ k(X)` is finite separable in char 0, and `f` is étale over a dense open.
2. **(B2a)** For finite `f : X ⟶ Y`, `g : Y ⟶ Z`: `Branch (f ≫ g) ⊆ g '' (Branch f) ∪ Branch g`.
3. **(B2b)** Compatibility with base change along a field extension `k ⊆ K`: `Ram (f_K) = (Ram f)_K` (char 0), and the corresponding statement for `Branch`.
4. **(B2c)** `f` restricted over `Y ∖ Branch f` is étale (and finite).

### Definition

Call `f : X ⟶ ℙ¹_k` a **Belyi map** if it is finite and `Branch f ⊆ {{0, 1, ∞}}` (using the point API of `Belyi/P1.lean`). Introduce this definition here (`Belyi/BelyiMap.lean`) so downstream issues can state everything against it.

### Deliverables

`Belyi/Ramification.lean`, `Belyi/BelyiMap.lean` with the above, plus simp/API lemmas (`Branch` of an isomorphism is empty; `Branch` of a composition with an isomorphism on either side).

References: [Szamuely2009] §4.4–4.5; Stacks 0BTC (different/ramification for curves).""",
)

issue(
    "Definability over a subfield: models of schemes and of morphisms",
    [1, 2],
    f"""Statement **B3** (with **B3a–B3d**) in {OUTLINE}.

### Goal

Formalize "`X` is definable over `k₀`" for a scheme of finite type over an extension field `K`, together with the pair version for morphisms to `ℙ¹`, and the API needed by both directions of Belyi.

### Definitions

For `k₀ ⊆ K` fields, `X` a scheme over `K`:

* `DefinableOver k₀ X` : there exists a scheme `X₀` of finite type over `k₀` and an isomorphism `X₀ ×_{{Spec k₀}} Spec K ≅ X` of schemes over `K`. (Design note: phrase base change via mathlib's `pullback` along `Spec K ⟶ Spec k₀`; provide a `Nonempty`-free constructor and an eliminator.)
* Pair version `DefinableOverPair k₀ (X, f)` for `f : X ⟶ ℙ¹_K`: a model `f₀ : X₀ ⟶ ℙ¹_{{k₀}}` whose base change is identified with `f` compatibly with the canonical identification `ℙ¹_{{k₀}} ×_{{k₀}} K ≅ ℙ¹_K` (this identification, for the chosen model of `ℙ¹`, is itself a deliverable).

### Statements to prove

1. **(B3a)** Invariance under `K`-isomorphism, in both scheme and pair versions.
2. **(B3b)** Transitivity: definable over `k₀` ⇒ definable over any intermediate `k₀ ⊆ k₁ ⊆ K` (by base-changing the model).
3. **(B3c)** If `X` is a curve over `K` (issue on curve API) and `X₀` is a model over `k₀`, then `X₀` is a curve over `k₀`, and conversely. Inputs: smoothness/properness/geometric connectedness are stable under base change, and descend along field extensions — check which descent statements exist in mathlib (`AlgebraicGeometry.Morphisms.*` mostly have the base-change direction; the descent direction along `Spec K ⟶ Spec k₀`, a faithfully flat map, may need dedicated arguments).
4. **(B3d)** For a pair model: `f` is finite iff `f₀` is; in char 0, `Branch f` is the preimage of `Branch f₀` under `ℙ¹_K → ℙ¹_{{k₀}}`. In particular `f` is a Belyi map iff `f₀` is (with `{{0,1,∞}}` matched up by the canonical identification).

### Deliverables

`Belyi/Definable.lean` (+ a file for the descent lemmas of B3c if they grow). Keep the definition eliminator-friendly: both Belyi directions produce/consume explicit models.

References: [Koeck2004] §1–2 for the intended usage pattern; Stacks 04X? (descent of properties along field extensions).""",
)

issue(
    "Polynomial reduction I: moving algebraic branch points to ℚ (Belyi's descending induction)",
    [],
    f"""Statement **B6** in {OUTLINE}. Pure commutative algebra / field theory over ℚ — **no scheme theory**; this issue can proceed independently of the geometric foundations.

### Setting

Work inside a fixed algebraic closure `ℚ̄` (e.g. `AlgebraicClosure ℚ`, or the subfield of algebraic numbers of `ℂ`; coordinate the choice with the descent issue, which fixes `ℚ̄ ⊆ ℂ`). For a non-constant `g ∈ ℚ[X]` define its **critical value set**

`CritVal g := {{ g(a) | a ∈ ℚ̄, g'(a) = 0 }} ⊆ ℚ̄`

(mathlib: `Polynomial.derivative`, `Polynomial.aeval`, root sets). The point `∞` needs no tracking: polynomials fix `∞` and `∞` is always allowed as a branch point.

### Statement to prove

For every finite `S ⊆ ℚ̄` there is a non-constant `g ∈ ℚ[X]` with
`g '' S ∪ CritVal g ⊆ (algebraMap ℚ ℚ̄) '' Set.univ` (i.e. every element is rational).

### Suggested proof (Belyi's induction, [Szamuely2009] proof of Thm 4.7.6, step 1)

WLOG `S` is stable under `Gal(ℚ̄/ℚ)`-conjugation (enlarge `S` by all conjugates: finitely many, via `minpoly`). Induct on the lexicographic measure `(d, n)` where `d` is the maximal degree `[ℚ(s) : ℚ]` of elements of `S` and `n` the number of elements of degree `d`:

* pick `s ∈ S` of degree `d > 1`, let `m := minpoly ℚ s`;
* `m` kills `s` and all its conjugates in `S` (they map to `0`);
* for any other `s' ∈ S`, `m(s') ∈ ℚ(s')`, so its degree does not go up;
* every critical value `m(a)` (with `m'(a) = 0`) lies in `ℚ(a)` with `[ℚ(a):ℚ] ≤ deg m' = d - 1 < d`;
* hence `S' := m '' S ∪ CritVal m` (re-closed under conjugation — check `CritVal m` is already conjugation-stable since `m ∈ ℚ[X]`) has strictly smaller measure; recurse and compose: the composition lemma `CritVal (g ∘ h) ⊆ g '' (CritVal h) ∪ CritVal g` (chain rule, `Polynomial.comp`) is the bookkeeping engine and should be proved first.

### Deliverables

`Belyi/Polynomial/CritVal.lean` (definition + composition lemma + conjugation stability) and `Belyi/Polynomial/ReductionRational.lean` (the induction). State the final result both as above and in a form directly consumable by the forward-direction issue.""",
)

issue(
    "Polynomial reduction II: moving rational branch points into {0, 1, ∞}",
    [],
    f"""Statement **B7** in {OUTLINE}. Like reduction I, this is elementary algebra, independent of the scheme-theoretic foundations, but it needs rational *functions* (Möbius maps), not just polynomials.

### Setting

Work with non-constant `h ∈ RatFunc ℚ` acting on `OnePoint ℚ̄ = ℚ̄ ∪ {{∞}}` (mathlib has `RatFunc` and `OnePoint`; an evaluation of a rational function on `OnePoint` of the algebraic closure, with the usual conventions at poles and `∞`, is a small self-contained API to build — keep it in its own file, the forward-direction bridge will reuse it). Extend the critical-value calculus of reduction I to this setting:

`CritVal∞ h ⊆ OnePoint ℚ̄` — critical values of `h` including the contribution at `∞` and at poles (for a polynomial `g`, `CritVal∞ g = CritVal g ∪ {{∞}}`; for a Möbius map, `CritVal∞ = ∅`). Prove the composition lemma `CritVal∞ (g ∘ h) ⊆ g '' (CritVal∞ h) ∪ CritVal∞ g`.

### Statement to prove

For every finite `S ⊆ ℚ ∪ {{∞}} ⊆ OnePoint ℚ̄` there is a non-constant `h ∈ RatFunc ℚ` with
`h '' S ∪ CritVal∞ h ⊆ {{0, 1, ∞}}`.

### Suggested proof ([GirondoGonzalezDiez2012] proof of Thm 3.1; [Szamuely2009] step 2)

Induct on `|S ∖ {{0, 1, ∞}}|`:

* if it is 0, take `h = X` — done;
* otherwise pick a Möbius map `μ ∈ PGL₂(ℚ)` (an explicit ratio of linear polynomials suffices; no group theory needed) sending three points of `S ∪ {{0,1,∞}}` so that afterwards `0, 1, ∞ ∈ μ '' S ∪ {{0,1,∞}}` and some `s ∈ μ '' S` satisfies `0 < s < 1`, `s = m/(m+n)` with `m, n ≥ 1` natural numbers;
* compose with `λ_{{m,n}} := ((m+n)^(m+n) / (m^m n^n)) · X^m (1-X)^n`. Verify by direct computation: `λ_{{m,n}}` maps `0 ↦ 0`, `1 ↦ 0`, `∞ ↦ ∞`, `m/(m+n) ↦ 1`, and `CritVal∞ λ_{{m,n}} ⊆ {{0, 1, ∞}}` (its derivative is `C·X^(m-1)(1-X)^(n-1)(m-(m+n)X)`);
* the composite strictly decreases the count; recurse using the composition lemma.

Both this issue and reduction I should agree on the `CritVal` interfaces; whichever lands second adapts.

### Deliverables

`Belyi/Polynomial/OnePointEval.lean`, `Belyi/Polynomial/Lambda.lean` (the `λ_{{m,n}}` computations), `Belyi/Polynomial/ReductionZeroOneInfty.lean`.""",
)

issue(
    "Forward direction: curves definable over ℚ̄ admit Belyi maps",
    [1, 2, 3, 4, 5],
    f"""Statements **B4**, **B5**, **B8** in {OUTLINE}: assemble the forward direction of Belyi's theorem from the foundations and the two polynomial reductions.

### The bridge (B4)

The polynomial issues speak about `CritVal`-sets of rational functions over ℚ; the geometric issues speak about branch loci of finite morphisms. Prove the dictionary, for an algebraically closed field `k` of char 0:

* a non-constant `h ∈ RatFunc k` induces a finite morphism `ℙ¹_k ⟶ ℙ¹_k` (via the `ℙ¹` API and the finite-morphism criterion from the curve foundations issue);
* under the identification of closed points of `ℙ¹_k` with `OnePoint k`, `Branch h = CritVal∞ h` — in particular for a polynomial `g`, `Branch g = CritVal g ∪ {{∞}}`.

This is where the two `CritVal` files meet the scheme theory; expect the main work to be in relating scheme-theoretic étaleness at a closed point to non-vanishing of the derivative (standard: étale iff unramified iff the local different is trivial iff `h'(a) ≠ 0` for finite points).

### Composition bookkeeping (B5)

Specialize the branch-locus composition lemma (B2a) to towers `X ⟶ ℙ¹ ⟶ ℙ¹` and match it against the `CritVal` composition lemmas.

### Main theorem (B8)

If `X` is a curve over `ℂ` definable over `ℚ̄` (in the sense of the definability issue), then `X` admits a Belyi map `f : X ⟶ ℙ¹_ℂ`; moreover the pair `(X, f)` can be taken definable over `ℚ̄`.

Proof from the pieces: choose a model `X₀/ℚ̄`; choose a finite `f₀ : X₀ ⟶ ℙ¹_ℚ̄`; `Branch f₀` is finite and consists of `ℚ̄`-points, giving (through the `OnePoint` dictionary and a chosen embedding of the branch set into `ℚ̄`) a finite `S ⊆ ℚ̄ ∪ {{∞}}`; apply reduction I then reduction II over ℚ, base-change the resulting `h` to `ℚ̄`, compose, and transport along B3d back to `ℂ`.

Record the "moreover" (pair definability): it is what the marked-curve issue and later cuspidalization work actually consume.

### Deliverables

`Belyi/Bridge.lean` (B4/B5) and `Belyi/Forward.lean` (B8).""",
)

issue(
    "Finiteness of covers of ℙ¹ étale outside {0, 1, ∞} (rigidity input)",
    [1, 2],
    f"""Statement **B9** in {OUTLINE}: the deep external input to the converse direction. This issue is expected to become a sub-project; its first deliverable is a *decision*, its second a *statement in Lean*, and only then proofs.

### Statement

Let `k` be an algebraically closed field of characteristic 0 and `d ≥ 1`. Up to isomorphism over `ℙ¹_k`, there are only finitely many pairs `(X, f)` with `X` a curve over `k` and `f : X ⟶ ℙ¹_k` finite of degree `≤ d`, étale outside `{{0, 1, ∞}}`.

(Equivalent formulation, likely better for Lean: the category of finite étale covers of `ℙ¹_k ∖ {{0,1,∞}}` of degree `≤ d` has finitely many isomorphism classes; then attach the smooth compactification — normalization of `ℙ¹` in the function field of the cover — to recover the pair version. The compactification step is itself nontrivial and should be split out if pursued.)

### Classical proofs and what they need

1. **Riemann existence route** (over `ℂ`): finite covers of the thrice-punctured line correspond to finite-index subgroup data of `π₁^top = F₂`; a finitely generated group has finitely many subgroups of bounded index. Needs: comparison between finite étale covers and topological covers (Riemann existence — very far from mathlib: analytification, GAGA), though the group-theoretic half (mathlib: `FreeGroup`, covering-space theory in `Mathlib.Topology.Covering`, finiteness of bounded-index subgroups — check; a Marshall-Hall-style counting argument is elementary) is feasible today.
2. **Étale fundamental group route**: `π₁^ét(ℙ¹_k ∖ {{0,1,∞}})` is topologically finitely generated. Mathlib has the Galois-categories framework (`Mathlib/CategoryTheory/Galois/`) and finite étale morphisms; the finite generation itself is SGA 1 XIII and again rests on Riemann existence in char 0 — but the *reduction* of B9 to a clean statement about the fundamental group functor may be the right formalization boundary.
3. **Invariance under change of algebraically closed base field** (needed to transfer from `ℂ` to `ℚ̄(V)‾` in the descent issue, or vice versa): the category of finite étale covers of `ℙ¹ ∖ {{0,1,∞}}` is invariant under extension of algebraically closed fields of char 0 (SGA 1 XIII 4.6 / [Szamuely2009] Cor. 4.8.11 area). Decide whether this is proved or whether the descent issue is restructured to avoid it.

### First deliverable

A design document (`references/rigidity-design.md` in the repo or a comment on this issue) fixing: the exact Lean statement of B9, which route is taken, what is axiomatized as `sorry`-free assumptions vs. proved, and a split into further child issues. Coordinate with the maintainers before large-scale work.

References: [Szamuely2009] §4.6 & §4.8; [Guillot2014] §1–4; SGA 1, Exp. XIII.""",
)

issue(
    "Converse direction: curves with a Belyi map descend to ℚ̄",
    [2, 3, 7],
    f"""Statements **B10–B12** in {OUTLINE}: the "obvious" direction of Belyi's theorem, following the algebraic proof of [Koeck2004] (local copy: `references/sources/koeck-belyi-revisited.pdf`; alternative exposition [Szamuely2009] §4.8).

### Statement (B12)

If a curve `X` over `ℂ` admits a Belyi map `f : X ⟶ ℙ¹_ℂ`, then `X` is definable over `ℚ̄`; moreover the pair `(X, f)` is definable over `ℚ̄`.

### Decomposition

**(B10) Spreading out.** `(X, f)` is of finite presentation, so it is definable over a subfield `L ⊆ ℂ` finitely generated over `ℚ̄`; write `L` as the function field of a smooth affine ℚ̄-variety `V`. Spread `(X_L, f_L)` out to a family `(𝒳 ⟶ ℙ¹_U ⟶ U)` over a dense open `U ⊆ V` such that every closed fiber is a curve with a finite map to `ℙ¹_ℚ̄` étale outside `{{0,1,∞}}` and the generic fiber recovers `(X_L, f_L)`. This is standard EGA IV limit formalism and is mostly **not in mathlib**; scope it carefully — only the statements needed here (finite presentation of the pair, openness of the loci where fibers are smooth/proper/geom. connected/finite/étale-outside-{{0,1,∞}}) should be proved, in the special situation at hand (base `V` smooth affine over `ℚ̄`, relative dimension 1). If this grows too large, split it into its own child issues and coordinate with maintainers — some of it belongs in mathlib.

**(B11) Rigidity/isotriviality.** Using the finiteness input (rigidity issue) over the algebraic closure of `L`: among the finitely many isomorphism classes of degree-`≤ d` covers of `ℙ¹` étale outside `{{0,1,∞}}`, the fibers of the family must be constant on a dense open (a countable-vs-uncountable or constructibility argument; [Koeck2004] Thm 2.2 makes this precise via the isomorphism scheme `Isom_U(𝒳, 𝒳')` being of finite type over `U` — its image is constructible, and if it dominates it contains a dense open with a point over ℚ̄... follow Köck's argument, don't improvise). Conclude: there is a closed point `u ∈ U(ℚ̄)` with `(𝒳_u, f_u) ×_ℚ̄ ℂ ≅ (X, f)`.

**(B12) Assembly** into the definability predicate (pair version), yielding also that Belyi maps themselves are "rigid" objects defined over `ℚ̄`.

### Deliverables

`Belyi/SpreadOut.lean`, `Belyi/Descent.lean`. This issue may be re-split after B10 is scoped; treat the current split as provisional and record design decisions as comments on this issue.""",
)

issue(
    "Marked curves: prescribed points inside the fiber over {0, 1, ∞}",
    [6],
    f"""Statement **B13** in {OUTLINE}: the strengthening of the forward direction used by later Belyi-cuspidalization work (see the parent issue's "Use in IUT" section).

### Statement

Let `X₀` be a curve over `ℚ̄`, `S₀` a finite set of closed points of `X₀`, and `X := X₀ ×_ℚ̄ ℂ` with `S ⊆ X` the preimage of `S₀` (a finite set of closed points). Then there exists a Belyi map `f : X ⟶ ℙ¹_ℂ` such that:

* `S ⊆ f⁻¹({{0, 1, ∞}})` (as closed points), and
* the pair `(X, f)` is definable over `ℚ̄` with a model `(X₀, f₀)` satisfying `S₀ ⊆ f₀⁻¹({{0, 1, ∞}})`.

### Suggested proof

Rerun the forward-direction assembly with the marked set folded into the branch data: choose a finite `f₀ : X₀ ⟶ ℙ¹_ℚ̄` (curve foundations); the set `T := f₀ '' S₀ ∪ Branch f₀` is a finite set of `ℚ̄`-points of `ℙ¹`; apply polynomial reduction I + II to `T` (not just to `Branch f₀`), obtaining `g` over ℚ with `g '' T ∪ CritVal∞ g ⊆ {{0,1,∞}}`; then `g ∘ f₀` is a Belyi map with `f₀ '' S₀` mapped into `{{0,1,∞}}`, i.e. `S₀ ⊆ (g ∘ f₀)⁻¹({{0,1,∞}})`; base change to `ℂ`.

The only new ingredients over the forward issue are bookkeeping lemmas: behaviour of fibers/preimages under composition and base change of the marked set. Design the statement so that a consumer holding `(X₀, S₀)` gets the Belyi pair *and* the containment in a single package (a structure `MarkedBelyiPair` may be worthwhile).

### Deliverables

`Belyi/Marked.lean`. Confirm with the maintainers (comment on this issue) that the packaging matches what the Belyi-cuspidalization consumers (successors of taxis issue #8) expect **before** finalizing the API.""",
)

issue(
    "Main theorem: assemble Belyi's theorem and finalize the API",
    [6, 8, 9],
    f"""Statement **B14** in {OUTLINE}: the top-level deliverable of the parent issue.

### Statements

In `Belyi/Main.lean`, prove and name:

1. `belyi_tfae` / `belyi_iff` — for a curve `X` over `ℂ`: `DefinableOver ℚ̄ X ↔ ∃ f, IsBelyiMap f` (both directions imported from the forward and converse issues; fix here, once, the global conventions: the model of `ℙ̄¹`, the copy of `ℚ̄` inside `ℂ`, the `{{0,1,∞}}` subset).
2. **(B14a)** Invariance of both sides under isomorphism of curves over `ℂ`, stated as explicit congruence lemmas.
3. Invariance under base change along automorphisms/isomorphisms in the relevant setting, packaged the way the parent issue requests ("invariance under base change/isomorphism").
4. **(B14c)** Re-export of the marked form (marked-curve issue) next to the main theorem, so downstream Belyi-cuspidalization work has a single import target (`import Belyi` or `import Belyi.Main`).

### API polish (definition of done for the whole project)

* `Belyi.lean` root module imports everything; `lake build` green in CI; doc-gen builds.
* Every public definition/theorem has a docstring; module docstrings explain the mathematical content and cite `references/proof-outline.md` labels.
* No `sorry`s, no `axiom`s beyond what the rigidity issue's design document explicitly sanctioned (if any remain, they must be isolated in one clearly named file and reflected in the final report on this issue).
* A closing comment on the parent issue #{PARENT} summarizing what was proved, in which generality, and any deviations from the outline.""",
)


def req(method, path, payload=None):
    data = json.dumps(payload).encode() if payload is not None else None
    r = urllib.request.Request(BASE + path, data=data, method=method)
    r.add_header("Content-Type", "application/json")
    if TOKEN:
        r.add_header("Authorization", "Bearer " + TOKEN)
    with urllib.request.urlopen(r) as resp:
        return json.loads(resp.read())


def emit_markdown():
    print("# Child issues of taxis issue #18 (Belyi's theorem)")
    print()
    print("Generated by `scripts/create_child_issues.py --emit-markdown`; edit the")
    print("script, not this file. Task numbers below are local; dependencies refer")
    print("to these local numbers and are translated to taxis issue ids on filing.")
    for n, it in enumerate(issues, start=1):
        print(f"\n---\n\n## Task {n}: {it['title']}\n")
        if it["deps"]:
            print(f"*Depends on task(s): {', '.join(str(d) for d in it['deps'])}.*\n")
        print(it["body"])


def main():
    if "--emit-markdown" in sys.argv:
        emit_markdown()
        return
    dry = "--dry-run" in sys.argv
    created = {}  # local index (1-based) -> real issue id
    for n, it in enumerate(issues, start=1):
        payload = {
            "title": it["title"],
            "description": it["body"],
            "parent": PARENT,
            "state": "open",
            "labels": [],
            "dependencies": sorted(created[d] for d in it["deps"] if d in created),
        }
        if dry:
            print(f"--- [{n}] {it['title']}\n    deps(local): {it['deps']}\n    body: {len(it['body'])} chars")
            created[n] = 100 + n
            continue
        out = req("POST", "/issues", payload)
        iid = out.get("id") or out.get("issue", {}).get("id")
        created[n] = iid
        print(f"created #{iid}: {it['title']}")
    print(json.dumps(created, indent=1))


if __name__ == "__main__":
    main()
