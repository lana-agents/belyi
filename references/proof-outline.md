# Proof outline and statement labels

This file fixes the mathematical roadmap for the formalization and assigns a label
to every statement that a child issue formalizes. Issues on the taxis tracker refer
to these labels. Citations refer to [`README.md`](README.md).

Throughout, *curve over `k`* means: a scheme `X` with a morphism `X → Spec k` that
is smooth, projective (equivalently proper, in dimension 1), geometrically
connected — hence geometrically integral — and of pure dimension 1. `ℙ¹_k` denotes
the projective line over `k`, and we identify closed points of `ℙ¹_k` with elements
of `k ∪ {∞}` when `k` is algebraically closed. `ℚ̄` denotes the algebraic closure of
`ℚ` inside `ℂ`.

## Main theorem

**(B14, Belyi)** Let `X` be a curve over `ℂ`. Equivalent are:

1. `X` is definable over `ℚ̄` (see B3);
2. there is a finite morphism `f : X → ℙ¹_ℂ` whose branch locus is contained in
   `{0, 1, ∞}`.

A morphism as in (2) is called a *Belyi map*.

**(B13, marked form)** Moreover, if `X` is definable over `ℚ̄` with model `X₀/ℚ̄` and
`S` is a finite set of closed points of `X` whose image in `X₀` consists of closed
points (automatic: all points of `X` above closed points of `X₀` with residue field
`ℚ̄`… take `S` any finite set of closed points of `X₀` base-changed to `ℂ`), then a
Belyi map `f` can be chosen with `S ⊆ f⁻¹({0, 1, ∞})`.

## Part 0: foundations

**(B1) Curves and maps to the line.**
API for curves over a field `k` as above. Key output: for every curve `X/k` and
every non-constant `t` in the function field `k(X)`, the induced morphism
`X → ℙ¹_k` is finite (and flat). In particular every curve admits a finite morphism
to `ℙ¹_k`. [Szamuely2009, §4.1; standard.]

**(B2) Ramification and branch locus.**
For a finite separable morphism `f : X → Y` of curves over `k`: the étale locus is
open and dense, its complement in `X` (the ramification locus) is finite, and the
*branch locus* `Branch f ⊆ Y` (the image of the ramification locus) is a finite set
of closed points. Functoriality:
* (B2a) `Branch (g ∘ f) ⊆ Branch g ∪ g(Branch f)`;
* (B2b) formation of the branch locus commutes with base change along field
  extensions (in characteristic 0);
* (B2c) `f` is étale over `Y ∖ Branch f`.
In characteristic 0 every finite morphism of curves is separable, which is the only
case we need. [Szamuely2009, §4.4–4.5.]

**(B3) Definability over a subfield.**
For a field extension `k₀ ⊆ K` and a scheme `X` of finite type over `K`:
`X` is *definable over* `k₀` if there is a scheme `X₀` of finite type over `k₀`
(a *model*) and an isomorphism `X₀ ×_{k₀} K ≅ X` over `K`. Variant for pairs:
`(X, f : X → ℙ¹_K)` is definable over `k₀` if there is `f₀ : X₀ → ℙ¹_{k₀}` whose
base change is isomorphic to `f` over `ℙ¹_K`. Basic API:
* (B3a) invariance under `K`-isomorphism;
* (B3b) transitivity in `k₀ ⊆ k₁ ⊆ K`;
* (B3c) stability of curve properties (smooth, proper, geometrically connected,
  dimension 1) under base change and descent along field extensions, so a model of
  a curve is a curve;
* (B3d) finiteness and branch loci match up: if `(X, f)` has model `(X₀, f₀)` then
  `f` finite ⇔ `f₀` finite, and `Branch f` is the preimage of `Branch f₀` under
  `ℙ¹_K → ℙ¹_{k₀}` (char. 0).

## Part 1: forward direction (ℚ̄-model ⇒ Belyi map)

The two combinatorial reduction steps are statements about polynomials over ℚ and
can be formalized independently of any scheme theory, via the branch locus of the
self-map of `ℙ¹` defined by a polynomial: for a non-constant `g ∈ k[x]`, viewed as a
finite morphism `ℙ¹_k → ℙ¹_k`, the branch locus is `g({critical points of g}) ∪ {∞}`
(B4).

**(B4) Branch locus of a polynomial map.**
For non-constant `g ∈ k[x]` (char. 0), the morphism `ℙ¹_k → ℙ¹_k` it defines is
finite of degree `deg g`, `∞ ↦ ∞`, and its branch locus is
`{g(a) : g'(a) = 0} ∪ {∞}` (as a subset of `k̄ ∪ {∞}`).

**(B5) Composition bookkeeping.**
For finite maps `X --f--> ℙ¹ --g--> ℙ¹` (char. 0):
`Branch (g ∘ f) ⊆ g(Branch f) ∪ Branch g`. (Specialization of B2a.)

**(B6) Reduction of algebraic branch points to rational ones.**
For every finite set `S ⊂ ℚ̄ ∪ {∞}` there is a non-constant `g ∈ ℚ[x]` with
`g(S) ∪ Branch g ⊆ ℚ ∪ {∞}`.
*Proof sketch (Belyi's descending induction):* let `m(x) ∈ ℚ[x]` be the product of
the minimal polynomials of the finite non-rational points of `S`. Then
`m(S) ⊆ {0} ∪ {∞}`… more precisely `g₁ = m` maps `S` into `ℚ ∪ {∞}` *up to* the new
branch points `m(crit m)`, whose degrees over `ℚ` are strictly smaller than
`max_{s ∈ S} [ℚ(s) : ℚ]` (since `deg m' < deg m` and critical values generate
subfields of bounded degree). Iterate on `m(S) ∪ Branch m` and compose; the
induction terminates because the maximal degree of the branch points strictly
decreases. [Belyi1979, §2; GirondoGonzalezDiez2012, Lemma 3.4; Szamuely2009,
proof of Thm 4.7.6, step 1.]

**(B7) Reduction of rational branch points to `{0, 1, ∞}`.**
For every finite set `S ⊂ ℚ ∪ {∞}` there is a non-constant `h ∈ ℚ[x]`, a
composition of Möbius maps defined over `ℚ` and of the maps
`λ_{m,n}(x) = ((m+n)^{m+n} / (m^m n^n)) · x^m (1-x)^n` (`m, n ≥ 1`), with
`h(S) ∪ Branch h ⊆ {0, 1, ∞}`.
*Proof sketch:* `λ_{m,n}` has critical points `{0, 1, m/(m+n), ∞}` and maps
`{0, 1, m/(m+n), ∞}` into `{0, 1, ∞}`; hence, after a Möbius normalization sending
three points of `S` to `0, m/(m+n), 1`, composing with `λ_{m,n}` decreases
`|S ∖ {0, 1, ∞}|`. Induct. [GirondoGonzalezDiez2012, proof of Thm 3.1;
Szamuely2009, step 2.]

**(B8) Forward direction.**
If `X/ℂ` is definable over `ℚ̄`, then `X` admits a Belyi map.
*Proof sketch:* pick a model `X₀/ℚ̄` and a finite `f₀ : X₀ → ℙ¹_ℚ̄` (B1). Its branch
locus is a finite set of ℚ̄-points (B2). Apply B6 then B7 to get `g` with
`Branch (g ∘ f₀) ⊆ {0, 1, ∞}` (B4, B5). Base change to ℂ (B3d, B2b).

## Part 2: converse direction (Belyi map ⇒ ℚ̄-model)

Reference route: the algebraic proof of [Koeck2004] (also [Szamuely2009, §4.8]).
The moduli-theoretic route of [GonzalezDiez2006] is an acceptable alternative.

**(B9) Rigidity input: finiteness of covers.**
Fix `d ≥ 1` and an algebraically closed field `k` of characteristic 0. Up to
isomorphism over `ℙ¹_k`, there are only finitely many finite morphisms
`f : X → ℙ¹_k` of degree `≤ d` from a curve `X/k`, étale outside `{0, 1, ∞}`.
Over `ℂ` this follows from the Riemann existence theorem: such covers correspond to
index-`≤ d` subgroup data for the (topologically finitely generated) fundamental
group of the three-punctured sphere; a free group of rank 2 has finitely many
subgroups of bounded index. The transfer to arbitrary `k` (in particular `ℚ̄ ⊆ ℂ`)
is by invariance of the category of covers under extension of algebraically closed
fields of char. 0. *This is the deepest external input; how much of Riemann
existence to formalize vs. axiomatize must be decided in the corresponding issue.*
[Szamuely2009, §4.6; Guillot2014, §1–4.]

**(B10) Spreading out and specialization.**
Let `(X, f)` be a Belyi pair over `ℂ`. Then `(X, f)` is definable over a subfield
`L ⊆ ℂ` finitely generated over `ℚ̄`; writing `L = ℚ̄(V)` for a ℚ̄-variety `V`, the
pair spreads out to a family over a dense open `U ⊆ V`, all of whose closed fibers
are Belyi pairs over `ℚ̄`, and such that the generic fiber base-changed to `ℂ`
recovers `(X, f)`. [Koeck2004, §2; standard spreading-out.]

**(B11) Descent through the family.**
In the situation of B10, using B9: two suitable fibers (a ℚ̄-fiber and the geometric
generic fiber) are isomorphic as covers of `ℙ¹`, hence `X` is definable over `ℚ̄`.
[Koeck2004] makes this precise via a rigidity argument: since (by B9, over the
algebraically closed field `ℚ̄(V)‾`) there are only finitely many covers of bounded
degree étale outside `{0, 1, ∞}`, the family is "isotrivial" over a dense open, and
a ℚ̄-point of `U` gives a ℚ̄-model of `X`.

**(B12) Converse direction.**
A curve over `ℂ` admitting a Belyi map is definable over `ℚ̄`. (Assemble B10 + B11;
record also the pair version: the Belyi map itself descends.)

## Part 3: marked curves and final assembly

**(B13) Marked-curve strengthening.**
Let `X₀/ℚ̄` be a curve, `S₀` a finite set of closed points of `X₀`, and
`X = X₀ ×_ℚ̄ ℂ`, `S ⊆ X` the (finite) preimage of `S₀`. Then there is a Belyi map
`f : X → ℙ¹_ℂ`, definable over `ℚ̄`, with `S ⊆ f⁻¹({0, 1, ∞})`.
*Proof sketch:* choose finite `f₀ : X₀ → ℙ¹_ℚ̄` (B1); apply B6 + B7 to the finite
set `f₀(S₀) ∪ Branch f₀ ⊂ ℚ̄ ∪ {∞}`; the resulting composite `g ∘ f₀` is a Belyi map
sending `S₀` into `{0, 1, ∞}`, so `S ⊆ (g ∘ f₀)⁻¹({0, 1, ∞})` after base change.

**(B14) Main theorem and API.**
The equivalence stated at the top, obtained from B8 and B12, together with:
* (B14a) invariance of both sides under `ℂ`-isomorphism;
* (B14b) invariance of "definable over ℚ̄" under choice of embedding `ℚ̄ ↪ ℂ` is
  *not* required — `ℚ̄` is fixed inside `ℂ` throughout;
* (B14c) the marked form B13 packaged so that later Belyi-cuspidalization work
  (taxis issue #8 and its successors) can consume it.

## Dependency graph

```
B1  B2  B3          B4  B5 (polynomial algebra, independent)
 \  |  /             |  /
  \ | /              | /
   B8  <──── B6 ── B7
   |
   |    B9 ──> B11 <── B10
   |            |
   |           B12
    \          /
     B13     /
       \    /
        B14
```

(B6/B7 are pure algebra and can proceed in parallel with B1–B3; B9 is the deepest
prerequisite and should be started early.)
