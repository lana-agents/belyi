# Belyi's theorem in Lean 4

A complete, sorry- and axiom-free formalization of **Belyi's theorem** in Lean 4 building on
[mathlib](https://github.com/leanprover-community/mathlib4) and on the Riemann existence theorem
of [oka](https://github.com/lana-agents/oka)
(with [pi1](https://github.com/lana-agents/pi1), étale fundamental groups, as a further dependency):

> A smooth projective geometrically connected curve over `ℂ` is definable over `ℚ̄`
> if and only if it admits a finite morphism to `ℙ¹` whose branch locus is contained
> in `{0, 1, ∞}`.

The project covers both directions of the theorem, invariance under base change and
isomorphism, and a marked-curve form in which a prescribed finite set of closed
points is enlarged into the inverse image of `{0, 1, ∞}`.

Project coordination happens on the
[taxis issue tracker](https://taxis.lana.merten.dev/#/issues/18); the project is
divided into child issues of issue #18. The mathematical background, an annotated
bibliography and a detailed proof outline (with statement labels referenced by the
issues) live in [`references/`](references/).

## Building

The project uses the Lean toolchain pinned in [`lean-toolchain`](lean-toolchain) and
the matching mathlib release. With [elan](https://github.com/leanprover/elan)
installed:

```sh
lake exe cache get   # fetch prebuilt mathlib oleans
lake build
```

## Structure

* `Belyi/` — the Lean library (root module: `Belyi.lean`).
* `references/` — bibliography, proof outline and locally prepared source material.
* `.github/workflows/` — CI: build on every push/PR (`lean_action_ci.yml`), toolchain
  release tagging (`create-release.yml`) and manually triggered mathlib bumps
  (`update.yml`).

## Contents

Everything below is sorry-free and axiom-free. Statement labels (B1, B2a, …) refer to
[`references/proof-outline.md`](references/proof-outline.md).

**Curves and the projective line**

* `Belyi/Curve/Basic.lean` — the curve predicate `IsCurveOver`.
* `Belyi/P1.lean` — `P1 k = Proj k[X₀,X₁]`, its structure morphism, properness.
* `Belyi/P1/Points.lean` — the marked points `0`, `1`, `∞` as homogeneous primes,
  pairwise distinct.
* `Belyi/P1/AffineChart.lean` — `R`-valued points with a given affine coordinate.
* `Belyi/P1/Transcendental.lean` — points at transcendental elements are not closed.
* `Belyi/P1/BaseChange.lean` — the comparison morphism `ℙ¹_K ⟶ ℙ¹_{k₀} ×_{k₀} K`.

**Maps to `ℙ¹` (B1)**

* `Belyi/RationalMap.lean` — rational maps into proper schemes extend over
  valuation-ring stalks (a mathlib-PR candidate).
* `Belyi/FunctionField.lean`, `Belyi/Curve/ToP1.lean` — the morphism `X ⟶ ℙ¹`
  attached to a rational function.
* `Belyi/Dimension.lean` — finiteness of fibers over one-dimensional stalks.
* `Belyi/Curve/B1.lean` — **B1**: that morphism is finite for transcendental `t`.
* `Belyi/Curve/Stalks.lean` — reduction of the remaining hypothesis to a cotangent
  bound.

**Ramification (B2) and Belyi maps**

* `Belyi/Ramification.lean` — `Ram`/`Branch`, B2a, B2c, finiteness.
* `Belyi/BelyiMap.lean` — `IsBelyiMap` and the composition step B5.

**Reductions (B6, B7) and definability (B3)**

* `Belyi/Polynomial/` — the two polynomial reduction theorems, complete.
* `Belyi/Definable.lean`, `Belyi/Curve/BaseChange.lean` — `DefinableOver`, B3a, B3b
  and the base-change half of B3c.

**Converse via Riemann existence** (plan: [`references/converse-rie-design.md`](references/converse-rie-design.md))

* `Belyi/Converse/Basic.lean` — the base-change interface `IsBaseChangeAlong`.
* `Belyi/Converse/PuncturedLine.lean` — (P1) `ℙ¹ ∖ {0, 1, ∞} = Spec k[t][(t(t-1))⁻¹]` and its
  base change, compatibly with `ℙ¹_K ≅ ℙ¹_k ×_k K`.
* `Belyi/Converse/PuncturedLineBelyi.lean` — (P1) a Belyi map is finite étale over the
  punctured line: `f⁻¹(ℙ¹ ∖ {0, 1, ∞}) = Spec B` with `B` finite étale, dense in `X`.
* `Belyi/Converse/BaseChange.lean`, `Belyi/Converse/ConstantFamily.lean` — base-change API.
* `Belyi/Converse/Spread.lean` — (S1) spreading a finite étale algebra out over a smooth
  finitely generated `k`-subalgebra of `K`.
* `Belyi/Converse/Points.lean` — (S4) `k`-points and injective embeddings into `ℂ`.
* `Belyi/Converse/HomDescent.lean`, `Belyi/Converse/IsoDescent.lean` — (S2) isomorphisms over
  `ℂ` descend to `K`.
* `Belyi/Converse/CoveringHomotopy.lean` — (S3b) covering maps over `Z × T` have homeomorphic
  fibres along paths in `T`.
* `Belyi/Converse/PathConnected.lean` — (S3a) analytifications of smooth connected
  `ℂ`-schemes are path connected.
* `Belyi/Converse/AnalyticProduct.lean`, `Belyi/Converse/Rigidity.lean`,
  `Belyi/Converse/RigidityC.lean` — (S3) finite étale families over a smooth connected base have
  isomorphic fibres at any two `ℂ`-points, by the Riemann existence theorem of `oka`.
* `Belyi/Converse/FEtDescent.lean` — (★) finite étale covers descend from `K` to `k`.
* `Belyi/Converse/Normalization.lean`, `Belyi/Converse/IntegralClosureBaseChange.lean`,
  `Belyi/Converse/NormalizationBaseChange.lean` — (P2) a curve is the normalization of `ℙ¹` in
  a dense open; normalization commutes with base change along field extensions.
* `Belyi/Converse/DefinableOfBelyi.lean`, `Belyi/Converse/Main.lean` — **B12**, the converse.

**Main theorem**

* `Belyi/Main.lean` — **B14** `Belyi.belyi_iff`: for a curve `X` over `K = ℂ` (any algebraically
  closed field of characteristic zero) and `k = ℚ̄`,
  `DefinableOver k K X ↔ ∃ f : X ⟶ P1 K, IsBelyiMap K f`.
  `#print axioms Belyi.belyi_iff` = `[propext, Classical.choice, Quot.sound]`.
