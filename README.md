# Belyi's theorem in Lean 4

A formalization of **Belyi's theorem** in Lean 4 building on
[mathlib](https://github.com/leanprover-community/mathlib4):

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

Everything below is sorry-free. Statement labels (B1, B2a, …) refer to
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
