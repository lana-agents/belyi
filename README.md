# Belyi's theorem in Lean 4

A sorry- and axiom-free formalization of **Belyi's theorem** and of **noncritical Belyi maps**
in Lean 4, building on [mathlib](https://github.com/leanprover-community/mathlib4) and on the
Riemann existence theorem of [oka](https://github.com/lana-agents/oka). The library has two
independent halves.

1. **Belyi's theorem, scheme-theoretically** (`Belyi.belyi_iff`, `Belyi/Main.lean`):

   > A smooth projective geometrically connected curve over `ℂ` is definable over `ℚ̄`
   > if and only if it admits a finite morphism to `ℙ¹` whose branch locus is contained
   > in `{0, 1, ∞}`.

   Both directions are proved, together with invariance under base change and isomorphism,
   and a marked-curve form in which a prescribed finite set of closed points is sent into
   `{0, 1, ∞}` (`Belyi.exists_isBelyiMap_marked_of_isCurveOver`).

2. **Curves over number fields as function fields** (`Belyi.CurveField`, `Belyi/CurveField/`):
   places, divisors, Riemann's theorem, the canonical divisor and Riemann–Hurwitz, the Belyi
   relation, Kummer–Fermat coverings, and **Mochizuki's noncritical Belyi maps** (*Noncritical
   Belyi maps*, Math. J. Okayama Univ. 46 (2004), Theorem 2.5 with `S = ∅`):

   > For every finite set `T` of places of the function field `K` of a curve over a number
   > field there is a Belyi function `φ ∈ K` none of whose cusps `φ⁻¹{0, 1, ∞}` lies in `T`
   > (`Belyi.CurveField.exists_isBelyi_notMem_belyiCusps`).

   This half is the one used downstream (see *Use in the IUT/ABC programme* below). It does
   not import the scheme-theoretic half, and no bridge between `IsCurveField` and
   `IsCurveOver` is formalized.

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

Everything below is sorry-free and axiom-free (no `sorry` and no `axiom` in `Belyi/`). Statement labels (B1, B2a, …) refer to
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

**Noncritical Belyi maps on `ℙ¹`** (`Belyi/NoncriticalP1/`)

* `Belyi/NoncriticalP1/ElemMap.lean`, `Belyi/NoncriticalP1/Rational.lean`,
  `Belyi/NoncriticalP1/Reduction.lean` — elementary maps of `ℙ¹(ℚ̄)` (Möbius transformations and
  polynomials over `ℚ`), ramification of composites, Mochizuki's Lemmas 2.1–2.4.
* `Belyi/NoncriticalP1/Main.lean` — `Belyi.NoncriticalP1.exists_isNoncriticalBelyi`: for a finite
  Galois-stable `S ⊆ ℙ¹(ℚ̄)` and `τ ∈ ℙ¹(ℚ) ∖ S` there is a composite `H` of elementary maps with
  `H(S) ⊆ {0, 1, ∞}`, `H(τ) ∉ {0, 1, ∞}`, unramified over `ℙ¹ ∖ {0, 1, ∞}` (Theorem 2.5 for `ℙ¹`).

**Curves over number fields as function fields** (`Belyi/CurveDeriv/`, `Belyi/CurveField/`)

A curve over a number field is represented by its function field: `Belyi.CurveField.IsCurveField K`
says that `K` (of characteristic zero) is finite over `ℚ⟮t⟯` for some transcendental `t`.

* `Belyi/CurveDeriv/` — the derivation `d/dt` (`Belyi.CurveDeriv.derivAlong`) and its order at a
  place.
* `Belyi/CurveField/Basic.lean`, `Chart.lean`, `Place.lean`, `Residue.lean`, `ZerosPoles.lean`,
  `Point.lean`, `Degree.lean` — places, residue fields, `ord`, zeros and poles, `ℚ̄`-points
  (`Belyi.CurveField.QbarPoint`) and their fields of definition.
* `Belyi/CurveField/Extension.lean`, `Fundamental.lean` — restriction of places along finite
  extensions; the fundamental identity `∑_{Q|P} e(Q|P) deg Q = [L : K] deg P`
  (`Belyi.CurveField.Place.sum_ramificationIdx_mul_deg`).
* `Belyi/CurveField/Divisor.lean`, `RiemannRochSpace.lean`, `Riemann.lean` — divisors, principal
  divisors of degree 0, Riemann–Roch spaces, Riemann's inequality and theorem
  (`Belyi.CurveField.Divisor.riemann_inequality`, `Belyi.CurveField.Divisor.riemann_equality`, with
  a constant `riemannConst K` in place of `g - 1`), realisation of polar divisors
  (`Belyi.CurveField.Divisor.exists_polarDivisor_eq`).
* `Belyi/CurveField/Rational.lean`, `Tripod.lean`, `CoordRing.lean` — the rational function field,
  the tripod `ℙ¹ ∖ {0, 1, ∞}`, coordinate rings of affine curves.
* `Belyi/CurveField/RamIdx.lean`, `Canonical.lean`, `Hurwitz.lean` — ramification indices, the
  canonical divisor of a function, Riemann–Hurwitz
  (`Belyi.CurveField.Divisor.canonicalDiv_algebraMap`,
  `Belyi.CurveField.Divisor.deg_canonicalDiv_algebraMap`).
* `Belyi/CurveField/BelyiRelation.lean` — Belyi functions `Belyi.CurveField.IsBelyi`, their cusps
  `belyiCusps` and reduced cusp divisor `cuspDivisor`, and the Belyi relation
  `K_φ + E = div (φ (φ - 1)) + (φ)_∞` (`Belyi.CurveField.canonicalDiv_add_cuspDivisor`).
* `Belyi/CurveField/Noncritical*.lean` — **noncritical Belyi maps**
  (`Belyi.CurveField.Noncritical.exists_isBelyi_forall_notMem_cusps`, restated in terms of
  `IsBelyi`/`belyiCusps` as `Belyi.CurveField.exists_isBelyi_notMem_belyiCusps`). Only the case
  `S = ∅` of Mochizuki's Theorem 2.5 is formalized.
* `Belyi/CurveField/KummerStep.lean`, `Kummer.lean` — Kummer–Fermat coverings `u^N = φ`,
  `v^N = 1 - φ`: unramified off the cusps of `φ`
  (`Belyi.CurveField.Place.ramificationIdx_eq_one_of_not_isCuspOf`), ramification bounds over the
  cusps (`Belyi.CurveField.Place.le_ramificationIdx_mul_abs_ord`), residue fields generated by the
  Kummer coordinates (`Belyi.CurveField.Place.adjoin_residue_kummer_eq_top`).

`#print axioms` of `Belyi.CurveField.exists_isBelyi_notMem_belyiCusps`,
`Belyi.CurveField.canonicalDiv_add_cuspDivisor`, `Belyi.CurveField.Place.adjoin_residue_kummer_eq_top`
and `Belyi.NoncriticalP1.exists_isNoncriticalBelyi` = `[propext, Classical.choice, Quot.sound]`.

## Use in the IUT/ABC programme

[lana-agents/heights](https://github.com/lana-agents/heights) requires this repository (at
`9ce4d3f`) for `Belyi.CurveField`, and the lana-agents fork of
[genl](https://github.com/lana-agents/genl) obtains it through heights. There, `Genl.Curves`
builds the height theory of curves over number fields and the Belyi descent of the proof package
(`Genl/Curves/BelyiDescent.lean`, `Genl/Curves/Covering.lean`) from the noncritical Belyi maps,
the Belyi relation and the Kummer–Fermat coverings. [lana-agents/iut](https://github.com/lana-agents/iut)
pins `belyi` at `9ce4d3f` in its `lake-manifest.json` as a transitive dependency; it does not
use the library directly.

License: Apache 2.0 (see LICENSE)
