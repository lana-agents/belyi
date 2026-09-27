# Converse direction via Riemann existence: design

This document replaces the `SpreadOut`/`rigidity_finiteness`/`spreadOut_isotrivial_point`
skeleton (`references/converse-design.md`) with an actual proof of the converse
`DefinableOver k K X` for a curve `X / K` admitting a Belyi map, where `k` is algebraically
closed, of characteristic zero and algebraic over `ℚ`, and `K ⊇ k` is algebraically closed of
characteristic zero (not necessarily `ℂ`).

It uses the Riemann existence theorem of `lana-agents/oka`
(`ComplexAnalytic.riemannExistenceTheorem`, sorry-free), only through **full faithfulness** of
analytification on finite étale covers
(`ComplexAnalytic.fullyFaithfulAnalytificationSepFiniteEtaleOver`), and oka's comparison of finite
étale analytic maps with topological covering maps. It needs **neither** finiteness of the number
of Belyi covers of bounded degree (B9) **nor** isomorphism schemes / constructibility (B11).

## 0. Overview

```
 X curve / K, f : X ⟶ ℙ¹_K Belyi
   │  (P1) Y := f⁻¹(ℙ¹_K ∖ {0,1,∞}) = Spec B, B finite étale over K ⊗_k R,
   │        R := Γ(ℙ¹_k ∖ {0,1,∞}) = k[t, t⁻¹, (t-1)⁻¹]
   ▼
 (★) FEt descent: B ≅ K ⊗_k B₀ for a finite étale R-algebra B₀
   ▼
 (P2) X ≅ normalization of ℙ¹_K in Y ≅ (normalization of ℙ¹_k in Spec B₀) ×_k K
   ▼
 DefinableOver k K X
```

### The core theorem (★): finite étale covers descend along `k ⊆ K`

> Let `k` be algebraically closed of characteristic zero and algebraic over `ℚ`, `K ⊇ k`
> algebraically closed, `R` a finitely generated `k`-algebra and `B` a finite étale
> `K ⊗_k R`-algebra. Then there is a finite étale `R`-algebra `B₀` with
> `K ⊗_k B₀ ≅ B` as `K ⊗_k R`-algebras.

Proof:

* **(S1) Spreading out.** `K` is the filtered union of its finitely generated `k`-subalgebras.
  `B` is finitely presented over `K ⊗_k R`, so it descends to a finite étale
  `A ⊗_k R`-algebra `B_A` for some finitely generated `k`-subalgebra `A ⊆ K`, with
  `K ⊗_A B_A ≅ B`. By generic smoothness (`Scheme.Hom.dense_smoothLocus_of_perfectField`),
  after inverting one element we may assume `A` is smooth over `k`. `A` is a domain (it sits
  inside `K`).
* **(S4) Two points of `Spec A`.** (a) A `k`-algebra map `s : A → k` exists (Nullstellensatz,
  `k` algebraically closed). (b) Fix `k → ℂ` (`k` is algebraic over `ℚ`, `IsAlgClosed.lift`).
  An **injective** `k`-algebra map `ι : A → ℂ` exists: `Frac A` is finitely generated over the
  countable field `k` and `ℂ` has infinite (continuum) transcendence degree over `k`.
* **(S3) Topological rigidity over `ℂ`.** Let `Ω := ULift ℂ`. Then
  `Ω ⊗_{A,ι} B_A ≅ Ω ⊗_{A,s} B_A` as `Ω ⊗_k R`-algebras. Proof:
  - `T := Spec (Ω ⊗_k A)` is smooth over `ℂ` and connected (`Ω ⊗_k A` is a domain since `k` is
    algebraically closed), so `T^an` is connected (oka `connectedSpace_analytification`) and
    locally path connected (smooth ⇒ locally étale over `𝔸ⁿ`, oka
    `isLocalIso_analytification_map_of_etale`, `ℂⁿ` locally path connected), hence path
    connected. `ι` and `s` define two points `t_ι, t_s ∈ T^an`.
  - `Z := Spec (Ω ⊗_k R)`. The family `𝒴 := Spec (Ω ⊗_k B_A) ⟶ Spec (Ω ⊗_k (A ⊗_k R)) = Z ×_ℂ T`
    is finite étale, so `𝒴^an ⟶ Z^an × T^an` is a covering map with finite fibres
    (oka `isCoveringMap_base_of_isFiniteEtale`, analytifications are Hausdorff).
  - **(S3b) Covering-homotopy lemma (pure topology).** If `p : E → Z × T` is a covering map and
    `γ` is a path in `T` from `t₀` to `t₁`, then `E|_{Z × {t₀}}` and `E|_{Z × {t₁}}` are
    homeomorphic over `Z` (lift the homotopy `(e, τ) ↦ (p₁ e, γ τ)` with
    `IsCoveringMap.liftHomotopy`; inverse from the reversed path; `monodromy_theorem` for
    the compositions).
  - **(S3c)** Fibres of `𝒴^an` over `Z^an × {t}` are the analytifications of the fibres of `𝒴`
    over the `ℂ`-points `t` (oka `analytificationFibreProdIso`), a homeomorphism over the base
    between finite étale analytic covers is an isomorphism of analytic covers (oka
    `AnalyticSpace.coveringSpace` machinery), and full faithfulness of analytification on
    `SchemeLFTℂ.FiniteEtaleOver Z` turns the analytic isomorphism into an algebraic one.
* **(S2) From `ℂ` back to `K`.** The isomorphism of (S3) is defined over a finitely generated
  `k`-subalgebra `C ⊆ ℂ` containing `ι(A)`; since `A → C` is injective and `C` a domain, and
  `K ⊇ Frac A` is algebraically closed, there is an `A`-algebra map `C → K`; base change gives
  `K ⊗_A B_A ≅ K ⊗_{A,s} B_A = K ⊗_k B₀` with `B₀ := k ⊗_{A,s} B_A`.

### The Belyi part

* **(P1)** For `f : X ⟶ ℙ¹_K` Belyi, `f` is étale over `U_K := ℙ¹_K ∖ {0,1,∞}`, finite, so
  `f⁻¹(U_K)` is affine, `= Spec B` with `B` finite étale over `Γ(U_K) ≅ K ⊗_k R`,
  compatibly with `P1.toPullback` (`ℙ¹_K ≅ ℙ¹_k ×_k K`, `P1.isIso_toPullback`).
* **(P2a)** A curve `X` with a finite map `f : X ⟶ ℙ¹_K` and dense open `Y = f⁻¹(U_K)` is the
  relative normalization of `Y ⟶ ℙ¹_K` (`Scheme.Hom.normalization`): `X` has normal stalks
  (DVRs/fields: `Belyi/Curve/Stalks.lean`, curve stalks), `f` is integral.
* **(P2b)** Relative normalization commutes with base change along `Spec K ⟶ Spec k` for any
  field extension `K / k` of a characteristic-zero field: `K` is a filtered union of smooth
  finitely generated `k`-subalgebras (generic smoothness), mathlib proves the smooth case
  (`instance [Smooth g] : IsIso (f.normalizationPullback g)`), and integral closure commutes
  with filtered colimits of flat base changes.
* **(P2c)** Assembly: `X ≅ norm(Y ⟶ ℙ¹_K) ≅ norm(Y₀ ×_k K ⟶ ℙ¹_k ×_k K) ≅ norm(Y₀ ⟶ ℙ¹_k) ×_k K`
  with `Y₀ := Spec B₀ ⟶ U_k ⊆ ℙ¹_k`; hence `DefinableOver k K X` with model
  `X₀ := norm(Y₀ ⟶ ℙ¹_k)`.

## 1. Lean layout

New files under `Belyi/Converse/`:

| file | content | package |
|---|---|---|
| `Spread.lean` | (S1) spreading a finite étale algebra over `K ⊗_k R` to `A ⊗_k R` | S1 |
| `Points.lean` | (S4) `s : A →ₐ[k] k`, injective `ι : A →ₐ[k] ℂ` | S4 |
| `IsoDescent.lean` | (S2) from an iso over `ℂ` to an iso over `K` | S2 |
| `CoveringHomotopy.lean` | (S3b) pure topology | S3b |
| `PathConnected.lean` | (S3a) `T^an` path connected for smooth connected `T` | S3a |
| `Rigidity.lean` | (S3c) + (S3) | S3c |
| `FEtDescent.lean` | (★) | assembly |
| `PuncturedLine.lean` | (P1) | P1 |
| `Normalization.lean` | (P2a), (P2b) | P2 |
| `Main.lean` | (P2c), new proof of `definableOver_of_exists_isBelyiMap` | assembly |

Once `Belyi/Converse/Main.lean` proves `definableOver_of_exists_isBelyiMap` without `sorry`,
`Belyi/SpreadOut.lean` and `Belyi/Descent.lean` are removed, `rigidity_finiteness` is removed
from `Belyi/Rigidity.lean` (the `BelyiCover` definitions stay), and `belyi_iff` becomes
axiom-free: `#print axioms Belyi.belyi_iff` = `[propext, Classical.choice, Quot.sound]`.
