/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Forward
import Belyi.Descent
import Belyi.MarkedPair
import Belyi.MarkedBaseChange

/-!
# Belyi's theorem: the assembled main statements (B14)

This file is the single top-level entry point for Belyi's theorem, statement **B14** of
`references/proof-outline.md`. It gathers the two directions — assembled elsewhere in the
library — under stable, documented names, records the **B14a** invariance-under-isomorphism
congruence lemmas, and states the headline equivalence **B14** in an honest
hypothesis-gated form. Downstream developments (marked-curve / Belyi-cuspidalization work)
can depend on `import Belyi.Main` alone.

## The two directions

Working with `k = ℚ̄` (an algebraically closed field of characteristic zero that is algebraic
over `ℚ`) and `K = ℂ` (any algebraically closed field of characteristic zero over `k`):

* **Forward (B8), `belyi_forward`.** Every curve over `k = ℚ̄` admits a Belyi map. This is the
  genuinely `axiom`/`sorry`-free half (`Belyi/Forward.lean`), taking the `ℚ̄`-curve **model as
  data** — exactly what B1 produces.
* **Converse (B12), `belyi_converse`.** A curve over `K = ℂ` that admits a Belyi map is
  definable over `k = ℚ̄` (`Belyi/Descent.lean`). This rests on the three **sanctioned**
  converse obligations `rigidity_finiteness` (B9), `belyi_spreadOut` (B10(ii)) and
  `spreadOut_isotrivial_point` (B11), currently stated as `theorem … := sorry` and tracked by
  taxis issues #194 / #199 / #200.

## The headline equivalence and its gap

The clean two-way statement `DefinableOver ℚ̄ X ↔ ∃ f, IsBelyiMap f` for a curve `X` over `ℂ`
is **not** assemblable today. Its `←` half is `belyi_converse` above. Its `→` half — from a
bare `DefinableOver k K X` witness produce a Belyi map — needs the model `X₀ / k` obtained
from definability to be *itself a curve*, i.e. the **B3c descent** direction
`IsCurveOver K X ⇒ IsCurveOver k X₀` along the faithfully-flat `Spec K ⟶ Spec k` (taxis #167,
whose ring-core keystone #167/#183 has no mathlib v4.32 template). One cannot instead apply the
forward direction over `K = ℂ` directly: `belyi_forward` requires `Algebra.IsAlgebraic ℚ K`,
which fails for `ℂ` — precisely why one descends the branch points to `ℚ̄`.

We therefore state the equivalence as `belyi_iff`, **gated on the forward implication as an
explicit hypothesis** `hforward` (the content #167 unlocks), and prove the `←` half
unconditionally. Once #167 lands, discharging `hforward` upgrades `belyi_iff` to the
ungated headline in one line.

## Main results

* `Belyi.belyi_forward` / `Belyi.belyi_forward_baseChange` — forward direction (B8), re-exported.
* `Belyi.belyi_converse` — converse direction (B12), re-exported.
* `Belyi.exists_isBelyiMap_congr` (**B14a**) — the "admits a Belyi map" side is invariant under
  isomorphism of the source curve.
* `Belyi.definableOver_congr` (**B14a**) — the "definable over `ℚ̄`" side is invariant under
  isomorphism over `Spec K`.
* `Belyi.belyi_iff` (**B14**) — Belyi's theorem as an `↔`, with the forward implication gated on
  the B3c descent input.
* Marked re-exports (**B14c**): `Belyi.exists_isBelyiMap_marked_of_isCurveOver` and
  `Belyi.exists_definableOverPair_isBelyiMap_marked_baseChange_of_isCurveOver` are made
  reachable through this single import target for downstream marked-curve work.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

/-! ## Forward and converse directions (re-exports) -/

/-- **Belyi's theorem, forward direction (B8), model form.** Every curve `X` over an
algebraically closed field `k` of characteristic zero that is algebraic over `ℚ` — i.e. over
`ℚ̄` — admits a Belyi map. Re-export of `Belyi.exists_isBelyiMap_of_isCurveOver`. -/
theorem belyi_forward
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] [IsCurveOver k X] :
    ∃ f : X ⟶ P1 k, IsBelyiMap k f :=
  (exists_isBelyiMap_of_isCurveOver k X).imp fun _ h => h.1

/-- **Belyi's theorem, forward direction after base change (B8 + B2b/B3d).** The base change of
a curve over `k = ℚ̄` to an arbitrary extension field `K` (model case `K = ℂ`) admits a Belyi
map over `K`. Re-export of `Belyi.exists_isBelyiMap_baseChange_of_isCurveOver`. -/
theorem belyi_forward_baseChange
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
    (K : Type u) [Field K] [Algebra k K]
    (X₀ : Scheme.{u}) [X₀.Over (Spec (CommRingCat.of k))] [IsCurveOver k X₀] :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ P1 K), IsBelyiMap K f :=
  exists_isBelyiMap_baseChange_of_isCurveOver k K X₀

/-- **Belyi's theorem, converse direction (B12).** A curve `X` over `K = ℂ` (algebraically
closed, characteristic zero) that admits a Belyi map is definable over `k = ℚ̄`. Re-export of
`Belyi.definableOver_of_exists_isBelyiMap`; rests on the sanctioned converse obligations
(`rigidity_finiteness`, `belyi_spreadOut`, `spreadOut_isotrivial_point`). -/
theorem belyi_converse (k K : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    [Algebra.IsAlgebraic ℚ k] [Field K] [IsAlgClosed K] [CharZero K] [Algebra k K]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X]
    (h : ∃ f : X ⟶ P1 K, IsBelyiMap K f) : DefinableOver k K X :=
  definableOver_of_exists_isBelyiMap k K X h

/-! ## B14a: invariance under isomorphism -/

/-- **B14a (Belyi side).** Admitting a Belyi map is invariant under isomorphism of the source
curve: if `X ≅ Y` then `X` admits a Belyi map iff `Y` does. Transport is precomposition of a
Belyi map with the isomorphism (`IsBelyiMap.of_isIso_comp`), which preserves the branch
locus. -/
theorem exists_isBelyiMap_congr (K : Type u) [Field K] {X Y : Scheme.{u}} (φ : X ≅ Y) :
    (∃ f : X ⟶ P1 K, IsBelyiMap K f) ↔ (∃ g : Y ⟶ P1 K, IsBelyiMap K g) := by
  constructor
  · rintro ⟨f, hf⟩
    haveI := hf.locallyOfFinitePresentation
    exact ⟨φ.inv ≫ f, hf.of_isIso_comp φ.inv⟩
  · rintro ⟨g, hg⟩
    haveI := hg.locallyOfFinitePresentation
    exact ⟨φ.hom ≫ g, hg.of_isIso_comp φ.hom⟩

/-- **B14a (definability side).** Being definable over `k` is invariant under isomorphism over
`Spec K`: if `φ : X ≅ Y` is compatible with the structure morphisms to `Spec K`, then
`DefinableOver k K X ↔ DefinableOver k K Y`. Both directions are `DefinableOver.of_iso`
(B3a). -/
theorem definableOver_congr (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    (φ : X ≅ Y) (hφ : φ.hom ≫ (Y ↘ Spec (CommRingCat.of K)) = X ↘ Spec (CommRingCat.of K)) :
    DefinableOver k K X ↔ DefinableOver k K Y := by
  constructor
  · exact DefinableOver.of_iso φ hφ
  · refine DefinableOver.of_iso φ.symm ?_
    rw [Iso.symm_hom, ← hφ, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-! ## B14: the headline equivalence (hypothesis-gated) -/

/-- **Belyi's theorem (B14), hypothesis-gated equivalence.** For a curve `X` over `K = ℂ`
(algebraically closed, characteristic zero) and `k = ℚ̄`, definability over `ℚ̄` is equivalent
to admitting a Belyi map.

The converse (`←`) is `belyi_converse`, proved unconditionally (modulo the sanctioned converse
`sorry`s). The forward (`→`) implication `hforward` is supplied as a hypothesis: producing a
Belyi map from a bare `DefinableOver k K X` witness requires the model of `X` to be a *curve*,
i.e. the B3c descent input `IsCurveOver K X ⇒ IsCurveOver k X₀` (taxis #167), which is not yet
available in mathlib v4.32. Once #167 lands, `hforward` is discharged and this becomes the
ungated headline. -/
theorem belyi_iff (k K : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    [Algebra.IsAlgebraic ℚ k] [Field K] [IsAlgClosed K] [CharZero K] [Algebra k K]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X]
    (hforward : DefinableOver k K X → ∃ f : X ⟶ P1 K, IsBelyiMap K f) :
    DefinableOver k K X ↔ ∃ f : X ⟶ P1 K, IsBelyiMap K f :=
  ⟨hforward, belyi_converse k K X⟩

end Belyi
