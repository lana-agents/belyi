/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Forward
import Belyi.ForwardDefinable
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
is **not** assemblable unconditionally today. Its `←` half is `belyi_converse` above. Its `→`
half — from a bare `DefinableOver k K X` witness produce a Belyi map — needs the model `X₀ / k`
obtained from definability to be *itself a curve*, i.e. the **B3c descent** direction
`IsCurveOver K X ⇒ IsCurveOver k X₀` along the faithfully-flat `Spec K ⟶ Spec k` (taxis #167).
One cannot instead apply the forward direction over `K = ℂ` directly: `belyi_forward` requires
`Algebra.IsAlgebraic ℚ K`, which fails for `ℂ` — precisely why one descends the branch points
to `ℚ̄`.

That entire forward `→` half is now assembled: `exists_isBelyiMap_of_definableOver`
(`Belyi/ForwardDefinable.lean`) unpacks a bare `DefinableOver k K X` witness, uses the descent
`IsCurveOver.of_baseChangeModel` to obtain `[IsCurveOver k X₀]`, and transports the base-changed
Belyi map back onto `X`. After the geometric-integrality and separated/proper legs of the
descent landed (taxis #204/#167), the *only* residual input is the single mathlib-shaped
instance `MorphismProperty.DescendsAlong (@SmoothOfRelativeDimension 1)
(@Surjective ⊓ @Flat ⊓ @QuasiCompact)` — the smooth-descent brick, taxis #205.

We therefore provide two forms of the equivalence:

* `belyi_iff` — **gated on the forward implication as an explicit hypothesis** `hforward`, with
  the `←` half proved unconditionally. Maximally weak assumption: a caller supplying the forward
  map by any route obtains the `↔`.
* `belyi_iff_of_descendsAlong` — **gated on the single mathlib-shaped instance**
  `[DescendsAlong (@SmoothOfRelativeDimension 1) (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]`, the
  exact taxis-#205 brick, with the forward implication discharged internally by
  `exists_isBelyiMap_of_definableOver`. The moment #205 supplies that instance globally, this
  becomes the **fully ungated headline** with no further edit here.

## Main results

* `Belyi.belyi_forward` / `Belyi.belyi_forward_baseChange` — forward direction (B8), re-exported.
* `Belyi.belyi_converse` — converse direction (B12), re-exported.
* `Belyi.exists_isBelyiMap_congr` (**B14a**) — the "admits a Belyi map" side is invariant under
  isomorphism of the source curve.
* `Belyi.definableOver_congr` (**B14a**) — the "definable over `ℚ̄`" side is invariant under
  isomorphism over `Spec K`.
* `Belyi.belyi_iff` (**B14**) — Belyi's theorem as an `↔`, with the forward implication supplied
  as an explicit hypothesis.
* `Belyi.belyi_iff_of_descendsAlong` (**B14**) — Belyi's theorem as an `↔`, with the forward
  implication discharged internally and gated only on the single smooth-descent instance
  (taxis #205); fully ungated the moment that instance lands globally.
* `Belyi.definableOver_baseChangeAlgEquiv` / `Belyi.exists_isBelyiMap_baseChangeAlgEquiv`
  (**B14 item 3**) — both sides of Belyi's theorem are invariant under base change of the source
  along a `k`-algebra automorphism `σ` of `K` (Galois conjugation): a definable curve `X` and
  its conjugate `X^σ` share the same `k`-model (`Belyi.baseChangeConjIso`), hence are
  isomorphic over `Spec K`, so definability and admitting a Belyi map transport across.
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

/-- **Belyi's theorem (B14), instance-gated equivalence.** For a curve `X` over `K = ℂ`
(algebraically closed, characteristic zero) and `k = ℚ̄`, definability over `ℚ̄` is equivalent
to admitting a Belyi map.

Unlike `belyi_iff`, the forward implication `→` is **not** taken as a hypothesis: it is
discharged internally by `exists_isBelyiMap_of_definableOver` (`Belyi/ForwardDefinable.lean`),
which unpacks the `DefinableOver k K X` witness, descends the model to a curve over `ℚ̄`
(`IsCurveOver.of_baseChangeModel`), and transports the base-changed Belyi map back onto `X`.
The converse `←` is `belyi_converse` (modulo the sanctioned converse `sorry`s).

The single residual assumption is the instance
`[DescendsAlong (@SmoothOfRelativeDimension 1) (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]` — the
smooth-descent brick of B3c (taxis #205), the *only* leg of `IsCurveOver.of_baseChangeModel`
not yet available in mathlib v4.32 (the geometric-integrality and separated/proper legs landed
in taxis #204/#167). The moment that instance is supplied globally, this theorem is the fully
ungated headline of Belyi's theorem, with no further change to this file. -/
theorem belyi_iff_of_descendsAlong (k K : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    [Algebra.IsAlgebraic ℚ k] [Field K] [IsAlgClosed K] [CharZero K] [Algebra k K]
    [MorphismProperty.DescendsAlong (@SmoothOfRelativeDimension 1)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] [IsCurveOver K X] :
    DefinableOver k K X ↔ ∃ f : X ⟶ P1 K, IsBelyiMap K f :=
  ⟨exists_isBelyiMap_of_definableOver k K X, belyi_converse k K X⟩

/-! ## B14 (item 3): invariance under base change along a `k`-automorphism of `K`

The parent issue asks for "invariance under base change/isomorphism". `exists_isBelyiMap_congr`
and `definableOver_congr` above record invariance under isomorphism of the source curve
(**B14a**). This section records invariance under **base change of the source along a
`k`-algebra automorphism `σ` of `K`** — the Galois-conjugation action in the relevant setting.

The mathematical content is the honest observation that *definability forces Galois
invariance*: because `σ` fixes `k`, the spectrum map `Spec.map σ` is compatible with the
structure map `Spec K ⟶ Spec k` (`specAlgebraMap_algEquiv_comp`), so the `σ`-conjugate of a
scheme with a `k`-model has the **same** `k`-model (`baseChangeConjIso`). Hence the conjugate
scheme is isomorphic to the original over `Spec K`, and both sides of `belyi_iff` are invariant
(`definableOver_baseChangeAlgEquiv`, `exists_isBelyiMap_baseChangeAlgEquiv`). -/

/-- The spectrum map of a `k`-algebra automorphism `σ` of `K` is compatible with the structure
morphism `Spec K ⟶ Spec k₀`: precomposing `specAlgebraMap k₀ K` with `Spec.map σ` leaves it
unchanged, because `σ` fixes `k₀` (`AlgEquiv.commutes`). -/
lemma specAlgebraMap_algEquiv_comp (k₀ K : Type u) [CommRing k₀] [CommRing K] [Algebra k₀ K]
    (σ : K ≃ₐ[k₀] K) :
    Spec.map (CommRingCat.ofHom (σ : K →+* K)) ≫ specAlgebraMap k₀ K = specAlgebraMap k₀ K := by
  rw [specAlgebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun x => σ.commutes x

/-- The base change of a scheme `X` over `Spec K` along a `k₀`-algebra automorphism `σ` of `K`
(its **Galois conjugate** `X^σ`): the pullback of the structure morphism `X ↘ Spec K` along
`Spec.map σ`. -/
noncomputable def baseChangeAlgEquiv (k₀ K : Type u) [CommRing k₀] [CommRing K] [Algebra k₀ K]
    (σ : K ≃ₐ[k₀] K) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] : Scheme.{u} :=
  pullback (X ↘ Spec (CommRingCat.of K)) (Spec.map (CommRingCat.ofHom (σ : K →+* K)))

/-- `baseChangeAlgEquiv σ X` is a scheme over `Spec K` via the second projection. -/
noncomputable instance (k₀ K : Type u) [CommRing k₀] [CommRing K] [Algebra k₀ K]
    (σ : K ≃ₐ[k₀] K) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] :
    (baseChangeAlgEquiv k₀ K σ X).Over (Spec (CommRingCat.of K)) :=
  ⟨pullback.snd _ _⟩

section Conjugate

variable (k₀ K : Type u) [CommRing k₀] [CommRing K] [Algebra k₀ K] (σ : K ≃ₐ[k₀] K)
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))]
  {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of k₀))
  (e : X ≅ pullback f₀ (specAlgebraMap k₀ K))
  (he : e.hom ≫ pullback.snd f₀ (specAlgebraMap k₀ K) = X ↘ Spec (CommRingCat.of K))

include e he

/-- Left-leg iso: replace the left leg `X ↘ Spec K = e.hom ≫ pullback.snd f₀ q` of
`baseChangeAlgEquiv σ X = pullback (X ↘ Spec K) (Spec.map σ)` by the isomorphism `e.hom`. -/
noncomputable def conjLegIso :
    baseChangeAlgEquiv k₀ K σ X ≅ pullback (pullback.snd f₀ (specAlgebraMap k₀ K))
      (Spec.map (CommRingCat.ofHom (σ : K →+* K))) := by
  have e₁ : (X ↘ Spec (CommRingCat.of K)) ≫ 𝟙 _ =
      e.hom ≫ pullback.snd f₀ (specAlgebraMap k₀ K) := by rw [Category.comp_id, ← he]
  have e₂ : (Spec.map (CommRingCat.ofHom (σ : K →+* K))) ≫ 𝟙 _ =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom (σ : K →+* K)) := by rw [Category.comp_id, Category.id_comp]
  have himap : IsIso (pullback.map (X ↘ Spec (CommRingCat.of K))
      (Spec.map (CommRingCat.ofHom (σ : K →+* K))) (pullback.snd f₀ (specAlgebraMap k₀ K))
      (Spec.map (CommRingCat.ofHom (σ : K →+* K))) e.hom (𝟙 _) (𝟙 _) e₁ e₂) :=
    pullback.map_isIso _ _ _ _ e.hom (𝟙 _) (𝟙 _) e₁ e₂
  exact @asIso _ _ _ _ _ himap

/-- The isomorphism `baseChangeAlgEquiv σ X ≅ X₀ ×_{k₀} K` built from an explicit `k₀`-model
`(X₀, f₀, e)` of `X`. Since `σ` fixes `k₀`, base change along `Spec.map σ` acts trivially on the
model: `Spec.map σ ≫ specAlgebraMap k₀ K = specAlgebraMap k₀ K`. Data helper for
`definableOver_baseChangeAlgEquiv` / `exists_isBelyiMap_baseChangeAlgEquiv`. -/
noncomputable def baseChangeConjIso :
    baseChangeAlgEquiv k₀ K σ X ≅ pullback f₀ (specAlgebraMap k₀ K) :=
  conjLegIso k₀ K σ X f₀ e he ≪≫
    pullbackLeftPullbackSndIso f₀ (specAlgebraMap k₀ K)
        (Spec.map (CommRingCat.ofHom (σ : K →+* K))) ≪≫
      pullback.congrHom rfl (specAlgebraMap_algEquiv_comp k₀ K σ)

/-- `baseChangeConjIso` is compatible with the structure morphisms to `Spec K`. -/
lemma baseChangeConjIso_hom_snd :
    (baseChangeConjIso k₀ K σ X f₀ e he).hom ≫ pullback.snd f₀ (specAlgebraMap k₀ K) =
      pullback.snd (X ↘ Spec (CommRingCat.of K))
        (Spec.map (CommRingCat.ofHom (σ : K →+* K))) := by
  simp only [baseChangeConjIso, conjLegIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_snd]
  erw [pullback.lift_snd]
  rw [Category.comp_id]

end Conjugate

/-- **B14 (item 3), definability side.** Being definable over `k₀` is invariant under base change
along a `k₀`-automorphism `σ` of `K`. -/
theorem definableOver_baseChangeAlgEquiv (k₀ K : Type u) [CommRing k₀] [CommRing K]
    [Algebra k₀ K] (σ : K ≃ₐ[k₀] K) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))]
    (h : DefinableOver k₀ K X) : DefinableOver k₀ K (baseChangeAlgEquiv k₀ K σ X) := by
  obtain ⟨X₀, f₀, e, he⟩ := h
  exact ⟨X₀, f₀, baseChangeConjIso k₀ K σ X f₀ e he, baseChangeConjIso_hom_snd k₀ K σ X f₀ e he⟩

/-- **B14 (item 3), Belyi side.** For a curve `X` over `K` definable over `k₀`, admitting a
Belyi map is invariant under base change along a `k₀`-automorphism `σ` of `K` (the conjugate
scheme is isomorphic to `X`, so `exists_isBelyiMap_congr` applies). -/
theorem exists_isBelyiMap_baseChangeAlgEquiv (k₀ K : Type u) [CommRing k₀] [Field K]
    [Algebra k₀ K] (σ : K ≃ₐ[k₀] K) (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of K))] (h : DefinableOver k₀ K X) :
    (∃ f : baseChangeAlgEquiv k₀ K σ X ⟶ P1 K, IsBelyiMap K f) ↔
      (∃ f : X ⟶ P1 K, IsBelyiMap K f) := by
  obtain ⟨X₀, f₀, e, he⟩ := h
  exact exists_isBelyiMap_congr K (baseChangeConjIso k₀ K σ X f₀ e he ≪≫ e.symm)

end Belyi
