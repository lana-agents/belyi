/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.BaseChange
import Belyi.P1.BaseChangeIso

/-!
# Definability of a morphism to `ℙ¹` over a subfield (the pair version of B3)

This file develops the *pair version* of statement **B3** of `references/proof-outline.md`
(taxis issue #48): for an extension `k₀ ⊆ K` (encoded as `[Algebra k₀ K]`), a morphism
`f : X ⟶ ℙ¹_K` from a scheme over `Spec K` is *definable over* `k₀` if it is the base
change of a morphism `f₀ : X₀ ⟶ ℙ¹_{k₀}` over `k₀`, compatibly with the canonical
identification `ℙ¹_{k₀} ×_{k₀} K ≅ ℙ¹_K` (`Belyi.P1.toPullback`, an isomorphism by
`Belyi.P1.isIso_toPullback`).

The base change of the model is expressed through `Belyi.baseChangeModelHom`: given a
model `f₀ : X₀ ⟶ ℙ¹_{k₀}` over `Spec k₀`, its base change along `specAlgebraMap k₀ K` is
the induced morphism `pullback p₀ (specAlgebraMap …) ⟶ pullback (ℙ¹_{k₀} ↘ Spec k₀)
(specAlgebraMap …)` into the base change of `ℙ¹_{k₀}`. The pair definability condition
then reads `f ≫ toPullback = e.hom ≫ baseChangeModelHom …`, where `e : X ≅ pullback p₀
(specAlgebraMap …)` is the identification of `X` with the base change of the model `X₀`
(as in `Belyi.DefinableOver`).

## Main definitions

* `Belyi.baseChangeModelHom`: the base change of a model morphism `f₀ : X₀ ⟶ ℙ¹_{k₀}`
  along `specAlgebraMap k₀ K`.
* `Belyi.DefinableOverPair k₀ K X f`: the existence of a model `f₀ : X₀ ⟶ ℙ¹_{k₀}` of the
  morphism `f : X ⟶ ℙ¹_K`. The witness data is packaged in an existential so that both
  directions of Belyi produce/consume explicit models.

## Main results

* `Belyi.DefinableOverPair.definableOver`: a pair-definable morphism has a definable
  source (forgetting the morphism recovers `Belyi.DefinableOver`).
* `Belyi.DefinableOverPair.comp_structMap`: a pair-definable morphism is automatically a
  morphism over `Spec K` (`f ≫ (ℙ¹_K ↘ Spec K) = X ↘ Spec K`); this is forced by the
  definability condition and does not have to be assumed.
* `Belyi.DefinableOverPair.of_iso` (**B3a**, pair version): invariance under an
  isomorphism of the source over `Spec K` that intertwines the two morphisms to `ℙ¹_K`.

The transitivity in a tower `k₀ ⊆ k₁ ⊆ K` (B3b, pair version), the descent of curve
properties to pair models (B3c) and the matching of finiteness / branch loci (B3d, which
additionally needs the ramification API of #47) are follow-up work on the same issue.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory Limits

variable (k₀ K : Type u) [CommRing k₀] [CommRing K] [Algebra k₀ K]

section BaseChangeModelHom

variable {X₀ : Scheme.{u}} (p₀ : X₀ ⟶ Spec (CommRingCat.of k₀)) (f₀ : X₀ ⟶ P1 k₀)
  (hf₀ : f₀ ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)) = p₀)

/-- The base change of a model morphism `f₀ : X₀ ⟶ ℙ¹_{k₀}` over `Spec k₀` (with structure
morphism `p₀ = f₀ ≫ (ℙ¹_{k₀} ↘ Spec k₀)`) along `specAlgebraMap k₀ K`: the induced morphism
from the base change of `X₀` to the base change `pullback (ℙ¹_{k₀} ↘ Spec k₀)
(specAlgebraMap …)` of `ℙ¹_{k₀}`, which the identification `Belyi.P1.toPullback` compares
with `ℙ¹_K`. -/
noncomputable def baseChangeModelHom :
    pullback p₀ (specAlgebraMap k₀ K) ⟶
      pullback (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K) :=
  pullback.lift (pullback.fst p₀ _ ≫ f₀) (pullback.snd p₀ _)
    (by rw [Category.assoc, hf₀]; exact pullback.condition)

@[reassoc (attr := simp)]
lemma baseChangeModelHom_fst :
    baseChangeModelHom k₀ K p₀ f₀ hf₀ ≫
        pullback.fst (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K) =
      pullback.fst p₀ (specAlgebraMap k₀ K) ≫ f₀ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeModelHom_snd :
    baseChangeModelHom k₀ K p₀ f₀ hf₀ ≫
        pullback.snd (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K) =
      pullback.snd p₀ (specAlgebraMap k₀ K) :=
  pullback.lift_snd _ _ _

end BaseChangeModelHom

/-- A morphism `f : X ⟶ ℙ¹_K` from a scheme over `Spec K` is *definable over* `k₀` if there
is a model `f₀ : X₀ ⟶ ℙ¹_{k₀}` over `Spec k₀` whose base change is identified with `f`
through the canonical identification `ℙ¹_{k₀} ×_{k₀} K ≅ ℙ¹_K` (`Belyi.P1.toPullback`).
Concretely: an identification `e : X ≅ pullback p₀ (specAlgebraMap …)` of `X` with the base
change of the model source (compatible with the structure morphisms, as in
`Belyi.DefinableOver`) such that `f ≫ toPullback = e.hom ≫ baseChangeModelHom …`. -/
def DefinableOverPair (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))]
    (f : X ⟶ P1 K) : Prop :=
  ∃ (X₀ : Scheme.{u}) (p₀ : X₀ ⟶ Spec (CommRingCat.of k₀)) (f₀ : X₀ ⟶ P1 k₀)
    (hf₀ : f₀ ≫ (P1 k₀ ↘ Spec (CommRingCat.of k₀)) = p₀)
    (e : X ≅ pullback p₀ (specAlgebraMap k₀ K)),
    e.hom ≫ pullback.snd p₀ (specAlgebraMap k₀ K) = X ↘ Spec (CommRingCat.of K) ∧
    f ≫ P1.toPullback k₀ K = e.hom ≫ baseChangeModelHom k₀ K p₀ f₀ hf₀

namespace DefinableOverPair

variable {k₀ K} {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [Y.Over (Spec (CommRingCat.of K))]

/-- A pair-definable morphism has a definable source: forgetting the morphism data
recovers `Belyi.DefinableOver`. -/
lemma definableOver {f : X ⟶ P1 K} (h : DefinableOverPair k₀ K X f) :
    DefinableOver k₀ K X := by
  obtain ⟨X₀, p₀, f₀, hf₀, e, hsnd, _⟩ := h
  exact ⟨X₀, p₀, e, hsnd⟩

/-- A pair-definable morphism is automatically a morphism over `Spec K`. The definability
condition forces `f ≫ (ℙ¹_K ↘ Spec K) = X ↘ Spec K`, so this need not be assumed. -/
lemma comp_structMap {f : X ⟶ P1 K} (h : DefinableOverPair k₀ K X f) :
    f ≫ (P1 K ↘ Spec (CommRingCat.of K)) = X ↘ Spec (CommRingCat.of K) := by
  obtain ⟨X₀, p₀, f₀, hf₀, e, hsnd, hf⟩ := h
  have := hf =≫ pullback.snd (P1 k₀ ↘ Spec (CommRingCat.of k₀)) (specAlgebraMap k₀ K)
  rwa [Category.assoc, P1.toPullback_snd, Category.assoc, baseChangeModelHom_snd, hsnd] at this

/-- **B3a** (pair version): pair definability is invariant under an isomorphism `φ : X ≅ Y`
of the source over `Spec K` that intertwines the morphisms to `ℙ¹_K` (`f = φ.hom ≫ g`). -/
lemma of_iso {f : X ⟶ P1 K} {g : Y ⟶ P1 K} (φ : X ≅ Y)
    (hφ : φ.hom ≫ (Y ↘ Spec (CommRingCat.of K)) = X ↘ Spec (CommRingCat.of K))
    (hfg : f = φ.hom ≫ g) (h : DefinableOverPair k₀ K X f) :
    DefinableOverPair k₀ K Y g := by
  obtain ⟨X₀, p₀, f₀, hf₀, e, hsnd, hf⟩ := h
  refine ⟨X₀, p₀, f₀, hf₀, φ.symm ≪≫ e, ?_, ?_⟩
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hsnd, ← hφ, Iso.inv_hom_id_assoc]
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hf, hfg, Category.assoc,
      Iso.inv_hom_id_assoc]

end DefinableOverPair

end Belyi
