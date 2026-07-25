/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Faithfully-flat descent of quasi-finiteness

Mathlib v4.32 provides faithfully-flat *codescent* of `RingHom.Finite`, `RingHom.FiniteType`,
`RingHom.FinitePresentation`, `RingHom.FormallyUnramified`, `RingHom.Smooth` and `RingHom.Etale`
(`Mathlib/RingTheory/Etale/Descent.lean`, `Mathlib/RingTheory/Finiteness/Descent.lean`), but
**not** of quasi-finiteness. This file supplies that missing brick and its scheme-level
consequence:

* `Algebra.QuasiFinite.of_quasiFinite_tensorProduct_of_faithfullyFlat` — if `T` is a faithfully
  flat `R`-algebra and `T ⊗[R] S` is quasi-finite over `T`, then `S` is quasi-finite over `R`.
* `RingHom.QuasiFinite.codescendsAlong_faithfullyFlat` — the `RingHom.CodescendsAlong` packaging.
* `AlgebraicGeometry.LocallyQuasiFinite.descendsAlong_surjective_inf_flat_inf_quasicompact` —
  `@LocallyQuasiFinite` descends along an fpqc cover `@Surjective ⊓ @Flat ⊓ @QuasiCompact`.

The ring-level statement is the exact converse of `Algebra.QuasiFinite.baseChange`, and reuses its
fibre identification `P.Fiber (T ⊗[R] S) ≃ₐ[κ(P)] κ(P) ⊗[κ(p)] (p.Fiber S)`: quasi-finiteness is
finiteness of every fibre `Module.Finite κ(p) (p.Fiber S)`, and since a faithfully flat cover is
surjective on `Spec`, each prime `p` of `R` is `P.under R` for some prime `P` of `T`; the fibre
finiteness upstairs then descends along the field extension `κ(p) → κ(P)` (faithfully flat, being a
nonzero vector space) by `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`.

This is exactly the ingredient the converse direction of Belyi's theorem needs to descend
finiteness of a Belyi map to its `ℚ̄`-model (B3d descent direction, taxis issue #48): with
`IsProper` of the model available from the curve-descent B3c (#167), `IsFinite` of the model
follows from `IsProper ⊓ LocallyQuasiFinite` via Zariski's main theorem.
-/

open TensorProduct CategoryTheory MorphismProperty

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Faithfully-flat descent of quasi-finiteness.** If `T` is a faithfully flat `R`-algebra and
the base change `T ⊗[R] S` is quasi-finite over `T`, then `S` is quasi-finite over `R`.

This is the converse of `Algebra.QuasiFinite.baseChange`; together they say quasi-finiteness is
insensitive to a faithfully flat base change. -/
lemma QuasiFinite.of_quasiFinite_tensorProduct_of_faithfullyFlat
    (T : Type*) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [QuasiFinite T (T ⊗[R] S)] :
    QuasiFinite R S := by
  refine ⟨fun p hp ↦ ?_⟩
  -- Every prime of `R` is `P.under R` for some prime `P` of `T` (faithful flatness ⇒ surjective
  -- on `Spec`).
  obtain ⟨P, hPprime, hlo⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (A := R) (B := T) p
  letI := Localization.AtPrime.algebraOfLiesOver p P
  -- Fibre finiteness upstairs, transported through the base-change fibre identification.
  have hfin : Module.Finite P.ResidueField (P.Fiber (T ⊗[R] S)) := QuasiFinite.finite_fiber P
  let e : P.Fiber (T ⊗[R] S) ≃ₐ[P.ResidueField]
      P.ResidueField ⊗[p.ResidueField] (p.Fiber S) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  haveI : Module.Finite P.ResidueField (P.ResidueField ⊗[p.ResidueField] (p.Fiber S)) :=
    .of_surjective e.toLinearMap e.surjective
  -- Descend along the faithfully flat field extension `κ(p) → κ(P)`.
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat P.ResidueField

end Algebra

namespace RingHom

/-- **Faithfully-flat codescent of quasi-finiteness**, `RingHom.CodescendsAlong` packaging. -/
lemma QuasiFinite.codescendsAlong_faithfullyFlat :
    CodescendsAlong QuasiFinite FaithfullyFlat := by
  refine .mk _ QuasiFinite.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [quasiFinite_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_quasiFinite_tensorProduct_of_faithfullyFlat S

end RingHom

namespace AlgebraicGeometry

/-- **Faithfully-flat (fpqc) descent of `@LocallyQuasiFinite`.** If the base change of `f` along an
fpqc cover `g` (i.e. `g` is `@Surjective ⊓ @Flat ⊓ @QuasiCompact`) is locally quasi-finite, then so
is `f`. -/
instance LocallyQuasiFinite.descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @LocallyQuasiFinite (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.QuasiFinite.codescendsAlong_faithfullyFlat

/-- **Faithfully-flat (fpqc) descent of `@IsFinite`, via Zariski's main theorem.** Given a
cartesian square `IsPullback fst snd f g` whose leg `g` is an fpqc cover
(`@Surjective ⊓ @Flat ⊓ @QuasiCompact`), if the base change `snd` is finite and `f` is proper,
then `f` is finite.

`IsFinite = IsProper ⊓ LocallyQuasiFinite` (`IsFinite.of_isProper_of_locallyQuasiFinite`, ZMT):
`IsProper f` is a hypothesis (in applications it comes from the target being separated over the
base and the source being proper), and `LocallyQuasiFinite f` descends from `LocallyQuasiFinite snd`
(free from `IsFinite snd`) along the fpqc leg. `@IsFinite` itself does **not** descend along fpqc
covers with the current mathlib API without properness, because affineness descent
(`DescendsAlong @IsAffineHom …`) is still absent — routing through quasi-finiteness + ZMT sidesteps
that gap.

Orientation follows the `DescendsAlong` convention: `f` is the fpqc cover, `fst` its base change of
the descended morphism `g`, and the property descends from `fst` to `g`. -/
theorem isFinite_of_isPullback_of_faithfullyFlat
    {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) [IsProper g]
    [Surjective f] [Flat f] [QuasiCompact f] [IsFinite fst] : IsFinite g := by
  have hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) f :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  haveI : LocallyQuasiFinite g :=
    of_isPullback_of_descendsAlong h hf (inferInstanceAs (LocallyQuasiFinite fst))
  exact IsFinite.of_isProper_of_locallyQuasiFinite g

end AlgebraicGeometry
