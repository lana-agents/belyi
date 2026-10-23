/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.CategoryTheory.Conj
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.RingTheory.TensorProduct.Finite
import Pi1.FundamentalGroup.GaloisQuotient
import Belyi.Curve.Basic
import Belyi.FunctionField

/-!
# Whitelist: the relative Grothendieck conjecture over sub-`p`-adic fields ([LocAn] Thm A)

This file **states** (it does not prove) the classical theorem

> **[LocAn] Theorem A** (S. Mochizuki, *The local pro-`p` anabelian geometry of curves*,
> Invent. Math. 138 (1999), Theorem A = Theorem 16.5; text file
> `The Local Pro-p Anabelian Geometry of Curves.txt`, l.104 and l.4704). Let `K` be
> sub-`p`-adic, `X_K` a smooth pro-variety and `Y_K` a hyperbolic pro-curve over `K`. Then the
> natural map `Hom^dom_K(X_K, Y_K) → Hom^open_{Γ_K}(Π_{X_K}, Π_{Y_K})` (open continuous
> homomorphisms over `Γ_K`, up to composition with inner automorphisms from `Δ_Y`) is bijective,

in the form in which [AbsTopI] Definition 4.6 (ii) ("the rel-isom-DGC holds", resp. "the
rel-hom-DGC holds"; `Topics in Absolute Anabelian Geometry I.txt` l.3351–3403) uses it, for
hyperbolic curves over `k`, full profinite `π₁`, `Σ` the set of all primes, the identity as
scheme-theoretic envelope and `ζ_k = id` ([AbsTopI] Example 4.8 (ii), l.3570: "the rel-hom-DGC
follows from [Mzk3], Theorem A"). The statement follows the multiradial scoping document
`MR6-scoping.md` §1.3 (iut repository, `Iut/Multiradial/ROADMAP.md` MR7).

**Phase I whitelist.** By the owner's decision (Zulip #628), the multiradial algorithm of IUT III
Theorem 3.11 is formalised over genuine objects, conditional on a short whitelist of classical
theorems stated about genuine objects. `RelIsomDGC k` (and its homomorphism version
`RelHomDGC k`) is the whitelist entry for [LocAn] Theorem A. It is never assumed globally: a
theorem that needs it takes the explicit hypothesis `(hDGC : ∀ k, IsSubPAdic k → RelIsomDGC k)`.

Everything here is a genuine object:

* `IsSubPAdic k` is [LocAn] Definition 15.4 (i) (l.4337): `k` embeds into a finitely generated
  field extension of `ℚ_p`.
* `curveGenus k X` is `dim_k H⁰(X, Ω¹_{X/k})`, computed inside `Ω_{K(X)/k}` as the differentials
  that are regular at every point (`Ω¹_{X/k}` is locally free for a smooth curve, so its global
  sections are the generic germs lying in every stalk `Ω_{𝒪_{X,x}/k}`).
* `HypCurve k`: an open `U` of a smooth proper geometrically integral curve `X̄` over `k`
  (`Belyi.IsCurveOver`) with finite complement and `2g - 2 + r > 0`, where `r` is the number of
  geometric cusps `Σ_{c ∉ U} [κ(c) : k]`.
* `π₁ᵉᵗ(ξ)` is pi1's étale fundamental group (automorphisms of the fibre functor at the geometric
  point `ξ : Spec Ω ⟶ U`), with `FiniteEtale.fundamentalGroupMap` and `FiniteEtale.toGaloisGroup`
  (`Π_U → G_k = Gal(Ω/k)`).
* "Up to `Δ₂`-conjugation" is expressed with *paths*: isomorphisms of fibre functors
  `γ : fiber (ξ₁ ≫ f) ≅ fiber ξ₂` lying over the trivial path of `Spec k`
  (`IsPathOverBase`); two such paths differ exactly by an element of `Δ₂ = ker(Π₂ → G_k)`.

## Main definitions

* `Belyi.Anabelian.IsSubPAdic`, `Belyi.Anabelian.curveGenus`, `Belyi.Anabelian.cuspDegree`;
* `Belyi.Anabelian.HypCurve`, `HypCurve.GeomPt`, `HypCurve.KIso`, `HypCurve.KHom`;
* `Belyi.Anabelian.IsOverGk`, `Belyi.Anabelian.IsPathOverBase`, `Belyi.Anabelian.InducedBy`,
  `Belyi.Anabelian.InducedByHom`;
* `Belyi.Anabelian.RelIsomDGC`, `Belyi.Anabelian.RelHomDGC` (**whitelist: [LocAn] Thm A**);
* `Belyi.Anabelian.RelIsomDGC.Exists`, `Belyi.Anabelian.RelIsomDGC.Unique`: the existence and
  uniqueness halves, with `Belyi.Anabelian.relIsomDGC_iff_exists_and_unique`
  (`RelIsomDGC k ↔ Exists k ∧ Unique k`). Consumers can take the two halves as separate inputs, so
  that a proved uniqueness half (MR7) leaves only the existence half as a hypothesis.
-/

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace Belyi.Anabelian

/-! ### Sub-`p`-adic fields -/

/-- **Sub-`p`-adic fields** ([LocAn], Definition 15.4 (i), l.4337): "We shall call a field `K` a
sub-`p`-adic field if there exists a prime number `p`, together with a finitely generated field
extension `L` of `ℚ_p` such that `K` is isomorphic to a subfield of `L`." -/
def IsSubPAdic (k : Type u) [Field k] : Prop :=
  ∃ (p : ℕ) (_ : Fact p.Prime) (L : Type u) (_ : Field L) (_ : Algebra ℚ_[p] L),
    (⊤ : IntermediateField ℚ_[p] L).FG ∧ Nonempty (k →+* L)

/-- A subfield of a sub-`p`-adic field is sub-`p`-adic. -/
theorem IsSubPAdic.of_ringHom {k k' : Type u} [Field k] [Field k'] (f : k →+* k')
    (h : IsSubPAdic k') : IsSubPAdic k := by
  obtain ⟨p, hp, L, _, _, hL, ⟨g⟩⟩ := h
  exact ⟨p, hp, L, _, _, hL, ⟨g.comp f⟩⟩

/-- A finite extension of `ℚ_p` (in particular an MLF) is sub-`p`-adic. -/
theorem isSubPAdic_of_finiteDimensional (p : ℕ) [Fact p.Prime] (L : Type u) [Field L]
    [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] : IsSubPAdic L :=
  ⟨p, inferInstance, L, inferInstance, inferInstance,
    IntermediateField.fg_of_noetherian _, ⟨RingHom.id L⟩⟩

/-- `ℚ_p` is sub-`p`-adic. -/
theorem isSubPAdic_padic (p : ℕ) [Fact p.Prime] : IsSubPAdic ℚ_[p] :=
  isSubPAdic_of_finiteDimensional p ℚ_[p]

/-- **Number fields are sub-`p`-adic** (for every prime `p`): a number field `K` embeds into the
residue field of a maximal ideal of `ℚ_p ⊗_ℚ K`, a finite extension of `ℚ_p`. -/
theorem isSubPAdic_of_numberField (p : ℕ) [Fact p.Prime] (K : Type u) [Field K]
    [NumberField K] : IsSubPAdic K := by
  haveI : Nontrivial (ℚ_[p] ⊗[ℚ] K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain ℚ ℚ_[p] K
      (algebraMap ℚ ℚ_[p]).injective (algebraMap ℚ K).injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (ℚ_[p] ⊗[ℚ] K)
  letI : Field ((ℚ_[p] ⊗[ℚ] K) ⧸ m) := Ideal.Quotient.field m
  haveI : FiniteDimensional ℚ_[p] ((ℚ_[p] ⊗[ℚ] K) ⧸ m) := inferInstance
  exact (isSubPAdic_of_finiteDimensional p ((ℚ_[p] ⊗[ℚ] K) ⧸ m)).of_ringHom
    ((Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom)

/-! ### Genus and cusps of a curve -/

section Genus

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The `k`-algebra structure on the stalk `𝒪_{X,x}` of a `k`-scheme: pull a constant back along
the structure morphism and take its germ at `x`. -/
abbrev stalkAlgebra (x : X) : Algebra k (X.presheaf.stalk x) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop ≫
    X.presheaf.germ ⊤ x trivial).hom.toAlgebra

/-- The `k`-algebra structure on the residue field `κ(x)` of a point of a `k`-scheme. -/
abbrev residueFieldAlgebra (x : X) : Algebra k (X.residueField x) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop ≫
    X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom.toAlgebra

/-- The degree `[κ(x) : k]` of a point of a `k`-scheme (`0` if infinite). For a closed point of
a curve over `k` of characteristic `0`, it is the number of geometric points over `x`. -/
def pointDegree (x : X) : ℕ :=
  letI := residueFieldAlgebra k X x
  Module.finrank k (X.residueField x)

section IsIntegral

open scoped Belyi

variable [IsIntegral X]

/-- The composite `k → 𝒪_{X,x} → K(X)` is the structure map `k → K(X)`. -/
theorem stalkAlgebra_isScalarTower (x : X) :
    letI := stalkAlgebra k X x
    IsScalarTower k (X.presheaf.stalk x) X.functionField := by
  letI := stalkAlgebra k X x
  refine IsScalarTower.of_algebraMap_eq' ?_
  simp_rw [RingHom.algebraMap_toAlgebra]
  rw [← CommRingCat.hom_comp]
  congr 1
  simp only [Category.assoc, X.presheaf.germ_stalkSpecializes]

/-- The image of `Ω_{𝒪_{X,x}/k}` in `Ω_{K(X)/k}`: the differentials of the function field that
are regular at `x`. -/
def regularDifferentialsAt (x : X) : Submodule k (Ω[X.functionField⁄k]) :=
  letI := stalkAlgebra k X x
  letI := stalkAlgebra_isScalarTower k X x
  LinearMap.range
    ((KaehlerDifferential.map k k (X.presheaf.stalk x) X.functionField).restrictScalars k)

/-- `H⁰(X, Ω¹_{X/k})`, realised inside `Ω_{K(X)/k}` as the differentials of the function field
that are regular at every point of `X`. For a smooth curve `X` over `k`, `Ω¹_{X/k}` is locally
free, so its global sections are exactly the generic germs that lie in every stalk
`(Ω¹_{X/k})_x = Ω_{𝒪_{X,x}/k}`. -/
def globalDifferentials : Submodule k (Ω[X.functionField⁄k]) :=
  ⨅ x : X, regularDifferentialsAt k X x

/-- The **genus** `g = dim_k H⁰(X, Ω¹_{X/k})` of a smooth proper curve over `k`. -/
def curveGenus : ℕ :=
  Module.finrank k (globalDifferentials k X)

end IsIntegral

/-- The number of geometric points of `X` outside the open `U`: `Σ_{c ∉ U} [κ(c) : k]`. -/
def cuspDegree (U : X.Opens) : ℕ :=
  ∑ᶠ c ∈ (U : Set X)ᶜ, pointDegree k X c

end Genus

/-! ### Hyperbolic curves -/

/-- A **hyperbolic curve** over `k` ([LocAn] §0, [AbsTopI] §0): the complement `U` of finitely
many closed points in a smooth proper geometrically integral curve `X̄` over `k`, such that
`2g - 2 + r > 0`, where `g` is the genus of `X̄` and `r = Σ_{c ∉ U} [κ(c) : k]` is the number of
geometric cusps. The fields are the defining conditions of the notion. -/
structure HypCurve (k : Type u) [Field k] where
  /-- The smooth compactification `X̄`. -/
  Xbar : Scheme.{u}
  /-- The structure morphism `X̄ ⟶ Spec k`. -/
  [over : Xbar.Over (Spec (.of k))]
  /-- `X̄` is a smooth proper geometrically integral curve over `k`. -/
  [isCurve : IsCurveOver k Xbar]
  /-- The open subscheme `U = X̄ ∖ {cusps}`. -/
  U : Xbar.Opens
  nonempty : (U : Set Xbar).Nonempty
  cusps_finite : (U : Set Xbar)ᶜ.Finite
  /-- `2g - 2 + r > 0`. -/
  hyperbolic :
    haveI := IsCurveOver.isIntegral k Xbar
    2 < 2 * curveGenus k Xbar + cuspDegree k Xbar U

namespace HypCurve

variable {k : Type u} [Field k]

attribute [instance] HypCurve.over HypCurve.isCurve

/-- The structure morphism `U ⟶ Spec k`. -/
def toSpec (C : HypCurve k) : C.U.toScheme ⟶ Spec (.of k) :=
  C.U.ι ≫ (C.Xbar ↘ Spec (.of k))

/-- A **geometric point** of `U` over a fixed separably closed extension `Ω` of `k`. -/
structure GeomPt (Ω : Type u) [Field Ω] [Algebra k Ω] (C : HypCurve k) where
  /-- The point `Spec Ω ⟶ U`. -/
  x : Spec (.of Ω) ⟶ C.U.toScheme
  over : x ≫ C.toSpec = Spec.map (CommRingCat.ofHom (algebraMap k Ω))

/-- `k`-isomorphisms `U₁ ≅ U₂`. -/
def KIso (C₁ C₂ : HypCurve k) : Type u :=
  {f : C₁.U.toScheme ≅ C₂.U.toScheme // f.hom ≫ C₂.toSpec = C₁.toSpec}

/-- Dominant `k`-morphisms `U₁ ⟶ U₂`. -/
def KHom (C₁ C₂ : HypCurve k) : Type u :=
  {f : C₁.U.toScheme ⟶ C₂.U.toScheme // IsDominant f ∧ f ≫ C₂.toSpec = C₁.toSpec}

end HypCurve

/-! ### Outer homomorphisms over `G_k` and the maps induced by morphisms of curves -/

section Induced

open FiniteEtale HypCurve

variable {k : Type u} [Field k] {Ω : Type u} [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
  [IsGalois k Ω] {C₁ C₂ : HypCurve k}

/-- A continuous homomorphism `φ : Π_{U₁} → Π_{U₂}` **lies over `G_k`**:
`pr₂ ∘ φ = pr₁` for the projections `Π_{U_i} → Gal(Ω/k)`. -/
def IsOverGk (ξ₁ : GeomPt Ω C₁) (ξ₂ : GeomPt Ω C₂) (φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)) : Prop :=
  (toGaloisGroup C₂.toSpec ξ₂.over).comp φ.toMonoidHom = toGaloisGroup C₁.toSpec ξ₁.over

/-- A **path** `γ : fiber y₁ ≅ fiber y₂` between two geometric points of `U₂` over `Spec Ω ⟶ Spec k`
**lies over the trivial path of `Spec k`**: after base change of finite étale `k`-schemes to `U₂`,
`γ` becomes the identity of the fibre functor of `Spec Ω ⟶ Spec k`. Two such paths differ by an
element of `Δ₂ = ker(Π_{U₂} → G_k)`. -/
def IsPathOverBase {y₁ y₂ : Spec (.of Ω) ⟶ C₂.U.toScheme}
    (hy₁ : y₁ ≫ C₂.toSpec = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hy₂ : y₂ ≫ C₂.toSpec = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (γ : fiber y₁ ≅ fiber y₂) : Prop :=
  Functor.isoWhiskerLeft (pullback C₂.toSpec) γ ≪≫ pullbackFiberIso C₂.toSpec hy₂ =
    pullbackFiberIso C₂.toSpec hy₁

omit [IsSepClosed Ω] [IsGalois k Ω] in
theorem comp_over_of_kHom (ξ₁ : GeomPt Ω C₁) {f : C₁.U.toScheme ⟶ C₂.U.toScheme}
    (hf : f ≫ C₂.toSpec = C₁.toSpec) :
    (ξ₁.x ≫ f) ≫ C₂.toSpec = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
  rw [Category.assoc, hf, ξ₁.over]

/-- `φ : Π_{U₁} → Π_{U₂}` is **induced by** the `k`-morphism `f : U₁ ⟶ U₂`, up to
`Δ₂`-conjugation: `φ = γ ∘ π₁ᵉᵗ(f) ∘ γ⁻¹`-conjugate for a path `γ : fiber (ξ₁ ≫ f) ≅ fiber ξ₂`
over the trivial path of `Spec k`. -/
def InducedByHom (ξ₁ : GeomPt Ω C₁) (ξ₂ : GeomPt Ω C₂) (f : C₁.U.toScheme ⟶ C₂.U.toScheme)
    (hf : f ≫ C₂.toSpec = C₁.toSpec) (φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)) : Prop :=
  ∃ γ : fiber (ξ₁.x ≫ f) ≅ fiber ξ₂.x, IsPathOverBase (comp_over_of_kHom ξ₁ hf) ξ₂.over γ ∧
    ∀ σ, φ σ = γ.conjAut (fundamentalGroupMap f rfl σ)

/-- `φ : Π_{U₁} ≃ Π_{U₂}` is **induced by** the `k`-isomorphism `f : U₁ ≅ U₂`, up to
`Δ₂`-conjugation. -/
def InducedBy (ξ₁ : GeomPt Ω C₁) (ξ₂ : GeomPt Ω C₂) (f : KIso C₁ C₂)
    (φ : π₁ᵉᵗ(ξ₁.x) ≃ₜ* π₁ᵉᵗ(ξ₂.x)) : Prop :=
  InducedByHom ξ₁ ξ₂ f.1.hom f.2 (φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x))

end Induced

/-! ### The whitelist statements -/

open HypCurve in
/-- **The rel-isom-DGC over `k`** ([AbsTopI] Definition 4.6 (ii), for hyperbolic curves over
`k`, full profinite `π₁`, `Σ` = all primes, envelope = identity, `ζ_k = id`): for hyperbolic
curves `U₁, U₂` over `k`, geometric points over an algebraic closure `Ω` of `k`, every continuous
isomorphism `Π_{U₁} ≃ Π_{U₂}` over `G_k` is induced (up to `Δ₂`-conjugation) by a **unique**
`k`-isomorphism `U₁ ≅ U₂`.

**Whitelist: [LocAn] Theorem A** (with [LocAn] Corollary 15.5 and Lemma 15.8; see the module
docstring). For sub-`p`-adic `k` this is a classical theorem of Mochizuki; it enters the
formalisation only as the explicit hypothesis `(hDGC : ∀ k, IsSubPAdic k → RelIsomDGC k)`. -/
def RelIsomDGC (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω],
    haveI := IsAlgClosure.isAlgClosed (R := k) (K := Ω)
    ∀ (C₁ C₂ : HypCurve k) (ξ₁ : GeomPt Ω C₁) (ξ₂ : GeomPt Ω C₂) (φ : π₁ᵉᵗ(ξ₁.x) ≃ₜ* π₁ᵉᵗ(ξ₂.x)),
    IsOverGk ξ₁ ξ₂ (φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)) → ∃! f : KIso C₁ C₂, InducedBy ξ₁ ξ₂ f φ

open HypCurve in
/-- **Existence half of the rel-isom-DGC over `k`**: every continuous isomorphism
`Π_{U₁} ≃ Π_{U₂}` over `G_k` is induced (up to `Δ₂`-conjugation) by some `k`-isomorphism
`U₁ ≅ U₂`. Together with `RelIsomDGC.Unique` it is equivalent to `RelIsomDGC`
(`relIsomDGC_iff_exists_and_unique`). For sub-`p`-adic `k` this is the hard half of [LocAn]
Theorem A (the MR7 track proves the two halves separately). -/
def RelIsomDGC.Exists (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω],
    haveI := IsAlgClosure.isAlgClosed (R := k) (K := Ω)
    ∀ (C₁ C₂ : HypCurve k) (ξ₁ : GeomPt Ω C₁) (ξ₂ : GeomPt Ω C₂) (φ : π₁ᵉᵗ(ξ₁.x) ≃ₜ* π₁ᵉᵗ(ξ₂.x)),
    IsOverGk ξ₁ ξ₂ (φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)) → ∃ f : KIso C₁ C₂, InducedBy ξ₁ ξ₂ f φ

open HypCurve in
/-- **Uniqueness half of the rel-isom-DGC over `k`**: two `k`-isomorphisms `U₁ ≅ U₂` inducing
(up to `Δ₂`-conjugation) the same continuous isomorphism `Π_{U₁} ≃ Π_{U₂}` over `G_k` are equal
([LocAn] Thm 14.1, injectivity paragraph, l.4019–4032). Together with `RelIsomDGC.Exists` it is
equivalent to `RelIsomDGC` (`relIsomDGC_iff_exists_and_unique`). -/
def RelIsomDGC.Unique (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω],
    haveI := IsAlgClosure.isAlgClosed (R := k) (K := Ω)
    ∀ (C₁ C₂ : HypCurve k) (ξ₁ : GeomPt Ω C₁) (ξ₂ : GeomPt Ω C₂) (φ : π₁ᵉᵗ(ξ₁.x) ≃ₜ* π₁ᵉᵗ(ξ₂.x)),
    IsOverGk ξ₁ ξ₂ (φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)) →
      ∀ f f' : KIso C₁ C₂, InducedBy ξ₁ ξ₂ f φ → InducedBy ξ₁ ξ₂ f' φ → f = f'

/-- **The rel-isom-DGC splits into existence and uniqueness**:
`RelIsomDGC k ↔ RelIsomDGC.Exists k ∧ RelIsomDGC.Unique k`. -/
theorem relIsomDGC_iff_exists_and_unique (k : Type u) [Field k] [CharZero k] :
    RelIsomDGC k ↔ RelIsomDGC.Exists k ∧ RelIsomDGC.Unique k := by
  refine ⟨fun h ↦ ⟨fun Ω _ _ _ C₁ C₂ ξ₁ ξ₂ φ hφ ↦ (h Ω C₁ C₂ ξ₁ ξ₂ φ hφ).exists,
    fun Ω _ _ _ C₁ C₂ ξ₁ ξ₂ φ hφ f f' hf hf' ↦ (h Ω C₁ C₂ ξ₁ ξ₂ φ hφ).unique hf hf'⟩,
    fun ⟨hE, hU⟩ Ω _ _ _ C₁ C₂ ξ₁ ξ₂ φ hφ ↦ ?_⟩
  obtain ⟨f, hf⟩ := hE Ω C₁ C₂ ξ₁ ξ₂ φ hφ
  exact ⟨f, hf, fun f' hf' ↦ hU Ω C₁ C₂ ξ₁ ξ₂ φ hφ f' f hf' hf⟩

/-- The rel-isom-DGC from its existence and uniqueness halves. -/
theorem RelIsomDGC.of_exists_of_unique {k : Type u} [Field k] [CharZero k]
    (hE : RelIsomDGC.Exists k) (hU : RelIsomDGC.Unique k) : RelIsomDGC k :=
  (relIsomDGC_iff_exists_and_unique k).2 ⟨hE, hU⟩

/-- The existence half of the rel-isom-DGC. -/
theorem RelIsomDGC.exists_half {k : Type u} [Field k] [CharZero k] (h : RelIsomDGC k) :
    RelIsomDGC.Exists k :=
  ((relIsomDGC_iff_exists_and_unique k).1 h).1

/-- The uniqueness half of the rel-isom-DGC. -/
theorem RelIsomDGC.unique_half {k : Type u} [Field k] [CharZero k] (h : RelIsomDGC k) :
    RelIsomDGC.Unique k :=
  ((relIsomDGC_iff_exists_and_unique k).1 h).2

open HypCurve in
/-- **The rel-hom-DGC over `k`** ([AbsTopI] Definition 4.6 (ii), homomorphism version): every
open continuous homomorphism `Π_{U₁} → Π_{U₂}` over `G_k` is induced (up to `Δ₂`-conjugation) by
a **unique** dominant `k`-morphism `U₁ ⟶ U₂`.

**Whitelist: [LocAn] Theorem A** (the statement of [LocAn] Thm A itself, for `X_K = U₁` a
hyperbolic curve). -/
def RelHomDGC (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω],
    haveI := IsAlgClosure.isAlgClosed (R := k) (K := Ω)
    ∀ (C₁ C₂ : HypCurve k) (ξ₁ : GeomPt Ω C₁) (ξ₂ : GeomPt Ω C₂) (φ : π₁ᵉᵗ(ξ₁.x) →ₜ* π₁ᵉᵗ(ξ₂.x)),
    IsOpen (Set.range φ) → IsOverGk ξ₁ ξ₂ φ →
      ∃! f : KHom C₁ C₂, InducedByHom ξ₁ ξ₂ f.1 f.2.2 φ

end Belyi.Anabelian
