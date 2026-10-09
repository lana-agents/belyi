/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Smooth.Field

/-!
# The cotangent space of a formally smooth local algebra

Taxis issue #75: the local-algebra input to B1. For a local `k`-algebra `A` with residue
field `κ`, the conormal (second fundamental) exact sequence reads

`𝔪/𝔪² → κ ⊗[A] Ω[A⁄k] → Ω[κ⁄k] → 0`,

and the first map is *injective* as soon as both `A` and `κ` are formally smooth over
`k` — by the Jacobian criterion `Algebra.FormallySmooth.iff_split_injection` applied to
the surjection `A ↠ κ`, whose kernel is the maximal ideal. Consequently

`dim_κ 𝔪/𝔪² ≤ dim_κ (κ ⊗[A] Ω[A⁄k])`.

Both hypotheses are available in the geometric situation: `A = 𝒪_{X,x}` is formally
smooth over `k` exactly when `x` lies in mathlib's `Scheme.Hom.smoothLocus` (which is how
`Belyi/Ramification.lean` defines the unramified locus), and `κ` is formally smooth over
`k` whenever the residue extension is separable — automatic in characteristic zero, and
in general over a perfect field.

Combined with `Belyi/Curve/Stalks.lean` (which turns a cotangent bound of `1` into
`ValuationRing` and `Ring.KrullDimLE 1`), this reduces issue #75 to computing the rank of
`Ω` at a stalk of a morphism smooth of relative dimension `1`.

## Main results

* `Belyi.injective_cotangentSpaceToTensor`: injectivity of `𝔪/𝔪² → κ ⊗[A] Ω[A⁄k]`.
* `Belyi.finrank_cotangentSpace_le`: the resulting bound on `dim_κ 𝔪/𝔪²`.
* `Belyi.finrank_cotangentSpace_le_of_finrank_kaehler_le`: the form consumed by
  `Belyi/Curve/Stalks.lean`, with the bound stated for `κ ⊗[A] Ω[A⁄k]`.
-/

universe u v

namespace Belyi

open IsLocalRing Module TensorProduct KaehlerDifferential

variable (k : Type u) [Field k] (A : Type v) [CommRing A] [IsLocalRing A] [Algebra k A]

section Conormal

/-- The kernel of the residue map is the maximal ideal, as an algebra map to the residue
field. -/
lemma ker_algebraMap_residueField :
    RingHom.ker (algebraMap A (ResidueField A)) = maximalIdeal A :=
  ker_residue

/-- The conormal map `𝔪/𝔪² → κ ⊗[A] Ω[A⁄k]` of the surjection `A ↠ κ`, transported to
the cotangent space of the local ring `A` (mathlib's `IsLocalRing.CotangentSpace` is by
definition `(maximalIdeal A).Cotangent`). -/
noncomputable def cotangentSpaceToTensor :
    CotangentSpace A →ₗ[A] ResidueField A ⊗[A] Ω[A⁄k] :=
  (kerCotangentToTensor k A (ResidueField A)).restrictScalars A ∘ₗ
    Ideal.mapCotangent (maximalIdeal A) (RingHom.ker (algebraMap A (ResidueField A)))
      (AlgHom.id A A) (le_of_eq (ker_algebraMap_residueField A).symm)

variable {k A}

/-- **Injectivity in the conormal sequence.** If both `A` and its residue field are
formally smooth over `k`, the conormal map `𝔪/𝔪² → κ ⊗[A] Ω[A⁄k]` is injective.

`Algebra.FormallySmooth k A` is exactly what membership in the smooth locus of
`Spec A ⟶ Spec k` provides, and `Algebra.FormallySmooth k (ResidueField A)` holds
whenever the residue extension is separable (e.g. in characteristic zero). -/
theorem injective_kerCotangentToTensor [Algebra.FormallySmooth k A]
    [Algebra.FormallySmooth k (ResidueField A)] :
    Function.Injective (kerCotangentToTensor k A (ResidueField A)) := by
  obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection
    (R := k) (P := A) (A := ResidueField A) residue_surjective).mp inferInstance
  intro x y hxy
  have h := congrArg (fun m : _ →ₗ[A] _ => m x) hl
  have h' := congrArg (fun m : _ →ₗ[A] _ => m y) hl
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at h h'
  rw [← h, ← h', hxy]

omit [IsLocalRing A] in
/-- The transport map `𝔪/𝔪² → (ker (A → κ))/(…)²` induced by the identity is
injective (the two ideals are equal). -/
lemma injective_mapCotangent_id {I J : Ideal A} (h₁ : I ≤ J.comap (AlgHom.id A A))
    (h₂ : J ≤ I.comap (AlgHom.id A A)) :
    Function.Injective (Ideal.mapCotangent I J (AlgHom.id A A) h₁) := by
  refine Function.LeftInverse.injective
    (g := Ideal.mapCotangent J I (AlgHom.id A A) h₂) fun x => ?_
  obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective I x
  rw [Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent]
  rfl

/-- **The conormal map out of the cotangent space is injective** for a formally smooth
local `k`-algebra with formally smooth residue field. -/
theorem injective_cotangentSpaceToTensor [Algebra.FormallySmooth k A]
    [Algebra.FormallySmooth k (ResidueField A)] :
    Function.Injective (cotangentSpaceToTensor k A) := by
  have h1 := injective_kerCotangentToTensor (k := k) (A := A)
  have h2 := injective_mapCotangent_id (A := A)
    (I := maximalIdeal A) (J := RingHom.ker (algebraMap A (ResidueField A)))
    (le_of_eq (ker_algebraMap_residueField A).symm)
    (le_of_eq (ker_algebraMap_residueField A))
  exact h1.comp h2

end Conormal

section Finrank

variable {k A}

/-- The conormal map as a `κ`-linear map: both sides are modules over the residue
field, and the map is `A`-linear, so it extends along the surjection `A ↠ κ`. -/
noncomputable def cotangentSpaceToTensorₖ :
    CotangentSpace A →ₗ[ResidueField A] ResidueField A ⊗[A] Ω[A⁄k] :=
  LinearMap.extendScalarsOfSurjective residue_surjective (cotangentSpaceToTensor k A)

lemma injective_cotangentSpaceToTensorₖ [Algebra.FormallySmooth k A]
    [Algebra.FormallySmooth k (ResidueField A)] :
    Function.Injective (cotangentSpaceToTensorₖ (k := k) (A := A)) :=
  injective_cotangentSpaceToTensor

/-- **The cotangent bound.** For a formally smooth local `k`-algebra whose residue field
is formally smooth over `k` (e.g. in characteristic zero), the dimension of the cotangent
space `𝔪/𝔪²` is at most the dimension of `κ ⊗[A] Ω[A⁄k]`.

This is the local-algebra half of taxis issue #75: together with
`Belyi/Curve/Stalks.lean` it turns the rank of the module of Kähler differentials at a
stalk — i.e. the relative dimension of a smooth morphism — into the `ValuationRing` and
`Ring.KrullDimLE 1` hypotheses of B1. -/
theorem finrank_cotangentSpace_le [Algebra.FormallySmooth k A]
    [Algebra.FormallySmooth k (ResidueField A)]
    [Module.Finite (ResidueField A) (ResidueField A ⊗[A] Ω[A⁄k])] :
    finrank (ResidueField A) (CotangentSpace A) ≤
      finrank (ResidueField A) (ResidueField A ⊗[A] Ω[A⁄k]) :=
  LinearMap.finrank_le_finrank_of_injective injective_cotangentSpaceToTensorₖ

/-- The form consumed by `Belyi/Curve/Stalks.lean`: a rank bound on the Kähler
differentials gives the cotangent bound. -/
theorem finrank_cotangentSpace_le_of_finrank_kaehler_le [Algebra.FormallySmooth k A]
    [Algebra.FormallySmooth k (ResidueField A)]
    [Module.Finite (ResidueField A) (ResidueField A ⊗[A] Ω[A⁄k])] {n : ℕ}
    (h : finrank (ResidueField A) (ResidueField A ⊗[A] Ω[A⁄k]) ≤ n) :
    finrank (ResidueField A) (CotangentSpace A) ≤ n :=
  finrank_cotangentSpace_le.trans h

/-- Over a perfect base field (in particular in characteristic zero) the hypothesis on
the residue field is automatic, as soon as it is essentially of finite type over `k` —
which holds for stalks of schemes locally of finite type. -/
theorem finrank_cotangentSpace_le_of_perfectField [PerfectField k]
    [Algebra.FormallySmooth k A] [Algebra.EssFiniteType k (ResidueField A)]
    [Module.Finite (ResidueField A) (ResidueField A ⊗[A] Ω[A⁄k])] :
    finrank (ResidueField A) (CotangentSpace A) ≤
      finrank (ResidueField A) (ResidueField A ⊗[A] Ω[A⁄k]) :=
  finrank_cotangentSpace_le

end Finrank

end Belyi
