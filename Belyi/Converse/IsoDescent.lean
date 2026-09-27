/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Converse.Basic
import Belyi.Converse.HomDescent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring

/-!
# From an isomorphism over `Ω` to an isomorphism over `K`

Step (S2) of `references/converse-rie-design.md`. Let `A` be a finitely generated domain over a
field `k`, with injective `k`-algebra maps `ι : A → Ω` into a field and `j : A → K` into an
algebraically closed field. If the base changes along `ι` of two finitely presented
`A ⊗[k] R`-algebras `B₁`, `B₂` are isomorphic (as `Ω ⊗[k] R`-algebras), then so are their base
changes along `j` (as `K ⊗[k] R`-algebras). (Finite generation of `A` over `k` is in fact not
needed.)

Proof: the isomorphism over `Ω` is defined over some finitely generated `A`-subalgebra `C ⊆ Ω`
(`Belyi.Converse.HomDescent.exists_algEquiv_of_fg`), and `C` admits an `A`-algebra map to `K`
(`Belyi.Converse.nonempty_algHom_of_fg`: `Frac A ⊗_A C` is a nonzero finitely generated
`Frac A`-algebra, and its residue fields at maximal ideals are finite over `Frac A`, hence embed
into `K`).

## Main results

* `Belyi.Converse.nonempty_algHom_of_fg`: a finitely generated `A`-subalgebra of a field `Ω ⊇ A`
  maps to any algebraically closed field `K ⊇ A` over `A`.
* `Belyi.Converse.IsBaseChangeAlong.exists_ringEquiv`: if `B'` is the base change of `B` along
  `φ : A → L` (in the sense of `IsBaseChangeAlong`), then `B' ≅ L ⊗[A] B`.
* `Belyi.Converse.nonempty_algEquiv_of_isBaseChangeAlong`: the main result described above.

Deviations from the target statement of the design: the hypothesis `[Algebra.FiniteType k A]` is
not needed and has been dropped, and the `IsBaseChangeAlong` hypotheses are written
`IsBaseChangeAlong (R := R) ι g₁` (the ring `R` cannot be inferred by unification otherwise).
-/

universe u

open TensorProduct

namespace Belyi.Converse

/-- A finitely generated `A`-subalgebra of a field `Ω` containing the domain `A` admits an
`A`-algebra map into any algebraically closed field `K` containing `A`. -/
theorem nonempty_algHom_of_fg {A Ω K : Type*} [CommRing A] [IsDomain A] [Field Ω] [Algebra A Ω]
    [FaithfulSMul A Ω] [Field K] [IsAlgClosed K] [Algebra A K] [FaithfulSMul A K]
    (C : Subalgebra A Ω) (hC : C.FG) : Nonempty (C →ₐ[A] K) := by
  letI := FractionRing.liftAlgebra A Ω
  letI := FractionRing.liftAlgebra A K
  obtain ⟨s, rfl⟩ := hC
  let D := Algebra.adjoin (FractionRing A) (s : Set Ω)
  haveI : Algebra.FiniteType (FractionRing A) D :=
    Algebra.FiniteType.adjoin_of_finite s.finite_toSet
  obtain ⟨m, hm⟩ := Ideal.exists_maximal D
  letI := Ideal.Quotient.field m
  haveI : Module.Finite (FractionRing A) (D ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing (FractionRing A) (D ⧸ m)
  haveI : Algebra.IsAlgebraic (FractionRing A) (D ⧸ m) := inferInstance
  haveI : Module.IsTorsionFree (FractionRing A) (D ⧸ m) := inferInstance
  haveI : Module.IsTorsionFree (FractionRing A) K := inferInstance
  let ψ : (D ⧸ m) →ₐ[FractionRing A] K := IsAlgClosed.lift
  let φ : D →ₐ[FractionRing A] K := ψ.comp (Ideal.Quotient.mkₐ _ m)
  haveI : IsScalarTower A (FractionRing A) K := FractionRing.isScalarTower_liftAlgebra A K
  haveI : IsScalarTower A (FractionRing A) Ω := FractionRing.isScalarTower_liftAlgebra A Ω
  have hle : Algebra.adjoin A (s : Set Ω) ≤ D.restrictScalars A := Algebra.adjoin_le fun x hx ↦
    (Subalgebra.mem_restrictScalars _).mpr (Algebra.subset_adjoin hx)
  exact ⟨((φ.restrictScalars A).comp (Subalgebra.inclusion hle) :)⟩

section Translation

variable {k : Type u} [CommRing k] {R : Type u} [CommRing R] [Algebra k R]
  {A : Type u} [CommRing A] [Algebra k A] {L : Type u} [CommRing L] [Algebra k L]
  {B : Type u} [CommRing B] [Algebra (A ⊗[k] R) B]
  {B' : Type u} [CommRing B'] [Algebra (L ⊗[k] R) B']

/-- The comparison map of a base change is compatible with the structure maps. -/
lemma IsBaseChangeAlong.map_algebraMap {φ : A →ₐ[k] L} {g : B →+* B'}
    (hg : IsBaseChangeAlong (R := R) φ g) (p : A ⊗[k] R) :
    g (algebraMap (A ⊗[k] R) B p) =
      algebraMap (L ⊗[k] R) B' (Algebra.TensorProduct.map φ (AlgHom.id k R) p) := by
  letI := tensorMapAlgebra R φ
  letI : Algebra B B' := g.toAlgebra
  letI : Algebra (A ⊗[k] R) B' := ((algebraMap B B').comp (algebraMap (A ⊗[k] R) B)).toAlgebra
  obtain ⟨h, -⟩ := hg
  exact IsScalarTower.algebraMap_apply (A ⊗[k] R) (L ⊗[k] R) B' p

/-- If `B'` is the base change of the `A ⊗[k] R`-algebra `B` along `φ : A → L`, then `B'` is
isomorphic to `L ⊗[A] B` (with `B` an `A`-algebra via `A → A ⊗[k] R`). -/
theorem IsBaseChangeAlong.exists_ringEquiv [Algebra A B] [IsScalarTower A (A ⊗[k] R) B]
    {φ : A →ₐ[k] L} {g : B →+* B'} (hg : IsBaseChangeAlong (R := R) φ g) :
    letI := φ.toRingHom.toAlgebra
    ∃ Θ : L ⊗[A] B ≃+* B', ∀ (l : L) (b : B),
      Θ (l ⊗ₜ b) = algebraMap (L ⊗[k] R) B' (l ⊗ₜ 1) * g b := by
  letI := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k A L := .of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  letI := tensorMapAlgebra R φ
  letI : Algebra B B' := g.toAlgebra
  letI : Algebra (A ⊗[k] R) B' := ((algebraMap B B').comp (algebraMap (A ⊗[k] R) B)).toAlgebra
  haveI : IsScalarTower (A ⊗[k] R) B B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨htower, hpush⟩ := hg
  letI : Algebra A B' := ((algebraMap (A ⊗[k] R) B').comp (algebraMap A (A ⊗[k] R))).toAlgebra
  letI : Algebra L B' := ((algebraMap (L ⊗[k] R) B').comp (algebraMap L (L ⊗[k] R))).toAlgebra
  have hAP : IsScalarTower A (A ⊗[k] R) (L ⊗[k] R) := .of_algebraMap_eq fun a ↦ by
    change φ a ⊗ₜ 1 = Algebra.TensorProduct.map φ (AlgHom.id k R) (a ⊗ₜ 1)
    simp
  haveI : IsScalarTower A (A ⊗[k] R) B' := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower A B B' := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A (A ⊗[k] R) B, ← IsScalarTower.algebraMap_apply]
    rfl
  haveI : IsScalarTower L (L ⊗[k] R) B' := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower A (L ⊗[k] R) B' := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A (A ⊗[k] R) B',
      IsScalarTower.algebraMap_apply A (A ⊗[k] R) (L ⊗[k] R),
      ← IsScalarTower.algebraMap_apply (A ⊗[k] R) (L ⊗[k] R) B']
  haveI : IsScalarTower A L B' := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A (L ⊗[k] R) B']
    rfl
  haveI : Algebra.IsPushout A L (A ⊗[k] R) (L ⊗[k] R) :=
    Algebra.IsPushout.tensorProduct_tensorProduct k R A L <| by
      ext r; simp [RingHom.algebraMap_toAlgebra]
  haveI : Algebra.IsPushout A (A ⊗[k] R) L (L ⊗[k] R) := Algebra.IsPushout.symm inferInstance
  have h₁ : Algebra.IsPushout A B L B' :=
    (Algebra.IsPushout.comp_iff A (A ⊗[k] R) L (L ⊗[k] R) (T := B) (T' := B')).mpr hpush.symm
  haveI := h₁.symm
  refine ⟨(Algebra.IsPushout.equiv A L B B').toRingEquiv, fun l b ↦ ?_⟩
  change Algebra.IsPushout.equiv A L B B' (l ⊗ₜ b) = _
  rw [Algebra.IsPushout.equiv_tmul]
  rfl

end Translation

/-- **Iso descent (S2)**: let `A` be a finitely generated domain over the field `k`, with injective
`k`-algebra maps `ι : A → Ω` into a field and `j : A → K` into an algebraically closed field. If
the base changes `BᵢΩ` along `ι` of two finitely presented `A ⊗[k] R`-algebras `B₁`, `B₂` are
isomorphic as `Ω ⊗[k] R`-algebras, then their base changes `BᵢK` along `j` are isomorphic as
`K ⊗[k] R`-algebras. -/
theorem nonempty_algEquiv_of_isBaseChangeAlong
    (k K Ω R A : Type u) [Field k] [Field K] [IsAlgClosed K] [Algebra k K]
    [Field Ω] [Algebra k Ω] [CommRing R] [Algebra k R]
    [CommRing A] [IsDomain A] [Algebra k A]
    (j : A →ₐ[k] K) (hj : Function.Injective j) (ι : A →ₐ[k] Ω) (hι : Function.Injective ι)
    (B₁ B₂ : Type u) [CommRing B₁] [Algebra (A ⊗[k] R) B₁]
    [Algebra.FinitePresentation (A ⊗[k] R) B₁]
    [CommRing B₂] [Algebra (A ⊗[k] R) B₂] [Algebra.FinitePresentation (A ⊗[k] R) B₂]
    (B₁Ω B₂Ω : Type u) [CommRing B₁Ω] [Algebra (Ω ⊗[k] R) B₁Ω] [CommRing B₂Ω]
    [Algebra (Ω ⊗[k] R) B₂Ω]
    (g₁ : B₁ →+* B₁Ω) (hg₁ : IsBaseChangeAlong (R := R) ι g₁) (g₂ : B₂ →+* B₂Ω)
    (hg₂ : IsBaseChangeAlong (R := R) ι g₂)
    (B₁K B₂K : Type u) [CommRing B₁K] [Algebra (K ⊗[k] R) B₁K] [CommRing B₂K]
    [Algebra (K ⊗[k] R) B₂K]
    (h₁ : B₁ →+* B₁K) (hh₁ : IsBaseChangeAlong (R := R) j h₁) (h₂ : B₂ →+* B₂K)
    (hh₂ : IsBaseChangeAlong (R := R) j h₂)
    (e : B₁Ω ≃ₐ[Ω ⊗[k] R] B₂Ω) : Nonempty (B₁K ≃ₐ[K ⊗[k] R] B₂K) := by
  letI : Algebra A B₁ := ((algebraMap (A ⊗[k] R) B₁).comp (algebraMap A (A ⊗[k] R))).toAlgebra
  haveI : IsScalarTower A (A ⊗[k] R) B₁ := .of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra A B₂ := ((algebraMap (A ⊗[k] R) B₂).comp (algebraMap A (A ⊗[k] R))).toAlgebra
  haveI : IsScalarTower A (A ⊗[k] R) B₂ := .of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨Θ₁, hΘ₁⟩ := hg₁.exists_ringEquiv
  obtain ⟨Θ₂, hΘ₂⟩ := hg₂.exists_ringEquiv
  obtain ⟨Ψ₁, hΨ₁⟩ := hh₁.exists_ringEquiv
  obtain ⟨Ψ₂, hΨ₂⟩ := hh₂.exists_ringEquiv
  letI : Algebra A Ω := ι.toRingHom.toAlgebra
  letI : Algebra A K := j.toRingHom.toAlgebra
  haveI : FaithfulSMul A Ω := (faithfulSMul_iff_algebraMap_injective A Ω).mpr hι
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr hj
  -- the isomorphism over `Ω`, in the form `Ω ⊗[A] B₁ ≃ Ω ⊗[A] B₂`
  let eΩ₀ : Ω ⊗[A] B₁ ≃+* Ω ⊗[A] B₂ := (Θ₁.trans e.toRingEquiv).trans Θ₂.symm
  have hΘ₂' : ∀ ω : Ω, Θ₂.symm (algebraMap (Ω ⊗[k] R) B₂Ω (ω ⊗ₜ 1)) = ω ⊗ₜ 1 := fun ω ↦ by
    rw [RingEquiv.symm_apply_eq, hΘ₂, map_one, mul_one]
  let eΩ : Ω ⊗[A] B₁ ≃ₐ[Ω] Ω ⊗[A] B₂ := AlgEquiv.ofRingEquiv (f := eΩ₀) fun ω ↦ by
    simp only [eΩ₀, RingEquiv.trans_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, hΘ₁, map_one, mul_one]
    erw [e.commutes]
    exact hΘ₂' ω
  have heΩ : ∀ p : A ⊗[k] R,
      eΩ (1 ⊗ₜ algebraMap (A ⊗[k] R) B₁ p) = 1 ⊗ₜ algebraMap (A ⊗[k] R) B₂ p := fun p ↦ by
    change Θ₂.symm (e (Θ₁ _)) = _
    rw [RingEquiv.symm_apply_eq, hΘ₁, hΘ₂, hg₁.map_algebraMap, hg₂.map_algebraMap]
    simp only [← Algebra.TensorProduct.one_def, map_one, one_mul]
    exact e.commutes _
  obtain ⟨eK, heK⟩ := HomDescent.exists_algEquiv_of_fg (K := K)
    (fun C hC ↦ nonempty_algHom_of_fg C hC) eΩ heΩ
  -- back to `B₁K ≃ B₂K`
  let E : B₁K ≃+* B₂K := (Ψ₁.symm.trans eK.toRingEquiv).trans Ψ₂
  refine ⟨AlgEquiv.ofRingEquiv (f := E) fun x ↦ ?_⟩
  induction x with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  | tmul l r =>
    have key₁ : algebraMap (K ⊗[k] R) B₁K (l ⊗ₜ r) =
        Ψ₁ (l ⊗ₜ algebraMap (A ⊗[k] R) B₁ (1 ⊗ₜ r)) := by
      rw [hΨ₁, hh₁.map_algebraMap, ← map_mul]; simp
    have key₂ : algebraMap (K ⊗[k] R) B₂K (l ⊗ₜ r) =
        Ψ₂ (l ⊗ₜ algebraMap (A ⊗[k] R) B₂ (1 ⊗ₜ r)) := by
      rw [hΨ₂, hh₂.map_algebraMap, ← map_mul]; simp
    have hl : (l ⊗ₜ[A] algebraMap (A ⊗[k] R) B₁ (1 ⊗ₜ r) : K ⊗[A] B₁) =
        algebraMap K _ l * (1 ⊗ₜ algebraMap (A ⊗[k] R) B₁ (1 ⊗ₜ r)) := by simp
    change Ψ₂ (eK (Ψ₁.symm _)) = _
    rw [key₁, key₂, RingEquiv.symm_apply_apply, hl, map_mul, AlgEquiv.commutes, heK]
    simp

end Belyi.Converse
