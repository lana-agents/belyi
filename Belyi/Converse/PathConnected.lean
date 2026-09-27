/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Oka.Analytification.RET.Connected
import Oka.Analytification.RET.ES.SmoothLocus

/-!
# Analytifications of smooth connected schemes are path connected (S3a)

Step (S3a) of the converse direction of Belyi's theorem (`references/converse-rie-design.md`):
for `k` algebraically closed, `k → ℂ` and `A` a finitely generated smooth `k`-algebra which is a
domain, the analytification of `T = Spec (ℂ ⊗[k] A)` is path connected, so that any two
`ℂ`-points of `T` can be joined by a path in `T^an`.

## Main results

* `Belyi.Converse.locallyPathConnectedSpace_analytification`: the analytification of a scheme
  smooth over `ℂ` is locally path connected. A smooth scheme is locally étale over affine spaces
  (oka `SchemeLFTℂ.isLocallyEtaleOverAffineSpace_of_smooth`), so its analytification is locally
  isomorphic to opens of `ℂⁿ` (oka `isLocallyOpenInAffine_analytification`); a space jointly
  covered by local homeomorphisms out of locally path connected spaces is locally path connected
  (`Belyi.Converse.locallyPathConnectedSpace_of_isLocalHomeomorph`).
* `Belyi.Converse.pathConnectedSpace_analytification`: if moreover the scheme is connected, its
  analytification is path connected (oka `connectedSpace_analytification`).
* `Belyi.Converse.isDomain_tensorProduct_of_isAlgClosed`: over an algebraically closed field,
  the tensor product of a finitely generated domain with any domain is a domain.
* `Belyi.Converse.pathConnectedSpace_analytification_baseChangeSpec`: the special case
  `T = Spec (ℂ ⊗[k] A)` (`Belyi.Converse.baseChangeSpec k A`) needed by the converse.
-/

universe u

open CategoryTheory AlgebraicGeometry Topology TensorProduct

namespace Belyi.Converse

/-- A space which is jointly covered by local homeomorphisms out of locally path connected
spaces is locally path connected. -/
theorem locallyPathConnectedSpace_of_isLocalHomeomorph {X : Type*} [TopologicalSpace X]
    {ι : Type*} {S : ι → Type*} [∀ i, TopologicalSpace (S i)]
    [∀ i, LocallyPathConnectedSpace (S i)] (f : ∀ i, S i → X)
    (hf : ∀ i, IsLocalHomeomorph (f i)) (hsurj : ∀ x, ∃ i s, f i s = x) :
    LocallyPathConnectedSpace X := by
  let F : (Σ i, S i) → X := fun p ↦ f p.1 p.2
  have hF : IsQuotientMap F :=
    IsOpenMap.isQuotientMap (isOpenMap_sigma.2 fun i ↦ (hf i).isOpenMap)
      (continuous_sigma fun i ↦ (hf i).continuous)
      (fun x ↦ let ⟨i, s, hs⟩ := hsurj x; ⟨⟨i, s⟩, hs⟩)
  exact hF.locallyPathConnectedSpace

open ComplexAnalytic in
/-- A complex analytic space locally isomorphic to opens of affine spaces is locally path
connected. -/
theorem locallyPathConnectedSpace_of_isLocallyOpenInAffine {Y : AnalyticSpace.{u}}
    (hY : AnalyticSpace.IsLocallyOpenInAffine Y) : LocallyPathConnectedSpace Y := by
  choose n U φ z hφ hz using hY
  haveI (y : Y) : LocallyPathConnectedSpace (AnalyticSpace.complexAffineSpace.{u} (n y)) :=
    inferInstanceAs (LocallyPathConnectedSpace (ULift.{u} (Fin (n y)) → ℂ))
  haveI (y : Y) : LocallyPathConnectedSpace
      ((AnalyticSpace.complexAffineSpace.{u} (n y)).restrict (U y)) :=
    (U y).2.locallyPathConnectedSpace
  exact locallyPathConnectedSpace_of_isLocalHomeomorph (fun y ↦ (φ y).toLRSHom.base)
    (fun y ↦ (hφ y).isLocalHomeomorph) fun y ↦ ⟨y, z y, hz y⟩

/-! ### Tensor products of domains over an algebraically closed field -/

section TensorDomain

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]

/-- **Nullstellensatz, weak form.** A nonzero element of a finitely generated domain over an
algebraically closed field `k` does not vanish at some `k`-point. -/
theorem exists_algHom_apply_ne_zero [IsAlgClosed k] [IsDomain A] [Algebra.FiniteType k A]
    {f : A} (hf : f ≠ 0) : ∃ χ : A →ₐ[k] k, χ f ≠ 0 := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hbot : (⊥ : Ideal A).jacobson = ⊥ :=
    isJacobsonRing_iff_prime_eq.1 ‹_› ⊥ Ideal.isPrime_bot
  have hfJ : f ∉ (⊥ : Ideal A).jacobson := by
    rw [hbot, Ideal.mem_bot]
    exact hf
  obtain ⟨m, ⟨-, hm⟩, hfm⟩ : ∃ m : Ideal A, (⊥ ≤ m ∧ m.IsMaximal) ∧ f ∉ m := by
    simpa [Ideal.jacobson, Ideal.mem_sInf] using hfJ
  letI := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m)
      (Ideal.Quotient.mkₐ_surjective k m)
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  let e : k ≃ₐ[k] A ⧸ m :=
    AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  simpa [Ideal.Quotient.eq_zero_iff_mem] using hfm

variable {B : Type*} [CommRing B] [Algebra k B]

/-- Evaluation `A ⊗[k] B → B` of the first tensor factor at a `k`-point `χ` of `A`. -/
noncomputable def evalLeft (χ : A →ₐ[k] k) : A ⊗[k] B →ₐ[k] B :=
  Algebra.TensorProduct.lift ((Algebra.ofId k B).comp χ) (AlgHom.id k B)
    fun _ _ ↦ Commute.all _ _

/-- If `x ∈ A ⊗[k] B` evaluates to zero at `χ`, then so do all its coordinates with respect to a
basis of `B`. -/
theorem apply_repr_eq_zero_of_evalLeft_eq_zero {κ : Type*} (b : Module.Basis κ k B)
    (χ : A →ₐ[k] k) {x : A ⊗[k] B} (hx : evalLeft χ x = 0) (j : κ) :
    χ ((Algebra.TensorProduct.basis A b).repr x j) = 0 := by
  set c := (Algebra.TensorProduct.basis A b).repr x
  have hsum : evalLeft χ x = ∑ i ∈ c.support, χ (c i) • b i := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis A b).linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.TensorProduct.basis_repr_symm_apply', evalLeft,
      Algebra.TensorProduct.lift_tmul]
    simp [c, Algebra.smul_def]
  by_cases hj : j ∈ c.support
  · rw [hsum] at hx
    exact linearIndependent_iff'.1 b.linearIndependent c.support (fun i ↦ χ (c i)) hx j hj
  · rw [Finsupp.notMem_support_iff.1 hj, map_zero]

/-- **The tensor product of domains over an algebraically closed field is a domain**, provided one
of the factors is finitely generated. -/
theorem isDomain_tensorProduct_of_isAlgClosed [IsAlgClosed k] [IsDomain A]
    [Algebra.FiniteType k A] [IsDomain B] : IsDomain (A ⊗[k] B) := by
  haveI : Nontrivial (A ⊗[k] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k A B
      (algebraMap k A).injective (algebraMap k B).injective
  let b := Module.Free.chooseBasis k B
  let e := Algebra.TensorProduct.basis A b
  haveI : NoZeroDivisors (A ⊗[k] B) := by
    refine ⟨fun {x y} hxy ↦ ?_⟩
    by_contra! h
    obtain ⟨i, hi⟩ : ∃ i, e.repr x i ≠ 0 := by
      by_contra! H
      exact h.1 (e.repr.injective (Finsupp.ext fun i ↦ by simpa using H i))
    obtain ⟨j, hj⟩ : ∃ j, e.repr y j ≠ 0 := by
      by_contra! H
      exact h.2 (e.repr.injective (Finsupp.ext fun j ↦ by simpa using H j))
    obtain ⟨χ, hχ⟩ := exists_algHom_apply_ne_zero (k := k) (mul_ne_zero hi hj)
    have : evalLeft χ x * evalLeft χ y = 0 := by rw [← map_mul, hxy, map_zero]
    rw [map_mul] at hχ
    rcases mul_eq_zero.1 this with h0 | h0
    · exact left_ne_zero_of_mul hχ (apply_repr_eq_zero_of_evalLeft_eq_zero b χ h0 i)
    · exact right_ne_zero_of_mul hχ (apply_repr_eq_zero_of_evalLeft_eq_zero b χ h0 j)
  exact NoZeroDivisors.to_isDomain _

end TensorDomain

/-! ### Analytifications of smooth schemes -/

section Analytification

open ComplexAnalytic

/-- **The analytification of a scheme smooth over `ℂ` is locally path connected.** -/
theorem locallyPathConnectedSpace_analytification (X : SchemeLFTℂ.{u}) [Smooth X.obj.hom] :
    LocallyPathConnectedSpace (analytification.obj X) :=
  locallyPathConnectedSpace_of_isLocallyOpenInAffine
    (isLocallyOpenInAffine_analytification (SchemeLFTℂ.isLocallyEtaleOverAffineSpace_of_smooth X))

/-- **The analytification of a connected scheme smooth over `ℂ` is path connected.** -/
theorem pathConnectedSpace_analytification (X : SchemeLFTℂ.{u}) [Smooth X.obj.hom]
    [ConnectedSpace X.obj.left] : PathConnectedSpace (analytification.obj X) :=
  haveI := locallyPathConnectedSpace_analytification X
  haveI := connectedSpace_analytification X
  PathConnectedSpace.of_locallyPathConnectedSpace

variable (k : Type u) [Field k] [Algebra k (ULift.{u} ℂ)] (A : Type u) [CommRing A] [Algebra k A]

/-- The structure map `ℂ → ℂ ⊗[k] A`, for a finitely generated `k`-algebra `A`, is of finite
type. -/
theorem finiteType_algebraMap_uliftComplex_tensor [Algebra.FiniteType k A] :
    (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) (ULift.{u} ℂ ⊗[k] A))).hom.FiniteType :=
  RingHom.finiteType_algebraMap.2 inferInstance

/-- The base change `Spec (ℂ ⊗[k] A)` of `Spec A` along `k → ℂ`, for a finitely generated
`k`-algebra `A`, as a scheme locally of finite type over `ℂ`. -/
noncomputable abbrev baseChangeSpec [Algebra.FiniteType k A] : SchemeLFTℂ.{u} :=
  SchemeLFTℂ.spec (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) (ULift.{u} ℂ ⊗[k] A)))
    (finiteType_algebraMap_uliftComplex_tensor k A)

instance smooth_baseChangeSpec [Algebra.FiniteType k A] [Algebra.Smooth k A] :
    Smooth (baseChangeSpec k A).obj.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) (ULift.{u} ℂ ⊗[k] A))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.2 inferInstance

theorem connectedSpace_baseChangeSpec [IsAlgClosed k] [IsDomain A] [Algebra.FiniteType k A] :
    ConnectedSpace (baseChangeSpec k A).obj.left := by
  haveI : IsDomain (A ⊗[k] ULift.{u} ℂ) := isDomain_tensorProduct_of_isAlgClosed
  haveI : IsDomain (ULift.{u} ℂ ⊗[k] A) :=
    (Algebra.TensorProduct.comm k (ULift.{u} ℂ) A).toMulEquiv.isDomain
  change ConnectedSpace (Spec (CommRingCat.of (ULift.{u} ℂ ⊗[k] A)))
  infer_instance

/-- **The analytification of `Spec (ℂ ⊗[k] A)` is path connected**, for `k` algebraically closed
and `A` a finitely generated smooth `k`-algebra which is a domain. -/
theorem pathConnectedSpace_analytification_baseChangeSpec [IsAlgClosed k] [IsDomain A]
    [Algebra.FiniteType k A] [Algebra.Smooth k A] :
    PathConnectedSpace (analytification.obj (baseChangeSpec k A)) :=
  haveI := connectedSpace_baseChangeSpec k A
  pathConnectedSpace_analytification _

end Analytification

end Belyi.Converse
