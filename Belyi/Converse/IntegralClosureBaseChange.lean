/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Integral closure commutes with base change along a field extension over a perfect field

Ring-theoretic input for package P2b of `references/converse-rie-design.md`.

Let `k` be a perfect field (e.g. of characteristic zero), `K / k` a field extension, `R` a
`k`-algebra and `B` an `R`-algebra. We show that the comparison map
`TensorProduct.toIntegralClosure R (R ⊗[k] K) B :
  (R ⊗[k] K) ⊗[R] integralClosure R B → integralClosure (R ⊗[k] K) ((R ⊗[k] K) ⊗[R] B)`
is bijective (`Belyi.toIntegralClosure_tensorProduct_bijective`), and more generally that
`TensorProduct.toIntegralClosure R S B` is bijective whenever `S` is the base change of `K` along
`k → R` in the sense of `Algebra.IsPushout k K R S`
(`Belyi.toIntegralClosure_bijective_of_isPushout`).

Proof: injectivity is flatness. For surjectivity, `K` is the filtered union of the images of
smooth finitely generated `k`-algebras `A ↪ K` (generic smoothness: a finitely generated
`k`-subalgebra `A₀ ⊆ K` is a domain whose fraction field is formally smooth over the perfect
field `k`, so some localization `A₀[1/a]`, `a ≠ 0`, is smooth; this is
`Belyi.exists_smooth_algHom_injective`). An integral element of `(R ⊗[k] K) ⊗[R] B` together with
a monic equation involves only finitely many elements of `K`, so it comes from an integral
element of `(R ⊗[k] A) ⊗[R] B` for such a smooth `A` (the transition map is injective since
`B` is flat over the field `k`), where mathlib's smooth case
`TensorProduct.toIntegralClosure_bijective_of_smooth` applies.
-/

universe u

open TensorProduct

namespace Belyi

section Approximation

variable (k : Type*) [Field k] [PerfectField k] {K : Type u} [Field K] [Algebra k K]

/-- **Smooth approximation.** Over a perfect field `k`, every finite subset of a field
extension `K` lies in the image of an injective `k`-algebra map `A → K` from a smooth
`k`-algebra `A`. -/
theorem exists_smooth_algHom_injective (F : Finset K) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra k A), Algebra.Smooth k A ∧
      ∃ ι : A →ₐ[k] K, Function.Injective ι ∧ (F : Set K) ⊆ Set.range ι := by
  let A₀ := Algebra.adjoin k (F : Set K)
  haveI : Algebra.FiniteType k A₀ :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset F)
  haveI : Algebra.FinitePresentation k A₀ := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have hfr : IsFractionRing A₀ (Localization.AtPrime (⊥ : Ideal A₀)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal A₀).primeCompl)
  letI : Field (Localization.AtPrime (⊥ : Ideal A₀)) := IsFractionRing.toField A₀
  haveI : Algebra.IsSmoothAt k (⊥ : Ideal A₀) := Algebra.FormallySmooth.of_perfectField
  obtain ⟨a, ha, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth k (⊥ : Ideal A₀)
  have ha0 : (a : K) ≠ 0 := fun h ↦ ha (Ideal.mem_bot.mpr (Subtype.ext h))
  have hunit : ∀ y : Submonoid.powers a, IsUnit (A₀.val y) := by
    rintro ⟨_, n, rfl⟩
    simpa using (pow_ne_zero n ha0).isUnit
  refine ⟨Localization.Away a, inferInstance, inferInstance, hsm,
    IsLocalization.liftAlgHom (M := Submonoid.powers a) hunit, ?_, ?_⟩
  · rw [IsLocalization.coe_liftAlgHom, IsLocalization.lift_injective_iff]
    intro x y
    have hinj : Function.Injective (algebraMap A₀ (Localization.Away a)) :=
      IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors
        (by simpa using ha))
    exact ⟨fun h ↦ by rw [hinj h], fun h ↦ by rw [Subtype.val_injective h]⟩
  · intro c hc
    refine ⟨algebraMap A₀ _ ⟨c, Algebra.subset_adjoin hc⟩, ?_⟩
    rw [IsLocalization.coe_liftAlgHom, IsLocalization.lift_eq]
    rfl

end Approximation

section Lifting

variable {k : Type*} [Field k] (R : Type*) [CommRing R] [Algebra k R]
  (B : Type*) [CommRing B] [Algebra R B] [Algebra k B] [IsScalarTower k R B]
  {K : Type u} [CommRing K] [Algebra k K]

/-- The transition map `R ⊗[k] A → R ⊗[k] K` induced by `ι : A →ₐ[k] K`. -/
noncomputable abbrev tensorMapLeft {A : Type*} [CommRing A] [Algebra k A] (ι : A →ₐ[k] K) :
    R ⊗[k] A →ₐ[R] R ⊗[k] K :=
  Algebra.TensorProduct.map (AlgHom.id R R) ι

/-- The transition map `(R ⊗[k] A) ⊗[R] B → (R ⊗[k] K) ⊗[R] B` induced by `ι : A →ₐ[k] K`. -/
noncomputable abbrev tensorMapLeftTensor {A : Type*} [CommRing A] [Algebra k A]
    (ι : A →ₐ[k] K) : (R ⊗[k] A) ⊗[R] B →ₐ[R] (R ⊗[k] K) ⊗[R] B :=
  Algebra.TensorProduct.map (tensorMapLeft R ι) (AlgHom.id R B)

omit [Algebra k B] [IsScalarTower k R B] in
/-- Every element of `R ⊗[k] K` comes from `R ⊗[k] A` for any `ι : A → K` whose image contains a
suitable finite set. -/
theorem exists_finset_mem_range_tensorMapLeft (s : R ⊗[k] K) :
    ∃ F : Finset K, ∀ (A : Type u) [CommRing A] [Algebra k A] (ι : A →ₐ[k] K),
      (F : Set K) ⊆ Set.range ι → s ∈ Set.range (tensorMapLeft R ι) := by
  classical
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun A _ _ ι _ ↦ ⟨0, map_zero _⟩⟩
  | tmul r c =>
    refine ⟨{c}, fun A _ _ ι h ↦ ?_⟩
    obtain ⟨a, ha⟩ := h (Finset.mem_coe.mpr (Finset.mem_singleton_self c))
    exact ⟨r ⊗ₜ a, by simp [ha]⟩
  | add x y hx hy =>
    obtain ⟨F₁, h₁⟩ := hx
    obtain ⟨F₂, h₂⟩ := hy
    refine ⟨F₁ ∪ F₂, fun A _ _ ι h ↦ ?_⟩
    obtain ⟨x', rfl⟩ := h₁ A ι (by grw [← h]; simp)
    obtain ⟨y', rfl⟩ := h₂ A ι (by grw [← h]; simp)
    exact ⟨x' + y', map_add _ _ _⟩

omit [Algebra k B] [IsScalarTower k R B] in
/-- Every element of `(R ⊗[k] K) ⊗[R] B` comes from `(R ⊗[k] A) ⊗[R] B` for any `ι : A → K`
whose image contains a suitable finite set. -/
theorem exists_finset_mem_range_tensorMapLeftTensor (z : (R ⊗[k] K) ⊗[R] B) :
    ∃ F : Finset K, ∀ (A : Type u) [CommRing A] [Algebra k A] (ι : A →ₐ[k] K),
      (F : Set K) ⊆ Set.range ι → z ∈ Set.range (tensorMapLeftTensor R B ι) := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨∅, fun A _ _ ι _ ↦ ⟨0, map_zero _⟩⟩
  | tmul s b =>
    obtain ⟨F, hF⟩ := exists_finset_mem_range_tensorMapLeft R s
    refine ⟨F, fun A _ _ ι h ↦ ?_⟩
    obtain ⟨s', rfl⟩ := hF A ι h
    exact ⟨s' ⊗ₜ b, by simp⟩
  | add x y hx hy =>
    obtain ⟨F₁, h₁⟩ := hx
    obtain ⟨F₂, h₂⟩ := hy
    refine ⟨F₁ ∪ F₂, fun A _ _ ι h ↦ ?_⟩
    obtain ⟨x', rfl⟩ := h₁ A ι (by grw [← h]; simp)
    obtain ⟨y', rfl⟩ := h₂ A ι (by grw [← h]; simp)
    exact ⟨x' + y', map_add _ _ _⟩

/-- `(R ⊗[k] A) ⊗[R] B ≃ B ⊗[k] A`. -/
noncomputable def tensorTensorEquiv (A : Type*) [CommRing A] [Algebra k A] :
    (R ⊗[k] A) ⊗[R] B ≃ₐ[R] B ⊗[k] A :=
  (Algebra.TensorProduct.comm R (R ⊗[k] A) B).trans
    (Algebra.TensorProduct.cancelBaseChange k R R B A)

theorem tensorTensorEquiv_comp_tensorMapLeftTensor {A : Type*} [CommRing A] [Algebra k A]
    (ι : A →ₐ[k] K) :
    (tensorTensorEquiv (k := k) R B K).toAlgHom.comp (tensorMapLeftTensor R B ι) =
      (Algebra.TensorProduct.map (AlgHom.id R B) ι).comp
        (tensorTensorEquiv (k := k) R B A).toAlgHom := by
  ext <;> simp [tensorTensorEquiv, Algebra.TensorProduct.one_def]

/-- The transition map `(R ⊗[k] A) ⊗[R] B → (R ⊗[k] K) ⊗[R] B` is injective for injective
`ι : A → K`, since `B` is flat over the field `k`. -/
theorem tensorMapLeftTensor_injective {A : Type*} [CommRing A] [Algebra k A]
    {ι : A →ₐ[k] K} (hι : Function.Injective ι) :
    Function.Injective (tensorMapLeftTensor R B ι) := by
  have h : Function.Injective (Algebra.TensorProduct.map (AlgHom.id R B) ι) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := B) ι.toLinearMap hι
  have := congrArg DFunLike.coe (tensorTensorEquiv_comp_tensorMapLeftTensor R B ι)
  simp only [AlgHom.coe_comp] at this
  refine Function.Injective.of_comp (f := tensorTensorEquiv (k := k) R B K) ?_
  erw [this]
  exact h.comp (tensorTensorEquiv (k := k) R B A).injective

omit [Algebra k B] [IsScalarTower k R B] in
/-- Naturality of `TensorProduct.toIntegralClosure` in the base change `R ⊗[k] A → R ⊗[k] K`. -/
theorem coe_toIntegralClosure_tensorMap {A : Type*} [CommRing A] [Algebra k A]
    (ι : A →ₐ[k] K) (y : (R ⊗[k] A) ⊗[R] integralClosure R B) :
    (toIntegralClosure R (R ⊗[k] K) B
        (Algebra.TensorProduct.map (tensorMapLeft R ι) (AlgHom.id R _) y) :
          (R ⊗[k] K) ⊗[R] B) =
      tensorMapLeftTensor R B ι (toIntegralClosure R (R ⊗[k] A) B y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  | tmul s c => simp [toIntegralClosure]

end Lifting

section Transport

variable {R S S' B : Type*} [CommRing R] [CommRing S] [CommRing S'] [CommRing B] [Algebra R S]
  [Algebra R S'] [Algebra R B]

/-- Bijectivity of `TensorProduct.toIntegralClosure R S B` only depends on the `R`-algebra `S`
up to isomorphism. -/
theorem toIntegralClosure_bijective_of_algEquiv (e : S ≃ₐ[R] S')
    (H : Function.Bijective (toIntegralClosure R S B)) :
    Function.Bijective (toIntegralClosure R S' B) := by
  letI : Algebra S S' := e.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower R S S' := .of_algebraMap_eq fun r ↦ (e.commutes r).symm
  haveI : IsLocalization (⊥ : Submonoid S) S :=
    IsLocalization.self (bot_le (a := IsUnit.submonoid S))
  haveI : IsLocalization (⊥ : Submonoid S) S' :=
    IsLocalization.isLocalization_of_algEquiv ⊥ { e with commutes' := fun _ ↦ rfl }
  exact toIntegralClosure_bijective_of_tower H (toIntegralClosure_bijective_of_isLocalization ⊥)

end Transport

section Main

variable (k : Type*) [Field k] [PerfectField k] (R : Type*) [CommRing R] [Algebra k R]
  (B : Type*) [CommRing B] [Algebra R B]
  (K : Type u) [Field K] [Algebra k K]

/-- **Integral closure commutes with base change along a field extension** of a perfect field:
`(R ⊗[k] K) ⊗[R] integralClosure R B ≃ integralClosure (R ⊗[k] K) ((R ⊗[k] K) ⊗[R] B)`. -/
theorem toIntegralClosure_tensorProduct_bijective :
    Function.Bijective (toIntegralClosure R (R ⊗[k] K) B) := by
  classical
  letI : Algebra k B := ((algebraMap R B).comp (algebraMap k R)).toAlgebra
  haveI : IsScalarTower k R B := .of_algebraMap_eq fun _ ↦ rfl
  refine ⟨toIntegralClosure_injective_of_flat, ?_⟩
  rintro ⟨x, p, hp, hpx⟩
  choose Fc hFc using fun i ↦ exists_finset_mem_range_tensorMapLeft R (p.coeff i)
  obtain ⟨Fx, hFx⟩ := exists_finset_mem_range_tensorMapLeftTensor R B x
  obtain ⟨A, _, _, hA, ι, hι, hF⟩ :=
    exists_smooth_algHom_injective k (Fx ∪ p.support.biUnion Fc)
  obtain ⟨x', rfl⟩ := hFx A ι (by grw [← hF]; simp)
  have hlift : p ∈ Polynomial.lifts (tensorMapLeft R ι).toRingHom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    by_cases hi : i ∈ p.support
    · exact hFc i A ι (by grw [← hF]; exact fun c hc ↦ by simp; grind)
    · rw [Polynomial.notMem_support_iff.mp hi]
      exact ⟨0, map_zero _⟩
  obtain ⟨p', hp'map, -, hp'monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hp
  have hx' : IsIntegral (R ⊗[k] A) x' := by
    refine ⟨p', hp'monic, tensorMapLeftTensor_injective R B hι ?_⟩
    have hcomm : (tensorMapLeftTensor R B ι).toRingHom.comp
        (algebraMap (R ⊗[k] A) ((R ⊗[k] A) ⊗[R] B)) =
        (algebraMap (R ⊗[k] K) ((R ⊗[k] K) ⊗[R] B)).comp (tensorMapLeft R ι).toRingHom := by
      ext c <;> simp
    rw [map_zero, ← hpx, ← hp'map, Polynomial.eval₂_map, ← hcomm]
    exact Polynomial.hom_eval₂ _ _ _ _
  obtain ⟨y, hy⟩ := (toIntegralClosure_bijective_of_smooth (R := R) (S := R ⊗[k] A)
    (B := B)).2 ⟨x', hx'⟩
  refine ⟨Algebra.TensorProduct.map (tensorMapLeft R ι) (AlgHom.id R _) y, Subtype.ext ?_⟩
  rw [coe_toIntegralClosure_tensorMap, hy]

/-- **Integral closure commutes with base change along a field extension** of a perfect field,
pushout form: if `S` is the base change of `K` along `k → R`, then
`S ⊗[R] integralClosure R B ≃ integralClosure S (S ⊗[R] B)`. -/
theorem toIntegralClosure_bijective_of_isPushout (S : Type*) [CommRing S] [Algebra k S]
    [Algebra R S] [Algebra K S] [IsScalarTower k R S] [IsScalarTower k K S]
    [Algebra.IsPushout k R K S] :
    Function.Bijective (toIntegralClosure R S B) :=
  toIntegralClosure_bijective_of_algEquiv (Algebra.IsPushout.equiv k R K S)
    (toIntegralClosure_tensorProduct_bijective k R B K)

end Main

end Belyi
