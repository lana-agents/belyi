/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Converse.BaseChange
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Spreading out a finite étale algebra over `K ⊗[k] R`

Step (S1) of `references/converse-rie-design.md`. Let `k ⊆ K` be fields with `k` of
characteristic zero, `R` a `k`-algebra and `B` a finite étale `K ⊗[k] R`-algebra. Then there is a
finitely generated, smooth `k`-subalgebra `A ⊆ K` and a finite étale `A ⊗[k] R`-algebra `B_A` whose
base change along `A ⊗[k] R → K ⊗[k] R` is `B`.

## Main results

* `Belyi.Converse.exists_finite_etale_model`: a finite étale `T`-algebra `B` has a finite étale
  model over every ring `R₀ ↪ T` containing a certain finite set of elements of `T`.
* `Belyi.Converse.exists_fg_subset_range`: every finite subset of `K ⊗[k] R` lies in the image
  of `A ⊗[k] R` for some finitely generated `k`-subalgebra `A ⊆ K`.
* `Belyi.Converse.exists_smooth_le`: generic smoothness; every finitely generated `k`-subalgebra
  of `K` is contained in a finitely generated smooth one (obtained by inverting one element).
* `Belyi.Converse.exists_spread`: the spreading-out statement.

## Implementation notes

The model is constructed from a submersive presentation of relative dimension `0` of `B`
(`Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`), using mathlib's
`Algebra.SubmersivePresentation.ofHasCoeffs` (as in `Algebra.Etale.exists_subalgebra_fg`), but
over an arbitrary ring `R₀ ↪ T` instead of a subring of `T`: this is needed since the model has
to live over `A ⊗[k] R`, which is not a subring of `K ⊗[k] R` on the nose. Finiteness of the
model is obtained by also descending monic equations of the generators together with the
witnesses that they lie in the ideal of relations.

Compared with the target statement in the design, the hypothesis `Algebra.FiniteType k R` of
`exists_spread` is dropped, since it is not needed.
-/

universe u

open TensorProduct

namespace Belyi.Converse

section Model

variable (T B : Type u) [CommRing T] [CommRing B] [Algebra T B]

/-- A finite étale `T`-algebra `B` has finite étale models over all rings `R₀` with an injective
map `R₀ → T` whose image contains a certain finite subset `s ⊆ T`. -/
theorem exists_finite_etale_model [Algebra.Etale T B] [Module.Finite T B] :
    ∃ s : Set T, s.Finite ∧ ∀ (R₀ : Type u) [CommRing R₀] [Algebra R₀ T],
      Function.Injective (algebraMap R₀ T) → s ⊆ Set.range (algebraMap R₀ T) →
      ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra R₀ B₀),
        Algebra.Etale R₀ B₀ ∧ Module.Finite R₀ B₀ ∧ Nonempty (T ⊗[R₀] B₀ ≃ₐ[T] B) := by
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp ‹_›).out
  have := Fintype.ofFinite σ
  have hmem (i : ι) : ∃ p : Polynomial T, p.Monic ∧
      Polynomial.aeval (MvPolynomial.X i : P.Ring) p ∈ Ideal.span (Set.range P.relation) := by
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := T) (P.val i)
    refine ⟨p, hpm, ?_⟩
    rw [P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val, RingHom.mem_ker,
      ← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
    exact hp
  choose p hpm hp using hmem
  choose c hc using fun i ↦ Ideal.mem_span_range_iff_exists_fun.mp (hp i)
  refine ⟨P.coeffs ∪ (⋃ i, ((p i).coeffs : Set T)) ∪ ⋃ i, ⋃ j, ((c i j).coeffs : Set T),
    ((P.finite_coeffs.union (Set.finite_iUnion fun i ↦ Finset.finite_toSet _)).union
      (Set.finite_iUnion fun i ↦ Set.finite_iUnion fun j ↦ Finset.finite_toSet _)), ?_⟩
  intro R₀ _ _ hinj hs
  letI : Algebra R₀ B := ((algebraMap T B).comp (algebraMap R₀ T)).toAlgebra
  haveI : IsScalarTower R₀ T B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : FaithfulSMul R₀ T := (faithfulSMul_iff_algebraMap_injective R₀ T).mpr hinj
  haveI : P.HasCoeffs R₀ := ⟨fun x hx ↦ hs (Or.inl (Or.inl hx))⟩
  let B₀ := P.ModelOfHasCoeffs R₀
  have hEt : Algebra.Etale R₀ B₀ := Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr
    ((P.ofHasCoeffs R₀).isStandardSmoothOfRelativeDimension hP)
  -- integrality of the generators of the model
  have hint (i : ι) : IsIntegral R₀ (Ideal.Quotient.mk _ (MvPolynomial.X i) : B₀) := by
    have hlift : p i ∈ Polynomial.lifts (algebraMap R₀ T) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : (p i).coeff n = 0
      · exact ⟨0, by simp [hn]⟩
      · exact hs (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨i, Polynomial.coeff_mem_coeffs hn⟩)))
    obtain ⟨q, hq⟩ := hlift
    have hqm : q.Monic := by
      rw [Polynomial.Monic, ← hinj.eq_iff, ← Polynomial.leadingCoeff_map_of_injective hinj,
        Polynomial.coe_mapRingHom] at *
      rw [hq, (hpm i).leadingCoeff, map_one]
    have hc' (j : σ) : ∃ c₀ : MvPolynomial ι R₀, MvPolynomial.map (algebraMap R₀ T) c₀ = c i j := by
      rw [← Set.mem_range, MvPolynomial.mem_range_map_iff_coeffs_subset]
      exact fun x hx ↦ hs (Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hx⟩⟩))
    choose c₀ hc₀ using hc'
    refine ⟨q, hqm, ?_⟩
    have key : Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) q =
        ∑ j, c₀ j * P.relationOfHasCoeffs R₀ j := by
      apply MvPolynomial.map_injective _ hinj
      rw [Polynomial.hom_eval₂, MvPolynomial.map_X, map_sum]
      simp only [map_mul, hc₀, Algebra.Presentation.map_relationOfHasCoeffs]
      rw [hc i, ← hq, Polynomial.coe_mapRingHom, Polynomial.aeval_def, Polynomial.eval₂_map]
      congr 1
      ext
      simp
    have h2 := congrArg (Ideal.Quotient.mk (Ideal.span (Set.range (P.relationOfHasCoeffs R₀)))) key
    rw [Polynomial.hom_eval₂] at h2
    refine h2.trans ?_
    simp
  have hInt : Algebra.IsIntegral R₀ B₀ := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction y using MvPolynomial.induction_on with
    | C a => exact isIntegral_algebraMap
    | add f g hf hg => rw [map_add]; exact hf.add hg
    | mul_X f i hf => rw [map_mul]; exact hf.mul (hint i)
  exact ⟨B₀, inferInstance, inferInstance, hEt, Algebra.IsIntegral.finite,
    ⟨P.tensorModelOfHasCoeffsEquiv R₀⟩⟩

end Model

section Subalgebra

variable {k K : Type u} [Field k] [Field K] [Algebra k K] (R : Type u) [CommRing R] [Algebra k R]

/-- The image of `A ⊗[k] R → K ⊗[k] R` is monotone in the subalgebra `A ⊆ K`. -/
theorem range_map_val_mono {A A' : Subalgebra k K} (h : A ≤ A') :
    Set.range (Algebra.TensorProduct.map A.val (AlgHom.id k R)) ⊆
      Set.range (Algebra.TensorProduct.map A'.val (AlgHom.id k R)) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id k R) x, ?_⟩
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
  rfl

/-- For a subalgebra `A` of the field extension `K` of `k`, the map `A ⊗[k] R → K ⊗[k] R` is
injective (`R` is flat over the field `k`). -/
theorem injective_map_val (A : Subalgebra k K) :
    Function.Injective (Algebra.TensorProduct.map A.val (AlgHom.id k R)) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := R) A.val.toLinearMap
    Subtype.val_injective

/-- Every element of `K ⊗[k] R` comes from `A ⊗[k] R` for a finitely generated `A ⊆ K`. -/
theorem exists_fg_mem_range (x : K ⊗[k] R) :
    ∃ A : Subalgebra k K, A.FG ∧
      x ∈ Set.range (Algebra.TensorProduct.map A.val (AlgHom.id k R)) := by
  induction x with
  | zero => exact ⟨⊥, Subalgebra.fg_bot, 0, map_zero _⟩
  | tmul a r =>
    refine ⟨Algebra.adjoin k ((({a} : Finset K)) : Set K), Subalgebra.fg_adjoin_finset {a}, ?_⟩
    exact ⟨⟨a, Algebra.subset_adjoin (by simp)⟩ ⊗ₜ r, rfl⟩
  | add x y hx hy =>
    obtain ⟨A, hA, x', rfl⟩ := hx
    obtain ⟨A', hA', y', rfl⟩ := hy
    refine ⟨A ⊔ A', hA.sup hA', ?_⟩
    obtain ⟨x'', hx''⟩ := range_map_val_mono R (le_sup_left : A ≤ A ⊔ A') ⟨x', rfl⟩
    obtain ⟨y'', hy''⟩ := range_map_val_mono R (le_sup_right : A' ≤ A ⊔ A') ⟨y', rfl⟩
    exact ⟨x'' + y'', by rw [map_add, hx'', hy'']⟩

/-- Every finite subset of `K ⊗[k] R` comes from `A ⊗[k] R` for a finitely generated `A ⊆ K`. -/
theorem exists_fg_subset_range (s : Set (K ⊗[k] R)) (hs : s.Finite) :
    ∃ A : Subalgebra k K, A.FG ∧
      s ⊆ Set.range (Algebra.TensorProduct.map A.val (AlgHom.id k R)) := by
  classical
  obtain ⟨t, rfl⟩ := hs.exists_finset_coe
  induction t using Finset.induction_on with
  | empty => exact ⟨⊥, Subalgebra.fg_bot, by simp⟩
  | insert x t _ ih =>
    obtain ⟨A, hA, hsA⟩ := ih (Finset.finite_toSet t)
    obtain ⟨A', hA', hx⟩ := exists_fg_mem_range R x
    refine ⟨A ⊔ A', hA.sup hA', ?_⟩
    rw [Finset.coe_insert, Set.insert_subset_iff]
    exact ⟨range_map_val_mono R le_sup_right hx,
      hsA.trans (range_map_val_mono R le_sup_left)⟩

end Subalgebra

section GenericSmoothness

/-- **Generic smoothness**: a finitely generated domain over a field of characteristic zero
becomes smooth after inverting a nonzero element. -/
theorem exists_smooth_localizationAway (k : Type u) [Field k] [CharZero k] (A₀ : Type u)
    [CommRing A₀] [IsDomain A₀] [Algebra k A₀] [Algebra.FiniteType k A₀] :
    ∃ f : A₀, f ≠ 0 ∧ Algebra.Smooth k (Localization.Away f) := by
  have : Algebra.FinitePresentation k A₀ := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : IsFractionRing A₀ (Localization.AtPrime (⊥ : Ideal A₀)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal A₀).primeCompl)
  let : Field (Localization.AtPrime (⊥ : Ideal A₀)) := IsFractionRing.toField A₀
  have : Algebra.IsSmoothAt k (⊥ : Ideal A₀) := Algebra.FormallySmooth.of_perfectField
  obtain ⟨f, hf, h⟩ := Algebra.IsSmoothAt.exists_notMem_smooth k (⊥ : Ideal A₀)
  exact ⟨f, hf, h⟩

/-- Every finitely generated `k`-subalgebra `A₀` of `K` (`k` of characteristic zero) is contained
in a finitely generated smooth `k`-subalgebra `A` of `K`, namely `A₀[1/f]` for some `f ≠ 0`. -/
theorem exists_smooth_le {k K : Type u} [Field k] [CharZero k] [Field K] [Algebra k K]
    (A₀ : Subalgebra k K) (hA₀ : A₀.FG) :
    ∃ A : Subalgebra k K, A₀ ≤ A ∧ Algebra.FiniteType k A ∧ Algebra.Smooth k A := by
  have : Algebra.FiniteType k A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  obtain ⟨f, hf, _⟩ := exists_smooth_localizationAway k A₀
  have hu : ∀ y : Submonoid.powers f, IsUnit (algebraMap A₀ K y) := by
    rintro ⟨_, n, rfl⟩
    simpa using (Subtype.coe_ne_coe.mpr hf).isUnit.pow n
  let φ : Localization.Away f →ₐ[k] K :=
    { IsLocalization.lift hu with
      commutes' := fun r ↦ by
        simp [IsScalarTower.algebraMap_apply k A₀ (Localization.Away f)] }
  have hφ : Function.Injective φ := by
    change Function.Injective (IsLocalization.lift hu)
    rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [(IsLocalization.injective (Localization.Away f)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf)).eq_iff]
    exact Subtype.val_injective.eq_iff.symm
  let e := AlgEquiv.ofInjective φ hφ
  have : Algebra.Smooth k φ.range := .of_equiv e
  refine ⟨φ.range, fun a ha ↦ ⟨algebraMap A₀ (Localization.Away f) ⟨a, ha⟩, ?_⟩, inferInstance,
    this⟩
  exact IsLocalization.lift_eq hu _

end GenericSmoothness

section Spread

/-- **Spreading out** a finite étale algebra over `K ⊗[k] R`: for fields `k ⊆ K`, `k` of
characteristic zero, and a finite étale `K ⊗[k] R`-algebra `B`, there is a finitely generated smooth
`k`-subalgebra `A ⊆ K` and a finite étale `A ⊗[k] R`-algebra `B_A` with `B` the base change of
`B_A` along `A ⊗[k] R → K ⊗[k] R`. -/
theorem exists_spread (k K R : Type u) [Field k] [CharZero k] [Field K] [Algebra k K]
    [CommRing R] [Algebra k R]
    (B : Type u) [CommRing B] [Algebra (K ⊗[k] R) B] [Algebra.Etale (K ⊗[k] R) B]
    [Module.Finite (K ⊗[k] R) B] :
    ∃ (A : Subalgebra k K) (_ : Algebra.FiniteType k A) (_ : Algebra.Smooth k A)
      (B_A : Type u) (_ : CommRing B_A) (_ : Algebra (A ⊗[k] R) B_A)
      (_ : Algebra.Etale (A ⊗[k] R) B_A) (_ : Module.Finite (A ⊗[k] R) B_A)
      (g : B_A →+* B), IsBaseChangeAlong (R := R) A.val g := by
  obtain ⟨s, hs, H⟩ := exists_finite_etale_model (K ⊗[k] R) B
  obtain ⟨A₀, hA₀, hsA₀⟩ := exists_fg_subset_range R s hs
  obtain ⟨A, hle, hA, hAs⟩ := exists_smooth_le A₀ hA₀
  letI := tensorMapAlgebra R A.val
  obtain ⟨B₀, _, _, hEt, hFin, ⟨e⟩⟩ := H (A ⊗[k] R) (injective_map_val R A)
    (hsA₀.trans (range_map_val_mono R hle))
  exact ⟨A, hA, hAs, B₀, inferInstance, inferInstance, hEt, hFin,
    e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom,
    IsBaseChangeAlong.of_equiv A.val _ e fun _ ↦ rfl⟩

end Spread


end Belyi.Converse
