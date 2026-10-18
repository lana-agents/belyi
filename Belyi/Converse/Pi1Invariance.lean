/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Converse.Main
import Pi1.FundamentalGroup.AlgClosedBaseChange
import Pi1.FundamentalGroup.BaseChangeInjective

/-!
# Invariance of `π₁ᵉᵗ` under extension of algebraically closed fields (affine case)

Let `k` be an algebraically closed field of characteristic zero which is countable
(e.g. `ℚ̄`), `Ω ⊇ k` an algebraically closed field (e.g. `ℂ`) and `X = Spec R` a connected affine
scheme of finite type over `k`. Then the projection `X_Ω = Spec (Ω ⊗[k] R) ⟶ X` induces an
**isomorphism** `π₁ᵉᵗ(X_Ω) ≃ₜ* π₁ᵉᵗ(X)` (SGA 1 X.1.8 in characteristic `0`, affine case).

* Surjectivity is pi1's `FiniteEtale.fundamentalGroupMap_surjective_of_geometricallyConnected`
  (`Spec Ω ⟶ Spec k` is geometrically connected for algebraically closed `k`,
  `AlgebraicGeometry.geometricallyConnected_Spec_of_isAlgClosed`).
* Injectivity uses the Galois-category criterion `PreGaloisCategory.fiberAutMap_injective`
  (SGA 1 V.6.11): every finite étale `X_Ω`-scheme must be a subobject of the base change of a
  finite étale `X`-scheme. Here it is even isomorphic to one, by the finite étale descent
  `Belyi.Converse.fEtDescent` (proved in this repository from the Riemann existence theorem of
  `oka`, via spreading out and topological rigidity over `ℂ`). The transport from algebras to
  `FiniteEtale (Spec (Ω ⊗[k] R))` follows pi1's `FiniteEtale.exists_mono_pullback_baseChange`.

## Main results

* `AlgebraicGeometry.FiniteEtale.exists_mono_pullback_baseChange_of_fEtDescent`
* `AlgebraicGeometry.FiniteEtale.fundamentalGroupMap_baseChange_injective_of_isAlgClosed`
* `AlgebraicGeometry.FiniteEtale.fundamentalGroupMap_baseChange_bijective_of_isAlgClosed`
* `AlgebraicGeometry.FiniteEtale.fundamentalGroupBaseChangeEquiv`: `π₁ᵉᵗ(X_Ω) ≃ₜ* π₁ᵉᵗ(X)`.
-/

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

namespace FiniteEtale

variable {k Ω R : Type u} [Field k] [Field Ω] [Algebra k Ω] [CommRing R] [Algebra k R]

/-- Two ring maps out of `B ≅ Ω ⊗[k] B₀` agree if they agree on the images of `Ω` and of `B₀`. -/
lemma ringHom_ext_of_descent {B₀ B : Type u} [CommRing B₀] [Algebra k B₀] [CommRing B]
    (e : Ω ⊗[k] B₀ ≃+* B) {C : Type u} [CommRing C] (a b : B →+* C)
    (hΩ : ∀ x : Ω, a (e (x ⊗ₜ 1)) = b (e (x ⊗ₜ 1)))
    (hB : ∀ y : B₀, a (e (1 ⊗ₜ y)) = b (e (1 ⊗ₜ y))) : a = b := by
  have h (z : Ω ⊗[k] B₀) : a (e z) = b (e z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      have : (x ⊗ₜ y : Ω ⊗[k] B₀) = (x ⊗ₜ 1) * (1 ⊗ₜ y) := by simp
      rw [this, map_mul, map_mul, map_mul, hΩ, hB]
    | add z w hz hw => rw [map_add, map_add, map_add, hz, hw]
  ext y
  simpa using h (e.symm y)

/-- **Every finite étale `X_Ω`-scheme is (a subobject of) the base change of a finite étale
`X`-scheme**, for `X = Spec R` of finite type over `k`, given finite étale descent along
`k ⊆ Ω` (`Belyi.Converse.FEtDescent`). -/
theorem exists_mono_pullback_baseChange_of_fEtDescent (hdesc : Belyi.Converse.FEtDescent k Ω)
    [Algebra.FiniteType k R] (A' : FiniteEtale (Spec (.of (Ω ⊗[k] R)))) :
    ∃ (Y : FiniteEtale (Spec (.of R))) (i : A' ⟶ (pullback (baseChangeSpec k Ω R)).obj Y),
      Mono i := by
  let B : CommRingCat.{u} := Γ(A'.left, ⊤)
  letI : Algebra (Ω ⊗[k] R) B := (ringHomΓ A').hom.toAlgebra
  haveI : Algebra.FiniteEtale (Ω ⊗[k] R) B := finiteEtale_ringHomΓ A'
  obtain ⟨B₀, _, _, _, _, _, _, e, he₁, he₂⟩ := hdesc R B
  let incΩ : R →+* Ω ⊗[k] R :=
    (Algebra.TensorProduct.includeRight : R →ₐ[k] Ω ⊗[k] R).toRingHom
  let φY : R →+* B₀ := algebraMap R B₀
  haveI : IsFiniteEtale (Spec.map (CommRingCat.ofHom φY)) := by
    rw [IsFiniteEtale.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finiteEtale_algebraMap_iff]
    exact ⟨⟩
  let Y : FiniteEtale (Spec (.of R)) := mk (Spec.map (CommRingCat.ofHom φY))
  let ψ : B₀ →+* B := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : B₀ →ₐ[k] Ω ⊗[k] B₀).toRingHom
  have hψ (y : B₀) : ψ y = e (1 ⊗ₜ y) := rfl
  have hα (t : Ω ⊗[k] R) : ringHomΓ A' t = algebraMap (Ω ⊗[k] R) B t := rfl
  have hring : CommRingCat.ofHom φY ≫ CommRingCat.ofHom ψ =
      CommRingCat.ofHom incΩ ≫ ringHomΓ A' := by
    ext r
    change ψ (algebraMap R B₀ r) = ringHomΓ A' (incΩ r)
    rw [hψ, he₂, hα]
    rfl
  have h : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φY) =
      Spec.map (ringHomΓ A') ≫ Spec.map (CommRingCat.ofHom incΩ) := by
    rw [← Spec.map_comp, ← Spec.map_comp, hring]
  have hgen (C : CommRingCat.{u}) (a b : B ⟶ C) (ha : CommRingCat.ofHom ψ ≫ a =
      CommRingCat.ofHom ψ ≫ b) (hb : ringHomΓ A' ≫ a = ringHomΓ A' ≫ b) : a = b := by
    ext1
    refine ringHom_ext_of_descent e a.hom b.hom (fun x ↦ ?_) (fun y ↦ congr($ha y))
    rw [he₁ x]
    exact congr($hb (x ⊗ₜ 1))
  have hmono := mono_pullback_lift_Spec (CommRingCat.ofHom φY) (CommRingCat.ofHom incΩ)
    (CommRingCat.ofHom ψ) (ringHomΓ A') h hgen
  let ℓ : A'.left ⟶ ((pullback (baseChangeSpec k Ω R)).obj Y).left :=
    A'.left.isoSpec.hom ≫ pullback.lift _ _ h
  have hw : ℓ ≫ ((pullback (baseChangeSpec k Ω R)).obj Y).hom = A'.hom := by
    rw [hom_eq_isoSpec_hom_comp A']
    change A'.left.isoSpec.hom ≫ pullback.lift _ _ h ≫ pullback.snd _ _ = _
    rw [pullback.lift_snd]
  refine ⟨Y, MorphismProperty.Over.homMk ℓ hw trivial, ?_⟩
  have : Mono ℓ := @mono_comp _ _ _ _ _ _ inferInstance _ hmono
  exact (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mono_of_mono_map this

variable [IsAlgClosed k] [CharZero k] [Countable k] [IsAlgClosed Ω]
  [Algebra.FiniteType k R]

/-- **`π₁ᵉᵗ(X_Ω) → π₁ᵉᵗ(X)` is injective** for an extension `Ω ⊇ k` of algebraically closed
fields of characteristic zero with `k` countable, and `X = Spec R` affine of finite type
over `k` with `X_Ω` connected. -/
theorem fundamentalGroupMap_baseChange_injective_of_isAlgClosed
    [ConnectedSpace (Spec (.of (Ω ⊗[k] R)))] {L : Type u} [Field L] [IsSepClosed L]
    (x : Spec (.of L) ⟶ Spec (.of (Ω ⊗[k] R))) :
    Function.Injective (fundamentalGroupMap (baseChangeSpec k Ω R) (rfl :
      x ≫ baseChangeSpec k Ω R = _)) := fun _ _ hab ↦
  PreGaloisCategory.fiberAutMap_injective (fiber x) (pullbackFiberIso _ rfl)
    (fun A _ ↦ exists_mono_pullback_baseChange_of_fEtDescent
      (Belyi.Converse.fEtDescent_of_countable k Ω) A)
    hab

omit [IsAlgClosed k] [CharZero k] [Countable k] [IsAlgClosed Ω]
  [Algebra.FiniteType k R] in
/-- `X_Ω = Spec (Ω ⊗[k] R) ⟶ X = Spec R` is the base change of `Spec Ω ⟶ Spec k`. -/
lemma isPullback_baseChangeSpec :
    IsPullback (baseChangeSpec k Ω R)
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : Ω →ₐ[k] Ω ⊗[k] R).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct k Ω R)).flip

omit [CharZero k] [Countable k] [IsAlgClosed Ω] [Algebra.FiniteType k R] in
instance geometricallyConnected_baseChangeSpec : GeometricallyConnected (baseChangeSpec k Ω R) :=
  haveI := geometricallyConnected_Spec_of_isAlgClosed k Ω
  MorphismProperty.of_isPullback isPullback_baseChangeSpec.flip ‹_›

omit [IsAlgClosed k] [CharZero k] [Countable k] [IsAlgClosed Ω]
  [Algebra.FiniteType k R] in
instance universallyOpen_baseChangeSpec : UniversallyOpen (baseChangeSpec k Ω R) :=
  MorphismProperty.of_isPullback isPullback_baseChangeSpec.flip inferInstance

omit [CharZero k] [Countable k] [IsAlgClosed Ω] [Algebra.FiniteType k R] in
/-- For `X = Spec R` connected over an algebraically closed `k`, `X_Ω` is connected. -/
instance connectedSpace_baseChange [ConnectedSpace (Spec (.of R))] :
    ConnectedSpace (Spec (.of (Ω ⊗[k] R))) :=
  GeometricallyConnected.connectedSpace (baseChangeSpec k Ω R)
    (baseChangeSpec k Ω R).isOpenMap

/-- **Invariance of `π₁ᵉᵗ` under extension of algebraically closed fields** (affine case, SGA 1
X.1.8 in characteristic `0`): for `k ⊆ Ω` algebraically closed of characteristic zero with `k`
countable, and `X = Spec R` connected of finite type over `k`, the projection
`X_Ω ⟶ X` induces a bijection `π₁ᵉᵗ(X_Ω, x) → π₁ᵉᵗ(X, x)` at every geometric point `x`. -/
theorem fundamentalGroupMap_baseChange_bijective_of_isAlgClosed [ConnectedSpace (Spec (.of R))]
    {L : Type u} [Field L] [IsSepClosed L] (x : Spec (.of L) ⟶ Spec (.of (Ω ⊗[k] R))) :
    Function.Bijective (fundamentalGroupMap (baseChangeSpec k Ω R) (rfl :
      x ≫ baseChangeSpec k Ω R = _)) :=
  ⟨fundamentalGroupMap_baseChange_injective_of_isAlgClosed x,
    fundamentalGroupMap_surjective_of_geometricallyConnected _ _⟩

/-- **`π₁ᵉᵗ(X_Ω, x) ≃ₜ* π₁ᵉᵗ(X, x)`** for `X = Spec R` connected of finite type over `k`, as in
`fundamentalGroupMap_baseChange_bijective_of_isAlgClosed`. The inverse is continuous because
`π₁ᵉᵗ(X_Ω, x)` is compact and `π₁ᵉᵗ(X, x)` is Hausdorff. -/
noncomputable def fundamentalGroupBaseChangeEquiv [ConnectedSpace (Spec (.of R))]
    {L : Type u} [Field L] [IsSepClosed L] (x : Spec (.of L) ⟶ Spec (.of (Ω ⊗[k] R))) :
    π₁ᵉᵗ(x) ≃ₜ* π₁ᵉᵗ(x ≫ baseChangeSpec k Ω R) :=
  let f := fundamentalGroupMap (baseChangeSpec k Ω R) (rfl : x ≫ baseChangeSpec k Ω R = _)
  let e : π₁ᵉᵗ(x) ≃* π₁ᵉᵗ(x ≫ baseChangeSpec k Ω R) := MulEquiv.ofBijective f.toMonoidHom
    (fundamentalGroupMap_baseChange_bijective_of_isAlgClosed (Ω := Ω) (R := R) x)
  let h : π₁ᵉᵗ(x) ≃ₜ π₁ᵉᵗ(x ≫ baseChangeSpec k Ω R) :=
    Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) f.continuous_toFun
  { e with
    continuous_toFun := h.continuous_toFun
    continuous_invFun := h.continuous_invFun }

end FiniteEtale

end AlgebraicGeometry
