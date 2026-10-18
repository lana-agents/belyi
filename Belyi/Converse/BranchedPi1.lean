/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Converse.PathConnected
import Belyi.Converse.Pi1Invariance
import Belyi.Converse.Points
import Oka.Analytification.Pi1.BranchedCoordinateSpec
import Oka.Analytification.Pi1.General

/-!
# `π₁` of a smooth affine curve over `ℚ̄` with a function étale over `𝔸¹ ∖ {0, 1}`

Let `k` be an algebraically closed field with `k → ℂ`, `B` a finitely generated `k`-algebra which
is a domain, smooth of relative dimension one, and `t ∈ B` such that `k[t] → B` is finite and
étale after inverting `t (t - 1)` (for instance `B = Γ(X ∖ f⁻¹(∞))`, `t = f` for a Belyi map
`f : X → ℙ¹`). This file moves these hypotheses along `k → ℂ` to `A = ℂ ⊗[k] B` and `z = 1 ⊗ t`
(`Belyi.Converse.BranchedData.finite_baseChange`, `…etale_baseChange`,
`…smoothOfRelativeDimension_baseChange`): the squares

```
  k[X] → B          k[X] → B[(t(t-1))⁻¹]
   ↓     ↓            ↓          ↓
  ℂ[X] → ℂ ⊗ B      ℂ[X] → (ℂ ⊗ B)[(z(z-1))⁻¹]
```
are pushouts (`Algebra.IsPushout.comp_iff`, pasted with the pushout `k[X] → ℂ[X]` of
`k → ℂ` and with localisation). Then oka's
`ComplexAnalytic.exists_fundamentalGroup_analytification_specLFT_mulEquiv_freeGroup` gives:
**`π₁((Spec (ℂ ⊗ B))^an, x)` is free of rank `d + 1 - c₀ - c₁`**, where `d`, `c₀`, `c₁` are the
numbers of maximal ideals of `ℂ ⊗ B` containing `z - c` (any `c ∉ {0, 1}`), `z`, `z - 1`
(`Belyi.Converse.BranchedData.exists_fundamentalGroup_mulEquiv_freeGroup`).
-/

open CategoryTheory AlgebraicGeometry Topology
open scoped TensorProduct

universe u

namespace Belyi.Converse

open ComplexAnalytic

/-- The polynomial `X (X - 1)` over a commutative ring. -/
noncomputable abbrev branchPolyZeroOne (R : Type*) [CommRing R] : MvPolynomial (Fin 1) R :=
  MvPolynomial.X 0 * (MvPolynomial.X 0 - 1)

/-- **The data of a function on an affine curve over `k`, finite and étale over `𝔸¹ ∖ {0, 1}`.** -/
structure BranchedData (k : Type u) [Field k] (B : Type u) [CommRing B] [Algebra k B] where
  /-- The function. -/
  t : B
  /-- `k[t] → B` is finite. -/
  finite : (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ t).Finite
  /-- `k[t] → B[(t(t-1))⁻¹]` is étale. -/
  etale : ((algebraMap B (Localization.Away
    (MvPolynomial.aeval (R := k) (fun _ : Fin 1 ↦ t) (branchPolyZeroOne k)))).comp
      (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ t).toRingHom).Etale

namespace BranchedData

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B] (D : BranchedData k B)
  {Ω : Type u} [CommRing Ω] [Algebra k Ω]

attribute [local instance] Algebra.TensorProduct.rightAlgebra MvPolynomial.algebraMvPolynomial

/-- `k[X]` acting on `B` through `t`. -/
@[reducible] noncomputable def polyAlgebra : Algebra (MvPolynomial (Fin 1) k) B :=
  (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ D.t).toRingHom.toAlgebra

/-- `Ω[X]` acting on `Ω ⊗ B` through `1 ⊗ t`. -/
@[reducible] noncomputable def polyAlgebraBaseChange :
    Algebra (MvPolynomial (Fin 1) Ω) (Ω ⊗[k] B) :=
  (MvPolynomial.aeval (R := Ω) fun _ : Fin 1 ↦ (1 ⊗ₜ D.t : Ω ⊗[k] B)).toRingHom.toAlgebra

/-- `k[X]` acting on `Ω ⊗ B` through `1 ⊗ t`. -/
@[reducible] noncomputable def polyAlgebraBaseChange' :
    Algebra (MvPolynomial (Fin 1) k) (Ω ⊗[k] B) :=
  ((algebraMap B (Ω ⊗[k] B)).comp
    (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ D.t).toRingHom).toAlgebra

/-- **Properties stable under base change pass from `k[X] → B` to `Ω[X] → Ω ⊗ B`**: the square
`k[X] → B`, `Ω[X] → Ω ⊗ B` is a pushout (`Algebra.IsPushout.comp_iff`, pasted with the pushout
`k[X] → Ω[X]` of `k → Ω`). -/
theorem baseChange_of_isStableUnderBaseChange {P : ∀ {R S : Type u} [CommRing R] [CommRing S],
      (R →+* S) → Prop} (hP : RingHom.IsStableUnderBaseChange P)
    (h : P (MvPolynomial.aeval (R := k) fun _ : Fin 1 ↦ D.t).toRingHom) :
    P (MvPolynomial.aeval (R := Ω) fun _ : Fin 1 ↦ (1 ⊗ₜ D.t : Ω ⊗[k] B)).toRingHom := by
  letI := D.polyAlgebra
  letI := D.polyAlgebraBaseChange (Ω := Ω)
  letI := D.polyAlgebraBaseChange' (Ω := Ω)
  haveI : IsScalarTower k (MvPolynomial (Fin 1) k) B :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap k B r = MvPolynomial.aeval _ (MvPolynomial.C r)
      rw [MvPolynomial.aeval_C]
  haveI : IsScalarTower (MvPolynomial (Fin 1) k) B (Ω ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (MvPolynomial (Fin 1) k) (MvPolynomial (Fin 1) Ω) (Ω ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq' (MvPolynomial.ringHom_ext (fun r ↦ by
      change algebraMap B (Ω ⊗[k] B) (MvPolynomial.aeval _ (MvPolynomial.C r)) =
        MvPolynomial.aeval _ (MvPolynomial.map (algebraMap k Ω) (MvPolynomial.C r))
      rw [MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.aeval_C]
      change (1 : Ω) ⊗ₜ algebraMap k B r = algebraMap k Ω r ⊗ₜ (1 : B)
      rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply'])
      (fun i ↦ by
        change algebraMap B (Ω ⊗[k] B) (MvPolynomial.aeval _ (MvPolynomial.X i)) =
          MvPolynomial.aeval _ (MvPolynomial.map (algebraMap k Ω) (MvPolynomial.X i))
        rw [MvPolynomial.aeval_X, MvPolynomial.map_X, MvPolynomial.aeval_X]
        rfl))
  haveI : IsScalarTower k (MvPolynomial (Fin 1) Ω) (Ω ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap k (Ω ⊗[k] B) r =
        MvPolynomial.aeval _ (MvPolynomial.C (algebraMap k Ω r))
      rw [MvPolynomial.aeval_C]
      rfl
  haveI : IsScalarTower Ω (MvPolynomial (Fin 1) Ω) (Ω ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap Ω (Ω ⊗[k] B) r = MvPolynomial.aeval _ (MvPolynomial.C r)
      rw [MvPolynomial.aeval_C]
  haveI : IsScalarTower k B (Ω ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap Ω (Ω ⊗[k] B) (algebraMap k Ω r) = (1 : Ω) ⊗ₜ algebraMap k B r
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  haveI : Algebra.IsPushout k B Ω (Ω ⊗[k] B) := TensorProduct.isPushout'
  haveI : Algebra.IsPushout (MvPolynomial (Fin 1) k) B (MvPolynomial (Fin 1) Ω) (Ω ⊗[k] B) :=
    (Algebra.IsPushout.comp_iff k (MvPolynomial (Fin 1) k) Ω (S' := MvPolynomial (Fin 1) Ω)
      (T := B) (T' := Ω ⊗[k] B)).1 inferInstance
  exact hP (MvPolynomial (Fin 1) k) B (MvPolynomial (Fin 1) Ω) (Ω ⊗[k] B) h

/-- **`Ω[X] → Ω ⊗ B`, `X ↦ 1 ⊗ t`, is finite.** -/
theorem finite_baseChange :
    (MvPolynomial.aeval (R := Ω) fun _ : Fin 1 ↦ (1 ⊗ₜ D.t : Ω ⊗[k] B)).Finite :=
  D.baseChange_of_isStableUnderBaseChange RingHom.finite_isStableUnderBaseChange D.finite

/-- `t (t - 1)` on `Ω ⊗ B` is `1 ⊗ t (t - 1)`. -/
lemma aeval_branchPolyZeroOne_baseChange :
    MvPolynomial.aeval (R := Ω) (fun _ : Fin 1 ↦ (1 ⊗ₜ D.t : Ω ⊗[k] B)) (branchPolyZeroOne Ω) =
      algebraMap B (Ω ⊗[k] B)
        (MvPolynomial.aeval (R := k) (fun _ : Fin 1 ↦ D.t) (branchPolyZeroOne k)) := by
  simp only [map_mul, map_sub, map_one, MvPolynomial.aeval_X]
  rfl

/-- **`Ω[X] → (Ω ⊗ B)[(z(z-1))⁻¹]`, `X ↦ z = 1 ⊗ t`, is étale.** The square
`k[X] → B[(t(t-1))⁻¹]`, `Ω[X] → (Ω ⊗ B) ⊗_B B[(t(t-1))⁻¹]` is a pushout (paste the pushout
`k[X] → B`, `Ω[X] → Ω ⊗ B` with the base change `B → B[(t(t-1))⁻¹]`), and
`(Ω ⊗ B) ⊗_B B[(t(t-1))⁻¹]` is the localisation of `Ω ⊗ B` at `z (z - 1)`. -/
theorem etale_baseChange :
    ((algebraMap (Ω ⊗[k] B) (Localization.Away (MvPolynomial.aeval (R := Ω)
      (fun _ : Fin 1 ↦ (1 ⊗ₜ D.t : Ω ⊗[k] B)) (branchPolyZeroOne Ω)))).comp
        (MvPolynomial.aeval (R := Ω) fun _ : Fin 1 ↦ (1 ⊗ₜ D.t : Ω ⊗[k] B)).toRingHom).Etale := by
  letI := D.polyAlgebra
  letI := D.polyAlgebraBaseChange (Ω := Ω)
  letI := D.polyAlgebraBaseChange' (Ω := Ω)
  haveI : IsScalarTower k (MvPolynomial (Fin 1) k) B :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap k B r = MvPolynomial.aeval _ (MvPolynomial.C r)
      rw [MvPolynomial.aeval_C]
  haveI : IsScalarTower (MvPolynomial (Fin 1) k) B (Ω ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (MvPolynomial (Fin 1) k) (MvPolynomial (Fin 1) Ω) (Ω ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq' (MvPolynomial.ringHom_ext (fun r ↦ by
      change algebraMap B (Ω ⊗[k] B) (MvPolynomial.aeval _ (MvPolynomial.C r)) =
        MvPolynomial.aeval _ (MvPolynomial.map (algebraMap k Ω) (MvPolynomial.C r))
      rw [MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.aeval_C]
      change (1 : Ω) ⊗ₜ algebraMap k B r = algebraMap k Ω r ⊗ₜ (1 : B)
      rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply'])
      (fun i ↦ by
        change algebraMap B (Ω ⊗[k] B) (MvPolynomial.aeval _ (MvPolynomial.X i)) =
          MvPolynomial.aeval _ (MvPolynomial.map (algebraMap k Ω) (MvPolynomial.X i))
        rw [MvPolynomial.aeval_X, MvPolynomial.map_X, MvPolynomial.aeval_X]
        rfl))
  haveI : IsScalarTower k (MvPolynomial (Fin 1) Ω) (Ω ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap k (Ω ⊗[k] B) r =
        MvPolynomial.aeval _ (MvPolynomial.C (algebraMap k Ω r))
      rw [MvPolynomial.aeval_C]
      rfl
  haveI : IsScalarTower Ω (MvPolynomial (Fin 1) Ω) (Ω ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap Ω (Ω ⊗[k] B) r = MvPolynomial.aeval _ (MvPolynomial.C r)
      rw [MvPolynomial.aeval_C]
  haveI : IsScalarTower k B (Ω ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap Ω (Ω ⊗[k] B) (algebraMap k Ω r) = (1 : Ω) ⊗ₜ algebraMap k B r
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  haveI : Algebra.IsPushout k B Ω (Ω ⊗[k] B) := TensorProduct.isPushout'
  haveI : Algebra.IsPushout (MvPolynomial (Fin 1) k) B (MvPolynomial (Fin 1) Ω) (Ω ⊗[k] B) :=
    (Algebra.IsPushout.comp_iff k (MvPolynomial (Fin 1) k) Ω (S' := MvPolynomial (Fin 1) Ω)
      (T := B) (T' := Ω ⊗[k] B)).1 inferInstance
  haveI hPO : Algebra.IsPushout (MvPolynomial (Fin 1) k) B (MvPolynomial (Fin 1) Ω)
      (Ω ⊗[k] B) :=
    (Algebra.IsPushout.comp_iff k (MvPolynomial (Fin 1) k) Ω (S' := MvPolynomial (Fin 1) Ω)
      (T := B) (T' := Ω ⊗[k] B)).1 inferInstance
  -- the localisations `B_h` and `T_h`
  set h := MvPolynomial.aeval (R := k) (fun _ : Fin 1 ↦ D.t) (branchPolyZeroOne k)
  rw [aeval_branchPolyZeroOne_baseChange]
  let Bh := Localization.Away h
  let T := Ω ⊗[k] B
  let Th := Localization.Away (algebraMap B T h)
  letI : Algebra Bh Th := (Localization.awayMap (algebraMap B T) h).toAlgebra
  haveI : IsScalarTower B Bh Th := IsScalarTower.of_algebraMap_eq fun b ↦ by
    change algebraMap T Th (algebraMap B T b) = Localization.awayMap (algebraMap B T) h
      (algebraMap B Bh b)
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  haveI : IsScalarTower (MvPolynomial (Fin 1) k) Bh Th := IsScalarTower.of_algebraMap_eq fun p ↦ by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin 1) k) B Bh,
      ← IsScalarTower.algebraMap_apply B Bh Th, IsScalarTower.algebraMap_apply B T Th,
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin 1) k) T Th]
    rfl
  haveI : IsScalarTower (MvPolynomial (Fin 1) k) (MvPolynomial (Fin 1) Ω) Th :=
    IsScalarTower.of_algebraMap_eq fun p ↦ by
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin 1) k) T Th,
        IsScalarTower.algebraMap_apply (MvPolynomial (Fin 1) Ω) T Th,
        ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin 1) k) (MvPolynomial (Fin 1) Ω) T]
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid T (Submonoid.powers h)) Th := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact Localization.isLocalization
  haveI : Algebra.IsPushout B T Bh Th :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers h) Bh T Th
  haveI : Algebra.IsPushout B Bh T Th := Algebra.IsPushout.symm inferInstance
  haveI : Algebra.IsPushout (MvPolynomial (Fin 1) k) Bh (MvPolynomial (Fin 1) Ω) Th :=
    (Algebra.IsPushout.comp_iff (MvPolynomial (Fin 1) k) B (MvPolynomial (Fin 1) Ω) (S' := T)
      (T := Bh) (T' := Th)).2 inferInstance
  have hTh : (algebraMap (MvPolynomial (Fin 1) Ω) Th).Etale :=
    RingHom.Etale.isStableUnderBaseChange (MvPolynomial (Fin 1) k) Bh (MvPolynomial (Fin 1) Ω)
      Th (by rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin 1) k) B Bh]; exact D.etale)
  rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin 1) Ω) T Th] at hTh
  exact hTh

omit [Algebra k Ω] in
/-- **Smoothness of relative dimension one is preserved by `Spec (Ω ⊗[k] -)`.** -/
theorem smoothOfRelativeDimension_baseChange {n : ℕ} [Algebra k Ω]
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap k B)))] :
    SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap Ω (Ω ⊗[k] B)))) := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct k Ω B)
  exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := n)).of_isPullback
    h.flip inferInstance

end BranchedData


/-- A `ProfiniteGrp` isomorphism as a continuous multiplicative equivalence. -/
def _root_.ProfiniteGrp.isoToContinuousMulEquiv {X Y : ProfiniteGrp.{u}} (e : X ≅ Y) :
    X ≃ₜ* Y where
  toFun := e.hom.hom
  invFun := e.inv.hom
  left_inv x := by
    change (e.hom ≫ e.inv).hom x = x
    rw [e.hom_inv_id]
    rfl
  right_inv x := by
    change (e.inv ≫ e.hom).hom x = x
    rw [e.inv_hom_id]
    rfl
  map_mul' := map_mul _
  continuous_toFun := e.hom.hom.continuous
  continuous_invFun := e.inv.hom.continuous

/-- `X (X - 1)` is oka's `ComplexAnalytic.branchPoly {0, 1}`. -/
lemma branchPoly_zero_one : branchPoly ({0, 1} : Finset ℂ) = branchPolyZeroOne (ULift.{u} ℂ) := by
  rw [branchPoly, Finset.prod_pair zero_ne_one]
  rw [show (⟨0⟩ : ULift.{u} ℂ) = 0 from rfl, show (⟨1⟩ : ULift.{u} ℂ) = 1 from rfl, map_zero,
    sub_zero, map_one]

namespace BranchedData

variable {k : Type u} [Field k] [IsAlgClosed k] [Algebra k (ULift.{u} ℂ)] {B : Type u}
  [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
  [SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap k B)))]
  (D : BranchedData k B)

/-- **`π₁` of the analytification of `ℂ ⊗[k] B` is free of rank `d + 1 - c₀ - c₁`**, where `d`,
`c₀`, `c₁` are the numbers of maximal ideals of `ℂ ⊗[k] B` containing `z - c`, `z`, `z - 1` for
`z = 1 ⊗ t` and any `c ∉ {0, 1}`; at every base point `x`. -/
theorem exists_fundamentalGroup_mulEquiv_freeGroup {c : ℂ} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (x : analytification.obj (baseChangeSpec k B)) :
    ∃ (ι : Type u) (_ : Finite ι),
      Nonempty (FundamentalGroup (analytification.obj (baseChangeSpec k B)) x ≃* FreeGroup ι) ∧
      Nat.card ι + fiberCard (ULift.{u} ℂ ⊗[k] B) (1 ⊗ₜ D.t) c +
          (fiberCard (ULift.{u} ℂ ⊗[k] B) (1 ⊗ₜ D.t) 0 +
            fiberCard (ULift.{u} ℂ ⊗[k] B) (1 ⊗ₜ D.t) 1) =
        2 * fiberCard (ULift.{u} ℂ ⊗[k] B) (1 ⊗ₜ D.t) c + 1 := by
  haveI : IsDomain (B ⊗[k] ULift.{u} ℂ) := isDomain_tensorProduct_of_isAlgClosed
  haveI : IsDomain (ULift.{u} ℂ ⊗[k] B) :=
    (Algebra.TensorProduct.comm k (ULift.{u} ℂ) B).toMulEquiv.isDomain
  haveI := smoothOfRelativeDimension_baseChange (k := k) (Ω := ULift.{u} ℂ) (B := B) (n := 1)
  have het := D.etale_baseChange (Ω := ULift.{u} ℂ)
  rw [← branchPoly_zero_one] at het
  have hc : c ∉ ({0, 1} : Finset ℂ) := by simp [hc0, hc1]
  obtain ⟨ι, hι, hΦ, hcard⟩ :=
    exists_fundamentalGroup_analytification_specLFT_mulEquiv_freeGroup (A := ULift.{u} ℂ ⊗[k] B)
      (1 ⊗ₜ D.t) D.finite_baseChange {0, 1} het hc x
  refine ⟨ι, hι, hΦ, ?_⟩
  rw [Finset.sum_pair zero_ne_one, Finset.card_pair zero_ne_one] at hcard
  linarith

variable [CharZero k] [Algebra.IsAlgebraic ℚ k]

/-- **`π₁ᵉᵗ(Spec B)` is the profinite completion of a free group of rank `d + 1 - c₀ - c₁`**
(notation of `Belyi.Converse.BranchedData.exists_fundamentalGroup_mulEquiv_freeGroup`), at the
geometric point given by any point `x` of `(Spec (ℂ ⊗[k] B))^an`: oka's comparison theorem
`ComplexAnalytic.etaleFundamentalGroupEquivCompletion` and the invariance of `π₁ᵉᵗ` under
`k ⊆ ℂ` (`AlgebraicGeometry.FiniteEtale.fundamentalGroupBaseChangeEquiv`). -/
theorem exists_etaleFundamentalGroup_equiv_completion_freeGroup {c : ℂ} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) (x : analytification.obj (baseChangeSpec k B)) :
    ∃ (ι : Type u) (_ : Finite ι),
      Nonempty (π₁ᵉᵗ(geometricPoint (baseChangeSpec k B) x ≫
          FiniteEtale.baseChangeSpec k (ULift.{u} ℂ) B) ≃ₜ*
        ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FreeGroup ι))) ∧
      Nat.card ι + fiberCard (ULift.{u} ℂ ⊗[k] B) (1 ⊗ₜ D.t) c +
          (fiberCard (ULift.{u} ℂ ⊗[k] B) (1 ⊗ₜ D.t) 0 +
            fiberCard (ULift.{u} ℂ ⊗[k] B) (1 ⊗ₜ D.t) 1) =
        2 * fiberCard (ULift.{u} ℂ ⊗[k] B) (1 ⊗ₜ D.t) c + 1 := by
  obtain ⟨ι, hι, ⟨Φ⟩, hcard⟩ := D.exists_fundamentalGroup_mulEquiv_freeGroup hc0 hc1 x
  refine ⟨ι, hι, ⟨?_⟩, hcard⟩
  haveI : ConnectedSpace (baseChangeSpec k B).obj.left := connectedSpace_baseChangeSpec k B
  haveI : ConnectedSpace (Spec (CommRingCat.of B)) := inferInstance
  haveI : ConnectedSpace (Spec (CommRingCat.of (ULift.{u} ℂ ⊗[k] B))) :=
    connectedSpace_baseChangeSpec k B
  haveI := Belyi.Converse.countable_of_isAlgebraic_rat k
  exact (FiniteEtale.fundamentalGroupBaseChangeEquiv (Ω := ULift.{u} ℂ)
    (geometricPoint (baseChangeSpec k B) x)).symm.trans
      ((etaleFundamentalGroupEquivCompletion x).trans
        (ProfiniteGrp.isoToContinuousMulEquiv
          (ProfiniteGrp.profiniteCompletion.mapIso (MulEquiv.toGrpIso Φ))))

end BranchedData

end Belyi.Converse
