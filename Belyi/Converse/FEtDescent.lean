/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Converse.ConstantFamily
import Belyi.Converse.IsoDescent
import Belyi.Converse.Points
import Belyi.Converse.Spread

/-!
# Descent of finite étale covers along `k ⊆ K` (★)

The core theorem (★) of `references/converse-rie-design.md`: for `k` algebraically closed of
characteristic zero and algebraic over `ℚ`, `K ⊇ k` algebraically closed, `R` a finitely generated
`k`-algebra and `B` a finite étale `K ⊗[k] R`-algebra, there is a finite étale `R`-algebra `B₀`
with `K ⊗[k] B₀ ≅ B` as `K ⊗[k] R`-algebras.

The proof is assembled from the packages of the converse, assuming the rigidity statement over
`ℂ` (package S3c), which is recorded here as the proposition `Belyi.Converse.RigidityOverC`:

1. (S1, `exists_spread`) `B` is the base change of a finite étale `A ⊗[k] R`-algebra `B_A` along
   `A ⊆ K`, for a finitely generated smooth `k`-subalgebra `A ⊆ K`.
2. (S4) There is a `k`-point `s : A → k` and an injective `k`-algebra map `ι : A → Ω := ULift ℂ`.
3. Let `B₀ := R ⊗[A ⊗[k] R] B_A` be the fibre of `B_A` at `s`; it is finite étale over `R`.
   The base change of `B_A` along `A → k → Ω` is the constant family `Ω ⊗[k] B₀`
   (`isBaseChangeAlong_fibre`).
4. (S3) By rigidity, the base change of `B_A` along `ι` is isomorphic to `Ω ⊗[k] B₀`, which is
   also the base change of the constant family `A ⊗[k] B₀` along `ι` (`isBaseChangeAlong_map`).
5. (S2, `nonempty_algEquiv_of_isBaseChangeAlong`) Hence the base changes of `B_A` and of
   `A ⊗[k] B₀` along `A ⊆ K`, namely `B` and `K ⊗[k] B₀`, are isomorphic.

## Main definitions and results

* `Belyi.Converse.FEtDescent k K`: the statement (★), as used by
  `Belyi/Converse/DefinableOfBelyi.lean`.
* `Belyi.Converse.RigidityOverC`: the statement of package S3c.
* `Belyi.Converse.exists_finiteEtale_model_of_rigidity`, `Belyi.Converse.fEtDescent_of_rigidity`:
  (★), assuming `RigidityOverC`.
-/

universe u

open TensorProduct

namespace Belyi.Converse

/-- **Finite étale descent along `k ⊆ K`** (the core theorem (★) of
`references/converse-rie-design.md`): every finite étale `K ⊗[k] R`-algebra `B`, for `R` a
finitely generated `k`-algebra, is the base change `K ⊗[k] B₀` of a finite étale `R`-algebra
`B₀`, compatibly with the structure maps from `K` and from `R`. -/
def FEtDescent (k K : Type u) [Field k] [Field K] [Algebra k K] : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    (B : Type u) [CommRing B] [Algebra (K ⊗[k] R) B] [Algebra.Etale (K ⊗[k] R) B]
    [Module.Finite (K ⊗[k] R) B],
    ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra R B₀) (_ : Algebra k B₀)
      (_ : IsScalarTower k R B₀) (_ : Algebra.Etale R B₀) (_ : Module.Finite R B₀)
      (e : K ⊗[k] B₀ ≃+* B),
      (∀ x : K, e (x ⊗ₜ 1) = algebraMap (K ⊗[k] R) B (x ⊗ₜ 1)) ∧
      (∀ r : R, e (1 ⊗ₜ algebraMap R B₀ r) = algebraMap (K ⊗[k] R) B (1 ⊗ₜ r))

/-- Rigidity over `ℂ` (package S3c): base changes of a finite étale family over a smooth
connected `Spec A` along any two `ℂ`-points are isomorphic. Here `ℂ` is lifted to `Type u` as
`ULift ℂ`, with an arbitrary `k`-algebra structure. -/
def RigidityOverC (k : Type u) [Field k] [Algebra k (ULift.{u} ℂ)] : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [Algebra.Smooth k A]
    (B : Type u) [CommRing B] [Algebra (A ⊗[k] R) B] [Algebra.Etale (A ⊗[k] R) B]
    [Module.Finite (A ⊗[k] R) B]
    (ι s : A →ₐ[k] ULift.{u} ℂ)
    (Bι Bs : Type u) [CommRing Bι] [Algebra (ULift.{u} ℂ ⊗[k] R) Bι] [CommRing Bs]
    [Algebra (ULift.{u} ℂ ⊗[k] R) Bs]
    (gι : B →+* Bι) (_ : IsBaseChangeAlong (R := R) ι gι) (gs : B →+* Bs)
    (_ : IsBaseChangeAlong (R := R) s gs),
    Nonempty (Bι ≃ₐ[ULift.{u} ℂ ⊗[k] R] Bs)

/-- The assembly of (S3) and (S2): let `B_A` be a finite étale `A ⊗[k] R`-algebra, for a finitely
generated smooth `k`-subalgebra `A ⊆ K`, with base change `B` along `A ⊆ K`. If the base change of
`B_A` along some `ℂ`-point `s` of `A` is a constant family `ℂ ⊗[k] B₀` with `B₀` finite étale over
`R`, then `B ≅ K ⊗[k] B₀` as `K ⊗[k] R`-algebras, assuming rigidity over `ℂ`. -/
theorem nonempty_algEquiv_tensor_of_rigidity
    (k K R : Type u) [Field k] [Countable k] [Field K] [IsAlgClosed K] [Algebra k K]
    [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    [Algebra k (ULift.{u} ℂ)] (hrig : RigidityOverC k)
    (A : Subalgebra k K) [Algebra.FiniteType k A] [Algebra.Smooth k A]
    (BA : Type u) [CommRing BA] [Algebra (A ⊗[k] R) BA] [Algebra.Etale (A ⊗[k] R) BA]
    [Module.Finite (A ⊗[k] R) BA]
    (B : Type u) [CommRing B] [Algebra (K ⊗[k] R) B] (g : BA →+* B)
    (hg : IsBaseChangeAlong (R := R) A.val g) (s : A →ₐ[k] ULift.{u} ℂ)
    (B₀ : Type u) [CommRing B₀] [Algebra R B₀] [Algebra k B₀] [IsScalarTower k R B₀]
    [Algebra.Etale R B₀] [Module.Finite R B₀] (g₀ : BA →+* ULift.{u} ℂ ⊗[k] B₀)
    (hg₀ : letI := tensorRightAlgebra k R (ULift.{u} ℂ) B₀; IsBaseChangeAlong (R := R) s g₀) :
    letI := tensorRightAlgebra k R K B₀
    Nonempty (K ⊗[k] B₀ ≃ₐ[K ⊗[k] R] B) := by
  haveI : Uncountable (ULift.{u} ℂ) := ULift.up_injective.uncountable
  obtain ⟨ι, hι⟩ := exists_injective_algHom k (ULift.{u} ℂ) A
  -- (S3) rigidity over `ℂ`
  obtain ⟨Bι, _, _, gι, hgι, -, -⟩ := exists_isBaseChangeAlong (R := R) ι BA
  letI := tensorRightAlgebra k R (ULift.{u} ℂ) B₀
  obtain ⟨eΩ⟩ := hrig R A BA ι s Bι (ULift.{u} ℂ ⊗[k] B₀) gι hgι g₀ hg₀
  -- (S2) descent of the isomorphism to `K`
  letI := tensorRightAlgebra k R A B₀
  letI := tensorRightAlgebra k R K B₀
  haveI := etale_tensorRight (k := k) (R := R) A B₀
  haveI := finite_tensorRight (k := k) (R := R) A B₀
  obtain ⟨eK⟩ := nonempty_algEquiv_of_isBaseChangeAlong k K (ULift.{u} ℂ) R A A.val
    Subtype.val_injective ι hι BA (A ⊗[k] B₀) Bι (ULift.{u} ℂ ⊗[k] B₀) gι hgι _
    (isBaseChangeAlong_map (R := R) ι B₀) B (K ⊗[k] B₀) g hg _
    (isBaseChangeAlong_map (R := R) A.val B₀) eΩ
  exact ⟨eK.symm⟩

/-- **Descent of finite étale covers (★)**, assuming rigidity over `ℂ` (package S3c): let `k` be
algebraically closed of characteristic zero and algebraic over `ℚ`, `K ⊇ k` algebraically closed,
`R` a finitely generated `k`-algebra and `B` a finite étale `K ⊗[k] R`-algebra. Then there is a
finite étale `R`-algebra `B₀` with `K ⊗[k] B₀ ≅ B` as `K ⊗[k] R`-algebras. -/
theorem exists_finiteEtale_model_of_rigidity
    (k K R : Type u) [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
    [Field K] [IsAlgClosed K] [Algebra k K]
    [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    (hrig : ∀ [Algebra k (ULift.{u} ℂ)], RigidityOverC k)
    (B : Type u) [CommRing B] [Algebra (K ⊗[k] R) B] [Algebra.Etale (K ⊗[k] R) B]
    [Module.Finite (K ⊗[k] R) B] :
    ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra R B₀) (_ : Algebra k B₀)
      (_ : IsScalarTower k R B₀) (_ : Algebra.Etale R B₀) (_ : Module.Finite R B₀)
      (e : K ⊗[k] B₀ ≃+* B),
      (∀ x : K, e (x ⊗ₜ 1) = algebraMap (K ⊗[k] R) B (x ⊗ₜ 1)) ∧
      (∀ r : R, e (1 ⊗ₜ algebraMap R B₀ r) = algebraMap (K ⊗[k] R) B (1 ⊗ₜ r)) := by
  -- (S1) spreading out
  obtain ⟨A, hAft, hAsm, BA, _, _, _, _, g, hg⟩ := exists_spread k K R B
  -- (S4) a `k`-point of `A`, and `k → ℂ`
  obtain ⟨s⟩ := nonempty_algHom_of_isAlgClosed k A
  obtain ⟨σ⟩ := nonempty_ringHom_complex k
  letI : Algebra k (ULift.{u} ℂ) :=
    ((ULift.ringEquiv.symm : ℂ ≃+* ULift.{u} ℂ).toRingHom.comp σ).toAlgebra
  haveI : Countable k := countable_of_isAlgebraic_rat k
  -- the fibre `B₀` of `B_A` at `s`
  letI := (evalTensor R s).toRingHom.toAlgebra
  letI := tensorRightAlgebra k R K (R ⊗[A ⊗[k] R] BA)
  obtain ⟨eK⟩ := nonempty_algEquiv_tensor_of_rigidity k K R hrig A BA B g hg
    ((Algebra.ofId k _).comp s) (R ⊗[A ⊗[k] R] BA) _ (isBaseChangeAlong_fibre s _ BA)
  refine ⟨R ⊗[A ⊗[k] R] BA, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, eK.toRingEquiv, fun x ↦ ?_, fun r ↦ ?_⟩
  · change eK (x ⊗ₜ 1) = _
    rw [← eK.commutes (x ⊗ₜ 1)]
    congr 1
  · rw [← eK.commutes (1 ⊗ₜ r)]
    rfl
/-- **Descent of finite étale covers (★)**, assuming rigidity over `ℂ` (package S3c), in the form
`Belyi.Converse.FEtDescent k K`. -/
theorem fEtDescent_of_rigidity
    (k K : Type u) [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
    [Field K] [IsAlgClosed K] [Algebra k K]
    (hrig : ∀ [Algebra k (ULift.{u} ℂ)], RigidityOverC k) : FEtDescent k K :=
  fun R _ _ _ B _ _ _ _ ↦ exists_finiteEtale_model_of_rigidity k K R hrig B

end Belyi.Converse
