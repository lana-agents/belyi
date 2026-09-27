/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Converse.Basic
import Belyi.Converse.PathConnected
import Belyi.Converse.Rigidity

/-!
# Rigidity of families of finite étale algebras over `ℂ` (S3)

Step (S3) of the converse direction of Belyi's theorem (`references/converse-rie-design.md`),
in algebraic form: let `k` be an algebraically closed field with `k → ℂ`, `R` a finitely
generated `k`-algebra, `A` a finitely generated smooth `k`-algebra which is a domain and `B` a
finite étale `A ⊗[k] R`-algebra. Then for any two `k`-algebra maps `ι, s : A → ℂ`, the base
changes of `B` along `ι ⊗ id_R` and `s ⊗ id_R` are isomorphic `ℂ ⊗[k] R`-algebras
(`Belyi.Converse.rigidityOverC`).

Proof: this is the scheme-level rigidity theorem `Belyi.Converse.exists_iso_of_isPullback_fiber`
applied to `Z = Spec (ℂ ⊗[k] R)`, `T = Spec (ℂ ⊗[k] A)` (whose analytification is path connected,
`Belyi.Converse.pathConnectedSpace_analytification_baseChangeSpec`), `P = Z ×_ℂ T`, the finite
étale `𝒴 = P ×_{Spec (A ⊗[k] R)} Spec B ⟶ P` and the `ℂ`-points `t_ι, t_s` of `T` induced by
`ι, s`. The fibre of `𝒴` over `t_ι` is `Spec B_ι`: the section `Z ⟶ P` at `t_ι` followed by
`P ⟶ Spec (A ⊗[k] R)` is `Spec (ι ⊗ id_R)`, and the base-change square of `B_ι` is a pullback.
Finally an isomorphism `Spec B_ι ≅ Spec B_s` over `Spec (ℂ ⊗[k] R)` comes from an isomorphism of
`ℂ ⊗[k] R`-algebras (`Spec` is fully faithful).

Here `ℂ` is `ULift.{u} ℂ`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry ComplexAnalytic TensorProduct

namespace Belyi.Converse

noncomputable section

/-! ### Base change squares as pullbacks of spectra -/

section BaseChange

variable {k : Type u} [CommRing k] {R : Type u} [CommRing R] [Algebra k R]
  {A : Type u} [CommRing A] [Algebra k A] {L : Type u} [CommRing L] [Algebra k L]
  {B : Type u} [CommRing B] [Algebra (A ⊗[k] R) B]
  {B' : Type u} [CommRing B'] [Algebra (L ⊗[k] R) B']

/-- The base change square of `IsBaseChangeAlong φ g` is a pullback square of spectra. -/
theorem isPullback_Spec_of_isBaseChangeAlong (φ : A →ₐ[k] L) (g : B →+* B')
    (hbc : IsBaseChangeAlong (R := R) φ g) :
    IsPullback (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (algebraMap (L ⊗[k] R) B')))
      (Spec.map (CommRingCat.ofHom (algebraMap (A ⊗[k] R) B)))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id k R)).toRingHom)) := by
  letI := tensorMapAlgebra R φ
  letI : Algebra B B' := g.toAlgebra
  letI : Algebra (A ⊗[k] R) B' := ((algebraMap B B').comp (algebraMap (A ⊗[k] R) B)).toAlgebra
  haveI : IsScalarTower (A ⊗[k] R) B B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨_, _⟩ := hbc
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout (A ⊗[k] R) (L ⊗[k] R) B B')).flip

end BaseChange

/-! ### The schemes -/

variable (k : Type u) [Field k] [Algebra k (ULift.{u} ℂ)]
  (R : Type u) [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
  (A : Type u) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

/-- The product `Z ×_ℂ T` of `Z = Spec (ℂ ⊗[k] R)` and `T = Spec (ℂ ⊗[k] A)`. -/
abbrev prodSpec : SchemeLFTℂ.{u} :=
  SchemeLFTℂ.fibreProd (toPointLFT (baseChangeSpec k R)) (toPointLFT (baseChangeSpec k A))

lemma isPullback_prodSpec :
    IsPullback (SchemeLFTℂ.fibreProdFst (toPointLFT (baseChangeSpec k R))
        (toPointLFT (baseChangeSpec k A))).hom.left
      (SchemeLFTℂ.fibreProdSnd (toPointLFT (baseChangeSpec k R))
        (toPointLFT (baseChangeSpec k A))).hom.left
      (baseChangeSpec k R).obj.hom (baseChangeSpec k A).obj.hom :=
  IsPullback.of_hasPullback _ _

variable {k A} in
/-- The `ℂ`-algebra map `ℂ ⊗[k] A → ℂ` induced by a `k`-algebra map `φ : A → ℂ`. -/
def evalTensor (φ : A →ₐ[k] ULift.{u} ℂ) : ULift.{u} ℂ ⊗[k] A →ₐ[ULift.{u} ℂ] ULift.{u} ℂ :=
  Algebra.TensorProduct.lift (AlgHom.id (ULift.{u} ℂ) (ULift.{u} ℂ)) φ
    (fun _ _ ↦ Commute.all _ _)

variable {k A} in
/-- The `ℂ`-point of `T = Spec (ℂ ⊗[k] A)` induced by a `k`-algebra map `φ : A → ℂ`. -/
def pointOfAlgHom (φ : A →ₐ[k] ULift.{u} ℂ) : pointLFT.{u} ⟶ baseChangeSpec k A :=
  SchemeLFTℂ.specHom _ _ (CommRingCat.ofHom (evalTensor φ).toRingHom) (by
    ext x
    exact congrArg ULift.down ((evalTensor φ).commutes x))

variable {k A} in
lemma pointOfAlgHom_comp (φ : A →ₐ[k] ULift.{u} ℂ) :
    (pointOfAlgHom φ).hom.left ≫ (baseChangeSpec k A).obj.hom = 𝟙 _ := by
  have h : CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) (ULift.{u} ℂ ⊗[k] A)) ≫
      CommRingCat.ofHom (evalTensor φ).toRingHom = 𝟙 _ := by
    ext x
    exact congrArg ULift.down ((evalTensor φ).commutes x)
  exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map h).trans (Spec.map_id _))

variable {k A} in
/-- The section `Z ⟶ Z ×_ℂ T` at the `ℂ`-point induced by `φ : A → ℂ`. -/
def sectionOfAlgHom (φ : A →ₐ[k] ULift.{u} ℂ) : baseChangeSpec k R ⟶ prodSpec k R A :=
  ObjectProperty.homMk (Over.homMk (pullback.lift (𝟙 _)
      ((baseChangeSpec k R).obj.hom ≫ (pointOfAlgHom φ).hom.left) (by
        change 𝟙 _ ≫ (baseChangeSpec k R).obj.hom =
          ((baseChangeSpec k R).obj.hom ≫ (pointOfAlgHom φ).hom.left) ≫
            (baseChangeSpec k A).obj.hom
        rw [Category.id_comp, Category.assoc]
        exact ((congrArg ((baseChangeSpec k R).obj.hom ≫ ·) (pointOfAlgHom_comp φ)).trans
          (Category.comp_id _)).symm)) (by
      change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ _ = _
      rw [pullback.lift_fst_assoc, Category.id_comp]))

variable {k A} in
lemma sectionOfAlgHom_fst (φ : A →ₐ[k] ULift.{u} ℂ) :
    sectionOfAlgHom R φ ≫ SchemeLFTℂ.fibreProdFst _ _ = 𝟙 _ := by
  ext1
  exact Over.OverMorphism.ext (pullback.lift_fst _ _ _)

variable {k A} in
lemma sectionOfAlgHom_snd (φ : A →ₐ[k] ULift.{u} ℂ) :
    sectionOfAlgHom R φ ≫ SchemeLFTℂ.fibreProdSnd _ _ =
      toPointLFT (baseChangeSpec k R) ≫ pointOfAlgHom φ := by
  ext1
  exact Over.OverMorphism.ext (pullback.lift_snd _ _ _)

omit [Algebra k (ULift.{u} ℂ)] [Algebra.FiniteType k R] [Algebra.FiniteType k A] in
/-- `Spec (A ⊗[k] R)` as the pullback `Spec A ×_{Spec k} Spec R`. -/
lemma isPullback_Spec_tensor :
    IsPullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft (R := k) (S := k) (A := A) (B := R)).toRingHom))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := k) (A := A) (B := R)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct k A R)

variable {k} in
lemma algebraMap_comp_includeRight (M : Type u) [CommRing M] [Algebra k M] :
    CommRingCat.ofHom (algebraMap k M) ≫ CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := k) (A := ULift.{u} ℂ) (B := M)).toRingHom =
      CommRingCat.ofHom (algebraMap k (ULift.{u} ℂ)) ≫
        CommRingCat.ofHom (algebraMap (ULift.{u} ℂ) (ULift.{u} ℂ ⊗[k] M)) := by
  ext c
  change Algebra.TensorProduct.includeRight (algebraMap k M c) =
    algebraMap (ULift.{u} ℂ) (ULift.{u} ℂ ⊗[k] M) (algebraMap k (ULift.{u} ℂ) c)
  rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

variable {k} in
/-- The morphism `Spec (ℂ ⊗[k] M) ⟶ Spec M`. -/
def incSpec (M : Type u) [CommRing M] [Algebra k M] [Algebra.FiniteType k M] :
    (baseChangeSpec k M).obj.left ⟶ Spec (CommRingCat.of M) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := k) (A := ULift.{u} ℂ) (B := M)).toRingHom)

variable {k} in
lemma incSpec_comp (M : Type u) [CommRing M] [Algebra k M] [Algebra.FiniteType k M] :
    incSpec M ≫ Spec.map (CommRingCat.ofHom (algebraMap k M)) =
      (baseChangeSpec k M).obj.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k (ULift.{u} ℂ))) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, algebraMap_comp_includeRight]

/-- The morphism `Z ×_ℂ T ⟶ Spec (A ⊗[k] R)`. -/
def prodSpecToSpecTensor : (prodSpec k R A).obj.left ⟶ Spec (CommRingCat.of (A ⊗[k] R)) :=
  (isPullback_Spec_tensor k R A).lift (pullback.snd _ _ ≫ incSpec A) (pullback.fst _ _ ≫ incSpec R)
    (by
      rw [Category.assoc, Category.assoc, incSpec_comp, incSpec_comp, ← Category.assoc,
        ← Category.assoc]
      exact congrArg (· ≫ _) (pullback.condition (f := (toPointLFT (baseChangeSpec k R)).hom.left)
        (g := (toPointLFT (baseChangeSpec k A)).hom.left)).symm)

variable {k A} in
lemma sectionOfAlgHom_hom_left_fst (φ : A →ₐ[k] ULift.{u} ℂ) :
    (sectionOfAlgHom R φ).hom.left ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

variable {k A} in
lemma sectionOfAlgHom_hom_left_snd (φ : A →ₐ[k] ULift.{u} ℂ) :
    (sectionOfAlgHom R φ).hom.left ≫ pullback.snd _ _ =
      (baseChangeSpec k R).obj.hom ≫ (pointOfAlgHom φ).hom.left :=
  pullback.lift_snd _ _ _

variable {k A} in
/-- The section at `φ` followed by `Z ×_ℂ T ⟶ Spec (A ⊗[k] R)` is `Spec (φ ⊗ id_R)`. -/
lemma sectionOfAlgHom_comp_prodSpecToSpecTensor (φ : A →ₐ[k] ULift.{u} ℂ) :
    (sectionOfAlgHom R φ).hom.left ≫ prodSpecToSpecTensor k R A =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map φ (AlgHom.id k R)).toRingHom) := by
  refine (isPullback_Spec_tensor k R A).hom_ext ?_ ?_
  · rw [Category.assoc, prodSpecToSpecTensor, IsPullback.lift_fst, ← Category.assoc,
      sectionOfAlgHom_hom_left_snd]
    change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    simp only [← Spec.map_comp]
    congr 1
    ext a
    change algebraMap (ULift.{u} ℂ) (ULift.{u} ℂ ⊗[k] R) (evalTensor φ (1 ⊗ₜ a)) = φ a ⊗ₜ 1
    simp [evalTensor, Algebra.TensorProduct.algebraMap_apply]
  · rw [Category.assoc, prodSpecToSpecTensor, IsPullback.lift_snd, ← Category.assoc,
      sectionOfAlgHom_hom_left_fst, Category.id_comp]
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext r
    change (1 : ULift.{u} ℂ) ⊗ₜ[k] r = Algebra.TensorProduct.map φ (AlgHom.id k R) (1 ⊗ₜ r)
    simp

section

omit [Algebra k (ULift.{u} ℂ)] [Algebra.FiniteType k R] [Algebra.FiniteType k A]

variable (B : Type u) [CommRing B] [Algebra (A ⊗[k] R) B]

/-- The morphism `Spec B ⟶ Spec (A ⊗[k] R)`. -/
abbrev specStructure : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (A ⊗[k] R)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (A ⊗[k] R) B))

lemma isFinite_specStructure [Module.Finite (A ⊗[k] R) B] : IsFinite (specStructure k R A B) :=
  (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)

lemma etale_specStructure [Algebra.Etale (A ⊗[k] R) B] : Etale (specStructure k R A B) :=
  (HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.2 inferInstance)

end

variable (B : Type u) [CommRing B] [Algebra (A ⊗[k] R) B] [Algebra.Etale (A ⊗[k] R) B]
  [Module.Finite (A ⊗[k] R) B]

/-- The finite étale family `𝒴 = (Z ×_ℂ T) ×_{Spec (A ⊗[k] R)} Spec B`. -/
def familySpec : SchemeLFTℂ.{u} :=
  ⟨Over.mk (pullback.fst (prodSpecToSpecTensor k R A) (specStructure k R A B) ≫
      (prodSpec k R A).obj.hom), by
    haveI := isFinite_specStructure k R A B
    haveI : LocallyOfFiniteType (prodSpec k R A).obj.hom := (prodSpec k R A).property
    haveI : IsFinite (pullback.fst (prodSpecToSpecTensor k R A) (specStructure k R A B)) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip ‹_›
    have h₁ : LocallyOfFiniteType
        (pullback.fst (prodSpecToSpecTensor k R A) (specStructure k R A B)) := inferInstance
    have h₂ : LocallyOfFiniteType (prodSpec k R A).obj.hom := (prodSpec k R A).property
    exact @locallyOfFiniteType_comp _ _ _ _ _ h₁ h₂⟩

/-- The structure morphism `𝒴 ⟶ Z ×_ℂ T`. -/
def familySpecHom : familySpec k R A B ⟶ prodSpec k R A :=
  ObjectProperty.homMk (Over.homMk (pullback.fst _ _) rfl)

lemma isFiniteEtale_familySpecHom : SchemeLFTℂ.isFiniteEtale (familySpecHom k R A B) := by
  haveI := isFinite_specStructure k R A B
  haveI := etale_specStructure k R A B
  exact ⟨MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip ‹_›,
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip ‹_›⟩

/-! ### The fibres -/

variable {k A B}

omit [Algebra.FiniteType k R] [Algebra.FiniteType k A] [Algebra.Etale (A ⊗[k] R) B] in
lemma isFinite_specMap_algebraMap_of_isBaseChangeAlong (φ : A →ₐ[k] ULift.{u} ℂ)
    (Bφ : Type u) [CommRing Bφ] [Algebra (ULift.{u} ℂ ⊗[k] R) Bφ] {gφ : B →+* Bφ}
    (hbc : IsBaseChangeAlong (R := R) φ gφ) :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ ⊗[k] R) Bφ))) := by
  haveI := isFinite_specStructure k R A B
  exact MorphismProperty.of_isPullback (isPullback_Spec_of_isBaseChangeAlong φ gφ hbc) ‹_›

variable (Bφ : Type u) [CommRing Bφ] [Algebra (ULift.{u} ℂ ⊗[k] R) Bφ]

/-- `Spec Bφ`, for a finite `ℂ ⊗[k] R`-algebra `Bφ`, as a scheme locally of finite type over
`ℂ`. -/
def fiberSpec
    (hBφ : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ ⊗[k] R) Bφ)))) :
    SchemeLFTℂ.{u} :=
  ⟨Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ ⊗[k] R) Bφ)) ≫
      (baseChangeSpec k R).obj.hom), by
    have h₁ : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ ⊗[k] R) Bφ))) := inferInstance
    have h₂ : LocallyOfFiniteType (baseChangeSpec k R).obj.hom := (baseChangeSpec k R).property
    exact @locallyOfFiniteType_comp _ _ _ _ _ h₁ h₂⟩

variable (hBφ : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ ⊗[k] R) Bφ))))

/-- The structure morphism `Spec Bφ ⟶ Z`. -/
def fiberSpecHom : fiberSpec R Bφ hBφ ⟶ baseChangeSpec k R :=
  ObjectProperty.homMk (Over.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℂ ⊗[k] R) Bφ))) rfl)

/-- The morphism `Spec Bφ ⟶ 𝒴`. -/
def fiberSpecToFamily (φ : A →ₐ[k] ULift.{u} ℂ) {gφ : B →+* Bφ}
    (hbc : IsBaseChangeAlong (R := R) φ gφ) : fiberSpec R Bφ hBφ ⟶ familySpec k R A B :=
  ObjectProperty.homMk (Over.homMk (pullback.lift
      ((fiberSpecHom R Bφ hBφ).hom.left ≫ (sectionOfAlgHom R φ).hom.left)
      (Spec.map (CommRingCat.ofHom gφ)) (by
        rw [Category.assoc, sectionOfAlgHom_comp_prodSpecToSpecTensor]
        exact (isPullback_Spec_of_isBaseChangeAlong φ gφ hbc).w.symm)) (by
      change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ _ = _
      rw [pullback.lift_fst_assoc, Category.assoc, Over.w (sectionOfAlgHom R φ).hom]
      rfl))

omit [Algebra.Etale (A ⊗[k] R) B] in
/-- `Spec Bφ` is the fibre of `𝒴` over the `ℂ`-point induced by `φ`. -/
lemma isPullback_fiberSpec (φ : A →ₐ[k] ULift.{u} ℂ) {gφ : B →+* Bφ}
    (hbc : IsBaseChangeAlong (R := R) φ gφ) :
    IsPullback (fiberSpecToFamily R Bφ hBφ φ hbc).hom.left (fiberSpecHom R Bφ hBφ).hom.left
      (familySpecHom k R A B).hom.left (sectionOfAlgHom R φ).hom.left := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback _ _).flip
  change IsPullback (pullback.lift _ _ _ ≫ pullback.snd _ _) _ _
    ((sectionOfAlgHom R φ).hom.left ≫ prodSpecToSpecTensor k R A)
  rw [pullback.lift_snd, sectionOfAlgHom_comp_prodSpecToSpecTensor]
  exact isPullback_Spec_of_isBaseChangeAlong φ gφ hbc

/-! ### Rigidity over `ℂ` -/

omit [Algebra.FiniteType k R] in
/-- An isomorphism `Spec B₁ ≅ Spec B₂` over `Spec S` comes from an `S`-algebra isomorphism. -/
lemma nonempty_algEquiv_of_iso {S B₁ B₂ : Type u} [CommRing S] [CommRing B₁] [CommRing B₂]
    [Algebra S B₁] [Algebra S B₂]
    (e : Spec (CommRingCat.of B₁) ≅ Spec (CommRingCat.of B₂))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap S B₂)) =
      Spec.map (CommRingCat.ofHom (algebraMap S B₁))) :
    Nonempty (B₁ ≃ₐ[S] B₂) := by
  let φ₁ : CommRingCat.of B₂ ⟶ CommRingCat.of B₁ := Spec.preimage e.hom
  let φ₂ : CommRingCat.of B₁ ⟶ CommRingCat.of B₂ := Spec.preimage e.inv
  have h₁₂ : φ₁ ≫ φ₂ = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, e.inv_hom_id, Spec.map_id])
  have h₂₁ : φ₂ ≫ φ₁ = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, e.hom_inv_id, Spec.map_id])
  have hc : CommRingCat.ofHom (algebraMap S B₂) ≫ φ₁ = CommRingCat.ofHom (algebraMap S B₁) :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_preimage, he])
  have hc' : CommRingCat.ofHom (algebraMap S B₁) ≫ φ₂ = CommRingCat.ofHom (algebraMap S B₂) := by
    rw [← hc, Category.assoc, h₁₂, Category.comp_id]
  let f : B₁ ≃+* B₂ := RingEquiv.ofRingHom φ₂.hom φ₁.hom
    (congrArg CommRingCat.Hom.hom h₁₂) (congrArg CommRingCat.Hom.hom h₂₁)
  exact ⟨AlgEquiv.ofRingEquiv (f := f) fun x ↦
    congrArg (fun ψ : CommRingCat.of S ⟶ CommRingCat.of B₂ ↦ ψ x) hc'⟩

omit [Algebra.FiniteType k R] [Algebra.FiniteType k A] in
/-- **Rigidity over `ℂ` (S3).** Let `k` be an algebraically closed field with `k → ℂ`, `R` a
finitely generated `k`-algebra, `A` a finitely generated smooth `k`-algebra which is a domain, and
`B` a finite étale `A ⊗[k] R`-algebra. For any two `k`-algebra maps `ι, s : A → ℂ`, the base
changes `B_ι`, `B_s` of `B` along `ι ⊗ id_R` and `s ⊗ id_R` are isomorphic as
`ℂ ⊗[k] R`-algebras. -/
theorem rigidityOverC [IsAlgClosed k] :
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
      Nonempty (Bι ≃ₐ[ULift.{u} ℂ ⊗[k] R] Bs) := by
  intro R _ _ _ A _ _ _ _ _ B _ _ _ _ ι s Bι Bs _ _ _ _ gι hι gs hs
  haveI := pathConnectedSpace_analytification_baseChangeSpec k A
  haveI : IsAffine (baseChangeSpec k R).obj.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (ULift.{u} ℂ ⊗[k] R))))
  haveI : IsAffine (baseChangeSpec k A).obj.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (ULift.{u} ℂ ⊗[k] A))))
  obtain ⟨e, he⟩ := exists_iso_of_isPullback_fiber (isPullback_prodSpec k R A)
    (isFiniteEtale_familySpecHom k R A B) (sectionOfAlgHom_fst R ι) (sectionOfAlgHom_snd R ι)
    (sectionOfAlgHom_fst R s) (sectionOfAlgHom_snd R s)
    (isPullback_fiberSpec R Bι (isFinite_specMap_algebraMap_of_isBaseChangeAlong R ι Bι hι) ι hι)
    (isPullback_fiberSpec R Bs (isFinite_specMap_algebraMap_of_isBaseChangeAlong R s Bs hs) s hs)
  exact nonempty_algEquiv_of_iso e he

end

end Belyi.Converse
