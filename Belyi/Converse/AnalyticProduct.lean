/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Oka.Analytification.GAGA.ClosedImmersion
import Oka.Analytification.RET.ClosedPoints
import Oka.Analytification.RET.ES.FiniteSplitting
import Oka.AnalyticSpace.CoveringSpaceHomeomorph

/-!
# Points of analytifications and the analytification of a product

For the converse direction of Belyi's theorem (`references/converse-rie-design.md`, step (S3c))
we need to know the topological space underlying the analytification of a product
`Z ×_ℂ T` of schemes (locally) of finite type over `ℂ`.

## Main definitions

* `Belyi.Converse.pointLFT`: the point `Spec ℂ`, as a scheme locally of finite type over `ℂ`.
* `Belyi.Converse.toPointLFT X`: the structure morphism `X ⟶ Spec ℂ`.
* `Belyi.Converse.pointOf X x`: the `ℂ`-point `Spec ℂ ⟶ X` through a point `x` of `X^an`.

## Main results

* `Belyi.Converse.analytification_map_pointOf`: `(pointOf X x)^an` maps the point of
  `(Spec ℂ)^an` to `x`.
* `Belyi.Converse.isHomeomorph_prodMk_analytification`: if `P` is a fibre product `Z ×_ℂ T` of
  **affine** schemes of finite type over `ℂ`, the map `P^an → Z^an × T^an` induced by the two
  projections is a homeomorphism.

The proof of the latter: bijectivity comes from `ℂ`-points (points of `X^an` are the closed points
of `X`, oka's `range_analytificationπ_base`, and these are the `ℂ`-points of `X`). For the
topology, choose generators of `Γ(Z)` and `Γ(T)`; together they generate `Γ(P)` (which is the
pushout `Γ(Z) ⊗_ℂ Γ(T)`), so they define closed embeddings `Z^an → ℂⁿ`, `T^an → ℂᵐ` and
`P^an → ℂⁿ⁺ᵐ` (oka's `SchemeLFTℂ.anToAffine` and `isClosedEmbedding_analytification_map`), and the
last one is the composite of `P^an → Z^an × T^an` with the continuous map
`Z^an × T^an → ℂⁿ × ℂᵐ ≅ ℂⁿ⁺ᵐ`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Topology ComplexAnalytic

namespace Belyi.Converse

noncomputable section

/-! ### The point `Spec ℂ` -/

/-- The point `Spec ℂ`, as a scheme locally of finite type over `ℂ`. -/
abbrev pointLFT : SchemeLFTℂ.{u} :=
  SchemeLFTℂ.spec (𝟙 (CommRingCat.of (ULift.{u} ℂ))) (by
    rw [CommRingCat.hom_id]; exact RingHom.FiniteType.id _)

lemma pointLFT_obj_hom : pointLFT.{u}.obj.hom = 𝟙 _ := Spec.map_id _

/-- The structure morphism `X ⟶ Spec ℂ` of a scheme locally of finite type over `ℂ`. -/
def toPointLFT (X : SchemeLFTℂ.{u}) : X ⟶ pointLFT.{u} :=
  ObjectProperty.homMk (Over.homMk X.obj.hom (by rw [pointLFT_obj_hom]; exact Category.comp_id _))

@[simp]
lemma toPointLFT_hom_left (X : SchemeLFTℂ.{u}) : (toPointLFT X).hom.left = X.obj.hom := rfl

instance : Subsingleton (pointLFT.{u}.obj.left : Type u) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum (ULift.{u} ℂ)))

instance : Subsingleton (analytification.obj pointLFT.{u}) := by
  haveI : Subsingleton ((schemeToOverSpec.obj pointLFT.{u}.obj).left.toPresheafedSpace :
      Type u) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (ULift.{u} ℂ)))
  exact (analytificationπ_base_injective pointLFT).subsingleton

instance : Nonempty (analytification.obj pointLFT.{u}) := by
  let x : pointLFT.{u}.obj.left := IsLocalRing.closedPoint (ULift.{u} ℂ)
  have hx : IsClosed ({x} : Set pointLFT.{u}.obj.left) := by
    rw [show ({x} : Set pointLFT.{u}.obj.left) = Set.univ from
      Set.eq_univ_of_forall fun y ↦ Subsingleton.elim y x]
    exact isClosed_univ
  obtain ⟨p, -⟩ := (mem_range_analytificationπ_base_iff pointLFT x).2 hx
  exact ⟨p⟩

lemma analytification_base_comp_apply {X Y W : SchemeLFTℂ.{u}} (f : X ⟶ Y) (g : Y ⟶ W)
    (x : analytification.obj X) :
    (analytification.map (f ≫ g)).toLRSHom.base x =
      (analytification.map g).toLRSHom.base ((analytification.map f).toLRSHom.base x) := by
  rw [Functor.map_comp]
  rfl

/-- The `ℂ`-point of `X` through the closed point underlying a point `x` of `X^an`. -/
def pointOf (X : SchemeLFTℂ.{u}) (x : analytification.obj X) : pointLFT.{u} ⟶ X :=
  haveI : LocallyOfFiniteType X.obj.hom := X.property
  ObjectProperty.homMk (Over.homMk (pointOfClosedPoint X.obj.hom ((analytificationπ X).left.base x)
    ((mem_range_analytificationπ_base_iff X _).1 ⟨x, rfl⟩)) (by
      rw [pointLFT_obj_hom]
      exact pointOfClosedPoint_comp _ _ _))

/-- `(pointOf X x)^an` maps the point of `(Spec ℂ)^an` to `x`. -/
@[simp]
lemma analytification_map_pointOf (X : SchemeLFTℂ.{u}) (x : analytification.obj X)
    (p : analytification.obj pointLFT.{u}) :
    (analytification.map (pointOf X x)).toLRSHom.base p = x := by
  haveI : LocallyOfFiniteType X.obj.hom := X.property
  refine analytificationπ_base_injective X ?_
  rw [analytificationπ_base_map_apply]
  exact pointOfClosedPoint_apply _ _ _ _

/-- A morphism out of `Spec ℂ` is determined, after analytification, by its value at the point. -/
lemma analytification_map_apply_eq_of_subsingleton {X : SchemeLFTℂ.{u}} (f : pointLFT.{u} ⟶ X)
    (p q : analytification.obj pointLFT.{u}) :
    (analytification.map f).toLRSHom.base p = (analytification.map f).toLRSHom.base q := by
  rw [Subsingleton.elim p q]

/-! ### The analytification of a product -/

section Product

variable {Z T P : SchemeLFTℂ.{u}} {pZ : P ⟶ Z} {pT : P ⟶ T}

/-- The two projections from `P^an`, as a map to the product `Z^an × T^an`. -/
def analytificationProdMk (pZ : P ⟶ Z) (pT : P ⟶ T) :
    analytification.obj P → analytification.obj Z × analytification.obj T :=
  fun x ↦ ((analytification.map pZ).toLRSHom.base x, (analytification.map pT).toLRSHom.base x)

lemma continuous_analytificationProdMk (pZ : P ⟶ Z) (pT : P ⟶ T) :
    Continuous (analytificationProdMk pZ pT) :=
  (analytification.map pZ).toLRSHom.base.hom.continuous.prodMk
    (analytification.map pT).toLRSHom.base.hom.continuous

variable (h : IsPullback pZ.hom.left pT.hom.left Z.obj.hom T.obj.hom)
include h

/-- The morphism `Spec ℂ ⟶ P` with given components. -/
def pullbackPointLift (σZ : pointLFT.{u} ⟶ Z) (σT : pointLFT.{u} ⟶ T) : pointLFT.{u} ⟶ P :=
  ObjectProperty.homMk (Over.homMk (h.lift σZ.hom.left σT.hom.left
    (by rw [Over.w σZ.hom, Over.w σT.hom])) (by
      rw [← Over.w pZ.hom, IsPullback.lift_fst_assoc, Over.w σZ.hom]))

lemma pullbackPointLift_fst (σZ : pointLFT.{u} ⟶ Z) (σT : pointLFT.{u} ⟶ T) :
    pullbackPointLift h σZ σT ≫ pZ = σZ := by
  ext1
  exact Over.OverMorphism.ext (h.lift_fst _ _ _)

lemma pullbackPointLift_snd (σZ : pointLFT.{u} ⟶ Z) (σT : pointLFT.{u} ⟶ T) :
    pullbackPointLift h σZ σT ≫ pT = σT := by
  ext1
  exact Over.OverMorphism.ext (h.lift_snd _ _ _)

/-- `P^an → Z^an × T^an` is surjective. -/
theorem surjective_analytificationProdMk : Function.Surjective (analytificationProdMk pZ pT) := by
  rintro ⟨z, t⟩
  obtain ⟨p⟩ := (inferInstance : Nonempty (analytification.obj pointLFT.{u}))
  refine ⟨(analytification.map (pullbackPointLift h (pointOf Z z) (pointOf T t))).toLRSHom.base p,
    Prod.ext ?_ ?_⟩
  · change (analytification.map pZ).toLRSHom.base _ = z
    rw [← analytification_base_comp_apply, pullbackPointLift_fst, analytification_map_pointOf]
  · change (analytification.map pT).toLRSHom.base _ = t
    rw [← analytification_base_comp_apply, pullbackPointLift_snd, analytification_map_pointOf]

omit h in
/-- A ring map `ℂ[x₁, …, xₙ] → Γ(Z)` compatible with the structure maps, pulled back to `P`. -/
lemma comp_rename_eq {n m : ℕ} (s : MvPolynomial (Fin n) (ULift.{u} ℂ) →+* Γ(Z.obj.left, ⊤))
    (hs : s.comp MvPolynomial.C = Z.constMap) (pZ : P ⟶ Z)
    (e : Fin n → Fin m) (g : Fin m → Γ(P.obj.left, ⊤))
    (hg : ∀ i, g (e i) = pZ.hom.left.appTop (s (MvPolynomial.X i))) :
    (MvPolynomial.eval₂Hom P.constMap g).comp (MvPolynomial.rename e).toRingHom =
      pZ.hom.left.appTop.hom.comp s := by
  refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.rename_C, MvPolynomial.eval₂Hom_C]
    rw [← RingHom.comp_apply s MvPolynomial.C, hs]
    exact (SchemeLFTℂ.appTop_constMap pZ c).symm
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.rename_X, MvPolynomial.eval₂Hom_X']
    exact hg i

/-- If `P = Z ×_ℂ T` with `Z`, `T` affine, then `Γ(P)` is generated by the images of `Γ(Z)` and
`Γ(T)`: a subring containing both is everything. -/
lemma eq_top_of_range_le [IsAffine Z.obj.left] [IsAffine T.obj.left]
    (R₀ : Subring Γ(P.obj.left, ⊤)) (hZ : ∀ a, pZ.hom.left.appTop a ∈ R₀)
    (hT : ∀ b, pT.hom.left.appTop b ∈ R₀) : R₀ = ⊤ := by
  have hpo := isPushout_appTop_of_isPullback h
  let ι : CommRingCat.of R₀ ⟶ Γ(P.obj.left, ⊤) := CommRingCat.ofHom R₀.subtype
  let a : Γ(Z.obj.left, ⊤) ⟶ CommRingCat.of R₀ :=
    CommRingCat.ofHom (pZ.hom.left.appTop.hom.codRestrict R₀ hZ)
  let b : Γ(T.obj.left, ⊤) ⟶ CommRingCat.of R₀ :=
    CommRingCat.ofHom (pT.hom.left.appTop.hom.codRestrict R₀ hT)
  have ha : a ≫ ι = pZ.hom.left.appTop := rfl
  have hb : b ≫ ι = pT.hom.left.appTop := rfl
  have hw : Z.obj.hom.appTop ≫ a = T.obj.hom.appTop ≫ b := by
    ext x
    change (Z.obj.hom.appTop ≫ a ≫ ι) x = (T.obj.hom.appTop ≫ b ≫ ι) x
    rw [ha, hb, hpo.w]
  have hid : hpo.desc a b hw ≫ ι = 𝟙 _ := by
    refine hpo.hom_ext ?_ ?_
    · rw [IsPushout.inl_desc_assoc, ha, Category.comp_id]
    · rw [IsPushout.inr_desc_assoc, hb, Category.comp_id]
  refine eq_top_iff.2 fun x _ ↦ ?_
  have : (hpo.desc a b hw ≫ ι) x = x := by rw [hid]; rfl
  rw [← this]
  exact ((hpo.desc a b hw) x).2

/-- The continuous map `ℂⁿ × ℂᵐ → ℂⁿ⁺ᵐ` concatenating coordinates. -/
def appendCoords {n m : ℕ} (w : (ULift.{u} (Fin n) → ℂ) × (ULift.{u} (Fin m) → ℂ)) :
    ULift.{u} (Fin (n + m)) → ℂ :=
  fun k ↦ Fin.append (fun i ↦ w.1 ⟨i⟩) (fun j ↦ w.2 ⟨j⟩) k.down

omit h in
lemma continuous_appendCoords {n m : ℕ} : Continuous (appendCoords.{u} (n := n) (m := m)) := by
  refine continuous_pi fun ⟨k⟩ ↦ ?_
  induction k using Fin.addCases with
  | left i =>
    simp only [appendCoords, Fin.append_left]
    exact (continuous_apply _).comp continuous_fst
  | right j =>
    simp only [appendCoords, Fin.append_right]
    exact (continuous_apply _).comp continuous_snd

omit h in
/-- The `i`-th coordinate of the image of `z ∈ Z^an` in `ℂⁿ` under `anToAffine s` is the value
of `s(Xᵢ)` at `z`. -/
lemma anToAffine_coord {n : ℕ} {X : SchemeLFTℂ.{u}}
    (s : MvPolynomial (Fin n) (ULift.{u} ℂ) →+* Γ(X.obj.left, ⊤))
    (hs : s.comp MvPolynomial.C = X.constMap) (x : analytification.obj X) (i : Fin n) :
    ((SchemeLFTℂ.anToAffine s hs).toLRSHom.base x : ULift.{u} (Fin n) → ℂ) ⟨i⟩ =
      (analytification.obj X).eval (U := ⊤) x trivial (analytificationΓ X (s (MvPolynomial.X i))) :=
  by rw [SchemeLFTℂ.eval_analytificationΓ, affineEval_X]

omit h in
/-- Values of pulled back functions. -/
lemma eval_analytificationΓ_appTop {X Y : SchemeLFTℂ.{u}} (f : Y ⟶ X) (a : Γ(X.obj.left, ⊤))
    (y : analytification.obj Y) :
    (analytification.obj Y).eval (U := ⊤) y trivial (analytificationΓ Y (f.hom.left.appTop a)) =
      (analytification.obj X).eval (U := ⊤) ((analytification.map f).toLRSHom.base y) trivial
        (analytificationΓ X a) := by
  rw [analytificationΓ_naturality]
  exact AnalyticSpace.eval_c_app _ (analytification.map f).isCLinear (U := ⊤) y trivial _

omit h in
lemma isEmbedding_anToAffine {n : ℕ} {X : SchemeLFTℂ.{u}} [IsAffine X.obj.left]
    (s : MvPolynomial (Fin n) (ULift.{u} ℂ) →+* Γ(X.obj.left, ⊤))
    (hs : s.comp MvPolynomial.C = X.constMap) (hsurj : Function.Surjective s) :
    IsEmbedding (SchemeLFTℂ.anToAffine s hs).toLRSHom.base := by
  haveI := SchemeLFTℂ.isClosedImmersion_toAffineSpace s hs hsurj
  have h₁ := (isClosedEmbedding_analytification_map (SchemeLFTℂ.toAffineSpace s hs)).isEmbedding
  have h₂ := (AnalyticSpace.isHomeomorph_base_of_isIso
    (analytificationAffineSpaceIso.{u} n).hom).isEmbedding
  exact h₂.comp h₁

/-- **The analytification of `Z ×_ℂ T` is the product `Z^an × T^an`**, for `Z`, `T` affine: the
map induced by the two projections is an embedding. -/
theorem isEmbedding_analytificationProdMk [IsAffine Z.obj.left] [IsAffine T.obj.left] :
    IsEmbedding (analytificationProdMk pZ pT) := by
  obtain ⟨n, sZ, hsZ, hsZC⟩ := SchemeLFTℂ.exists_surjective Z
  obtain ⟨m, sT, hsT, hsTC⟩ := SchemeLFTℂ.exists_surjective T
  haveI : IsAffine P.obj.left := IsAffine.of_isPullback h
  let g : Fin (n + m) → Γ(P.obj.left, ⊤) := Fin.append
    (fun i ↦ pZ.hom.left.appTop (sZ (MvPolynomial.X i)))
    (fun j ↦ pT.hom.left.appTop (sT (MvPolynomial.X j)))
  let sP := MvPolynomial.eval₂Hom P.constMap g
  have hsPC : sP.comp MvPolynomial.C = P.constMap := MvPolynomial.eval₂Hom_comp_C _ _
  have hZ := comp_rename_eq sZ hsZC pZ (Fin.castAdd m) g (fun i ↦ Fin.append_left _ _ i)
  have hT := comp_rename_eq sT hsTC pT (Fin.natAdd n) g (fun j ↦ Fin.append_right _ _ j)
  have hsP : Function.Surjective sP := by
    have := eq_top_of_range_le h sP.range
      (fun a ↦ by
        obtain ⟨p, rfl⟩ := hsZ a
        exact ⟨_, congrArg (fun φ : _ →+* _ ↦ φ p) hZ⟩)
      (fun b ↦ by
        obtain ⟨p, rfl⟩ := hsT b
        exact ⟨_, congrArg (fun φ : _ →+* _ ↦ φ p) hT⟩)
    exact RingHom.range_eq_top.1 this
  let EZ := SchemeLFTℂ.anToAffine sZ hsZC
  let ET := SchemeLFTℂ.anToAffine sT hsTC
  let EP := SchemeLFTℂ.anToAffine sP hsPC
  have hEP := isEmbedding_anToAffine sP hsPC hsP
  let G : analytification.obj Z × analytification.obj T → ULift.{u} (Fin (n + m)) → ℂ :=
    fun w ↦ appendCoords (EZ.toLRSHom.base w.1, ET.toLRSHom.base w.2)
  have hG : Continuous G := continuous_appendCoords.comp
    ((EZ.toLRSHom.base.hom.continuous.comp continuous_fst).prodMk
      (ET.toLRSHom.base.hom.continuous.comp continuous_snd))
  have hkey : (fun x ↦ (EP.toLRSHom.base x : ULift.{u} (Fin (n + m)) → ℂ)) =
      G ∘ analytificationProdMk pZ pT := by
    funext x ⟨k⟩
    induction k using Fin.addCases with
    | left i =>
      simp only [Function.comp_apply, G, appendCoords, Fin.append_left, analytificationProdMk]
      rw [anToAffine_coord, anToAffine_coord]
      simp only [sP, MvPolynomial.eval₂Hom_X', g, Fin.append_left]
      exact eval_analytificationΓ_appTop pZ _ x
    | right j =>
      simp only [Function.comp_apply, G, appendCoords, Fin.append_right, analytificationProdMk]
      rw [anToAffine_coord, anToAffine_coord]
      simp only [sP, MvPolynomial.eval₂Hom_X', g, Fin.append_right]
      exact eval_analytificationΓ_appTop pT _ x
  refine IsEmbedding.of_comp (continuous_analytificationProdMk pZ pT) hG ?_
  rw [← hkey]
  exact hEP

/-- **The analytification of `Z ×_ℂ T` is the product `Z^an × T^an`**, for `Z`, `T` affine. -/
theorem isHomeomorph_analytificationProdMk [IsAffine Z.obj.left] [IsAffine T.obj.left] :
    IsHomeomorph (analytificationProdMk pZ pT) :=
  isHomeomorph_iff_isEmbedding_surjective.2
    ⟨isEmbedding_analytificationProdMk h, surjective_analytificationProdMk h⟩

end Product

end

end Belyi.Converse
