/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Belyi.Converse.Pi1Invariance
import Pi1.FundamentalGroup.TwoCharts

/-!
# Bijectivity of `π₁ᵉᵗ(g)` from two charts

Let `X = U ∪ U'` satisfy the hypotheses of pi1's étale van Kampen theorem
`AlgebraicGeometry.FiniteEtale.ker_fundamentalGroupMap_eq`, and let `g : X' ⟶ X` be a morphism
with opens `V, V' ⊆ X'` mapping to `U, U'` (via `rU : V ⟶ U`, `rU' : V' ⟶ U'`,
`rI : V ∩ V' ⟶ U ∩ U'`, compatible with the inclusions). If `π₁ᵉᵗ(V ∩ V') → π₁ᵉᵗ(U ∩ U')` is
surjective, `π₁ᵉᵗ(V) → π₁ᵉᵗ(U)` bijective and `π₁ᵉᵗ(V') → π₁ᵉᵗ(U')` injective, and
`π₁ᵉᵗ(V) → π₁ᵉᵗ(X')` is surjective, then `π₁ᵉᵗ(X') → π₁ᵉᵗ(X)` is bijective
(`AlgebraicGeometry.FiniteEtale.fundamentalGroupMap_bijective_of_charts`).

This reduces the invariance of `π₁ᵉᵗ` of a curve under extension of algebraically closed fields
(INV-2) to the affine case (`fundamentalGroupMap_baseChange_bijective_of_isAlgClosed`) on two
affine charts and their intersection. Note that no van Kampen theorem is needed for `X'`: the
relations of `π₁ᵉᵗ(X)` already hold in `π₁ᵉᵗ(X')` by functoriality.

## Main results

* `MonoidHom.injective_of_ker_eq_topologicalClosure`: the group-theoretic core.
* `AlgebraicGeometry.FiniteEtale.fundamentalGroupMap_bijective_of_charts`.
* `AlgebraicGeometry.FiniteEtale.fundamentalGroupMap_bijective_of_isPullback`: INV-1 for any
  base change square `Y' ⟶ Y` of `Spec Ω ⟶ Spec k` with `Y ≅ Spec R` affine, connected, of finite
  type over `k` (the form needed on the charts).
-/

universe u

open CategoryTheory
open scoped TensorProduct

/-- **The group-theoretic core.** Consider commutative squares
`βA ∘ μ' = μ ∘ βP`, `βB ∘ ν' = ν ∘ βP`, `βC ∘ ψ' = ψ ∘ βA` of groups, with
`ker ψ = ⟨⟨μ (ker ν)⟩⟩` (closed normal closure), `μ' (ker ν') ⊆ ker ψ'`, `ψ'` surjective and
continuous, `βP` surjective, `βB` injective and `βA` a continuous bijection from a compact group.
Then `βC` is injective. -/
theorem MonoidHom.injective_of_ker_eq_topologicalClosure {P' P A' A B' B C' C : Type*}
    [Group P'] [Group P] [Group A'] [Group A] [Group B'] [Group B] [Group C'] [Group C]
    [TopologicalSpace A'] [CompactSpace A'] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] [TopologicalSpace C'] [T1Space C']
    (μ' : P' →* A') (ν' : P' →* B') (ψ' : A' →* C') (μ : P →* A) (ν : P →* B) (ψ : A →* C)
    (βP : P' →* P) (βA : A' →* A) (βB : B' →* B) (βC : C' →* C)
    (hA : ∀ p, βA (μ' p) = μ (βP p)) (hB : ∀ p, βB (ν' p) = ν (βP p))
    (hC : ∀ a, βC (ψ' a) = ψ (βA a))
    (hker : ψ.ker = (Subgroup.normalClosure (μ '' ν.ker)).topologicalClosure)
    (hμ' : ∀ p, ν' p = 1 → ψ' (μ' p) = 1) (hψ' : Continuous ψ') (hψ's : Function.Surjective ψ')
    (hβP : Function.Surjective βP) (hβA : Function.Bijective βA) (hβAc : Continuous βA)
    (hβB : Function.Injective βB) : Function.Injective βC := by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨a, rfl⟩ := hψ's c
  have hψa : βA a ∈ ψ.ker := by rw [MonoidHom.mem_ker, ← hC, hc]
  have hMc : IsClosed (ψ'.ker : Set A') := by
    have : (ψ'.ker : Set A') = ψ' ⁻¹' {1} := by ext; simp
    rw [this]
    exact isClosed_singleton.preimage hψ'
  haveI : (ψ'.ker.map βA).Normal := (MonoidHom.normal_ker ψ').map βA hβA.2
  have hMc' : IsClosed ((ψ'.ker.map βA : Subgroup A) : Set A) := by
    rw [Subgroup.coe_map]
    exact (hMc.isCompact.image hβAc).isClosed
  have hle : ψ.ker ≤ ψ'.ker.map βA := by
    rw [hker]
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hMc'
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨p', rfl⟩ := hβP p
    refine ⟨μ' p', ?_, hA p'⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hp ⊢
    refine hμ' p' (hβB ?_)
    rw [hB, hp, map_one]
  obtain ⟨m, hm, hma⟩ := hle hψa
  rw [← hβA.1 hma]
  exact hm

namespace AlgebraicGeometry.FiniteEtale

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (U U' : X.Opens) (V V' : X'.Opens)
  (rU : (V : Scheme) ⟶ U) (rU' : (V' : Scheme) ⟶ U')
  (rI : ((V ⊓ V' : X'.Opens) : Scheme) ⟶ ((U ⊓ U' : X.Opens) : Scheme))

/-- **`π₁ᵉᵗ(X') → π₁ᵉᵗ(X)` is bijective if it is so on two charts.** See the module docstring. -/
theorem fundamentalGroupMap_bijective_of_charts (hUU' : U ⊔ U' = ⊤) [ConnectedSpace X]
    [ConnectedSpace U] [ConnectedSpace U'] [ConnectedSpace (U ⊓ U' : X.Opens)]
    [QuasiCompact U.ι] [QuasiCompact (incl₂ U U')] [IsIso U.ι.fromNormalization]
    [IsIso (incl₂ U U').fromNormalization] [IsReduced X] [IsLocallyNoetherian X]
    [ConnectedSpace X'] [ConnectedSpace V] [QuasiCompact V.ι] [IsIso V.ι.fromNormalization]
    (hgU : V.ι ≫ g = rU ≫ U.ι) (hI₁ : incl₁ V V' ≫ rU = rI ≫ incl₁ U U')
    (hI₂ : incl₂ V V' ≫ rU' = rI ≫ incl₂ U U')
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ζ : Spec (.of Ω) ⟶ (V ⊓ V' : X'.Opens))
    (hP : Function.Surjective (fundamentalGroupMap rI (rfl : ζ ≫ rI = _)))
    (hA : Function.Bijective (fundamentalGroupMap rU
      (by rw [Category.assoc, hI₁, ← Category.assoc] :
        (ζ ≫ incl₁ V V') ≫ rU = (ζ ≫ rI) ≫ incl₁ U U')))
    (hB : Function.Injective (fundamentalGroupMap rU'
      (by rw [Category.assoc, hI₂, ← Category.assoc] :
        (ζ ≫ incl₂ V V') ≫ rU' = (ζ ≫ rI) ≫ incl₂ U U'))) :
    Function.Bijective (fundamentalGroupMap g
      (by rw [Category.assoc, hgU, ← Category.assoc, Category.assoc ζ, hI₁, ← Category.assoc] :
        ((ζ ≫ incl₁ V V') ≫ V.ι) ≫ g = (((ζ ≫ rI) ≫ incl₁ U U') ≫ U.ι))) := by
  have h₁ : (ζ ≫ incl₁ V V') ≫ rU = (ζ ≫ rI) ≫ incl₁ U U' := by
    rw [Category.assoc, hI₁, ← Category.assoc]
  have h₂ : (ζ ≫ incl₂ V V') ≫ rU' = (ζ ≫ rI) ≫ incl₂ U U' := by
    rw [Category.assoc, hI₂, ← Category.assoc]
  have hg : ((ζ ≫ incl₁ V V') ≫ V.ι) ≫ g = (((ζ ≫ rI) ≫ incl₁ U U') ≫ U.ι) := by
    rw [Category.assoc, hgU, ← Category.assoc, h₁]
  -- the commutative squares
  have sqA (p : π₁ᵉᵗ(ζ)) : fundamentalGroupMap rU h₁ (fundamentalGroupMap (incl₁ V V') rfl p) =
      fundamentalGroupMap (incl₁ U U') rfl (fundamentalGroupMap rI rfl p) := by
    have hh1 : ζ ≫ incl₁ V V' ≫ rU = (ζ ≫ rI) ≫ incl₁ U U' := by
      rw [← Category.assoc]; exact h₁
    have hh2 : ζ ≫ rI ≫ incl₁ U U' = (ζ ≫ rI) ≫ incl₁ U U' := (Category.assoc _ _ _).symm
    have e1 := DFunLike.congr_fun (fundamentalGroupMap_comp (incl₁ V V') rU rfl h₁ hh1) p
    have e2 := DFunLike.congr_fun (fundamentalGroupMap_comp rI (incl₁ U U') rfl rfl hh2) p
    rw [fundamentalGroupMap_congr hI₁ _ hh2] at e1
    exact e1.symm.trans e2
  have sqB (p : π₁ᵉᵗ(ζ)) : fundamentalGroupMap rU' h₂ (fundamentalGroupMap (incl₂ V V') rfl p) =
      fundamentalGroupMap (incl₂ U U') rfl (fundamentalGroupMap rI rfl p) := by
    have hh1 : ζ ≫ incl₂ V V' ≫ rU' = (ζ ≫ rI) ≫ incl₂ U U' := by
      rw [← Category.assoc]; exact h₂
    have hh2 : ζ ≫ rI ≫ incl₂ U U' = (ζ ≫ rI) ≫ incl₂ U U' := (Category.assoc _ _ _).symm
    have e1 := DFunLike.congr_fun (fundamentalGroupMap_comp (incl₂ V V') rU' rfl h₂ hh1) p
    have e2 := DFunLike.congr_fun (fundamentalGroupMap_comp rI (incl₂ U U') rfl rfl hh2) p
    rw [fundamentalGroupMap_congr hI₂ _ hh2] at e1
    exact e1.symm.trans e2
  have sqC (a : π₁ᵉᵗ(ζ ≫ incl₁ V V')) :
      fundamentalGroupMap g hg (fundamentalGroupMap V.ι rfl a) =
        fundamentalGroupMap U.ι rfl (fundamentalGroupMap rU h₁ a) := by
    have hh1 : (ζ ≫ incl₁ V V') ≫ V.ι ≫ g = ((ζ ≫ rI) ≫ incl₁ U U') ≫ U.ι := by
      rw [← Category.assoc]; exact hg
    have hh2 : (ζ ≫ incl₁ V V') ≫ rU ≫ U.ι = ((ζ ≫ rI) ≫ incl₁ U U') ≫ U.ι := by
      rw [← Category.assoc, h₁]
    have e1 := DFunLike.congr_fun (fundamentalGroupMap_comp V.ι g rfl hg hh1) a
    have e2 := DFunLike.congr_fun (fundamentalGroupMap_comp rU U.ι h₁ rfl hh2) a
    rw [fundamentalGroupMap_congr hgU _ hh2] at e1
    exact e1.symm.trans e2
  -- the relations of `π₁ᵉᵗ(X)` hold in `π₁ᵉᵗ(X')`
  have hμ' (p : π₁ᵉᵗ(ζ)) (hp : fundamentalGroupMap (incl₂ V V') rfl p = 1) :
      fundamentalGroupMap V.ι rfl (fundamentalGroupMap (incl₁ V V') rfl p) = 1 := by
    have hV2 : (ζ ≫ incl₂ V V') ≫ V'.ι = (ζ ≫ incl₁ V V') ≫ V.ι := by
      simp only [Category.assoc, incl₁_ι]
    have hh : ζ ≫ incl₂ V V' ≫ V'.ι = (ζ ≫ incl₁ V V') ≫ V.ι := by
      rw [← Category.assoc]; exact hV2
    have e1 := DFunLike.congr_fun (fundamentalGroupMap_comp (incl₁ V V') V.ι rfl rfl
      (Category.assoc _ _ _).symm) p
    have e2 := DFunLike.congr_fun (fundamentalGroupMap_comp (incl₂ V V') V'.ι rfl hV2 hh) p
    rw [fundamentalGroupMap_congr (incl₁_ι V V') _ hh] at e1
    refine e1.symm.trans (e2.trans ?_)
    change fundamentalGroupMap V'.ι hV2 (fundamentalGroupMap (incl₂ V V') rfl p) = 1
    rw [hp, map_one]
  have hψ' := fundamentalGroupMap_surjective_of_isIso_fromNormalization V.ι
    (rfl : (ζ ≫ incl₁ V V') ≫ V.ι = _)
  have hψ := fundamentalGroupMap_surjective_of_isIso_fromNormalization U.ι
    (rfl : ((ζ ≫ rI) ≫ incl₁ U U') ≫ U.ι = _)
  refine ⟨MonoidHom.injective_of_ker_eq_topologicalClosure
    (fundamentalGroupMap (incl₁ V V') rfl).toMonoidHom
    (fundamentalGroupMap (incl₂ V V') rfl).toMonoidHom
    (fundamentalGroupMap V.ι rfl).toMonoidHom
    (fundamentalGroupMap (incl₁ U U') rfl).toMonoidHom
    (fundamentalGroupMap (incl₂ U U') rfl).toMonoidHom
    (fundamentalGroupMap U.ι rfl).toMonoidHom
    (fundamentalGroupMap rI rfl).toMonoidHom (fundamentalGroupMap rU h₁).toMonoidHom
    (fundamentalGroupMap rU' h₂).toMonoidHom (fundamentalGroupMap g hg).toMonoidHom
    sqA sqB sqC (ker_fundamentalGroupMap_eq U U' hUU' (ζ ≫ rI)) hμ'
    (fundamentalGroupMap V.ι _).continuous hψ' hP hA (fundamentalGroupMap rU h₁).continuous hB,
    fun c => ?_⟩
  obtain ⟨a, rfl⟩ := hψ c
  obtain ⟨a', rfl⟩ := hA.2 a
  exact ⟨fundamentalGroupMap V.ι rfl a', sqC a'⟩

section Affine

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed k] [CharZero k]
  [Countable k] [IsAlgClosed Ω]

/-- **INV-1 for base change squares.** If `g : Y' ⟶ Y` is the base change of
`Spec Ω ⟶ Spec k` along `q : Y ⟶ Spec k`, where `Y ≅ Spec R` with `R` connected of finite type
over `k` (compatibly with `q`), then `π₁ᵉᵗ(Y') → π₁ᵉᵗ(Y)` is bijective at every geometric
point. -/
theorem fundamentalGroupMap_bijective_of_isPullback {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (p : Y' ⟶ Spec (.of Ω)) (q : Y ⟶ Spec (.of k))
    (H : IsPullback g p q (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))
    (R : Type u) [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    [ConnectedSpace (Spec (.of R))] (e : Y ≅ Spec (.of R))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = q)
    {L : Type u} [Field L] [IsSepClosed L] (x : Spec (.of L) ⟶ Y') :
    Function.Bijective (fundamentalGroupMap g (rfl : x ≫ g = _)) := by
  have H' : IsPullback (baseChangeSpec k Ω R ≫ e.inv)
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : Ω →ₐ[k] Ω ⊗[k] R).toRingHom))
      q (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) :=
    isPullback_baseChangeSpec.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc, Iso.refl_hom,
        Category.comp_id]) (by simp)
  let eY := H.isoIsPullback _ _ H'
  have hg : eY.hom ≫ baseChangeSpec k Ω R ≫ e.inv = g := H.isoIsPullback_hom_fst _ _ H'
  have h4 : ((x ≫ eY.hom) ≫ baseChangeSpec k Ω R) ≫ e.inv = x ≫ g := by
    simp only [Category.assoc, hg]
  have h5 : x ≫ eY.hom ≫ baseChangeSpec k Ω R ≫ e.inv = x ≫ g := by rw [hg]
  have h6 : (x ≫ eY.hom) ≫ baseChangeSpec k Ω R ≫ e.inv = x ≫ g := by
    rw [Category.assoc, hg]
  have key : ⇑(fundamentalGroupMap g (rfl : x ≫ g = _)) =
      ⇑(fundamentalGroupMap e.inv h4) ∘
        ⇑(fundamentalGroupMap (baseChangeSpec k Ω R) (rfl : (x ≫ eY.hom) ≫ _ = _)) ∘
          ⇑(fundamentalGroupMap eY.hom (rfl : x ≫ eY.hom = _)) := by
    funext a
    rw [fundamentalGroupMap_congr hg.symm _ h5,
      DFunLike.congr_fun (fundamentalGroupMap_comp eY.hom (baseChangeSpec k Ω R ≫ e.inv) rfl h6
        h5) a]
    exact DFunLike.congr_fun (fundamentalGroupMap_comp (baseChangeSpec k Ω R) e.inv rfl h4 h6) _
  rw [key]
  exact (fundamentalGroupMap_bijective_of_isIso _ h4).comp
    ((fundamentalGroupMap_baseChange_bijective_of_isAlgClosed (x ≫ eY.hom)).comp
      (fundamentalGroupMap_bijective_of_isIso _ rfl))

end Affine

end AlgebraicGeometry.FiniteEtale
