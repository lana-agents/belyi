/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.Algebra.Algebra.Subalgebra.Directed

/-!
# `Spec K` as a cofiltered limit of `Spec Rᵢ` over finitely generated subalgebras

This file is the *producer* half of statement **B10(i)** of the converse direction of Belyi's
theorem (`references/converse-design.md` §3a/§4; taxis issue #196): it presents `Spec K`, for a
`k`-algebra `K`, as the cofiltered limit of `Spec Rᵢ` over the diagram of finitely generated
`k`-subalgebras `Rᵢ ⊆ K` with the inclusion (affine) transition maps.

This is the input the `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` machinery consumes
to descend a finite-presentation morphism and scheme over `K` to a finite-type subfield.

## Main definitions

* `Belyi.SpecLimit.FGSub k K`: the index category — finitely generated `k`-subalgebras of `K`,
  ordered by inclusion; filtered (directed, nonempty).
* `Belyi.SpecLimit.ringDiagram k K`: the diagram `FGSub k K ⥤ CommRingCat`, `R ↦ R`.
* `Belyi.SpecLimit.ringCocone k K`: the cocone with tip `K` and the subalgebra inclusions.
* `Belyi.SpecLimit.schemeDiagram k K`: the diagram `(FGSub k K)ᵒᵖ ⥤ Scheme`, `R ↦ Spec R`.
* `Belyi.SpecLimit.schemeCone k K`: the cone with tip `Spec K`.

## Main results

* `Belyi.SpecLimit.isColimitRingCocone`: `K = colim Rᵢ` in `CommRingCat`.
* `Belyi.SpecLimit.isLimitSchemeCone`: `Spec K = lim Spec Rᵢ` in `Scheme`.
* The instances (`IsCofiltered`, affine transition maps, compact/quasi-separated fibres) the
  `AffineTransitionLimit` lemmas require.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace Belyi.SpecLimit

variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]

/-- The index category: finitely generated `k`-subalgebras of `K`, ordered by inclusion. -/
abbrev FGSub : Type u := {R : Subalgebra k K // R.FG}

instance : Preorder (FGSub k K) := Subtype.preorder _

/-- The finitely generated subalgebras are directed upward by inclusion (join of two f.g.
subalgebras is f.g.). -/
instance : IsDirected (FGSub k K) (· ≤ ·) where
  directed R S :=
    ⟨⟨(R.1 ⊔ S.1), R.2.sup S.2⟩,
      Subtype.coe_le_coe.mp le_sup_left, Subtype.coe_le_coe.mp le_sup_right⟩

instance : Nonempty (FGSub k K) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

/-- The diagram `R ↦ R` (as a plain commutative ring) indexed by finitely generated
`k`-subalgebras of `K`. -/
@[simps]
noncomputable def ringDiagram : FGSub k K ⥤ CommRingCat.{u} where
  obj R := CommRingCat.of R.1
  map {R S} h := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom h)).toRingHom
  map_id R := by ext x; rfl
  map_comp {R S T} h h' := by ext x; rfl

/-- The cocone over `ringDiagram` with tip `K`, given by the subalgebra inclusions `Rᵢ ↪ K`. -/
@[simps]
noncomputable def ringCocone : Cocone (ringDiagram k K) where
  pt := CommRingCat.of K
  ι :=
    { app R := CommRingCat.ofHom R.1.val.toRingHom
      naturality {R S} h := by ext x; rfl }

/-- Every element of `K` lies in a finitely generated `k`-subalgebra (namely `k[x]`). -/
lemma exists_mem_fg (x : K) : ∃ R : FGSub k K, x ∈ R.1 :=
  ⟨⟨Algebra.adjoin k ↑({x} : Finset K), Subalgebra.fg_adjoin_finset _⟩,
    Algebra.subset_adjoin (by simp)⟩

/-- `K` is the colimit of its finitely generated `k`-subalgebras. -/
noncomputable def isColimitRingCocone : IsColimit (ringCocone k K) := by
  have : PreservesColimit (ringDiagram k K) (forget CommRingCat.{u}) := inferInstance
  have : ReflectsColimit (ringDiagram k K) (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget CommRingCat.{u})
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨R, hxR⟩ := exists_mem_fg k K x
    exact ⟨R, ⟨x, hxR⟩, rfl⟩
  · intro R x y h
    refine ⟨R, 𝟙 R, ?_⟩
    have hxy : x = y := Subtype.ext h
    rw [hxy]

/-- The scheme-level diagram `Spec Rᵢ`, indexed by `(FGSub k K)ᵒᵖ`. -/
noncomputable def schemeDiagram : (FGSub k K)ᵒᵖ ⥤ Scheme.{u} :=
  (ringDiagram k K).op ⋙ Scheme.Spec

/-- The cone over `schemeDiagram` with tip `Spec K`. -/
noncomputable def schemeCone : Cone (schemeDiagram k K) :=
  Scheme.Spec.mapCone (ringCocone k K).op

/-- `Spec K` is the cofiltered limit of `Spec Rᵢ` over the finitely generated
`k`-subalgebras `Rᵢ ⊆ K`. -/
noncomputable def isLimitSchemeCone : IsLimit (schemeCone k K) :=
  isLimitOfPreserves Scheme.Spec (isColimitRingCocone k K).op

instance (R : (FGSub k K)ᵒᵖ) : IsAffine ((schemeDiagram k K).obj R) :=
  inferInstanceAs (IsAffine (Spec _))

instance {R S : (FGSub k K)ᵒᵖ} (h : R ⟶ S) : IsAffineHom ((schemeDiagram k K).map h) :=
  isAffineHom_of_isAffine _

instance (R : (FGSub k K)ᵒᵖ) : CompactSpace ((schemeDiagram k K).obj R) :=
  inferInstanceAs (CompactSpace (Spec _))

instance (R : (FGSub k K)ᵒᵖ) : QuasiSeparatedSpace ((schemeDiagram k K).obj R) :=
  inferInstanceAs (QuasiSeparatedSpace (Spec _))

end Belyi.SpecLimit
