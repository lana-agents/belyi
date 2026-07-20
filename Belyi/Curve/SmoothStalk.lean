/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.Curve.B1
import Belyi.Curve.B1Surjective
import Belyi.KaehlerRank

/-!
# Stalks of a smooth curve are valuation rings (last blocker of B1)

Taxis issue #75, scheme-side glue.  The commutative-algebra core is in
`Belyi/KaehlerRank.lean`: a local localization `B` of a chart ring `A` that is standard
smooth of relative dimension `1` over `k` is a valuation ring of Krull dimension `≤ 1`
(`Belyi.valuationRing_of_standardSmooth_localization`,
`Belyi.krullDimLE_one_of_standardSmooth_localization`).  This file supplies the missing
scheme-theoretic identification:

* `AlgebraicGeometry.SmoothOfRelativeDimension` unfolds, around any `x : X`, to an affine
  chart `V ∋ x` on which the induced ring map `Γ(Spec k, U) ⟶ Γ(X, V)` is standard smooth
  of relative dimension `1`
  (`SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension`);
* the base `U` is forced to be `⊤` since `Spec k` has a single point, so `Γ(Spec k, U) ≅ k`
  and `A := Γ(X, V)` is a standard smooth `k`-algebra of relative dimension `1`;
* the stalk `𝒪_{X,x}` is the localization of `A` at the prime of `x`
  (`IsAffineOpen.isLocalization_stalk`).

Feeding this to the two lemmas above yields, for a smooth curve over a perfect field, the
hypotheses `hX` and `hdim` of `Belyi.isFinite_homOfFunctionField` — making **B1
unconditional** (`Belyi.isFinite_homOfFunctionField_of_isCurveOver`).

The perfect-field hypothesis discharges the residue-field formal smoothness that is the
delicate point over non-perfect base fields; it is satisfied in characteristic zero, in
particular over `ℂ`, which is all the Belyi project needs.
-/

universe u

namespace Belyi

open AlgebraicGeometry CategoryTheory IsLocalRing TensorProduct

section SmoothStalk

variable (k : Type u) [Field k] [PerfectField k] (X : Scheme.{u})
  [inst_over : X.Over (Spec (CommRingCat.of k))]
  [inst_smooth : SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  [IsIntegral X]

include inst_over inst_smooth

/-- **Stalks of a smooth curve are valuation rings of Krull dimension `≤ 1`.**  For a
scheme `X` over a perfect field `k` whose structure morphism is smooth of relative
dimension `1` (and which is integral and locally Noetherian), every stalk is a valuation
ring of Krull dimension at most `1`. -/
theorem valuationRing_and_krullDimLE_stalk_of_smooth (x : X) :
    ValuationRing (X.presheaf.stalk x) ∧ Ring.KrullDimLE 1 (X.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hxV, hVU, hss⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 1) (f := X ↘ Spec (CommRingCat.of k)) x
  set φ := ((X ↘ Spec (CommRingCat.of k)).appLE U V hVU).hom
  -- `Spec k` is a single point, so the base chart `U` is `⊤`.
  have hfx : (X ↘ Spec (CommRingCat.of k)).base x ∈ U := hVU hxV
  have hUtop : U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true, SetLike.mem_coe]
    rw [Subsingleton.elim y ((X ↘ Spec (CommRingCat.of k)).base x)]
    exact hfx
  -- Identify the source ring `Γ(Spec k, U)` with `k`.
  let ι : Γ(Spec (CommRingCat.of k), U) ≅ CommRingCat.of k :=
    (Spec (CommRingCat.of k)).presheaf.mapIso (eqToIso (congrArg Opposite.op hUtop)) ≪≫
      Scheme.ΓSpecIso (CommRingCat.of k)
  let e : Γ(Spec (CommRingCat.of k), U) ≃+* k := ι.commRingCatIsoToRingEquiv
  -- Put a `k`-algebra structure on `A := Γ(X, V)` via `φ ∘ e⁻¹`, standard smooth of dim 1.
  letI algA : Algebra k Γ(X, V) := (φ.comp (e.symm : k →+* _)).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 k Γ(X, V) := by
    have he0 := RingHom.IsStandardSmoothOfRelativeDimension.equiv e.symm
    have hc := hss.comp he0
    rw [Nat.add_zero] at hc
    exact hc
  haveI : Algebra.IsStandardSmooth k Γ(X, V) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  -- The stalk is the localization of `A` at the prime of `x`.
  letI algAB : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  set M := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
  haveI hlocB : IsLocalization M (X.presheaf.stalk x) := hV.isLocalization_stalk ⟨x, hxV⟩
  -- `k`-algebra structure on the stalk, compatible with the tower.
  letI algkB : Algebra k (X.presheaf.stalk x) :=
    ((algebraMap Γ(X, V) (X.presheaf.stalk x)).comp (algebraMap k Γ(X, V))).toAlgebra
  haveI : IsScalarTower k Γ(X, V) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- Ring-theoretic side conditions.
  haveI : Nontrivial Γ(X, V) := by
    refine ⟨1, 0, fun h => one_ne_zero (α := X.presheaf.stalk x) ?_⟩
    rw [← map_one (algebraMap Γ(X, V) (X.presheaf.stalk x)),
      ← map_zero (algebraMap Γ(X, V) (X.presheaf.stalk x)), h]
  haveI : Algebra.EssFiniteType Γ(X, V) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization (S := X.presheaf.stalk x) M
  haveI : Algebra.EssFiniteType k (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.comp k Γ(X, V) (X.presheaf.stalk x)
  haveI : IsNoetherianRing (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.isNoetherianRing k (X.presheaf.stalk x)
  haveI : Algebra.EssFiniteType k (ResidueField (X.presheaf.stalk x)) :=
    inferInstanceAs
      (Algebra.EssFiniteType k (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x)))
  haveI : Algebra.FormallySmooth k (ResidueField (X.presheaf.stalk x)) := inferInstance
  exact ⟨valuationRing_of_standardSmooth_localization k Γ(X, V) M (X.presheaf.stalk x),
    krullDimLE_one_of_standardSmooth_localization k Γ(X, V) M (X.presheaf.stalk x)⟩

/-- Stalks of a smooth curve are valuation rings: the hypothesis `hX` of
`Belyi.isFinite_homOfFunctionField`. -/
theorem valuationRing_stalk_of_smooth (x : X) : ValuationRing (X.presheaf.stalk x) :=
  (valuationRing_and_krullDimLE_stalk_of_smooth k X x).1

/-- Stalks of a smooth curve have Krull dimension `≤ 1`: the hypothesis `hdim` of
`Belyi.isFinite_homOfFunctionField`. -/
theorem krullDimLE_one_stalk_of_smooth (x : X) : Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
  (valuationRing_and_krullDimLE_stalk_of_smooth k X x).2

end SmoothStalk

section Curve

variable (k : Type u) [Field k] [PerfectField k] (X : Scheme.{u})
  [inst_over : X.Over (Spec (CommRingCat.of k))] [inst_curve : IsCurveOver k X]
  [IsIntegral X]

include inst_over inst_curve

/-- **Stalks of a curve over a perfect field are valuation rings** (taxis issue #75): the
hypothesis `hX` of `Belyi.homOfFunctionField` and `Belyi.isFinite_homOfFunctionField`,
now discharged unconditionally.  (`IsIntegral X` is `Belyi.IsCurveOver.isIntegral`.) -/
theorem valuationRing_stalk_of_isCurveOver (x : X) : ValuationRing (X.presheaf.stalk x) :=
  valuationRing_stalk_of_smooth k X x

/-- **Stalks of a curve over a perfect field have Krull dimension `≤ 1`** (taxis issue #75):
the hypothesis `hdim` of `Belyi.isFinite_homOfFunctionField`, now discharged
unconditionally. -/
theorem krullDimLE_one_stalk_of_isCurveOver (x : X) :
    Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
  krullDimLE_one_stalk_of_smooth k X x

/-- **B1, unconditional.** For a curve `X` over a perfect field `k` and a transcendental
`t ∈ K(X)`, the induced morphism `X ⟶ ℙ¹` is finite.  The stalk hypotheses of
`Belyi.isFinite_homOfFunctionField` are supplied by
`Belyi.valuationRing_stalk_of_isCurveOver` and `Belyi.krullDimLE_one_stalk_of_isCurveOver`,
so no side hypotheses on the local rings remain. -/
theorem isFinite_homOfFunctionField_of_isCurveOver {t : X.functionField}
    (ht : Transcendental k t) :
    IsFinite (homOfFunctionField k X (valuationRing_stalk_of_isCurveOver k X) t) :=
  isFinite_homOfFunctionField k X (valuationRing_stalk_of_isCurveOver k X)
    (krullDimLE_one_stalk_of_isCurveOver k X) ht

/-- **B1, surjectivity, unconditional.** For a curve `X` over a perfect field `k` and a
transcendental `t ∈ K(X)`, the induced morphism `X ⟶ ℙ¹` is surjective.  The stalk
hypotheses of `Belyi.surjective_homOfFunctionField` are supplied by
`Belyi.valuationRing_stalk_of_isCurveOver` and `Belyi.krullDimLE_one_stalk_of_isCurveOver`,
so no side hypotheses on the local rings remain. -/
theorem surjective_homOfFunctionField_of_isCurveOver {t : X.functionField}
    (ht : Transcendental k t) :
    Function.Surjective
      (homOfFunctionField k X (valuationRing_stalk_of_isCurveOver k X) t).base :=
  surjective_homOfFunctionField k X (valuationRing_stalk_of_isCurveOver k X)
    (krullDimLE_one_stalk_of_isCurveOver k X) ht

/-- **B1, main theorem, unconditional.** For a curve `X` over a perfect field `k` and a
transcendental `t ∈ K(X)`, the induced morphism `X ⟶ ℙ¹` is finite **and** surjective —
every such curve admits a finite surjective morphism to `ℙ¹`.  This is the fully
unconditional form of `Belyi.isFinite_and_surjective_homOfFunctionField`, with the stalk
hypotheses discharged by issue #75. -/
theorem isFinite_and_surjective_homOfFunctionField_of_isCurveOver {t : X.functionField}
    (ht : Transcendental k t) :
    IsFinite (homOfFunctionField k X (valuationRing_stalk_of_isCurveOver k X) t) ∧
      Function.Surjective
        (homOfFunctionField k X (valuationRing_stalk_of_isCurveOver k X) t).base :=
  ⟨isFinite_homOfFunctionField_of_isCurveOver k X ht,
    surjective_homOfFunctionField_of_isCurveOver k X ht⟩

end Curve

end Belyi
