/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.CurveField.Point
import Belyi.CurveField.ZerosPoles

/-!
# Places and points in finite extensions of curve fields

Let `L / K` be a finite extension of curve fields (a finite morphism of curves `Y → X`).

* Every place `Q` of `L` restricts to a place `Q.restrict K = Q ∩ K` of `K`
  (`Belyi.CurveField.Place.restrict`); restriction is surjective
  (`Belyi.CurveField.Place.exists_restrict_eq`) with finite fibres
  (`Belyi.CurveField.Place.finite_setOf_restrict_eq`).
* The ramification index `e(Q|P)` (`Belyi.CurveField.Place.ramificationIdx`) satisfies
  `ord_Q (f) = e(Q|P) · ord_P (f)` for `f ∈ K` (`Belyi.CurveField.Place.ord_algebraMap`).
* The residue field `κ(Q)` is an extension of `κ(P)` of degree `f(Q|P) ≤ [L : K]`
  (`Belyi.CurveField.Place.inertiaDeg`, `Belyi.CurveField.Place.inertiaDeg_le_finrank`), and
  `deg Q = f(Q|P) · deg P` (`Belyi.CurveField.Place.deg_eq_inertiaDeg_mul`).
* Algebraic points of `L` restrict to algebraic points of `K`
  (`Belyi.CurveField.QbarPoint.restrict`), compatibly with evaluation, and every point of `K`
  lifts to a point of `L` of degree at most `[L : K]` times its degree
  (`Belyi.CurveField.QbarPoint.exists_restrict_eq`).
-/

open IsLocalRing Module

namespace Belyi.CurveField

namespace Place

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

section Restrict

variable [Algebra.IsIntegral K L]

theorem comap_ne_top (Q : Place L) : Q.1.comap (algebraMap K L) ≠ ⊤ := by
  intro h
  apply Q.ne_top
  have : IsIntegrallyClosedIn Q.1.toSubring L := inferInstanceAs (IsIntegrallyClosedIn Q.1 L)
  have hle : (integralClosure K L).toSubring ≤ Q.1.toSubring := by
    refine Subring.integralClosure_le_iff.mpr fun r ↦ ?_
    have : r ∈ Q.1.comap (algebraMap K L) := h ▸ ValuationSubring.mem_top r
    exact this
  exact top_unique fun y _ ↦ hle (Algebra.IsIntegral.isIntegral (R := K) y)

variable (K) in
/-- The restriction `Q ∩ K` of a place `Q` of `L` to `K`. -/
def restrict (Q : Place L) : Place K :=
  ⟨Q.1.comap (algebraMap K L), comap_ne_top Q, fun q ↦ by
    rw [ValuationSubring.mem_comap, map_ratCast]; exact Q.ratCast_mem q⟩

variable (Q : Place L)

theorem restrict_val : (Q.restrict K).1 = Q.1.comap (algebraMap K L) := rfl

@[simp]
theorem mem_restrict_iff {x : K} : x ∈ (Q.restrict K).1 ↔ algebraMap K L x ∈ Q.1 := Iff.rfl

theorem mem_restrict_nonunits_iff {x : K} :
    x ∈ (Q.restrict K).1.nonunits ↔ algebraMap K L x ∈ Q.1.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    mem_restrict_iff, map_inv₀, map_eq_zero]

variable (K) in
/-- The inclusion `O_{Q ∩ K} → O_Q`. -/
noncomputable def restrictHom : (Q.restrict K).1 →+* Q.1 :=
  ((algebraMap K L).comp (Q.restrict K).1.subtype).codRestrict Q.1 fun x ↦ x.2

@[simp]
theorem coe_restrictHom (a : (Q.restrict K).1) :
    (Q.restrictHom K a : L) = algebraMap K L a := rfl

instance : IsLocalHom (Q.restrictHom K) where
  map_nonunit a ha := by
    by_contra h
    have hmem : (a : K) ∈ (Q.restrict K).1.nonunits := by
      rw [ValuationSubring.coe_mem_nonunits_iff]; exact h
    rw [mem_restrict_nonunits_iff, ← coe_restrictHom,
      ValuationSubring.coe_mem_nonunits_iff] at hmem
    exact hmem ha

end Restrict

section Uniformizer

variable [CharZero K] [IsCurveField K]

/-- A (chosen) uniformiser of a place: `ord_P π_P = 1`. -/
noncomputable def uniformizer (P : Place K) : K := Classical.choose P.exists_ord_eq_one

@[simp]
theorem ord_uniformizer (P : Place K) : P.ord P.uniformizer = 1 :=
  Classical.choose_spec P.exists_ord_eq_one

theorem uniformizer_ne_zero (P : Place K) : P.uniformizer ≠ 0 := by
  intro h
  have := P.ord_uniformizer
  rw [h, ord_zero] at this
  exact zero_ne_one this

end Uniformizer

section Ord

variable [CharZero K] [CharZero L] [IsCurveField K] [IsCurveField L] [Algebra.IsIntegral K L]
variable (Q : Place L)

theorem ord_restrict_pos_iff (x : K) :
    0 < (Q.restrict K).ord x ↔ 0 < Q.ord (algebraMap K L x) := by
  rw [ord_pos_iff, ord_pos_iff, mem_restrict_nonunits_iff, Ne, Ne, map_eq_zero]

theorem ord_restrict_eq_zero_iff {x : K} (hx : x ≠ 0) :
    (Q.restrict K).ord x = 0 ↔ Q.ord (algebraMap K L x) = 0 := by
  rw [ord_eq_zero_iff _ hx, ord_eq_zero_iff _ ((map_ne_zero _).mpr hx), mem_restrict_iff,
    mem_restrict_iff, map_inv₀]

variable (K) in
/-- The ramification index `e(Q|P)` of `Q` over `P = Q ∩ K`. -/
noncomputable def ramificationIdx : ℕ :=
  (Q.ord (algebraMap K L (Q.restrict K).uniformizer)).toNat

theorem ord_algebraMap_uniformizer :
    Q.ord (algebraMap K L (Q.restrict K).uniformizer) = Q.ramificationIdx K := by
  rw [ramificationIdx, Int.toNat_of_nonneg]
  exact ((Q.ord_restrict_pos_iff _).mp (by rw [ord_uniformizer]; exact one_pos)).le

theorem ramificationIdx_pos : 0 < Q.ramificationIdx K := by
  have := (Q.ord_restrict_pos_iff (Q.restrict K).uniformizer).mp
    (by rw [ord_uniformizer]; exact one_pos)
  rw [ord_algebraMap_uniformizer] at this
  exact_mod_cast this

/-- `ord_Q (f) = e(Q|P) · ord_P (f)` for `f ∈ K`, where `P = Q ∩ K`. -/
theorem ord_algebraMap_eq_mul (x : K) :
    Q.ord (algebraMap K L x) = Q.ramificationIdx K * (Q.restrict K).ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  set P := Q.restrict K
  set π := P.uniformizer
  have hπ : π ≠ 0 := P.uniformizer_ne_zero
  set n := P.ord x
  have hu0 : x * π ^ (-n) ≠ 0 := mul_ne_zero hx (zpow_ne_zero _ hπ)
  have hu : P.ord (x * π ^ (-n)) = 0 := by
    rw [P.ord_mul hx (zpow_ne_zero _ hπ), ord_zpow, ord_uniformizer]; ring
  have hu' := (Q.ord_restrict_eq_zero_iff hu0).mp hu
  have hx' : algebraMap K L x = algebraMap K L (x * π ^ (-n)) * algebraMap K L π ^ n := by
    rw [← map_zpow₀, ← map_mul, mul_assoc, ← zpow_add₀ hπ, neg_add_cancel, zpow_zero, mul_one]
  have hπL : algebraMap K L π ≠ 0 := (map_ne_zero _).mpr hπ
  rw [hx', Q.ord_mul ((map_ne_zero _).mpr hu0) (zpow_ne_zero _ hπL), hu', ord_zpow,
    ord_algebraMap_uniformizer]
  ring

omit [CharZero K] [CharZero L] [IsCurveField K] [IsCurveField L] in
theorem nonunits_subset_of_restrict_eq {P : Place K} (hQ : Q.restrict K = P) {x : K}
    (hx : x ∈ P.1.nonunits) : algebraMap K L x ∈ Q.1.nonunits := by
  subst hQ; exact (mem_restrict_nonunits_iff Q).mp hx

variable (K) in
/-- The fibre of the restriction map over a place is finite. -/
theorem finite_setOf_restrict_eq (P : Place K) : {Q : Place L | Q.restrict K = P}.Finite := by
  refine (finite_setOf_ord_pos (algebraMap K L P.uniformizer)).subset fun Q hQ ↦ ?_
  have hQ' : Q.restrict K = P := hQ
  rw [Set.mem_setOf_eq, ← Q.ord_restrict_pos_iff, hQ', ord_uniformizer]
  exact one_pos

omit [IsCurveField L] [CharZero L] in
variable (L) in
/-- Every place of `K` is the restriction of a place of `L`. -/
theorem exists_restrict_eq (P : Place K) : ∃ Q : Place L, Q.restrict K = P := by
  set π := P.uniformizer
  have hπ0 : π ≠ 0 := P.uniformizer_ne_zero
  have hπP : π ∈ P.1.nonunits := ((P.ord_pos_iff).mp (by rw [ord_uniformizer]; exact one_pos)).2
  have hπmem : π ∈ P.1 := P.1.nonunits_subset hπP
  set A : Subring L := P.1.toSubring.map (algebraMap K L)
  let πA : A := ⟨algebraMap K L π, Subring.mem_map.mpr ⟨π, hπmem, rfl⟩⟩
  have hI : Ideal.span {πA} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    rintro ⟨u, hu⟩
    obtain ⟨b, hb, hbu⟩ := Subring.mem_map.mp ((u⁻¹ : Aˣ) : A).2
    have h1 : algebraMap K L (π * b) = 1 := by
      rw [map_mul, hbu]
      have := congrArg Subtype.val u.mul_inv
      rwa [hu] at this
    have h2 : π * b = 1 := (algebraMap K L).injective (by rw [h1, map_one])
    rw [ValuationSubring.mem_nonunits_iff_or] at hπP
    refine hπP.elim hπ0 fun h ↦ h ?_
    rw [← eq_inv_of_mul_eq_one_right h2]
    exact hb
  obtain ⟨B, hAB, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  have hπB : algebraMap K L π ∈ B.nonunits := hB ⟨πA, Ideal.mem_span_singleton_self _, rfl⟩
  have hBtop : B ≠ ⊤ := by
    rintro rfl
    rw [ValuationSubring.mem_nonunits_iff_or] at hπB
    exact hπB.elim ((map_ne_zero _).mpr hπ0) fun h ↦ h (ValuationSubring.mem_top _)
  have hPB : ∀ x ∈ P.1, algebraMap K L x ∈ B := fun x hx ↦ hAB (Subring.mem_map.mpr ⟨x, hx, rfl⟩)
  refine ⟨⟨B, hBtop, fun q ↦ ?_⟩, ?_⟩
  · rw [← map_ratCast (algebraMap K L)]; exact hPB _ (P.ratCast_mem q)
  · have hle : P.1 ≤ (Place.restrict K (⟨B, hBtop, fun q ↦ by
        rw [← map_ratCast (algebraMap K L)]; exact hPB _ (P.ratCast_mem q)⟩ : Place L)).1 :=
      fun x hx ↦ hPB x hx
    exact (Place.ext (ValuationSubring.eq_of_le_of_ne_top _ hle (Place.ne_top _))).symm

end Ord

section Residue

variable [Algebra.IsIntegral K L] (Q : Place L)

variable (K) in
/-- The embedding of residue fields `κ(Q ∩ K) → κ(Q)`. -/
noncomputable def residueFieldMap : (Q.restrict K).ResidueField →+* Q.ResidueField :=
  IsLocalRing.ResidueField.map (Q.restrictHom K)

theorem residueFieldMap_residue (a : (Q.restrict K).1) :
    Q.residueFieldMap K ((Q.restrict K).residue a) = Q.residue (Q.restrictHom K a) :=
  IsLocalRing.ResidueField.map_residue _ a

variable (K) in
/-- `κ(Q)` as an algebra over `κ(Q ∩ K)`. -/
noncomputable abbrev residueAlgebra : Algebra (Q.restrict K).ResidueField Q.ResidueField :=
  (Q.residueFieldMap K).toAlgebra

variable (K) in
/-- The residue degree `f(Q|P) = [κ(Q) : κ(P)]` of `Q` over `P = Q ∩ K`. -/
noncomputable def inertiaDeg : ℕ :=
  letI := Q.residueAlgebra K
  finrank (Q.restrict K).ResidueField Q.ResidueField

theorem algebraMap_residue (a : (Q.restrict K).1) :
    letI := Q.residueAlgebra K
    algebraMap (Q.restrict K).ResidueField Q.ResidueField ((Q.restrict K).residue a) =
      Q.residue (Q.restrictHom K a) :=
  Q.residueFieldMap_residue a

variable [CharZero K] [CharZero L] [IsCurveField K] [IsCurveField L]

/-- `deg Q = f(Q|P) · deg P`. -/
theorem deg_eq_inertiaDeg_mul : Q.deg = Q.inertiaDeg K * (Q.restrict K).deg := by
  letI := Q.residueAlgebra K
  rw [deg, deg, inertiaDeg, mul_comm,
    Module.finrank_mul_finrank ℚ (Q.restrict K).ResidueField Q.ResidueField]

theorem inertiaDeg_pos : 0 < Q.inertiaDeg K := by
  have h := Q.deg_eq_inertiaDeg_mul (K := K)
  rcases Nat.eq_zero_or_pos (Q.inertiaDeg K) with h0 | h0
  · rw [h0, zero_mul] at h; exact absurd h Q.deg_pos.ne'
  · exact h0

/-- `f(Q|P) ≤ [L : K]`: lifts of a `κ(P)`-basis of `κ(Q)` are `K`-linearly independent. -/
theorem inertiaDeg_le_finrank [FiniteDimensional K L] : Q.inertiaDeg K ≤ finrank K L := by
  classical
  dsimp only [inertiaDeg]
  letI := Q.residueAlgebra K
  have : FiniteDimensional (Q.restrict K).ResidueField Q.ResidueField :=
    Module.Finite.of_restrictScalars_finite ℚ _ _
  let b := Module.finBasis (Q.restrict K).ResidueField Q.ResidueField
  choose y hy using fun i ↦ Q.residue_surjective (b i)
  have hli : LinearIndependent K (fun i ↦ (y i : L)) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    by_contra hgi
    obtain ⟨j, hj, hjmin⟩ := (s.filter (fun i ↦ g i ≠ 0)).exists_min_image
      (fun i ↦ (Q.restrict K).ord (g i)) ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
    rw [Finset.mem_filter] at hj
    set c := g j
    have hc : c ≠ 0 := hj.2
    have hmem : ∀ i ∈ s, g i / c ∈ (Q.restrict K).1 := by
      intro i hi
      rcases eq_or_ne (g i) 0 with h0 | h0
      · rw [h0, zero_div]; exact (Q.restrict K).1.zero_mem
      refine (Q.restrict K).mem_of_ord_nonneg ?_
      rw [(Q.restrict K).ord_div h0 hc, sub_nonneg]
      exact hjmin i (Finset.mem_filter.mpr ⟨hi, h0⟩)
    let hP : Fin (finrank (Q.restrict K).ResidueField Q.ResidueField) → (Q.restrict K).1 := fun i ↦
      if hs : g i / c ∈ (Q.restrict K).1 then ⟨g i / c, hs⟩ else 0
    have hhP : ∀ i ∈ s, (hP i : K) = g i / c := fun i hi ↦ by simp only [hP, dif_pos (hmem i hi)]
    have hsumQ : ∑ i ∈ s, Q.restrictHom K (hP i) * y i = 0 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero]
      calc ∑ i ∈ s, ((Q.restrictHom K (hP i) * y i : Q.1) : L)
          = ∑ i ∈ s, (algebraMap K L c)⁻¹ * (g i • (y i : L)) :=
            Finset.sum_congr rfl fun i hi ↦ by
              rw [MulMemClass.coe_mul, coe_restrictHom, hhP i hi, Algebra.smul_def, map_div₀]
              ring
        _ = (algebraMap K L c)⁻¹ * ∑ i ∈ s, g i • (y i : L) := by rw [Finset.mul_sum]
        _ = 0 := by rw [hg, mul_zero]
    have hres := congrArg Q.residue hsumQ
    rw [map_sum, map_zero] at hres
    simp only [map_mul, hy, ← algebraMap_residue, ← Algebra.smul_def] at hres
    have := (linearIndependent_iff'.mp b.linearIndependent) s
      (fun i ↦ (Q.restrict K).residue (hP i)) hres j hj.1
    have h1 : hP j = 1 := Subtype.ext (by rw [hhP j hj.1, div_self hc]; rfl)
    rw [h1, map_one] at this
    exact one_ne_zero this
  have := hli.fintype_card_le_finrank
  rwa [Fintype.card_fin] at this

end Residue

end Place

namespace QbarPoint

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] [Algebra K L]
  [Algebra.IsIntegral K L]

variable (K) in
/-- The restriction of an algebraic point of `L` to `K` (its image under `Y → X`). -/
noncomputable def restrict (y : QbarPoint L) : QbarPoint K :=
  ⟨y.P.restrict K, y.σ.comp (y.P.residueFieldMap K)⟩

variable (y : QbarPoint L)

@[simp]
theorem restrict_P : (y.restrict K).P = y.P.restrict K := rfl

/-- `f(y|_K) = f(y)` for `f ∈ K` regular at `y|_K`. -/
theorem eval_restrict (f : K) (hf : f ∈ (y.restrict K).P.1) :
    (y.restrict K).eval f hf = y.eval (algebraMap K L f) hf := by
  change y.σ (y.P.residueFieldMap K ((y.P.restrict K).residue ⟨f, hf⟩)) =
    y.σ (y.P.residue ⟨algebraMap K L f, hf⟩)
  rw [Place.residueFieldMap_residue]
  rfl

theorem fieldOf_restrict_le : (y.restrict K).fieldOf ≤ y.fieldOf := by
  rintro _ ⟨a, rfl⟩
  exact ⟨y.P.residueFieldMap K a, rfl⟩

variable [IsCurveField K] [IsCurveField L]

/-- Every algebraic point of `K` lifts to an algebraic point of `L` of degree at most
`[L : K]` times its degree. -/
theorem exists_restrict_eq [FiniteDimensional K L] (x : QbarPoint K) :
    ∃ y : QbarPoint L, y.restrict K = x ∧ y.deg ≤ finrank K L * x.deg := by
  obtain ⟨P, σ⟩ := x
  obtain ⟨Q, rfl⟩ := Place.exists_restrict_eq L P
  letI := Q.residueAlgebra K
  letI : Algebra (Q.restrict K).ResidueField (AlgebraicClosure ℚ) := σ.toAlgebra
  haveI : Algebra.IsAlgebraic (Q.restrict K).ResidueField Q.ResidueField :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) _
  let τ : Q.ResidueField →ₐ[(Q.restrict K).ResidueField] AlgebraicClosure ℚ :=
    IsAlgClosed.lift
  refine ⟨⟨Q, τ.toRingHom⟩, ?_, ?_⟩
  · simp only [restrict, mk.injEq, heq_eq_eq, true_and]
    ext a
    exact τ.commutes a
  · change Module.finrank ℚ _ ≤ _
    rw [(QbarPoint.mk Q τ.toRingHom).residueFieldEquiv.toLinearEquiv.finrank_eq.symm]
    change Q.deg ≤ _
    rw [Q.deg_eq_inertiaDeg_mul (K := K), deg_eq]
    exact Nat.mul_le_mul_right _ (Q.inertiaDeg_le_finrank)

end QbarPoint

end Belyi.CurveField
