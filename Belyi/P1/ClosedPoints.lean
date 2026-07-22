/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.PolynomialMapInfty
import Belyi.P1.Curve
import Belyi.P1.ChartCoord
import Belyi.P1.AffineChart
import Belyi.P1.ChartInjective
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Closed-point classification of `ℙ¹` over an algebraically closed field

Over an algebraically closed field `k`, every non-generic point of `ℙ¹_k = Proj (P1Grading k)`
is a `k`-rational affine point `[a : 1]` or the point at infinity `∞ = [1 : 0]`.

## Strategy

Handle the point at infinity first: if `X₁` lies in the homogeneous ideal of `x`, then
`x = ∞` (`Belyi.P1.eq_infty_of_X1_mem`).  Otherwise `x` lies in the affine chart `D₊(X₁)`,
so `x = awayι q` for a prime `q` of the chart ring `Away (X₁) ≃ₐ[k] k[T]`
(`Belyi.P1.awayChartEquivOne`).  If `q` were the bottom prime, `x` would be the generic
point (`Belyi.P1.asHomogeneousIdeal_awayι_eq_bot`), contradicting the hypothesis.  Hence the
image ideal `Q ⊆ k[T]` is a nonzero prime, so by the Nullstellensatz over `IsAlgClosed k`
(`Belyi.P1.exists_span_X_sub_C_of_isPrime`) it is `span {T - a}` for some `a : k`.
Transporting back, `q = ker (awayEval k a)`, and this is exactly the point `[a : 1]`.

## Main results

* `Belyi.P1.exists_span_X_sub_C_of_isPrime`: a nonzero prime of `k[T]` (over an algebraically
  closed field) is `span {T - a}` for some `a`.
* `Belyi.P1.asHomogeneousIdeal_awayι_eq_bot`: if the prime `q` of the chart ring `Away (X₁)`
  is `⊥`, then `awayι q` has homogeneous ideal `⊥`.
* `Belyi.P1.exists_eq_point_or_eq_infty_of_ne_genericPoint`: the closed-point classification.
-/

universe u

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open scoped Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Nullstellensatz for `k[T]` over an algebraically closed field.** A nonzero prime ideal
of `k[T]` is `span {T - a}` for some `a : k`. Since `k[T]` is a PID, a nonzero prime `Q` is
`span {g}` for an irreducible `g`; over `IsAlgClosed k` the irreducible `g` has degree one,
hence a root `a`, and `(T - a) ∣ g` forces `Q = span {T - a}` by maximality. -/
theorem exists_span_X_sub_C_of_isPrime {k : Type*} [Field k] [IsAlgClosed k]
    {Q : Ideal (Polynomial k)} [Q.IsPrime] (hQ : Q ≠ ⊥) :
    ∃ a : k, Q = Ideal.span {Polynomial.X - Polynomial.C a} := by
  haveI : Q.IsPrincipal := IsPrincipalIdealRing.principal Q
  obtain ⟨g, hg⟩ : ∃ g, Q = Ideal.span {g} :=
    ⟨_, (Ideal.span_singleton_generator Q).symm⟩
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hQ (hg.trans (Ideal.span_singleton_eq_bot.mpr rfl))
  haveI hprime : (Ideal.span {g}).IsPrime := hg ▸ ‹Q.IsPrime›
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).mp hprime
  have hgirr : Irreducible g := hgp.irreducible
  have hdeg : g.degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible k hgirr
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root g (by rw [hdeg]; exact one_ne_zero)
  refine ⟨a, ?_⟩
  have hmax : (Ideal.span {g}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hgirr
  rw [← hg] at hmax
  refine hmax.eq_of_le ?_ ?_
  · exact fun h => Polynomial.not_isUnit_X_sub_C a (Ideal.span_singleton_eq_top.mp h)
  · rw [hg, Ideal.span_singleton_le_span_singleton]
    exact Polynomial.dvd_iff_isRoot.mpr ha

variable (k : Type u) [Field k]

/-- If the prime `q` of the affine chart ring `Away (X₁)` is the bottom ideal, then the point
`awayι q` of `ℙ¹` has homogeneous ideal `⊥` (i.e. it is the generic point). A homogeneous
element `a` lies in the ideal iff the fraction `a / X₁ⁿ` lies in `q = ⊥`, iff it is zero,
iff `a = 0` (since `k[X₀,X₁]` is a domain and `X₁ ≠ 0`). -/
theorem asHomogeneousIdeal_awayι_eq_bot
    (q : Spec (CommRingCat.of (Away (P1Grading k) (X 1 : MvPolynomial (Fin 2) k))))
    (hq : (q : PrimeSpectrum (Away (P1Grading k) (X 1))).asIdeal = ⊥) :
    ((Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos).base q).asHomogeneousIdeal
      = ⊥ := by
  refine HomogeneousIdeal.ext' fun i a ha => ?_
  have hden : a ∈ P1Grading k (i • 1) := by simpa using ha
  have hmk : (HomogeneousLocalization.Away.mk (P1Grading k) (X_mem_P1Grading k 1) i a hden = 0)
      ↔ a = 0 := by
    rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk,
      HomogeneousLocalization.val_zero, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
    constructor
    · rintro ⟨⟨m, j, rfl⟩, hma⟩
      rcases mul_eq_zero.mp hma with h | h
      · exact absurd h (pow_ne_zero j (X_ne_zero (R := k) 1))
      · exact h
    · rintro rfl
      exact ⟨1, by simp⟩
  rw [← Proj.awayMk_mem_iff_mem_awayι (P1Grading k) (X_mem_P1Grading k 1) one_pos q i a hden, hq,
    Ideal.mem_bot, hmk, ← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot]

/-- **Closed-point classification of `ℙ¹` over an algebraically closed field.** Every point of
`ℙ¹_k` other than the generic point is an affine `k`-point `[a : 1]` (`point k a` evaluated at
the closed point of `Spec k`) or the point at infinity `∞`. -/
theorem exists_eq_point_or_eq_infty_of_ne_genericPoint [IsAlgClosed k]
    (x : P1 k) (hx : x ≠ _root_.genericPoint (P1 k)) :
    (∃ a : k, x = (point k a).base (IsLocalRing.closedPoint (CommRingCat.of k)))
      ∨ x = infty k := by
  classical
  by_cases hX1 : (X 1 : MvPolynomial (Fin 2) k) ∈ x.asHomogeneousIdeal.toIdeal
  · exact Or.inr (eq_infty_of_X1_mem k hX1)
  refine Or.inl ?_
  -- `x` lies in the chart `D₊(X₁)`; obtain the preimage prime `q`.
  have hmemBO : x ∈ Proj.basicOpen (P1Grading k) (X 1) :=
    fun h => hX1 (HomogeneousIdeal.mem_iff.mpr h)
  have hmem : x ∈ (Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos).opensRange := by
    rw [Proj.opensRange_awayι]; exact hmemBO
  obtain ⟨q, hq⟩ := hmem
  set e := awayChartEquivOne k with he
  -- the image ideal `Q ⊆ k[T]`.
  haveI hqp : (q : PrimeSpectrum (Away (P1Grading k) (X 1))).asIdeal.IsPrime :=
    (q : PrimeSpectrum (Away (P1Grading k) (X 1))).isPrime
  set Q : Ideal (Polynomial k) :=
    Ideal.comap (e.symm.toRingHom) (q : PrimeSpectrum (Away (P1Grading k) (X 1))).asIdeal with hQdef
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  -- `q.asIdeal = comap e Q`.
  have hqcomap : (q : PrimeSpectrum (Away (P1Grading k) (X 1))).asIdeal
      = Ideal.comap e.toRingHom Q := by
    rw [hQdef, Ideal.comap_comap,
      show (e.symm.toRingHom).comp e.toRingHom = RingHom.id _ from
        RingHom.ext fun z => e.symm_apply_apply z,
      Ideal.comap_id]
  -- non-generic ⟹ `q.asIdeal ≠ ⊥`.
  have hqbot : (q : PrimeSpectrum (Away (P1Grading k) (X 1))).asIdeal ≠ ⊥ := by
    intro h0
    have hxbot : x.asHomogeneousIdeal = ⊥ := by
      rw [← hq]; exact asHomogeneousIdeal_awayι_eq_bot k q h0
    have hgen : _root_.genericPoint (P1 k) = genericPoint k :=
      (genericPoint_spec (P1 k)).eq (isGenericPoint_genericPoint k)
    exact hx ((ProjectiveSpectrum.ext (by rw [hxbot]; rfl)).trans hgen.symm)
  -- hence `Q ≠ ⊥`.
  have hQ0 : Q ≠ ⊥ := by
    intro h
    apply hqbot
    rw [hqcomap, h]
    exact (RingHom.injective_iff_ker_eq_bot _).mp e.injective
  -- Nullstellensatz: `Q = span {T - a}`.
  obtain ⟨a, haQ⟩ := exists_span_X_sub_C_of_isPrime hQ0
  refine ⟨a, ?_⟩
  -- `awayEval k a = evalRingHom a ∘ e`.
  have hFG : awayEvalₐ k a = (Polynomial.aeval a).comp (awayChartEquivOne k).toAlgHom := by
    have hid : (awayChartEquivOne k).symm.toAlgHom.comp (awayChartEquivOne k).toAlgHom
        = AlgHom.id k _ := AlgHom.ext fun z => (awayChartEquivOne k).symm_apply_apply z
    have hs : (awayChartEquivOne k).symm (Polynomial.X) = affineCoord k :=
      (AlgEquiv.symm_apply_eq _).mpr (awayChartEquivOne_affineCoord k).symm
    have halg : (awayEvalₐ k a).comp (awayChartEquivOne k).symm.toAlgHom
        = Polynomial.aeval a := by
      apply Polynomial.algHom_ext
      rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hs, Polynomial.aeval_X]
      exact awayEval_affineCoord k a
    rw [← halg, AlgHom.comp_assoc, hid, AlgHom.comp_id]
  have hFGring : awayEval k a = (Polynomial.evalRingHom a).comp e.toRingHom := by
    ext z
    have h := DFunLike.congr_fun hFG z
    rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at h
    rw [RingHom.comp_apply, ← Polynomial.coe_aeval_eq_evalRingHom]
    exact h
  -- so `ker (awayEval k a) = comap e (span {T - a})`.
  have hker : RingHom.ker (awayEval k a)
      = Ideal.comap e.toRingHom (Ideal.span {Polynomial.X - Polynomial.C a}) := by
    rw [← Polynomial.ker_evalRingHom a, RingHom.comap_ker, ← hFGring]
  have hqker : (q : PrimeSpectrum (Away (P1Grading k) (X 1))).asIdeal
      = RingHom.ker (awayEval k a) := by
    rw [hqcomap, haQ, hker]
  -- identify `x` with the point `[a : 1]`.
  set y : Spec (CommRingCat.of (Away (P1Grading k) (X 1 : MvPolynomial (Fin 2) k))) :=
    (Spec.map (CommRingCat.ofHom (awayEval k a))).base
      (IsLocalRing.closedPoint (CommRingCat.of k)) with hy
  have hyker : (y : PrimeSpectrum (Away (P1Grading k) (X 1))).asIdeal
      = RingHom.ker (awayEval k a) := by
    have hbot : (IsLocalRing.closedPoint (CommRingCat.of k)).asIdeal = ⊥ :=
      IsLocalRing.maximalIdeal_eq_bot
    rw [show (y : PrimeSpectrum (Away (P1Grading k) (X 1))) =
        PrimeSpectrum.comap (awayEval k a) (IsLocalRing.closedPoint (CommRingCat.of k)) from rfl,
      PrimeSpectrum.comap_asIdeal, hbot]
    rfl
  have hpoint : (point k a).base (IsLocalRing.closedPoint (CommRingCat.of k))
      = (Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos).base y := by
    have h : point k a (IsLocalRing.closedPoint (CommRingCat.of k))
        = Proj.awayι (P1Grading k) (X 1) (X_mem_P1Grading k 1) one_pos y := by
      rw [point, Scheme.Hom.comp_apply]
      rfl
    exact h
  have hqy : q = y := PrimeSpectrum.ext (hqker.trans hyker.symm)
  rw [hpoint, ← hqy]
  exact hq.symm

end Belyi.P1
