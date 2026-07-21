/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Belyi.P1.PolynomialMapImage
import Belyi.P1.MarkedPointMatching

/-!
# B4c (infinity): the polynomial self-map fixes `∞`

For a non-constant `g : k[X]` the self-map `Belyi.P1.polynomialSelfMap g : ℙ¹ ⟶ ℙ¹`
(realizing `[x₀ : x₁] ↦ [g.homogenize d : X₁ᵈ]`, taxis issue #106) fixes the point at
infinity:

* `Belyi.P1.polynomialSelfMap_infty`: `polynomialSelfMap g (∞) = ∞`.

Together with the affine-point images `[a : 1] ↦ [g(a) : 1]`
(`Belyi.P1.polynomialSelfMap_point`, `Belyi/P1/PolynomialMapImage.lean`) this pins down the
image of every closed point of `ℙ¹`, one of the two inputs the branch-locus identification of
statement **B4c** (taxis issue #108) consumes.

## Strategy

`∞ = [1 : 0]` lies in the source chart `D₊(G)` (since `G ≡ lc·X₀ᵈ (mod X₁)` and `lc ≠ 0`),
where the self-map is the `D₊(X₀)`-valued point `point₀ k (X₁ᵈ/G)` (`selfMapChartZero`).  We
identify `∞` with `awayι(G)` applied to the chart point `q`, so `polynomialSelfMap g (∞) =
point₀ k (X₁ᵈ/G) q`, and then show the homogeneous ideal of that image contains `X₁`.  The
computation runs through the `Proj.toSpec` point description (`mk_mem_toSpec_base_apply`) on the
two affine charts `D₊(X₀)` (target) and `D₊(G)` (source), reducing `X₁ ∈ image` to
`X₁ᵈ ∈ (∞)`, which holds.  Finally the auxiliary `V(X₁) = {∞}` characterization
`eq_infty_of_X1_mem` (a variant of the `∞` marked-point computation of #164) concludes.

## Main results

* `Belyi.P1.eq_infty_of_X1_mem`: a point of `ℙ¹` whose homogeneous ideal contains `X₁` is `∞`.
* `Belyi.P1.polynomialSelfMap_infty`: `polynomialSelfMap g (∞) = ∞`.
-/

universe u

namespace AlgebraicGeometry.Proj

open CategoryTheory HomogeneousLocalization

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **Point description of `awayι`.** For `f` homogeneous of positive degree and a point `y` of
`Spec (A_f)₀`, a homogeneous fraction `mk z` lies in `y` iff its numerator lies in the
homogeneous ideal of the corresponding point `awayι f y` of `Proj A`. This is
`mk_mem_toSpec_base_apply` transported across the iso `Proj|D₊(f) ≅ Spec (A_f)₀`. -/
lemma mk_mem_iff_num_mem_awayι {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    (y : Spec (CommRingCat.of (Away 𝒜 f)))
    (z : NumDenSameDeg 𝒜 (.powers f)) :
    HomogeneousLocalization.mk z ∈ (y : PrimeSpectrum (Away 𝒜 f)).asIdeal ↔
      z.num.1 ∈ ((Proj.awayι 𝒜 f f_deg hm).base y).asHomogeneousIdeal := by
  set w := (Proj.basicOpenIsoSpec 𝒜 f f_deg hm).inv y with hwdef
  have hbase : (Proj.awayι 𝒜 f f_deg hm).base y = w.val := by
    rw [← Proj.basicOpenIsoSpec_inv_ι 𝒜 f f_deg hm, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  have htoSpec : (ProjectiveSpectrum.Proj.toSpec 𝒜 f).base w = y := by
    rw [Proj.toSpec_base_apply_eq_basicOpenToSpec 𝒜 f,
      ← Proj.basicOpenIsoSpec_hom 𝒜 f f_deg hm, hwdef, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  rw [hbase, ← htoSpec]
  exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 w z

/-- **Point description of `awayι`, `Away.mk` form.** Specialization of
`mk_mem_iff_num_mem_awayι` to the convenient fraction constructor `Away.mk`. -/
lemma awayMk_mem_iff_mem_awayι {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    (y : Spec (CommRingCat.of (Away 𝒜 f))) (n : ℕ) (num : A) (hnum : num ∈ 𝒜 (n • m)) :
    HomogeneousLocalization.Away.mk 𝒜 f_deg n num hnum ∈
        (y : PrimeSpectrum (Away 𝒜 f)).asIdeal ↔
      num ∈ ((Proj.awayι 𝒜 f f_deg hm).base y).asHomogeneousIdeal :=
  mk_mem_iff_num_mem_awayι 𝒜 f_deg hm y
    ⟨n • m, ⟨num, hnum⟩, ⟨f ^ n, SetLike.pow_mem_graded n f_deg⟩, ⟨n, rfl⟩⟩

end AlgebraicGeometry.Proj

namespace Belyi.P1

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open scoped Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (g : k[X])

/-- **`V(X₁) = {∞}`.** A point of `ℙ¹` whose homogeneous ideal contains `X₁` is the point at
infinity. This mirrors the `∞` case of the marked-point computation of #164
(`mapOfAlgebra_base_eq_infty`) with the comap step removed. -/
lemma eq_infty_of_X1_mem {y : P1 k}
    (hX1 : (X 1 : MvPolynomial (Fin 2) k) ∈ y.asHomogeneousIdeal.toIdeal) : y = infty k := by
  have hX0 : (X 0 : MvPolynomial (Fin 2) k) ∉ y.asHomogeneousIdeal.toIdeal :=
    fun h0 => X01_not_both_mem y h0 hX1
  have hspan : y.asHomogeneousIdeal.toIdeal = Ideal.span {(X 1 : MvPolynomial (Fin 2) k)} :=
    eq_span_of_forall_dvd y.asHomogeneousIdeal.isHomogeneous (isHomogeneous_X k 1) hX1
      (fun n w hw hwJ => dvd_of_isHomog_mem y.isPrime 1 0 (by decide) hX1 hX0 hw hwJ)
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  rw [hspan, infty, mkPoint_asIdeal]

/-- The homogenization `G` does not vanish at `∞ = [1 : 0]`: modulo `X₁` it is `lc·X₀ᵈ` with
`lc ≠ 0`, so `X₁ ∤ G`, i.e. `G ∉ (X₁) = (∞)`. Hence `∞ ∈ D₊(G)`. -/
lemma homogInput_notMem_infty (hd : 0 < g.natDegree) :
    homogInput k g ∉ (infty k).asHomogeneousIdeal := by
  rw [← HomogeneousIdeal.mem_iff, infty, mkPoint_asIdeal, Ideal.mem_span_singleton]
  intro hdvd
  have hg_ne : g ≠ 0 := fun h0 => by simp [h0] at hd
  obtain ⟨H, hH⟩ := X1_dvd_homogInput_sub k g
  have hdvd2 : (X 1 : MvPolynomial (Fin 2) k) ∣
      C (g.coeff g.natDegree) * X 0 ^ g.natDegree := by
    have heq : (C (g.coeff g.natDegree) * X 0 ^ g.natDegree : MvPolynomial (Fin 2) k)
        = homogInput k g - X 1 * H := by rw [← hH]; ring
    rw [heq]; exact dvd_sub hdvd (dvd_mul_right (X 1) H)
  have hev := map_dvd (eval (![1, 0] : Fin 2 → k)) hdvd2
  simp only [map_mul, map_pow, eval_X, eval_C, Matrix.cons_val_one,
    Matrix.cons_val_zero, one_pow, mul_one] at hev
  rw [zero_dvd_iff] at hev
  exact Polynomial.leadingCoeff_ne_zero.mpr hg_ne hev

/-- **B4c (infinity): the polynomial self-map fixes `∞`.** For a non-constant `g : k[X]`, the
self-map `[x₀ : x₁] ↦ [g.homogenize d : X₁ᵈ]` of `ℙ¹` sends `∞` to `∞`. -/
theorem polynomialSelfMap_infty (hd : 0 < g.natDegree) :
    polynomialSelfMap k g hd (infty k) = infty k := by
  -- `∞` lies in the source chart `D₊(G)`; obtain a point `q` of `Spec (A_G)₀` above it.
  have hGmem : infty k ∈ Proj.basicOpen (P1Grading k) (homogInput k g) :=
    homogInput_notMem_infty k g hd
  have hmem : infty k ∈
      (Proj.awayι (P1Grading k) (homogInput k g) (homogInput_mem k g) hd).opensRange := by
    rw [Proj.opensRange_awayι]; exact hGmem
  obtain ⟨q, hawayι⟩ := hmem
  -- the chart map on `D₊(G)` is `point₀ k (X₁ᵈ/G)`.
  have hchart : Proj.awayι (P1Grading k) (homogInput k g) (homogInput_mem k g) hd ≫
      polynomialSelfMap k g hd = point₀ k (selfMapCoordZero k g) := by
    have h := ι_polynomialSelfMap k g hd true
    rw [Scheme.AffineOpenCover.openCover_f] at h
    exact h
  -- so the image of `∞` is `point₀ k (X₁ᵈ/G) q`.
  have himg : polynomialSelfMap k g hd (infty k) = point₀ k (selfMapCoordZero k g) q := by
    have key := congrArg (fun φ : _ ⟶ P1 k => φ.base q) hchart
    rw [Scheme.Hom.comp_apply, hawayι] at key
    exact key
  -- it suffices to show `X₁` lies in the homogeneous ideal of the image.
  apply eq_infty_of_X1_mem
  rw [himg]
  -- unfold `point₀` as `Spec.map (awayEval₀ …) ≫ awayι(X₀)`.
  set s := selfMapCoordZero k g with hs
  have hX1_deg : (X 1 : MvPolynomial (Fin 2) k) ∈ P1Grading k (1 • 1) := by
    simpa using X_mem_P1Grading k 1
  have hpt : point₀ k s q = (Proj.awayι (P1Grading k) (X 0) (X_mem_P1Grading k 0) one_pos).base
      ((Spec.map (CommRingCat.ofHom (awayEval₀ k s))).base q) := rfl
  rw [hpt, HomogeneousIdeal.mem_iff,
    ← Proj.awayMk_mem_iff_mem_awayι (P1Grading k) (X_mem_P1Grading k 0) one_pos _ 1 (X 1) hX1_deg]
  -- reduce membership in `q'` to evaluation into `q`.
  change HomogeneousLocalization.Away.mk (P1Grading k) (X_mem_P1Grading k 0) 1 (X 1) hX1_deg ∈
    (PrimeSpectrum.comap (awayEval₀ k s) q).asIdeal
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, awayEval₀_mk]
  -- `awayEval₀ k s (X₁/X₀) = s = X₁ᵈ/G`.
  simp only [aeval_X, Matrix.cons_val_one]
  -- `s = Away.mk G 1 (X₁ᵈ)`; membership reduces to `X₁ᵈ ∈ (∞)` via `awayι(G) q = ∞`.
  rw [hs]
  change HomogeneousLocalization.Away.mk (P1Grading k) (homogInput_mem k g) 1 (X 1 ^ g.natDegree)
      (by simpa using SetLike.pow_mem_graded g.natDegree (X_mem_P1Grading k 1)) ∈
    (q : PrimeSpectrum (Away (P1Grading k) (homogInput k g))).asIdeal
  rw [Proj.awayMk_mem_iff_mem_awayι (P1Grading k) (homogInput_mem k g) hd q 1
      (X 1 ^ g.natDegree) (by simpa using SetLike.pow_mem_graded g.natDegree (X_mem_P1Grading k 1)),
    hawayι, ← HomogeneousIdeal.mem_iff, infty, mkPoint_asIdeal, Ideal.mem_span_singleton]
  exact dvd_pow_self (X 1) hd.ne'

end Belyi.P1
