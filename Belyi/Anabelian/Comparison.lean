/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-!
# The group-theoretic part of the comparison of cuspidalisations ([AbsTopII] Cor 3.8)

[AbsTopII] Corollary 3.8 (`Topics in Absolute Anabelian Geometry II.txt` l.4831–4842): for
`φ : Π₁ ≅ Π₂` and each `U_{X₁}` there are `U_{X₂}` and an isomorphism
`φ_U : Π_{U_{X₁}} ≅ Π_{U_{X₂}}` "that is compatible with `φ`, relative to the natural surjections
`Π_{U_{X_i}} ↠ Π_i`. Moreover, such an isomorphism `φ_U` is unique up to composition with an
inner automorphism arising from an element of the kernel of `Π_{U_{X_i}} ↠ Π_i`." Proof
(l.4839–4841): "the asserted uniqueness then follows immediately from our assumption that the
rel-isom-DGC holds."

The rel-isom-DGC shows that two compatible `φ_U, φ_U'` differ by an inner automorphism of
`Π_{U_{X₂}}`. This file proves the remaining (purely group-theoretic) steps, writing `P_i → Q_i`
for `Π_{U_{X_i}} ↠ Π_i`:

* `Belyi.Anabelian.IsCompatible`: `p₂ ∘ ψ = φ ∘ p₁`;
* `IsCompatible.conj`: composing a compatible `ψ` with an inner automorphism by an element of
  `ker p₂` keeps it compatible;
* `IsCompatible.mem_ker_of_eq_conj`: if `Π₂` is center-free (e.g. slim) and `p₁` is surjective,
  then for compatible `ψ, ψ'` with `ψ = inn(γ) ∘ ψ'`, the element `γ` lies in `ker p₂`.
-/

namespace Belyi.Anabelian

variable {P₁ P₂ Q₁ Q₂ : Type*} [Group P₁] [Group P₂] [Group Q₁] [Group Q₂]
  {p₁ : P₁ →* Q₁} {p₂ : P₂ →* Q₂} {φ : Q₁ ≃* Q₂}

variable (p₁ p₂ φ) in
/-- An isomorphism `ψ : P₁ ≅ P₂` is **compatible** with `φ : Q₁ ≅ Q₂` relative to
`p_i : P_i → Π_i` if `p₂ ∘ ψ = φ ∘ p₁`. -/
def IsCompatible (ψ : P₁ ≃* P₂) : Prop :=
  ∀ x, p₂ (ψ x) = φ (p₁ x)

/-- Composing a compatible isomorphism with the inner automorphism by an element of `ker p₂`
gives a compatible isomorphism. -/
theorem IsCompatible.conj {ψ : P₁ ≃* P₂} (h : IsCompatible p₁ p₂ φ ψ) {γ : P₂}
    (hγ : γ ∈ p₂.ker) : IsCompatible p₁ p₂ φ (ψ.trans (MulAut.conj γ)) := fun x ↦ by
  rw [MonoidHom.mem_ker] at hγ
  simp [MulAut.conj_apply, hγ, h x]

/-- **Uniqueness in [AbsTopII] Cor 3.8, group-theoretic step.** If `Q₂` is center-free and `p₁` is
surjective, and two isomorphisms `ψ, ψ' : P₁ ≅ P₂` compatible with `φ` differ by the inner
automorphism by `γ` (`ψ = inn(γ) ∘ ψ'`, which is what the rel-isom-DGC provides), then
`γ ∈ ker p₂`. -/
theorem IsCompatible.mem_ker_of_eq_conj (hp₁ : Function.Surjective p₁)
    (hQ₂ : Subgroup.center Q₂ = ⊥) {ψ ψ' : P₁ ≃* P₂} (h : IsCompatible p₁ p₂ φ ψ)
    (h' : IsCompatible p₁ p₂ φ ψ') {γ : P₂} (hγ : ∀ x, ψ x = γ * ψ' x * γ⁻¹) :
    γ ∈ p₂.ker := by
  rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← hQ₂, Subgroup.mem_center_iff]
  intro g
  obtain ⟨x, rfl⟩ := (φ.surjective.comp hp₁) g
  have hx := congrArg p₂ (hγ x)
  rw [h x, map_mul, map_mul, h' x, map_inv] at hx
  simp only [Function.comp_apply]
  calc φ (p₁ x) * p₂ γ = p₂ γ * φ (p₁ x) * (p₂ γ)⁻¹ * p₂ γ := by rw [← hx]
    _ = p₂ γ * φ (p₁ x) := inv_mul_cancel_right _ _

/-- **Uniqueness in [AbsTopII] Cor 3.8, group-theoretic form.** Under the hypotheses of
`IsCompatible.mem_ker_of_eq_conj`, `ψ` is `ψ'` followed by the inner automorphism by an element of
`ker p₂`. -/
theorem IsCompatible.eq_trans_conj (hp₁ : Function.Surjective p₁)
    (hQ₂ : Subgroup.center Q₂ = ⊥) {ψ ψ' : P₁ ≃* P₂} (h : IsCompatible p₁ p₂ φ ψ)
    (h' : IsCompatible p₁ p₂ φ ψ') {γ : P₂} (hγ : ∀ x, ψ x = γ * ψ' x * γ⁻¹) :
    γ ∈ p₂.ker ∧ ψ = ψ'.trans (MulAut.conj γ) :=
  ⟨h.mem_ker_of_eq_conj hp₁ hQ₂ h' hγ, MulEquiv.ext fun x ↦ by simp [hγ x, MulAut.conj_apply]⟩

end Belyi.Anabelian
