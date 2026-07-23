/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# fpqc descent of separatedness and properness

This file provides two `MorphismProperty.DescendsAlong … (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`
instances that are missing from mathlib v4.32:

* `AlgebraicGeometry.descendsAlong_isSeparated_surjective_inf_flat_inf_quasicompact`
* `AlgebraicGeometry.descendsAlong_isProper_surjective_inf_flat_inf_quasicompact`

They are the separatedness/properness half of the descent step B3c (taxis #167): a scheme
`X₀ / k₀` whose base change `X₀ ×_{Spec k₀} Spec K` along a field extension `k₀ ⊆ K` is
separated (resp. proper) is itself separated (resp. proper) over `k₀`, because
`Spec K ⟶ Spec k₀` is `@Surjective ⊓ @Flat ⊓ @QuasiCompact`.

## The key observation

Mathlib already descends `@UniversallyClosed` along `@Surjective ⊓ @Flat ⊓ @QuasiCompact`
(`descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`), but it does *not*
descend `@IsClosedImmersion`: that would require faithfully-flat codescent of
`RingHom.SurjectiveOnStalks`, an unsolved (research-grade) ring-theoretic descent problem.

Separatedness, however, does **not** need it. Since `@IsSeparated = diagonal @IsClosedImmersion`
and the diagonal `pullback.diagonal f` is **always** an immersion — hence a preimmersion, so it
already satisfies `SurjectiveOnStalks` for free — being a closed immersion on the diagonal is
equivalent to merely having a *closed range*, which is exactly what universal closedness
supplies. Concretely `@IsSeparated = diagonal @UniversallyClosed`
(`isSeparated_eq_diagonal_universallyClosed`). Descent of `@IsSeparated` then follows from the
existing `@UniversallyClosed` descent through mathlib's `diagonal`-descent combinator, with no
`SurjectiveOnStalks` descent anywhere. Properness follows by `MorphismProperty.DescendsAlong.inf`
from `isProper_eq` together with the descent of `@UniversallyClosed` and `@LocallyOfFiniteType`.

These are pure `AlgebraicGeometry` statements with only mathlib imports; they are natural
candidates for upstreaming.
-/

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

/-- On diagonals — which are always immersions, hence preimmersions with `SurjectiveOnStalks`
holding automatically — being a closed immersion is equivalent to being universally closed:
closedness of the range is the only condition beyond preimmersion, and that is exactly what
universal closedness supplies. Hence `@IsSeparated`, which is `diagonal @IsClosedImmersion`,
equals `diagonal @UniversallyClosed`. -/
theorem isSeparated_eq_diagonal_universallyClosed :
    @IsSeparated = MorphismProperty.diagonal @UniversallyClosed := by
  rw [IsSeparated.isSeparated_eq_diagonal_isClosedImmersion]
  ext X Y f
  rw [MorphismProperty.diagonal_iff, MorphismProperty.diagonal_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · haveI := h; infer_instance
  · haveI := h
    -- `pullback.diagonal f` is an immersion, so a preimmersion; universal closedness gives it a
    -- closed range, upgrading it to a closed immersion.
    refine IsClosedImmersion.of_isPreimmersion _ ?_
    rw [← Set.image_univ]
    exact (pullback.diagonal f).isClosedMap _ isClosed_univ

/-- Separatedness satisfies fpqc descent: it descends along
`@Surjective ⊓ @Flat ⊓ @QuasiCompact`. This avoids any codescent of `SurjectiveOnStalks`,
routing entirely through the descent of `@UniversallyClosed` (see
`isSeparated_eq_diagonal_universallyClosed`). -/
instance descendsAlong_isSeparated_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @IsSeparated (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [isSeparated_eq_diagonal_universallyClosed]
  infer_instance

/-- Properness satisfies fpqc descent: it descends along
`@Surjective ⊓ @Flat ⊓ @QuasiCompact`. This follows from the descent of its three factors
(`@IsSeparated`, `@UniversallyClosed`, `@LocallyOfFiniteType`) via `isProper_eq` and
`MorphismProperty.DescendsAlong.inf`. -/
instance descendsAlong_isProper_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @IsProper (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [isProper_eq]
  infer_instance

end AlgebraicGeometry
