# Converse direction (B10–B12): design decision and formalization boundary

Taxis issue **#53** — *Converse direction: curves with a Belyi map descend to `ℚ̄`*.
This is the second half of Belyi's theorem (`references/proof-outline.md`, statements
**B10 → B11 → B12**, feeding on the rigidity input **B9** of issue #52). This document is
the issue's **first deliverable**: it fixes *what is proved vs. what is axiomatized*, the
exact Lean statement of **B12**, the interfaces of the axiomatized inputs, and the split
into child issues. It is a proposal for maintainer sign-off before any large-scale proof
work, and it mirrors the shape of the already-approved `references/rigidity-design.md`
(the analogous first deliverable of #52).

## 0. TL;DR of the decision

* The converse rests on **three** pieces of infrastructure that are genuinely far from
  mathlib v4.32 and are, individually, research-grade: **B9** (rigidity/finiteness of
  covers — Riemann existence; already axiomatized in `Belyi/Rigidity.lean` per #52),
  **B10** (spreading out a Belyi pair to a family over a `ℚ̄`-variety — EGA IV limit
  formalism), and the **faithfully-flat descent infrastructure** (B3c/B3d/B2b, issues
  #167/#168/#183) needed to recognise the special ℚ̄-fibre as a genuine curve model of `X`
  and to match branch loci.
* Following the precedent set by #52 for B9, the converse is formalized against a **fixed,
  clearly-named interface of sanctioned axioms/hypotheses** for the mathlib-absent inputs,
  with the **actual Köck rigidity argument (B11)** — the mathematical content that is
  *not* a generic EGA fact — carried as far as the interface allows. Concretely:
  - **B10** is packaged as a Lean **`structure SpreadOut`** bundling the output of
    spreading out (a family `𝒳 ⟶ ℙ¹_U ⟶ U` over a dense open `U` of a smooth affine
    `ℚ̄`-variety, with Belyi fibres and a generic-fibre identification), plus **one
    sanctioned axiom** `belyi_spreadOut` producing such a structure from a Belyi pair over
    `ℂ`. This isolates the EGA limit formalism exactly as `rigidity_finiteness` isolates
    Riemann existence.
  - **B11** (the rigidity/isotriviality step) consumes `rigidity_finiteness` (#52) together
    with a `SpreadOut` datum and produces a `ℚ̄`-point `u ∈ U(ℚ̄)` whose fibre is
    isomorphic, over `ℙ¹`, to the geometric generic fibre — hence to `(X, f)` after base
    change. The *combinatorics* of "finitely many iso-classes ⇒ constant on a dense open ⇒
    a ℚ̄-point works" is where genuine Lean content lives; the precise constructibility /
    isom-scheme input from [Koeck2004, Thm 2.2] is itself partly axiomatized (see §3).
  - **B12** assembles B10 + B11 into `DefinableOverPair ℚ̄ ℂ X f` (pair version) and
    `DefinableOver ℚ̄ ℂ X` (scheme version), the exact predicates the forward direction
    produces and the main theorem #55 consumes.
* **Honest scope.** With mathlib v4.32 this design does **not** yield an axiom-free converse;
  it yields a converse **modulo a small, explicitly enumerated set of sanctioned axioms**
  (B9 rigidity — already sanctioned; B10 spreading-out; and the B11 isom-scheme
  constructibility input), each isolated in one named place, plus the descent bricks of
  #167/#168 for the fibre-recognition step. The forward direction (#51) stays axiom-free.
  The main theorem #55 will therefore be `belyi_iff` **relative to the sanctioned axioms**,
  with `#print axioms` enumerating exactly `rigidity_finiteness`, `belyi_spreadOut`, and the
  B11 input — nothing else.

## 1. The mathematical statements (recap of the outline)

Fix `ℚ̄ ⊆ ℂ` (`ℚ̄ = AlgebraicClosure ℚ` with a fixed embedding, as the outline's B14b notes,
so no choice-of-embedding invariance is needed). Let `(X, f : X ⟶ ℙ¹_ℂ)` be a Belyi pair
over `ℂ` with `X` a curve.

* **(B10) Spreading out.** `(X, f)` is of finite presentation, hence definable over a
  subfield `L ⊆ ℂ` finitely generated over `ℚ̄`. Writing `L = ℚ̄(V)` for a smooth affine
  `ℚ̄`-variety `V`, spread `(X_L, f_L)` out to a family `𝒳 ⟶ ℙ¹_U ⟶ U` over a dense open
  `U ⊆ V` such that every closed fibre `(𝒳_u, f_u)` (`u ∈ U`) is a Belyi pair over `ℚ̄` and
  the generic fibre base-changed to `ℂ` recovers `(X, f)`. [Koeck2004, §2; standard
  spreading-out; Szamuely2009, §4.8.]

* **(B11) Descent through the family (rigidity/isotriviality).** By B9 over `ℚ̄(V)‾` there
  are only finitely many degree-`≤ d` covers of `ℙ¹` étale outside `{0,1,∞}` up to iso, so
  the family `𝒳/U` is isotrivial on a dense open: the geometric generic fibre is isomorphic
  as a cover to `𝒳_u` for a closed point `u ∈ U(ℚ̄)`. [Koeck2004, Thm 2.2] realises this via
  the isomorphism scheme `Isom_U(𝒳, 𝒳')` being of finite type over `U`, whose image is
  constructible and, if dominant, contains a dense open with a `ℚ̄`-point.

* **(B12) Converse.** Hence `X` (and the pair `(X, f)`) is definable over `ℚ̄`:
  `(𝒳_u, f_u) ×_ℚ̄ ℂ ≅ (X, f)` over `ℙ¹_ℂ`.

## 2. The Lean target statement (B12)

The forward direction delivers (`Belyi/Forward.lean`, `Belyi/ForwardPair.lean`):

```text
exists_isBelyiMap_of_isCurveOver (k) [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
    (X) [X.Over (Spec k)] [IsCurveOver k X] : ∃ f : X ⟶ P1 k, IsBelyiMap k f
exists_definableOverPair_isBelyiMap_baseChange_of_isCurveOver … : … DefinableOverPair k K …
```

The converse must produce the **same** predicates in the opposite direction. Target shape,
stated over the abstract field `K` playing the role of `ℂ` (an algebraically closed
characteristic-zero field containing the working `ℚ̄ = k`; the model case is `k = ℚ̄`,
`K = ℂ`):

```text
/-- **B12 (converse), pair version.** A Belyi pair over `ℂ` is definable over `ℚ̄`. -/
theorem definableOverPair_of_isBelyiMap
    (k K) [Field k] [IsAlgClosed k] [CharZero k] [Algebra.IsAlgebraic ℚ k]
    [Field K] [IsAlgClosed K] [CharZero K] [Algebra k K]
    (X) [X.Over (Spec K)] [IsCurveOver K X]
    (f : X ⟶ P1 K) (hf : IsBelyiMap K f) :
    DefinableOverPair k K X f

/-- **B12 (converse), scheme version.** -/
theorem definableOver_of_exists_isBelyiMap … [IsCurveOver K X]
    (h : ∃ f : X ⟶ P1 K, IsBelyiMap K f) : DefinableOver k K X
```

The pair version implies the scheme version through `DefinableOverPair.definableOver`
(already merged). `DefinableOverPair k K X f` is the existence of a model
`f₀ : X₀ ⟶ ℙ¹_k` with base change identified with `f` — precisely the `(𝒳_u, f_u)` produced
by B11 with `X₀ := 𝒳_u`. **This is the interface contract**: B11 must hand back its `ℚ̄`-fibre
in exactly the `DefinableOverPair` shape (a model + a base-change identification), so the
final `exact` in B12 is definitional bookkeeping, not new mathematics.

## 3. The formalization boundary and the sanctioned interface

### 3a. B10 — two sub-steps: a *provable* descent-to-a-subfield, then an axiomatized family

B10 splits cleanly into two very different sub-steps, and the mathlib audit (§4) shows the
boundary between them falls **inside** B10, not at its edge:

* **B10(i) — definability over a finitely generated subfield `L ⊆ ℂ` (PROVABLE today).**
  "`(X, f)` is of finite presentation, hence definable over a subfield `L ⊆ ℂ` finitely
  generated over `ℚ̄`" is achievable against mathlib v4.32 via the
  `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` machinery (`Spec ℂ = lim Spec R_i`
  over the cofiltered diagram of `ℚ̄`-finitely-generated subalgebras; descend the finite-
  presentation morphism `f` and the scheme `X` to some stage, recover `(X, f)` by base
  change). This produces `DefinableOverPair L ℂ X f` (and `DefinableOver L ℂ X`) for some
  intermediate `ℚ̄ ⊆ L ⊆ ℂ` with `L/ℚ̄` finitely generated. See §4 for the exact lemma names;
  this is real, sorry-free, axiom-free Lean and is the converse's genuinely provable nugget.
* **B10(ii) — spreading `L = ℚ̄(V)` out to a family with good fibres (RESEARCH-GRADE).**
  Realising `L` as the function field of a smooth affine `ℚ̄`-variety `V` and propagating the
  Belyi-pair property from the generic fibre to a dense open `U ⊆ V` of closed `ℚ̄`-fibres is
  EGA IV constructibility/openness-of-good-fibres, absent from mathlib (§4). This is the part
  packaged and axiomatized.

Spreading out to a family with good fibres (B10(ii)) is EGA IV §8–§17 limit formalism.
Mathlib v4.32 has a **starting toolkit** but not the specific outputs (see §4). We therefore
**package the output** and **axiomatize its existence**, exactly as B9 axiomatizes finiteness:

```text
/-- The data produced by spreading out a Belyi pair `(X, f)` over `K = ℂ` to a family over a
dense open of a smooth affine `ℚ̄`-variety.  All fibres over closed `ℚ̄`-points are Belyi
pairs; the generic fibre base-changed to `K` recovers `(X, f)`. -/
structure SpreadOut (k K) [Field k] … [Algebra k K] (X) (f : X ⟶ P1 K) where
  base       : Scheme          -- U, a smooth affine ℚ̄-variety (dense open of V)
  [baseOver  : base.Over (Spec k)]
  total      : Scheme          -- 𝒳
  fibreMap   : total ⟶ …       -- 𝒳 ⟶ ℙ¹_U over U
  -- every closed ℚ̄-point u ∈ U gives a Belyi pair (𝒳_u, f_u) over ℚ̄:
  fibre_isBelyi : ∀ u : (Spec k ⟶ base), IsBelyiMap k (fibreAt … u)
  fibre_isCurve : ∀ u : …, IsCurveOver k (fibreAt … u).left
  -- degree bound d (so B9 applies) and the generic-fibre / base-change identification to (X, f):
  deg_le     : ∀ u, degree (fibreAt … u) ≤ d
  generic_eq : DefinableOverPair k K X f  -- "the geometric generic fibre is (X,f)", after ℚ̄(V)‾

/-- **B10 (spreading out), axiomatized.**  Every Belyi pair over `K = ℂ` spreads out. -/
axiom belyi_spreadOut (k K) … (X) [IsCurveOver K X] (f) (hf : IsBelyiMap K f) :
    Nonempty (SpreadOut k K X f)
```

The exact field list is design work for the child issue (§4, #53a): it must be *just enough*
for B11 to run and for B12's final identification. Notably `generic_eq` should be phrased so
that a specialization `u ∈ U(ℚ̄)` with `𝒳_u ≅ 𝒳_{generic geom}` yields `DefinableOverPair`.

**Alternative considered and rejected for now:** proving B10 from mathlib's
`SpreadingOut.lean`/`AffineTransitionLimit.lean` toolkit. This is a large, genuinely
research-grade effort (see §4) that also needs "write a f.g. field extension as the function
field of a smooth `ℚ̄`-variety" and openness of the good-fibre loci — neither in mathlib.
It is filed as a research-grade tracker (#53d) analogous to #194/#183, not a blocker.

### 3b. B11 — `Belyi/Descent.lean`: the rigidity argument

B11 is the one place with genuine, non-EGA mathematical content that should be *proved* to
the extent the interface allows. It consumes `rigidity_finiteness` (#52) and a `SpreadOut`
datum. The core combinatorial move — *finitely many iso-classes of fibres ⇒ the family is
isotrivial on a dense open ⇒ a `ℚ̄`-point realises the generic fibre* — rests on
[Koeck2004, Thm 2.2]'s **isomorphism-scheme constructibility** input:

> `Isom_U(𝒳, 𝒳' )` is of finite type over `U`; its image in `U` is constructible; if it
> meets the generic point it contains a dense open, which (over `ℚ̄`) has a `ℚ̄`-point.

Finiteness of type of `Isom_U` and constructibility of images (Chevalley) are, again, mostly
mathlib-absent at the required generality. The **decision** is to axiomatize the single clean
consequence B11 actually needs and prove the wrapper around it:

```text
/-- **B11 input (isom-scheme / isotriviality), axiomatized.** In a `SpreadOut` family whose
fibres fall (by B9) into finitely many iso-classes over `ℚ̄(V)‾`, some closed `ℚ̄`-point `u`
has fibre isomorphic over `ℙ¹` to the geometric generic fibre. -/
axiom spreadOut_isotrivial_point (S : SpreadOut k K X f) :
    ∃ u : (Spec k ⟶ S.base), BelyiCover.IsoRel k d (fibreCover S u) (genericGeomFibre S)
```

then **prove** `B11 : SpreadOut … → DefinableOverPair k K X f` by transporting the
identification, and **prove** B12 by `belyi_spreadOut` + B11. The reduction of
`spreadOut_isotrivial_point` to `rigidity_finiteness` (the actual "finitely many ⇒ dense
open" pigeonhole via constructibility) is recorded as the research-grade de-axiomatization
tracker (#53d). *If, on closer scoping, the pigeonhole from `Finite (BelyiCover.Iso)` to a
dense-open constant locus turns out formalizable given the `SpreadOut` interface, promote it
out of the axiom — that is the most valuable provable nugget in the converse and should be
attempted (#53c).*

**Verdict (#53c / taxis #199, attempted 2026-07-23): the nugget bottoms out — and *not* where
this section anticipated.** The wall is **not** Chevalley constructibility of `Isom_U`'s image;
it is one level earlier, at the **interface**. The `SpreadOut` structure as actually implemented
(`Belyi/SpreadOut.lean`) carries only `d : ℕ`, `base`, `basePoint`, and
`fibre : (Spec k ⟶ base) → BelyiCover k d`; the pair parameter `f` is **unused** (declared `_f`)
and `X` enters only through a typeclass, so *no field of `SpreadOut k K X f` logically ties the
family's fibres to `(X, f)`*. Consequently `(S : SpreadOut …) + hfin : Finite (BelyiCover.Iso k S.d)`
cannot prove `DefinableOverPair k K X f`: the pigeonhole on `Finite (BelyiCover.Iso)` yields at
most "two fibres of the family are isomorphic", but **no** datum connects any fibre to `(X, f)`,
which is what the conclusion asserts. This is exactly the soundness note on
`spreadOut_isotrivial_point` (`Belyi/Descent.lean`): the mathematical content is carried entirely
by `hf : IsBelyiMap K f`, so the axiom essentially *is* Belyi's converse.

To make a provable `spreadOut_isotrivial_point` even *statable*, `SpreadOut` must first be
strengthened to carry (i) the generic fibre `(𝒳_η, f_η)` over `L = ℚ̄(V)` with a base-change
identification `(𝒳_η, f_η) ×_L K ≅ (X, f)`; (ii) an actual family `𝒳 ⟶ ℙ¹_U ⟶ U` (only per-`ℚ̄`-point
`BelyiCover` fibres are stored today, not a family), so that "specialization generic → closed point"
is expressible; and (iii) the isotriviality/constructibility link between them. Items (i)–(iii) are
precisely the mathlib-absent B10(ii) + isom-scheme infrastructure of §4 that the research-grade
tracker #53d/#200 owns. **The pigeonhole nugget is therefore not separable from the research-grade
wall**; it bottoms out before Chevalley even enters. Fold #53c/#199 into #53d/#200 and leave the
axiom in place.

### 3c. Descent bricks for fibre recognition (#167/#168)

B10's `fibre_isCurve`/`generic_eq` and B12's final identification implicitly use that a
`ℚ̄`-model of a `ℂ`-curve is itself a curve (**B3c descent**, #167) and that branch loci match
under base change (**B3d/B2b**, #168). These are the faithfully-flat descent statements whose
keystone (`SurjectiveOnStalks` codescent, #183) is documented as research-grade
(`references/rigidity-design.md` §5; memory `b2b-b3d-smoothlocus-basechange-mathlib-gap.md`).
The converse design **reuses** those issues rather than duplicating them: `SpreadOut` is
phrased to *carry* `IsCurveOver`/`IsBelyiMap` on the fibres as hypotheses (produced together
with the family by `belyi_spreadOut`), so the descent bricks are needed only where #167/#168
already track them, and B11/B12 do not re-derive them.

## 4. What mathlib v4.32 has for B10, and where the wall is

*(Inventory from a direct audit of `Mathlib/AlgebraicGeometry/` at the pinned revision;
recorded on issue #53.)*

**The real workhorse — `AffineTransitionLimit.lean` (enables B10(i)).** For a cofiltered
diagram `D : I ⥤ Scheme` with affine transition maps and limit cone (`Spec ℂ = lim Spec R_i`
over the `ℚ̄`-finitely-generated subalgebras `R_i ⊆ ℂ`), the consumable lemmas are:

* `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` — descend a
  finite-**presentation** morphism into `X` to a finite stage `D.obj i` (the clause "generic
  fibre recovers `(X,f)` after base change"); affine special case
  `..._of_isAffine`. Also the finite-**type** versions
  `exists_hom_comp_eq_comp_of_locallyOfFiniteType` / `exists_hom_hom_comp_...`.
* `Scheme.exists_isAffine_of_isLimit`, `exists_isQuasiAffine_of_isLimit`,
  `exists_isOpenCover_and_isAffine` / `_of_finite`,
  `Scheme.OpenCover.exists_of_isCofiltered_of_finite` — descend the scheme, an affine open
  cover, and affine opens to a finite stage.
* section/topology helpers: `exists_appTop_π_eq_of_isLimit`, `preservesColimit_yoneda`
  (`Hom_S(-,X)` preserves the cofiltered limit for `X` of finite presentation),
  `compactSpace_of_isLimit`, `nonempty_of_isLimit`.

This is enough to build `DefinableOver L ℂ X` / `DefinableOverPair L ℂ X f` for an f.g.
subfield `L` — **B10(i) is real assembly work, not new theory.** (Prerequisite caveat: the
finiteness-descent *converse* `f` finite ⇒ model finite is still open in-repo,
`Belyi/DefinablePairFinite.lean:19-20`, tracked on #48; needed if the model map is required
finite rather than merely finite-presentation.)

**Spreading a map out of a stalk — `SpreadingOut.lean`.** This file is germ-injectivity and
spreading a map out of `Spec 𝒪_{X,x}` to an open neighbourhood
(`spread_out_of_isGermInjective'`, `@[stacks 0BX6]`), *not* family spreading over a base.
Curves are integral ⇒ `IsGermInjective` is a free instance. Useful as a component, not the
theorem. (`Belyi/RationalMap.lean:20` already uses this primitive via `PartialMap`.)

**Descent plumbing — `Morphisms/Descent.lean`, `FlatDescent.lean`, `LocalFlatDescent.lean`.**
`MorphismProperty.DescendsAlong`/`CodescendsAlong` framework + descent instances for
`Surjective`/`UniversallyClosed`/… and `Smooth`/`Etale`/`LocallyOfFinitePresentation` along
`Surjective ⊓ Flat ⊓ QuasiCompact` — descent along a **fixed faithfully-flat cover**, not down
a filtered limit (see `references/rigidity-design.md` §2 and the memory descent notes for the
turnkey list and the missing bricks #167/#168/#183).

**The wall — B10(ii) and B11 (not in mathlib v4.32):**

* **No "finitely generated field extension = function field of a smooth affine variety".**
  Nothing takes an f.g. field `L/ℚ̄` and returns a smooth affine model variety `V` with
  `L = ℚ̄(V) = colim 𝒪(U_i)`. The limit machinery is available *once you have the diagram*,
  but building `V` and the identification is on you.
* **No openness/density of the good-fibre locus** (fibres = smooth proper curve + finite map
  + branch ⊆ `{0,1,∞}`) for a family over a base. No "finite locus is open", no
  "smooth-proper-curve locus is open", no constructibility of geometrically-integral fibres
  at this generality. This is the hard heart of B10(ii); mathlib gives nothing turnkey.
* **No isomorphism scheme `Isom_U` of finite type + Chevalley constructibility of its image**
  at the required generality (the B11 input of §3b).

Conclusion: the axiomatization boundary lies **inside** B10 — B10(i) is provable, while
B10(ii) and the B11 isom-scheme input are the correct things to axiomatize, in direct analogy
with B9. The descent bricks (#167/#168/#183) are a *separate*, already-tracked mathlib gap.

## 5. Child-issue split (proposed)

* **#53e — (PROVABLE, ready now) definability over a finitely generated subfield — B10(i).**
  `Belyi/DefinableSubfield.lean`: from a Belyi pair `(X, f)` over `ℂ` (more generally over any
  algebraically closed char-0 `K ⊇ ℚ̄`), of finite presentation, produce an intermediate
  `ℚ̄ ⊆ L ⊆ ℂ` with `L/ℚ̄` finitely generated and `DefinableOverPair L ℂ X f` (hence
  `DefinableOver L ℂ X`), via the `AffineTransitionLimit.lean` machinery (§4). Sorry-free and
  **axiom-free** — the converse's genuinely provable piece. Independent of B9/B10(ii)/B11 and
  of the descent bricks; can proceed immediately. (Mind the finiteness-descent caveat of §4 /
  #48: state the model map at the finite-presentation level, or first close
  `DefinablePairFinite`'s open converse.) Depends only on the merged definability API and #46.

* **#53a — `Belyi/SpreadOut.lean`: the `SpreadOut` structure + `belyi_spreadOut` axiom.**
  Fix the exact fields of `SpreadOut` against B11's needs; state the single spreading-out
  axiom, taking the finitely generated subfield `L` from **#53e** as its input (B10(ii)
  starts where B10(i) stops). Depends on #46/#47 (curve + Belyi API), the merged definability
  API, and #53e. Coordinate the interface with #53b before finalizing. This is the converse
  analogue of #52's #52a (the statement + isolated axiom).

* **#53b — `Belyi/Descent.lean`: B11 + B12 assembly against the interface.**
  Prove `B11 : SpreadOut → DefinableOverPair` (transport of the isotriviality point's
  identification) and `B12 : IsBelyiMap → DefinableOverPair`/`DefinableOver` from
  `belyi_spreadOut` + B11 + `spreadOut_isotrivial_point`. Sorry-free modulo the sanctioned
  axioms; `#print axioms` must list exactly the sanctioned set. Depends on #53a and #52
  (`Belyi/Rigidity.lean`).

* **#53c — (provable nugget, attempt — RESOLVED 2026-07-23: bottoms out, fold into #53d/#200).**
  Investigated whether, given the `SpreadOut` interface, the reduction of
  `spreadOut_isotrivial_point` to `rigidity_finiteness` — the "finitely many iso-classes over
  a connected base ⇒ constant on a dense open ⇒ a ℚ̄-point" step — is formalizable without the
  full isom-scheme machinery. **Verdict: no** (see the boxed verdict at the end of §3b). The wall
  is not Chevalley constructibility but the interface: the implemented `SpreadOut k K X f` carries
  no field tying its fibres to `(X, f)` (the pair parameter is unused), so no pigeonhole on
  `Finite (BelyiCover.Iso)` can produce `DefinableOverPair k K X f`. Making the statement provable
  first requires strengthening `SpreadOut` with the generic-fibre identification + an actual family
  + the isotriviality link — the same mathlib-absent B10(ii)/isom-scheme infra owned by #53d/#200.
  The nugget is not separable from the research-grade wall; folded into #53d/#200, axiom left in place.

* **#53d — `[BLOCKED — research-grade]` de-axiomatize B10/B11.**
  Tracker for replacing `belyi_spreadOut` (EGA IV spreading out + generic smoothness of the
  base + openness of good-fibre loci) and `spreadOut_isotrivial_point` (isom-scheme finite
  type + Chevalley) by real proofs, gated on major mathlib additions. Off critical path;
  record the §4 wall so future scanners do not re-scope it. Analogous to #194 (B9) and #183.

## 6. Interaction with the rest of the project

* **Forward direction (#51)** is unaffected and remains axiom-free; nothing in `Belyi/Forward*`
  imports `Belyi/SpreadOut.lean` or `Belyi/Descent.lean`.
* **Main theorem (#55)** assembles `belyi_iff` from the forward `∃ f, IsBelyiMap` ⇐ side and
  the converse `⇒` side; with this design its `#print axioms` enumerates exactly
  `rigidity_finiteness` (#52), `belyi_spreadOut` and `spreadOut_isotrivial_point` (#53) — the
  sanctioned set — plus the classical `propext/Classical.choice/Quot.sound`. #55's
  definition-of-done ("no axioms beyond what the design documents explicitly sanction") is met
  by this document sanctioning the two converse axioms alongside `rigidity-design.md`'s B9.
* **Marked form (B13, #54)** is the *forward* marked strengthening and is independent of the
  converse; #55 re-exports it (B14c).
* **Descent infra (#167/#168/#183)** is reused, not duplicated: `SpreadOut` carries the fibre
  curve/Belyi data so the converse does not re-derive faithfully-flat descent.

**Honest overall assessment.** This design gives the converse a *fixed, buildable interface*
and isolates its mathlib-absent inputs into two clearly-named axioms (plus the already-
sanctioned B9), mirroring how `rigidity-design.md` handled B9. It does **not** by itself make
the converse axiom-free — that requires EGA IV spreading-out, Chevalley constructibility, and
the faithfully-flat descent bricks, all research-grade against mathlib v4.32. What it *does*
enable: (i) landing the B12 assembly (#53b) as sorry-free-modulo-sanctioned-axioms real Lean,
(ii) a scoped attempt (#53c) at the one genuinely provable rigidity nugget, and (iii) a clean
main theorem (#55) with a fully enumerated, sanctioned axiom set.

## References

* [Koeck2004] *Belyi's theorem revisited* (`references/sources/koeck-belyi-revisited.pdf`), §2
  (spreading out + the rigidity/isotriviality argument; Thm 2.2, the isomorphism scheme).
* [Szamuely2009] *Galois Groups and Fundamental Groups*, §4.8 (algebraic proof of the converse).
* [GonzalezDiez2006] the moduli-theoretic route (acceptable alternative to Köck).
* `references/rigidity-design.md` — the analogous B9 design decision (issue #52).
* `references/proof-outline.md` — statements B9–B14 and the dependency graph.
