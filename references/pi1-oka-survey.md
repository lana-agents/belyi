# Survey: what `chrisflav/pi1` and `chrisflav/oka` provide toward Belyi's theorem

Taxis issue **#210** — *Survey requirements about étale fundamental groups and GAGA*.

The two deepest inputs to the **converse** direction of Belyi's theorem
(`references/proof-outline.md`, statements **B9 → B11**) are currently isolated as
sanctioned `sorry`s (see `references/rigidity-design.md` §0, `references/converse-design.md`
§0):

* **B9** — `Belyi.rigidity_finiteness` (`Belyi/Rigidity.lean`, taxis **#194**): finiteness of
  degree-`≤ d` covers of `ℙ¹_k` étale outside `{0,1,∞}`. Its mathematical justification is
  **Riemann existence + the computation `π₁ᵉᵗ(ℙ¹_k ∖ {0,1,∞}) ≅ F̂₂`**.
* **B10(ii)/B11** — `belyi_spreadOut`, `spreadOut_isotrivial_point`
  (`Belyi/SpreadOut.lean`, `Belyi/Descent.lean`, taxis **#199/#200**): spreading out + the
  isotriviality argument (EGA IV limit formalism; Köck rigidity).

Both `references/rigidity-design.md` §2 and `references/converse-design.md` §4 diagnose the
wall the same way: *mathlib v4.32 has the Galois-category framework but no analytification,
no GAGA, no Riemann existence, and no computation of any étale fundamental group.* This
document surveys two external Lean 4 / Mathlib v4.32 formalisation projects that target
exactly that gap, records what they provide, and scopes what is **still required** if their
content is assumed. It is the first deliverable of #210; the concrete follow-up work is filed
as child issues (§5).

> **Scope caveat.** This is a survey of *external, not-yet-upstreamed* repositories, read at
> the commit state of 2026-07-23. Nothing here is imported by the project build. The purpose
> is to decide which of the sanctioned `sorry`s could, *in principle and modulo a clearly
> enumerated remaining chain*, be discharged by depending on (or upstreaming) `pi1`/`oka`,
> and to give each remaining link an exact statement and a reference. It does **not** propose
> adding either as a build dependency now: both are moving targets and `pi1`'s own README says
> "everything will eventually be integrated into mathlib".

---

## 1. `chrisflav/pi1` — the étale fundamental group

**Repository.** <https://github.com/chrisflav/pi1>. Lean 4 / Mathlib **v4.32.0** (matches this
project's pin). Authors incl. Christian Merten. ~119 commits. Apache-2.0. Root: `Pi1.lean`.

**Purpose (README).** Formalise the étale fundamental group of a connected scheme as the
automorphism group of a fibre functor, and show the category of finite étale covers is a
Galois category, hence equivalent to finite continuous `π₁ᵉᵗ`-sets.

### 1a. What it provides (exact API, `Pi1/FundamentalGroup/`)

* `AlgebraicGeometry.FiniteEtale (X : Scheme)` — the category of schemes finite étale over
  `X` (`FiniteEtale.lean`).
* `instance galoisCategory [ConnectedSpace X] : GaloisCategory (FiniteEtale X)`
  (`Galois.lean`). Also the `PreGaloisCategory` instance.
* `def fiber (ξ) : FiniteEtale X ⥤ FintypeCat` — the geometric fibre functor at a geometric
  point `ξ : Spec Ω ⟶ X` (`Ω` sep. closed), and
  `instance fiberFunctor [ConnectedSpace X] [IsSepClosed Ω] : FiberFunctor (fiber ξ)`.
* `notation "π₁ᵉᵗ(" x ")" => Aut (fiber x)`, together with the profinite-group structure:
  `IsTopologicalGroup`, `T2Space`, `TotallyDisconnectedSpace`, `CompactSpace` on `π₁ᵉᵗ(ξ)`.
* `def equivFintypeCat [IsSepClosed Ω] : FiniteEtale (Spec (.of Ω)) ≌ FintypeCat` — over a
  separably closed field the finite étale category is just finite sets.
* `Rank.lean`: `Scheme.Hom.finrank` for a flat, finite, locally-of-finite-presentation
  morphism, and `finrank_eq_const_of_preconnectedSpace` — the rank (= degree of the cover) is
  constant on a connected base. This is the project's `deg`-of-a-cover invariant.
* Supporting: `Point.lean` (geometric points), `AffineAnd.lean`, `AffineColimits.lean`
  (finite étale is closed under the relevant (co)limits), plus `Pi1/RingTheory/FiniteEtale/`
  (`Basic`, `Descent`, `Equalizer`) and Mathlib-shim files.

### 1b. What it does **not** provide (confirmed by the full file tree)

* **No computation of any étale fundamental group.** There is no file identifying
  `π₁ᵉᵗ(ℙ¹ ∖ {0,1,∞})`, or even its finite quotients, with `F̂₂` or any free profinite group.
* **No analytification, no comparison with topology, no Riemann existence.** Nothing connects
  `π₁ᵉᵗ` to a topological fundamental group or to covering spaces.
* **No base-field-invariance theorem** for the finite étale category / `π₁ᵉᵗ` under extension
  of algebraically closed fields of characteristic 0 (SGA 1 XIII 4.6).
* **No "finitely many covers of bounded degree"** statement — this is exactly B9 and is
  precisely what is missing (see §3).

**Net.** `pi1` supplies the entire *categorical target* named as "present and usable" in
`rigidity-design.md` §2 — but as a ready-to-use Galois-category **instance** on the concrete
`FiniteEtale X`, which mathlib alone does not give you (mathlib has the abstract Galois
machinery; `pi1` discharges its hypotheses for finite étale covers of schemes). Combined with
mathlib's `CategoryTheory/Galois` equivalence to `Action FintypeCat (Aut F)`, assuming `pi1`
gives:

> finite étale covers of a connected scheme `U`, up to iso, `≃` finite continuous
> `π₁ᵉᵗ(U)`-sets, up to iso; and degree `=` cardinality of the fibre (`Rank.finrank`).

This reduces **B9 to a single statement about `π₁ᵉᵗ(ℙ¹∖{0,1,∞})`**: *it is topologically
finitely generated* (see §3, link (E)). That is the Riemann-existence content, and it is
**not** in `pi1`.

---

## 2. `chrisflav/oka` — complex analytic spaces and Oka coherence

**Repository.** <https://github.com/chrisflav/oka>. Lean 4 / Mathlib **v4.32.0** (matches).
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. Apache-2.0.

**Purpose (README).** Formalise **Oka's coherence theorem**: the structure sheaf of a complex
analytic space is a coherent sheaf of modules over itself. Main theorem proven; some gaps
remain in the analytic core.

### 2a. What it provides

* `Oka/OkaRing.lean`, `LocalOkaRing.lean` — holomorphic functions on opens of `ℂⁿ` and their
  germs (convergent power series).
* `Oka/Weierstrass.lean` — Weierstrass preparation and division.
* `Oka/OkaLemma.lean`, `Statement.lean` — Oka's bounded-degree lemma and the coherence lemma
  on `ℂⁿ`.
* `Oka/AnalyticSpace/` — **complex analytic spaces as locally ringed spaces**, and the
  coherence of their structure sheaf.
* `Oka/Algebra/Category/` — coherent sheaves of modules on a site.

### 2b. What it does **not** provide

* **No GAGA.** Oka coherence (`𝒪_X` is coherent) is a *prerequisite* for Serre's GAGA, not
  GAGA itself: there is no analytification of *algebraic* coherent sheaves, and no comparison
  theorem `Hⁱ(X, ℱ) ≅ Hⁱ(Xᵃⁿ, ℱᵃⁿ)` for proper `X/ℂ`.
* **No analytification functor** `Scheme /ℂ ⤳ AnalyticSpace`.
* **No Riemann existence theorem** and no fundamental-group content.

**Net.** `oka` supplies the *analytic substrate* — a usable category of complex analytic
spaces with a coherent structure sheaf — on which an analytification functor and GAGA could be
built. It is the hardest purely-analytic prerequisite (coherence of `𝒪_{Xᵃⁿ}`), and having it
turns "build GAGA from nothing" into "build the analytification functor and the comparison
map, then run the standard coherent-cohomology dévissage".

---

## 3. What is still required, assuming `pi1` + `oka`

Goal: discharge **B9** (`rigidity_finiteness`), the deepest converse input. Below, each link is
either **HAVE** (`pi1`/`oka`/mathlib), **PROVABLE now** (mathlib only, no analytic input), or
**REQUIRED** (the remaining chain). Statements are given in the project's vocabulary where it
already exists.

Let `k` be algebraically closed of characteristic `0`, `U := ℙ¹_k ∖ {0,1,∞}`.

**(A) HAVE — Galois dictionary.** Assuming `pi1.galoisCategory` + mathlib
`CategoryTheory/Galois`: iso-classes of finite étale covers of `U` of degree `≤ d` `≃`
iso-classes of finite continuous `π₁ᵉᵗ(U)`-sets of cardinality `≤ d`, with degree `=`
cardinality via `Rank.finrank`.

**(B) PROVABLE now (mathlib only) — group theory, no geometry.** *A topologically finitely
generated profinite group `G` admits only finitely many continuous homomorphisms to any fixed
finite group, hence only finitely many open subgroups of index `≤ d`, hence only finitely many
iso-classes of finite continuous `G`-sets of cardinality `≤ d`.* This is the profinite
analogue of the free-group lemma already scoped as #52b (`rigidity-design.md` §3b); mathlib
has `ProfiniteGrp`, `Subgroup.index`, `Group.FG`/topological generation, and
`MonoidHom` finiteness by evaluation on generators. **No `pi1`/`oka` needed.** Reference:
Ribes–Zalesskii, *Profinite Groups*, §2.

**(C) REQUIRED — analytification functor.** A functor `(-)ᵃⁿ` from schemes locally of finite
type over `Spec ℂ` to `oka`'s complex analytic spaces, on the underlying set the `ℂ`-points
with the analytic topology, compatible with structure sheaves; sending finite étale morphisms
to finite topological covering maps. Exact target: `(-)ᵃⁿ : Scheme.lft ℂ ⥤ Oka.AnalyticSpace`
with `(f finite étale) ⇒ (fᵃⁿ a finite covering map)`. Reference: SGA 1, Exp. XII;
[Serre, GAGA, 1956]. Builds on `oka`'s `AnalyticSpace`.

**(D) REQUIRED — Riemann existence (the crux analytic comparison).** For `U` a smooth variety
over `ℂ`, `(-)ᵃⁿ` induces an **equivalence** between finite étale covers of `U` and finite
covering spaces of `Uᵃⁿ`. Exact statement: `FiniteEtale U ≌ FiniteCovering Uᵃⁿ` (finite
topological covers). Reference: SGA 1, Exp. XII, Thm 5.1; Grauert–Remmert. Needs (C) + GAGA
(coherent-sheaf comparison, on top of `oka` coherence) for the algebraisation of analytic
covers.

**(E) REQUIRED — profinite completion + computation.** Composing (A)+(D) with mathlib's Galois
equivalence gives `π₁ᵉᵗ(U) ≅ (π₁ᵗᵒᵖ(Uᵃⁿ))^` (profinite completion). Combined with the
**topological** fact `π₁ᵗᵒᵖ((ℙ¹ℂ)ᵃⁿ ∖ {0,1,∞}) ≅ FreeGroup (Fin 2)` (the thrice-punctured
sphere is homotopy-equivalent to a wedge of two circles; van Kampen), conclude
`π₁ᵉᵗ(ℙ¹_ℂ ∖ {0,1,∞})` is topologically finitely generated (its finite quotients factor
through `F̂₂`). Reference: SGA 1 XII 5.2; [Szamuely2009] §4.6. The topological input
`π₁ᵗᵒᵖ(S² ∖ 3 pts) ≅ F₂` is its own sub-task (mathlib's `FundamentalGroup` exists but van
Kampen / this computation does not) — **provable in principle without `pi1`/`oka`**, purely in
`AlgebraicTopology`.

**(F) REQUIRED — base-field invariance.** Transfer topological finite generation of
`π₁ᵉᵗ(ℙ¹∖{0,1,∞})` from `ℂ` to an arbitrary algebraically closed `k` of char 0 (and to
`ℚ̄(V)‾`, the field B11 works over). Exact statement: for `k ⊆ k'` algebraically closed of
char 0, base change `FiniteEtale (ℙ¹_k ∖ {0,1,∞}) ≌ FiniteEtale (ℙ¹_{k'} ∖ {0,1,∞})`, hence
`π₁ᵉᵗ` agrees. Reference: SGA 1, Exp. XIII, 4.6. Part of this (base change of the finite étale
category) may be within reach of `pi1`'s descent files; the char-0 invariance is the deep part.

**(G) PROVABLE now — project bridge.** Identify the project's `BelyiCover k d` (degree-`≤ d`
curve `X` with finite `f : X ⟶ ℙ¹_k` étale outside `{0,1,∞}`) with rank-`≤ d` objects of
`FiniteEtale U` via restriction over `U` and **normalisation of `ℙ¹` in the function field**
for the reverse (compactification). Exact statement: an equivalence of the "iso over `ℙ¹`"
groupoid of `BelyiCover k d` with the rank-`≤ d` full subcategory of `FiniteEtale U`, matching
`deg` with `Rank.finrank`. mathlib has `AlgebraicGeometry.Normalization`; this is project-side
glue, **no `pi1`/`oka` needed** beyond the `FiniteEtale U` object.

**Assembly.** (G) + (A) + (B), with (E)+(F) supplying "`π₁ᵉᵗ(U)` topologically finitely
generated", discharge `rigidity_finiteness`. The genuinely *new* analytic content that
`pi1`/`oka` do **not** already give is exactly **(C), (D), (E-topological), (F)** — i.e.
analytification, Riemann existence, the one topological `π₁` computation, and char-0
base-field invariance.

### 3'. What `pi1` + `oka` do **not** help with at all

* **B10 (spreading out)** — EGA IV limit formalism over a smooth `ℚ̄`-variety
  (`Belyi/SpreadOut.lean`, #200). Orthogonal to `pi1`/`oka`; still requires the mathlib
  spreading-out toolkit (`AffineTransitionLimit.lean`, `SpreadingOut.lean`) plus openness of
  good-fibre loci. Not addressed here.
* **B11 constructibility / isom-scheme** (`Belyi/Descent.lean`, #199/#200) — Chevalley
  constructibility of the image of the isomorphism scheme. Orthogonal.
* **Faithfully-flat descent bricks** (#168, #183) — a different mathlib gap.

So even assuming both repositories in full, the converse still rests on B10 + the B11
constructibility input. `pi1` + `oka` address **only the B9 (rigidity) input** — but that is
the single deepest one and the one both design docs flag first.

---

## 4. Verdict

* **`pi1` is directly usable and squarely on the B9 critical path.** It removes the
  "categorical target" half of the B9 wall (`rigidity-design.md` §2) by providing the
  Galois-category instance and the profinite `π₁ᵉᵗ`. After (G) bridges the project's covers to
  `FiniteEtale U`, **B9 reduces to a single group-theoretic finiteness fact (B, provable now)
  plus one input: `π₁ᵉᵗ(ℙ¹∖{0,1,∞})` is topologically finitely generated.**
* **`oka` is the analytic substrate for that one input** (via (C)→(D)→(E)), but a substantial
  chain — analytification, GAGA-style comparison, Riemann existence, one topological `π₁`
  computation, char-0 base-field invariance — remains between `oka` and a proof. Each link is
  a recognised, referenced theorem; none is in mathlib v4.32.
* **Recommended immediate, dependency-free wins** (do not need either repo as a build dep):
  the group theory **(B)** and the topological computation `π₁ᵗᵒᵖ(S²∖3) ≅ F₂` (part of **E**).
  Both are self-contained, upstreamable, and are genuine evidence for the sanctioned axioms.
* **Recommended `pi1`-assuming work:** the project bridge **(G)** and the Galois dictionary
  **(A)** wiring — these turn `rigidity_finiteness` from an opaque axiom into "axiom = `π₁ᵉᵗ(U)`
  topologically finitely generated", a much sharper and smaller sanctioned input.
* **`oka`-assuming work (C/D/E/F)** is large and research-grade; it is the honest home of the
  remaining Riemann-existence content and should be tracked, not speculatively attempted.

The child issues below (§5) file each link with an exact target statement and a reference.

## 5. Child issues filed under #210

Filed as sub-issues of #210 (see the taxis tracker for live status). Each names the exact
required statement and a reference; dependency-free ones are marked *ready now*.

* **#210-B** *(ready now, mathlib-only)* — Profinite finiteness: a topologically finitely
  generated profinite group has finitely many continuous homs to a finite group / open
  subgroups of index `≤ d`. Link (B).
* **#210-E-top** *(ready now, mathlib-only, topology)* — `π₁ᵗᵒᵖ` of the thrice-punctured
  Riemann sphere is `FreeGroup (Fin 2)`. Link (E, topological part).
* **#210-G** *(ready now, `pi1` object only)* — Project bridge: `BelyiCover k d` groupoid `≃`
  rank-`≤ d` finite étale covers of `ℙ¹∖{0,1,∞}`, matching `deg`/`finrank`. Link (G).
* **#210-A** *(assumes `pi1`)* — Galois dictionary wiring: finite étale covers of `U` `≃`
  finite `π₁ᵉᵗ(U)`-sets, degree = cardinality; reduce `rigidity_finiteness` to "`π₁ᵉᵗ(U)`
  topologically finitely generated". Link (A).
* **#210-CDE** *(research-grade, assumes `oka`)* — Analytification + Riemann existence:
  `(-)ᵃⁿ : Scheme.lft ℂ ⥤ Oka.AnalyticSpace` and `FiniteEtale U ≌ FiniteCovering Uᵃⁿ`. Links
  (C),(D),(E-comparison). Blocked / tracked.
* **#210-F** *(research-grade)* — Char-0 base-field invariance of the finite étale category /
  `π₁ᵉᵗ` of `ℙ¹∖{0,1,∞}` (SGA 1 XIII 4.6). Link (F). Blocked / tracked.

## References

* [Serre1956] J.-P. Serre, *Géométrie algébrique et géométrie analytique* (GAGA).
* SGA 1 (Grothendieck), Exp. **XII** (Riemann existence, analytification), Exp. **XIII**
  (finite generation and base-field invariance of `π₁ᵉᵗ`; 4.6).
* [Szamuely2009] *Galois Groups and Fundamental Groups*, §4.6, §4.8.
* [Koeck2004] *Belyi's theorem revisited* (`references/sources/koeck-belyi-revisited.pdf`).
* Grauert–Remmert, *Coherent Analytic Sheaves*; Ribes–Zalesskii, *Profinite Groups*.
* `chrisflav/pi1` (étale `π₁`, Galois category), `chrisflav/oka` (complex analytic spaces,
  Oka coherence) — both Lean 4 / Mathlib v4.32.0, read at 2026-07-23.
</content>
</invoke>
