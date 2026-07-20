# References for the Belyi formalization

This directory collects the source material for the project:

* [`proof-outline.md`](proof-outline.md) — the mathematical roadmap. All statements
  are labelled (`B1`, `B2`, …); the child issues of
  [taxis issue #18](https://taxis.lana.merten.dev/#/issues/18) refer to these labels.
* [`sources/`](sources/) — local copies of the freely available papers, fetched by
  [`fetch-sources.sh`](fetch-sources.sh) (not committed; run the script once after
  cloning).

## Annotated bibliography

### Primary source

* **[Belyi1979]** G. V. Belyi, *On Galois extensions of a maximal cyclotomic field*,
  Izv. Akad. Nauk SSSR Ser. Mat. 43 (1979), 267–276; English translation:
  Math. USSR Izv. 14 (1980), 247–256.
  The original paper. §2 contains the descending induction producing a map ramified
  only over `{0, 1, ∞}` from an arbitrary finite map with algebraic branch points
  (statements B6–B8 in the outline). Not freely available; use the library copy.

### The "obvious" direction (Belyi map ⇒ definable over ℚ̄)

* **[Koeck2004]** B. Köck, *Belyi's theorem revisited*, Beiträge Algebra Geom. 45
  (2004), 253–265. [arXiv:math/0108222](https://arxiv.org/abs/math/0108222).
  A careful, purely algebraic proof of the descent direction (statements B9–B12),
  fixing gaps in earlier write-ups. This is the main reference for the converse
  direction: spreading out a Belyi pair over a ℚ̄-variety and specializing.

* **[GonzalezDiez2006]** G. González-Diez, *Variations on Belyi's theorem*,
  Q. J. Math. 57 (2006), 339–354.
  An analytic/moduli proof of the descent direction via the finite-orbit criterion
  for fields of moduli. Useful as an alternative route to B11.

### Textbook expositions

* **[Szamuely2009]** T. Szamuely, *Galois Groups and Fundamental Groups*, Cambridge
  Studies in Advanced Mathematics 117, CUP 2009.
  §4.7–4.8: complete proof of Belyi's theorem (Theorem 4.7.6) in scheme-theoretic
  language, including the Riemann existence input and the specialization argument.
  The closest existing exposition to the intended formalization.

* **[GirondoGonzalezDiez2012]** E. Girondo, G. González-Diez, *Introduction to
  Compact Riemann Surfaces and Dessins d'Enfants*, LMS Student Texts 79, CUP 2012.
  Ch. 3–4: Belyi's theorem and dessins from the Riemann-surface viewpoint; explicit
  treatment of the polynomial reduction steps (B6–B8).

### Surveys / context

* **[Zapponi2003]** L. Zapponi, *What is a dessin d'enfant?*, Notices AMS 50 (2003),
  788–789. [PDF](https://www.ams.org/notices/200307/what-is.pdf).
  Two-page overview and statement.

* **[Guillot2014]** P. Guillot, *An elementary approach to dessins d'enfants and the
  Grothendieck–Teichmüller group*, Enseign. Math. 60 (2014), 293–375.
  [arXiv:1309.1968](https://arxiv.org/abs/1309.1968).
  §1–4: covers, monodromy and the equivalence between finite covers of
  `ℙ¹ ∖ {0, 1, ∞}` and finite sets with an action of the free group on two
  generators (background for B9/B10).

### Downstream use (context only, not needed for this project)

* S. Mochizuki, *Topics in Absolute Anabelian Geometry II* (Example 3.6,
  Cor. 3.7–3.8) and *III* (§1): Belyi cuspidalization, the consumer of the
  marked-curve form B13. See the description of taxis issue #18.
