# Belyi's theorem in Lean 4

A formalization of **Belyi's theorem** in Lean 4 building on
[mathlib](https://github.com/leanprover-community/mathlib4):

> A smooth projective geometrically connected curve over `ℂ` is definable over `ℚ̄`
> if and only if it admits a finite morphism to `ℙ¹` whose branch locus is contained
> in `{0, 1, ∞}`.

The project covers both directions of the theorem, invariance under base change and
isomorphism, and a marked-curve form in which a prescribed finite set of closed
points is enlarged into the inverse image of `{0, 1, ∞}`.

Project coordination happens on the
[taxis issue tracker](https://taxis.lana.merten.dev/#/issues/18); the project is
divided into child issues of issue #18. The mathematical background, an annotated
bibliography and a detailed proof outline (with statement labels referenced by the
issues) live in [`references/`](references/).

## Building

The project uses the Lean toolchain pinned in [`lean-toolchain`](lean-toolchain) and
the matching mathlib release. With [elan](https://github.com/leanprover/elan)
installed:

```sh
lake exe cache get   # fetch prebuilt mathlib oleans
lake build
```

## Structure

* `Belyi/` — the Lean library (root module: `Belyi.lean`).
* `references/` — bibliography, proof outline and locally prepared source material.
* `.github/workflows/` — CI: build + doc generation on every push/PR
  (`lean_action_ci.yml`), toolchain release tagging (`create-release.yml`) and
  manually triggered mathlib bumps (`update.yml`).

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
