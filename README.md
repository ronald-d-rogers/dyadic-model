# dyadic-model

A machine-checked Lean 4 formalization of the **dyadic shell model** of turbulence:
an infinite system of ODEs for the amplitudes of eddies at scales `2^k`, with a
quadratic transfer term between neighbouring scales and a dissipation term of
degree `e`,

```
u_k' = 2^k (u_{k-1}^2 - 2 u_k u_{k+1}) + kappa theta_k - nu 2^{e k} u_k
```

## What this is — and what it is not

**This is a record of a negative result.** The honest one-page verdict is
[`Cascade/OUTCOME.md`](Cascade/OUTCOME.md). The short version:

The project set out to find a finite-time blowup in a dyadic caricature of the 3D
Navier–Stokes equations, of the kind Tao suggested in his 2014 post on finite-time
blowup for averaged 3D NSE. **In this class of models it does not exist**, and the
reasons are structural rather than technical:

- the sharp per-shell bar is scale-invariant only at `e = 1`, so it is marginal
  precisely at the degree corresponding to 3D;
- at the dimension-matched degree the truncated model is provably regular;
- the Bernstein constraint that would recover a space dimension is **vacuous** for
  `d >= 2`, because the model is exactly `d = 2` Bernstein-saturated;
- genuine intermittency ("jitter") needs a second, *dynamical* degree of freedom per
  scale, which this class of models does not provide.

What the tree does contain is **verification, not new mathematics**: the model, its
thresholds, a machine-checked self-similar solution, and reproducible figures. The
resulting mathematical facts are essentially all already in the literature —
Cheskidov (TAMS 2008), Barbato–Morandin–Romito (Nonlinearity 2011), and the
Cheskidov–Dai–Friedlander survey (JMFM 2023) in particular. Nothing here settles
anything about the Navier–Stokes equations.

## Contents

| path | what |
|---|---|
| `Cascade.lean` | root, importing all 29 modules |
| `Cascade/*.lean` | the model, its estimates and its theorems |
| `Cascade/OUTCOME.md` | **the one-page verdict** — read this first |
| `Cascade/PROGRESS.md` | the full chronological record, including a `WITHDRAWN` block |
| `Cascade/VISION.md`, `Cascade/PLAN.md` | original intent and plan |
| `Cascade/plot_*.py` | figure generators (Python standard library only) |
| `Cascade/*.svg`, `Cascade/*.png` | the figures |

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain and mathlib are
pinned in `lean-toolchain` and `lakefile.toml`.

```
lake exe cache get     # fetch prebuilt mathlib
lake build
```

**One setup risk, stated plainly:** the pin is a *release candidate*,
`leanprover/lean4:v4.34.0-rc2`. Mathlib's prebuilt cache does not always cover
release candidates. If `lake exe cache get` cannot serve that revision, mathlib
must be built from source, which takes hours and several GB. That is the only
non-trivial part of a fresh clone.

## Provenance

Extracted from a larger Lean development, where this library lived alongside
`NavierStokes/`, `Euler/` and `Criticality/` libraries. Those are **not** included:
this directory is self-contained and imports nothing outside mathlib and its own
modules. The prior-art surveys referenced in `Cascade/PROGRESS.md`
(`../LEAN_PDE_PRIOR_ART.md` and `../research_lean4_pde_formalizations.md`) stayed
with the parent repository, as did `Criticality/BernsteinExport.lean`, which
re-exports part of this material under the `Criticality` namespace.

No license file is included; the Lean sources carry "Copyright: none. Public
domain." headers.
