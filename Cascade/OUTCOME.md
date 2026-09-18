# Outcome: how the dyadic-cascade exercise turned out

**One page. Read this before `PROGRESS.md`.**

The short version: **the exercise has a negative answer, and the negative is structural rather than
technical.** Tao's suggested dyadic caricature of the Alpöge–Buckmaster construction does not exist
for the model class this library builds; the reason is that scaling covariance pins the dissipation
degree into a range where the model is already provably regular, and the one escape route — putting
the spatial dimension in by hand — is closed because the constraint you would insert is implied by
the definitions. Along the way the exchange's loose end (Palasek's high-dimension caveat) turned out
to be a known criterion in different notation, and that is now machine-checked arithmetic. No new
mathematics was produced. The record is the deliverable, plus one small verification first.

---

## What was asked

On 2026-09-08 Alpöge and Buckmaster announced finite-time blowup **with a smooth force** for Euler and
Boussinesq. Palasek observed that without the force the cascade cannot sustain itself — the velocity
at frequency `N_k` grows at most like `N_k^{3/2}` while depletion acts at `N_k²` — adding "in high
dimension, though, there is no obstruction!". Tao replied suggesting an *illustrative exercise*:
locate a dyadic model with the same scaling features and see what the blowup analogue is there. The
full quotes are in `VISION.md`; the plan is `PLAN.md`.

## The answer, in three findings

**1. The caricature does not exist in this class — and the model is provably regular, not merely
unproven.** Fixing the model from its scaling and coupling alone (`VISION.md`'s fidelity rule 1),
scaling covariance together with the Boussinesq law **forces the dissipation degree** to `e = 2`, i.e.
Cheskidov's `α = 1`. That lies inside his globally regular range (`α ≥ 1/2`, and
Barbato–Morandin–Romito push it down to `α ≥ 2/5`). So Stage B's forced blowup is not "unproven
here" — it is impossible here. The truncated model, separately, is *trivially* regular (the transfer
cancels exactly and a finite range bounds every weighted norm by the energy).

**2. The one escape route is closed.** The model is dimension-blind: with one amplitude per octave the
Bernstein constraint `a_k² ≤ 2^{dk}u_k²` is *implied by the definitions* for every `d ≥ 2`, so it
constrains nothing, and at `d = 2` the model is exactly Bernstein-saturated. Inserting a Bernstein
factor therefore cannot make `d` intrinsic — it only replaces the model's sharper, dimension-free
bound by a weaker one, re-importing `d/2` by hand. Any dimensional crossover a "repaired" model
appears to show belongs to the insertion, not the dynamics. Both candidate insertions were analysed
and both are artifacts.

**3. Palasek's caveat is a known criterion.** The intermittency-dimension dyadic models put the
dimension in the *nonlinearity exponent*, `(2 + n − δ)/2`, against dissipation exponent `2`; the
critical case is therefore `δ = n − 2`. At the measured `δ ≈ 2.7` that gives dissipation winning
through dimension 4 and not from 5 — **Palasek's threshold** — and the arithmetic is machine-checked
in `Cascade/IntermittencyThreshold.lean` with the measured input `2 < δ ≤ 3` left as an explicit
hypothesis. The literature also already records the corresponding fidelity fact: the dyadic range
corresponding to 3D Navier–Stokes is globally regular, and the open gap is `α ∈ [1/3, 2/5)`.

## Verified here versus cited

| | status |
|---|---|
| Model definitions, scaling covariance, degree forcing (`DissipationDegree`) | **proved here** |
| Exact per-shell threshold `u_{j+1} > (ν/6)2^{(e−1)j}`; bar scale-invariant iff `e = 1`; no enstrophy-only criterion at `e = 1` (`PerShellThreshold`) | **proved here** |
| Truncated model trivially regular (`TruncatedRegularity`) | **proved here**, and flagged trivial |
| Dimension blindness (`DimensionBlind`) | **proved here** |
| Intermittency criterion; Palasek's 5 as conditional arithmetic (`IntermittencyThreshold`) | **proved here** |
| Flat self-similar solution of the inviscid untruncated system (`SelfSimilarSolution`) | **proved here** |
| Pillar A (concentration barrier, Bernstein chain, Heisenberg commutator form), dyadic partitions, scaling criticality, Euler product | **proved here** (`Criticality` library) |
| `α ≥ 1/2` regular, `α < 1/3` blowup, `α = 1/3` ↔ 4D | cited: Cheskidov, TAMS **360** (2008) |
| `α ∈ [2/5, 1/2)` smooth, and that range ↔ 3D NS | cited: Barbato–Morandin–Romito, Nonlinearity **24** (2011) |
| `δ ∈ [0,3]`, `δ = 3` Kolmogorov, measured `δ ≈ 2.7`, model eq. (3.7) | cited: Dai, arXiv:2006.15094 §2–§3.1 |
| The `n`-dimensional exponent, and the `θ = 1/γ`, `α = 1/θ` equivalences | **reported, not verified here** — see the Prior art section of `PROGRESS.md` |
| Palasek's remark and Tao's exercise (2026-09-08); Looi's rigorous obstruction | cited; the remark itself is unwritten, Looi is talks-only |

## Two corrections we made to our own record

* **The vacuous predicate episode.** The original truncated-solution predicates imposed the shell
  equation on all of `ℤ` *and* `u_N = 0`, which forces `u ≡ 0`; every no-blowup theorem resting on
  them was vacuous, and the claimed `e = 0` blowup was false on repair. The chain was deleted and is
  recorded in the **WITHDRAWN** block of `PROGRESS.md`.
* **The outdated gap.** Four places in the repo asserted the open Cheskidov gap was
  `α ∈ [1/3, 1/2)`. It is `[1/3, 2/5)`; the upper part was closed in 2011. Corrected, with the
  citation, in `PROGRESS.md` and `DissipationThreshold.lean`.

## What is genuinely new here, and it is narrow

* **A machine-checked dyadic blowup solution** (`SelfSimilarSolution.lean`): the inviscid untruncated
  system has the flat self-similar solution `u_k = (1/3)·2^{−k}·(T−t)^{−1}`, verified against the
  repo's own right-hand side. Its vorticity is independent of `k`, so the profile is flat and the
  local exponent is `0` everywhere — **zero jitter** — while the level is unbounded as `t → T⁻`. This
  is *verification of known mathematics*, not new mathematics, and its limits are on its face: it is
  the untruncated inviscid system, and the flat profile means the enstrophy diverges at every time,
  so it is not a blowup from finite-enstrophy data. As far as our own prior-art survey can tell, it is
  the first machine-checked dyadic blow-up.
* **The record itself**, including the honest negative.

## What is not here

* **No new mathematics.** Every mathematical statement is either elementary, or known, or both.
* **Nothing about the PDE.** This is a model throughout; it proves nothing about 3D Navier–Stokes
  regularity, and nothing here can win a Clay prize.
* **No jitter theorem, and there cannot be one in this class.** Jitter is a statistical property of a
  chaotic dynamical system; making it a theorem means proving an invariant-measure-and-scaling-exponent
  statement whose hard core — anomalous scaling — is open for *every* nonlinear shell model. A
  rigorous no-jitter statement for the one-mode class is available and small; a jitter theorem is not.
  (The figures that show jitter are labelled: the roughness is synthetic, since the real statistics
  are measured, not proved.)

## Where to read what

| file | what |
|---|---|
| `VISION.md` | the plan and the fidelity rules |
| `PROGRESS.md` | the full record; see the **WITHDRAWN** block and the **Prior art** section |
| `PerShellThreshold.lean`, `DissipationThreshold.lean` | the exact criticality of the model |
| `DimensionBlind.lean` | why the dimension cannot be inserted |
| `IntermittencyThreshold.lean` | Palasek's threshold as conditional arithmetic |
| `SelfSimilarSolution.lean` | the certified divergence, and what it is not |
| `plot_phase_diagram.py`, `plot_jitter_*.py`, `plot_explosion.py` | the figures, regenerable from source |

## Build

```sh
export ELAN_HOME="$PWD/.elan"; export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR="$PWD/.cache/mathlib"
lake build Cascade        # 3721 jobs, exit 0
lake build Criticality    # 3211 jobs, exit 0
```

No `sorry`, no `admit`, no `axiom` anywhere in either library. Every theorem added by this project
carries `#print axioms`, and each reports exactly `[propext, Classical.choice, Quot.sound]`.
