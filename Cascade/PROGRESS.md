# Progress: dyadic cascade models

Where we are now. The *target* is `PLAN.md`; the *why* is `VISION.md`.

> **Snapshot:** branch `dyadic-cascade`. **All planned stages are done: S, R, R′, A, G (phase),
> O, O′, and B.** Stage **B** (forced blowup) came out **negative** — the forced model does not
> blow up either, so the `B ∧ O` asymmetry does not materialise — which is itself the headline
> finding; see the Stage B section below. Stage **R** is `Cascade/Boussinesq.lean`
> (the frozen two-species dyadic Boussinesq model), plus `Cascade/BoussinesqScaling.lean`
> (scaling covariance) and `Cascade/BoussinesqEnergy.lean` (the two-species energy balance).
> Stage **R′** is `Cascade/DissipationDegree.lean`: the dissipation degree `d` is not a free
> parameter — Boussinesq covariance *forces* `d = 2`, which places the model in the provably
> regular regime. Stage **A** is `Cascade/Lacunary.lean` (the lacunary ansatz and the *exact*
> amplitude-ODE reduction) plus `Cascade/Amplitude.lean` (the Rayleigh–Taylor growth rate).
> Stage **G** is
> `Cascade/Phase.lean` (the wavevector phase, the steering lemma, and the steerable cosine
> coupling) plus `Cascade/PhaseGrowth.lean` (the consequence: the phase selects growth vs
> oscillation and the growth rate is fully controllable) and `Cascade/PhaseControl.lean` (steering
> *both* coefficients — the exact product formula, its range, and the stably stratified case where
> the phase buys nothing), plus `Cascade/Layers.lean` (stage G‴/H — the one-wavevector-per-octave
> realisation: AB eq. (3.3)'s accumulated background `G_{<q}`, `D_{<q}` and the *triangularity* of
> the layer model, i.e. no feedback from higher octaves). Stage **O** is
> `Cascade/Obstruction.lean` (the pointwise obstruction), `Cascade/Gronwall.lean` (the abstract
> Grönwall engine) and `Cascade/NoBlowup.lean` (capstone: no finite-time **energy** blowup).
> Stage **O′** is `Cascade/Enstrophy.lean` (the enstrophy budget), `Cascade/Riccati.lean` (the
> Bernoulli barrier engine), `Cascade/EnstrophyBound.lean` (capstone: no finite-time blowup in
> the **enstrophy/`H¹`** norm) and `Cascade/ScaleObstruction.lean` (the frequency-localized
> version, tied to Palasek's `N^{d/2}`-vs-`N²` comparison). Stage **B** is
> `Cascade/ForcedModel.lean` — the forced model frozen so `f ≡ 0` recovers the unforced one, with
> both forced negatives (no finite-time energy blowup, no finite-time enstrophy blowup), and
> Stage **B′** is `Cascade/BuoyancySign.lean` — `|κ|` replaces `κ`, dropping the `0 ≤ κ` hypothesis
> from eleven statements, so **no finite-time blowup for any sign of `κ`** either. The truncated
> Stage-R model is therefore *closed*: no blowup, any `κ`, forced or not.
> `Cascade/DissipationThreshold.lean` then locates **where the method dies**: generalising the
> dissipation to degree `e` (Cheskidov's `α = e/2`), the enstrophy barrier closes unconditionally
> for `e ≥ 2`, ties exactly at `e = 1` (which is Cheskidov's own regularity threshold `α = 1/2`),
> and the quadratic dissipation domination provably fails for every `e < 2`. The model's own
> `e = 2` is the **bottom** of the barrier's unconditional range.
> **A claimed positive half at `e = 0` has been withdrawn.** The former
> `Cascade/BlowupDegreeZero.lean` (with its auxiliaries `Cascade/BlowupRate.lean` and
> `Cascade/PositivityDegreeE.lean`) asserted **finite-time blowup at dissipation degree `e = 0`**
> — no globally-defined solution above the threshold `(2ν/c)²`, `c = 27√35/400`. That theorem is
> **false**. The truncated solution predicate on which every one of those files rested imposed the
> shell equation on *all* of `ℤ`, which is inconsistent with the Dirichlet value `u t N = 0`: the
> equation at `k = N` forces `u t (N-1) = 0` for all `t`, and the same step cascades downward, so
> the retained range vanishes identically and every theorem assuming the predicate was **vacuous**.
> With the repaired predicate (equations on `0 ≤ k < N` only) the truncated chain has **no**
> finite-time blowup, for any degree `e ≥ 0` and any `κ` — see
> `Cascade/TruncatedRegularity.lean` and the correctness episode below. The three files have been
> deleted; `Cascade/BlowupEngine.lean` is abstract, correct, and currently unused.
> Finally, `Cascade/LayerTrap.lean` closes the one-wavevector-per-octave (AB eq. (3.3)) direction
> with a **documented negative**: with the common rotation off and component `0` of the background
> and of every wavevector vanishing, all three layer right-hand sides vanish — a nontrivial,
> self-perpetuating equilibrium with no growth. So the layer model does not generically blow up, and
> what remains there is the construction of good data.
> `Cascade/PerShellThreshold.lean` then replaces the vague "the homogeneities tie at `e = 1`" with
> the **exact per-shell criterion** `u_{j+1} > (ν/6)·2^{(e−1)j}` for the **Katz–Pavlović** sector —
> scale-invariant exactly at
> `e = 1` — and proves that **no criterion reading the enstrophy alone can decide the sign of its
> rate at `e = 1`**, by exhibiting two nonnegative states with equal enstrophy and opposite rates.
> That is the honest sense in which this threshold is pinnable: the criterion is exact, and the
> impossibility of a single-number version at criticality is a theorem.
> `lake build Cascade` and
> `lake build Criticality` are both
> green; **every** new theorem's `#print axioms` is `[propext, Classical.choice, Quot.sound]`;
> no `sorry`.
>
> **Bernstein (Pillar A) has moved into this library.** `ConcentrationBarrier.lean`,
> `Bernstein.lean`, `BernsteinGrowth.lean` were relocated from `Criticality/` to `Cascade/`
> and renamed into the `Cascade` namespace. `Criticality/` now *depends on* `Cascade` and
> re-exports the declarations under the `Criticality` namespace via `Criticality/BernsteinExport.lean`
> (genuine `alias`es — same bodies, same axioms), so the documented `Criticality.bernstein*`
> API still resolves. `Cascade` is self-contained: it imports no `Criticality` module.

---

## Library layout

| File | Contents |
|---|---|
| `Cascade/ShellModel.lean` | stage S — one-species dyadic shell model |
| `Cascade/Boussinesq.lean` | stage R — frozen model + general version + pairing/flux lemmas |
| `Cascade/BoussinesqScaling.lean` | stage R — scaling covariance (general + frozen) |
| `Cascade/BoussinesqEnergy.lean` | stage R — two-species energy balance (general + frozen) |
| `Cascade/DissipationDegree.lean` | stage R′ — general dissipation degree `d`; Boussinesq covariance forces `d = 2` |
| `Cascade/Lacunary.lean` | stage A — lacunary ansatz + exact amplitude-ODE reduction |
| `Cascade/Amplitude.lean` | stage A — Rayleigh–Taylor growth of the amplitude system |
| `Cascade/Phase.lean` | stage G — wavevector phase, steering lemma, steerable cosine coupling |
| `Cascade/PhaseGrowth.lean` | stage G′ — the phase selects growth vs oscillation; the rate is fully controllable |
| `Cascade/PhaseControl.lean` | stage G″ — steering both coefficients: exact product formula, range, and the stable case |
| `Cascade/Layers.lean` | stage H — AB eq. (3.3): one wavevector per octave, accumulated `G_{<q}`/`D_{<q}`, triangularity |
| `Cascade/LayerTrap.lean` | a growth-free equilibrium of the layer model (`α' = 0`, component 0 vanishing) — closes the layer direction |
| `Cascade/Obstruction.lean` | stage O — pointwise obstruction inequalities |
| `Cascade/Gronwall.lean` | stage O — abstract Grönwall no-blowup engine |
| `Cascade/NoBlowup.lean` | stage O — capstone: no finite-time energy blowup |
| `Cascade/Enstrophy.lean` | stage O′ — enstrophy pairing identity + budget |
| `Cascade/Riccati.lean` | stage O′ — Bernoulli/Riccati barrier engine |
| `Cascade/EnstrophyBound.lean` | stage O′ — capstone: no finite-time `H¹` blowup |
| `Cascade/ScaleObstruction.lean` | stage O′ — frequency-localized dissipation dominance (Palasek, shell form) |
| `Cascade/ForcedModel.lean` | stage B — the forced model; forced energy and enstrophy bounds (both negative) |
| `Cascade/BuoyancySign.lean` | stage B′ — `\|κ\|` replaces `κ`: no-blowup for **every** sign of `κ` (11 statements re-proved) |
| `Cascade/DissipationThreshold.lean` | the dissipation threshold: no blowup for degree `e ≥ 2`; the barrier ties at `e = 1`; quadratic domination provably fails below `e = 2` |
| `Cascade/PerShellThreshold.lean` | the **exact per-shell criterion** `u_{j+1} > (ν/6)·2^{(e−1)j}` *in the Katz–Pavlović sector*, and the theorem that no enstrophy-only criterion decides at `e = 1` |
| `Cascade/PerShellSectorObukhov.lean` | the Obukhov sector: the pairing identity there, and **`no_obukhov_perShellBar` — no `(ν,e,j)`-only per-shell bar; what it has instead is a state-dependent threshold** |
| `Cascade/TruncatedRegularity.lean` | **the truncated model is trivially globally regular** — the honest statement after the predicate repair |
| `Cascade/TruncatedRegularity.lean` | **honest replacement**: the truncated model is trivially globally regular (transfer cancellation, exact energy identity, finite-range norm domination by the energy) |
| `Cascade/BlowupEngine.lean` | the reversed-Bernoulli engine + the inverted Hölder lemma (abstract, correct, **currently unused**) |
| `Cascade/PositivityDegreeE.lean` | **deleted** — fed the withdrawn `e = 0` blowup capstone |
| `Cascade/BlowupRate.lean` | **deleted** — fed the withdrawn `e = 0` blowup capstone |
| `Cascade/BlowupDegreeZero.lean` | **deleted** — false on the repaired predicate |
| `Cascade/BernsteinTransfer.lean` | the Bernstein `N^{d/2}` exponent is dominated by dissipation |
| `Cascade/ConcentrationBarrier.lean` | Bernstein chain, part 1 (pointwise `≤ ‖𝓕 f‖₁`) |
| `Cascade/Bernstein.lean` | Bernstein chain, part 2 (`‖f‖∞ ≤ √(vol ball) ‖f‖₂`) |
| `Cascade/BernsteinGrowth.lean` | Bernstein chain, part 3 (`L² → L∞` with the `N^{d/2}` exponent; gradient form) |
| `Criticality/BernsteinExport.lean` | re-exports the moved Pillar A under `Criticality.*` |
| `Cascade/DimensionBlind.lean` | the one-mode model is dimension-blind: the Bernstein constraint is implied by the definitions for every `d ≥ 2`, so it cannot make `d` intrinsic |
| `Cascade/IntermittencyThreshold.lean` | the intermittency criterion over real `n`: critical at `δ = n − 2`, and Palasek's crossover at 5 as a theorem conditional on the measured `2 < δ ≤ 3` |
| `Cascade/SelfSimilarSolution.lean` | the flat self-similar solution `u_k = (1/3)·2^{−k}·(T−t)^{−1}` of the inviscid untruncated system — zero jitter, level unbounded (see the section below) |

`Cascade.lean` imports `ShellModel`, `Boussinesq`, `BoussinesqScaling`, `BoussinesqEnergy`,
`DissipationDegree`, `Lacunary`, `Amplitude`, `Phase`, `PhaseGrowth`, `PhaseControl`, `Layers`,
`Obstruction`, `Gronwall`, `NoBlowup`, `ForcedModel`, `Enstrophy`, `Riccati`, `EnstrophyBound`,
`BuoyancySign`, `DissipationThreshold`, `PerShellThreshold`, `BlowupEngine`, `TruncatedRegularity`,
`LayerTrap`, `ScaleObstruction`, `BernsteinTransfer` (and hence the Bernstein chain), and — more
recently — `DimensionBlind`, `IntermittencyThreshold`, `SelfSimilarSolution`.
(`PositivityDegreeE`, `BlowupRate` and `BlowupDegreeZero` have been deleted — see the correctness
episode below.)

---

## Correctness episode — the vacuous truncated predicate, and the honest replacement

**The bug.** The truncated dyadic solution predicates — `IsUnforcedTruncatedSolution`,
`IsForcedTruncatedSolution`, `IsUnforcedTruncatedSolutionE`, `IsForcedTruncatedSolutionE` — imposed
the shell equation for **every** `k : ℤ` *and* imposed `u t N = 0` for every `t`. Those two are
inconsistent: `u · N` is the zero function, so its derivative is `0`, so the equation at `k = N`
forces `velocityRHS … N = 2^N (u t (N-1))² = 0`, hence `u t (N-1) = 0` for all `t`; the same step
cascades downward and the retained range vanishes identically. Machine-checked: for `κ = 0`,
`IsUnforcedTruncatedSolutionE ν μ 0 e N u θ` implies `∀ j ≤ N, ∀ t, u t ((N:ℤ) - j) = 0`.
Consequently **every theorem assuming one of those predicates was vacuous** — including the whole
no-blowup chain and, fatally, the `e = 0` blowup capstone.

**The fix.** The equations are now restricted to the retained shells `0 ≤ k < N`. The predicates are
consistent (inhabited by the zero equilibrium, and by genuinely nonzero local data), and the
boundary conditions still close the truncation.

**The honest consequence.** With the repaired predicate the truncated model is **trivially globally
regular**, and there is no blowup theorem to be had:

* The transfer pairing cancels exactly on the retained range (the Dirichlet ends make the
  telescoping boundary terms vanish), so
  `E' = 2κ ∑_{k<N} u_k θ_k − 2ν ∑_{k<N} 2^{ek} u_k²`, `E = ∑_{k<N} u_k²`. For `κ = 0`, `e = 0`
  this is `E' = −2νE`, i.e. exponential decay.
* On a **finite** range every weighted norm is dominated by the energy:
  `∑_{k<N} 2^{sk} u_k² ≤ 2^{s(N-1)} · E` for `s ≥ 0`.
* So nothing can blow up: no weighted norm can grow faster than `E`, which is non-increasing
  (`κ = 0`) or Grönwall-bounded (general `κ`).

This is stated and proved in `Cascade/TruncatedRegularity.lean`
(`transfer_pairing_eq_zero`, `weighted_sq_le_energy`, `truncated_energy_hasDerivAt`,
`truncated_globally_regular`).

**The deletions.** `Cascade/BlowupDegreeZero.lean` (the blowup capstone; **false** on repair),
`Cascade/BlowupRate.lean` and `Cascade/PositivityDegreeE.lean` (built solely to feed it) have been
`git rm`-ed and their imports removed from `Cascade.lean`. `Cascade/BlowupEngine.lean` (the
reversed-Bernoulli engine, the inverted Hölder lemma and some elementary inequalities) is abstract,
correct and independent of any solution predicate; it is retained but **currently unused**, and its
docstring now says so.

**Where blowup actually lives.** Blowup in these models needs the **untruncated** lattice: there
the weights `4^k` are unbounded, so the energy can decay while the enstrophy diverges, and the
nonlinear transfer is no longer a finite sum with vanishing boundary terms. "Truncation is the
dangerous direction" was exactly backwards — truncation **caps** the weights and is the safe
direction.

**Doc corrections.** The line in the "Open" section below that called truncation "the *dangerous*
direction (it removes the enstrophy sink, which is why the Stage-O′ bound is only linear in `T`)"
has been corrected: truncation is safe, and the linear-in-`T` form is an artifact of a Grönwall
route that never used the finite-range norm cap. `Cascade/NoBlowup.lean`'s scope paragraph had
claimed a Stage-B finite-time blowup for the forced model; that claim is withdrawn.
`Cascade/EnstrophyBound.lean`'s module docstring now records the artifact explicitly.

---

## Done — Stage S (`Cascade/ShellModel.lean`)

```lean
def shellRHS (ν : ℝ) (C : ℕ → ℝ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  C k - ν * (2 : ℝ) ^ (2 * k) * u k

theorem shell_energy_identity (ν : ℝ) (C : ℕ → ℝ) (u : ℕ → ℝ) (n : ℕ)
    (hC : (Finset.sum (Finset.range n) (fun k => u k * C k)) = 0) :
    (Finset.sum (Finset.range n) (fun k => u k * shellRHS ν C u k))
      = -ν * (Finset.sum (Finset.range n) (fun k => (2 : ℝ) ^ (2 * k) * (u k) ^ 2))

theorem transfer_le_dissipation (N : ℝ) (hN : 1 ≤ N) :
    N ^ ((3 : ℝ) / 2) ≤ N ^ (2 : ℝ)
```

---

## Done — Stage R (`Cascade/Boussinesq.lean` + scaling + energy)

Two ladders `u θ : ℤ → ℝ`; shell `k` carries wavenumber `2^k`. The **named / frozen** model
is `dyadicBoussinesqRHS (ν μ κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ × ℝ`, the coupling choice
`A = 1, B = 0, Ã = 1, B̃ = 1` of the general model below:

```
du_k/dt = 2^k (u_{k-1}² − 2 u_k u_{k+1}) + κ θ_k − ν 2^{2k} u_k
dθ_k/dt = 2^k (u_{k-1}θ_{k-1} − 2 u_k θ_{k+1} + u_k θ_{k-1} − 2 u_{k+1}θ_{k+1}) − μ 2^{2k} θ_k
```

Nearest-octave; buoyancy `κ θ_k`; viscosity `ν 2^{2k}` and thermal diffusivity `μ 2^{2k}`.
Origin: the standard dyadic (shell) model of natural convection — Mailybaev,
[arXiv:1210.2494](https://ar5iv.labs.arxiv.org/html/1210.2494), eqs (3)–(4) at `h = 2`, `k_n = 2^n`.

### The frozen model API

```lean
def dyadicWeight (k : ℤ) : ℝ := (2 : ℝ) ^ k

def dyadicVelocityRHS (ν κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ
def dyadicTemperatureRHS (μ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ
def dyadicBoussinesqRHS (ν μ κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ × ℝ
def dyadicVelocityFlux (u : ℤ → ℝ) (k : ℤ) : ℝ
def dyadicTemperatureFlux (u θ : ℤ → ℝ) (k : ℤ) : ℝ
```

The four-parameter general model is kept as the structural result:

```lean
def boussinesqTransferU (A B : ℝ) (u : ℤ → ℝ) (k : ℤ) : ℝ
def boussinesqTransferTheta (At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ
def generalVelocityRHS (ν κ A B : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ
def generalTemperatureRHS (μ At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ
def generalBoussinesqRHS (ν μ κ A B At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ × ℝ
def velocityFlux (A B : ℝ) (u : ℤ → ℝ) (k : ℤ) : ℝ
def temperatureFlux (At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ
```

### Why this coupling

From the thread that motivated the library, Tao points at the **exact affine wave ODE**,
eq. (3.2) of Alpöge–Buckmaster's `boussinesq.pdf` (Lemma 3.1):

```
ζ̇ = −Dᵀζ,   Θ̇ = −(Jζ·G)/(λ|ζ|²)·Ω,   Ω̇ = λζ₁Θ,
```

a *linear* system whose coefficients `D_{<q}`, `G_{<q}` are frozen from the lower layers. The
coupling choice is fixed by matching the frozen-background linearisation of the frozen model
to (3.2). This matching is **heuristic motivation, not a Lean theorem** (nothing below is
formalized), so the derivation is spelled out so it can be checked by hand:

* Write the temperature perturbation `φ_k` and the vorticity perturbation `Ω_k := 2^k v_k`
  (`v_k` = velocity perturbation). Perturb only octave `k` and freeze every other octave.
  In the temperature equation the *only* surviving linear terms are the two carrying `u_k`
  at fixed `k`: `−2Ã·2^k u_k θ_{k+1}` contributes `−2Ã θ̄_{k+1} Ω_k`, and
  `+B̃·2^k u_k θ_{k−1}` contributes `+B̃ θ̄_{k−1} Ω_k`. Hence
  `φ̇_k = a_k Ω_k − μ4^k φ_k + (background)`, `a_k = B̃ θ̄_{k−1} − 2Ã θ̄_{k+1}`.
  In the velocity equation the surviving linear terms give
  `v̇_k = [2^k(B ū_{k−1} − 2A ū_{k+1}) − ν4^k] v_k + κ φ_k`, i.e., multiplying by `2^k`,
  `Ω̇_k = c_k Ω_k + b_k φ_k + (background)`, `b_k = 2^k κ`,
  `c_k = 2^k(B ū_{k−1} − 2A ū_{k+1}) − ν4^k`.
  Equivalently `a_k = ∂φ̇_k/∂Ω_k`, `b_k = ∂Ω̇_k/∂φ_k`, `c_k = ∂Ω̇_k/∂Ω_k`.
* With `B̃ = 0` and the wave at the newest (highest) octave — so `θ̄_{k+1} = ū_{k+1} = 0`, and
  `Ã`'s contribution vanishes — `a_k = 0`: the temperature equation is triangular and there
  is **no `Θ̇ ∝ Ω` term** — (3.2) cannot be reached. So **`B̃ = 1` is load-bearing**: it is
  the lower-octave temperature-gradient coupling.
* `B` only adds an extra inviscid diagonal `2^k ū_{k−1}` which (3.2) does not have (in the
  PDE it vanishes because the background vorticity is spatially constant). So `B = 0`.
* `A = Ã = 1` is the default; `Ã` does not contribute at the highest octave.

The transfers are individually conservative for **all** `A, B, Ã, B̃`; the choice above is
about fidelity to (3.2), not about conservation. **Caveats recorded for later stages:**
(i) Mailybaev's own "traditional" choice is `A = ε ≈ 0.01`, `B = Ã = B̃ = 1`, so the frozen
choice is not the model he studies nor a small perturbation of it; (ii) a *scalar* shell
model has no `ζ₁` phase direction, so it cannot reproduce the AB **phase-steering control** —
any dyadic blowup will be uncontrolled, not the controlled AB one.

### Scaling covariance (Stage R deliverable)

Theorem `scaling_covariant` (and its components). With `λ = 2^s`, the scaling acts by the
shell shift `k ↦ k − s` and the amplitude factors of the Boussinesq symmetry

```
u_λ = λ^b u(λx, λ^{b+1}t),   θ_λ = λ^{2b+1} θ(λx, λ^{b+1}t),   p_λ = λ^{2b} p,
```

i.e. `scaleVelocity s b u k = dyadicWeight (s*b) * u (k-s)` and
`scaleTemperature s b θ k = dyadicWeight (s*(2*b+1)) * θ (k-s)`:

```lean
theorem scaling_covariant_velocity (s b : ℤ) (ν κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    dyadicVelocityRHS (ν * dyadicWeight (s * (b - 1))) κ
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight (s * (2 * b + 1)) * dyadicVelocityRHS ν κ u θ (k - s)

theorem scaling_covariant_temperature (s b : ℤ) (μ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    dyadicTemperatureRHS (μ * dyadicWeight (s * (b - 1)))
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight (s * (3 * b + 2)) * dyadicTemperatureRHS μ u θ (k - s)

theorem scaling_covariant (s b : ℤ) (ν μ κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    dyadicBoussinesqRHS (ν * dyadicWeight (s * (b - 1))) (μ * dyadicWeight (s * (b - 1))) κ
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = (dyadicWeight (s * (2 * b + 1)) * (dyadicBoussinesqRHS ν μ κ u θ (k - s)).1,
         dyadicWeight (s * (3 * b + 2)) * (dyadicBoussinesqRHS ν μ κ u θ (k - s)).2)
```

The momentum equation is homogeneous of degree `2b+1`, the temperature equation of degree
`3b+2`, and the viscosity/diffusivity rescale by `λ^{b−1}`. At `b = 1` (the fixed standard
2D choice, `boussinesqB`) the parameters are **unchanged** (`λ^0 = 1`) and the degrees are
`3` and `5`:

```lean
theorem scaling_covariant_b_one_velocity (s : ℤ) (ν κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    dyadicVelocityRHS ν κ (scaleVelocity s boussinesqB u) (scaleTemperature s boussinesqB θ) k
      = dyadicWeight (3 * s) * dyadicVelocityRHS ν κ u θ (k - s)

theorem scaling_covariant_b_one_temperature (s : ℤ) (μ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    dyadicTemperatureRHS μ (scaleVelocity s boussinesqB u) (scaleTemperature s boussinesqB θ) k
      = dyadicWeight (5 * s) * dyadicTemperatureRHS μ u θ (k - s)

theorem scaling_pressure_gradient_degree (s b : ℤ) :
    dyadicWeight (s * (2 * b)) * dyadicWeight s = dyadicWeight (s * (2 * b + 1))
```

`b = 1` is the *unique* exponent at which `λ^{b−1} = 1` for a nontrivial scaling
(`λ ≠ 1`, i.e. `s ≠ 0`), hence the one that fixes `ν` and `μ`.
For the inviscid model (`ν = μ = 0`) the family is covariant for every `b`; viscosity breaks
it except at `b = 1`. **`b = 1` is fixed here, before any statement about solutions**
(fidelity rule 1). The `general_*` versions of all of the above hold for the four-parameter
model.

### Stage R′ — the dissipation degree is forced (`Cascade/DissipationDegree.lean`)

The covariance above is not merely a *sufficient* condition on the viscosity term — it is
*necessary*, and that is what pins the dissipation degree. Generalise the viscosity to
`ν · 2^{d k} · u_k` for an arbitrary **degree** `d : ℤ` (so `d = 2` is the library's Laplacian
`−Δ`, and Cheskidov's `α` is `d/2`):

```lean
def velocityRHSDegree (ν κ A B : ℝ) (d : ℤ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ :=
  boussinesqTransferU A B u k + κ * θ k - ν * dyadicWeight (d * k) * u k

theorem velocityRHSDegree_two … :
    velocityRHSDegree ν κ A B 2 u θ k = generalVelocityRHS ν κ A B u θ k   -- rfl

theorem velocityRHSDegree_scaling_covariant (s b : ℤ) (ν κ A B : ℝ) (d : ℤ) … :
    velocityRHSDegree (ν * dyadicWeight (s * (b + 1 - d))) κ A B d
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight (s * (2 * b + 1)) * velocityRHSDegree ν κ A B d u θ (k - s)

theorem velocityRHSDegree_scaling_covariant_two (s b : ℤ) … :   -- the law ν ↦ ν λ^{b-1}
    velocityRHSDegree (ν * dyadicWeight (s * (b - 1))) κ A B 2
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight (s * (2 * b + 1)) * velocityRHSDegree ν κ A B 2 u θ (k - s)

theorem boussinesq_law_forces_degree_two (s b d : ℤ) (hs : s ≠ 0) (ν κ : ℝ) (hν : ν ≠ 0)
    (h : ∀ (u θ : ℤ → ℝ) (k : ℤ),
      velocityRHSDegree (ν * dyadicWeight (s * (b - 1))) κ 1 0 d
          (scaleVelocity s b u) (scaleTemperature s b θ) k
        = dyadicWeight (s * (2 * b + 1)) * velocityRHSDegree ν κ 1 0 d u θ (k - s)) :
    d = 2

theorem boussinesqB_forces_degree_two … : d = 2      -- the same at boussinesqB = 1
```

**What this says.** For general `d`, covariance with the viscosity law `ν ↦ ν λ^{b+1−d}` holds.
The **Boussinesq** law is `ν ↦ ν λ^{b−1}` (that is the law the Laplacian gives: `∂_t` scales as
`λ^{b+1}`, `Δ` as `λ^{b+2}`), and requiring covariance under *that* law forces `d = 2` — for
**every** `b`, not just `b = 1`. Equivalently, at `b = 1` the equation is covariant with `ν`
**unchanged** only at degree `2`. So the exponent is not a modelling free parameter: the symmetry
that makes the model a faithful Boussinesq analogue is exactly what determines it.

**The proof is a one-shell test.** Take the ladder supported only at shell `0`, zero temperature,
and read the covariance identity at shell `k = s` (the image of shell `0` under the scaling). Every
transfer term dies — the scaled ladder is supported at `s` and both neighbours vanish, and at shell
`0` the unscaled ladder has vanishing neighbours — and both buoyancy terms are zero. The identity
collapses to `2^{s(b−1)} · 2^{ds} · 2^{sb} = 2^{s(2b+1)}`, i.e. `s(d−2) = 0`, so `d = 2` whenever
`s ≠ 0`. The only ingredient beyond arithmetic is injectivity of `k ↦ 2^k`
(`dyadicWeight_injective`, from `zpow_right_injective₀`). A non-vacuity `example` records that the
hypothesis *is* satisfied at `d = 2`, so "the law holds nowhere else" is not an empty statement.

**Why it matters for the project.** Write `α = d/2` (Cheskidov's dissipation degree). Then
`d = 2` is `α = 1`. Cheskidov's dyadic model is regular for `α ≥ 1/2` and blows up in finite time
for `α < 1/3`; his model *includes* the force. So the model this
library froze at Stage R is in the **provably regular** regime, and Stage B's forced blowup is not
merely unproven there — it is impossible.

**CORRECTION — the gap is narrower than this file used to say.** The open gap is
`α ∈ [1/3, 2/5)`, *not* `[1/3, 1/2)`. Barbato–Morandin–Romito, *Smooth solutions for the dyadic
model*, Nonlinearity **24** (2011) 3083–3097 (arXiv:1007.3401), Theorem A, prove existence,
uniqueness and smoothness for `β ∈ (2, 5/2]` in their normalisation; that parameter is `α = 1/β`
here, so they give `α ∈ [2/5, 1/2)`. Together with Cheskidov's `α ≥ 1/2` this is global regularity
for **all `α ≥ 2/5`**. The same paper states explicitly that `β ∈ (2, 5/2]` "is essentially the one
corresponding, within the simplification of the model, to the three dimensional Navier–Stokes
equations". So the dyadic range corresponding to 3D Navier–Stokes is *provably globally regular*,
and the only undecided range is `α ∈ [1/3, 2/5)`.

**The calibration, and what it does to the fidelity story.** Matching the model's sharp dyadic
estimate against the `d`-dimensional sharp `H¹` estimate gives `α(d) = 2/(d+2)`, equivalently
`d = 2/α − 2`. (This matching is our own computation, not a theorem; what follows is why it is
credible.) What this is *not*, and must be said plainly: the values `2/5` at `d = 3` and `1/3` at
`d = 4` were already in this project's notes as "Cheskidov's quoted values" *before* the matching was
carried out. So the matching reproducing them is a consistency check, not independent confirmation,
and it must not be recorded as a discovery. The literature statements themselves are Cheskidov's
abstract — the model with `α = 1/3` "enjoys the same estimates on the nonlinear term as the 4D
Navier–Stokes equations", and `α(4) = 2/6 = 1/3` — and BMR's identification above, 3D at
`α ∈ [2/5, 1/2)` with `α(3) = 2/5`. Under that map the open dyadic gap `α ∈ [1/3, 2/5)`
corresponds to `d ∈ (3, 4]` — dimensions *above* the physical one. At the physical `d = 3` the
calibrated model lands exactly on BMR's regularity endpoint. The caricature is therefore decided —
in the **regular** direction — at the dimension whose PDE is open, and undecided only for
non-physical `d ∈ (3, 4)`. That, not the exponent arithmetic, is the honest end of this line; see
the Stage B discussion below and `Cascade/DimensionBlind.lean`.

### Two-species energy balance (Stage R deliverable)

The pairing lemmas say the nonlinear transfer contributes only a boundary flux:

```lean
theorem dyadic_velocity_pairing_eq_flux (u : ℤ → ℝ) (k : ℤ) :
    u k * boussinesqTransferU 1 0 u k = dyadicVelocityFlux u k - dyadicVelocityFlux u (k + 1)

theorem dyadic_temperature_pairing_eq_flux (u θ : ℤ → ℝ) (k : ℤ) :
    θ k * boussinesqTransferTheta 1 1 u θ k
      = dyadicTemperatureFlux u θ k - dyadicTemperatureFlux u θ (k + 1)
```

Summing over the truncated range `k = 0, …, n−1`:

```lean
theorem dyadic_velocity_energy_identity (ν κ : ℝ) (u θ : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, u (k : ℤ) * dyadicVelocityRHS ν κ u θ (k : ℤ))
      = dyadicVelocityFlux u 0 - dyadicVelocityFlux u (n : ℤ)
        + κ * (∑ k ∈ Finset.range n, u (k : ℤ) * θ (k : ℤ))
        - ν * (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2)

theorem dyadic_temperature_energy_identity (μ : ℝ) (u θ : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, θ (k : ℤ) * dyadicTemperatureRHS μ u θ (k : ℤ))
      = dyadicTemperatureFlux u θ 0 - dyadicTemperatureFlux u θ (n : ℤ)
        - μ * (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (θ (k : ℤ)) ^ 2)

theorem dyadic_energy_identity (ν μ κ : ℝ) (u θ : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n,
        (u (k : ℤ) * (dyadicBoussinesqRHS ν μ κ u θ (k : ℤ)).1
          + θ (k : ℤ) * (dyadicBoussinesqRHS ν μ κ u θ (k : ℤ)).2))
      = (dyadicVelocityFlux u 0 - dyadicVelocityFlux u (n : ℤ))
        + (dyadicTemperatureFlux u θ 0 - dyadicTemperatureFlux u θ (n : ℤ))
        + κ * (∑ k ∈ Finset.range n, u (k : ℤ) * θ (k : ℤ))
        - ν * (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2)
        - μ * (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (θ (k : ℤ)) ^ 2)
```

Reading: velocity energy grows at the buoyancy rate `κ Σ u_k θ_k` and decays at the viscous
rate `ν Σ 2^{2k} u_k²`; entropy decays only at `μ Σ 2^{2k} θ_k²`. The nonlinear transfers
survive only as the boundary fluxes at shells `0` and `n`. **`Σ½(u_k² + θ_k²)` is not
conserved** — the missing invariant is the potential term (`∫αgzθ` in the PDE, and `z` is
not a shell variable); cf. the paragraph following Mailybaev eqs (5)–(6). The `general_*`
versions hold for the
four-parameter model.

**Consequence for Stage O (recorded now, from the audit).** Since entropy is non-increasing,
`|κ Σ u_k θ_k| ≤ |κ| √(2E_u) √(2S(0))`, so buoyancy alone cannot produce finite-time blowup
(uniform bound for `ν > 0`, at most linear growth for `ν = 0`). The quantity that can grow is
the **enstrophy `Σ 4^k u_k² = Σ Ω_k²`**, not the transfer-conserved `Σ u_k²`. A Stage O
"dissipation beats transfer" theorem must bound the buoyancy term separately (or state the
entropy hypothesis) rather than assume a conservation law the model lacks.

### Bonus — the Bernstein arrow (`Cascade/BernsteinTransfer.lean`)

`Cascade/ShellModel.lean`'s `transfer_le_dissipation` states the scalar `N^{3/2} ≤ N²` with
the `3/2` hard-coded. This file derives it from the actual Bernstein exponent:

```lean
theorem bernstein_exponent_le_dissipation {d : ℕ} (hd : d ≤ 4) (N : ℝ) (hN : 1 ≤ N) :
    N ^ ((d : ℝ) / 2) ≤ N ^ (2 : ℝ)

theorem finrank_euclideanSpace_fin_three :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3

theorem transfer_le_dissipation_bernstein (N : ℝ) (hN : 1 ≤ N) :
    N ^ ((Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) / 2) ≤ N ^ (2 : ℝ)

theorem bernstein_L2_to_Linf_dissipation (hf : (Module.finrank ℝ V : ℝ) / 2 ≤ 2)
    [CompleteSpace F] (f : 𝓢(V, F)) (N : ℝ) (hN : 1 ≤ N)
    (hband : ∀ x, 𝓕 f x ≠ 0 → ‖x‖ < N) :
    ‖f.toBoundedContinuousFunction‖ ≤
      Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal * N ^ (2 : ℝ) * ‖f.toLp 2 volume‖
```

The `3/2` is no longer a literal: it is `(Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))/2`,
the exact exponent of `Cascade.bernstein_L2_to_Linf`, and the last theorem composes Bernstein
with the exponent comparison in every dimension `d ≤ 4`.

---

## Done — Stage A (`Cascade/Lacunary.lean` + `Cascade/Amplitude.lean`)

### The lacunary ansatz and the exact reduction

At generation `n : ℤ` the active octave is `N_n = 2^n`; the background `(u₋, θ₋)` lives
strictly below `n` and the wave amplitudes `(a, b)` sit at octave `n`
(`u = Function.update u₋ n a`, `θ = Function.update θ₋ n b`, with `u₋ (n+1) = θ₋ (n+1) = 0`).

The reduction is **exact, not a linearisation error**: the shell-`n` RHS is affine in `(a, b)`
because no `u_n²`, `θ_n²` or `u_nθ_n` term exists, and the only discarded couplings are the
`n+1` ones, killed by the support hypotheses.

```lean
def lacunaryVelocity (n : ℤ) (u_minus : ℤ → ℝ) (a : ℝ) : ℤ → ℝ
def lacunaryTemperature (n : ℤ) (θ_minus : ℤ → ℝ) (b : ℝ) : ℤ → ℝ
def lacunaryFrequency (n : ℤ) : ℝ := dyadicWeight n
def lacunaryVorticity (n : ℤ) (a : ℝ) : ℝ := dyadicWeight n * a

def lacunaryVelocityRHS (ν κ A B : ℝ) (n : ℤ) (u_minus : ℤ → ℝ) (a b : ℝ) : ℝ
def lacunaryTemperatureRHS (μ At Bt : ℝ) (n : ℤ) (u_minus θ_minus : ℤ → ℝ) (a b : ℝ) : ℝ
def dyadicLacunaryVelocityRHS (ν κ : ℝ) (n : ℤ) (u_minus : ℤ → ℝ) (a b : ℝ) : ℝ
def dyadicLacunaryTemperatureRHS (μ : ℝ) (n : ℤ) (u_minus θ_minus : ℤ → ℝ) (a b : ℝ) : ℝ

theorem lacunary_reduction_velocity (ν μ κ A B At Bt : ℝ) (n : ℤ) … (hu : u_minus (n+1) = 0) :
    (generalBoussinesqRHS ν μ κ A B At Bt (lacunaryVelocity n u_minus a)
        (lacunaryTemperature n θ_minus b) n).1 = lacunaryVelocityRHS ν κ A B n u_minus a b
theorem lacunary_reduction_temperature …
theorem lacunary_reduction_dyadic_velocity / lacunary_reduction_dyadic_temperature
```

Writing `Ω_n = 2^n a` (vorticity amplitude) and `Θ_n = b` (temperature amplitude), the part
linear in `(Ω, Θ)` is exactly Tao's page-4 ODE (Alpöge–Buckmaster eq. (3.2)):

```
Θ̇ = θ̄_{n−1} Ω − μ 4^n Θ,      θ̄_{n−1} := B̃ θ₋_{n−1},
Ω̇ = 2^n κ Θ − ν 4^n Ω,
```

with off-diagonal couplings `a_n = θ̄_{n−1}` (lower-octave temperature gradient) and
`b_n = 2^n κ` (one-derivative buoyancy `N_n κ`). This **supersedes the previously unformalized
prose** in `Cascade/Boussinesq.lean`; the reduction is a machine-checked theorem, not a sketch.

### The amplitude growth (`Cascade/Amplitude.lean`)

Standalone (Mathlib only). For the inviscid amplitude matrix `M = !![0, b; a, 0]`:

* `rayleighTaylorMatrix_mulVec : M *ᵥ ![Θ, Ω] = ![b*Ω, a*Θ]`;
* `rayleighTaylor_charpoly : charpoly M = X^2 - C (a*b)`, with eigenvectors `![b, ±√(ab)]`
  when `a*b ≥ 0` (`rayleighTaylor_eigenvector_pos/_neg`);
* `rayleighTaylorSolution` — the explicit `cosh`/`sinh` solution of `Θ̇ = bΩ`, `Ω̇ = aΘ` —
  with `rayleighTaylorSolution_hasDerivAt` and `rayleighTaylorSolution_unbounded`
  (`Tendsto … atTop atTop` for `a*b > 0`, `Θ₀ > 0`, plus the documented sign hypothesis
  `0 ≤ b·Ω₀`);
* the stably stratified counterpart `rayleighTaylorOscillation` / `_hasDerivAt` / `_bounded`
  (`cos`/`sin` at the Brunt–Väisälä frequency `√(−ab)` when `a*b < 0`);
* `rayleighTaylor_growthRate_dichotomy`: the growth rate `√(ab)` is positive exactly when
  `a*b > 0`.

Reading: with the frozen `B̃ = 1` we get `a_n = θ₋_{n−1}`, so an unstably stratified background
(`2^n κ θ₋_{n−1} > 0`) grows the wave exponentially at rate `√(N_n κ θ₋_{n−1})` — the
Rayleigh–Taylor instability that Stage B must turn into a finite-time blowup.

---

## Done — Stage O (`Obstruction.lean` + `Gronwall.lean` + `NoBlowup.lean`)

**The obstruction.** The interior nonlinear transfer is exactly energy-conserving: by the Stage-R
pairing/flux lemmas, `Σ_k u_k T^u_k` is a *difference of boundary fluxes*, and the truncation /
Dirichlet conditions `u(−1) = u(N) = θ(−1) = θ(N) = 0` kill both. So there is no interior energy
source; the only bulk source is buoyancy, bounded by the entropy, and viscosity dominates. Hence
the unforced truncated model has **no finite-time energy blowup** — Palasek's obstruction,
formalized.

### Model-side inequalities (`Cascade/Obstruction.lean`)

```lean
theorem sum_mul_le_sqrt_mul_sqrt (s : Finset ℤ) (u θ : ℤ → ℝ) :
    (∑ k ∈ s, u k * θ k) ≤ Real.sqrt (∑ k ∈ s, (u k)^2) * Real.sqrt (∑ k ∈ s, (θ k)^2)

theorem velocity_energy_rate_le (ν κ : ℝ) (hκ : 0 ≤ κ) (hν : 0 ≤ ν) (u θ : ℤ → ℝ) (n : ℕ)
    (hbot : u (-1) = 0) (htop : u (n : ℤ) = 0) :
    (∑ k ∈ Finset.range n, u (k : ℤ) * dyadicVelocityRHS ν κ u θ (k : ℤ))
      ≤ κ * (Real.sqrt (∑u²) * Real.sqrt (∑θ²)) - ν * (∑u²)

theorem temperature_energy_rate_nonpos (μ : ℝ) (hμ : 0 ≤ μ) (u θ : ℤ → ℝ) (n : ℕ)
    (hbot : θ (-1) = 0) (htop : θ (n : ℤ) = 0) :
    (∑ k ∈ Finset.range n, θ (k : ℤ) * dyadicTemperatureRHS μ u θ (k : ℤ)) ≤ 0

theorem no_energy_production_except_buoyancy … : (velocity pairing ≤ κ√E√S - νE) ∧ (temperature pairing ≤ 0)
```

**`hκ : 0 ≤ κ` is required.** As first specified the velocity bound is *false* for `κ < 0`: a
machine-checked counterexample (`ν=1, κ=−1, n=1, u₀=1, u₁=0, θ≡−1` gives LHS `0`, RHS `−2`) was
produced and removed. `κ ≥ 0` is the physical buoyancy sign.

### The Grönwall engine (`Cascade/Gronwall.lean`, standalone)

`le_gronwallBound_of_hasDerivAt` (linear comparison, from mathlib's
`le_gronwallBound_of_liminf_deriv_right_le`), `gronwallBound_le_max_of_neg` (uniform-in-time bound
when `b < 0`). For the model's `E' ≤ 2κ√S₀·√E − 2νE` the AM–GM step `2√E ≤ 1 + E` gives the
linear inequality `E' ≤ a + bE` with `a = κ√S₀`, `b = κ√S₀ − 2ν`; hence
`energy_le_max_of_rate_le` (uniform bound `E t ≤ max (E 0) (κ√S₀/(2ν − κ√S₀))` when `2ν > κ√S₀`)
and `no_finite_time_blowup` (bounded on every compact `[0,T]`, with the explicit constant
`energyBound`). **Continuity is required and was added**: the literal `[0,T)`-derivative
statements are false without it — `E t = exp(−2νt)/t`, `E 0 = 0` satisfies every stated
hypothesis and is unbounded at `0⁺` — so the theorems carry `ContinuousOn`/`ContinuousAt`.

### The capstone (`Cascade/NoBlowup.lean`)

```lean
def IsUnforcedTruncatedSolution (ν μ κ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ) : Prop
def velocityEnergy (u : ℤ → ℝ) (N : ℕ) : ℝ
def entropy (θ : ℤ → ℝ) (N : ℕ) : ℝ

theorem velocityEnergy_hasDerivAt … : HasDerivAt (fun s => velocityEnergy (u s) N)
    (2 * ∑ k ∈ Finset.range N, u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ)) t
theorem entropy_hasDerivAt …
theorem entropy_antitone (hμ : 0 ≤ μ) … : Antitone fun t => entropy (θ t) N

theorem truncated_unforced_energy_bounded (hν : 0 < ν) (hμ : 0 ≤ μ) (hκ : 0 ≤ κ) … :
    ∃ C, ∀ t ∈ Set.Icc 0 T, velocityEnergy (u t) N ≤ C
theorem truncated_unforced_energy_le_max … (hgap : 0 < 2 * ν - κ * Real.sqrt (entropy (θ 0) N)) :
    ∀ t ∈ Set.Icc 0 T,
      velocityEnergy (u t) N ≤ max (velocityEnergy (u 0) N)
        (κ * Real.sqrt (entropy (θ 0) N) / (2 * ν - κ * Real.sqrt (entropy (θ 0) N)))
```

The predicate is inhabited (`zero_is_unforcedTruncatedSolution`), and the rate inequality is
checked non-vacuously at a concrete non-zero state (`E = 10`, `S = 5`, pairing `= −30`,
`−60 ≤ 2√5·√10 − 20`, strict). The capstone carries a redundant `hcont : ContinuousOn …`
(derivable from differentiability) kept for interface symmetry; note it when reusing.

**Scope caveat.** This is the *truncated* model with Dirichlet ends — the boundary conditions are
an explicit modelling hypothesis. The stronger **enstrophy** statement is a documented stretch:
the conserved pairing is `Σ u_k T^u_k = 0`, but the enstrophy pairing `Σ 4^k u_k T^u_k` does
**not** telescope (`= (3/4)Σ 8^k u_{k−1}²u_k` on a finite range), so enstrophy genuinely
cascades; bounding it is a Riccati/Bernoulli estimate, not claimed here.

---

## Done — Stage O′ (`Enstrophy.lean` + `Riccati.lean` + `EnstrophyBound.lean`)

Stage O bounds the **`L²` energy**, which is *not* the norm blowup is measured in. Stage O′ bounds
the **enstrophy** `H = Σ4^k u_k²`, i.e. the `H¹` norm.

**Key fact — enstrophy cascades.** Energy is conserved by the transfer (`Σ u_k T^u_k = 0`), but
enstrophy is not:

```lean
theorem enstrophy_pairing (ν κ : ℝ) (u θ : ℤ → ℝ) (N : ℕ)
    (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0) :
    (∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)) * u (k:ℤ) * dyadicVelocityRHS ν κ u θ (k:ℤ))
      = 3 * (∑ k ∈ Finset.range N, (vorticity u ((k:ℤ)-1))^2 * vorticity u (k:ℤ))
        + κ * (∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)) * u (k:ℤ) * θ (k:ℤ))
        - ν * (∑ k ∈ Finset.range N, dyadicWeight (4*(k:ℤ)) * (u (k:ℤ))^2)
```
with `vorticity u k = 2^k u_k` and `dyadicWeight k = 2^k`. On `u = (0,1,3,0)` both sides are `18`.
Proved via an explicit enstrophy flux `enstrophyFlux u k = (1/4)·8^k u_{k-1}²u_k` and telescoping
(`transfer_enstrophy_pointwise`).

**The budget.** `Σ_k 4^k u_k·dyadicVelocityRHS_k ≤ 3H√H + κ√H√T − νH²/E`, assembled from
`sum_vorticity_cubic_le` (`Σa_{k-1}²a_k ≤ H√H`, needs `u(-1)=0` — false without it),
`enstrophy_sq_le_dissipation_mul_energy` (`H² ≤ (Σ16^k u_k²)·E`, Cauchy–Schwarz interpolation) and
`buoyancy_enstrophy_le` (`Σ4^k u_kθ_k ≤ √H√T`). The transfer is **cubic** (`H^{3/2}`) against
**quadratic** dissipation (`H²/E`), ratio `E/√H → 0` — the correct form of "dissipation beats
transfer", as opposed to the naive termwise `N^{3/2}` vs `N²` comparison.

**The engine** (`Cascade/Riccati.lean`, standalone): the Bernoulli barrier
```lean
theorem le_of_deriv_le_bernoulli {y y'} {a b T : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hcont : ContinuousOn y (Set.Icc 0 T)) (hderiv : ∀ t ∈ Set.Ico 0 T, HasDerivAt y (y' t) t)
    (hineq : ∀ t ∈ Set.Ico 0 T, y' t ≤ a * y t * Real.sqrt (y t) - b * (y t)^2) :
    ∀ t ∈ Set.Icc 0 T, y t ≤ max (y 0) ((a / b)^2)
```
proved by first-crossing + mean value theorem (no ODE-comparison black box, **no added
hypotheses**), plus `le_of_deriv_le_const_sub_sq`. `y * √y` is used throughout so no `Real.rpow`
appears.

**The capstone** (`Cascade/EnstrophyBound.lean`):
```lean
theorem truncated_unforced_enstrophy_bounded (hν : 0 < ν) (hμ : 0 < μ) (hκ : 0 ≤ κ) … :
    ∃ C, ∀ t ∈ Set.Icc 0 T, enstrophy (u t) N ≤ C

theorem enstrophy_bounded_isothermal … (hκ0 : κ = 0) … :
    ∀ t ∈ Set.Icc 0 T, enstrophy (u t) N ≤ max (enstrophy (u 0) N) ((3 * E_max / ν) ^ 2)
```
Route: the **Lyapunov function** `enstrophyLyapunov = H + (κ/(2μ))·S`, whose `S' = −2μT` cancels
the `+κT` buoyancy source exactly (`temperature_pairing_eq_neg_mu_tempEnstrophy`); Young
(`young_cubic_le`, `young_linear_le` — both **sharp**, equality at the optimal points) absorbs
`6H√H` and `κH` into the dissipation, giving `Ψ' ≤ enstrophyYoungConst ν κ E_max` and hence
`H(t) ≤ H(0) + (κ/(2μ))S(0) + enstrophyYoungConst ν κ E_max · T`. The bound is **linear in `T`** —
bounded on every compact interval, exactly no finite-time blowup in the `H¹` norm. For `κ = 0` the
source is absent and the barrier gives the strictly better **uniform** bound
`H ≤ max(H(0), (3E_max/ν)²)`.

**Scope caveats.** Still the *truncated* model with Dirichlet ends, still *unforced*. The
uniform-in-`T` bound for `κ > 0` (as opposed to linear-in-`T`) would need the coupled `(H, T)`
system done jointly and is not claimed. The ODE continuation corollary (bounded on compacts ⟹
global existence) is also not formalised.

**Frequency-localized version, tied to Palasek's argument** (`Cascade/ScaleObstruction.lean`):

```lean
theorem dissipation_tail_ge (u : ℤ → ℝ) (K N : ℕ) (hKN : K ≤ N) :
    dyadicWeight (2*(K:ℤ)) * (∑ k ∈ Finset.Ico K N, dyadicWeight (2*(k:ℤ)) * (u (k:ℤ))^2)
      ≤ ∑ k ∈ Finset.Ico K N, dyadicWeight (4*(k:ℤ)) * (u (k:ℤ))^2

theorem tail_transfer_cubic_le (u : ℤ → ℝ) (K N : ℕ) (huBot : u (-1) = 0) :
    |∑ k ∈ Finset.Ico K N, (vorticity u ((k:ℤ)-1))^2 * vorticity u (k:ℤ)|
      ≤ enstrophy u N * Real.sqrt (enstrophy u N)

theorem scale_dissipation_dominates (ν : ℝ) (hν : 0 < ν) … (hthr : 3 * (H * √H) ≤ ν * N_K² * H_tail) :
    3 * |∑_{k∈Ico K N} a_{k-1}²a_k| ≤ ν * (∑_{k∈Ico K N} 16^k u_k²)

theorem bernstein_exponent_gt_dissipation {d : ℕ} (hd : 5 ≤ d) (N : ℝ) (hN : 1 < N) :
    N ^ (2:ℝ) < N ^ ((d:ℝ)/2)
```

**Honest framing** (recorded in the file header). Palasek's argument is a **spatial** one: Bernstein
`L²→L∞` converts an energy bound into an `N_k^{d/2}` amplitude bound, compared against viscous
damping `νN_k²`. A shell model has **explicit amplitudes**, so `|a_k| ≤ √H`
(`vorticity_abs_le_sqrt_enstrophy`) replaces Bernstein and is *stronger* than `N^{d/2}√E`; hence
the factor `N_k^{3/2}` **never appears literally**. This is Palasek's comparison *in shell
variables*, not the literal spatial-Bernstein proof. The `d/2`-vs-`2` dichotomy is recorded
separately — `N^{d/2} ≤ N²` for `d ≤ 4` (`Cascade.bernstein_exponent_le_dissipation`, delegating to
`BernsteinTransfer`) and `N² < N^{d/2}` for `d ≥ 5`, `N > 1`
(`Cascade.bernstein_exponent_gt_dissipation`, the new high-dimension direction, Palasek's "no
obstruction in high dimension"). `tail_transfer_cubic_le` needs `u(-1) = 0` — it is false without
it (`K=0`, `u(-1)=2000`, `u(0)=1`, `N=1` gives `10⁶ > 1`), because the boundary amplitude sits in
the tail with no matching contribution to `H`.

**Upshot.** The dyadic obstruction does not need Bernstein, and is *strictly easier* than the PDE
heuristic — which is exactly Tao's hope that removing unwanted interactions makes the argument
shorter and more transparent. The transfer/dissipation dichotomy is captured by the shell's own
`H^{3/2}`-vs-`H²/E` budget, and the `d/2`-vs-`2` comparison is retained separately as the
"where the obstruction lives" statement.

---

## Done — Stage G, the phase (`Cascade/Phase.lean`)

`Cascade/Lacunary.lean` reduced the model to the amplitude pair but **deleted the wave's
geometry**: the buoyancy coupling was the frozen number `b = 2ⁿκ`. Stage G restores the
wavevector `ζ` with AB's own page-4 dynamics (their eq. (3.2)):

```
ζ̇ = −Dᵀζ,   Θ̇ = −(Jζ·G)/(λ|ζ|²)·Ω,   Ω̇ = λζ₀·Θ.
```

* **The steering lemma.** For the `α̇J` part of AB's background gradient (`D_{<q}`, eq. (3.3)),
  `D = α' • rotJ` and `Dᵀ = −D`, so `ζ̇ = α' • (Jζ)`, solved by `ζ(t) = rotR(α(t))·ζ(0)`:
  `rotJ * rotR α` is the angular derivative of `rotR α` and `rotJ² = −1`, i.e. `rotR α = exp(αJ)`.
  Stated componentwise (`phase_steering_component`) because `Matrix (Fin 2) (Fin 2) ℝ` has no norm
  instance in this pin.
* **The coupling is a steerable cosine.**
  ```lean
  theorem phase_coupling_cosine (λ α : ℝ) (ζ₀ : Fin 2 → ℝ) :
      abVortCoeff λ (rotR α *ᵥ ζ₀) = λ * (ζ₀ 0 * Real.cos α - ζ₀ 1 * Real.sin α)
  theorem phase_coupling_bound (λ α : ℝ) (ζ₀ : Fin 2 → ℝ) :
      |abVortCoeff λ (rotR α *ᵥ ζ₀)| ≤ |λ| * l2norm ζ₀
  theorem phase_flip (λ c : ℝ) (hc : 0 < c) :
      abVortCoeff λ (rotR 0 *ᵥ ![c,0]) = λ * c ∧ abVortCoeff λ (rotR Real.pi *ᵥ ![c,0]) = -(λ * c)
  theorem phase_flip_quantitative (λ c : ℝ) (hc : 0 < c) (y : ℝ) (hy : |y| ≤ |λ| * c) :
      ∃ α, abVortCoeff λ (rotR α *ᵥ ![c,0]) = y
  ```
  a half-turn flips the sign, and the coupling sweeps the whole interval `[-|λ|c, |λ|c]`.
* `ab_product`: the product of AB's two coefficients is independent of `λ`, and
  `rotJ_mulVec_dot_rotR`: AB's temperature numerator is invariant under a *simultaneous* rotation
  of `ζ` and `G` (with `G` fixed it is **not** invariant — the steering changes the angle, hence
  the temperature coupling too).

### Stage G′ — the consequence (`Cascade/PhaseGrowth.lean`)

The scalar obstruction assumes a *constant-coefficient* amplitude pair: the sign of `ab` is
frozen, so growth vs oscillation is decided by the initial data. With the phase, `b` is steerable,
and that is now a theorem. Taking `a` fixed and nonzero and `ζ₀ = ![c,0]`:

```lean
theorem phase_controls_growth_sign (a lam c : ℝ) (hc : 0 < c) (ha : a ≠ 0) (hlam : lam ≠ 0) :
    ∃ α₁ α₂, a * abVortCoeff lam (rotR α₁ *ᵥ ![c,0]) > 0
           ∧ a * abVortCoeff lam (rotR α₂ *ᵥ ![c,0]) < 0

theorem phase_selects_growth_or_oscillation (a lam c : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hc : 0 < c) :
    (0 < a * b(0) ∧ 0 < Real.sqrt (a * b(0)))
    ∧ (a * b(π) < 0 ∧ Real.sqrt (a * b(π)) = 0)          -- b(α) := abVortCoeff lam (rotR α *ᵥ ![c,0])

theorem phase_controls_growth_rate (a lam c : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hc : 0 < c)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ Real.sqrt (a * lam * c)) :
    ∃ α, Real.sqrt (a * abVortCoeff lam (rotR α *ᵥ ![c,0])) = r
```

**The finding.** The sign of the growth product is steerable whatever `a` is; aligned data
(`α = 0`) gives `ab > 0` and positive growth rate while the *same data* after a half turn
(`α = π`) gives `ab < 0` and rate `0` — growth vs oscillation is selected by the phase, not by
the initial data; and as `α` turns, the rate sweeps the **whole** interval
`[0, √(a λ c)]`, with the maximum at the aligned wavevector. So the scalar model deleted exactly
the interaction that controls the instability. This is also the formal setting of AB's control
problem: Stage B's force must *hold* the coupling favourable, not merely excite a mode.

**Scope.** Only `b` is treated as steerable here; in AB the temperature coefficient
`a = abTempCoeff λ ζ G` also depends on `ζ` (with `G` fixed, `(Jζ)·G` is *not* invariant when
`ζ` rotates — cf. `rotJ_mulVec_dot_rotR`), so steering both together, and the full per-octave
realisation (one wavevector per octave, `G`/`D` accumulated from the lower octaves as in AB
eq. (3.3)), is the next step and is not claimed.

**This does not touch the Stage-O/O′ enstrophy bound.** That bound is a comparison in
*magnitudes* — transfer `≤ 3H√H` against dissipation acting at rate `N_K²` — and phases never
enter it (the tail transfer is `Σ a_{k-1}²a_k`). Nothing in the repo bridges the 2×2 amplitude
pair to enstrophy production, so `PhaseGrowth` cannot loosen the obstruction. What the phase
removes is a **linear** brake: with the frozen coupling `b = 2ⁿκ`, a wrong-signed constant kept
the Rayleigh–Taylor mode from igniting at all. It does **not** raise the coupling ceiling
either — `a·λ·c` is the coupling the scalar model already had at the aligned wavevector; the
phase lets the system *reach* it. The one open route by which the phase could touch the
absorption threshold — whether steering `a` as well can move the `3H√H` coefficient itself — is
now treated in Stage G″ below.

---

### Stage G″ — controlling **both** coefficients (`Cascade/PhaseControl.lean`)

Stage G′ held the temperature coefficient `a` fixed and steered only `b`. AB steers both, and that
changes the answer. With `ζ(α) = rotR α · ![c,0]` and `G = ![g₀,g₁]`:

```lean
theorem ab_both_formula (λ c : ℝ) (hλ : λ ≠ 0) (hc : 0 < c) (G : Fin 2 → ℝ) (α : ℝ) :
    abTempCoeff λ (rotR α *ᵥ ![c,0]) G * abVortCoeff λ (rotR α *ᵥ ![c,0])
      = -(G 1)/2 + (G 0/2) * Real.sin (2*α) - (G 1/2) * Real.cos (2*α)

theorem ab_both_add_pi … : (product at α + π) = (product at α)
theorem ab_both_range … : -(G 1)/2 - √(G 0²+G 1²)/2 ≤ product ≤ -(G 1)/2 + √(G 0²+G 1²)/2
theorem ab_both_max_attained … / ab_both_min_attained …        -- both bounds attained
theorem ab_both_positive_iff (λ c : ℝ) (hλ : λ ≠ 0) (hc : 0 < c) (G : Fin 2 → ℝ) :
    (∃ α, 0 < product) ↔ (G 0 ≠ 0 ∨ G 1 < 0)
theorem ab_both_vertical_nonpos … (h0 : G 0 = 0) (h1 : 0 ≤ G 1) : product ≤ 0
```

**Three consequences, and one correction.**

1. **`λ` and `c` cancel** (`ab_both_eq_of_lambda_c`): the product depends only on the background
   gradient `G` and the steering angle — neither the coupling strength nor the wavenumber matters
   for *which* regime you are in.
2. **Correction to Stage G′.** The product is **`π`-periodic in `α`**: a *half turn leaves it
   unchanged* (`ab_both_add_pi`). The G′ statement "a half turn flips the coupling" was an artifact
   of holding `a` fixed — when both coefficients move, the half turn flips `a` and `b` *together*, so
   `ab` is invariant. The G′ theorems remain true, but they describe a model in which only `b` moves.
3. **In the stably stratified case the obstruction survives the phase.** The range is exactly
   `[-(g₁+R)/2, (R−g₁)/2]` with `R = √(g₀²+g₁²)`, so growth is attainable **iff `g₀ ≠ 0` or
   `g₁ < 0`**, and the maximum rate is `√((R−g₁)/2)`. For a **purely upward** gradient
   (`G 0 = 0`, `0 ≤ G 1`) the product is `≤ 0` for **every** orientation
   (`ab_both_vertical_nonpos`): orientation is not a control there. This is the first place in the
   project where restoring the phase buys nothing — and the natural thing for Stage B's force to
   have to overcome.

As in G′, this is a statement about the 2×2 amplitude pair and does **not** touch the Stage-O/O′
enstrophy budget (a magnitude comparison in which phases do not appear).

---

### Stage H — the one-wavevector-per-octave realisation (`Cascade/Layers.lean`)

Stages G/G′/G″ treated a **single** wavevector whose steering angle `α` is a *free* control. AB
eq. (3.3) is a different model: **one wavevector per octave**, the `q`-th octave driven **one-way**
by the accumulated background of the octaves below it. `Layers.lean` realises it. With
`e_j = ζ_j/|ζ_j|` (Euclidean, `unitVec`), `A_j = −λ_j|ζ_j|Θ_j` (`layerGradScalar`) and
`G_{<q} = −e₀ − Σ_{j<q} w_j A_j e_j` (`Gprefix`),
`D_{<q} = α' J + Σ_{j<q} w_j Ω_j (J e_j) ⊗ e_j` (`Dprefix`), the octave ODEs are

```lean
def layerZetaRHS  (α' w Ω ζ q)        := fun i => -(((Dprefix α' w Ω ζ q)ᵀ) *ᵥ ζ q) i
def layerThetaRHS (e0 lam w Θ Ω ζ q)  := abTempCoeff (lam q) (ζ q) (Gprefix e0 lam w Θ ζ q) * Ω q
def layerOmegaRHS (lam Θ ζ q)         := abVortCoeff (lam q) (ζ q) * Θ q
```

with the structural content:

```lean
theorem Gprefix_zero / Dprefix_zero                      -- G_{<0} = −e₀, D_{<0} = α' • J
theorem Gprefix_succ (q) / Dprefix_succ (q)              -- append one octave: the greedy step
theorem Gprefix_congr / Dprefix_congr                    -- lower octaves only
theorem layerRHS_congr_of_agree_le                       -- TRIANGULARITY (headline)
theorem layerOmegaRHS_eq                                 -- b_q = λ_q (ζ_q)₀ * Θ_q
```

**Two findings.**

1. **The phase is no longer a free control.** `ζ_q` is forced by `D_{<q}`, which is assembled from
   the *lower* octaves' `Ω_j`, `ζ_j`; `G_{<q}` likewise from the lower octaves' `Θ_j`, `ζ_j`. Only
   the common rotation rate `α'` remains a free background parameter — the individual phases are
   determined by the cascade beneath them. `Gprefix_succ`/`Dprefix_succ` make the generation-by-
   generation appending precise.
2. **Triangularity** (`layerRHS_congr_of_agree_le`): the right-hand sides at octave `q` are
   unchanged if only octaves `j > q` are altered. `G_{<q}`/`D_{<q}` mention only `j < q`, and
   octave `q`'s own RHS mentions `ζ_q`, `Θ_q`, `Ω_q` and nothing higher. This is Tao's "barely any
   feedback from high frequency waves back into the low frequency components" made structural, and
   it is what makes the greedy (low-to-high) construction of AB possible.

**Scope.** This is the *realisation* — model plus one-way structure — **not** the blowup: no claim
here that the coupled system develops a singularity. As in `Phase.lean`/`PhaseControl.lean`, `|ζ|`
is the explicit Euclidean `l2norm` (never the ambient `‖·‖`, which is the sup norm on `Fin 2 → ℝ`),
and the layer ODEs are recorded as right-hand sides rather than `HasDerivAt` statements because
`Matrix (Fin 2) (Fin 2) ℝ` carries no norm instance at this pin. Non-vacuity is checked against
AB (3.3) numerically: `Gprefix` at `e0 = ![1,0]`, `λ = w = 1`, `Θ = (3,5)`, `ζ_j = ![1,0]` and
`q = 2` is `![7,0]`; `Dprefix` with `α' = 1`, `Ω = (2,4)` is `!![0,−1;7,0]`.

---

## Done — Stage B, the forced model (negative result) (`Cascade/ForcedModel.lean`)

Stage B asked for the dyadic analogue of the Alpöge–Buckmaster construction: a forced model that
blows up in finite time, so that `B ∧ O` would exhibit a forced-vs-unforced asymmetry. **It came out
negative, and that is the result.** The force does not open a blowup channel in this model.

### The model is frozen so that `B` and `O` are the *same* model

Following the Stage-O recommendation (viscous + force, force toggled), the force enters as one added
term and nothing else changes:

```lean
def forcedVelocityRHS (ν κ : ℝ) (f u θ : ℤ → ℝ) (k : ℤ) : ℝ :=
  dyadicVelocityRHS ν κ u θ k + f k
def forcedTemperatureRHS (μ : ℝ) (h u θ : ℤ → ℝ) (k : ℤ) : ℝ :=
  dyadicTemperatureRHS μ u θ k + h k
def forcedBoussinesqRHS (ν μ κ : ℝ) (f h u θ : ℤ → ℝ) (k : ℤ) : ℝ × ℝ :=
  (forcedVelocityRHS ν κ f u θ k, forcedTemperatureRHS μ h u θ k)

theorem forcedVelocityRHS_zero … : forcedVelocityRHS ν κ (fun _ => 0) u θ k = dyadicVelocityRHS ν κ u θ k
theorem forcedTemperatureRHS_zero … / forcedBoussinesqRHS_zero …
theorem isForcedTruncatedSolution_zero_iff … :
    IsForcedTruncatedSolution ν μ κ N 0 0 u θ ↔ IsUnforcedTruncatedSolution ν μ κ N u θ
```

`IsForcedTruncatedSolution` has **exactly** the shape of `IsUnforcedTruncatedSolution` — equations
on all of `ℤ`, the same Dirichlet ends `u(-1) = u(N) = θ(-1) = θ(N) = 0`, time-dependent ladders
`u θ : ℝ → ℤ → ℝ` — with only the RHS forced. The `_zero` lemmas are not `rfl` (see gotcha 15) but
they unfold *only* the forced-RHS definition, so `B ∧ O` really is one system with the force
toggled, not two systems that happen to look alike.

### Negative 1 — the force cannot blow up the energy

```lean
theorem forced_energy_rate_le (ν μ κ) (hκ : 0 ≤ κ) (hν : 0 ≤ ν) (N) (f h) (u θ)
    (hsol : IsForcedTruncatedSolution ν μ κ N f h u θ) (t) :
    2 * (∑ k ∈ range N, u t k * forcedVelocityRHS ν κ f (u t) (θ t) k)
      ≤ 2 * (κ * √(entropy (θ t) N) + √(forceEnergy f N)) * √(velocityEnergy (u t) N)
        - 2 * ν * velocityEnergy (u t) N

theorem forced_truncated_energy_bounded (hν : 0 < ν) (hκ : 0 ≤ κ) … (T) (hT : 0 ≤ T) :
    ∃ C, ∀ t ∈ Set.Icc 0 T, velocityEnergy (u t) N ≤ C
```

With energy-conserving transfer the forced energy obeys the **logistic** inequality
`E' ≤ 2(κ√S + √F)√E − 2νE`, which is globally bounded: a fixed force is *linear* in `√E` while
dissipation is linear in `E`, so large `E` is always damped. The entropy appears at the current time
`S(t)`, not `S(0)` — a temperature force destroys entropy monotonicity, so `S(0)` is not available;
using `S(t)` is strictly stronger and needs no monotonicity at all. There is also
`forced_energy_le_max_unforced_temperature`: for the standard case `h = 0` the entropy *is* antitone
and one gets a **uniform-in-time** bound `E(t) ≤ max(E(0), (κ√S(0)+√F)/(2ν − κ√S(0) − √F))`,
provided the dissipation gap `2ν > κ√S(0) + √F`; the extra `√F` in the gap is the price of the
force.

Load-bearing hypotheses, and two that turned out **not** to be needed: `0 < ν` and `0 ≤ κ` are
load-bearing; finiteness of `f` is *not* needed (`forceEnergy f N` is a finite sum of squares for any
`f`), and neither is continuity (it is derived from differentiability in the predicate, with the
entropy ceiling obtained from compactness of `Icc 0 T`).

### Negative 2 — the force cannot blow up the enstrophy either

```lean
theorem forced_enstrophy_rate_le (ν κ E_max) (hκ : 0 ≤ κ) (hν : 0 ≤ ν) (hEpos : 0 < E_max) (N f u θ)
    (huBot : u (-1) = 0) (huTop : u (N:ℤ) = 0) (hEmax : velocityEnergy u N ≤ E_max) :
    2 * ∑_{k<N} 4^k u_k (du_k/dt)_forced
      ≤ 6 H √H + κ (H + T) + 2 √H √He − 2 ν H²/E_max

theorem forced_enstrophy_young (hν : 0 < ν) (hEpos : 0 < E_max) (hκ : 0 ≤ κ) (hHe : 0 ≤ He)
    (hTmax : 0 ≤ T_max) (hs : 0 ≤ s) :
    6s³ + κs² + 2√He·s + κT_max ≤ (ν/E_max)s⁴ + (2187/(16(ν/(2E_max))³) + κ²/(4(ν/(4E_max))) + E_max/ν + He + κT_max)

theorem forced_truncated_enstrophy_bounded (hν : 0 < ν) (hκ : 0 ≤ κ) … (T) (hT : 0 ≤ T) (hcont) :
    ∃ C, ∀ t ∈ Set.Icc 0 T, enstrophy (u t) N ≤ C
```

This is the forced analogue of `truncated_unforced_enstrophy_bounded`, and it is the closest the
project came to a blowup. The mechanism is a **homogeneity mismatch**: the destabilising terms are
cubic transfer (`6H^{3/2}`) and the force work, which Cauchy–Schwarz makes *sublinear*
(`2√H√He`) — homogeneity `1/2` — while viscous dissipation is quadratic (`2νH²/E_max`). Young's
inequality absorbs the cubic and the force terms into the dissipation above the explicit threshold
`√(C₀/(ν/E_max))`, and the Bernoulli barrier `le_of_deriv_le_const_sub_sq` forbids crossing it. So
the force merely *shifts* the barrier; it does not create a channel. The force's own Cauchy–Schwarz
step is `force_enstrophy_work_le`: `∑_{k<N} 4^k u_k f_k ≤ √H √He`, the exact analogue of
`buoyancy_enstrophy_le`.

### Verdict

**The forced-vs-unforced asymmetry does not materialise in this model.** Force off: no blowup
(Stage O energy, Stage O′ enstrophy). Force on: still no blowup (Stage B energy and enstrophy). So
the capstone `B ∧ O` is itself a **negative** result — the model is too dissipative to exhibit the
asymmetry that the Tao/Palasek exchange is about. Combined with Stage R′ this is consistent rather
than surprising: the scaling-covariant Boussinesq model has dissipation degree `d = 2` (`α = 1`),
which is inside the provably regular regime of the scalar dyadic model, and Cheskidov's model
already includes the force.

The same conclusion holds for the **untruncated** model: at `α = 1` the scalar dyadic model is
globally regular (Cheskidov), and Stage O/O′ are our own proofs in the Boussinesq setting. So at
`d = 2` there is no forced blowup, truncated or not. A dyadic blowup requires a **different model
with weaker dissipation** — Cheskidov's threshold is `α < 1/3`, and his blowup is *data-driven*
(large `H^γ` norm) rather than force-driven, on the infinite lattice. Stage R′ is precisely the
statement that the scaling-covariant Boussinesq model cannot be that model.

Honest limitations of the bounds above:

- The enstrophy constant `C` depends on the solution (through the energy ceiling `E_max` and the
  temperature-enstrophy ceiling `T_max`), not on the data alone. A uniform-in-time enstrophy bound
  would need `h = 0` (so `T` is non-increasing, via `temperature_pairing_eq_neg_mu_tempEnstrophy`)
  *and* a uniform energy ceiling, i.e. the gap condition above.
- `hcont` is carried as an explicit hypothesis to match the unforced capstone's convention; it is in
  fact automatic here.
- The buoyancy source `κ(H + T)` is what defeats the unforced Lyapunov cancellation
  `Ψ = H + (κ/2μ)S` once `h ≠ 0`.
- As always: a model. Nothing here is a statement about the Boussinesq PDE.

### Stage B′ — the sign of `κ` is irrelevant (`Cascade/BuoyancySign.lean`)

Every no-blowup theorem above assumed `0 ≤ κ`. That hypothesis was a **statement artifact**, not
mathematics: the bounds were written `κ · Σ_k u_k θ_k ≤ κ · √E · √S`, which is false for `κ < 0`
(the correct Cauchy–Schwarz bound is two-sided: `|Σ_k u_k θ_k| ≤ √E √S`). It entered the proofs only
through `mul_le_mul_of_nonneg_left`. The sign-free replacement is

```lean
theorem buoyancy_energy_le_abs (κ : ℝ) (u θ : ℤ → ℝ) (N : ℕ) :
    κ * (∑ k ∈ Finset.range N, u k * θ k)
      ≤ |κ| * (Real.sqrt (velocityEnergy u N) * Real.sqrt (entropy θ N))

theorem buoyancy_enstrophy_le_abs (κ : ℝ) (u θ : ℤ → ℝ) (N : ℕ) :
    κ * (∑ k ∈ Finset.range N, dyadicWeight (2*k) * u k * θ k)
      ≤ |κ| * (Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N))
```

and with `|κ| ≥ 0` every downstream engine applies verbatim (`ν`-Grönwall,
`energy_le_energyBound_of_rate_le`, `energy_le_max_of_rate_le`, the Young absorptions, the barrier
`le_of_deriv_le_const_sub_sq`). **Eleven statements are re-proved with `κ` arbitrary**, dropping
`0 ≤ κ` entirely:

```lean
velocity_energy_pairing_le_abs / velocity_energy_rate_le_of_solution_abs
truncated_unforced_energy_bounded_abs / truncated_unforced_energy_le_max_abs
forced_velocity_pairing_le_abs / forced_energy_rate_le_abs
forced_energy_rate_le_of_entropy_le_abs / forced_truncated_energy_bounded_abs
forced_energy_le_max_unforced_temperature_abs
enstrophy_pairing_le_abs / enstrophy_rate_le_of_solution_abs
enstrophyLyapunov_deriv_le_abs / truncated_unforced_enstrophy_bounded_abs
forced_enstrophy_rate_le_abs / forced_truncated_enstrophy_bounded_abs
```

**Verdict: unstable stratification (`κ < 0`) does not produce a finite-time blowup either**, in
energy or enstrophy, forced or unforced. So **no finite-time blowup in the frozen truncated model
for any `κ`** — the missing piece of "no matter what" in this model. No `κ < 0` hypothesis was
needed anywhere, so no counterexample exists or was found.

**Why sign cannot matter here.** Buoyancy is a *bounded forcing*, never an amplifier. The temperature
ladder's own equation does not involve `κ`, and its energy is non-increasing (`entropy_antitone`),
so buoyancy enters the velocity equation linearly: `E' ≤ 2(|κ|√S + √F)√E − 2νE`, the same logistic
shape as Stage B. In the enstrophy budget it contributes only `|κ|√H√T`, homogeneity `1/2` in `H` —
the same order as the Stage-B force work, below the cubic transfer (`3/2`) and far below the
quadratic dissipation (`2`). The Stage O′ Lyapunov `Ψ = H + (κ/2μ)S` is itself sign-free (the
`+κT` source cancels `−κT` for either sign); the *only* place the sign survives is bookkeeping:

```lean
theorem enstrophyLyapunov_deriv_le_abs … :
    2*(∑ 4^k u_k · du_k/dt) + (κ/(2μ))*(2*(∑ θ_k · dθ_k/dt))
      ≤ enstrophyYoungConst ν κ E_max + (|κ| - κ) * T_max
```

with `(|κ| − κ)·T_max = 0` exactly when `κ ≥ 0` — so at `κ ≥ 0` this reduces to the existing
`enstrophyLyapunov_deriv_le`. That additive constant is the honest cost of unstable stratification,
and it is what keeps the barrier closing (it is a *constant*, not an `H`-dependent term). Uniform
recovery of `H` from `Ψ` uses `H ≤ Ψ + (|κ|/2μ)S(0)`.

**A deflationary corollary.** The two-species (Boussinesq) structure is **inert for the regularity
question** in this model. The temperature ladder is passive: it feeds the velocity equation a
bounded amount of energy and cannot drive a singularity whatever the sign of `κ`. All the action is
in the single-species cascade and its dissipation degree — which is what Stage R′ and Cheskidov's
thresholds are about.

Non-vacuity is machine-checked at `κ = −1` and mirrored at `κ = +1` (which is *not* excluded): at
`u = (0,1,3,0)`, `θ = (0,1,2,0)`, `f = (0,1,1,0)`, `N = 2` (`E = 10`, `S = 5`, `H = 37`, `T = 17`),
the energy buoyancy bound is `−7 ≤ √10·√5 ≈ 7.07` and the enstrophy one `−25 ≤ √37·√17 ≈ 25.08`,
both strict and with the right sign for the `|κ|` bound to be non-trivial.

Two hypothesis notes: the *unforced* enstrophy route keeps `0 < μ` because the Lyapunov bookkeeping
divides by `μ` (a `μ`-condition, not a `κ`-condition); the *forced* enstrophy route needs no `μ` at
all, matching `ForcedModel.lean`.

---

## Done — the dissipation threshold (`Cascade/DissipationThreshold.lean`)

Freezes the model with a general **dissipation degree** `e` — both channels, `ν·2^{ek}u_k` and
`μ·2^{ek}θ_k` — so `e = 2` is the library's Laplacian and Cheskidov's `α` is `e/2`. Recovery at
`e = 2` is `velocityRHSDegreeE_two` / `temperatureRHSDegreeE_two` / `boussinesqRHSDegreeE_two`, and
both components are scaling covariant with `ν, μ ↦ ·λ^{b+1−e}`, specialising to the library's
`λ^{b−1}` at `e = 2`.

### Two different thresholds, which are easy to conflate

With `H = Σ2^{2k}u_k²`, `E = Σu_k²`, `D_e = Σ2^{(2+e)k}u_k²` (the enstrophy-weighted dissipation),
`W_e = Σ2^{(2−e)k}u_k²`:

1. **Quadratic domination** `D_e ≥ c·H²/E` holds **iff `e ≥ 2`**. Below `e = 2` it fails for every
   constant, with the single-mode witness `D_e·E/H² = 2^{(e−2)k} → 0`:
   ```lean
   theorem single_mode_dissipation_ratio (e : ℤ) (k : ℕ) :
       D_e (deltaShell k) (k+1) * E (deltaShell k) (k+1) / (H (deltaShell k) (k+1))^2
         = (2:ℝ) ^ ((e-2) * (k:ℤ))
   theorem no_uniform_dissipation_domination (e : ℤ) (he : e < 2) (c : ℝ) (hc : 0 < c) :
       ∃ (u : ℤ → ℝ) (N : ℕ), D_e u N * E u N < c * (H u N)^2
   ```
2. **Barrier tractability** — what the enstrophy barrier actually needs. The interpolated backplate
   ```lean
   theorem weighted_cauchy_schwarz (e : ℤ) (u) (N) : (H u N)^2 ≤ D_e u N * W_e u N
   theorem weightedEnstrophy_sq_le (e : ℤ) (he0 : 0 ≤ e) (he2 : e ≤ 2) (u) (N) :
       (W_e u N)^2 ≤ (E u N)^e * (H u N)^(2-e)
   theorem dissipation_interp_sq (e : ℤ) (he0 : 0 ≤ e) (he2 : e ≤ 2) (u) (N) :
       (H u N)^((2+e).toNat) ≤ (D_e u N)^2 * (E u N)^e
   ```
   chains to `D_e ≥ H^{1+e/2}/E^{e/2}` — dissipation `H`-homogeneity `1 + e/2` against the cubic
   transfer's `3/2`. So the barrier closes **unconditionally iff `e > 1`**; at `e = 1` the two
   homogeneities **tie exactly** and it closes only conditionally (`ν > 3√E_max`); below that it is
   dead. For integers: unconditional at `e ≥ 2`, marginal at `e = 1`, dead at `e ≤ 0`.

The two are genuinely different questions: the barrier needs `1 + e/2 > 3/2`, *not* the homogeneity-2
quadratic domination. It was exactly this conflation that produced a spurious "the threshold is
`e = 2`, the brief is wrong" in a first pass at this file — see gotcha 17.

### The regular side, and what it means

```lean
theorem truncated_unforced_enstrophy_bounded_degreeE (hν : 0 < ν) (hμ : 0 < μ) (he : 2 ≤ e) … :
    ∃ C, ∀ t ∈ Set.Icc 0 T, enstrophy (u t) N ≤ C
theorem forced_truncated_enstrophy_bounded_degreeE (hν : 0 < ν) (he : 2 ≤ e) … :
    ∃ C, ∀ t ∈ Set.Icc 0 T, enstrophy (u t) N ≤ C
```

Both carry `|κ|` (no sign hypothesis — Stage B′) and use `dissipation_ge_of_two_le`
(`e ≥ 2 ⇒ D_e ≥ D_2 ≥ H²/E`), after which the Stage O′/B Young-plus-barrier argument goes through
unchanged. Ceilings for energy and for the thermal sinks come from continuity on the compact
`[0,T]`. `tempEnstrophyE e θ N = Σ2^{ek}θ_k²` is the degree-`e` thermal sink, matching the library's
convention that `tempEnstrophy` carries the dissipation weight.

**The finding.** The barrier's marginal point is `e = 1`, i.e. `α = 1/2` — which is **exactly
Cheskidov's global-regularity threshold**. So the natural energy method is *exponent-sharp*: it dies
at the same boundary as the state of the art, and the obvious method cannot cross the open gap. It
does **not** prove some cleverer argument cannot; only that this one is sharp. And the exponent
whose nonlinear estimates match 3D Navier–Stokes is `α = 2/5` (`e = 4/5`), which lies *below* the
barrier threshold: that is the formal content of "this toy model is easier than 3D Navier–Stokes".
**Correction:** the open gap is `α ∈ [1/3, 2/5)`, i.e. `e ∈ [2/3, 4/5)`, not `(2/3, 1)`;
Barbato–Morandin–Romito (Nonlinearity **24** (2011), arXiv:1007.3401) closed `α ∈ [2/5, 1/2)`, and
`α = 2/5` is their regularity endpoint — so the 3D-calibrated exponent is *regular*, not open. See
the correction block in the Stage R′ section.

**Integer restriction.** `dyadicWeight` is `zpow`, so `e : ℤ`. The unconditional range is `e ≥ 2`,
and the model's own exponent is `e = 2` — so the model sits at the **bottom** of the range the
barrier reaches, and there was never room to demonstrate the threshold by lowering `e` within the
integers. The continuous threshold would need `Real.rpow` for `2^{ek}`, real `e`, which is a
different (and much messier) formalisation; `dissipation_interp_sq` deliberately avoids it by
squaring, which turns every exponent into an integer.

---

## Done — the exact per-shell threshold (`Cascade/PerShellThreshold.lean`)

The threshold section above states the marginality of `e = 1` only as "the two homogeneities tie".
This file replaces that with an **exact, computable criterion**, and turns the fact that no
single-number threshold exists at `e = 1` into a **theorem**.

### The exact identity

Weighting the degree-`e` velocity equation by `2^{2k}u_k` and summing, the transfer telescopes
(reindexing `j = k−1` gives `8`, the second piece gives `2`, difference `6`, and the outer factor `2`
makes `12`; the Dirichlet values kill both boundary terms):

```lean
theorem enstrophy_pairing_degree (ν κ : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (N : ℕ)
    (huBot : u (-1) = 0) (huTop : u (N:ℤ) = 0) :
    2 * (∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)) * u (k:ℤ)
          * velocityRHSDegreeE ν κ 1 0 e u θ (k:ℤ))
      = 12 * (∑ j ∈ Finset.range (N-1), dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2 * u ((j:ℤ)+1))
        + 2 * κ * (∑ k ∈ Finset.range N, dyadicWeight (2*(k:ℤ)) * u (k:ℤ) * θ (k:ℤ))
        - 2 * ν * (∑ k ∈ Finset.range N, dyadicWeight ((2+e)*(k:ℤ)) * (u (k:ℤ))^2)
```

### The criterion, and why `e = 1` is the critical point

Comparing the transfer and dissipation contributions **shell by shell**, the transfer wins at
shell `j` exactly when `u_{j+1}` exceeds the bar

```lean
def perShellBar (ν : ℝ) (e : ℤ) (j : ℕ) : ℝ := (ν / 6) * dyadicWeight ((e - 1) * (j : ℤ))

theorem perShell_iff (ν : ℝ) (hν : 0 < ν) (e : ℤ) (u : ℤ → ℝ) (j : ℕ) (huj : u (j:ℤ) ≠ 0) :
    2 * ν * dyadicWeight ((2+e)*(j:ℤ)) * (u (j:ℤ))^2
        < 12 * dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2 * u ((j:ℤ)+1)
      ↔ perShellBar ν e j < u ((j:ℤ)+1)
```

**The bar is scale-invariant in `j` exactly at `e = 1`** (`bar_scale_invariant`), strictly
*increasing* in `j` for `e > 1` (`bar_strictMono`, so small scales face an ever-higher bar and
dissipation wins) and strictly *decreasing* for `e < 1` (`bar_strictAnti`, so small scales grow ever
more easily). That is the criticality as a number:

| `e` | bar `(ν/6)·2^{(e−1)j}` | verdict |
|---|---|---|
| `e > 1` | rises with `j` | regular |
| `e = 1` | **constant** `ν/6` | marginal |
| `e < 1` | falls with `j` | blowup |

### The headline: no single-number criterion at `e = 1`

At `e = 1` the identity collapses to a sum whose **sign depends on the distribution of `u`, not its
size**:

```lean
theorem budget_degree_one … :
    2 * (∑ k ∈ Finset.range N, …) = ∑ j ∈ Finset.range N,
        dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2 * (12 * u ((j:ℤ)+1) - 2*ν)
```

and the file exhibits two nonnegative states with **the same enstrophy and opposite rates**:

| state | enstrophy | rate |
|---|---|---|
| `u = (5, 0, 0, …)` | `25` | `−50` |
| `u = (3, 2, 0, …)` | `25` | `+134` |

```lean
theorem same_enstrophy_opposite_sign : ∃ u v : ℤ → ℝ, (∀ k, 0 ≤ u k) ∧ (∀ k, 0 ≤ v k)
    ∧ enstrophy u 2 = enstrophy v 2 ∧ budget2 1 u < 0 ∧ 0 < budget2 1 v

theorem no_enstrophy_only_criterion :
    ¬ ∃ P : ℝ → Prop, ∀ u : ℤ → ℝ, (∀ k, 0 ≤ u k) → (P (enstrophy u 2) ↔ 0 < budget2 1 u)
```

**So no criterion reading the enstrophy alone can decide the sign of its own rate at `e = 1`.** This
is non-pinnability stated exactly, and it is not vacuous: both witnesses are concrete and the
contradiction is derived, not assumed.

**Why this is the honest version of "pin the threshold".** The criterion is pinned exactly — a
closed-form critical amplitude per shell — and the *reason it cannot be sharpened to a single
number* is a theorem. At `e > 1` the rising bar suppresses the high shells regardless of shape, so
one number decides; at `e < 1` the falling bar favours them regardless of shape, so one number
decides; only at `e = 1` does shape get a vote. That is the precise sense in which the interesting
case is the undecidable one.

### Scope — the bar belongs to one sector, not to the model

Everything above is the **Katz–Pavlović** sector, `velocityRHSDegreeE ν κ 1 0` (`A = 1, B = 0` of
`boussinesqTransferU`, `Cascade/Boussinesq.lean:71`). The other named sector is **Obukhov**
(`A = 0, B = 1`) — the model of Palasek (arXiv:2407.06179, eq. (1.2)) and of Looi's
global-regularity theorem. `Cascade/PerShellSectorObukhov.lean` derives the pairing identity there
and finds that **there is no bar**: the shell summand carries `u_j` **linearly** instead of as
`u_j²`, so two states with the same `u_{j+1}` give opposite signs (`obukhovShellTerm_sign_flip`) and
no function of `(ν, e, j)` decides a shell (`no_obukhov_perShellBar`). The single structural
difference is that the square sits on `u_{j+1}` rather than on `u_j`.

**The bar is sector-specific; the `e = 1` criticality is not** — the factor `2^{(e−1)j}` is present
in both sectors, so its independence of `j` is governed by `e = 1` either way.

Two further facts worth recording. **Nothing in the library depends on the bar**: `perShellBar`,
`bar_scale_invariant`, `bar_strictMono`, `bar_strictAnti`, `perShell_iff`,
`same_enstrophy_opposite_sign` and `no_enstrophy_only_criterion` are referenced nowhere outside
`Cascade/PerShellThreshold.lean` — it is a leaf. And the `e ≥ 2` no-blowup capstones **cannot** use
it: they live in `DissipationThreshold.lean`, which this file *imports*. So the bar never carried
the library's negative results; it is a sector-specific presentation of the `e = 1` criticality.

---

## WITHDRAWN — the claimed finite-time blowup at degree `e = 0` (files deleted)

> **Status: WITHDRAWN / FALSE.** The files `Cascade/BlowupDegreeZero.lean`,
> `Cascade/BlowupRate.lean` and `Cascade/PositivityDegreeE.lean` have been deleted. Every
> statement below rested on the old all-of-`ℤ` truncated predicate, which is inconsistent with the
> Dirichlet condition `u_N = 0` and therefore vacuous (see the correctness episode above). What is
> actually true is recorded in `Cascade/TruncatedRegularity.lean`: the truncated chain has **no**
> finite-time blowup, at any degree `e ≥ 0` and any `κ`. The material below is kept only as a
> record of the withdrawn argument.

**The (withdrawn) claimed first genuine blowup theorem, and the `B` half of `B ∧ O`.** The model is
the scalar truncated dyadic chain at dissipation degree `e = 0` (uniform damping `ν·u_k`):

```
u_k' = 2^k (u_{k-1}² − 2 u_k u_{k+1}) − ν u_k,   0 ≤ k < N,   u_{-1} = u_N = 0,   ν ≥ 0
```

```lean
def blowupCoeff : ℝ := (27/28) * (holderConst 1 * (7/10) * Real.sqrt (7/10))   -- = 27√35/400 ≈ 0.399335
def blowupThreshold (ν : ℝ) : ℝ := (2 * ν / blowupCoeff) ^ 2                    -- ≈ 25.08 ν²

theorem no_global_solution_degree_zero (ν : ℝ) (hν : 0 ≤ ν) (μ : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (u θ : ℝ → ℤ → ℝ) (h : IsUnforcedTruncatedSolutionE ν μ 0 0 N u θ)
    (h0 : ∀ k, 0 ≤ u 0 k) (hlarge : blowupThreshold ν < lyap (u 0) N (4/7)) :
    False
```

In words: **no globally-defined ladder solves the chain from nonnegative data whose initial
Lyapunov value `lyap(u 0) N (4/7) = Σ_{k<N}2^k u_k(0)² + (4/7)Σ_{k<N}2^k u_k(0)u_{k+1}(0)` exceeds the
finite threshold `(2ν/c)²`.** The functional is forced to blow up by time `2/(c√y₀ − 2ν)`, so a
global solution cannot exist — since the predicate asserts differentiability for every real `t`,
`False` is the correct rendering of finite-time blowup.

### The four pieces, in dependency order

| Piece | File | What it supplies |
|---|---|---|
| Positivity | `Cascade/PositivityDegreeE.lean` | nonnegative data ⟹ `∀k, 0 ≤ u t k` (integrating factor; the source `2^k(u_{k-1})²` is a *square*, so no sign info on `k−1` is needed) |
| Lyapunov growth rate | `Cascade/BlowupRate.lean` | `H' ≥ (27/28)·cubicSum − 2ν·H` at `c₂ = 4/7`, plus `blowupNorm ≥ (7/10)H` |
| Inverted Hölder | `Cascade/BlowupEngine.lean` | `cubicSum ≥ A·S·√S` with `A = holderConst 1 = √(1/2)`, `S = blowupNorm` |
| Reversed Bernoulli engine | `Cascade/BlowupEngine.lean`, `BlowupDegreeZero.lean` | `y' ≥ c·y√y − 2ν·y`, `2ν < c√y₀` ⟹ `T ≤ 2/(c√y₀ − 2ν)` |

Chaining: `cubicSum ≥ A(7/10)^{3/2}·H√H`, so `H' ≥ c·H√H − 2ν·H` with
`c = (27/28)·A·(7/10)^{3/2} = 27√35/400`. Then `f = 1/√y` gives `f' ≤ νf − c/2`, and
`2ν < c√y₀` makes `f' ≤ −δ` for `δ = c/2 − νf₀ > 0`, so `f` reaches zero at `t = f₀/δ =
2/(c√y₀ − 2ν)` — contradicting `f > 0`.

**This is our theorem, not Cheskidov's.** His Theorem 5.1 requires `α > 0`; `e = 0` is `α = 0` and
is outside his hypotheses. We follow his argument and formalize the endpoint he does not cover.

### Two corrections to the brief, both found by the subagents and both load-bearing

1. **The engine needs `0 ≤ ν`.** The bound `T ≤ 2/(c√y₀ − 2ν)` is **false for `ν < 0`** — a
   machine-checked counterexample (`engine_false_without_nonneg`) exhibits `f t = (3/2)e^{-t} − 1/2`
   with `c = 1`, `ν = −1`, `f > 0` on `[0, 3/4]` where `3/4 > 2/3`. For `ν ≤ 0` the correct bound is
   the *larger* `2/(c√y₀)` (`le_of_deriv_ge_mul_sqrt_sub_nonpos`); the unified truth is
   `2/(c√y₀ − 2·max ν 0)`. The first draft of the brief asserted the `0 ≤ ν`-free version.
2. **The `7/10` needs the sharp correction bound.** The *exported* `correction_le_blowupNorm` gives
   only `correction ≤ blowupNorm`, hence `(7/11)·lyap ≤ blowupNorm`, not `(7/10)`. The sharp
   `correction ≤ (3/4)·blowupNorm` (AM–GM pointwise plus the weight shift `2^k = ½·2^{k+1}` and
   `u_N = 0`) is re-proved in `BlowupDegreeZero.lean` as `correction_le_three_quarters`, and it is
   what makes the stated `c` correct. Using `7/11` instead would give a different (smaller) `c`.

### The integer phase diagram (corrected)

| dissipation degree `e` | `α = e/2` | status |
|---|---|---|
| `e ≥ 2` | `α ≥ 1` | **no blowup** — enstrophy barrier closes; model's own exponent (`Cascade/DissipationThreshold.lean`) |
| `e = 1` | `α = 1/2` | **marginal for our method** — the two homogeneities tie exactly. This is Cheskidov's regularity threshold and regularity at `α ≥ 1/2` is known by other means, so this row is a limitation of the enstrophy barrier, **not** an open problem |
| `0 ≤ e` (incl. `e = 0`) | `α ≥ 0` | **no blowup** — the repaired truncated model is trivially globally regular (`Cascade/TruncatedRegularity.lean`). The old `e = 0` blowup row was an artifact of the vacuous predicate |

So there is **no** `B ∧ O` contrast inside the truncated model family: it is regular at every degree
`e ≥ 0`. Any genuine blowup needs the **untruncated** lattice.

---

## Done — the layer-model trap (`Cascade/LayerTrap.lean`)

A **documented negative** that closes the one-wavevector-per-octave direction. `Cascade/Layers.lean`
realises AB eq. (3.3) but says nothing about its dynamics; the question was whether that model can
be driven to blowup. This file shows it has a **growth-free equilibrium**, so nothing about the
model forces blowup and the whole question is a construction problem (AB's own), not a dynamical
one.

```lean
theorem layerRHS_eq_zero_of_transverse (e0 : Fin 2 → ℝ) (lam w : ℕ → ℝ) (Θ Ω : ℕ → ℝ)
    (ζ : ℕ → Fin 2 → ℝ) (he0 : e0 0 = 0) (hζ : ∀ q, ζ q 0 = 0) (q : ℕ) :
    layerZetaRHS 0 w Ω ζ q = 0 ∧
    layerThetaRHS e0 lam w Θ Ω ζ q = 0 ∧
    layerOmegaRHS lam Θ ζ q = 0
```

**The configuration:** the common rotation is off (`α' = 0`) and component `0` of the background
direction `e0` *and* of every wavevector `ζ_q` vanishes. In the library's convention component `0`
is the gravity-direction component — the one `abVortCoeff (lam q) (ζ q) = lam q * ζ q 0` reads off —
so this is the configuration in which the buoyancy coupling is identically zero. Then:

* `Gprefix_apply_zero` — the accumulated gradient has vanishing component `0` too, since it is built
  from `−e0` and the unit vectors `e_j`, all of which have vanishing component `0`;
* `abVortCoeff_eq_zero` — the buoyancy coupling is literally the vanishing component;
* `abTempCoeff_eq_zero` — `rotJ *ᵥ ζ_q = ![-(ζ_q)₁, 0]` is dotted against `G_{<q} = ![0, ·]`, giving `0`;
* `layerZetaRHS_eq_zero` — at `α' = 0` each rank-one term of `D_{<q}` is `(J e_j) ⊗ e_j` with
  **zero second row** (`Dprefix_zero_row_one`), so `D_{<q}ᵀ` has a zero second *column* and
  `D_{<q}ᵀ ζ_q = 0`.

So all three right-hand sides vanish at every octave: the wavevector field is stationary, hence the
hypothesis `∀ q, (ζ_q)₀ = 0` is **self-perpetuating**, and no amplitude grows. Non-vacuity is
machine-checked: `ζ_q = ![0,1]` is nonzero, and `Gprefix ![0,1] … 2 = ![0,1]`.

### The caveat, made quantitative

The equilibrium genuinely needs `α' = 0`, and the file proves exactly how much:

```lean
theorem layerZetaRHS_apply_zero (α' : ℝ) (w Ω : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ)
    (hζ : ∀ q, ζ q 0 = 0) (q : ℕ) :
    layerZetaRHS α' w Ω ζ q 0 = -(α' * ζ q 1)
```

So the whole `α' = 0` part of `D_{<q}` contributes *nothing* to `(D_{<q})ᵀζ_q` for these
wavevectors, and the component-`0` drift is exactly `−α' (ζ_q)₁`. With `α' ≠ 0` and `(ζ_q)₁ ≠ 0`
the wavevectors rotate out of the degenerate plane and the trap opens. Hence the honest statement is
**not** "the layer model has a growth-free configuration" but "**with the common rotation switched
off, this configuration is a nontrivial equilibrium in which nothing grows**".

### Why this closes the direction

A numeric scout (`/tmp/scout_margin.py`, not in the repo) had suggested the viability of AB's
greedy construction might be carried by the geometric growth of the octave weights `λ_q`, with the
growth margin recovering after each collapse. This theorem kills that reading: the recovery seen
there depended on the wavevector directions, and there is an admissible, **stationary** choice for
which the margin is identically zero. So no invariant forces growth, the model does not generically
blow up, and what remains is the construction of good data — which is AB's theorem, not a general
theory waiting to be found.

---

## Open — where a dyadic blowup could still live

The **frozen truncated model is now closed**: no finite-time blowup for any `κ`, forced or unforced,
in energy or enstrophy (Stages O, O′, B, B′), and in fact for every degree `e ≥ 0` — the repaired
predicate makes it trivially globally regular (`Cascade/TruncatedRegularity.lean`). Untruncated it is
cited-only (Cheskidov). So the remaining directions all *leave* that model.

- **Blowup below the threshold (the positive half).** **WITHDRAWN at `e = 0`.** The former
  `no_global_solution_degree_zero` and its two auxiliary files have been deleted: they rested on the
  old, vacuous truncated predicate, and with the repaired predicate the truncated chain has no
  finite-time blowup at any degree, so the statement is false. What remains is *fractional* `e` on
  the **untruncated** lattice: the blowup should hold throughout `0 < α < 1/3` (Cheskidov's theorem,
  untruncated), and reaching that interval needs real exponents (`Real.rpow`) since `dyadicWeight` is
  `zpow`. (`e = 1` needs no separate treatment: our barrier is marginal there, but regularity at
  `α = 1/2` is Cheskidov's.) `inverted_holder` covers every integer `e ≤ 0` but only as an abstract
  inequality. *Fidelity:* the dial is **not** free in the Boussinesq model — that is exactly Stage R′
  — so this is a question about the dyadic model *family*, with the Boussinesq branch located at
  `e = 2`.
- **Untruncated formalization of the Stage-R model.** The truncation is the **safe** direction, not
  the dangerous one: it caps the weights (`weighted_sq_le_energy`: on a finite range every weighted
  norm is dominated by the energy, so no truncated norm can outrun the energy). The linear-in-`T`
  form of the Stage-O′ bound is an artifact of a Grönwall route that never used the finite-range norm
  cap, not evidence that truncation creates blowup; an earlier version of this line said the opposite
  and was wrong. The untruncated ladder is where the unbounded weights `4^k` can carry a diverging
  enstrophy while the energy decays, so it is the direction that could be *less* regular, not more.
  Needs an infinite-sum layer the library lacks entirely: a phase space (`Summable (fun k => u_k²)`,
  `Summable (fun k => 4^k u_k²)`), flux telescoping to `±∞` (energy conservation as "the boundary
  flux vanishes"), `tsum` versions of the estimates, and a solution concept on the infinite lattice.
  Value: removes the citation on the headline claim.
- **Stage H's layer model as an ODE system.** **CLOSED as a documented negative** — see
  `Cascade/LayerTrap.lean` above. The model has an admissible, nontrivial, *stationary* equilibrium
  in which every right-hand side vanishes, so no invariant forces growth and the model does not
  generically blow up. What is left is the construction of good data, which is AB's own theorem.
  (Untouched by Stage B, which is about the Stage-R model.)
- **The `α = 2/5` sharp-estimate statement.** Formalize that the dissipation-dominance estimate is
  sharp at the exponent whose nonlinear estimates match 3D Navier–Stokes — a machine-checked version
  of "why this dyadic model is easier than 3D NS". Cheap, and the honest capstone to the fidelity
  story. **Corrected:** `α = 2/5` is *not* in the open gap — Barbato–Morandin–Romito prove global
  regularity there (Theorem A, arXiv:1007.3401), so the *verdict* at this exponent is a known
  theorem (theirs, not ours) and what remains ours is only the estimate.
- **Stage B for the AB construction proper.** Unchanged and untouched: AB build the force together
  with the solution, and their blowup is for the PDE, not a shell model.

---

## Build

```bash
cd /Users/ronaldrogers/Code/NavierStokesAndEuler
export ELAN_HOME="$PWD/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR="$PWD/.cache/mathlib"
lake build Cascade        # this library (includes the relocated Bernstein chain)
lake build Criticality    # sibling skeleton (now depends on Cascade for Pillar A)
lake env lean Cascade/<file>.lean   # fast single-file check while iterating
```

`lake build Cascade` and `lake build Criticality` both exit 0. `#print axioms` is appended at
the bottom of each file.

---

## Reference material

- Mastodon thread — all links quoted in `VISION.md` (Tao ×2, Tao→Nalini Joshi, Palasek,
  Buckmaster). Tao's reply to Nalini Joshi names the key ODE:
  <https://mathstodon.xyz/@tao/117234137753542696> → the second display on page 4 of
  `boussinesq.pdf`, i.e. eq. (3.2) "Exact affine wave".
- **Alpöge–Buckmaster**, *Blowup for the Boussinesq equations with smooth forcing* —
  `cims.nyu.edu/~tristanb/` (`boussinesq.pdf`). Lemma 3.1 / eq. (3.2) is the Stage A target;
  §3.2 eq. (3.3) gives the background coefficients `G_{<q}`, `D_{<q}`, `A_j = −λ_j|ζ_j|Θ_j`.
- **Mailybaev**, *Bifurcations of blowup in inviscid shell models of convective turbulence*,
  [arXiv:1210.2494](https://ar5iv.labs.arxiv.org/html/1210.2494) — the source of the
  four-parameter convection shell model (eqs (3)–(4)); the paragraph following its eqs (5)–(6)
  states the entropy
  conservation and the absence of a total-energy invariant.
- `../LEAN_PDE_PRIOR_ART.md` and `../research_lean4_pde_formalizations.md` — prior-art surveys.
- **`tristanbuckmaster/fluid_lean`** — reference only, do not port (see below).

---

## Gotchas

1. **Big-operator binder.** This Mathlib pin rejects `∑ k in s, …`
   (`unexpected token 'in'; expected ','`). Use `∑ k ∈ s, …`, which elaborates to the same
   `Finset.sum s (fun k => …)`.
2. **`b = 1` is the fixed Boussinesq exponent** (`boussinesqB`), fixed in
   `BoussinesqScaling.lean` before any solution statement. For a nontrivial scaling
   (`λ ≠ 1`, i.e. `s ≠ 0`), `λ^{b−1} = 1` only at `b = 1`.
3. **`[local irreducible]` does not propagate across imports.** Files touching `𝓕`/`𝓕⁻` or
   `Real.rpow` must re-declare `attribute [local irreducible] Real.rpow`,
   `SchwartzMap.fourierTransformCLM`, `MeasureTheory.Lp.fourierTransformₗᵢ` locally.
4. **Write the measure explicitly** (`‖f.toLp 2 volume‖`) when `𝓕` meets `toLp`; the default
   `volume_tac` can fail mid-elaboration.
5. **`Real.sqrt x` is not defeq to `x ^ (1/2)`** — use `Real.sqrt_eq_rpow`.
6. **Use `ring_nf`, not `ring`, on the telescoping pairing goals.** `ring` closes them but
   emits a cosmetic `info: Try this: ring_nf …` line; `ring_nf` is silent and yields the
   same kernel-checked term.
7. **Plancherel needs `[InnerProductSpace ℂ F]`.** `SchwartzMap.norm_fourier_toL2_eq`,
   `MeasureTheory.Lp.norm_fourier_eq` and the L² Fourier isometry all assume a complex
   *inner-product* space; there is no Plancherel for `[NormedSpace ℂ F]` alone.
8. **Library plumbing.** `Cascade` is registered in `lakefile.toml` as
   `[[lean_lib]] name = "Cascade" globs = ["Cascade", "Cascade.+"]` with root `Cascade.lean`.
   New submodules must be imported from `Cascade.lean` to be covered by `lake build Cascade`.
9. **`fluid_lean`** (`tristanbuckmaster/fluid_lean`) is reference only: ~1,400 modules (mostly
   machine-generated certificates), Lean `v4.32.2`, ~150 GB build, unmaintained, statement
   module recorded as `review: unreviewed`. Do not port.
10. **The subscript-minus glyph `₋` is not a legal identifier character** in this pin; the
    background ladders are spelled `u_minus` / `θ_minus` in code (the prose writes `u₋`, `θ₋`).
    Also, this pin has no `Function.update_noteq`; use
    `Function.update_of_ne (show n - 1 ≠ n by omega)`.
11. **Sign hypotheses are load-bearing.** The Stage-O velocity rate bound needs `0 ≤ κ` (false
    for `κ < 0`), and the Grönwall no-blowup statements need continuity (`ContinuousOn`/
    `ContinuousAt`); the literal `[0,T)`-derivative forms are false. Don't drop them when
    restating.
12. **`HasDerivAt.sum` returns a sum in the function space**, not the pointwise sum, and plain
    function types lack the `FunLike` instance the generic `sum_apply` needs at this pin;
    `Cascade/NoBlowup.lean` provides `finset_sum_apply` for this. `antitone_of_hasDerivAt_nonpos`
    lives in `Mathlib.Analysis.Calculus.Deriv.MeanValue` (not re-exported by
    `Mathlib.Analysis.Calculus.MeanValue`).
13. **`‖·‖` on `Fin 2 → ℝ` is the *sup* norm**, not the Euclidean norm (`Pi.norm_def`), so
    `‖rotR α *ᵥ ζ₀‖ = ‖ζ₀‖` is **false** — a rotation does not preserve the sup norm
    (`Cascade/Phase.lean`'s `rotR_norm_preserving_supNorm_counterexample`: `ζ₀ = ![1,1]`,
    `α = π/4`). Use an explicit Euclidean length (`Cascade.Phase.l2norm`, AB's `|ζ|`).
14. **`Matrix (Fin 2) (Fin 2) ℝ` has no topological/norm instance** in this pin (deliberately:
    matrix multiplication is not sup-norm submultiplicative), so `HasDerivAt` is ill-typed at
    matrix type. Take derivatives componentwise (`Cascade.Phase.phase_steering_component`).
15. **`x + 0 = x` on `ℝ` is *not* a definitional equality** — it is Mathlib's `add_zero`, proved
    through the quotient construction. So a "force off recovers the model" lemma whose definition
    is `… + f k` closes by `simp [forcedVelocityRHS]`, and bare `rfl` **fails** with "Not a
    definitional equality". The recovery is still definitional in the sense that matters (only the
    forced-RHS definition unfolds: no `funext`, no rewriting of the frozen couplings), but don't
    claim `rfl` and don't bend the definition to manufacture it.
16. **`zpow_right_injective₀` exists at this pin** (`0 < a`, `a ≠ 1`): it gives
    `a^m = a^n → m = n` for `m n : ℤ`, hence `Function.Injective dyadicWeight` in one line. No
    detour through `Real.log` is needed.
17. **Square away half-integer exponents when you can.** `D_e ≥ H^{1+e/2}/E^{e/2}` ⟺
    `H^{2+e} ≤ D_e²·E^e`, and with `e : ℤ` every exponent there is an integer — so an interpolation
    can often be *stated* without `Real.rpow` at all. The `rpow`-free route in
    `Cascade/DissipationThreshold.lean` (`weighted_cauchy_schwarz` + `weightedEnstrophy_sq_le` →
    `dissipation_interp_sq`) is short. (`rpow` is still fine *inside* a proof — but see gotcha 18
    for the elaboration trap that makes it look broken.) Related trap on any hand-verified
    inequality: the **quadratic** domination `D_e ≥ H²/E` (homogeneity 2) and the **interpolated**
    `D_e ≥ H^{1+e/2}/E^{e/2}` (homogeneity `1+e/2`) are *different statements* that coincide only at
    `e = 2`. Conflating them produces "counterexamples" to claims that are true — at `u = (0,0,3,0)`,
    `e = 1` one has `D_1·E = 5184 = H^{3/2}·√E` (equality: the interpolated bound holds) *and*
    `D_1·E = 5184 < 20736 = H²` (the quadratic one fails). Both facts, no contradiction.
18. **`Real.rpow` elaboration trap.** `(2 : ℝ)` and `((2 : ℕ) : ℝ)` are **not** interchangeable for
    `rw` pattern matching against `Real.rpow_mul` / `Real.rpow_natCast`, and `(1:ℕ):ℝ / 3` parses as
    `(1:ℕ) : (ℝ / 3)` — the ascription swallows the division. The symptoms are spurious "pattern not
    found" and `HDiv Type ℕ Type` errors, which read as *mathematics* failures when the lemma is
    fine. Always write `((n:ℕ):ℝ)` when the exponent arrived via `rpow_natCast`, and parenthesise
    `(((1:ℕ):ℝ)/3)`. This cost one agent its entire budget on `inverted_holder`.
19. **Keep the *truncated* geometric sum.** In the inverted-Hölder chain the factor must stay
    `Σ_{k<N} 2^{−εk}`; replacing it by the infinite-sum bound `2^ε/(2^ε−1)` inside `S³ ≤ G·Q²`
    makes the inequality **false**. The infinite bound is valid only for the separate step
    `A²·G ≤ 1` (where it is an upper bound used in the right direction). Also,
    `Σ_{k<N}2^{−2εk} ≠ (Σ_{k<N}2^{−εk})²`.
20. **Useful Hölder at this pin.** `Real.inner_le_Lp_mul_Lq_of_nonneg` is a *real*-valued finite-sum
    Hölder (with `Real.HolderConjugate 3 (3/2)` discharged by `norm_num`) — no `ℝ≥0` conversion is
    needed, unlike the `ℝ≥0`-valued variants.
21. **Process: one writer per file.** `lake build Cascade` compiles *every* file under `Cascade/`
    via the `Cascade.+` glob, so an agent's unfinished file (or one containing `sorry`) turns the
    aggregate build red even though nothing imports it. And two agents editing the *same* file
    concurrently produce a merge that happens to compile only by luck — check `list_agents` for a
    `running` entry before launching a second agent, and treat a "finished" notice as insufficient
    proof that the previous turn is over.

---

## The one divergence we can actually certify: the flat self-similar solution (2026-09-15)

`Cascade/SelfSimilarSolution.lean`.  The inviscid, unforced shell system (`ν = κ = 0`) on the whole
lattice `k : ℤ` has the exact self-similar solution

`u_k(t) = (1/3) · 2^{−k} · (T − t)^{−1}`,

verified in Lean (`selfSimilar_hasDerivAt`) against the repo's **own** `velocityRHSDegreeE` rather
than a hand-restated right-hand side, for every `k : ℤ` and every degree `e` (the inviscid transfer
does not see `e`).  Its vorticity is `a_k = 2^k u_k = (1/3)(T − t)^{−1}`, **independent of `k`**
(`selfSimilar_vorticity`), so the profile is flat, the local exponent is `0` at every shell and every
time, and this explosion carries **exactly zero jitter** — which is the point of the figure
`Cascade/explosion.svg`.  The level is unbounded as `t → T⁻`, in the elementary form
`selfSimilar_level_unbounded : ∀ M, ∃ t < T, M < (1/3)(T − t)^{−1}`.  The identity was also checked
independently in exact rational arithmetic before the Lean was written.

**What this is not** — stated plainly, because this project has already crossed this line once:

* **Not a blow-up of this repo's model.**  The truncated system provably cannot blow up
  (`Cascade/TruncatedRegularity.lean`); this is the *untruncated inviscid* system, a different
  object.  The two statements are not in tension because they are about different systems.
* **Not a blow-up from finite-enstrophy data.**  Because the profile is flat,
  `Σ_{k∈ℤ} a_k² = Σ_{k∈ℤ} (1/3)²(T−t)^{−2}` diverges at **every** `t < T`, not merely at `T`.  The
  solution has infinite enstrophy from the outset; what diverges is the **level**.
* **Not new mathematics.**  Explicit self-similar solutions of the inviscid dyadic model are standard
  in the literature; the contribution is machine verification in this repo's notation, and the
  docstring attributes the specific form to no paper.

The honest description: the first *verified* divergence in this project, and it is a self-similarity
statement about a system the project does not otherwise study.  Its content is the mirror of the
withdrawn claim — the withdrawn one asserted a blow-up of the truncated model and was false; this one
is true, and is about a different system, with the limits written on its face.

---

## Prior art: the obstruction remark, and what the literature already has (2026-09-15)

The Palasek/Tao exchange that started this project is dated **2026-09-08** (`Cascade/VISION.md` has
the right date; earlier notes here said September 2025 — wrong). Raw notes with all quotes and
links: `CASCADE_PALASEK_PRIOR_ART.md` (agent write-up, not independently re-verified except where
marked ✓ below).

**✓ Verified first-hand here (fetched from the source).**

* **Cheskidov**, *Blow-up in finite time for the dyadic model of the Navier–Stokes equations*,
  Trans. AMS **360** (2008) 5101–5120, arXiv:math/0601074. Abstract: local regularity `α > 1/3`,
  global regularity `α ≥ 1/2`, finite-time blow-up `α < 1/3`, and "the model with `α = 1/3` enjoys
  the same estimates on the nonlinear term as the 4D Navier–Stokes equations".
* **Barbato–Morandin–Romito**, *Smooth solutions for the dyadic model*, Nonlinearity **24** (2011)
  3083–3097, arXiv:1007.3401, Theorem A: for `β ∈ (2, 5/2]` every nonnegative `ℓ²` datum has a
  unique smooth solution. Their normalisation is dissipation `λ_n²` with nonlinearity exponent `β`,
  so `α = 1/β` and this is `α ∈ [2/5, 1/2)`. The paper states that `β ∈ (2, 5/2]` "is essentially
  the one corresponding, within the simplification of the model, to the three dimensional
  Navier–Stokes equations".
* **Consequence**, stated without decoration because it is the punchline of the fidelity question:
  global regularity holds for **all `α ≥ 2/5`**, the open gap is `α ∈ [1/3, 2/5)`, and *the dyadic
  range corresponding to 3D Navier–Stokes is globally regular*. The literature has this; it is not
  ours to claim. The toy does not merely fail to blow up at the physical dimension — it provably
  cannot, and that was known before this project began.

**✓ Also verified first-hand: the intermittency framework itself** (Dai, *Dyadic models with
intermittency dependence for the Hall MHD*, arXiv:2006.15094, §2 and §3.1).

* **How `δ` is defined.** "we gave a mathematical definition of intermittency dimension `δ` of a
  flow through saturation level of Bernstein's inequality. For 3D flow, `δ` belongs to `[0,3]`"
  (§2), with the optimal relation `‖v_j‖_{L^∞} ∼ λ_j^{(3−δ)/2}‖v_j‖_{L²}` at each scale (eq. (2.4)).
  So `δ` is read off as the *slope* of a log–log asymptote, measured down from the Bernstein
  ceiling — see `Cascade/intermittency_asymptote.svg`.
* **The two ends.** "Kolmogorov's theory corresponds to the extreme intermittency regime `δ = 3`, in
  which turbulent eddies fill the space" — so `δ = n` is the *flattest* line (no concentration) and
  `δ = 0` is the steepest, i.e. the ceiling itself. And "numerical simulations and experimental
  studies show that `δ ≈ 2.7`": real turbulence is only mildly intermittent.
* **The model.** Eq. (3.7): `d/dt a_j + νλ_j²a_j − α(λ_{j−1}^{(5−δ)/2}a_{j−1}² − …) = 0` with
  `a_j = ‖u_j‖_{L²}`. The amplitude is **dimension-free**; the dimension sits in the *nonlinearity
  exponent* `(5−δ)/2`, against dissipation `λ_j²` (the honest Laplacian). `α=1, β=0` is
  Katz–Pavlović, `α=0, β=1` is Obukhov.
* **The threshold, from that equation.** Nonlinearity beats dissipation iff `(5−δ)/2 > 2` iff
  `δ < 1`; the same arithmetic in `n` dimensions gives the critical case `δ = n − 2`. Dai's abstract
  confirms the shape — global solutions when `δ` is above the threshold, finite-time blow-up when
  below, with the blow-up regime flagged **"(unphysical)"**.
* **The crossover at dimension 5, and why it is not a theorem about Navier–Stokes.** The obstruction
  (dissipation wins) holds iff `δ > n − 2`. At the observed `δ ≈ 2.7` that gives obstruction for
  `n ≤ 4` and none from `n ≥ 5` — **Palasek's threshold** — for every `δ ∈ (2,3]`. Boundary care: at
  `δ = 3, n = 5` the exponent is exactly `2`, so the honest statement is "dissipation does not win
  from dimension 5", not "nonlinearity strictly wins". And `2.7` is a *measured* constant, so this is
  two heuristics agreeing at a measurement, not a theorem.
  `Cascade/IntermittencyThreshold.lean` formalizes the arithmetic with `2 < δ ≤ 3` as an explicit
  hypothesis, so the empirical input stays visible.

**Reported by the prior-art check, not independently re-verified here.** Pointers only.

* Palasek's remark itself — Bernstein `N_k^{3/2}` versus depletion `N_k²`, with "in high dimension
  there is no obstruction!", Mastodon 2026-09-08 — appears **nowhere** in written form, including in
  the paper he links in the same post (arXiv:2605.13827), whose full text reportedly contains no
  "Bernstein" and no high-dimension discussion. The rigorous obstruction (the force is necessary)
  that *is* written up there is attributed to **Looi**, whose proof is public only as seminar
  abstracts (Princeton, Caltech, 2026).
* The `d = 5` threshold is documented via a different route — Tao's blog (2014) and the
  Cheskidov–Dai–Friedlander survey (JMFM **25** (2023), arXiv:2209.10203): "5D is a common threshold
  for models exhibiting a blow-up" — *not* via Palasek's Bernstein-amplitude comparison.
* **Dimension-dependent dyadic models do exist**, but the dimension enters as the *nonlinearity
  exponent*, not as an intrinsic per-shell `N_k^{d/2}` amplitude factor — verified above for `n = 3`.
  The `n`-dimensional form `θ = (2+n−δ)/2` and the equivalence statements below are reported, not
  verified here: Cheskidov–Dai, Proc. Roy. Soc. Edinb. A **149** (2019) 429–446, arXiv:1510.00379
  (source of the definition of intermittency dimension); CDS survey arXiv:2209.10203 eq. (2.7); Dai
  arXiv:2006.15094 and arXiv:2108.12913.
* The dimension ↔ dissipation-degree trade-off is therefore in the literature as a *frequency
  rescaling*: CSDF "`(3.6)` is equivalent to `(3.7)` with `θ = 1/γ`", and Dai's `α = 1/θ` via
  `λ_j = λ̄_j^α`, i.e. generalised diffusion `(−Δ)^α`. The additive `2 ↦ 2 − d` bookkeeping is
  trivial algebra and is not recorded in that form.
* Nobody has publicly done Tao's suggested Boussinesq-dyadic exercise; his reply has no public
  descendants.

**What this means for the project.** The correct way to make the spatial dimension intrinsic to a
dyadic model is already known — put it in the nonlinearity exponent, via the intermittency
dimension — and that model is equivalent, by frequency rescaling, to a change of the dissipation
degree. So the "degree dial" this project spent its time on and the dimension are *the same knob* in
the literature (`θ = 1/γ`, `α = 1/θ`). That is the final explanation of why no repair of the model
could produce a new mechanism; it closes the fidelity question. `Cascade/DimensionBlind.lean` shows
the one-mode model cannot carry `d` intrinsically, and the literature shows that the model which
does carry it is the degree dial again.
