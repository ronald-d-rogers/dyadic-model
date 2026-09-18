# Plan: dyadic cascade models

The target specification. Current state lives in `PROGRESS.md`; motivation in `VISION.md`.

Each stage is a self-contained family of Lean theorems over a **fixed** model; the model
is frozen before the theorems about its solutions are stated (see the fidelity rules in
`VISION.md`).

---

## Stage S — the one-species shell model (done)

`Cascade/ShellModel.lean` — amplitudes `u_k` per octave,

```
du_k/dt = C_k − ν · 2^{2k} · u_k
```

with a general coupling `C`.

- `shellRHS` — the right-hand side.
- `shell_energy_identity` — energy-conserving coupling ⇒ `Σ u_k (du_k/dt) = −ν Σ 2^{2k} u_k²`.
- `transfer_le_dissipation` — `N^{3/2} ≤ N²` for `N ≥ 1`: the scalar half of Palasek's
  obstruction, with `3/2` the `d = 3` Bernstein exponent.

---

## Stage R — the dyadic Boussinesq model

Two ladders `(θ_k)` and `(u_k)`, coupled by buoyancy `κ θ_k`.

- `dyadicBoussinesqRHS` — the ODE.
- `scaling_covariant` — covariance under the Boussinesq scaling

  ```
  u_λ(x,t) = λ^b · u(λx, λ^{b+1}t),   θ_λ(x,t) = λ^{2b+1} · θ(λx, λ^{b+1}t),   p_λ = λ^{2b} p
  ```

  a one-parameter family. The standard 2D Boussinesq choice is `b = 1`
  (`u_λ = λ u(λx, λ²t)`, `θ_λ = λ³ θ(λx, λ²t)`, `p_λ = λ² p`), under which the momentum
  equation is homogeneous of degree `2b+1 = 3` and the temperature equation of degree
  `3b+2 = 5`. **Fix `b` here, before any blowup statement.**
- `dyadic_energy_identity` — the two-species energy balance.

---

## Stage A — the lacunary ansatz and the amplitude ODE

Impose the ansatz: at generation `n` the active octave is `N_n = 2^n` with amplitudes
`(a_n, b_n)`. Derive the amplitude-frequency ODE — Tao's "remarkably simple ODE" — and
state it as a theorem. This is the technical heart of the library.

---

## Stage B — forced blowup

The dyadic analogue of the Alpöge–Buckmaster construction: an iterative (or recursive)
addition of octaves, with the invariants proved by induction, concluding finite-time
blowup.

---

## Stage O — unforced obstruction

The dyadic analogue of Palasek's obstruction: without the force, dissipation beats the
transfer and the cascade cannot self-sustain.

---

## Capstone

**B ∧ O**: the model exhibits the forced vs. unforced asymmetry. That is the formal
content of the Tao/Palasek exchange, *in the model*.

---

## Explicitly out of scope

- The PDE. Nothing here is a statement about Navier–Stokes or Boussinesq.
- Porting `fluid_lean` (see `PROGRESS.md` for why: ~1,400 modules, mostly machine-generated
  certificates, Lean v4.32.2, ~150 GB build, unmaintained, statement `unreviewed`).
