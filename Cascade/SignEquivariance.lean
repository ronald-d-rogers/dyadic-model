import Cascade.SignReversal
import Cascade.SelfSimilarSolution

/-!
# Sign flip is time reversal: the equivariance structure of the dyadic model

## Why this file exists

`Cascade/SignReversal.lean` settles the **static** sign question at the critical degree `e = 1`: no
fixed sign pattern of the amplitudes can beat the all-positive profile
(`budgetSum_le_abs`, `budgetSum_signPattern_le`), and a single interior flip changes the enstrophy
budget by exactly `−24 · 2^{3(j−1)} · u_{j−1}² · u_j`.  That theorem is about *one* sign pattern
held fixed while the budget identity is evaluated.

It deliberately says nothing about **sign flips that vary in time**.  A trajectory may flip the
sign of a shell at some time and flip it back later, and such a trajectory is not obtained by
applying a single static pattern to a solution.  The natural worry is that this is the gap through
which enstrophy could grow *dynamically* even though no static pattern helps.  This file closes that
worry in the only way available: it identifies the exact algebraic reason the two situations
differ, namely a **time-reversal symmetry**.

The content is a three-way separation of the right-hand side of the velocity equation,

`u_k' = boussinesqTransferU A B u k + κ θ_k − ν · 2^{e k} u_k`,

into a quadratic transfer, a buoyancy term, and a viscous term, and the observation that

* the **transfer** is *even* in `u` (every monomial is a square or a product of two distinct
  amplitudes), and the **buoyancy** term does not read `u` at all;
* the **viscous** term `−ν 2^{e k} u_k` is *odd*.

Consequently, with `ν = 0` the whole right-hand side is even in `u`
(`velocityRHSDegreeE_neg_inviscid`), so the map `(t, u) ↦ (−t, −u)` is a symmetry of the inviscid
unforced model (`inviscid_timeReversal`).  **A global sign flip is a time reversal.**  In
particular the inviscid dynamics has no arrow of time at the level of this symmetry, so a sign flip
cannot, by itself, manufacture growth.  The viscous term breaks the symmetry and does so by
*reversing its own sign*: the reflected trajectory solves the equation with viscosity `−ν`
(`viscous_timeReversal_neg`), and the defect is exactly twice the viscous term
(`velocityRHSDegreeE_neg_sub`).  Viscosity is the obstruction, and it is an odd one.

So the static theorem of `SignReversal.lean` and the dynamical question are **genuinely different**,
not connected by an oversight: static patterns act on a time-symmetric inviscid transfer, whereas
time-varying flips are a *control / steering* problem on a system whose time-symmetry is broken only
by dissipation.  This file does not solve that control problem; it certifies its boundary.

## Scope (read this before citing the file)

* This is a statement about the **sign / time-reversal structure** of the dyadic shell model only.
* It is **not** a blowup result and it says **nothing** about Navier–Stokes.
* It does **not** extend the `e = 1` budget theorem of `SignReversal.lean`; it *delimits* it, by
  showing that the static theorem has no dynamical analogue for this structural reason.

Everything is stated against the repo's own `velocityRHSDegreeE`, whose exact shape is
`velocityRHSDegreeE ν κ A B e u θ k = boussinesqTransferU A B u k + κ θ_k − ν · 2^{e k} u_k`.

## Contents

1. `boussinesqTransferU_neg` — the quadratic transfer is even in the velocity.
2. `buoyancyTermDegreeE`, `viscousTermDegreeE`, `velocityRHSDegreeE_decomp` — the three-way
   decomposition, making "independent of `u`" / "odd in `u`" syntactic.
3. `viscousTermDegreeE_neg` — the viscous term is odd.
4. `velocityRHSDegreeE_neg_inviscid` — with `ν = 0` the right-hand side is even in `u`; no
   condition on `κ` is needed (`buoyancy` is even for free).
5. `velocityRHSDegreeE_neg_sub`, `velocityRHSDegreeE_neg_sub_eq` — the exact viscous defect.
6. `inviscid_timeReversal_at`, `inviscid_timeReversal` — **the time-reversal theorem**.
7. `velocityRHSDegreeE_neg_negVisc`, `viscous_timeReversal_neg` — viscosity flips sign.
8. `viscous_reflection_rhs_ne` — viscosity breaks the symmetry off the zero set.
9. Non-vacuity: numerical witnesses and a reflected self-similar solution.
-/

noncomputable section

set_option linter.unusedVariables false

namespace Cascade

/-! ## 1. The quadratic transfer is even in the velocity -/

/-- **The quadratic transfer is even under a global flip of the velocity**, for every coupling
`A`, `B`.  Each of the four monomials of `boussinesqTransferU A B u k` is either a square
(`(u_{k−1})²`, `(u_{k+1})²`) or a product of two *distinct* amplitudes (`u_k u_{k−1}`,
`u_k u_{k+1}`); both forms are invariant under `u ↦ −u`.  This is the whole reason the transfer
cannot see the overall sign. -/
theorem boussinesqTransferU_neg (A B : ℝ) (u : ℤ → ℝ) (k : ℤ) :
    boussinesqTransferU A B (fun j => -u j) k = boussinesqTransferU A B u k := by
  simp only [boussinesqTransferU]
  ring

/-! ## 2. The three-way separation of the right-hand side -/

/-- **The buoyancy term** `κ θ_k` of the velocity equation.  It is written with no velocity
argument: it is *independent of `u`*, hence trivially even under `u ↦ −u`. -/
def buoyancyTermDegreeE (κ : ℝ) (θ : ℤ → ℝ) (k : ℤ) : ℝ := κ * θ k

/-- **The viscous term** `−ν · 2^{e k} · u_k` of the velocity equation at dissipation degree `e`.
Unlike the transfer and the buoyancy, it *does* read `u`, and linearly, hence it is odd. -/
def viscousTermDegreeE (ν : ℝ) (e : ℤ) (u : ℤ → ℝ) (k : ℤ) : ℝ :=
  -ν * dyadicWeight (e * k) * u k

/-- **The exact decomposition of `velocityRHSDegreeE`** into its quadratic transfer, its buoyancy
term and its viscous term.  This is definitional; it is recorded so that the sign discussion below
is about the three named pieces rather than about the composite. -/
theorem velocityRHSDegreeE_decomp (ν κ A B : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (k : ℤ) :
    velocityRHSDegreeE ν κ A B e u θ k
      = boussinesqTransferU A B u k + buoyancyTermDegreeE κ θ k
        + viscousTermDegreeE ν e u k := by
  simp only [velocityRHSDegreeE, buoyancyTermDegreeE, viscousTermDegreeE]
  ring

/-- **The viscous term is odd in the velocity**: flipping `u` flips its sign.  This is the exact
opposite of `boussinesqTransferU_neg`. -/
theorem viscousTermDegreeE_neg (ν : ℝ) (e : ℤ) (u : ℤ → ℝ) (k : ℤ) :
    viscousTermDegreeE ν e (fun j => -u j) k = -viscousTermDegreeE ν e u k := by
  simp only [viscousTermDegreeE]
  ring

/-! ## 3. Evenness of the inviscid right-hand side -/

/-- **The inviscid right-hand side is even in the velocity.**  At `ν = 0` the whole
`velocityRHSDegreeE 0 κ A B e ·` is even under `u ↦ −u`, **for every** buoyancy coefficient `κ`,
every coupling `A`, `B`, every degree `e`, and every temperature profile `θ`.

The three pieces contribute as follows: the transfer is even (`boussinesqTransferU_neg`), the
buoyancy term `κ θ_k` does not read `u` so it is unchanged, and the viscous term has vanished.
So — answering the prompt's aside — **`κ = 0` is not needed**: evenness of the inviscid velocity
field holds for every `κ`.  What is needed is exactly `ν = 0`. -/
theorem velocityRHSDegreeE_neg_inviscid (κ A B : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (k : ℤ) :
    velocityRHSDegreeE 0 κ A B e (fun j => -u j) θ k = velocityRHSDegreeE 0 κ A B e u θ k := by
  simp only [velocityRHSDegreeE_decomp, boussinesqTransferU_neg, viscousTermDegreeE]
  ring

/-- **The literal `ν = κ = 0` form** requested for the inviscid unforced model
`velocityRHSDegreeE 0 0 A B e`: the right-hand side is even in `u`.  A special case of
`velocityRHSDegreeE_neg_inviscid`, included to fix the exact unforced signature. -/
theorem velocityRHSDegreeE_neg_inviscid_unforced (A B : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (k : ℤ) :
    velocityRHSDegreeE 0 0 A B e (fun j => -u j) θ k = velocityRHSDegreeE 0 0 A B e u θ k :=
  velocityRHSDegreeE_neg_inviscid 0 A B e u θ k

/-! ## 4. The exact viscous defect -/

/-- **The exact defect of the sign flip.**  For every `ν`, `κ`, `A`, `B`, `e`, `u`, `θ` and shell
`k`, the right-hand side at `−u` minus the right-hand side at `u` is exactly **twice the viscous
term at `u`**:

`velocityRHSDegreeE ν κ A B e (−u) θ k − velocityRHSDegreeE ν κ A B e u θ k
   = −2 · viscousTermDegreeE ν e u k`.

The transfer cancels by evenness and the buoyancy cancels identically, leaving only the odd viscous
term, which changes sign.  (The prompt's proposed identity is correct; the constant is `2`, not
something else, because `RHS(−u) = T + B + ν 2^{ek} u_k` while `RHS(u) = T + B − ν 2^{ek} u_k`.) -/
theorem velocityRHSDegreeE_neg_sub (ν κ A B : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (k : ℤ) :
    velocityRHSDegreeE ν κ A B e (fun j => -u j) θ k
        - velocityRHSDegreeE ν κ A B e u θ k
      = -2 * viscousTermDegreeE ν e u k := by
  simp only [velocityRHSDegreeE_decomp, boussinesqTransferU_neg, viscousTermDegreeE_neg]
  ring

/-- **The defect in expanded form**: the right-hand side at `−u` exceeds the one at `u` by
`2 ν 2^{e k} u_k`.  This is `velocityRHSDegreeE_neg_sub` with `viscousTermDegreeE` unfolded. -/
theorem velocityRHSDegreeE_neg_sub_eq (ν κ A B : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (k : ℤ) :
    velocityRHSDegreeE ν κ A B e (fun j => -u j) θ k
        - velocityRHSDegreeE ν κ A B e u θ k
      = 2 * ν * dyadicWeight (e * k) * u k := by
  rw [velocityRHSDegreeE_neg_sub]
  simp only [viscousTermDegreeE]
  ring

/-- **Flipping `u` together with `ν` is a symmetry of the right-hand side**:
`RHS_ν(−u) = RHS_{−ν}(u)`.  This is the pointwise core of the reversed-viscosity statement below:
the transfer is even, the buoyancy is `u`-free, and the two odd viscous terms match. -/
theorem velocityRHSDegreeE_neg_negVisc (ν κ A B : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (k : ℤ) :
    velocityRHSDegreeE ν κ A B e (fun j => -u j) θ k
      = velocityRHSDegreeE (-ν) κ A B e u θ k := by
  simp only [velocityRHSDegreeE_decomp, boussinesqTransferU_neg, viscousTermDegreeE]
  ring

/-! ## 5. The time-reversal theorem -/

/-- **The time-reversal theorem, pointwise in `(t, k)`.**  If `u` solves the inviscid velocity
equation at the *reflected* time `−t`,

`d/ds [u_s k]|_{s = −t} = velocityRHSDegreeE 0 κ A B e (u (−t)) θ k`,

then the reflected trajectory `t ↦ (fun k => −u (−t) k)` solves it at time `t`:

`d/dt [−u(−t)_k] = velocityRHSDegreeE 0 κ A B e (−u(−t)) θ k`.

The derivative of `s ↦ −u(−s)_k` is `−(−u'(−t)_k) = u'(−t)_k` (chain rule for `s ↦ −s`), and
evenness (`velocityRHSDegreeE_neg_inviscid`) rewrites the right-hand side from `u(−t)` to `−u(−t)`.
This pointwise form is stated separately so that it can be applied at a single time where a
solution is known to be differentiable. -/
theorem inviscid_timeReversal_at (κ A B : ℝ) (e : ℤ) (u : ℝ → ℤ → ℝ) (θ : ℤ → ℝ)
    (t : ℝ) (k : ℤ)
    (hu : HasDerivAt (fun s : ℝ => u s k)
        (velocityRHSDegreeE 0 κ A B e (u (-t)) θ k) (-t)) :
    HasDerivAt (fun s : ℝ => -u (-s) k)
      (velocityRHSDegreeE 0 κ A B e (fun j => -u (-t) j) θ k) t := by
  -- Chain rule for `s ↦ u (−s) k`: derivative `RHS · (−1) = −RHS`.
  have hcomp : HasDerivAt (fun s : ℝ => u (-s) k)
      (-(velocityRHSDegreeE 0 κ A B e (u (-t)) θ k)) t := by
    simpa [Function.comp_def] using hu.comp t (hasDerivAt_neg t)
  -- Negate: derivative `−(−RHS) = RHS`.
  have hneg : HasDerivAt (fun s : ℝ => -u (-s) k)
      (velocityRHSDegreeE 0 κ A B e (u (-t)) θ k) t := by
    simpa only [Pi.neg_def, neg_neg] using hcomp.neg
  -- Evenness rewrites the right-hand side from `u (−t)` to `−u (−t)`.
  simpa only [velocityRHSDegreeE_neg_inviscid] using hneg

/-- **THE TIME-REVERSAL THEOREM (inviscid, unforced).**  If `t ↦ u t` solves the inviscid velocity
equation shell by shell,

`∀ t k, HasDerivAt (fun s => u s k) (velocityRHSDegreeE 0 κ A B e (u t) θ k) t`,

then so does the reflected trajectory `t ↦ (fun k => −u (−t) k)`:

`∀ t k, HasDerivAt (fun s => −u (−s) k)
          (velocityRHSDegreeE 0 κ A B e (fun j => −u (−t) j) θ k) t`.

In words: **`(t, u) ↦ (−t, −u)` is a symmetry of the inviscid unforced dyadic model, so a global
sign flip is a time reversal.**  No assumption on `κ` is needed (the buoyancy term is `u`-free and
time-independent here); the hypothesis is `ν = 0`. -/
theorem inviscid_timeReversal (κ A B : ℝ) (e : ℤ) (u : ℝ → ℤ → ℝ) (θ : ℤ → ℝ)
    (hu : ∀ t k, HasDerivAt (fun s : ℝ => u s k)
        (velocityRHSDegreeE 0 κ A B e (u t) θ k) t) :
    ∀ t k, HasDerivAt (fun s : ℝ => -u (-s) k)
      (velocityRHSDegreeE 0 κ A B e (fun j => -u (-t) j) θ k) t := by
  intro t k
  exact inviscid_timeReversal_at κ A B e u θ t k (hu (-t) k)

/-- **The reflected trajectory of the inviscid unforced equation**, named so that the
time-reversal theorem reads as a symmetry statement.  `reflect u t k = −u(−t)_k`. -/
def reflect (u : ℝ → ℤ → ℝ) : ℝ → ℤ → ℝ := fun t k => -u (-t) k

/-- **Time reversal is an involution**: reflecting twice returns the original trajectory. -/
theorem reflect_involutive (u : ℝ → ℤ → ℝ) : reflect (reflect u) = u := by
  funext t k
  simp [reflect]

/-- **The time-reversal theorem, restated through `reflect`.**  If `u` solves the inviscid
unforced equation, so does `reflect u`, and the two trajectories are exchanged by reflection. -/
theorem inviscid_timeReversal_reflect (A B : ℝ) (e : ℤ) (u : ℝ → ℤ → ℝ) (θ : ℤ → ℝ)
    (hu : ∀ t k, HasDerivAt (fun s : ℝ => u s k)
        (velocityRHSDegreeE 0 0 A B e (u t) θ k) t) :
    ∀ t k, HasDerivAt (fun s : ℝ => reflect u s k)
      (velocityRHSDegreeE 0 0 A B e (reflect u t) θ k) t := by
  intro t k
  unfold reflect
  simpa using inviscid_timeReversal 0 A B e u θ hu t k

/-! ## 6. Viscosity breaks the symmetry, by flipping its own sign -/

/-- **The reflected trajectory solves the equation with viscosity `−ν`.**  If `t ↦ u t` solves the
viscous velocity equation with viscosity `ν`, then `t ↦ (fun k => −u (−t) k)` solves it with
viscosity `−ν`:

`∀ t k, HasDerivAt (fun s => −u (−s) k)
          (velocityRHSDegreeE (−ν) κ A B e (fun j => −u (−t) j) θ k) t`.

The engine is `velocityRHSDegreeE_neg_negVisc`, the pointwise identity `RHS_ν(−w) = RHS_{−ν}(w)`.
This is the precise sense in which **the odd viscous term is the obstruction**: reflecting the
trajectory reverses the effective viscosity, so `(t, u) ↦ (−t, −u)` is a symmetry of the viscous
model only if `ν = 0`. -/
theorem viscous_timeReversal_neg (ν κ A B : ℝ) (e : ℤ) (u : ℝ → ℤ → ℝ) (θ : ℤ → ℝ)
    (hu : ∀ t k, HasDerivAt (fun s : ℝ => u s k)
        (velocityRHSDegreeE ν κ A B e (u t) θ k) t) :
    ∀ t k, HasDerivAt (fun s : ℝ => -u (-s) k)
      (velocityRHSDegreeE (-ν) κ A B e (fun j => -u (-t) j) θ k) t := by
  intro t k
  have hcomp : HasDerivAt (fun s : ℝ => u (-s) k)
      (-(velocityRHSDegreeE ν κ A B e (u (-t)) θ k)) t := by
    simpa [Function.comp_def] using (hu (-t) k).comp t (hasDerivAt_neg t)
  have hneg : HasDerivAt (fun s : ℝ => -u (-s) k)
      (velocityRHSDegreeE ν κ A B e (u (-t)) θ k) t := by
    simpa only [Pi.neg_def, neg_neg] using hcomp.neg
  -- `RHS_ν(u(−t)) = RHS_{−ν}(−u(−t))` by flipping both the velocity and the viscosity.
  have key := velocityRHSDegreeE_neg_negVisc (-ν) κ A B e (u (-t)) θ k
  have hkey : velocityRHSDegreeE ν κ A B e (u (-t)) θ k
      = velocityRHSDegreeE (-ν) κ A B e (fun j => -u (-t) j) θ k := by
    simpa only [neg_neg] using key.symm
  rw [hkey] at hneg
  exact hneg

/-- **Viscosity breaks the symmetry at every shell where the viscous term is nonzero.**  If `ν ≠ 0`
and `u k ≠ 0`, then the right-hand side at `−u` differs from the right-hand side at `u`; the
difference is `2 ν 2^{e k} u_k ≠ 0`.  Equivalently: the reflected trajectory cannot satisfy the
original (nonzero-viscosity) equation at that shell.  The transfer and buoyancy contributions are
irrelevant here — they cancel exactly. -/
theorem viscous_reflection_rhs_ne (ν κ A B : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (k : ℤ)
    (hν : ν ≠ 0) (hu : u k ≠ 0) :
    velocityRHSDegreeE ν κ A B e (fun j => -u j) θ k
      ≠ velocityRHSDegreeE ν κ A B e u θ k := by
  intro h
  have h0 : 2 * ν * dyadicWeight (e * k) * u k = 0 := by
    rw [← velocityRHSDegreeE_neg_sub_eq ν κ A B e u θ k, h, sub_self]
  have hd : dyadicWeight (e * k) ≠ 0 := ne_of_gt (dyadicWeight_pos _)
  rcases mul_eq_zero.mp h0 with h1 | hu0
  · rcases mul_eq_zero.mp h1 with h2 | h3
    · rcases mul_eq_zero.mp h2 with h4 | h5
      · exact (by norm_num : (2 : ℝ) ≠ 0) h4
      · exact hν h5
    · exact hd h3
  · exact hu hu0

/-! ## 7. Non-vacuity witnesses -/

/-- **The inviscid evenness holds nontrivially.**  On the profile `u = (3, 2, 0, …)` at shell `1`
the inviscid right-hand side is `2 · (3² − 0) = 18`, and it is the *same* `18` at `−u`.  The value
is nonzero, so this is not the trivial zero state. -/
theorem witness_inviscid_even (A B : ℝ) :
    velocityRHSDegreeE 0 0 A B 1
        (fun k : ℤ => -(if k = 0 then 3 else if k = 1 then 2 else 0))
        (fun _ : ℤ => 0) 1
      = velocityRHSDegreeE 0 0 A B 1
        (fun k : ℤ => if k = 0 then 3 else if k = 1 then 2 else 0)
        (fun _ : ℤ => 0) 1 :=
  velocityRHSDegreeE_neg_inviscid 0 A B 1
    (fun k : ℤ => if k = 0 then 3 else if k = 1 then 2 else 0) (fun _ : ℤ => 0) 1

/-- The common value of the two sides of `witness_inviscid_even` is `18`, i.e. the transfer at
shell `1` of `(3, 2, 0, …)`: `2 · (3² − 2·2·0) = 18`. -/
theorem witness_inviscid_even_value :
    velocityRHSDegreeE 0 0 1 0 1
        (fun k : ℤ => if k = 0 then 3 else if k = 1 then 2 else 0)
        (fun _ : ℤ => 0) 1 = 18 := by
  norm_num [velocityRHSDegreeE, boussinesqTransferU, dyadicWeight]

/-- **The viscous defect is nonzero.**  For the same profile at shell `1` with `ν = 1`, `e = 1`,
the defect of `velocityRHSDegreeE_neg_sub` evaluates to `2 · 1 · 2^{1} · 2 = 8`. -/
theorem witness_viscous_diff :
    velocityRHSDegreeE 1 0 1 0 1
        (fun k : ℤ => -(if k = 0 then 3 else if k = 1 then 2 else 0))
        (fun _ : ℤ => 0) 1
      - velocityRHSDegreeE 1 0 1 0 1
        (fun k : ℤ => if k = 0 then 3 else if k = 1 then 2 else 0)
        (fun _ : ℤ => 0) 1 = 8 := by
  rw [velocityRHSDegreeE_neg_sub]
  norm_num [viscousTermDegreeE, dyadicWeight]

/-- A direct evaluation of both right-hand sides for the witness: `22 − 14 = 8`.  (Transfer `18`,
viscous term `∓4`.) -/
theorem witness_viscous_diff_direct :
    (velocityRHSDegreeE 1 0 1 0 1
        (fun k : ℤ => -(if k = 0 then 3 else if k = 1 then 2 else 0))
        (fun _ : ℤ => 0) 1 = 22)
      ∧ (velocityRHSDegreeE 1 0 1 0 1
        (fun k : ℤ => if k = 0 then 3 else if k = 1 then 2 else 0)
        (fun _ : ℤ => 0) 1 = 14) := by
  constructor <;> norm_num [velocityRHSDegreeE, boussinesqTransferU, dyadicWeight]

/-- **The reflected self-similar profile solves the inviscid equation.**  The repo's self-similar
solution `selfSimilar 1 t k = (1/3) 2^{−k} (1 − t)^{−1}` (`Cascade/SelfSimilarSolution.lean`) is a
genuine, nonzero solution of the inviscid unforced equation, and its reflection
`t ↦ (fun k => −selfSimilar 1 (−t) k)` is therefore a solution too
(`inviscid_timeReversal_at`).  This is a non-vacuous instance: the reflected profile is nonzero and
its blowup time is reflected from `t = 1` to `t = −1`. -/
theorem witness_timeReversal_reflected_selfSimilar (e : ℤ) :
    HasDerivAt (fun s : ℝ => -selfSimilar 1 (-s) 0)
      (velocityRHSDegreeE 0 0 1 0 e (fun j => -selfSimilar 1 0 j) (fun _ : ℤ => 0) 0) 0 := by
  have h := inviscid_timeReversal_at 0 1 0 e (fun t : ℝ => selfSimilar 1 t) (fun _ : ℤ => 0)
    0 0 (by simpa using selfSimilar_hasDerivAt e 1 0 (by norm_num) 0)
  simpa only [neg_zero] using h

end Cascade

/-! ## Axiom audit -/

#print axioms Cascade.boussinesqTransferU_neg
#print axioms Cascade.buoyancyTermDegreeE
#print axioms Cascade.viscousTermDegreeE
#print axioms Cascade.velocityRHSDegreeE_decomp
#print axioms Cascade.viscousTermDegreeE_neg
#print axioms Cascade.velocityRHSDegreeE_neg_inviscid
#print axioms Cascade.velocityRHSDegreeE_neg_inviscid_unforced
#print axioms Cascade.velocityRHSDegreeE_neg_sub
#print axioms Cascade.velocityRHSDegreeE_neg_sub_eq
#print axioms Cascade.velocityRHSDegreeE_neg_negVisc
#print axioms Cascade.inviscid_timeReversal_at
#print axioms Cascade.inviscid_timeReversal
#print axioms Cascade.reflect
#print axioms Cascade.reflect_involutive
#print axioms Cascade.inviscid_timeReversal_reflect
#print axioms Cascade.viscous_timeReversal_neg
#print axioms Cascade.viscous_reflection_rhs_ne
#print axioms Cascade.witness_inviscid_even
#print axioms Cascade.witness_inviscid_even_value
#print axioms Cascade.witness_viscous_diff
#print axioms Cascade.witness_viscous_diff_direct
#print axioms Cascade.witness_timeReversal_reflected_selfSimilar
