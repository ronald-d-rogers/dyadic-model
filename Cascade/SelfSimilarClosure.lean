import Cascade.SelfSimilarSolution
import Cascade.TruncatedRegularity
import Cascade.BlowupEngine

/-!
# The self-similar closure of the dyadic shell model, and its contrast with the Dirichlet truncation

## What this file does

The repo's degree-`e` shell model is

`u_k' = 2^k (u_{k-1}² − 2 u_k u_{k+1}) + κ θ_k − ν · 2^{ek} u_k`

(`velocityRHSDegreeE ν κ 1 0 e u θ k`).  This file studies a **closure** of the inviscid, unforced
system obtained by a self-similar *twist*

`u_k = 2^{-k} · q_k`,   `q_{k+N} = q_k`  (period `N`),

and certifies that it behaves in the **opposite** way to the Dirichlet-truncated model of
`Cascade/TruncatedRegularity.lean`:

1. **The matching closes the loop.**  The transfer is quadratic and carries a `2^k`, so under
   `u_{k+N} = μ u_k` one has `T_{k+N} = 2^N μ² T_k`.  Consistency of `u'_{k+N} = μ u'_k` with the
   inviscid equation forces `2^N μ² = μ`, hence `μ = 2^{-N}` (`selfSimilarMu_closes`,
   `matching_multiplier_forced`).  The naive closure `u_N = u_0` (`μ = 1`) leaves a genuine flux
   defect (`naive_closure_transfer_defect`): `T_{k+N} = 2^N T_k ≠ T_k` unless `T_k = 0`.  In reduced
   variables the self-similar matching is exactly **periodicity** (`twist_matching_iff`).

2. **The reduced cyclic model.**  With `u_k = 2^{-k} q_k` the transfer is
   `T_k = 2^{-k} (4 q_{k-1}² − q_k q_{k+1})` (`transfer_twist`), so the inviscid cascade *is* the
   finite-dimensional cyclic ODE `q_k' = 4 q_{k-1}² − q_k q_{k+1}`; the two equations are equivalent
   (`twist_solves_iff`, `twist_ode_iff`).

3. **The reduced budget has no boundary defect and no cancellation.**  For the per-period enstrophy
   `H = Σ_{k<N} q_k²` — which *is* the per-period sum `Σ_{k<N} 2^{2k} u_k²` under the twist
   (`twist_enstrophy`; this is a density, not the divergent lattice enstrophy, see the scope note
   below) — the cyclic reindexing `Σ_k q_k q_{k-1}² = Σ_k q_k² q_{k+1}` (`cyclic_reindex`) gives

   `H' = 6 Σ_{k<N} q_k² q_{k+1} − 2νH`   (`reduced_enstrophy_hasDerivAt`).

   The cubic term **survives**; contrast `transfer_pairing_eq_zero`, where the Dirichlet ends
   `u(-1) = u(N) = 0` make the pairing vanish identically.

4. **The blowup.**  The constant profile `q_k = c` reduces the cyclic ODE to `c' = 3c²`
   (`reducedTransfer_const`, `reduced_constant_ode`), whose explicit solution is
   `c(t) = (1/3)(T − t)^{-1}` (`selfSimilar_scalar_hasDerivAt`, obtained by *reusing*
   `selfSimilar_hasDerivAt`).  Under the twist that profile **is** `Cascade.selfSimilar T t k`
   (`twist_const_eq_selfSimilar`), it solves the model (`const_profile_twist_is_selfSimilar`), and
   its level is unbounded at the finite time `T` (`const_profile_level_unbounded`), with critical
   time `1/(3c₀)` from data `c₀` (`const_profile_blowup`).

5. **Viscosity closes only at `e = 0`.**  The twisted viscous coefficient is `ν · 2^{ek}`, which is
   a function on the cycle only if `2^{eN} = 1`, i.e. `e = 0` for `N > 0` (`viscous_periodicity_iff`,
   `e_two_not_closed`, `viscous_coefficient_not_periodic`).  At `e = 2` the ansatz is **not**
   preserved: this closure is a renormalization cycle, not a symmetry.

6. **Sign sensitivity.**  The cubic `Σ_{k<N} q_k² q_{k+1}` is **not** sign-blind: flipping the
   successor amplitude at shell `k` changes it by exactly `−2 q_k² q_{k+1}` (`cubic_flip_sub`), and
   a numeric witness takes `18 ↦ −18` (`cubic_sign_sensitive`).  By contrast the Dirichlet pairing
   vanishes for an *arbitrary* sign pattern (`dirichlet_pairing_sign_blind`).

7. **The finite truncations, for calibration.**  `N = 1` has a frozen shell (`n_one_transfer_frozen`),
   `N = 2` has a cancelling pairing (`n_two_pairing_eq_zero`), and `N = 3` is the smallest
   truncation with an **interior triad** (`n_three_interior_triad`) — but its pairing still cancels
   (`n_three_pairing_eq_zero`).  Blowup in the clamped model requires `N = ∞`.

## Scope: two opposite boundary conditions, not a discovery

The point of the file is an **interpretation of known facts, machine-checked**.  The two systems
differ in exactly one place — what happens at the seam of the retained range:

* **Dirichlet clamps** (`u(-1) = u(N) = 0`) kill *both* end fluxes, so the transfer's energy pairing
  telescopes to zero (`transfer_pairing_eq_zero`) and the cubic never appears.  The truncated model
  is therefore globally regular for every finite `N` and every sign schedule
  (`truncated_globally_regular`).
* The **self-similar twist** matches the two ends only up to the scaling `2^{-N}`
  (`twist_matching_iff`), which leaves the seam term alive: the cyclic reindexing
  (`cyclic_reindex`) is non-destructive and the cubic survives, so the constant profile blows up in
  finite time (`const_profile_blowup`).

Two opposite boundary conditions, two opposite outcomes.  **The Dirichlet wall is what kills the
cubic** — the vanishing is not a technical artifact of the telescoping but the boundary condition
itself.

### This is not a finite-data blowup of the physical model

The reduced quantity `H = Σ_{k<N} q_k²` is a **per-period density**, not a physical enstrophy.  The
physical enstrophy summand is `2^{2k} u_k² = q_k²` (`twist_physical_enstrophy_term`), which is
`N`-periodic; hence the lattice sum `Σ_{k∈ℤ} 2^{2k} u_k²` is the periodic value times
`Σ_{m∈ℤ} 1` and **diverges**.  For the constant profile `q ≡ c` every window of `M` consecutive
shells carries `M c²` (`constant_profile_enstrophy_block`), which is unbounded in `M`.  So the
closure's blowup is **not** a finite-data blowup of the physical model, and nothing here should be
read as one.  `Cascade/SelfSimilarSolution.lean` says the same thing about the same profile
(`selfSimilar_vorticity`, `selfSimilar_level_unbounded`): this is a solution whose level diverges,
not an enstrophy blowup from finite data.

### The profile is not admissible for the clamped model

The self-similar profile has `u_N = 2^{-N} q ≠ 0` (`selfSimilar_not_dirichlet`), so it does **not**
satisfy the Dirichlet condition and is **not** a solution of the clamped/truncated model at all.
The clamped model's regularity and the self-similar blowup are therefore **not in tension**: they are
statements about different systems.  In particular this file is **not** a counterexample to
`truncated_globally_regular`, and it does not contradict `Cascade/SelfSimilarSolution.lean`, which
already records that its profile lives on the untruncated lattice with no clamps.

### All finite `N` are regular; `N = 3` is the first with an interior triad

The clamp argument never needed an interior triad.  At `N = 1` the only retained shell is frozen by
`u(-1) = u(1) = 0` (`n_one_transfer_frozen`: `T_0 = u(-1)² − 2u_0u_1 = 0`, and the equation reads
`u_0' = κ θ_0 − ν u_0`); at `N = 2` the pairing cancels (`n_two_pairing_eq_zero`); at `N = 3` the
middle shell `1` is the smallest interior triad (`n_three_interior_triad`), yet the pairing still
cancels (`n_three_pairing_eq_zero`).  So `N = 3` is special only as the smallest truncation with
nontrivial **dynamics**, not as the smallest *regular* one: blowup in this model requires `N = ∞`.
Every finite `N` is already covered by `truncated_globally_regular`.

### Statements are about a closure, not Navier–Stokes

This is a statement about a **closure** of the shell model — a different model from the
Dirichlet-truncated one, and not a statement about Navier–Stokes.

## Honesty about novelty

The reduction is a **known device**: log-periodic self-similar profiles (a `2^{-k}` envelope times a
periodic modulation, i.e. **discrete scale invariance**) are standard in the shell-model and cascade
literature, and the blowup profile here is the repo's existing `selfSimilar` re-derived in log
coordinates.  Item 4 (`c' = 3c²` plus the identification with `selfSimilar`) **re-derives**
`selfSimilar_hasDerivAt` in the reduced variable; it is worth proving precisely because it makes the
"not new" point checkable.  What this file adds is that the **contrast** — Dirichlet clamps kill the
cubic, the self-similar twist leaves it alive — is machine-checked in this repo's own notation.  It
does **not** add a new blowup and it does not claim the reduction as new.  All constants
(`μ = 2^{-N}`, the `4` and `1` of the reduced ODE, the `6` of the budget, the `3` of `c' = 3c²`) are
derived here from the model definition rather than quoted.

## Formalization choices

* The cycle `ℤ/N` is **not** quotiented.  The reduced state is a function `q : ℤ → ℝ` together with
  an explicit periodicity hypothesis `∀ k, q (k + N) = q k`; this is what the self-similar matching
  produces (`twist_matching_iff`), and it keeps every statement a statement about `Finset.range N`
  sums over `ℤ`-indexed shells.
* Finite sums use `∑ k ∈ Finset.range N, …` (this pin rejects the `∑ k in s, …` binder form).

## Contents

`selfSimilarMu`, `twist`, `reducedTransfer`, `reducedRHS`, `reducedEnstrophy`, `flipAt`,
`cubicWitness`; the matching theorems and the non-Dirichlet facts (`twist_not_dirichlet_top`,
`selfSimilar_not_dirichlet`); the reduction theorem and its equivalence with the model
(`transfer_twist`, `twist_solves_iff`); the physical-enstrophy facts
(`twist_physical_enstrophy_term`, `twist_physical_enstrophy_periodic`, `twist_enstrophy`,
`constant_profile_enstrophy_block`); the
reduced budget (`cyclic_reindex`, `sum_reduced_pairing`, `reduced_enstrophy_hasDerivAt`); the
constant-profile blowup (`selfSimilar_scalar_hasDerivAt`, `twist_const_eq_selfSimilar`,
`const_profile_blowup`); the viscosity closure criterion (`viscous_periodicity_iff`,
`e_two_not_closed`); the sign contrast (`cubic_flip_sub`, `cubic_sign_sensitive`,
`dirichlet_pairing_sign_blind`); and the finite-`N` calibration facts (`n_one_transfer_frozen`,
`n_two_pairing_eq_zero`, `n_three_interior_triad`, `n_three_pairing_eq_zero`).
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators

namespace Cascade

/-! ## 0. The twist, the matching constant, and the reduced data -/

/-- **The self-similar matching multiplier** `μ = 2^{-N} = dyadicWeight (-N)`. -/
def selfSimilarMu (N : ℕ) : ℝ := dyadicWeight (-(N : ℤ))

/-- **The self-similar twist** `u_k = 2^{-k} q_k`.  The reduced state `q` is the modulation of the
`2^{-k}` envelope. -/
def twist (q : ℤ → ℝ) (k : ℤ) : ℝ := dyadicWeight (-k) * q k

/-- **The reduced transfer** `4 q_{k-1}² − q_k q_{k+1}`: the cyclic shell coupling obtained from
`boussinesqTransferU 1 0` after the twist. -/
def reducedTransfer (q : ℤ → ℝ) (k : ℤ) : ℝ := 4 * (q (k - 1)) ^ 2 - q k * q (k + 1)

/-- **The reduced right-hand side at degree `e = 0`**: `4 q_{k-1}² − q_k q_{k+1} − ν q_k`. -/
def reducedRHS (ν : ℝ) (q : ℤ → ℝ) (k : ℤ) : ℝ := reducedTransfer q k - ν * q k

/-- **The per-period enstrophy** `H = Σ_{k<N} q_k²`.  Under the twist this is `Σ_{k<N} 2^{2k} u_k²`
(`twist_enstrophy`). -/
def reducedEnstrophy (q : ℤ → ℝ) (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, (q (k : ℤ)) ^ 2

/-- **Sign flip at a single shell** `m`. -/
def flipAt (m : ℤ) (q : ℤ → ℝ) : ℤ → ℝ := fun k => if k = m then -q k else q k

/-- A concrete three-shell profile used for the sign-sensitivity witness: `q_0 = 3`, `q_1 = s`,
`q_k = 0` otherwise. -/
def cubicWitness (s : ℝ) : ℤ → ℝ := fun k => if k = 0 then 3 else if k = 1 then s else 0

/-! ## 1. The self-similar matching closes the loop -/

/-- `2^k · 2^{-k} = 1`. -/
theorem dyadicWeight_mul_neg (k : ℤ) : dyadicWeight k * dyadicWeight (-k) = 1 := by
  rw [← dyadicWeight_add, add_neg_cancel, dyadicWeight]
  norm_num

/-- `2^{-k} = (2^k)^{-1}`. -/
theorem dyadicWeight_neg (k : ℤ) : dyadicWeight (-k) = (dyadicWeight k)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [mul_comm, dyadicWeight_mul_neg])

/-- **The matching multiplier is positive.** -/
theorem selfSimilarMu_pos (N : ℕ) : 0 < selfSimilarMu N := dyadicWeight_pos _

/-- **The matching multiplier is nonzero.** -/
theorem selfSimilarMu_ne_zero (N : ℕ) : selfSimilarMu N ≠ 0 := (selfSimilarMu_pos N).ne'

/-- **The self-similar matching closes: `2^N μ² = μ` at `μ = 2^{-N}`.**  This is the arithmetic
content of `T_{k+N} = 2^N μ² T_k = μ T_k`: with `μ = 2^{-N}` the transfer relation reproduces the
derivative relation `u'_{k+N} = μ u'_k`, so the flux matches around the loop. -/
theorem selfSimilarMu_closes (N : ℕ) :
    dyadicWeight (N : ℤ) * (selfSimilarMu N) ^ 2 = selfSimilarMu N := by
  unfold selfSimilarMu
  have h : dyadicWeight (N : ℤ) * dyadicWeight (-(N : ℤ)) = 1 := dyadicWeight_mul_neg _
  calc dyadicWeight (N : ℤ) * dyadicWeight (-(N : ℤ)) ^ 2
      = dyadicWeight (-(N : ℤ)) * (dyadicWeight (N : ℤ) * dyadicWeight (-(N : ℤ))) := by ring
    _ = dyadicWeight (-(N : ℤ)) := by rw [h, mul_one]

/-- **Derived, not quoted: the matching multiplier is forced.**  `2^N μ² = μ` with `μ ≠ 0` has the
unique solution `μ = 2^{-N}`.  (The consistency condition is obtained from the transfer scaling
`T_{k+N} = 2^N μ² T_k` together with `u'_{k+N} = μ u'_k`.) -/
theorem matching_multiplier_forced {μ : ℝ} (N : ℕ) (hμ : μ ≠ 0)
    (h : dyadicWeight (N : ℤ) * μ ^ 2 = μ) : μ = selfSimilarMu N := by
  have h1 : (dyadicWeight (N : ℤ) * μ) * μ = (1 : ℝ) * μ := by
    rw [one_mul]
    calc (dyadicWeight (N : ℤ) * μ) * μ = dyadicWeight (N : ℤ) * μ ^ 2 := by ring
      _ = μ := h
  have hmul : dyadicWeight (N : ℤ) * μ = 1 := mul_right_cancel₀ hμ h1
  have hμinv : μ = (dyadicWeight (N : ℤ))⁻¹ := eq_inv_of_mul_eq_one_right hmul
  rw [hμinv, selfSimilarMu, ← dyadicWeight_neg]

/-- **The transfer is degree-2 homogeneous with a `2^k` weight.**  Under the matching hypothesis
`u (k+N) = μ u k`, the transfer at shell `k+N` is `2^N μ²` times the transfer at shell `k`. -/
theorem transfer_matching (u : ℤ → ℝ) (N : ℕ) (μ : ℝ)
    (hμ : ∀ k : ℤ, u (k + (N : ℤ)) = μ * u k) (k : ℤ) :
    boussinesqTransferU 1 0 u (k + (N : ℤ))
      = dyadicWeight (N : ℤ) * μ ^ 2 * boussinesqTransferU 1 0 u k := by
  have h1 : u ((k + (N : ℤ)) - 1) = μ * u (k - 1) := by
    have := hμ (k - 1)
    rwa [show k - 1 + (N : ℤ) = k + (N : ℤ) - 1 by ring] at this
  have h2 : u (k + (N : ℤ)) = μ * u k := hμ k
  have h3 : u ((k + (N : ℤ)) + 1) = μ * u (k + 1) := by
    have := hμ (k + 1)
    rwa [show k + 1 + (N : ℤ) = k + (N : ℤ) + 1 by ring] at this
  simp only [boussinesqTransferU, one_mul, zero_mul, add_zero]
  rw [h1, h2, h3, dyadicWeight_add]
  ring

/-- `2^n = 1` iff `n = 0`, in the repo's `dyadicWeight` notation. -/
theorem dyadicWeight_eq_one_iff (n : ℤ) : dyadicWeight n = 1 ↔ n = 0 :=
  zpow_eq_one_iff_right₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≠ 1)

/-- **The naive closure `u_N = u_0` leaves a flux defect.**  For `N > 0`, under the naive matching
`u (k+N) = u k` the transfer does not match itself around the loop: unless the transfer vanishes at
shell `k`, `T_{k+N} ≠ T_k` because `2^N ≠ 1`.  So `u_N = u_0` is incompatible with the untruncated
transfer; the self-similar multiplier `2^{-N}` is what makes the loop consistent. -/
theorem naive_closure_transfer_defect (u : ℤ → ℝ) (N : ℕ) (hN : 0 < N)
    (hper : ∀ k : ℤ, u (k + (N : ℤ)) = u k) {k : ℤ}
    (hT : boussinesqTransferU 1 0 u k ≠ 0) :
    boussinesqTransferU 1 0 u (k + (N : ℤ)) ≠ boussinesqTransferU 1 0 u k := by
  have hd : dyadicWeight (N : ℤ) ≠ 1 := by
    intro hcon
    have := (dyadicWeight_eq_one_iff (N : ℤ)).mp hcon
    omega
  have h := transfer_matching u N 1 (fun j => by simpa using hper j) k
  rw [h, one_pow, mul_one]
  intro hcon
  apply hT
  have hne : dyadicWeight (N : ℤ) - 1 ≠ 0 := sub_ne_zero.mpr hd
  have hzero : (dyadicWeight (N : ℤ) - 1) * boussinesqTransferU 1 0 u k = 0 := by
    rw [sub_mul, one_mul, hcon, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left hne

/-- **The self-similar matching is periodicity of the reduced state.**  The twist `u_k = 2^{-k} q_k`
satisfies `u_{k+N} = μ u_k` with `μ = 2^{-N}` **iff** `q_{k+N} = q_k`.  Thus the matching condition
of item 1 is exactly a cyclic (period-`N`) ansatz for `q`. -/
theorem twist_matching_iff (q : ℤ → ℝ) (N : ℕ) :
    (∀ k : ℤ, twist q (k + (N : ℤ)) = selfSimilarMu N * twist q k)
      ↔ ∀ k : ℤ, q (k + (N : ℤ)) = q k := by
  constructor
  · intro h k
    have hk := h k
    simp only [twist, selfSimilarMu] at hk
    rw [show -(k + (N : ℤ)) = -(N : ℤ) + -k by ring, dyadicWeight_add] at hk
    have hc : dyadicWeight (-(N : ℤ)) * dyadicWeight (-k) ≠ 0 :=
      mul_ne_zero (dyadicWeight_pos _).ne' (dyadicWeight_pos _).ne'
    have hk' : dyadicWeight (-(N : ℤ)) * dyadicWeight (-k) * q (k + (N : ℤ))
        = dyadicWeight (-(N : ℤ)) * dyadicWeight (-k) * q k := by
      rw [hk]
      ring
    exact mul_left_cancel₀ hc hk'
  · intro h k
    simp only [twist, selfSimilarMu]
    rw [show -(k + (N : ℤ)) = -k + -(N : ℤ) by ring, dyadicWeight_add, h k]
    ring

/-- **The twisted profile fails the Dirichlet condition at the top.**  If the reduced state does not
vanish at shell `0`, then the twisted profile does not vanish at shell `N` (periodicity gives
`q N = q 0`).  In particular the self-similar twist is **not** a solution of the clamped/truncated
model of `Cascade/TruncatedRegularity.lean`, whose top boundary condition is `u N = 0`. -/
theorem twist_not_dirichlet_top (q : ℤ → ℝ) (N : ℕ)
    (hper : ∀ k : ℤ, q (k + (N : ℤ)) = q k) (hq : q 0 ≠ 0) : twist q (N : ℤ) ≠ 0 := by
  have hqN : q (N : ℤ) ≠ 0 := by
    have h := hper 0
    rw [zero_add] at h
    rwa [h]
  simp only [twist]
  exact mul_ne_zero (dyadicWeight_pos _).ne' hqN

/-! ## 2. The reduced cyclic model -/

/-- **The transfer identity.**  Under the twist `u_k = 2^{-k} q_k`,
`T_k = 2^{-k} (4 q_{k-1}² − q_k q_{k+1})`.  Derived from `boussinesqTransferU 1 0` and the shift
identities `2^{-(k-1)} = 2 · 2^{-k}`, `2^{-(k+1)} = ½ · 2^{-k}`. -/
theorem transfer_twist (q : ℤ → ℝ) (k : ℤ) :
    boussinesqTransferU 1 0 (twist q) k = dyadicWeight (-k) * reducedTransfer q k := by
  have h1 : dyadicWeight (-(k - 1)) = dyadicWeight (-k) * 2 := by
    rw [show -(k - 1) = -k + 1 by ring, dyadicWeight_add,
      show dyadicWeight (1 : ℤ) = 2 by simp [dyadicWeight]]
  have h2 : dyadicWeight (-(k + 1)) = dyadicWeight (-k) * (1 / 2) := by
    rw [show -(k + 1) = -k + (-1) by ring, dyadicWeight_add, dyadicWeight_neg_one]
  have hW : dyadicWeight k = (dyadicWeight (-k))⁻¹ := eq_inv_of_mul_eq_one_left (dyadicWeight_mul_neg k)
  have hk : dyadicWeight (-k) ≠ 0 := (dyadicWeight_pos (-k)).ne'
  simp only [boussinesqTransferU, twist, one_mul, zero_mul, add_zero, reducedTransfer]
  rw [h1, h2, hW]
  field_simp
  ring

/-- **The constant-multiple equivalence of `HasDerivAt`.**  For `c ≠ 0`,
`(c f)' = c f'` at `t` iff `f' = f'` at `t`. -/
theorem hasDerivAt_const_mul_iff {c f' : ℝ} (hc : c ≠ 0) (f : ℝ → ℝ) (t : ℝ) :
    HasDerivAt (fun s => c * f s) (c * f') t ↔ HasDerivAt f f' t := by
  constructor
  · intro h
    have h2 : HasDerivAt (fun s => c⁻¹ * (c * f s)) (c⁻¹ * (c * f')) t := h.const_mul c⁻¹
    have hfun : (fun s => c⁻¹ * (c * f s)) = f := by
      funext s
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    have hval : c⁻¹ * (c * f') = f' := by rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rwa [hfun, hval] at h2
  · intro h
    simpa using h.const_mul c

/-- **The inviscid cascade is equivalent to the reduced cyclic ODE.**  The twisted profile
`u_k = 2^{-k} q_k` solves the pure transfer equation at shell `k` iff `q` solves
`q_k' = 4 q_{k-1}² − q_k q_{k+1}`.  This is the clean equivalence of the two equations; it is
`transfer_twist` plus the fact that `2^{-k} ≠ 0`. -/
theorem twist_ode_iff (q : ℝ → ℤ → ℝ) (t : ℝ) (k : ℤ) :
    HasDerivAt (fun s : ℝ => twist (q s) k) (boussinesqTransferU 1 0 (twist (q t)) k) t
      ↔ HasDerivAt (fun s : ℝ => q s k) (reducedTransfer (q t) k) t := by
  have hfun : (fun s : ℝ => twist (q s) k) = fun s : ℝ => dyadicWeight (-k) * q s k := by
    funext s
    rfl
  rw [hfun, transfer_twist]
  exact hasDerivAt_const_mul_iff (dyadicWeight_pos (-k)).ne' (fun s => q s k) t

/-- **The model right-hand side under the twist at degree `e = 0`** (inviscid closure with viscosity
`ν`): `velocityRHSDegreeE ν 0 1 0 0` becomes `2^{-k}` times `reducedRHS ν`. -/
theorem velocityRHSDegreeE_twist (ν : ℝ) (q : ℤ → ℝ) (k : ℤ) :
    velocityRHSDegreeE ν 0 1 0 0 (twist q) (fun _ : ℤ => 0) k
      = dyadicWeight (-k) * reducedRHS ν q k := by
  simp only [velocityRHSDegreeE, reducedRHS]
  rw [transfer_twist]
  have h0 : dyadicWeight (0 * k) = 1 := by simp [dyadicWeight]
  rw [h0]
  simp only [twist]
  ring

/-- **The full closure equivalence at degree `e = 0`**: the twisted profile solves the model
equation (with viscosity `ν` and no forcing) iff the reduced state solves the cyclic ODE
`q_k' = 4 q_{k-1}² − q_k q_{k+1} − ν q_k`. -/
theorem twist_solves_iff (ν : ℝ) (q : ℝ → ℤ → ℝ) (t : ℝ) (k : ℤ) :
    HasDerivAt (fun s : ℝ => twist (q s) k)
        (velocityRHSDegreeE ν 0 1 0 0 (twist (q t)) (fun _ : ℤ => 0) k) t
      ↔ HasDerivAt (fun s : ℝ => q s k) (reducedRHS ν (q t) k) t := by
  have hfun : (fun s : ℝ => twist (q s) k) = fun s : ℝ => dyadicWeight (-k) * q s k := by
    funext s
    rfl
  rw [hfun, velocityRHSDegreeE_twist]
  exact hasDerivAt_const_mul_iff (dyadicWeight_pos (-k)).ne' (fun s => q s k) t

/-! ## 3. The reduced budget: no boundary defect, no cancellation -/

/-- **The reduced enstrophy is nonnegative.** -/
theorem reducedEnstrophy_nonneg (q : ℤ → ℝ) (N : ℕ) : 0 ≤ reducedEnstrophy q N :=
  Finset.sum_nonneg fun k _ => sq_nonneg _

/-- **The physical enstrophy summand of the twisted profile is the *unweighted* reduced square.**
`2^{2k} u_k² = q_k²` for every shell `k`.  This is the pointwise form of `twist_enstrophy`, and it
is the reason the closure has **infinite physical enstrophy** whenever `q ≢ 0`: the summand is
`N`-periodic (hence bounded below by a positive constant on a nonzero orbit), so its lattice sum
`Σ_{k∈ℤ} 2^{2k} u_k²` diverges. -/
theorem twist_physical_enstrophy_term (q : ℤ → ℝ) (k : ℤ) :
    dyadicWeight (2 * k) * (twist q k) ^ 2 = (q k) ^ 2 := by
  have hsq : dyadicWeight (-k) ^ 2 = dyadicWeight (2 * (-k)) := by
    rw [sq, ← dyadicWeight_add]
    congr 1
    ring
  have h1 : dyadicWeight (2 * k) * dyadicWeight (-(2 * k)) = 1 := dyadicWeight_mul_neg _
  have h2 : -(2 * k) = 2 * (-k) := by ring
  simp only [twist]
  calc dyadicWeight (2 * k) * (dyadicWeight (-k) * q k) ^ 2
      = dyadicWeight (2 * k) * (dyadicWeight (-k) ^ 2 * (q k) ^ 2) := by ring
    _ = dyadicWeight (2 * k) * (dyadicWeight (2 * (-k)) * (q k) ^ 2) := by rw [hsq]
    _ = (dyadicWeight (2 * k) * dyadicWeight (-(2 * k))) * (q k) ^ 2 := by rw [h2]; ring
    _ = (q k) ^ 2 := by rw [h1, one_mul]

/-- **The physical enstrophy density is `N`-periodic.**  If `q (k+N) = q k` then
`2^{2(k+N)} u_{k+N}² = 2^{2k} u_k²`.  A nonzero periodic density has a divergent lattice sum
(a nonzero periodic function is bounded away from `0` on its orbit), which is the precise sense in
which the twisted profile carries **infinite physical enstrophy** at every time. -/
theorem twist_physical_enstrophy_periodic (q : ℤ → ℝ) (N : ℕ)
    (hper : ∀ k : ℤ, q (k + (N : ℤ)) = q k) (k : ℤ) :
    dyadicWeight (2 * (k + (N : ℤ))) * (twist q (k + (N : ℤ))) ^ 2
      = dyadicWeight (2 * k) * (twist q k) ^ 2 := by
  rw [twist_physical_enstrophy_term, twist_physical_enstrophy_term, hper k]

/-- **The per-period enstrophy is the twisted energy.**  `Σ_{k<N} 2^{2k} (2^{-k} q_k)² = Σ_{k<N} q_k²`:
the twist converts the weighted enstrophy into the *unweighted* sum `H`.  This is why the reduced
budget has no boundary defect: the weight has been absorbed into the envelope. -/
theorem twist_enstrophy (q : ℤ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * (twist q (k : ℤ)) ^ 2)
      = reducedEnstrophy q N := by
  rw [reducedEnstrophy]
  exact Finset.sum_congr rfl fun k _ => twist_physical_enstrophy_term q (k : ℤ)

/-- **A block of `M` physical shells carries enstrophy `M c²` for the constant reduced profile.**
The twisted constant profile `q ≡ c` has physical enstrophy density `2^{2m} u_m² = c²` at *every*
shell `m`, so any window of `M` consecutive shells has enstrophy `M c²`.  For `c ≠ 0` this is
unbounded in `M`: the closure's physical lattice enstrophy is **infinite**, and the reduced `H` is a
per-period density, not a finite physical enstrophy. -/
theorem constant_profile_enstrophy_block (c : ℝ) (M : ℕ) (a : ℤ) :
    (∑ k ∈ Finset.range M,
        dyadicWeight (2 * ((k : ℤ) + a)) * (twist (fun _ : ℤ => c) ((k : ℤ) + a)) ^ 2)
      = M * c ^ 2 := by
  have hterm : ∀ m : ℤ, dyadicWeight (2 * m) * (twist (fun _ : ℤ => c) m) ^ 2 = c ^ 2 :=
    fun m => twist_physical_enstrophy_term (fun _ : ℤ => c) m
  calc (∑ k ∈ Finset.range M,
        dyadicWeight (2 * ((k : ℤ) + a)) * (twist (fun _ : ℤ => c) ((k : ℤ) + a)) ^ 2)
      = ∑ _k ∈ Finset.range M, c ^ 2 :=
        Finset.sum_congr rfl fun k _ => hterm _
    _ = M * c ^ 2 := by simp [Finset.sum_const, nsmul_eq_mul]

/-- **Cyclic shift of a finite sum.**  If `f` is `N`-periodic then shifting the index by one does
not change the sum over one period.  (The wrap-around `f N = f 0` is exactly the periodicity.) -/
theorem cyclic_shift_sum (f : ℤ → ℝ) (N : ℕ) (hper : ∀ k : ℤ, f (k + (N : ℤ)) = f k) :
    (∑ k ∈ Finset.range N, f ((k : ℤ) + 1)) = ∑ k ∈ Finset.range N, f (k : ℤ) := by
  have h1 := Finset.sum_range_succ' (fun k : ℕ => f (k : ℤ)) N
  have h2 := Finset.sum_range_succ (fun k : ℕ => f (k : ℤ)) N
  have hFN : f (((N : ℕ) : ℤ)) = f (((0 : ℕ) : ℤ)) := by
    have := hper 0
    simpa using this
  have h3 : (∑ k ∈ Finset.range N, f (((k + 1 : ℕ) : ℤ))) = ∑ k ∈ Finset.range N, f (k : ℤ) := by
    have heq : (∑ k ∈ Finset.range N, f (((k + 1 : ℕ) : ℤ))) + f (((0 : ℕ) : ℤ))
        = (∑ k ∈ Finset.range N, f (k : ℤ)) + f (((N : ℕ) : ℤ)) := by
      rw [← h1, h2]
    rw [hFN] at heq
    exact add_right_cancel heq
  rw [← h3]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Nat.cast_add, Nat.cast_one]

/-- **The cyclic reindexing** `Σ_k q_k q_{k-1}² = Σ_k q_k² q_{k+1}`.  This is the step with no
Dirichlet boundary term: the wrap-around is handled by the periodicity `q (k+N) = q k`, and nothing
vanishes.  It is the exact replacement for the flux telescoping of `transfer_pairing_eq_zero`. -/
theorem cyclic_reindex (q : ℤ → ℝ) (N : ℕ) (hper : ∀ k : ℤ, q (k + (N : ℤ)) = q k) :
    (∑ k ∈ Finset.range N, q (k : ℤ) * (q ((k : ℤ) - 1)) ^ 2)
      = ∑ k ∈ Finset.range N, (q (k : ℤ)) ^ 2 * q ((k : ℤ) + 1) := by
  have hfper : ∀ j : ℤ,
      (fun j : ℤ => (q (j - 1)) ^ 2 * q j) (j + (N : ℤ))
        = (fun j : ℤ => (q (j - 1)) ^ 2 * q j) j := by
    intro j
    simp only
    rw [show j + (N : ℤ) - 1 = (j - 1) + (N : ℤ) by ring, hper (j - 1), hper j]
  have h := cyclic_shift_sum (fun j : ℤ => (q (j - 1)) ^ 2 * q j) N hfper
  have hL : (∑ k ∈ Finset.range N, q (k : ℤ) * (q ((k : ℤ) - 1)) ^ 2)
      = ∑ k ∈ Finset.range N, (q ((k : ℤ) - 1)) ^ 2 * q (k : ℤ) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hL, ← h]
  apply Finset.sum_congr rfl
  intro k _
  rw [show ((k : ℤ) + 1) - 1 = (k : ℤ) by ring]

/-- **The reduced pairing of the transfer** is `3 Σ_k q_k² q_{k+1}`: the two transfer monomials
contribute `4` and `−1`, and the cyclic reindexing makes the first `4 Σ q_k² q_{k+1}`, leaving `3`.
The cubic does **not** cancel. -/
theorem sum_reduced_pairing (q : ℤ → ℝ) (N : ℕ)
    (hper : ∀ k : ℤ, q (k + (N : ℤ)) = q k) :
    (∑ k ∈ Finset.range N, q (k : ℤ) * reducedTransfer q (k : ℤ))
      = 3 * ∑ k ∈ Finset.range N, (q (k : ℤ)) ^ 2 * q ((k : ℤ) + 1) := by
  have hsplit : ∀ k ∈ Finset.range N,
      q (k : ℤ) * reducedTransfer q (k : ℤ)
        = 4 * (q (k : ℤ) * (q ((k : ℤ) - 1)) ^ 2) - (q (k : ℤ)) ^ 2 * q ((k : ℤ) + 1) := by
    intro k _
    simp only [reducedTransfer]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
  rw [show (∑ k ∈ Finset.range N, 4 * (q (k : ℤ) * (q ((k : ℤ) - 1)) ^ 2))
        = 4 * ∑ k ∈ Finset.range N, q (k : ℤ) * (q ((k : ℤ) - 1)) ^ 2 by
    rw [Finset.mul_sum]]
  rw [cyclic_reindex q N hper]
  ring

/-- **THE REDUCED BUDGET.**  Any reduced state satisfying the cyclic degree-`0` ODE with viscosity
`ν` has

`H' = 6 Σ_{k<N} q_k² q_{k+1} − 2νH`,   `H = Σ_{k<N} q_k²`.

No Dirichlet hypothesis appears, and the cubic is **not** cancelled: the factor `6 = 2 · 3` is the
energy factor `2` times the reduced pairing constant `3`.  Compare `transfer_pairing_eq_zero`, where
the corresponding pairing is identically zero under the Dirichlet ends. -/
theorem reduced_enstrophy_hasDerivAt (ν : ℝ) (N : ℕ) (q : ℝ → ℤ → ℝ) (t : ℝ)
    (hper : ∀ k : ℤ, q t (k + (N : ℤ)) = q t k)
    (hq : ∀ k ∈ Finset.range N,
      HasDerivAt (fun s : ℝ => q s (k : ℤ)) (reducedRHS ν (q t) (k : ℤ)) t) :
    HasDerivAt (fun s : ℝ => reducedEnstrophy (q s) N)
      (6 * (∑ k ∈ Finset.range N, (q t (k : ℤ)) ^ 2 * q t ((k : ℤ) + 1))
        - 2 * ν * reducedEnstrophy (q t) N) t := by
  have hsum : HasDerivAt (∑ k ∈ Finset.range N, fun s : ℝ => (q s (k : ℤ)) ^ 2)
      (∑ k ∈ Finset.range N, 2 * q t (k : ℤ) * reducedRHS ν (q t) (k : ℤ)) t :=
    HasDerivAt.sum (u := Finset.range N)
      (A := fun k s => (q s (k : ℤ)) ^ 2)
      (A' := fun k => 2 * q t (k : ℤ) * reducedRHS ν (q t) (k : ℤ))
      (fun k hk => by
        have hd := (hq k hk).pow 2
        have hfun : ((fun s : ℝ => q s (k : ℤ)) ^ 2) = fun s : ℝ => (q s (k : ℤ)) ^ 2 := by
          funext s
          rw [Pi.pow_apply]
        rw [hfun] at hd
        simpa using hd)
  have hfun : (∑ k ∈ Finset.range N, fun s : ℝ => (q s (k : ℤ)) ^ 2)
      = fun s : ℝ => reducedEnstrophy (q s) N := by
    funext s
    rw [reducedEnstrophy]
    exact finset_sum_apply (Finset.range N) (fun (k : ℕ) (s : ℝ) => (q s (k : ℤ)) ^ 2) s
  rw [hfun] at hsum
  have hval : (∑ k ∈ Finset.range N, 2 * q t (k : ℤ) * reducedRHS ν (q t) (k : ℤ))
      = 6 * (∑ k ∈ Finset.range N, (q t (k : ℤ)) ^ 2 * q t ((k : ℤ) + 1))
        - 2 * ν * reducedEnstrophy (q t) N := by
    have h2 : (∑ k ∈ Finset.range N, 2 * q t (k : ℤ) * reducedRHS ν (q t) (k : ℤ))
        = 2 * ∑ k ∈ Finset.range N, q t (k : ℤ) * reducedRHS ν (q t) (k : ℤ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have h3 : (∑ k ∈ Finset.range N, q t (k : ℤ) * reducedRHS ν (q t) (k : ℤ))
        = 3 * (∑ k ∈ Finset.range N, (q t (k : ℤ)) ^ 2 * q t ((k : ℤ) + 1))
          - ν * reducedEnstrophy (q t) N := by
      have hsplit : ∀ k ∈ Finset.range N,
          q t (k : ℤ) * reducedRHS ν (q t) (k : ℤ)
            = q t (k : ℤ) * reducedTransfer (q t) (k : ℤ) - ν * (q t (k : ℤ)) ^ 2 := by
        intro k _
        simp only [reducedRHS]
        ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib,
        sum_reduced_pairing (q t) N hper]
      rw [show (∑ k ∈ Finset.range N, ν * (q t (k : ℤ)) ^ 2)
            = ν * reducedEnstrophy (q t) N by
        rw [reducedEnstrophy, Finset.mul_sum]]
    rw [h2, h3]
    ring
  rw [hval] at hsum
  exact hsum

/-! ## 4. The blowup -/

/-- **The constant profile is a fixed point of the transfer, up to the cubic.**  For `q ≡ c`,
`4 q_{k-1}² − q_k q_{k+1} = 3 c²`. -/
theorem reducedTransfer_const (c : ℝ) (k : ℤ) :
    reducedTransfer (fun _ : ℤ => c) k = 3 * c ^ 2 := by
  simp only [reducedTransfer]
  ring

/-- **The constant profile reduces the cyclic ODE to `c' = 3 c² − ν c`.** -/
theorem reducedRHS_const (ν c : ℝ) (k : ℤ) :
    reducedRHS ν (fun _ : ℤ => c) k = 3 * c ^ 2 - ν * c := by
  simp only [reducedRHS, reducedTransfer]
  ring

/-- **The constant-profile reduction of the cyclic ODE.**  The cyclic equation at the constant
profile `q_k = c t` is equivalent to the scalar Riccati equation `c' = 3c² − νc`. -/
theorem reduced_constant_ode (ν : ℝ) (c : ℝ → ℝ) (t : ℝ) (k : ℤ) :
    HasDerivAt (fun s : ℝ => (fun _ : ℤ => c s) k) (reducedRHS ν (fun _ : ℤ => c t) k) t
      ↔ HasDerivAt c (3 * (c t) ^ 2 - ν * (c t)) t := by
  have hfun : (fun s : ℝ => (fun _ : ℤ => c s) k) = c := rfl
  rw [hfun, reducedRHS_const]

/-- **`c' = 3c²` for the constant profile**: the inviscid (`ν = 0`) specialisation. -/
theorem reduced_constant_ode_inviscid (c : ℝ → ℝ) (t : ℝ) (k : ℤ) :
    HasDerivAt (fun s : ℝ => (fun _ : ℤ => c s) k) (reducedRHS 0 (fun _ : ℤ => c t) k) t
      ↔ HasDerivAt c (3 * (c t) ^ 2) t := by
  simpa using reduced_constant_ode 0 c t k

/-- **Shell shift down for the self-similar profile**: `u_{k-1} = 2 u_k`.  (Reproved here from
`dyadicWeight_add`; the copy in `Cascade/SelfSimilarSolution.lean` is private.) -/
theorem selfSimilar_sub_one (T t : ℝ) (k : ℤ) :
    selfSimilar T t (k - 1) = 2 * selfSimilar T t k := by
  unfold selfSimilar
  have h1 : dyadicWeight (-(k - 1)) = dyadicWeight (-k) * 2 := by
    rw [show -(k - 1) = -k + 1 by ring, dyadicWeight_add,
      show dyadicWeight (1 : ℤ) = 2 by simp [dyadicWeight]]
  rw [h1]
  ring

/-- **Shell shift up for the self-similar profile**: `u_{k+1} = ½ u_k`. -/
theorem selfSimilar_add_one (T t : ℝ) (k : ℤ) :
    selfSimilar T t (k + 1) = (1 / 2) * selfSimilar T t k := by
  unfold selfSimilar
  have h1 : dyadicWeight (-(k + 1)) = dyadicWeight (-k) * (1 / 2) := by
    rw [show -(k + 1) = -k + (-1) by ring, dyadicWeight_add, dyadicWeight_neg_one]
  rw [h1]
  ring

/-- **`c' = 3c²` for the explicit self-similar scalar, by reusing `selfSimilar_hasDerivAt`.**  The
value of the scalar derivative is `3 ((1/3)(T−t)^{-1})²`, i.e. the Riccati reduction of item 4 at
the self-similar profile; the proof evaluates the repo's own
`velocityRHSDegreeE 0 0 1 0 0 (selfSimilar T t) 0` at shell `0`, so no differentiation is redone. -/
theorem selfSimilar_scalar_hasDerivAt (T t : ℝ) (ht : t ≠ T) :
    HasDerivAt (fun s : ℝ => (1 / 3) * (T - s)⁻¹) (3 * ((1 / 3) * (T - t)⁻¹) ^ 2) t := by
  have h := selfSimilar_hasDerivAt 0 T t ht 0
  have hfun : (fun s : ℝ => selfSimilar T s 0) = fun s : ℝ => (1 / 3) * (T - s)⁻¹ := by
    funext s
    simp [selfSimilar, dyadicWeight]
  have hneg : selfSimilar T t (-1) = 2 * selfSimilar T t 0 := by
    simpa using selfSimilar_sub_one T t 0
  have hpos : selfSimilar T t 1 = (1 / 2) * selfSimilar T t 0 := by
    simpa using selfSimilar_add_one T t 0
  have hval : velocityRHSDegreeE 0 0 1 0 0 (selfSimilar T t) (fun _ : ℤ => 0) 0
      = 3 * ((1 / 3) * (T - t)⁻¹) ^ 2 := by
    have h0 : selfSimilar T t 0 = (1 / 3) * (T - t)⁻¹ := by simp [selfSimilar, dyadicWeight]
    simp only [velocityRHSDegreeE, boussinesqTransferU, one_mul, zero_mul, add_zero,
      mul_zero, sub_zero]
    rw [show (0 : ℤ) - 1 = -1 by norm_num, show (0 : ℤ) + 1 = 1 by norm_num]
    simp only [dyadicWeight, zpow_zero, one_mul]
    simp only [hneg, hpos, h0]
    ring
  rwa [hfun, hval] at h

/-- **The constant profile is the self-similar profile.**  Under the twist, the constant reduced
profile `q_k = c` with `c = (1/3)(T − t)^{-1}` gives back `Cascade.selfSimilar T t k`.  This is the
identification required of item 4: the abstract blowup profile is literally the repo's
`selfSimilar`. -/
theorem twist_const_eq_selfSimilar (T t : ℝ) (k : ℤ) :
    twist (fun _ : ℤ => (1 / 3) * (T - t)⁻¹) k = selfSimilar T t k := by
  unfold twist selfSimilar
  ring

/-- **The self-similar profile does not satisfy the Dirichlet condition.**  For `N > 0` and
`t ≠ T`, `selfSimilar T t N = 2^{-N} (1/3)(T-t)^{-1} ≠ 0`.  This is the concrete reason the
self-similar blowup and the clamped model's regularity are not in tension: the profile is not
admissible data for the clamped model at all.  (It is the constant-twist case of
`twist_not_dirichlet_top`.) -/
theorem selfSimilar_not_dirichlet (T t : ℝ) (N : ℕ) (hN : 0 < N) (ht : t ≠ T) :
    selfSimilar T t (N : ℤ) ≠ 0 := by
  have hc : (1 / 3) * (T - t)⁻¹ ≠ 0 :=
    mul_ne_zero (by norm_num) (inv_ne_zero (sub_ne_zero.mpr (Ne.symm ht)))
  have h := twist_not_dirichlet_top (fun _ : ℤ => (1 / 3) * (T - t)⁻¹) N (fun _ => rfl) hc
  rwa [twist_const_eq_selfSimilar] at h

/-- The twist of a constant at shell `0` is the constant. -/
theorem twist_const_zero (c : ℝ) : twist (fun _ : ℤ => c) 0 = c := by
  simp [twist, dyadicWeight]

/-- **The constant reduced profile solves the cyclic ODE at degree `0`.**  Capstone of item 4: the
self-similar scalar is a solution of the reduced model. -/
theorem const_profile_solves_reduced (T t : ℝ) (ht : t ≠ T) (k : ℤ) :
    HasDerivAt (fun s : ℝ => (fun _ : ℤ => (1 / 3) * (T - s)⁻¹) k)
      (reducedRHS 0 (fun _ : ℤ => (1 / 3) * (T - t)⁻¹) k) t := by
  rw [reduced_constant_ode]
  simpa using selfSimilar_scalar_hasDerivAt T t ht

/-- **The twisted constant profile solves the repo's model equation** (inviscid, unforced).  This
is `selfSimilar_hasDerivAt` at shell `k`, transported through the identification
`twist_const_eq_selfSimilar`. -/
theorem const_profile_twist_is_selfSimilar (T t : ℝ) (ht : t ≠ T) (k : ℤ) :
    HasDerivAt (fun s : ℝ => twist (fun _ : ℤ => (1 / 3) * (T - s)⁻¹) k)
      (boussinesqTransferU 1 0 (twist (fun _ : ℤ => (1 / 3) * (T - t)⁻¹)) k) t := by
  have h := selfSimilar_hasDerivAt 0 T t ht k
  have hfun : (fun s : ℝ => selfSimilar T s k)
      = fun s : ℝ => twist (fun _ : ℤ => (1 / 3) * (T - s)⁻¹) k := by
    funext s
    rw [twist_const_eq_selfSimilar]
  have hval : velocityRHSDegreeE 0 0 1 0 0 (selfSimilar T t) (fun _ : ℤ => 0) k
      = boussinesqTransferU 1 0 (twist (fun _ : ℤ => (1 / 3) * (T - t)⁻¹)) k := by
    have hsu : selfSimilar T t = twist (fun _ : ℤ => (1 / 3) * (T - t)⁻¹) := by
      funext j
      exact (twist_const_eq_selfSimilar T t j).symm
    simp only [velocityRHSDegreeE, zero_mul, mul_zero, sub_zero, add_zero]
    rw [hsu]
  rwa [hfun, hval] at h

/-- **The self-similar level is unbounded at the finite time `T`.**  For every bound `M` there is a
time `t < T` at which the twisted constant profile (at shell `0`, where the twist is the identity)
exceeds `M`.  This is `selfSimilar_level_unbounded` transported to the profile of this file. -/
theorem const_profile_level_unbounded (T : ℝ) :
    ∀ M : ℝ, ∃ t : ℝ, t < T ∧ M < twist (fun _ : ℤ => (1 / 3) * (T - t)⁻¹) 0 := by
  intro M
  obtain ⟨t, ht, hM⟩ := selfSimilar_level_unbounded T M
  exact ⟨t, ht, by simpa [twist_const_zero] using hM⟩

/-- **The algebraic law of the self-similar scalar**: `(1/3)(1/(3c₀) − t)^{-1} = c₀/(1 − 3c₀t)`,
so the profile with data `c₀` at `t = 0` is `c₀/(1 − 3c₀t)`. -/
theorem selfSimilar_scalar_eq (c₀ t : ℝ) (hc₀ : c₀ ≠ 0) :
    (1 / 3) * (1 / (3 * c₀) - t)⁻¹ = c₀ / (1 - 3 * c₀ * t) := by
  have h3 : (3 : ℝ) * c₀ ≠ 0 := mul_ne_zero (by norm_num) hc₀
  rcases eq_or_ne (1 - 3 * c₀ * t) 0 with hD | hD
  · rw [hD, div_zero]
    have hz : 1 / (3 * c₀) - t = 0 := by
      field_simp
      linarith
    rw [hz, inv_zero, mul_zero]
  · have hkey : 1 / (3 * c₀) - t = (1 - 3 * c₀ * t) / (3 * c₀) := by
      field_simp
    rw [hkey, inv_div]
    field_simp

/-- **FINITE-TIME BLOWUP.**  The constant reduced profile with data `c₀ > 0` at time `0`,
`c(t) = c₀/(1 − 3c₀t)`, is unbounded as `t ↑ 1/(3c₀)`: for every bound `M` it exceeds `M` at some
finite time `t < 1/(3c₀)`.  So the self-similar closure blows up in finite time for every `N`,
in sharp contrast with the Dirichlet-truncated model's global regularity. -/
theorem const_profile_blowup (c₀ : ℝ) (hc₀ : 0 < c₀) :
    ∀ M : ℝ, ∃ t : ℝ, t < 1 / (3 * c₀) ∧ M < c₀ / (1 - 3 * c₀ * t) := by
  intro M
  obtain ⟨t, ht, hM⟩ := const_profile_level_unbounded (1 / (3 * c₀)) M
  refine ⟨t, ht, ?_⟩
  rw [twist_const_zero] at hM
  rw [← selfSimilar_scalar_eq c₀ t hc₀.ne']
  exact hM

/-! ## 5. Viscosity closes only at `e = 0` -/

/-- **The viscous weight is `N`-periodic iff `e = 0`** (for `N > 0`): `2^{eN} = 1 ↔ e = 0`.  This is
the closure criterion: the twisted viscous term `−ν 2^{ek} q_k` descends to a function on the cycle
only when the multiplier `2^{eN}` is `1`. -/
theorem viscous_periodicity_iff (e : ℤ) (N : ℕ) (hN : 0 < N) :
    dyadicWeight (e * (N : ℤ)) = 1 ↔ e = 0 := by
  rw [dyadicWeight_eq_one_iff]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h (by exact_mod_cast hN.ne')
  · intro h
    rw [h, zero_mul]

/-- **At `e = 0` the viscous term is a function on the cycle**: the coefficient `2^{0·k} = 1`. -/
theorem viscous_coefficient_periodic_zero (k : ℤ) :
    dyadicWeight (0 * k) = dyadicWeight (0 * (k + 1)) := by
  simp

/-- **At `e ≠ 0` the viscous coefficient is NOT periodic** (for `N > 0`): there is a shell `k` with
`2^{e(k+N)} ≠ 2^{ek}`.  Hence the ansatz is not preserved by the viscous term at any `e ≠ 0`. -/
theorem viscous_coefficient_not_periodic (e : ℤ) (he : e ≠ 0) (N : ℕ) (hN : 0 < N) :
    ∃ k : ℤ, dyadicWeight (e * (k + (N : ℤ))) ≠ dyadicWeight (e * k) := by
  refine ⟨0, ?_⟩
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hne : e * (N : ℤ) ≠ 0 := mul_ne_zero he hN'
  have hz : dyadicWeight (0 : ℤ) = 1 := (dyadicWeight_eq_one_iff 0).mpr rfl
  intro h
  rw [zero_add, mul_zero, hz] at h
  exact hne ((dyadicWeight_eq_one_iff (e * (N : ℤ))).mp h)

/-- **At `e = 2` the ansatz is not preserved** (for `N > 0`): `2^{2N} ≠ 1`.  The physical degree-`2`
dissipation is exactly the case where the reduction fails; the closure at `e = 0` is a
renormalization cycle, not a symmetry. -/
theorem e_two_not_closed (N : ℕ) (hN : 0 < N) : dyadicWeight (2 * (N : ℤ)) ≠ 1 := by
  intro h
  have h2 : (2 : ℤ) = 0 := (viscous_periodicity_iff 2 N hN).mp h
  norm_num at h2

/-! ## 6. Sign sensitivity: the cubic survives and is not sign-blind -/

/-- **The single-shell flip of the cubic.**  Flipping `q_{k+1}` changes `Σ_{j<N} q_j² q_{j+1}` by
exactly `−2 q_k² q_{k+1}`.  The shell-`k+1` term of the sum is even in `q_{k+1}`; only the shell-`k`
term reacts, and there `q_{k+1}` enters linearly.  No periodicity is needed for this identity. -/
theorem cubic_flip_sub (q : ℤ → ℝ) (N k : ℕ) (hk : k < N) :
    (∑ j ∈ Finset.range N,
        ((flipAt ((k : ℤ) + 1) q) (j : ℤ)) ^ 2 * (flipAt ((k : ℤ) + 1) q) ((j : ℤ) + 1))
      - (∑ j ∈ Finset.range N, (q (j : ℤ)) ^ 2 * q ((j : ℤ) + 1))
      = -2 * (q (k : ℤ)) ^ 2 * q ((k : ℤ) + 1) := by
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k]
  · simp only [flipAt]
    rw [ite_eq_right (by omega : (k : ℤ) ≠ (k : ℤ) + 1)]
    simp only [ite_true]
    ring
  · intro j _ hjne
    have h2 : (j : ℤ) + 1 ≠ (k : ℤ) + 1 := by
      intro h
      exact hjne (by omega)
    simp only [flipAt]
    rw [ite_eq_right h2]
    by_cases hjk : (j : ℤ) = (k : ℤ) + 1
    · rw [ite_eq_left hjk]
      ring
    · rw [ite_eq_right hjk]
      ring
  · intro hknot
    exact absurd (Finset.mem_range.mpr hk) hknot

/-- **The contrast: the Dirichlet pairing is sign-blind.**  For any sign pattern `σ` and any state
with Dirichlet ends, the energy pairing of the sign-flipped state vanishes — it vanishes for the
original state (`transfer_pairing_eq_zero`) and it vanishes for *every* flip.  Nothing about the
signs is detected. -/
theorem dirichlet_pairing_sign_blind (u : ℤ → ℝ) (N : ℕ) (σ : ℤ → ℝ)
    (hbot : u (-1) = 0) (htop : u (N : ℤ) = 0) :
    (∑ k ∈ Finset.range N, (σ (k : ℤ) * u (k : ℤ))
        * boussinesqTransferU 1 0 (fun j : ℤ => σ j * u j) (k : ℤ)) = 0 := by
  have h := transfer_pairing_eq_zero (fun j : ℤ => σ j * u j) N (by simp [hbot]) (by simp [htop])
  simpa only using h

/-- The cubic at the witness profile `q = (3, s)`: `3²·s + s²·0 = 9s`. -/
theorem cubicWitness_value (s : ℝ) :
    (∑ j ∈ Finset.range 2, (cubicWitness s (j : ℤ)) ^ 2 * cubicWitness s ((j : ℤ) + 1))
      = 9 * s := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cubicWitness]
  norm_num

/-- At `s = 2` the witness cubic is `18`. -/
theorem cubicWitness_pos :
    (∑ j ∈ Finset.range 2, (cubicWitness 2 (j : ℤ)) ^ 2 * cubicWitness 2 ((j : ℤ) + 1)) = 18 := by
  rw [cubicWitness_value]
  norm_num

/-- **A concrete sign flip changes the cubic.**  Flipping the successor amplitude `q_1` of the
witness profile `(3, 2)` takes the cubic from `18` to `−18`; the flip formula gives the change
`−2 · 3² · 2 = −36`. -/
theorem cubicWitness_flip_sub :
    (∑ j ∈ Finset.range 2,
        ((flipAt 1 (cubicWitness 2)) (j : ℤ)) ^ 2 * (flipAt 1 (cubicWitness 2)) ((j : ℤ) + 1))
      - (∑ j ∈ Finset.range 2, (cubicWitness 2 (j : ℤ)) ^ 2 * cubicWitness 2 ((j : ℤ) + 1))
      = -36 := by
  have h := cubic_flip_sub (cubicWitness 2) 2 0 (by norm_num)
  norm_num [cubicWitness] at h ⊢
  exact h

/-- The flipped witness cubic itself: `(3, −2)` gives `3²·(−2) + (−2)²·0 = −18`. -/
theorem cubicWitness_flip_value :
    (∑ j ∈ Finset.range 2,
        ((flipAt 1 (cubicWitness 2)) (j : ℤ)) ^ 2 * (flipAt 1 (cubicWitness 2)) ((j : ℤ) + 1))
      = -18 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, flipAt, cubicWitness]
  norm_num

/-- **THE SIGN CONTRAST.**  The cubic `Σ_{k<N} q_k² q_{k+1}` is *not* sign-blind: flipping the
successor amplitude `q_1` of the concrete profile `q = (3, 2, 0, …)` changes the sum from `18` to
`−18`.  Compare `dirichlet_pairing_sign_blind` / `transfer_pairing_eq_zero`, where the pairing is `0`
for an arbitrary state and every sign pattern. -/
theorem cubic_sign_sensitive :
    (∑ j ∈ Finset.range 2, (cubicWitness 2 (j : ℤ)) ^ 2 * cubicWitness 2 ((j : ℤ) + 1))
      ≠ (∑ j ∈ Finset.range 2,
          ((flipAt 1 (cubicWitness 2)) (j : ℤ)) ^ 2
            * (flipAt 1 (cubicWitness 2)) ((j : ℤ) + 1)) := by
  rw [cubicWitness_pos, cubicWitness_flip_value]
  norm_num

/-! ## 7. Every finite truncation is regular; `N = 3` is the first with an interior triad

The clamp argument of `Cascade/TruncatedRegularity.lean` never needs an interior triad.  The two
smallest truncations are degenerate, and the facts below record that directly:

* `N = 1`: the only retained shell is `k = 0`, and with `u(-1) = u(1) = 0` its transfer is
  `T_0 = u(-1)² − 2u_0u_1 = 0`.  The shell is frozen (`n_one_transfer_frozen`): it sees only
  buoyancy and viscosity.  This is the nonzero-witness truncation of
  `Cascade/TruncatedRegularity.lean`.
* `N = 2`: the pairing cancels (`n_two_pairing_eq_zero`), so no enstrophy is produced.
* `N = 3`: the middle shell `1` has both neighbours inside the retained range — the smallest
  **interior triad** (`n_three_interior_triad`) — and the pairing still cancels
  (`n_three_pairing_eq_zero`).

So `N = 3` is special only as the smallest truncation with nontrivial *dynamics*, not as the
smallest *regular* one.  Every finite `N` is globally regular (`truncated_globally_regular`), and
blowup in this family requires `N = ∞`.  The closure of this file is a different system, not a
finite truncation of that one. -/

/-- **`N = 1`: the single retained shell is frozen.**  Under `u(-1) = u(1) = 0` the shell-`0`
transfer vanishes identically, so the equation is `u_0' = κ θ_0 − ν u_0` (no nonlinearity). -/
theorem n_one_transfer_frozen (ν κ : ℝ) (e : ℤ) (u θ : ℤ → ℝ)
    (hbot : u (-1) = 0) (htop : u 1 = 0) :
    velocityRHSDegreeE ν κ 1 0 e u θ 0 = κ * θ 0 - ν * u 0 := by
  have hb : boussinesqTransferU 1 0 u 0 = 0 := by
    simp only [boussinesqTransferU, one_mul, zero_mul, add_zero]
    rw [show (0 : ℤ) - 1 = -1 by norm_num, show (0 : ℤ) + 1 = 1 by norm_num, hbot, htop]
    ring
  have h0 : dyadicWeight (e * 0) = 1 := by simp [dyadicWeight]
  simp only [velocityRHSDegreeE, hb, zero_add, h0]
  ring

/-- **`N = 2`: the pairing cancels.**  The Dirichlet ends `u(-1) = u(2) = 0` kill both boundary
fluxes, so `u_0 T_0 + u_1 T_1 = 0`. -/
theorem n_two_pairing_eq_zero (u : ℤ → ℝ) (hbot : u (-1) = 0) (htop : u 2 = 0) :
    u 0 * boussinesqTransferU 1 0 u 0 + u 1 * boussinesqTransferU 1 0 u 1 = 0 := by
  have h := transfer_pairing_eq_zero u 2 hbot (by simpa using htop)
  simpa [Finset.sum_range_succ, Finset.sum_range_one] using h

/-- **`N = 3`: the middle shell has both neighbours inside the retained range.**  Shell `1` is the
smallest interior triad; its transfer reads `u_0` and `u_2`. -/
theorem n_three_interior_triad (u : ℤ → ℝ) :
    boussinesqTransferU 1 0 u 1 = dyadicWeight 1 * ((u 0) ^ 2 - 2 * u 1 * u 2) := by
  simp only [boussinesqTransferU, one_mul, zero_mul, add_zero]
  rw [show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num]

/-- **`N = 3`: the pairing still cancels.**  Even with an interior triad, the Dirichlet ends
`u(-1) = u(3) = 0` make `u_0 T_0 + u_1 T_1 + u_2 T_2 = 0`: nontrivial dynamics, no enstrophy
production.  `N = 3` is the first truncation with nontrivial dynamics, not the first irregular one. -/
theorem n_three_pairing_eq_zero (u : ℤ → ℝ) (hbot : u (-1) = 0) (htop : u 3 = 0) :
    u 0 * boussinesqTransferU 1 0 u 0 + u 1 * boussinesqTransferU 1 0 u 1
      + u 2 * boussinesqTransferU 1 0 u 2 = 0 := by
  have h := transfer_pairing_eq_zero u 3 hbot (by simpa using htop)
  simpa [Finset.sum_range_succ, Finset.sum_range_one] using h

end Cascade

/-! ## Axiom audit -/

#print axioms Cascade.selfSimilarMu
#print axioms Cascade.twist
#print axioms Cascade.reducedTransfer
#print axioms Cascade.reducedRHS
#print axioms Cascade.reducedEnstrophy
#print axioms Cascade.flipAt
#print axioms Cascade.cubicWitness
#print axioms Cascade.dyadicWeight_mul_neg
#print axioms Cascade.dyadicWeight_neg
#print axioms Cascade.selfSimilarMu_pos
#print axioms Cascade.selfSimilarMu_ne_zero
#print axioms Cascade.selfSimilarMu_closes
#print axioms Cascade.matching_multiplier_forced
#print axioms Cascade.transfer_matching
#print axioms Cascade.dyadicWeight_eq_one_iff
#print axioms Cascade.naive_closure_transfer_defect
#print axioms Cascade.twist_matching_iff
#print axioms Cascade.twist_not_dirichlet_top
#print axioms Cascade.selfSimilar_not_dirichlet
#print axioms Cascade.transfer_twist
#print axioms Cascade.hasDerivAt_const_mul_iff
#print axioms Cascade.twist_ode_iff
#print axioms Cascade.velocityRHSDegreeE_twist
#print axioms Cascade.twist_solves_iff
#print axioms Cascade.reducedEnstrophy_nonneg
#print axioms Cascade.twist_physical_enstrophy_term
#print axioms Cascade.twist_physical_enstrophy_periodic
#print axioms Cascade.twist_enstrophy
#print axioms Cascade.constant_profile_enstrophy_block
#print axioms Cascade.cyclic_shift_sum
#print axioms Cascade.cyclic_reindex
#print axioms Cascade.sum_reduced_pairing
#print axioms Cascade.reduced_enstrophy_hasDerivAt
#print axioms Cascade.reducedTransfer_const
#print axioms Cascade.reducedRHS_const
#print axioms Cascade.reduced_constant_ode
#print axioms Cascade.reduced_constant_ode_inviscid
#print axioms Cascade.selfSimilar_sub_one
#print axioms Cascade.selfSimilar_add_one
#print axioms Cascade.selfSimilar_scalar_hasDerivAt
#print axioms Cascade.twist_const_eq_selfSimilar
#print axioms Cascade.twist_const_zero
#print axioms Cascade.const_profile_solves_reduced
#print axioms Cascade.const_profile_twist_is_selfSimilar
#print axioms Cascade.const_profile_level_unbounded
#print axioms Cascade.selfSimilar_scalar_eq
#print axioms Cascade.const_profile_blowup
#print axioms Cascade.viscous_periodicity_iff
#print axioms Cascade.viscous_coefficient_periodic_zero
#print axioms Cascade.viscous_coefficient_not_periodic
#print axioms Cascade.e_two_not_closed
#print axioms Cascade.cubic_flip_sub
#print axioms Cascade.dirichlet_pairing_sign_blind
#print axioms Cascade.cubicWitness_value
#print axioms Cascade.cubicWitness_pos
#print axioms Cascade.cubicWitness_flip_sub
#print axioms Cascade.cubicWitness_flip_value
#print axioms Cascade.cubic_sign_sensitive
#print axioms Cascade.n_one_transfer_frozen
#print axioms Cascade.n_two_pairing_eq_zero
#print axioms Cascade.n_three_interior_triad
#print axioms Cascade.n_three_pairing_eq_zero
