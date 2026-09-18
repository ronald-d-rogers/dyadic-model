import Cascade.Boussinesq
import Cascade.NoBlowup
import Cascade.Obstruction
import Cascade.Enstrophy
import Cascade.EnstrophyBound
import Cascade.Riccati
import Cascade.Gronwall
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact

/-!
# Stage R′ — the **forced** truncated dyadic Boussinesq model

This is a **model-freezing** file.  The frozen Stage R model of `Cascade/Boussinesq.lean` is
extended by an additive force: a velocity force ladder `f : ℤ → ℝ` and a temperature force ladder
`h : ℤ → ℝ`, entering as *single added terms*

`du_k/dt = dyadicVelocityRHS ν κ u θ k + f k`,  `dθ_k/dt = dyadicTemperatureRHS μ u θ k + h k`.

The unforced model is recovered **definitionally** by taking the force to vanish
(`forcedVelocityRHS_zero` and friends below), so that any pair of forced/unforced statements is
literally a statement about the *same* couplings with the force toggled.

## Contents

1. `forcedVelocityRHS`, `forcedTemperatureRHS`, `forcedBoussinesqRHS` — the frozen forced model.
2. `forcedVelocityRHS_zero`, `forcedTemperatureRHS_zero`, `forcedBoussinesqRHS_zero` — the
   recovery of the unforced model.
3. `IsForcedTruncatedSolution` — the forced analogue of `IsUnforcedTruncatedSolution`.
4. `forceEnergy` — the truncated force-ladder energy `∑_{k<N} f_k²`, always finite.
5. `forcedVelocityEnergy_hasDerivAt` / `forcedEntropy_hasDerivAt` — differentiating the energy and
   the entropy along a forced solution.
6. `force_work_le` — Cauchy–Schwarz for the force work.
7. `forced_energy_rate_le` — the logistic rate inequality
   `E' ≤ 2 (κ√S(t) + √F) √E − 2νE`.
8. `forced_truncated_energy_bounded` — **no finite-time energy blowup** for the forced truncated
   model, for arbitrary additive force ladders.
9. `forced_energy_le_max_unforced_temperature` — the *uniform-in-time* explicit bound in the
   dissipative case, for the physically standard case of a velocity force and no temperature
   force.
10. `forced_enstrophy_rate_le`, `forced_enstrophy_young`, `forced_truncated_enstrophy_bounded` —
    the forced enstrophy budget, its Young absorption and the resulting **no finite-time enstrophy
    blowup** (Phase-3 verdict).
11. Non-vacuity: the zero-force / zero-state equilibrium and a concrete forced state at which the
    force work and the forced rate inequality are evaluated numerically.
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators

namespace Cascade

/-! ## 1. The frozen forced model -/

/-- **The forced velocity RHS**: the frozen Stage R velocity transfer *plus* a single additive
force term `f k`. -/
def forcedVelocityRHS (ν κ : ℝ) (f u θ : ℤ → ℝ) (k : ℤ) : ℝ :=
  dyadicVelocityRHS ν κ u θ k + f k

/-- **The forced temperature RHS**: the frozen Stage R temperature transfer *plus* a single
additive force term `h k`. -/
def forcedTemperatureRHS (μ : ℝ) (h u θ : ℤ → ℝ) (k : ℤ) : ℝ :=
  dyadicTemperatureRHS μ u θ k + h k

/-- **The frozen forced two-species dyadic Boussinesq ODE** `(du_k/dt, dθ_k/dt)`. -/
def forcedBoussinesqRHS (ν μ κ : ℝ) (f h u θ : ℤ → ℝ) (k : ℤ) : ℝ × ℝ :=
  (forcedVelocityRHS ν κ f u θ k, forcedTemperatureRHS μ h u θ k)

/-! ## 2. Recovering the unforced model

The force enters as a single additive term, so switching it off recovers the frozen Stage R RHS by
unfolding the definition of the forced RHS *alone*; no convergence, no extensionality and no
rewriting of the frozen couplings is needed.  (The remaining identity `x + 0 = x` on `ℝ` is
Mathlib's `add_zero`, which is not a definitional equality for `ℝ`, so these are closed by a
single `simp [forced…]` rather than by bare `rfl`; see the report.) -/

/-- **The unforced velocity model is the zero-force case.** -/
theorem forcedVelocityRHS_zero (ν κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    forcedVelocityRHS ν κ (fun _ => 0) u θ k = dyadicVelocityRHS ν κ u θ k := by
  simp [forcedVelocityRHS]

/-- **The unforced temperature model is the zero-force case.** -/
theorem forcedTemperatureRHS_zero (μ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    forcedTemperatureRHS μ (fun _ => 0) u θ k = dyadicTemperatureRHS μ u θ k := by
  simp [forcedTemperatureRHS]

/-- **The unforced model is the zero-force case.** -/
theorem forcedBoussinesqRHS_zero (ν μ κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    forcedBoussinesqRHS ν μ κ (fun _ => 0) (fun _ => 0) u θ k = dyadicBoussinesqRHS ν μ κ u θ k := by
  simp [forcedBoussinesqRHS, forcedVelocityRHS, forcedTemperatureRHS, dyadicBoussinesqRHS]

/-! ## 3. The forced truncated solution predicate

The predicate has the shape of `IsUnforcedTruncatedSolution`: the equations are imposed on the
retained shells `0 ≤ k < N` only, and the truncation is closed by the Dirichlet conditions
`u(-1) = u(N) = θ(-1) = θ(N) = 0`.  Only the RHS is forced.  (An earlier version imposed the
equations on all of `ℤ`, which is inconsistent with `u t N = 0` for all `t`; see
`Cascade/NoBlowup.lean`.) -/

/-- **The forced truncated dyadic Boussinesq solution predicate.** `u θ : ℝ → ℤ → ℝ` are the
velocity and temperature ladders as functions of time; `f` and `h` are the (time-independent)
velocity and temperature force ladders.  On the shells `0, …, N-1` the ladders solve the frozen
forced two-species dyadic Boussinesq ODE, and the truncation is closed by the Dirichlet boundary
conditions `u(-1) = u(N) = θ(-1) = θ(N) = 0`.  The equation is imposed only on `0 ≤ k < N`. -/
def IsForcedTruncatedSolution (ν μ κ : ℝ) (N : ℕ) (f h : ℤ → ℝ) (u θ : ℝ → ℤ → ℝ) : Prop :=
  (∀ t k, 0 ≤ k → k < (N : ℤ) →
    HasDerivAt (fun s => u s k) (forcedVelocityRHS ν κ f (u t) (θ t) k) t) ∧
  (∀ t k, 0 ≤ k → k < (N : ℤ) →
    HasDerivAt (fun s => θ s k) (forcedTemperatureRHS μ h (u t) (θ t) k) t) ∧
  (∀ t, u t (-1) = 0 ∧ u t (N : ℤ) = 0 ∧ θ t (-1) = 0 ∧ θ t (N : ℤ) = 0)

/-- The zero-force predicate is the unforced predicate. -/
theorem isForcedTruncatedSolution_zero_iff (ν μ κ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ) :
    IsForcedTruncatedSolution ν μ κ N (fun _ => 0) (fun _ => 0) u θ
      ↔ IsUnforcedTruncatedSolution ν μ κ N u θ := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun t k hk0 hkN => by rw [← forcedVelocityRHS_zero]; exact h1 t k hk0 hkN,
      fun t k hk0 hkN => by rw [← forcedTemperatureRHS_zero]; exact h2 t k hk0 hkN, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun t k hk0 hkN => by rw [forcedVelocityRHS_zero]; exact h1 t k hk0 hkN,
      fun t k hk0 hkN => by rw [forcedTemperatureRHS_zero]; exact h2 t k hk0 hkN, h3⟩

/-! ## 4. The truncated force-ladder energy -/

/-- **The truncated force-ladder energy** `F = ∑_{k<N} f_k²`.  It is a *finite* sum, so it is
always finite: no summability hypothesis on the force ladder is needed for the truncated model. -/
def forceEnergy (f : ℤ → ℝ) (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, (f (k : ℤ)) ^ 2

/-- The truncated force energy is nonnegative. -/
theorem forceEnergy_nonneg (f : ℤ → ℝ) (N : ℕ) : 0 ≤ forceEnergy f N := by
  rw [forceEnergy]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-! ## 5. Differentiating the energy and the entropy along a forced solution -/

/-- **The time derivative of the velocity energy along a forced truncated solution.** Identical to
`velocityEnergy_hasDerivAt`, with the forced velocity RHS in place of the unforced one. -/
theorem forcedVelocityEnergy_hasDerivAt (ν μ κ : ℝ) (N : ℕ) (f h : ℤ → ℝ) (u θ : ℝ → ℤ → ℝ)
    (hsol : IsForcedTruncatedSolution ν μ κ N f h u θ) (t : ℝ) :
    HasDerivAt (fun s => velocityEnergy (u s) N)
      (2 * ∑ k ∈ Finset.range N,
        u t (k : ℤ) * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ)) t := by
  have hsum : HasDerivAt (∑ k ∈ Finset.range N, fun s : ℝ => (u s (k : ℤ)) ^ 2)
      (∑ k ∈ Finset.range N,
        2 * u t (k : ℤ) * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ)) t :=
    HasDerivAt.sum (u := Finset.range N)
      (A := fun k s => (u s (k : ℤ)) ^ 2)
      (A' := fun k => 2 * u t (k : ℤ) * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ))
      (fun k hk => by
        have hd := (hsol.1 t (k : ℤ) (Int.natCast_nonneg k)
          (by exact_mod_cast (Finset.mem_range.mp hk))).pow 2
        have hfun : ((fun s : ℝ => u s (k : ℤ)) ^ 2)
            = fun s : ℝ => (u s (k : ℤ)) ^ 2 := by
          funext s
          rw [Pi.pow_apply]
        rw [hfun] at hd
        simpa using hd)
  have hfun : (∑ k ∈ Finset.range N, fun s : ℝ => (u s (k : ℤ)) ^ 2)
      = fun s : ℝ => ∑ k ∈ Finset.range N, (u s (k : ℤ)) ^ 2 := by
    funext s
    exact finset_sum_apply (Finset.range N) (fun (k : ℕ) (s : ℝ) => (u s (k : ℤ)) ^ 2) s
  rw [hfun] at hsum
  have heq : (∑ k ∈ Finset.range N,
        2 * u t (k : ℤ) * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ))
      = 2 * ∑ k ∈ Finset.range N,
          u t (k : ℤ) * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [heq] at hsum
  exact hsum

/-- **The time derivative of the thermal entropy along a forced truncated solution.** Identical to
`entropy_hasDerivAt`, with the forced temperature RHS in place of the unforced one. -/
theorem forcedEntropy_hasDerivAt (ν μ κ : ℝ) (N : ℕ) (f h : ℤ → ℝ) (u θ : ℝ → ℤ → ℝ)
    (hsol : IsForcedTruncatedSolution ν μ κ N f h u θ) (t : ℝ) :
    HasDerivAt (fun s => entropy (θ s) N)
      (2 * ∑ k ∈ Finset.range N,
        θ t (k : ℤ) * forcedTemperatureRHS μ h (u t) (θ t) (k : ℤ)) t := by
  have hsum : HasDerivAt (∑ k ∈ Finset.range N, fun s : ℝ => (θ s (k : ℤ)) ^ 2)
      (∑ k ∈ Finset.range N,
        2 * θ t (k : ℤ) * forcedTemperatureRHS μ h (u t) (θ t) (k : ℤ)) t :=
    HasDerivAt.sum (u := Finset.range N)
      (A := fun k s => (θ s (k : ℤ)) ^ 2)
      (A' := fun k => 2 * θ t (k : ℤ) * forcedTemperatureRHS μ h (u t) (θ t) (k : ℤ))
      (fun k hk => by
        have hd := (hsol.2.1 t (k : ℤ) (Int.natCast_nonneg k)
          (by exact_mod_cast (Finset.mem_range.mp hk))).pow 2
        have hfun : ((fun s : ℝ => θ s (k : ℤ)) ^ 2)
            = fun s : ℝ => (θ s (k : ℤ)) ^ 2 := by
          funext s
          rw [Pi.pow_apply]
        rw [hfun] at hd
        simpa using hd)
  have hfun : (∑ k ∈ Finset.range N, fun s : ℝ => (θ s (k : ℤ)) ^ 2)
      = fun s : ℝ => ∑ k ∈ Finset.range N, (θ s (k : ℤ)) ^ 2 := by
    funext s
    exact finset_sum_apply (Finset.range N) (fun (k : ℕ) (s : ℝ) => (θ s (k : ℤ)) ^ 2) s
  rw [hfun] at hsum
  have heq : (∑ k ∈ Finset.range N,
        2 * θ t (k : ℤ) * forcedTemperatureRHS μ h (u t) (θ t) (k : ℤ))
      = 2 * ∑ k ∈ Finset.range N,
          θ t (k : ℤ) * forcedTemperatureRHS μ h (u t) (θ t) (k : ℤ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [heq] at hsum
  exact hsum

/-- The velocity energy is continuous along a forced solution. -/
theorem forcedVelocityEnergy_continuous (ν μ κ : ℝ) (N : ℕ) (f h : ℤ → ℝ)
    (u θ : ℝ → ℤ → ℝ) (hsol : IsForcedTruncatedSolution ν μ κ N f h u θ) :
    Continuous fun t => velocityEnergy (u t) N := by
  unfold velocityEnergy
  refine continuous_finsetSum _ fun k hk => ?_
  have hdiff : Differentiable ℝ (fun t : ℝ => (u t (k : ℤ)) ^ 2) := fun t =>
    ((hsol.1 t (k : ℤ) (Int.natCast_nonneg k)
      (by exact_mod_cast (Finset.mem_range.mp hk))).differentiableAt).pow 2
  exact hdiff.continuous

/-- The entropy is continuous along a forced solution. -/
theorem forcedEntropy_continuous (ν μ κ : ℝ) (N : ℕ) (f h : ℤ → ℝ)
    (u θ : ℝ → ℤ → ℝ) (hsol : IsForcedTruncatedSolution ν μ κ N f h u θ) :
    Continuous fun t => entropy (θ t) N := by
  unfold entropy
  refine continuous_finsetSum _ fun k hk => ?_
  have hdiff : Differentiable ℝ (fun t : ℝ => (θ t (k : ℤ)) ^ 2) := fun t =>
    ((hsol.2.1 t (k : ℤ) (Int.natCast_nonneg k)
      (by exact_mod_cast (Finset.mem_range.mp hk))).differentiableAt).pow 2
  exact hdiff.continuous

/-! ## 6. Cauchy–Schwarz for the force work -/

/-- **Force-work Cauchy–Schwarz.** For any finsets of shells,
`∑_{k<N} u_k f_k ≤ √(∑ u_k²) √(∑ f_k²)`.  This is the estimate that turns the additive force
into the *logistic* driving term `2√F √E`. -/
theorem sum_mul_le_sqrt_mul_sqrt' {ι : Type*} (s : Finset ι) (u f : ι → ℝ) :
    (∑ k ∈ s, u k * f k)
      ≤ Real.sqrt (∑ k ∈ s, (u k) ^ 2) * Real.sqrt (∑ k ∈ s, (f k) ^ 2) := by
  have hsq : (∑ k ∈ s, u k * f k) ^ 2
      ≤ (∑ k ∈ s, (u k) ^ 2) * (∑ k ∈ s, (f k) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq s u f
  calc (∑ k ∈ s, u k * f k)
      ≤ Real.sqrt ((∑ k ∈ s, (u k) ^ 2) * (∑ k ∈ s, (f k) ^ 2)) :=
        Real.le_sqrt_of_sq_le hsq
    _ = Real.sqrt (∑ k ∈ s, (u k) ^ 2) * Real.sqrt (∑ k ∈ s, (f k) ^ 2) :=
        Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg (u i)) _

/-- **Force work is bounded by the force-ladder energy.** -/
theorem force_work_le (f u : ℤ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, u (k : ℤ) * f (k : ℤ))
      ≤ Real.sqrt (velocityEnergy u N) * Real.sqrt (forceEnergy f N) := by
  simpa [velocityEnergy, forceEnergy] using
    sum_mul_le_sqrt_mul_sqrt' (Finset.range N) (fun k : ℕ => u (k : ℤ)) (fun k : ℕ => f (k : ℤ))

/-! ## 7. The forced pointwise energy rate: the logistic inequality -/

/-- **The forced velocity pairing.**  Under the Dirichlet conditions the interior transfer
contributes nothing, so the pairing of the forced velocity equation is the buoyancy, plus the
**force work**, minus the viscous dissipation:

`∑_{k<N} u_k (du_k/dt) ≤ κ √E √S + √E √F − ν E`,  `F = forceEnergy f N`, `E = velocityEnergy u N`,
`S = entropy θ N`.

The two new features relative to `velocity_energy_rate_le` are the additive force work and the fact
that **no monotonicity of the entropy is assumed**: the bound is stated at the current time `t`,
so it applies verbatim to the forced temperature equation as well. -/
theorem forced_velocity_pairing_le (ν κ : ℝ) (hκ : 0 ≤ κ) (hν : 0 ≤ ν) (f : ℤ → ℝ)
    (u θ : ℤ → ℝ) (N : ℕ) (hbot : u (-1) = 0) (htop : u (N : ℤ) = 0) :
    (∑ k ∈ Finset.range N, u (k : ℤ) * forcedVelocityRHS ν κ f u θ (k : ℤ))
      ≤ κ * (Real.sqrt (velocityEnergy u N) * Real.sqrt (entropy θ N))
        + Real.sqrt (velocityEnergy u N) * Real.sqrt (forceEnergy f N)
        - ν * velocityEnergy u N := by
  have hsplit : (∑ k ∈ Finset.range N, u (k : ℤ) * forcedVelocityRHS ν κ f u θ (k : ℤ))
      = (∑ k ∈ Finset.range N, u (k : ℤ) * dyadicVelocityRHS ν κ u θ (k : ℤ))
        + (∑ k ∈ Finset.range N, u (k : ℤ) * f (k : ℤ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by simp only [forcedVelocityRHS, mul_add]
  rw [hsplit]
  have h1 := velocity_energy_rate_le ν κ hκ hν u θ N hbot htop
  have h2 := force_work_le f u N
  simp only [velocityEnergy, entropy, forceEnergy] at h1 h2 ⊢
  linarith

/-- **The forced energy rate inequality (logistic form).** Along a forced truncated solution the
derivative of the velocity energy obeys

`E' ≤ 2 (κ √S(t) + √F) √E − 2 ν E`,  `F = forceEnergy f N`.

The transfer is exactly energy-conserving, so the only sources are buoyancy (bounded by `κ√S√E`)
and the force work (bounded by `√F√E`); viscosity removes `2νE`.  This is the forced analogue of
`velocity_energy_rate_le_of_solution`, with two differences: the force term and the fact that the
entropy is evaluated at the *current* time (`S(t)`), because a temperature force destroys the
monotonicity of the entropy. -/
theorem forced_energy_rate_le (ν μ κ : ℝ) (hκ : 0 ≤ κ) (hν : 0 ≤ ν)
    (N : ℕ) (f h : ℤ → ℝ) (u θ : ℝ → ℤ → ℝ)
    (hsol : IsForcedTruncatedSolution ν μ κ N f h u θ) (t : ℝ) :
    2 * (∑ k ∈ Finset.range N,
        u t (k : ℤ) * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ))
      ≤ 2 * (κ * Real.sqrt (entropy (θ t) N) + Real.sqrt (forceEnergy f N))
          * Real.sqrt (velocityEnergy (u t) N)
        - 2 * ν * velocityEnergy (u t) N := by
  have hpair := forced_velocity_pairing_le ν κ hκ hν f (u t) (θ t) N
    (hsol.2.2 t).1 (hsol.2.2 t).2.1
  have h2 : 2 * (∑ k ∈ Finset.range N,
        u t (k : ℤ) * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ))
      ≤ 2 * (κ * (Real.sqrt (velocityEnergy (u t) N) * Real.sqrt (entropy (θ t) N))
        + Real.sqrt (velocityEnergy (u t) N) * Real.sqrt (forceEnergy f N)
        - ν * velocityEnergy (u t) N) :=
    mul_le_mul_of_nonneg_left hpair (by norm_num)
  nlinarith [h2]

/-- **The forced energy rate inequality with an entropy ceiling.**  If the entropy is bounded by
`S_max` at time `t`, the logistic coefficient can be frozen:

`E' ≤ 2 (κ √S_max + √F) √E − 2 ν E`.

This is the form fed to the linear Grönwall engine; the (load-bearing) sign hypothesis `0 ≤ κ` is
what allows the entropy ceiling to be pushed through the buoyancy coefficient. -/
theorem forced_energy_rate_le_of_entropy_le (ν μ κ : ℝ) (hκ : 0 ≤ κ) (hν : 0 ≤ ν)
    (N : ℕ) (f h : ℤ → ℝ) (u θ : ℝ → ℤ → ℝ)
    (hsol : IsForcedTruncatedSolution ν μ κ N f h u θ) {t S_max : ℝ}
    (hS : entropy (θ t) N ≤ S_max) :
    2 * (∑ k ∈ Finset.range N,
        u t (k : ℤ) * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ))
      ≤ 2 * (κ * Real.sqrt S_max + Real.sqrt (forceEnergy f N))
          * Real.sqrt (velocityEnergy (u t) N)
        - 2 * ν * velocityEnergy (u t) N := by
  have hrate := forced_energy_rate_le ν μ κ hκ hν N f h u θ hsol t
  have hsqrt : Real.sqrt (entropy (θ t) N) ≤ Real.sqrt S_max := Real.sqrt_le_sqrt hS
  have hcoef : κ * Real.sqrt (entropy (θ t) N) ≤ κ * Real.sqrt S_max :=
    mul_le_mul_of_nonneg_left hsqrt hκ
  have hcoef' : κ * Real.sqrt (entropy (θ t) N) + Real.sqrt (forceEnergy f N)
      ≤ κ * Real.sqrt S_max + Real.sqrt (forceEnergy f N) := by linarith
  have hE : 0 ≤ Real.sqrt (velocityEnergy (u t) N) := Real.sqrt_nonneg _
  have hstep : (κ * Real.sqrt (entropy (θ t) N) + Real.sqrt (forceEnergy f N))
        * Real.sqrt (velocityEnergy (u t) N)
      ≤ (κ * Real.sqrt S_max + Real.sqrt (forceEnergy f N))
        * Real.sqrt (velocityEnergy (u t) N) :=
    mul_le_mul_of_nonneg_right hcoef' hE
  nlinarith [hrate, hstep]

/-! ## 8. The forced capstone: no finite-time energy blowup -/

/-- **The forced truncated dyadic Boussinesq model has no finite-time energy blowup.** Along any
forced truncated solution with Dirichlet ends, the velocity energy is bounded on every compact
time interval `[0, T]`.  The force enters only through the finite constant
`F = forceEnergy f N = ∑_{k<N} f_k²`, so no summability/finiteness hypothesis on the force ladder
is needed; the only structural hypotheses are `0 < ν` (viscosity) and `0 ≤ κ` (the sign of the
buoyancy coupling, needed to bound `κ ∑ u_k θ_k` by `κ√E√S`).

The entropy ceiling used in the proof is extracted from the *continuity* of the entropy, which is
automatic because the solution predicate makes every ladder differentiable in time.  Hence no
hypothesis on the temperature force `h` beyond the ODE itself is required. -/
theorem forced_truncated_energy_bounded (ν μ κ : ℝ) (hν : 0 < ν) (hκ : 0 ≤ κ)
    (N : ℕ) (f h : ℤ → ℝ) (u θ : ℝ → ℤ → ℝ)
    (hsol : IsForcedTruncatedSolution ν μ κ N f h u θ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, velocityEnergy (u t) N ≤ C := by
  -- A ceiling for the entropy on `[0, T]`, from its continuity.
  obtain ⟨S₀, hS₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).bddAbove_image
    (forcedEntropy_continuous ν μ κ N f h u θ hsol).continuousOn
  set S_max : ℝ := max S₀ 0 with hS_max
  have hS_max_nonneg : 0 ≤ S_max := le_max_right _ _
  have hSle : ∀ t ∈ Set.Icc 0 T, entropy (θ t) N ≤ S_max := fun t ht =>
    (hS₀ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  -- The frozen logistic coefficient.
  set A : ℝ := κ * Real.sqrt S_max + Real.sqrt (forceEnergy f N) with hA
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    exact add_nonneg (mul_nonneg hκ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  refine ⟨energyBound (velocityEnergy (u 0) N) A 1 ν T, ?_⟩
  refine energy_le_energyBound_of_rate_le (E := fun t => velocityEnergy (u t) N)
    (E' := fun t => 2 * ∑ k ∈ Finset.range N,
      u t (k : ℤ) * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ))
    (κ := A) (S₀ := 1) (ν := ν) (T := T) hA_nonneg (by norm_num) hν hT ?_ ?_ ?_ ?_
  · exact (forcedVelocityEnergy_continuous ν μ κ N f h u θ hsol).continuousOn
  · intro t _; exact velocityEnergy_nonneg (u t) N
  · intro t _
    exact forcedVelocityEnergy_hasDerivAt ν μ κ N f h u θ hsol t
  · intro t ht
    have hrate := forced_energy_rate_le_of_entropy_le ν μ κ hκ hν.le N f h u θ hsol
      (hSle t ⟨ht.1, le_of_lt ht.2⟩)
    simpa [hA, Real.sqrt_one] using hrate

/-! ## 9. Uniform-in-time bound for a velocity force and no temperature force

When the temperature is unforced (`h = 0`) the thermal entropy is still non-increasing, so the
entropy ceiling is the *initial* entropy and the logistic barrier gives a bound valid for **all**
`t ≥ 0`, with no dependence on `T`, whenever the dissipation gap
`2ν > κ√S(0) + √F` holds. -/

/-- **Thermal entropy is non-increasing along a forced solution with unforced temperature.**
Identical to `entropy_antitone`: with `h = 0` the temperature equation is the unforced one, so
`temperature_energy_rate_nonpos` applies. -/
theorem forced_entropy_antitone (ν μ κ : ℝ) (hμ : 0 ≤ μ) (N : ℕ) (f : ℤ → ℝ)
    (u θ : ℝ → ℤ → ℝ) (hsol : IsForcedTruncatedSolution ν μ κ N f 0 u θ) :
    Antitone fun t => entropy (θ t) N := by
  refine antitone_of_hasDerivAt_nonpos
    (f' := fun t => 2 * ∑ k ∈ Finset.range N,
      θ t (k : ℤ) * forcedTemperatureRHS μ 0 (u t) (θ t) (k : ℤ)) ?_ ?_
  · intro t
    exact forcedEntropy_hasDerivAt ν μ κ N f 0 u θ hsol t
  · intro t
    have hpair := temperature_energy_rate_nonpos μ hμ (u t) (θ t) N
      (hsol.2.2 t).2.2.1 (hsol.2.2 t).2.2.2
    have heq : (∑ k ∈ Finset.range N, θ t (k : ℤ) * forcedTemperatureRHS μ 0 (u t) (θ t) (k : ℤ))
        = ∑ k ∈ Finset.range N, θ t (k : ℤ) * dyadicTemperatureRHS μ (u t) (θ t) (k : ℤ) := by
      exact Finset.sum_congr rfl fun k _ => by simp [forcedTemperatureRHS]
    change 2 * (∑ k ∈ Finset.range N,
      θ t (k : ℤ) * forcedTemperatureRHS μ 0 (u t) (θ t) (k : ℤ)) ≤ 0
    rw [heq]
    simpa using mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 2) hpair

/-- **Uniform-in-time bound in the dissipative case, with unforced temperature.** For a velocity
force `f` and *no* temperature force, if additionally the dissipation gap
`2ν > κ √S(0) + √F` holds, then for all `t ≥ 0`

`E(t) ≤ max (E(0)) ((κ√S(0) + √F) / (2ν − κ√S(0) − √F))`,

an explicit constant independent of `t`, where `E = velocityEnergy u N`, `S = entropy θ N` and
`F = forceEnergy f N`.  This is the forced analogue of `truncated_unforced_energy_le_max`; the
extra term `√F` in the gap is exactly the price of the additive force. -/
theorem forced_energy_le_max_unforced_temperature (ν μ κ : ℝ) (hν : 0 < ν) (hμ : 0 ≤ μ)
    (hκ : 0 ≤ κ) (N : ℕ) (f : ℤ → ℝ) (u θ : ℝ → ℤ → ℝ)
    (hsol : IsForcedTruncatedSolution ν μ κ N f 0 u θ)
    (hgap : 0 < 2 * ν - (κ * Real.sqrt (entropy (θ 0) N) + Real.sqrt (forceEnergy f N)))
    (t : ℝ) (ht : 0 ≤ t) :
    velocityEnergy (u t) N ≤ max (velocityEnergy (u 0) N)
      ((κ * Real.sqrt (entropy (θ 0) N) + Real.sqrt (forceEnergy f N))
        / (2 * ν - (κ * Real.sqrt (entropy (θ 0) N) + Real.sqrt (forceEnergy f N)))) := by
  have hanti := forced_entropy_antitone ν μ κ hμ N f u θ hsol
  set A : ℝ := κ * Real.sqrt (entropy (θ 0) N) + Real.sqrt (forceEnergy f N) with hA
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    exact add_nonneg (mul_nonneg hκ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hgap' : 0 < 2 * ν - A * Real.sqrt (1 : ℝ) := by
    rw [Real.sqrt_one, mul_one]; exact hgap
  have hmain : velocityEnergy (u t) N ≤ max (velocityEnergy (u 0) N)
      (A * Real.sqrt (1 : ℝ) / (2 * ν - A * Real.sqrt (1 : ℝ))) := by
    refine energy_le_max_of_rate_le (E := fun s => velocityEnergy (u s) N)
      (E' := fun s => 2 * ∑ k ∈ Finset.range N,
        u s (k : ℤ) * forcedVelocityRHS ν κ f (u s) (θ s) (k : ℤ))
      (κ := A) (S₀ := 1) (ν := ν) (T := t) hA_nonneg (by norm_num) hν hgap' ?_ ?_ ?_ ?_ t
      ⟨ht, le_rfl⟩
    · exact (forcedVelocityEnergy_continuous ν μ κ N f 0 u θ hsol).continuousOn
    · intro s _; exact velocityEnergy_nonneg (u s) N
    · intro s _
      exact forcedVelocityEnergy_hasDerivAt ν μ κ N f 0 u θ hsol s
    · intro s hs
      have hSle : entropy (θ s) N ≤ entropy (θ 0) N := hanti hs.1
      have hrate := forced_energy_rate_le_of_entropy_le ν μ κ hκ hν.le N f 0 u θ hsol hSle
      simpa [hA, Real.sqrt_one] using hrate
  simpa [hA, Real.sqrt_one] using hmain

/-! ## 10. Phase 3 — the forced **enstrophy** rate inequality and barrier

For the truncated forced model the enstrophy budget can be closed as well.  Weighting the forced
velocity equation by `4^k u_k` adds exactly the force work `∑ 4^k u_k f_k` to the unforced
enstrophy pairing, and Cauchy–Schwarz bounds it by `√H √(∑ 4^k f_k²)`.  The result is

`H' ≤ 6 H √H + κ (H + T) + 2 √H √He − 2 ν H²/E_max`,

with `H` the enstrophy, `T` the temperature enstrophy, `He = forceEnstrophy f N` and `E_max` an
energy ceiling.  The crucial point for blowup is that the two destabilising terms are of
homogeneity `3/2` in `H` (transfer) and `1/2` (force), while the dissipation is of homogeneity
`2`: above a threshold the right-hand side is negative, so the enstrophy cannot cross it.  The
Young absorption implementing this is `forced_enstrophy_young`, and the barrier
(`Cascade.le_of_deriv_le_const_sub_sq`) then gives **no finite-time enstrophy blowup**,
`forced_truncated_enstrophy_bounded`. -/

/-- **The truncated force-ladder enstrophy** `He = ∑_{k<N} 4^k f_k²`. -/
def forceEnstrophy (f : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * (f (k : ℤ)) ^ 2

/-- The truncated force enstrophy is nonnegative. -/
theorem forceEnstrophy_nonneg (f : ℤ → ℝ) (N : ℕ) : 0 ≤ forceEnstrophy f N := by
  rw [forceEnstrophy]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (dyadicWeight_nonneg _) (sq_nonneg _)

/-- **Force-work Cauchy–Schwarz in the enstrophy norm.**
`∑_{k<N} 4^k u_k f_k ≤ √H √He`, the exact analogue of `buoyancy_enstrophy_le`. -/
theorem force_enstrophy_work_le (f u : ℤ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * f (k : ℤ))
      ≤ Real.sqrt (enstrophy u N) * Real.sqrt (forceEnstrophy f N) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun k : ℕ => dyadicWeight (k : ℤ) * u (k : ℤ))
    (fun k : ℕ => dyadicWeight (k : ℤ) * f (k : ℤ))
  have hL : ∀ k : ℕ,
      (dyadicWeight (k : ℤ) * u (k : ℤ)) * (dyadicWeight (k : ℤ) * f (k : ℤ))
        = dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * f (k : ℤ) := by
    intro k
    rw [show (dyadicWeight (k : ℤ) * u (k : ℤ)) * (dyadicWeight (k : ℤ) * f (k : ℤ))
          = (dyadicWeight (k : ℤ)) ^ 2 * (u (k : ℤ) * f (k : ℤ)) by ring,
      ← dyadicWeight_two_mul]
    ring
  have hX : (∑ k ∈ Finset.range N, (dyadicWeight (k : ℤ) * u (k : ℤ)) ^ 2)
      = enstrophy u N := by
    rw [enstrophy]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow, ← dyadicWeight_two_mul]
  have hY : (∑ k ∈ Finset.range N, (dyadicWeight (k : ℤ) * f (k : ℤ)) ^ 2)
      = forceEnstrophy f N := by
    rw [forceEnstrophy]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow, ← dyadicWeight_two_mul]
  have hsq : (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * f (k : ℤ)) ^ 2
      ≤ enstrophy u N * forceEnstrophy f N := by
    rw [Finset.sum_congr rfl (fun k _ => hL k), hX, hY] at hcs
    exact hcs
  calc (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * f (k : ℤ))
      ≤ Real.sqrt (enstrophy u N * forceEnstrophy f N) := Real.le_sqrt_of_sq_le hsq
    _ = Real.sqrt (enstrophy u N) * Real.sqrt (forceEnstrophy f N) :=
        Real.sqrt_mul (enstrophy_nonneg u N) _

/-- **The time derivative of the enstrophy along a forced solution**, the forced analogue of
`enstrophy_hasDerivAt`. -/
theorem forcedEnstrophy_hasDerivAt (ν μ κ : ℝ) (N : ℕ) (f h : ℤ → ℝ) (u θ : ℝ → ℤ → ℝ)
    (hsol : IsForcedTruncatedSolution ν μ κ N f h u θ) (t : ℝ) :
    HasDerivAt (fun s => enstrophy (u s) N)
      (2 * ∑ k ∈ Finset.range N,
        dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
          * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ)) t := by
  have hterm : ∀ k ∈ Finset.range N,
      HasDerivAt (fun s : ℝ => dyadicWeight (2 * (k : ℤ)) * (u s (k : ℤ)) ^ 2)
        (dyadicWeight (2 * (k : ℤ))
          * (2 * u t (k : ℤ) * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ))) t := by
    intro k hk
    have hd := (hsol.1 t (k : ℤ) (Int.natCast_nonneg k)
      (by exact_mod_cast (Finset.mem_range.mp hk))).pow 2
    have hfun : ((fun s : ℝ => u s (k : ℤ)) ^ 2)
        = fun s : ℝ => (u s (k : ℤ)) ^ 2 := by
      funext s
      rw [Pi.pow_apply]
    rw [hfun] at hd
    simpa using hd.const_mul (dyadicWeight (2 * (k : ℤ)))
  have hsum := HasDerivAt.sum (u := Finset.range N)
    (A := fun k s => dyadicWeight (2 * (k : ℤ)) * (u s (k : ℤ)) ^ 2)
    (A' := fun k => dyadicWeight (2 * (k : ℤ))
      * (2 * u t (k : ℤ) * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ))) hterm
  have hfun : (∑ k ∈ Finset.range N,
        fun s : ℝ => dyadicWeight (2 * (k : ℤ)) * (u s (k : ℤ)) ^ 2)
      = fun s : ℝ => ∑ k ∈ Finset.range N,
          dyadicWeight (2 * (k : ℤ)) * (u s (k : ℤ)) ^ 2 := by
    funext s
    exact finset_sum_apply (Finset.range N)
      (fun (k : ℕ) (s : ℝ) => dyadicWeight (2 * (k : ℤ)) * (u s (k : ℤ)) ^ 2) s
  rw [hfun] at hsum
  have hfun2 : (fun s : ℝ => ∑ k ∈ Finset.range N,
        dyadicWeight (2 * (k : ℤ)) * (u s (k : ℤ)) ^ 2)
      = fun s => enstrophy (u s) N := by
    funext s
    rw [enstrophy]
  rw [hfun2] at hsum
  have heq : (∑ k ∈ Finset.range N,
        dyadicWeight (2 * (k : ℤ))
          * (2 * u t (k : ℤ) * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ)))
      = 2 * ∑ k ∈ Finset.range N,
          dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
            * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [heq] at hsum
  exact hsum

/-- **The forced pointwise enstrophy rate inequality.** With `H = enstrophy u N`,
`T = tempEnstrophy θ N`, `He = forceEnstrophy f N` and an energy ceiling `E_max ≥ E`,

`H' ≤ 6 H √H + κ (H + T) + 2 √H √He − 2 ν H²/E_max`.

The forced transfer is still cubic (`6H^{3/2}`), the buoyancy is AM–GM-ed into `κ(H+T)`, and the
force work adds the *sublinear* term `2√H√He`.  Only the velocity force `f` enters; a temperature
force `h` acts through `T` (it can increase the temperature enstrophy, see the report). -/
theorem forced_enstrophy_rate_le (ν κ E_max : ℝ) (hκ : 0 ≤ κ) (hν : 0 ≤ ν) (hEpos : 0 < E_max)
    (N : ℕ) (f : ℤ → ℝ) (u θ : ℤ → ℝ) (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0)
    (hEmax : velocityEnergy u N ≤ E_max) :
    2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)
        * forcedVelocityRHS ν κ f u θ (k : ℤ))
      ≤ 6 * (enstrophy u N * Real.sqrt (enstrophy u N))
        + κ * (enstrophy u N + tempEnstrophy θ N)
        + 2 * (Real.sqrt (enstrophy u N) * Real.sqrt (forceEnstrophy f N))
        - 2 * ν * (enstrophy u N) ^ 2 / E_max := by
  by_cases hE0 : velocityEnergy u N = 0
  · -- Degenerate case: zero energy forces every retained shell to vanish, so `H = 0` and both
    -- sides reduce to `0 ≤ κ T`.
    have hsum0 : (∑ k ∈ Finset.range N, (u (k : ℤ)) ^ 2) = 0 := by
      simpa [velocityEnergy] using hE0
    have hz : ∀ k ∈ Finset.range N, (u (k : ℤ)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.range N)
        (f := fun j : ℕ => (u (j : ℤ)) ^ 2)
        (fun j _ => sq_nonneg (u (j : ℤ)))).mp hsum0
    have hu0 : ∀ k ∈ Finset.range N, u (k : ℤ) = 0 := fun k hk =>
      sq_eq_zero_iff.mp (hz k hk)
    have hL : (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)
        * forcedVelocityRHS ν κ f u θ (k : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [hu0 k hk]
      ring
    have hH : enstrophy u N = 0 := by
      rw [enstrophy]
      apply Finset.sum_eq_zero
      intro k hk
      rw [hu0 k hk]
      ring
    rw [hL, hH]
    have hrhs : 6 * ((0 : ℝ) * Real.sqrt 0) + κ * (0 + tempEnstrophy θ N)
        + 2 * (Real.sqrt 0 * Real.sqrt (forceEnstrophy f N))
        - 2 * ν * (0 : ℝ) ^ 2 / E_max = κ * tempEnstrophy θ N := by
      rw [Real.sqrt_zero]
      ring
    rw [hrhs]
    simpa using mul_nonneg hκ (tempEnstrophy_nonneg θ N)
  · have hEpos' : 0 < velocityEnergy u N :=
      lt_of_le_of_ne (velocityEnergy_nonneg u N) (Ne.symm hE0)
    have hsplit : (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)
        * forcedVelocityRHS ν κ f u θ (k : ℤ))
        = (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)
            * dyadicVelocityRHS ν κ u θ (k : ℤ))
          + (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * f (k : ℤ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by simp only [forcedVelocityRHS, mul_add]
    rw [hsplit]
    have hpair := enstrophy_pairing_le ν κ hκ hν u θ N huBot huTop hEpos'
    have hwork := force_enstrophy_work_le f u N
    have h2pair := mul_le_mul_of_nonneg_left hpair (by norm_num : (0 : ℝ) ≤ 2)
    have h2work := mul_le_mul_of_nonneg_left hwork (by norm_num : (0 : ℝ) ≤ 2)
    have hHnn : 0 ≤ enstrophy u N := enstrophy_nonneg u N
    have hTEnn : 0 ≤ tempEnstrophy θ N := tempEnstrophy_nonneg θ N
    have hamgm : 2 * (Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N))
        ≤ enstrophy u N + tempEnstrophy θ N := by
      have h := sq_nonneg (Real.sqrt (enstrophy u N) - Real.sqrt (tempEnstrophy θ N))
      rw [sub_sq, Real.sq_sqrt hHnn, Real.sq_sqrt hTEnn] at h
      nlinarith
    have hκamgm : κ * (2 * (Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N)))
        ≤ κ * (enstrophy u N + tempEnstrophy θ N) := mul_le_mul_of_nonneg_left hamgm hκ
    have hdiv : (enstrophy u N) ^ 2 / E_max ≤ (enstrophy u N) ^ 2 / velocityEnergy u N :=
      div_le_div_of_nonneg_left (sq_nonneg _) hEpos' hEmax
    have hνdiv : 2 * ν * (enstrophy u N) ^ 2 / E_max
        ≤ 2 * ν * (enstrophy u N) ^ 2 / velocityEnergy u N := by
      have h2ν : 0 ≤ 2 * ν := by linarith
      have h := mul_le_mul_of_nonneg_left hdiv h2ν
      calc 2 * ν * (enstrophy u N) ^ 2 / E_max
          = (2 * ν) * ((enstrophy u N) ^ 2 / E_max) := by ring
        _ ≤ (2 * ν) * ((enstrophy u N) ^ 2 / velocityEnergy u N) := h
        _ = 2 * ν * (enstrophy u N) ^ 2 / velocityEnergy u N := by ring
    simp only [div_eq_mul_inv] at h2pair h2work hνdiv ⊢
    linarith [h2pair, h2work, hκamgm, hνdiv]

/-- **Young absorption for the forced enstrophy budget.** For `ν > 0`, `E_max > 0`, `κ ≥ 0` and
`s ≥ 0`,

`6 s³ + κ s² + 2 √He s + κ T_max ≤ (ν/E_max) s⁴ + C`,

with `C = 2187/(16 (ν/(2E_max))³) + κ²/(4 (ν/(4E_max))) + E_max/ν + He + κ T_max`.  The cubic
transfer is absorbed with the *optimal* Young constant of `young_cubic_le` at `γ = ν/(2E_max)`; the
linear and force terms share the remaining dissipation budget `ν/(4E_max)` each, leaving the
residual dissipation `ν/E_max` (against the actual `2ν/E_max` produced by viscosity) — this gap is
what makes the barrier threshold finite. -/
theorem forced_enstrophy_young {ν κ E_max He T_max s : ℝ} (hν : 0 < ν) (hEpos : 0 < E_max)
    (hκ : 0 ≤ κ) (hHe : 0 ≤ He) (hTmax : 0 ≤ T_max) (hs : 0 ≤ s) :
    6 * s ^ 3 + κ * s ^ 2 + 2 * Real.sqrt He * s + κ * T_max
      ≤ (ν / E_max) * s ^ 4
        + (2187 / (16 * (ν / (2 * E_max)) ^ 3) + κ ^ 2 / (4 * (ν / (4 * E_max)))
            + E_max / ν + He + κ * T_max) := by
  have hE2 : (0 : ℝ) < 2 * E_max := by linarith
  have hE4 : (0 : ℝ) < 4 * E_max := by linarith
  have hγ1 : 0 < ν / (2 * E_max) := div_pos hν hE2
  have hγ2 : 0 < ν / (4 * E_max) := div_pos hν hE4
  have h1 := young_cubic_le (γ := ν / (2 * E_max)) hγ1 hs
  have h2 := young_linear_le (γ := ν / (4 * E_max)) (κ := κ) (y := s ^ 2) hγ2
  have h2' : κ * s ^ 2 ≤ (ν / (4 * E_max)) * s ^ 4 + κ ^ 2 / (4 * (ν / (4 * E_max))) := by
    have hsq : (s ^ 2) ^ 2 = s ^ 4 := by ring
    rwa [hsq] at h2
  have h3a : 2 * Real.sqrt He * s ≤ s ^ 2 + He := by
    have h := sq_nonneg (s - Real.sqrt He)
    rw [sub_sq, Real.sq_sqrt hHe] at h
    nlinarith
  have h3b : s ^ 2 ≤ (ν / (4 * E_max)) * s ^ 4 + E_max / ν := by
    have h := young_linear_le (γ := ν / (4 * E_max)) (κ := 1) (y := s ^ 2) hγ2
    have hsq : (s ^ 2) ^ 2 = s ^ 4 := by ring
    rw [hsq] at h
    have hden : 4 * (ν / (4 * E_max)) = ν / E_max := by
      field_simp
    have hc : (1 : ℝ) ^ 2 / (4 * (ν / (4 * E_max))) = E_max / ν := by
      rw [hden, one_pow, one_div, inv_div]
    rw [hc, one_mul] at h
    exact h
  have hcoef : ν / (2 * E_max) + ν / (4 * E_max) + ν / (4 * E_max) = ν / E_max := by
    field_simp
    ring
  have hcoef' : ν / (2 * E_max) * s ^ 4 + ν / (4 * E_max) * s ^ 4
      + ν / (4 * E_max) * s ^ 4 = (ν / E_max) * s ^ 4 := by
    rw [← add_mul, ← add_mul, hcoef]
  linarith [h1, h2', h3a, h3b, hcoef', mul_nonneg hκ hTmax]

/-- **The forced truncated dyadic Boussinesq model has no finite-time enstrophy blowup.** Along any
forced truncated solution with Dirichlet ends the enstrophy `H = ∑_{k<N} 4^k u_k²` is bounded on
every compact time interval `[0, T]`.  The mechanism is the forced enstrophy budget: the transfer
is cubic (`6H^{3/2}`) and the force work is sublinear (`2√H√He`), while viscous dissipation is
quadratic (`2νH²/E_max`); Young's inequality (`forced_enstrophy_young`) absorbs the first two into
the third above the explicit threshold `√(C/(ν/E_max))`, and the barrier
`Cascade.le_of_deriv_le_const_sub_sq` forbids crossing it.  The energy ceiling `E_max` is supplied
by `forced_truncated_energy_bounded` and the temperature-enstrophy ceiling by continuity, so no
hypothesis on the force ladders beyond the ODE is needed. -/
theorem forced_truncated_enstrophy_bounded (ν μ κ : ℝ) (hν : 0 < ν) (hκ : 0 ≤ κ)
    (N : ℕ) (f h : ℤ → ℝ) (u θ : ℝ → ℤ → ℝ)
    (hsol : IsForcedTruncatedSolution ν μ κ N f h u θ) (T : ℝ) (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun t => enstrophy (u t) N) (Set.Icc 0 T)) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, enstrophy (u t) N ≤ C := by
  obtain ⟨E₀, hE₀⟩ := forced_truncated_energy_bounded ν μ κ hν hκ N f h u θ hsol T hT
  set E_max : ℝ := max E₀ 1 with hE_max
  have hEpos : 0 < E_max := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hEmax : ∀ t ∈ Set.Icc 0 T, velocityEnergy (u t) N ≤ E_max := fun t ht =>
    (hE₀ t ht).trans (le_max_left _ _)
  have hTcont : Continuous fun t => tempEnstrophy (θ t) N := by
    unfold tempEnstrophy
    refine continuous_finsetSum _ fun k hk => ?_
    have hdiff : Differentiable ℝ (fun t : ℝ => (θ t (k : ℤ)) ^ 2) := fun t =>
      ((hsol.2.1 t (k : ℤ) (Int.natCast_nonneg k)
        (by exact_mod_cast (Finset.mem_range.mp hk))).differentiableAt).pow 2
    exact continuous_const.mul hdiff.continuous
  obtain ⟨T₀, hT₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).bddAbove_image hTcont.continuousOn
  set T_max : ℝ := max T₀ 0 with hT_max
  have hTmax_nonneg : 0 ≤ T_max := le_max_right _ _
  have hTle : ∀ t ∈ Set.Icc 0 T, tempEnstrophy (θ t) N ≤ T_max := fun t ht =>
    (hT₀ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  set C₀ : ℝ := 2187 / (16 * (ν / (2 * E_max)) ^ 3) + κ ^ 2 / (4 * (ν / (4 * E_max)))
      + (E_max / ν) + forceEnstrophy f N + κ * T_max with hC₀
  have hC₀_nonneg : 0 ≤ C₀ := by
    rw [hC₀]
    have h1 : 0 ≤ 2187 / (16 * (ν / (2 * E_max)) ^ 3) :=
      div_nonneg (by norm_num) (by positivity)
    have h2 : 0 ≤ κ ^ 2 / (4 * (ν / (4 * E_max))) :=
      div_nonneg (sq_nonneg _) (by positivity)
    have h3 : 0 ≤ E_max / ν := div_nonneg hEpos.le hν.le
    have h4 : 0 ≤ forceEnstrophy f N := forceEnstrophy_nonneg f N
    have h5 : 0 ≤ κ * T_max := mul_nonneg hκ hTmax_nonneg
    linarith
  have hγpos : 0 < ν / E_max := div_pos hν hEpos
  have hderiv : ∀ t ∈ Set.Ico 0 T, HasDerivAt (fun s => enstrophy (u s) N)
      (2 * ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
        * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ)) t :=
    fun t _ => forcedEnstrophy_hasDerivAt ν μ κ N f h u θ hsol t
  have hineq : ∀ t ∈ Set.Ico 0 T,
      2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
          * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ))
        ≤ C₀ - (ν / E_max) * (enstrophy (u t) N) ^ 2 := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 T := ⟨ht.1, le_of_lt ht.2⟩
    have hrate := forced_enstrophy_rate_le ν κ E_max hκ hν.le hEpos N f (u t) (θ t)
      (hsol.2.2 t).1 (hsol.2.2 t).2.1 (hEmax t htIcc)
    have hHnn : 0 ≤ enstrophy (u t) N := enstrophy_nonneg _ _
    have hκT : κ * (enstrophy (u t) N + tempEnstrophy (θ t) N)
        ≤ κ * (enstrophy (u t) N + T_max) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl _) (hTle t htIcc)) hκ
    have hyoung := forced_enstrophy_young (ν := ν) (κ := κ) (E_max := E_max)
      (He := forceEnstrophy f N) (T_max := T_max) (s := Real.sqrt (enstrophy (u t) N))
      hν hEpos hκ (forceEnstrophy_nonneg f N) hTmax_nonneg (Real.sqrt_nonneg _)
    have hs2 : (Real.sqrt (enstrophy (u t) N)) ^ 2 = enstrophy (u t) N := Real.sq_sqrt hHnn
    have hs3 : (Real.sqrt (enstrophy (u t) N)) ^ 3
        = enstrophy (u t) N * Real.sqrt (enstrophy (u t) N) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, hs2]
    have hs4 : (Real.sqrt (enstrophy (u t) N)) ^ 4 = (enstrophy (u t) N) ^ 2 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, hs2]
      ring
    rw [hs3, hs4, hs2] at hyoung
    rw [hC₀]
    simp only [div_eq_mul_inv] at hrate hyoung ⊢
    linarith [hrate, hyoung, hκT]
  have hbar := le_of_deriv_le_const_sub_sq (y := fun t => enstrophy (u t) N)
    (y' := fun t => 2 * ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
      * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ))
    hC₀_nonneg hγpos hcont hderiv hineq
  exact ⟨max (enstrophy (u 0) N) (Real.sqrt (C₀ / (ν / E_max))), fun t ht => hbar t ht⟩

/-! ## 11. Non-vacuity -/

/-- **The zero state with zero force is an equilibrium** of the forced truncated model. -/
theorem zero_is_forcedTruncatedSolution (ν μ κ : ℝ) (N : ℕ) :
    IsForcedTruncatedSolution ν μ κ N (fun _ => 0) (fun _ => 0)
      (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t k _ _
    have h0 : forcedVelocityRHS ν κ (fun _ : ℤ => (0 : ℝ))
        (fun _ : ℤ => (0 : ℝ)) (fun _ : ℤ => (0 : ℝ)) k = 0 := by
      simp [forcedVelocityRHS, dyadicVelocityRHS, generalVelocityRHS, boussinesqTransferU,
        dyadicWeight]
    rw [h0]
    exact hasDerivAt_const t 0
  · intro t k _ _
    have h0 : forcedTemperatureRHS μ (fun _ : ℤ => (0 : ℝ))
        (fun _ : ℤ => (0 : ℝ)) (fun _ : ℤ => (0 : ℝ)) k = 0 := by
      simp [forcedTemperatureRHS, dyadicTemperatureRHS, generalTemperatureRHS,
        boussinesqTransferTheta, dyadicWeight]
    rw [h0]
    exact hasDerivAt_const t 0
  · intro t
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The forced capstone applies to the zero equilibrium. -/
example : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    velocityEnergy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2 ≤ C :=
  forced_truncated_energy_bounded 1 1 1 (by norm_num) (by norm_num) 2
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (zero_is_forcedTruncatedSolution 1 1 1 2) 1 (by norm_num)

/-- A concrete non-zero forced state on the shells `-1, 0, 1, 2`: `u = (0, 1, 3, 0)`. -/
private def uF : ℤ → ℝ :=
  fun k => if k = -1 then 0 else if k = 0 then 1 else if k = 1 then 3 else if k = 2 then 0 else 0

/-- The accompanying temperature state: `θ = (0, 1, 2, 0)`. -/
private def θF : ℤ → ℝ :=
  fun k => if k = -1 then 0 else if k = 0 then 1 else if k = 1 then 2 else if k = 2 then 0 else 0

/-- A concrete force ladder `f = (0, 1, 1, 0)` on the shells `-1, 0, 1, 2`. -/
private def fF : ℤ → ℝ :=
  fun k => if k = -1 then 0 else if k = 0 then 1 else if k = 1 then 1 else if k = 2 then 0 else 0

/-- Concrete force energy: `1² + 1² = 2`. -/
example : forceEnergy fF 2 = 2 := by
  norm_num [forceEnergy, Finset.sum_range_succ, Finset.sum_range_zero, fF]

/-- Concrete forced velocity pairing: `-30 + 1·1 + 3·1 = -26`, i.e. the force contribution
`∑ u_k f_k = 4` is genuinely non-zero. -/
example :
    (∑ k ∈ Finset.range 2, uF (k : ℤ) * forcedVelocityRHS 1 1 fF uF θF (k : ℤ)) = -26 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uF, θF, fF, forcedVelocityRHS,
    dyadicVelocityRHS, generalVelocityRHS, boussinesqTransferU, dyadicWeight]

/-- The forced logistic rate inequality at the concrete state is not vacuous:
`2 · (−26) ≤ 2 (1·√5 + √2)√10 − 2·1·10`. -/
example :
    2 * (∑ k ∈ Finset.range 2, uF (k : ℤ) * forcedVelocityRHS 1 1 fF uF θF (k : ℤ))
      ≤ 2 * (1 * Real.sqrt (entropy θF 2) + Real.sqrt (forceEnergy fF 2))
          * Real.sqrt (velocityEnergy uF 2)
        - 2 * 1 * velocityEnergy uF 2 := by
  have h : 2 * (∑ k ∈ Finset.range 2,
      uF (k : ℤ) * forcedVelocityRHS 1 1 fF uF θF (k : ℤ)) = -52 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uF, θF, fF, forcedVelocityRHS,
      dyadicVelocityRHS, generalVelocityRHS, boussinesqTransferU, dyadicWeight]
  have hS : entropy θF 2 = 5 := by
    norm_num [entropy, Finset.sum_range_succ, Finset.sum_range_zero, θF]
  have hE : velocityEnergy uF 2 = 10 := by
    norm_num [velocityEnergy, Finset.sum_range_succ, Finset.sum_range_zero, uF]
  have hF : forceEnergy fF 2 = 2 := by
    norm_num [forceEnergy, Finset.sum_range_succ, Finset.sum_range_zero, fF]
  rw [h, hS, hE, hF]
  have h1 : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have h2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have h3 : (0 : ℝ) ≤ Real.sqrt 10 := Real.sqrt_nonneg 10
  nlinarith [mul_nonneg h1 h3, mul_nonneg h2 h3]

end Cascade

/-! ## Axiom audit -/

#print axioms Cascade.forcedVelocityRHS
#print axioms Cascade.forcedTemperatureRHS
#print axioms Cascade.forcedBoussinesqRHS
#print axioms Cascade.forcedVelocityRHS_zero
#print axioms Cascade.forcedTemperatureRHS_zero
#print axioms Cascade.forcedBoussinesqRHS_zero
#print axioms Cascade.IsForcedTruncatedSolution
#print axioms Cascade.isForcedTruncatedSolution_zero_iff
#print axioms Cascade.forceEnergy
#print axioms Cascade.forceEnergy_nonneg
#print axioms Cascade.forcedVelocityEnergy_hasDerivAt
#print axioms Cascade.forcedEntropy_hasDerivAt
#print axioms Cascade.forcedVelocityEnergy_continuous
#print axioms Cascade.forcedEntropy_continuous
#print axioms Cascade.sum_mul_le_sqrt_mul_sqrt'
#print axioms Cascade.force_work_le
#print axioms Cascade.forced_velocity_pairing_le
#print axioms Cascade.forced_energy_rate_le
#print axioms Cascade.forced_energy_rate_le_of_entropy_le
#print axioms Cascade.forced_truncated_energy_bounded
#print axioms Cascade.forced_entropy_antitone
#print axioms Cascade.forced_energy_le_max_unforced_temperature
#print axioms Cascade.forceEnstrophy
#print axioms Cascade.forceEnstrophy_nonneg
#print axioms Cascade.force_enstrophy_work_le
#print axioms Cascade.forcedEnstrophy_hasDerivAt
#print axioms Cascade.forced_enstrophy_rate_le
#print axioms Cascade.forced_enstrophy_young
#print axioms Cascade.forced_truncated_enstrophy_bounded
#print axioms Cascade.zero_is_forcedTruncatedSolution
