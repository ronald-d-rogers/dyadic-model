import Cascade.BoussinesqEnergy
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Stage O — the unforced obstruction for the dyadic Boussinesq model

This file records the elementary *obstruction* to a self-sustaining unforced cascade in the
dyadic Boussinesq model of `Cascade/Boussinesq.lean`. The starting point is the exact
two-species energy identity of `Cascade/BoussinesqEnergy.lean`: summing the velocity pairing
over the truncated range of shells `k = 0, …, n-1`,

`∑_{k<n} u_k (du_k/dt) = Flux_u(0) − Flux_u(n) + κ ∑_{k<n} u_k θ_k − ν ∑_{k<n} 2^{2k} u_k²`,

and likewise for the temperature ladder. The nonlinear self-transfer is **exactly
energy-conserving in the interior**: it survives only through the boundary fluxes
`dyadicVelocityFlux 0`, `dyadicVelocityFlux n` (and their temperature counterparts). Under the
truncation / Dirichlet boundary conditions

`u(-1) = θ(-1) = u(n) = θ(n) = 0`

those boundary fluxes vanish, so the only bulk energy source is the buoyancy production
`κ ∑ u_k θ_k`, while viscosity removes energy at rate `ν ∑ 2^{2k} u_k²`.

Two elementary inequalities then show that buoyancy cannot beat dissipation in the unforced
model:

* **(Cauchy–Schwarz)** the buoyancy is bounded by the entropy, `∑ u_k θ_k ≤ √(∑ u_k²) √(∑ θ_k²)`;
* **(dyadic weight)** on the physical range `k ≥ 0` the viscous weight satisfies
  `2^{2k} ≥ 1`, hence `∑ u_k² ≤ ∑ 2^{2k} u_k²`.

Consequently the velocity energy pairing is at most `κ √E √S − ν E` with `E = ∑ u_k²` and
`S = ∑ θ_k²`, and the temperature pairing is nonpositive: thermal entropy is only dissipated.
The linear damping therefore dominates the (entropy-bounded) buoyancy, and no unforced
self-sustaining cascade is possible in this truncated model.

The rational `n = 2` example at the end shows the bound is not vacuous: the velocity pairing
equals `-30` while the bound is `√50 − 10 ≈ -2.93`, so the inequality `-30 ≤ √50 - 10` is
strict.
-/

noncomputable section

open scoped BigOperators

namespace Cascade

/-! ## Cauchy–Schwarz for the buoyancy term -/

/-- **Buoyancy Cauchy–Schwarz (generic index type).** Squaring with
`Finset.sum_mul_sq_le_sq_mul_sq` and passing through the square root gives the finset
Cauchy–Schwarz inequality. This generic form is what the shell sums (indexed by `ℕ`) use. -/
private lemma sum_mul_le_sqrt_mul_sqrt_gen {α : Type*} (s : Finset α) (u θ : α → ℝ) :
    (∑ k ∈ s, u k * θ k)
      ≤ Real.sqrt (∑ k ∈ s, (u k) ^ 2) * Real.sqrt (∑ k ∈ s, (θ k) ^ 2) := by
  have hsq : (∑ k ∈ s, u k * θ k) ^ 2
      ≤ (∑ k ∈ s, (u k) ^ 2) * (∑ k ∈ s, (θ k) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq s u θ
  calc (∑ k ∈ s, u k * θ k)
      ≤ Real.sqrt ((∑ k ∈ s, (u k) ^ 2) * (∑ k ∈ s, (θ k) ^ 2)) :=
        Real.le_sqrt_of_sq_le hsq
    _ = Real.sqrt (∑ k ∈ s, (u k) ^ 2) * Real.sqrt (∑ k ∈ s, (θ k) ^ 2) :=
        Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg (u i)) _

/-- **Buoyancy Cauchy–Schwarz.** For any finset of shells `s`, the buoyancy pairing
`∑_{k ∈ s} u_k θ_k` is bounded by `√(∑ u_k²) √(∑ θ_k²)`. The sign of the pairing is handled
automatically by `Real.le_sqrt_of_sq_le`. -/
theorem sum_mul_le_sqrt_mul_sqrt (s : Finset ℤ) (u θ : ℤ → ℝ) :
    (∑ k ∈ s, u k * θ k)
      ≤ Real.sqrt (∑ k ∈ s, (u k) ^ 2) * Real.sqrt (∑ k ∈ s, (θ k) ^ 2) :=
  sum_mul_le_sqrt_mul_sqrt_gen s u θ

/-! ## The dyadic weight is at least one on the physical range -/

/-- On the physical range `k ≥ 0` the dyadic weight `2^k` is at least `1`. -/
private lemma one_le_dyadicWeight {k : ℤ} (hk : 0 ≤ k) : 1 ≤ dyadicWeight k := by
  unfold dyadicWeight
  exact one_le_zpow₀ (by norm_num : (1 : ℝ) ≤ 2) hk

/-- Every dyadic weight is strictly positive. -/
private lemma dyadicWeight_pos (k : ℤ) : (0 : ℝ) < dyadicWeight k := by
  unfold dyadicWeight
  exact zpow_pos (by norm_num : (0 : ℝ) < 2) k

/-- **Viscous weight dominates.** On the physical shells `k ≥ 0` the viscous factor
`2^{2k} = dyadicWeight (2k)` is at least `1`, hence `u_k² ≤ 2^{2k} u_k²` shell by shell, and
summing gives `∑ u_k² ≤ ∑ 2^{2k} u_k²`. -/
private lemma sum_sq_le_sum_weighted_sq (u : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (u (k : ℤ)) ^ 2)
      ≤ (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2) := by
  apply Finset.sum_le_sum
  intro k _
  have h2k : (0 : ℤ) ≤ 2 * (k : ℤ) := by
    have : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    linarith
  have h1 : (1 : ℝ) ≤ dyadicWeight (2 * (k : ℤ)) := one_le_dyadicWeight h2k
  calc (u (k : ℤ)) ^ 2 = (u (k : ℤ)) ^ 2 * 1 := (mul_one _).symm
    _ ≤ (u (k : ℤ)) ^ 2 * dyadicWeight (2 * (k : ℤ)) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2 := mul_comm _ _

/-! ## Vanishing of the boundary fluxes under Dirichlet conditions -/

/-- The velocity energy flux at the bottom boundary `0` vanishes when `u(-1) = 0`. -/
private lemma dyadicVelocityFlux_bot (u : ℤ → ℝ) (h : u (-1) = 0) :
    dyadicVelocityFlux u 0 = 0 := by
  simp [dyadicVelocityFlux, velocityFlux, h]

/-- The velocity energy flux at the top boundary `n` vanishes when `u n = 0`. -/
private lemma dyadicVelocityFlux_top (u : ℤ → ℝ) (n : ℕ) (h : u (n : ℤ) = 0) :
    dyadicVelocityFlux u (n : ℤ) = 0 := by
  simp [dyadicVelocityFlux, velocityFlux, h]

/-- The temperature entropy flux at the bottom boundary `0` vanishes when `θ(-1) = 0`. -/
private lemma dyadicTemperatureFlux_bot (u θ : ℤ → ℝ) (h : θ (-1) = 0) :
    dyadicTemperatureFlux u θ 0 = 0 := by
  simp [dyadicTemperatureFlux, temperatureFlux, h]

/-- The temperature entropy flux at the top boundary `n` vanishes when `θ n = 0`. -/
private lemma dyadicTemperatureFlux_top (u θ : ℤ → ℝ) (n : ℕ) (h : θ (n : ℤ) = 0) :
    dyadicTemperatureFlux u θ (n : ℤ) = 0 := by
  simp [dyadicTemperatureFlux, temperatureFlux, h]

/-! ## The obstruction -/

/-- **Velocity energy rate bound (the obstruction).** Under the Dirichlet/truncation
conditions `u(-1) = u(n) = 0` the interior transfer contributes nothing to the velocity
energy balance, so the pairing is the buoyancy minus the viscous dissipation. Cauchy–Schwarz
bounds the buoyancy by the entropy, and the dyadic weight bound `2^{2k} ≥ 1` bounds the
dissipation below by `ν ∑ u_k²`:

`∑_{k<n} u_k (du_k/dt) ≤ κ √(∑ u_k²) √(∑ θ_k²) − ν ∑ u_k²`.

The hypothesis `0 ≤ κ` is needed to push the Cauchy–Schwarz bound through the (sign of the)
buoyancy coefficient; it is the physically relevant case and the statement is false for
`κ < 0` (see the report). -/
theorem velocity_energy_rate_le (ν κ : ℝ) (hκ : 0 ≤ κ) (hν : 0 ≤ ν) (u θ : ℤ → ℝ) (n : ℕ)
    (hbot : u (-1) = 0) (htop : u (n : ℤ) = 0) :
    (∑ k ∈ Finset.range n, u (k : ℤ) * dyadicVelocityRHS ν κ u θ (k : ℤ))
      ≤ κ * (Real.sqrt (∑ k ∈ Finset.range n, (u (k : ℤ)) ^ 2)
              * Real.sqrt (∑ k ∈ Finset.range n, (θ (k : ℤ)) ^ 2))
        - ν * (∑ k ∈ Finset.range n, (u (k : ℤ)) ^ 2) := by
  rw [dyadic_velocity_energy_identity ν κ u θ n,
    dyadicVelocityFlux_bot u hbot, dyadicVelocityFlux_top u n htop]
  have hCS : (∑ k ∈ Finset.range n, u (k : ℤ) * θ (k : ℤ))
      ≤ Real.sqrt (∑ k ∈ Finset.range n, (u (k : ℤ)) ^ 2)
        * Real.sqrt (∑ k ∈ Finset.range n, (θ (k : ℤ)) ^ 2) := by
    simpa using sum_mul_le_sqrt_mul_sqrt_gen (Finset.range n)
      (fun k : ℕ => u (k : ℤ)) (fun k : ℕ => θ (k : ℤ))
  have hκS := mul_le_mul_of_nonneg_left hCS hκ
  have hW := sum_sq_le_sum_weighted_sq u n
  have hνW := mul_le_mul_of_nonneg_left hW hν
  linarith

/-- **Entropy non-increase.** Under `θ(-1) = θ(n) = 0` the temperature advection contributes
nothing to the entropy balance, and the thermal dissipation term is nonnegative because
`0 ≤ μ` and every dyadic weight is positive. Hence the temperature pairing is nonpositive:
thermal entropy can only decrease. -/
theorem temperature_energy_rate_nonpos (μ : ℝ) (hμ : 0 ≤ μ) (u θ : ℤ → ℝ) (n : ℕ)
    (hbot : θ (-1) = 0) (htop : θ (n : ℤ) = 0) :
    (∑ k ∈ Finset.range n, θ (k : ℤ) * dyadicTemperatureRHS μ u θ (k : ℤ)) ≤ 0 := by
  rw [dyadic_temperature_energy_identity μ u θ n,
    dyadicTemperatureFlux_bot u θ hbot, dyadicTemperatureFlux_top u θ n htop]
  have hW : 0 ≤ (∑ k ∈ Finset.range n,
      dyadicWeight (2 * (k : ℤ)) * (θ (k : ℤ)) ^ 2) := by
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (dyadicWeight_pos (2 * (k : ℤ))).le (sq_nonneg _)
  linarith [mul_nonneg hμ hW]

/-- **No energy production except bounded buoyancy.** Under the truncation / Dirichlet
conditions `u(-1) = u(n) = θ(-1) = θ(n) = 0` and nonnegative `ν, μ, κ`, the velocity pairing
is at most `κ √E √S − ν E` (with `E = ∑ u_k²`, `S = ∑ θ_k²`) and the temperature pairing is
nonpositive. Thus in the unforced truncated model the exactly-conserving nonlinear transfer
supplies no interior energy; the sole source is buoyancy, which is bounded by the entropy
`S`, while viscosity damps at least at rate `ν E`. -/
theorem no_energy_production_except_buoyancy (ν κ μ : ℝ) (hκ : 0 ≤ κ) (hν : 0 ≤ ν)
    (hμ : 0 ≤ μ) (u θ : ℤ → ℝ) (n : ℕ)
    (huBot : u (-1) = 0) (huTop : u (n : ℤ) = 0)
    (hθBot : θ (-1) = 0) (hθTop : θ (n : ℤ) = 0) :
    (∑ k ∈ Finset.range n, u (k : ℤ) * dyadicVelocityRHS ν κ u θ (k : ℤ))
        ≤ κ * (Real.sqrt (∑ k ∈ Finset.range n, (u (k : ℤ)) ^ 2)
                * Real.sqrt (∑ k ∈ Finset.range n, (θ (k : ℤ)) ^ 2))
          - ν * (∑ k ∈ Finset.range n, (u (k : ℤ)) ^ 2)
      ∧ (∑ k ∈ Finset.range n, θ (k : ℤ) * dyadicTemperatureRHS μ u θ (k : ℤ)) ≤ 0 :=
  ⟨velocity_energy_rate_le ν κ hκ hν u θ n huBot huTop,
    temperature_energy_rate_nonpos μ hμ u θ n hθBot hθTop⟩

/-! ## Non-vacuity check

Concrete state `n = 2`, `ν = κ = μ = 1`, with `u_{-1}, u_0, u_1, u_2 = 0, 1, 3, 0` and
`θ_{-1}, θ_0, θ_1, θ_2 = 0, 1, 2, 0`. Then the velocity pairing evaluates to the *nonzero*
rational `-30`, while the right-hand side is `√10 · √5 − 10 = √50 − 10 ≈ -2.93`, so the
inequality `-30 ≤ √50 - 10` is strict and the bound is not vacuous. -/

private def uObs (k : ℤ) : ℝ :=
  if k = -1 then 0 else if k = 0 then 1 else if k = 1 then 3 else if k = 2 then 0 else 0

private def θObs (k : ℤ) : ℝ :=
  if k = -1 then 0 else if k = 0 then 1 else if k = 1 then 2 else if k = 2 then 0 else 0

/-- The energy identity specialised to the concrete state (both sides finite). -/
example :
    (∑ k ∈ Finset.range 2, uObs (k : ℤ) * dyadicVelocityRHS 1 1 uObs θObs (k : ℤ))
      = dyadicVelocityFlux uObs 0 - dyadicVelocityFlux uObs (2 : ℤ)
        + 1 * (∑ k ∈ Finset.range 2, uObs (k : ℤ) * θObs (k : ℤ))
        - 1 * (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * (uObs (k : ℤ)) ^ 2) :=
  dyadic_velocity_energy_identity 1 1 uObs θObs 2

/-- The velocity pairing of the concrete state equals `-30`. -/
example :
    (∑ k ∈ Finset.range 2, uObs (k : ℤ) * dyadicVelocityRHS 1 1 uObs θObs (k : ℤ)) = -30 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uObs, θObs,
    dyadicVelocityRHS, generalVelocityRHS, boussinesqTransferU, dyadicWeight]

/-- The right-hand side of the bound for the concrete state equals `√10 · √5 − 10`. -/
example :
    1 * (Real.sqrt (∑ k ∈ Finset.range 2, (uObs (k : ℤ)) ^ 2)
          * Real.sqrt (∑ k ∈ Finset.range 2, (θObs (k : ℤ)) ^ 2))
      - 1 * (∑ k ∈ Finset.range 2, (uObs (k : ℤ)) ^ 2)
      = Real.sqrt 10 * Real.sqrt 5 - 10 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uObs, θObs]

/-- The concrete inequality `-30 ≤ √10 · √5 − 10` holds strictly. -/
example : -30 ≤ Real.sqrt 10 * Real.sqrt 5 - 10 := by
  have h : (0 : ℝ) ≤ Real.sqrt 10 * Real.sqrt 5 := by positivity
  linarith

/-- The obstruction theorem specialised to the concrete state (with `norm_num` discharging the
boundary hypotheses). -/
example :
    (∑ k ∈ Finset.range 2, uObs (k : ℤ) * dyadicVelocityRHS 1 1 uObs θObs (k : ℤ))
      ≤ 1 * (Real.sqrt (∑ k ∈ Finset.range 2, (uObs (k : ℤ)) ^ 2)
              * Real.sqrt (∑ k ∈ Finset.range 2, (θObs (k : ℤ)) ^ 2))
        - 1 * (∑ k ∈ Finset.range 2, (uObs (k : ℤ)) ^ 2) :=
  velocity_energy_rate_le 1 1 (by norm_num) (by norm_num) uObs θObs 2
    (by norm_num [uObs]) (by norm_num [uObs])

end Cascade

#print axioms Cascade.sum_mul_le_sqrt_mul_sqrt
#print axioms Cascade.velocity_energy_rate_le
#print axioms Cascade.temperature_energy_rate_nonpos
#print axioms Cascade.no_energy_production_except_buoyancy
