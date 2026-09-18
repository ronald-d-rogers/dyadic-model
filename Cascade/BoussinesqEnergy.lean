import Cascade.Boussinesq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Stage R — the two-species energy balance of the dyadic Boussinesq model

This file derives the energy balance of the dyadic Boussinesq model defined in
`Cascade/Boussinesq.lean`. Pairing each ladder with its own ODE:

* the velocity pairing splits into the nonlinear self-transfer, the buoyancy production
  `κ u_k θ_k`, and the viscous dissipation `ν 2^{2k} u_k²`;
* the temperature pairing splits into the nonlinear advection (entropy-conserving) and the
  thermal dissipation `μ 2^{2k} θ_k²`.

Summing over the truncated range of shells `k = 0, …, n-1` and telescoping with
`velocity_pairing_eq_flux` / `temperature_pairing_eq_flux`, the two nonlinear transfers
survive only as the boundary fluxes `velocityFlux 0 - velocityFlux n` and
`temperatureFlux 0 - temperatureFlux n`. The exchange between the two ladders is exactly the
buoyancy term `κ Σ u_k θ_k`, which appears in the velocity balance and not in the temperature
balance. This is the standard Boussinesq energy budget: kinetic energy is produced from
potential energy at rate `κ Σ u_k θ_k` and dissipated at rate `ν Σ 2^{2k} u_k²`, while
thermal entropy is only dissipated, at rate `μ Σ 2^{2k} θ_k²`.

The named theorems `dyadic_velocity_energy_identity`, `dyadic_temperature_energy_identity` and
`dyadic_energy_identity` state the identity for the **frozen Stage R model**
(`A = 1`, `B = 0`, `Ã = 1`, `B̃ = 1`, with the frozen fluxes `dyadicVelocityFlux` /
`dyadicTemperatureFlux`). The four-parameter structural version is kept under the `general*`
names (`general_dyadic_velocity_energy_identity`, `general_dyadic_temperature_energy_identity`,
`general_dyadic_energy_identity`); each frozen theorem is the immediate specialisation of its
general counterpart at the frozen coupling.
-/

noncomputable section

open scoped BigOperators

namespace Cascade

/-- **Pointwise velocity pairing (general model).** The velocity pairing splits into the
nonlinear self-transfer, the buoyancy production and the viscous dissipation. -/
private lemma velocity_pairing_split (ν κ A B : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    u k * generalVelocityRHS ν κ A B u θ k
      = u k * boussinesqTransferU A B u k
        + κ * (u k * θ k)
        - ν * (dyadicWeight (2 * k) * (u k) ^ 2) := by
  simp only [generalVelocityRHS]
  ring

/-- **Pointwise temperature pairing (general model).** The temperature pairing splits into the
nonlinear advection and the thermal dissipation. -/
private lemma temperature_pairing_split (μ At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    θ k * generalTemperatureRHS μ At Bt u θ k
      = θ k * boussinesqTransferTheta At Bt u θ k
        - μ * (dyadicWeight (2 * k) * (θ k) ^ 2) := by
  simp only [generalTemperatureRHS]
  ring

/-- **Telescoping of the velocity pairing.** The velocity self-transfer summed over the
truncated range of shells `0, …, n-1` collapses to the difference of the energy flux across
the boundary shells `0` and `n`. -/
private lemma sum_velocity_pairing (A B : ℝ) (u : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, u (k : ℤ) * boussinesqTransferU A B u (k : ℤ))
      = velocityFlux A B u 0 - velocityFlux A B u (n : ℤ) := by
  have h : ∀ k ∈ Finset.range n,
      u (k : ℤ) * boussinesqTransferU A B u (k : ℤ)
        = (fun m : ℕ => velocityFlux A B u (m : ℤ)) k
          - (fun m : ℕ => velocityFlux A B u (m : ℤ)) (k + 1) := by
    intro k _
    rw [velocity_pairing_eq_flux]
    push_cast
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_range_sub']
  norm_num

/-- **Telescoping of the temperature pairing.** The temperature advection summed over the
truncated range of shells `0, …, n-1` collapses to the difference of the entropy flux across
the boundary shells `0` and `n`. -/
private lemma sum_temperature_pairing (At Bt : ℝ) (u θ : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, θ (k : ℤ) * boussinesqTransferTheta At Bt u θ (k : ℤ))
      = temperatureFlux At Bt u θ 0 - temperatureFlux At Bt u θ (n : ℤ) := by
  have h : ∀ k ∈ Finset.range n,
      θ (k : ℤ) * boussinesqTransferTheta At Bt u θ (k : ℤ)
        = (fun m : ℕ => temperatureFlux At Bt u θ (m : ℤ)) k
          - (fun m : ℕ => temperatureFlux At Bt u θ (m : ℤ)) (k + 1) := by
    intro k _
    rw [temperature_pairing_eq_flux]
    push_cast
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_range_sub']
  norm_num

/-- **Velocity energy identity (general four-parameter model).** Pairing the velocity ladder
with its own ODE gives the kinetic-energy balance: the buoyancy production `κ Σ u_k θ_k` minus
the viscous dissipation `ν Σ 2^{2k} u_k²`, plus the energy flux that leaves the truncated range
of shells. -/
theorem general_dyadic_velocity_energy_identity (ν κ A B : ℝ) (u θ : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, u (k : ℤ) * generalVelocityRHS ν κ A B u θ (k : ℤ))
      = velocityFlux A B u 0 - velocityFlux A B u (n : ℤ)
        + κ * (∑ k ∈ Finset.range n, u (k : ℤ) * θ (k : ℤ))
        - ν * (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2) := by
  rw [Finset.sum_congr (rfl : Finset.range n = Finset.range n)
    (fun k _ => velocity_pairing_split ν κ A B u θ (k : ℤ))]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_velocity_pairing A B u n, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **Temperature (entropy) identity (general four-parameter model).** The advection conserves
entropy up to the boundary flux, so the only bulk term is the thermal dissipation
`−μ Σ 2^{2k} θ_k²`. -/
theorem general_dyadic_temperature_energy_identity (μ At Bt : ℝ) (u θ : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, θ (k : ℤ) * generalTemperatureRHS μ At Bt u θ (k : ℤ))
      = temperatureFlux At Bt u θ 0 - temperatureFlux At Bt u θ (n : ℤ)
        - μ * (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (θ (k : ℤ)) ^ 2) := by
  rw [Finset.sum_congr (rfl : Finset.range n = Finset.range n)
    (fun k _ => temperature_pairing_split μ At Bt u θ (k : ℤ))]
  rw [Finset.sum_sub_distrib]
  rw [sum_temperature_pairing At Bt u θ n, ← Finset.mul_sum]

/-- **The two-species energy balance (general four-parameter model).** Summing the two
pairings: the exchange between the two ladders is *only* the buoyancy term `κ Σ u_k θ_k` (it
appears in the velocity balance and not in the temperature balance), against the two
dissipations; the nonlinear transfers survive only as boundary fluxes. -/
theorem general_dyadic_energy_identity (ν μ κ A B At Bt : ℝ) (u θ : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n,
        (u (k : ℤ) * (generalBoussinesqRHS ν μ κ A B At Bt u θ (k : ℤ)).1
          + θ (k : ℤ) * (generalBoussinesqRHS ν μ κ A B At Bt u θ (k : ℤ)).2))
      = (velocityFlux A B u 0 - velocityFlux A B u (n : ℤ))
        + (temperatureFlux At Bt u θ 0 - temperatureFlux At Bt u θ (n : ℤ))
        + κ * (∑ k ∈ Finset.range n, u (k : ℤ) * θ (k : ℤ))
        - ν * (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2)
        - μ * (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (θ (k : ℤ)) ^ 2) := by
  have hsplit :
      (∑ k ∈ Finset.range n,
          (u (k : ℤ) * (generalBoussinesqRHS ν μ κ A B At Bt u θ (k : ℤ)).1
            + θ (k : ℤ) * (generalBoussinesqRHS ν μ κ A B At Bt u θ (k : ℤ)).2))
        = (∑ k ∈ Finset.range n, u (k : ℤ) * generalVelocityRHS ν κ A B u θ (k : ℤ))
          + (∑ k ∈ Finset.range n, θ (k : ℤ) * generalTemperatureRHS μ At Bt u θ (k : ℤ)) := by
    rw [Finset.sum_add_distrib]
    simp only [generalBoussinesqRHS]
  rw [hsplit, general_dyadic_velocity_energy_identity, general_dyadic_temperature_energy_identity]
  ring

/-! ## The frozen Stage R energy identities (`A = 1`, `B = 0`, `Ã = 1`, `B̃ = 1`) -/

/-- **Frozen Stage R velocity energy identity.** -/
theorem dyadic_velocity_energy_identity (ν κ : ℝ) (u θ : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, u (k : ℤ) * dyadicVelocityRHS ν κ u θ (k : ℤ))
      = dyadicVelocityFlux u 0 - dyadicVelocityFlux u (n : ℤ)
        + κ * (∑ k ∈ Finset.range n, u (k : ℤ) * θ (k : ℤ))
        - ν * (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2) := by
  simpa [dyadicVelocityRHS, dyadicVelocityFlux] using
    general_dyadic_velocity_energy_identity ν κ 1 0 u θ n

/-- **Frozen Stage R temperature (entropy) identity.** -/
theorem dyadic_temperature_energy_identity (μ : ℝ) (u θ : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, θ (k : ℤ) * dyadicTemperatureRHS μ u θ (k : ℤ))
      = dyadicTemperatureFlux u θ 0 - dyadicTemperatureFlux u θ (n : ℤ)
        - μ * (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (θ (k : ℤ)) ^ 2) := by
  simpa [dyadicTemperatureRHS, dyadicTemperatureFlux] using
    general_dyadic_temperature_energy_identity μ 1 1 u θ n

/-- **Frozen Stage R two-species energy balance.** -/
theorem dyadic_energy_identity (ν μ κ : ℝ) (u θ : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n,
        (u (k : ℤ) * (dyadicBoussinesqRHS ν μ κ u θ (k : ℤ)).1
          + θ (k : ℤ) * (dyadicBoussinesqRHS ν μ κ u θ (k : ℤ)).2))
      = (dyadicVelocityFlux u 0 - dyadicVelocityFlux u (n : ℤ))
        + (dyadicTemperatureFlux u θ 0 - dyadicTemperatureFlux u θ (n : ℤ))
        + κ * (∑ k ∈ Finset.range n, u (k : ℤ) * θ (k : ℤ))
        - ν * (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2)
        - μ * (∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (θ (k : ℤ)) ^ 2) := by
  simpa [dyadicBoussinesqRHS, dyadicVelocityRHS, dyadicTemperatureRHS, dyadicVelocityFlux,
    dyadicTemperatureFlux, generalBoussinesqRHS] using
    general_dyadic_energy_identity ν μ κ 1 0 1 1 u θ n

/-! ## Non-vacuity checks

Concrete ladders `u_{-1}, u_0, u_1, u_2 = 1, 2, 4, 8` and `θ_{-1}, θ_0, θ_1, θ_2 = 1, 3, 5, 7`
(zero elsewhere), frozen diffusivities `ν = μ = κ = 1`, and `n = 1`. Both sides of each
identity evaluate to the same *nonzero* rational: `-28` (velocity), `-180` (temperature),
`-208` (combined), so none of the three identities is vacuous. -/

private def uCheck (k : ℤ) : ℝ :=
  if k = -1 then 1 else if k = 0 then 2 else if k = 1 then 4 else if k = 2 then 8 else 0

private def θCheck (k : ℤ) : ℝ :=
  if k = -1 then 1 else if k = 0 then 3 else if k = 1 then 5 else if k = 2 then 7 else 0

example :
    (∑ k ∈ Finset.range 1, uCheck (k : ℤ) * dyadicVelocityRHS 1 1 uCheck θCheck (k : ℤ))
      = dyadicVelocityFlux uCheck 0 - dyadicVelocityFlux uCheck (1 : ℤ)
        + 1 * (∑ k ∈ Finset.range 1, uCheck (k : ℤ) * θCheck (k : ℤ))
        - 1 * (∑ k ∈ Finset.range 1, dyadicWeight (2 * (k : ℤ)) * (uCheck (k : ℤ)) ^ 2) :=
  dyadic_velocity_energy_identity 1 1 uCheck θCheck 1

example :
    (∑ k ∈ Finset.range 1, uCheck (k : ℤ) * dyadicVelocityRHS 1 1 uCheck θCheck (k : ℤ))
      = -28 := by
  simp only [Finset.sum_range_one, uCheck, θCheck, dyadicVelocityRHS, generalVelocityRHS,
    boussinesqTransferU, dyadicWeight]
  norm_num

example :
    (∑ k ∈ Finset.range 1, θCheck (k : ℤ) * dyadicTemperatureRHS 1 uCheck θCheck (k : ℤ))
      = -180 := by
  simp only [Finset.sum_range_one, uCheck, θCheck, dyadicTemperatureRHS, generalTemperatureRHS,
    boussinesqTransferTheta, dyadicWeight]
  norm_num

example :
    (∑ k ∈ Finset.range 1,
        (uCheck (k : ℤ) * (dyadicBoussinesqRHS 1 1 1 uCheck θCheck (k : ℤ)).1
          + θCheck (k : ℤ) * (dyadicBoussinesqRHS 1 1 1 uCheck θCheck (k : ℤ)).2))
      = -208 := by
  simp only [Finset.sum_range_one, uCheck, θCheck, dyadicBoussinesqRHS, dyadicVelocityRHS,
    dyadicTemperatureRHS, generalVelocityRHS, generalTemperatureRHS,
    boussinesqTransferU, boussinesqTransferTheta, dyadicWeight]
  norm_num

end Cascade

#print axioms Cascade.general_dyadic_velocity_energy_identity
#print axioms Cascade.general_dyadic_temperature_energy_identity
#print axioms Cascade.general_dyadic_energy_identity
#print axioms Cascade.dyadic_velocity_energy_identity
#print axioms Cascade.dyadic_temperature_energy_identity
#print axioms Cascade.dyadic_energy_identity
