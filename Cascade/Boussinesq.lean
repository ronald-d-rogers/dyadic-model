import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

/-!
# Stage R — the two-species dyadic Boussinesq model

The dyadic (shell) model of natural convection / Boussinesq. Shells are indexed by `k : ℤ`
and shell `k` carries the wavenumber `2^k`; the velocity ladder is `u : ℤ → ℝ` and the
temperature ladder is `θ : ℤ → ℝ`. The general four-parameter ODE is

    du_k/dt = A·2^k·(u_{k-1}² − 2 u_k u_{k+1}) + B·2^k·(u_k u_{k-1} − 2 u_{k+1}²)
                + κ θ_k − ν 2^{2k} u_k,
    dθ_k/dt = Ã·2^k·(u_{k-1}θ_{k-1} − 2 u_k θ_{k+1}) + B̃·2^k·(u_k θ_{k-1} − 2 u_{k+1}θ_{k+1})
                − μ 2^{2k} θ_k.

* `κ θ_k` is buoyancy, `ν 2^{2k}` the viscosity on the velocity, `μ 2^{2k}` the thermal
  diffusivity; the nonlinearities are nearest-octave (`k−1, k, k+1`).
* `A, B, Ã, B̃` are the standard coupling parameters; the traditional values are
  `A = ε`, `B = Ã = B̃ = 1` (Mailybaev, arXiv:1210.2494, eqs (3)-(4) with `h = 2`).

## The frozen Stage R model

The **named / frozen Stage R model** is the specific coupling

    A = 1,  B = 0,   Ã = 1,  B̃ = 1

with signature `(ν, μ, κ)` only. It is exposed under the plain names `dyadicVelocityRHS`,
`dyadicTemperatureRHS`, `dyadicBoussinesqRHS` (with the frozen fluxes `dyadicVelocityFlux` /
`dyadicTemperatureFlux`), while the four-parameter version is kept as the **general structural
result** under the `general*` names (`generalVelocityRHS`, `generalTemperatureRHS`,
`generalBoussinesqRHS`).

*Motivation, now a theorem.* The `Ã`/`B̃` terms are the higher- and lower-octave
temperature-gradient couplings. Linearising about a frozen background (perturbing only octave
`k`, freezing the rest, and writing `Ω_k = 2^k v_k` for the vorticity perturbation) leaves, in
the temperature equation, only the two terms carrying `u_k`: `−2Ã·2^k u_k θ_{k+1}` and
`+B̃·2^k u_k θ_{k-1}`. So the coupling `Θ̇ ∝ Ω` is `(B̃ θ̄_{k-1} − 2Ã θ̄_{k+1}) Ω_k`, which for a
wave at the newest (highest) octave reduces to `B̃ θ̄_{k-1} Ω_k` — the lower-octave
temperature gradient. Matching Tao's (Boussinesq, page 4) `Θ̇ = aΩ`, `Ω̇ = bΘ` therefore needs
`B̃ ≠ 0`, while `B` only adds a velocity diagonal `2^k(B ū_{k-1} − 2A ū_{k+1}) − ν4^k` absent
from that ODE; hence `B = 0`. `A = 1` keeps the Katz–Pavlović dyadic self-interaction. This
argument is **formalized exactly** in `Cascade/Lacunary.lean`
(`lacunary_reduction_dyadic_velocity` / `lacunary_reduction_dyadic_temperature`): the shell-`n`
equation on the lacunary state *is* the amplitude ODE, with no linearisation error.

The file is a *model definition*: it is frozen from its scaling and coupling alone, before any
statement about solutions. It carries the Boussinesq scaling (proved in
`Cascade/BoussinesqScaling.lean`) and the two-species energy balance (proved in
`Cascade/BoussinesqEnergy.lean`).

`velocityFlux` / `temperatureFlux` are the general energy/entropy fluxes through the shell
boundary `k`; `velocity_pairing_eq_flux` / `temperature_pairing_eq_flux` say that the pairing of
a ladder with its nonlinear transfer is exactly a flux difference, which is what makes the
nonlinearity conserve energy/entropy up to the boundary flux. The frozen model's counterparts
are `dyadicVelocityFlux` / `dyadicTemperatureFlux` with
`dyadic_velocity_pairing_eq_flux` / `dyadic_temperature_pairing_eq_flux`. These lemmas are the
algebraic heart of the energy identity.
-/

noncomputable section

namespace Cascade

/-- The dyadic weight of shell `k`: the wavenumber `2^k`. -/
def dyadicWeight (k : ℤ) : ℝ := (2 : ℝ) ^ k

/-- Velocity self-interaction transfer (nearest-octave). The standard energy-conserving
dyadic coupling; the two terms are the `A`- and `B`-interactions of the convection shell
model. -/
def boussinesqTransferU (A B : ℝ) (u : ℤ → ℝ) (k : ℤ) : ℝ :=
  dyadicWeight k *
    (A * ((u (k - 1)) ^ 2 - 2 * u k * u (k + 1))
      + B * (u k * u (k - 1) - 2 * (u (k + 1)) ^ 2))

/-- Temperature advection transfer (nearest-octave). The standard entropy-conserving dyadic
coupling; the two terms are the `Ã`- and `B̃`-interactions of the convection shell model. -/
def boussinesqTransferTheta (At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ :=
  dyadicWeight k *
    (At * (u (k - 1) * θ (k - 1) - 2 * u k * θ (k + 1))
      + Bt * (u k * θ (k - 1) - 2 * (u (k + 1)) * θ (k + 1)))

/-- The velocity component of the general four-parameter dyadic Boussinesq ODE. -/
def generalVelocityRHS (ν κ A B : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ :=
  boussinesqTransferU A B u k + κ * θ k - ν * dyadicWeight (2 * k) * u k

/-- The temperature component of the general four-parameter dyadic Boussinesq ODE. -/
def generalTemperatureRHS (μ At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ :=
  boussinesqTransferTheta At Bt u θ k - μ * dyadicWeight (2 * k) * θ k

/-- **The general four-parameter dyadic Boussinesq ODE**, as a pair `(du_k/dt, dθ_k/dt)`. -/
def generalBoussinesqRHS (ν μ κ A B At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ × ℝ :=
  (generalVelocityRHS ν κ A B u θ k, generalTemperatureRHS μ At Bt u θ k)

/-- The frozen Stage R velocity coupling: `A = 1`, `B = 0` (the Katz–Pavlović dyadic
self-interaction). -/
def dyadicVelocityRHS (ν κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ :=
  generalVelocityRHS ν κ 1 0 u θ k

/-- The frozen Stage R temperature coupling: `Ã = 1`, `B̃ = 1`. -/
def dyadicTemperatureRHS (μ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ :=
  generalTemperatureRHS μ 1 1 u θ k

/-- **The frozen Stage R two-species dyadic Boussinesq ODE** `(du_k/dt, dθ_k/dt)`. -/
def dyadicBoussinesqRHS (ν μ κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ × ℝ :=
  (dyadicVelocityRHS ν κ u θ k, dyadicTemperatureRHS μ u θ k)

/-- Velocity energy flux through the shell boundary `k`. -/
def velocityFlux (A B : ℝ) (u : ℤ → ℝ) (k : ℤ) : ℝ :=
  dyadicWeight k * (A * (u (k - 1)) ^ 2 * u k + B * u (k - 1) * (u k) ^ 2)

/-- Temperature (entropy) flux through the shell boundary `k`. -/
def temperatureFlux (At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ :=
  dyadicWeight k * (At * u (k - 1) * θ (k - 1) * θ k + Bt * u k * θ (k - 1) * θ k)

/-- The frozen model's velocity energy flux. -/
def dyadicVelocityFlux (u : ℤ → ℝ) (k : ℤ) : ℝ := velocityFlux 1 0 u k

/-- The frozen model's temperature entropy flux. -/
def dyadicTemperatureFlux (u θ : ℤ → ℝ) (k : ℤ) : ℝ := temperatureFlux 1 1 u θ k

/-- **Energy pairing = flux difference (velocity).** Pairing the velocity ladder with its
nonlinear transfer telescopes into a difference of the flux at `k` and `k+1`. -/
theorem velocity_pairing_eq_flux (A B : ℝ) (u : ℤ → ℝ) (k : ℤ) :
    u k * boussinesqTransferU A B u k = velocityFlux A B u k - velocityFlux A B u (k + 1) := by
  simp only [boussinesqTransferU, velocityFlux, dyadicWeight]
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  ring_nf

/-- **Energy pairing = flux difference (temperature).** -/
theorem temperature_pairing_eq_flux (At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    θ k * boussinesqTransferTheta At Bt u θ k
      = temperatureFlux At Bt u θ k - temperatureFlux At Bt u θ (k + 1) := by
  simp only [boussinesqTransferTheta, temperatureFlux, dyadicWeight]
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  ring_nf

/-- **Energy pairing = flux difference (frozen velocity model).** -/
theorem dyadic_velocity_pairing_eq_flux (u : ℤ → ℝ) (k : ℤ) :
    u k * boussinesqTransferU 1 0 u k = dyadicVelocityFlux u k - dyadicVelocityFlux u (k + 1) := by
  simpa [dyadicVelocityFlux] using velocity_pairing_eq_flux 1 0 u k

/-- **Energy pairing = flux difference (frozen temperature model).** -/
theorem dyadic_temperature_pairing_eq_flux (u θ : ℤ → ℝ) (k : ℤ) :
    θ k * boussinesqTransferTheta 1 1 u θ k
      = dyadicTemperatureFlux u θ k - dyadicTemperatureFlux u θ (k + 1) := by
  simpa [dyadicTemperatureFlux] using temperature_pairing_eq_flux 1 1 u θ k

end Cascade

#print axioms Cascade.velocity_pairing_eq_flux
#print axioms Cascade.temperature_pairing_eq_flux
#print axioms Cascade.dyadic_velocity_pairing_eq_flux
#print axioms Cascade.dyadic_temperature_pairing_eq_flux
