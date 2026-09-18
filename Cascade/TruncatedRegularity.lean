import Cascade.DissipationThreshold
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The truncated dyadic model is trivially globally regular

This file records what is **actually true** about the truncated dyadic Boussinesq model, after the
repair of the truncated solution predicates (`IsUnforcedTruncatedSolution` in
`Cascade/NoBlowup.lean`, `IsForcedTruncatedSolution` in `Cascade/ForcedModel.lean`,
`IsUnforcedTruncatedSolutionE` / `IsForcedTruncatedSolutionE` in
`Cascade/DissipationThreshold.lean`): the shell equation is imposed only on the retained shells
`0 ≤ k < N`, and the truncation is closed by the Dirichlet values `u(-1) = u(N) = θ(-1) = θ(N) = 0`.
Before the repair the equation was imposed on *all* of `ℤ`, which is inconsistent with `u t N = 0`
and made every theorem assuming the predicate vacuous.

## The honest statement

**The truncated model has no finite-time blowup, for every dissipation degree `e ≥ 0` and every
buoyancy coupling `κ`.**  The reasons are elementary:

* The nonlinear transfer **cancels exactly** on the retained range
  (`transfer_pairing_eq_zero`): pairing the velocity ladder with its own transfer telescopes into a
  difference of boundary fluxes, and the Dirichlet values at `-1` and `N` kill both.  The same
  telescoping holds for the temperature advection.
* Consequently the energy `E = ∑_{k<N} u_k²` obeys the **exact** identity
  (`truncated_energy_hasDerivAt`)

  `E' = 2κ ∑_{k<N} u_k θ_k − 2ν ∑_{k<N} 2^{ek} u_k²`.

  For `κ = 0` the energy is non-increasing (`energy_antitone_of_kappa_eq_zero`); in the special
  case `e = 0` the identity is `E' = −2νE` exactly
  (`truncated_energy_hasDerivAt_degree_zero`), i.e. **exponential decay**.
* On a **finite** range every weighted norm is **dominated by the energy**
  (`weighted_sq_le_energy`): for `s ≥ 0`,

  `∑_{k<N} 2^{sk} u_k² ≤ 2^{s(N−1)} · ∑_{k<N} u_k²`.

  The weight factor is the *largest* weight in the range, and it is a finite constant depending only
  on `N` and `s`.  So no weighted norm (energy, enstrophy, any `H^s`) can grow faster than the
  energy: the energy is non-increasing (`κ = 0`) or Grönwall-bounded (general `κ`, via
  `velocity_energy_rate_le_of_solution_degreeE` and the abstract engine
  `no_finite_time_blowup`).  This is the content of
  `truncated_unforced_energy_bounded_degreeE` and
  `truncated_enstrophy_bounded_degreeE`.

## Why blowup needs the *untruncated* lattice

The domination `∑ 2^{sk} u_k² ≤ 2^{s(N−1)} E` uses that `N < ∞`.  On the **untruncated** lattice
`k ∈ ℕ` the weights `4^k → ∞` are unbounded and there is no such domination: a solution can lose
energy at low shells while its enstrophy, carried by ever higher shells, grows without bound — the
energy can decay while `∑ 4^k u_k²` diverges, and the nonlinear transfer is no longer a finite sum
whose boundary terms vanish.  Every genuine blowup scenario for these models therefore lives on the
untruncated lattice, not on any `N`-shell truncation.

## Consequences for the earlier chain of results

The earlier solution-level chain in this library is **superseded**:

* The no-blowup results (`truncated_unforced_energy_bounded`, `truncated_unforced_enstrophy_bounded`
  and their sign-free / forced variants) were **vacuous** under the old all-of-`ℤ` predicate, and are
  **trivially true** under the repaired predicate, since no finite range can support blowup.
* The blowup capstone `no_global_solution_degree_zero` (`Cascade/BlowupDegreeZero.lean`) is **false**
  on the repaired predicate: it has been **deleted**, together with its two auxiliary files
  `Cascade/BlowupRate.lean` and `Cascade/PositivityDegreeE.lean`.  The abstract engine
  `Cascade/BlowupEngine.lean` is correct and independent of any solution predicate, and is retained
  (currently unused) for a future untruncated-lattice argument.

## Contents

1. `transfer_pairing_eq_zero` — the transfer pairing cancels on the retained range.
2. `weighted_sq_le_energy` — finite-range weighted norms are energy-dominated.
3. `truncated_energy_hasDerivAt` (and the `e = 0` specialisation) — the energy identity.
4. `entropy_antitone_degreeE`, `velocity_energy_rate_le_of_solution_degreeE`,
   `truncated_unforced_energy_bounded_degreeE`, `truncated_enstrophy_bounded_degreeE`
   (a.k.a. `truncated_globally_regular`) — no finite-time blowup, for every `e ≥ 0` and every `κ`.
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators

namespace Cascade

/-! ## 1. The transfer pairing cancels on the retained range -/

/-- **Telescoping of the frozen velocity transfer pairing.** Summing
`u_k · boussinesqTransferU 1 0 u k` over the retained shells `0, …, N-1` collapses to the difference
of the energy flux across the boundary shells `0` and `N`. -/
theorem sum_velocityTransfer_eq_flux (u : ℤ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, u (k : ℤ) * boussinesqTransferU 1 0 u (k : ℤ))
      = dyadicVelocityFlux u 0 - dyadicVelocityFlux u (N : ℤ) := by
  have h : ∀ k ∈ Finset.range N,
      u (k : ℤ) * boussinesqTransferU 1 0 u (k : ℤ)
        = (fun m : ℕ => dyadicVelocityFlux u (m : ℤ)) k
          - (fun m : ℕ => dyadicVelocityFlux u (m : ℤ)) (k + 1) := by
    intro k _
    rw [dyadic_velocity_pairing_eq_flux]
    push_cast
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_range_sub']
  norm_num

/-- The frozen velocity energy flux at the bottom vanishes under `u(-1) = 0`. -/
theorem dyadicVelocityFlux_zero (u : ℤ → ℝ) (hbot : u (-1) = 0) :
    dyadicVelocityFlux u 0 = 0 := by
  simp only [dyadicVelocityFlux, velocityFlux]
  rw [show (0 : ℤ) - 1 = -1 by norm_num, hbot]
  ring

/-- The frozen velocity energy flux at the top vanishes under `u(N) = 0`. -/
theorem dyadicVelocityFlux_top (u : ℤ → ℝ) (N : ℕ) (htop : u (N : ℤ) = 0) :
    dyadicVelocityFlux u (N : ℤ) = 0 := by
  simp only [dyadicVelocityFlux, velocityFlux]
  rw [htop]
  ring

/-- **The transfer pairing cancels on the retained range: the Dirichlet ends kill the boundary
terms in the telescoping.** -/
theorem transfer_pairing_eq_zero (u : ℤ → ℝ) (N : ℕ) (hbot : u (-1) = 0) (htop : u (N : ℤ) = 0) :
    (∑ k ∈ Finset.range N, u (k : ℤ) * boussinesqTransferU 1 0 u (k : ℤ)) = 0 := by
  rw [sum_velocityTransfer_eq_flux, dyadicVelocityFlux_zero u hbot, dyadicVelocityFlux_top u N htop,
    sub_zero]

/-! ## 2. Finite-range weighted norms are energy-dominated -/

/-- The dyadic weight is non-decreasing in its exponent. -/
theorem dyadicWeight_mono {a b : ℤ} (h : a ≤ b) : dyadicWeight a ≤ dyadicWeight b := by
  unfold dyadicWeight
  exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h

/-- `2^m ≥ 1` for `m ≥ 0` (reproved here because the library's copy is private). -/
theorem one_le_dyadicWeight_of_nonneg {m : ℤ} (hm : 0 ≤ m) : (1 : ℝ) ≤ dyadicWeight m := by
  unfold dyadicWeight
  exact one_le_zpow₀ (by norm_num : (1 : ℝ) ≤ 2) hm

/-- **Every weighted norm is dominated by the energy on a finite range.**  For `s ≥ 0` the largest
weight in `k ∈ {0, …, N-1}` is `2^{s(N-1)}`, so

`∑_{k<N} 2^{sk} u_k² ≤ 2^{s(N−1)} · ∑_{k<N} u_k²`.

The finiteness of `N` is essential: this is exactly the estimate that fails on the untruncated
lattice, where `4^k` is unbounded. -/
theorem weighted_sq_le_energy (u : ℤ → ℝ) (N s : ℕ) :
    (∑ k ∈ Finset.range N, dyadicWeight ((s : ℤ) * (k : ℤ)) * (u (k : ℤ)) ^ 2)
      ≤ dyadicWeight ((s : ℤ) * ((N : ℤ) - 1)) * (∑ k ∈ Finset.range N, (u (k : ℤ)) ^ 2) := by
  have hmono : ∀ k ∈ Finset.range N,
      dyadicWeight ((s : ℤ) * (k : ℤ)) ≤ dyadicWeight ((s : ℤ) * ((N : ℤ) - 1)) := by
    intro k hk
    apply dyadicWeight_mono
    have hklt : (k : ℤ) < (N : ℤ) := by exact_mod_cast Finset.mem_range.mp hk
    have hsk : (0 : ℤ) ≤ (s : ℤ) := Int.natCast_nonneg s
    have hle : (k : ℤ) ≤ (N : ℤ) - 1 := by omega
    exact mul_le_mul_of_nonneg_left hle hsk
  calc (∑ k ∈ Finset.range N, dyadicWeight ((s : ℤ) * (k : ℤ)) * (u (k : ℤ)) ^ 2)
      ≤ ∑ k ∈ Finset.range N, dyadicWeight ((s : ℤ) * ((N : ℤ) - 1)) * (u (k : ℤ)) ^ 2 :=
        Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hmono k hk) (sq_nonneg _)
    _ = dyadicWeight ((s : ℤ) * ((N : ℤ) - 1)) * (∑ k ∈ Finset.range N, (u (k : ℤ)) ^ 2) := by
        rw [Finset.mul_sum]

/-! ## 3. The energy identity along a truncated degree-`e` solution -/

/-- **Telescoping of the frozen temperature transfer pairing.** -/
theorem sum_temperatureTransfer_eq_flux (u θ : ℤ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, θ (k : ℤ) * boussinesqTransferTheta 1 1 u θ (k : ℤ))
      = dyadicTemperatureFlux u θ 0 - dyadicTemperatureFlux u θ (N : ℤ) := by
  have h : ∀ k ∈ Finset.range N,
      θ (k : ℤ) * boussinesqTransferTheta 1 1 u θ (k : ℤ)
        = (fun m : ℕ => dyadicTemperatureFlux u θ (m : ℤ)) k
          - (fun m : ℕ => dyadicTemperatureFlux u θ (m : ℤ)) (k + 1) := by
    intro k _
    rw [dyadic_temperature_pairing_eq_flux]
    push_cast
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_range_sub']
  norm_num

/-- **The velocity pairing at degree `e`, as the exact energy budget.**  The nonlinear transfer
telescopes into boundary fluxes, the buoyancy `κ ∑ u_k θ_k` is the only source and the degree-`e`
dissipation `ν ∑ 2^{ek} u_k²` the only sink. -/
theorem sum_velocityRHS_degreeE (ν κ : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, u (k : ℤ) * velocityRHSDegreeE ν κ 1 0 e u θ (k : ℤ))
      = dyadicVelocityFlux u 0 - dyadicVelocityFlux u (N : ℤ)
        + κ * (∑ k ∈ Finset.range N, u (k : ℤ) * θ (k : ℤ))
        - ν * (∑ k ∈ Finset.range N, dyadicWeight (e * (k : ℤ)) * (u (k : ℤ)) ^ 2) := by
  have hsplit : ∀ k ∈ Finset.range N,
      u (k : ℤ) * velocityRHSDegreeE ν κ 1 0 e u θ (k : ℤ)
        = u (k : ℤ) * boussinesqTransferU 1 0 u (k : ℤ) + κ * (u (k : ℤ) * θ (k : ℤ))
          - ν * (dyadicWeight (e * (k : ℤ)) * (u (k : ℤ)) ^ 2) := by
    intro k _
    simp only [velocityRHSDegreeE]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_velocityTransfer_eq_flux, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The degree-`e` velocity pairing under the Dirichlet conditions: the boundary fluxes vanish, so
only buoyancy and dissipation survive. -/
theorem velocity_pairing_degreeE (ν κ : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (N : ℕ)
    (hbot : u (-1) = 0) (htop : u (N : ℤ) = 0) :
    (∑ k ∈ Finset.range N, u (k : ℤ) * velocityRHSDegreeE ν κ 1 0 e u θ (k : ℤ))
      = κ * (∑ k ∈ Finset.range N, u (k : ℤ) * θ (k : ℤ))
        - ν * (∑ k ∈ Finset.range N, dyadicWeight (e * (k : ℤ)) * (u (k : ℤ)) ^ 2) := by
  rw [sum_velocityRHS_degreeE, dyadicVelocityFlux_zero u hbot, dyadicVelocityFlux_top u N htop,
    sub_zero]
  ring

/-- **The temperature pairing at degree `e`.**  The advection telescopes and the Dirichlet ends kill
the boundary fluxes, leaving only the thermal dissipation `−μ ∑ 2^{ek} θ_k²`. -/
theorem temperature_pairing_degreeE_dirichlet (μ : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (N : ℕ)
    (hθbot : θ (-1) = 0) (hθtop : θ (N : ℤ) = 0) :
    (∑ k ∈ Finset.range N, θ (k : ℤ) * temperatureRHSDegreeE μ 1 1 e u θ (k : ℤ))
      = - μ * (∑ k ∈ Finset.range N, dyadicWeight (e * (k : ℤ)) * (θ (k : ℤ)) ^ 2) := by
  have hsplit : ∀ k ∈ Finset.range N,
      θ (k : ℤ) * temperatureRHSDegreeE μ 1 1 e u θ (k : ℤ)
        = θ (k : ℤ) * boussinesqTransferTheta 1 1 u θ (k : ℤ)
          - μ * (dyadicWeight (e * (k : ℤ)) * (θ (k : ℤ)) ^ 2) := by
    intro k _
    simp only [temperatureRHSDegreeE]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
  have h0 : dyadicTemperatureFlux u θ 0 = 0 := by
    simp only [dyadicTemperatureFlux, temperatureFlux]
    rw [show (0 : ℤ) - 1 = -1 by norm_num, hθbot]
    ring
  have hN : dyadicTemperatureFlux u θ (N : ℤ) = 0 := by
    simp only [dyadicTemperatureFlux, temperatureFlux]
    rw [hθtop]
    ring
  rw [sum_temperatureTransfer_eq_flux, h0, hN, zero_sub, neg_zero, zero_sub, ← Finset.mul_sum]
  ring

/-- On the physical shells `k ≥ 0` the degree-`e` viscous weight `2^{ek}` is at least `1` when
`e ≥ 0`, hence `∑ u_k² ≤ ∑ 2^{ek} u_k²`. -/
theorem sum_sq_le_sum_weighted_sq_degreeE (e : ℤ) (he : 0 ≤ e) (u : ℤ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (u (k : ℤ)) ^ 2)
      ≤ ∑ k ∈ Finset.range N, dyadicWeight (e * (k : ℤ)) * (u (k : ℤ)) ^ 2 := by
  apply Finset.sum_le_sum
  intro k _
  have hk : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  have h2k : (0 : ℤ) ≤ e * (k : ℤ) := mul_nonneg he hk
  have h1 : (1 : ℝ) ≤ dyadicWeight (e * (k : ℤ)) := one_le_dyadicWeight_of_nonneg h2k
  calc (u (k : ℤ)) ^ 2 = (u (k : ℤ)) ^ 2 * 1 := (mul_one _).symm
    _ ≤ (u (k : ℤ)) ^ 2 * dyadicWeight (e * (k : ℤ)) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = dyadicWeight (e * (k : ℤ)) * (u (k : ℤ)) ^ 2 := mul_comm _ _

/-- **The time derivative of the energy along a truncated degree-`e` solution.**  Differentiating
`∑_{k<N} (u s k)²` term by term and using the pairing identity gives the exact energy identity

`E' = 2κ ∑_{k<N} u_k θ_k − 2ν ∑_{k<N} 2^{ek} u_k²`. -/
theorem truncated_energy_hasDerivAt (ν μ κ : ℝ) (e : ℤ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ) (t : ℝ) :
    HasDerivAt (fun s => velocityEnergy (u s) N)
      (2 * κ * (∑ k ∈ Finset.range N, u t (k : ℤ) * θ t (k : ℤ))
        - 2 * ν * (∑ k ∈ Finset.range N,
            dyadicWeight (e * (k : ℤ)) * (u t (k : ℤ)) ^ 2)) t := by
  have hsum : HasDerivAt (∑ k ∈ Finset.range N, fun s : ℝ => (u s (k : ℤ)) ^ 2)
      (∑ k ∈ Finset.range N,
        2 * u t (k : ℤ) * velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ)) t :=
    HasDerivAt.sum (u := Finset.range N)
      (A := fun k s => (u s (k : ℤ)) ^ 2)
      (A' := fun k => 2 * u t (k : ℤ) * velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ))
      (fun k hk => by
        have hd := (h.1 t (k : ℤ) (Int.natCast_nonneg k)
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
        2 * u t (k : ℤ) * velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ))
      = 2 * ∑ k ∈ Finset.range N,
          u t (k : ℤ) * velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [heq] at hsum
  have hid := velocity_pairing_degreeE ν κ e (u t) (θ t) N (h.2.2 t).1 (h.2.2 t).2.1
  rw [hid] at hsum
  have hEv : (fun s => velocityEnergy (u s) N)
      = fun s => ∑ k ∈ Finset.range N, (u s (k : ℤ)) ^ 2 := by
    funext s
    rw [velocityEnergy]
  rw [hEv]
  convert hsum using 1
  ring

/-- **The `e = 0`, `κ = 0` energy identity is exponential decay**: `E' = −2νE` exactly. -/
theorem truncated_energy_hasDerivAt_degree_zero (ν μ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ 0 0 N u θ) (t : ℝ) :
    HasDerivAt (fun s => velocityEnergy (u s) N) (-2 * ν * velocityEnergy (u t) N) t := by
  have hd := truncated_energy_hasDerivAt ν μ 0 0 N u θ h t
  have hval : 2 * 0 * (∑ k ∈ Finset.range N, u t (k : ℤ) * θ t (k : ℤ))
      - 2 * ν * (∑ k ∈ Finset.range N,
          dyadicWeight (0 * (k : ℤ)) * (u t (k : ℤ)) ^ 2)
      = -2 * ν * velocityEnergy (u t) N := by
    have hsum : (∑ k ∈ Finset.range N, dyadicWeight (0 * (k : ℤ)) * (u t (k : ℤ)) ^ 2)
        = ∑ k ∈ Finset.range N, (u t (k : ℤ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      simp [dyadicWeight]
    rw [velocityEnergy, hsum]
    ring
  rwa [hval] at hd

/-! ## 4. No finite-time blowup, for every `e ≥ 0` and every `κ` -/

/-- **Thermal entropy is non-increasing along a truncated degree-`e` solution** (`μ ≥ 0`): the
temperature pairing is `−μ ∑ 2^{ek} θ_k² ≤ 0`. -/
theorem entropy_antitone_degreeE (ν μ κ : ℝ) (hμ : 0 ≤ μ) (e : ℤ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ) :
    Antitone fun t => entropy (θ t) N := by
  refine antitone_of_hasDerivAt_nonpos
    (f' := fun t => 2 * ∑ k ∈ Finset.range N,
      θ t (k : ℤ) * temperatureRHSDegreeE μ 1 1 e (u t) (θ t) (k : ℤ)) ?_ ?_
  · intro t
    exact entropy_hasDerivAt_degreeE ν μ κ e N u θ h t
  · intro t
    have hpair := temperature_pairing_degreeE_dirichlet μ e (u t) (θ t) N
      (h.2.2 t).2.2.1 (h.2.2 t).2.2.2
    have hDnn : 0 ≤ ∑ k ∈ Finset.range N,
        dyadicWeight (e * (k : ℤ)) * (θ t (k : ℤ)) ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (dyadicWeight_nonneg _) (sq_nonneg _)
    have hD : -μ * (∑ k ∈ Finset.range N,
        dyadicWeight (e * (k : ℤ)) * (θ t (k : ℤ)) ^ 2) ≤ 0 := by
      have : 0 ≤ μ * (∑ k ∈ Finset.range N,
          dyadicWeight (e * (k : ℤ)) * (θ t (k : ℤ)) ^ 2) := mul_nonneg hμ hDnn
      linarith
    have h2 := mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 2) hD
    simpa [hpair] using h2

/-- **The sign-free energy rate inequality at degree `e ≥ 0`.**  Using that the entropy is
non-increasing (`hanti`),

`E' ≤ 2|κ| √S(0) √E − 2νE`.

The sign of `κ` is handled by `buoyancy_energy_le_abs`, and the degree-`e` dissipation dominates the
plain energy because `2^{ek} ≥ 1` for `e, k ≥ 0`. -/
theorem velocity_energy_rate_le_of_solution_degreeE (ν μ κ : ℝ) (hν : 0 ≤ ν)
    (e : ℤ) (he : 0 ≤ e) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ)
    (hanti : Antitone fun t => entropy (θ t) N) {t : ℝ} (ht : 0 ≤ t) :
    2 * (∑ k ∈ Finset.range N,
        u t (k : ℤ) * velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ))
      ≤ 2 * |κ| * Real.sqrt (entropy (θ 0) N) * Real.sqrt (velocityEnergy (u t) N)
        - 2 * ν * velocityEnergy (u t) N := by
  have hpair := velocity_pairing_degreeE ν κ e (u t) (θ t) N (h.2.2 t).1 (h.2.2 t).2.1
  have hb := buoyancy_energy_le_abs κ (u t) (θ t) N
  have hw := sum_sq_le_sum_weighted_sq_degreeE e he (u t) N
  have hνw : ν * velocityEnergy (u t) N
      ≤ ν * (∑ k ∈ Finset.range N, dyadicWeight (e * (k : ℤ)) * (u t (k : ℤ)) ^ 2) :=
    mul_le_mul_of_nonneg_left (by simpa [velocityEnergy] using hw) hν
  have hpair' : (∑ k ∈ Finset.range N,
        u t (k : ℤ) * velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ))
      ≤ |κ| * (Real.sqrt (velocityEnergy (u t) N) * Real.sqrt (entropy (θ t) N))
        - ν * velocityEnergy (u t) N := by
    rw [hpair]
    linarith
  have h2 : 2 * (∑ k ∈ Finset.range N,
        u t (k : ℤ) * velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ))
      ≤ 2 * (|κ| * (Real.sqrt (velocityEnergy (u t) N) * Real.sqrt (entropy (θ t) N))
        - ν * velocityEnergy (u t) N) :=
    mul_le_mul_of_nonneg_left hpair' (by norm_num)
  have hcoef : 0 ≤ 2 * |κ| * Real.sqrt (velocityEnergy (u t) N) :=
    mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg κ)) (Real.sqrt_nonneg _)
  have hstep := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hanti ht)) hcoef
  nlinarith [h2, hstep]

/-- The same rate inequality in the "exact identity" form, i.e. for the derivative produced by
`truncated_energy_hasDerivAt`. -/
theorem energy_rate_le_of_solution_degreeE (ν μ κ : ℝ) (hν : 0 ≤ ν) (e : ℤ) (he : 0 ≤ e)
    (N : ℕ) (u θ : ℝ → ℤ → ℝ) (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ)
    (hanti : Antitone fun t => entropy (θ t) N) {t : ℝ} (ht : 0 ≤ t) :
    2 * κ * (∑ k ∈ Finset.range N, u t (k : ℤ) * θ t (k : ℤ))
        - 2 * ν * (∑ k ∈ Finset.range N,
            dyadicWeight (e * (k : ℤ)) * (u t (k : ℤ)) ^ 2)
      ≤ 2 * |κ| * Real.sqrt (entropy (θ 0) N) * Real.sqrt (velocityEnergy (u t) N)
        - 2 * ν * velocityEnergy (u t) N := by
  have hrate := velocity_energy_rate_le_of_solution_degreeE ν μ κ hν e he N u θ h hanti ht
  rw [velocity_pairing_degreeE ν κ e (u t) (θ t) N (h.2.2 t).1 (h.2.2 t).2.1] at hrate
  linarith [hrate]

/-- **No finite-time energy blowup at any degree `e ≥ 0`, for any sign of `κ`.**  The energy is
bounded on every compact time interval `[0, T]` by an explicit constant. -/
theorem truncated_unforced_energy_bounded_degreeE (ν μ κ : ℝ) (hν : 0 < ν) (hμ : 0 ≤ μ)
    (e : ℤ) (he : 0 ≤ e) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ)
    {T : ℝ} (hcont : ContinuousOn (fun t => velocityEnergy (u t) N) (Set.Icc 0 T))
    (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, velocityEnergy (u t) N ≤ C := by
  have hanti := entropy_antitone_degreeE ν μ κ hμ e N u θ h
  refine no_finite_time_blowup (E := fun t => velocityEnergy (u t) N)
    (E' := fun t => 2 * κ * (∑ k ∈ Finset.range N, u t (k : ℤ) * θ t (k : ℤ))
      - 2 * ν * (∑ k ∈ Finset.range N,
          dyadicWeight (e * (k : ℤ)) * (u t (k : ℤ)) ^ 2))
    (S₀ := entropy (θ 0) N) (κ := |κ|) (abs_nonneg κ) (entropy_nonneg (θ 0) N) hν ?_ ?_ ?_ ?_
    T hT
  · exact (truncated_energy_hasDerivAt ν μ κ e N u θ h 0).continuousAt
  · intro t _
    exact velocityEnergy_nonneg (u t) N
  · intro t _
    exact truncated_energy_hasDerivAt ν μ κ e N u θ h t
  · intro t ht
    exact energy_rate_le_of_solution_degreeE ν μ κ hν.le e he N u θ h hanti (le_of_lt ht)

/-- **In the isothermal case `κ = 0` the energy is non-increasing**, for every degree `e ≥ 0`. -/
theorem energy_antitone_of_kappa_eq_zero (ν μ : ℝ) (hν : 0 ≤ ν) (e : ℤ) (he : 0 ≤ e) (N : ℕ)
    (u θ : ℝ → ℤ → ℝ) (h : IsUnforcedTruncatedSolutionE ν μ 0 e N u θ) :
    Antitone fun t => velocityEnergy (u t) N := by
  refine antitone_of_hasDerivAt_nonpos
    (f' := fun t => 2 * 0 * (∑ k ∈ Finset.range N, u t (k : ℤ) * θ t (k : ℤ))
      - 2 * ν * (∑ k ∈ Finset.range N,
          dyadicWeight (e * (k : ℤ)) * (u t (k : ℤ)) ^ 2)) ?_ ?_
  · intro t
    exact truncated_energy_hasDerivAt ν μ 0 e N u θ h t
  · intro t
    have hw := sum_sq_le_sum_weighted_sq_degreeE e he (u t) N
    have hDnn : 0 ≤ ∑ k ∈ Finset.range N,
        dyadicWeight (e * (k : ℤ)) * (u t (k : ℤ)) ^ 2 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (dyadicWeight_nonneg _) (sq_nonneg _)
    have hE : (0 : ℝ) ≤ velocityEnergy (u t) N := velocityEnergy_nonneg (u t) N
    have hEw : velocityEnergy (u t) N
        ≤ ∑ k ∈ Finset.range N, dyadicWeight (e * (k : ℤ)) * (u t (k : ℤ)) ^ 2 := by
      simpa [velocityEnergy] using hw
    have h2ν : 0 ≤ 2 * ν := by linarith
    have hprod : 0 ≤ 2 * ν * (∑ k ∈ Finset.range N,
        dyadicWeight (e * (k : ℤ)) * (u t (k : ℤ)) ^ 2) := mul_nonneg h2ν hDnn
    show 2 * 0 * (∑ k ∈ Finset.range N, u t (k : ℤ) * θ t (k : ℤ))
      - 2 * ν * (∑ k ∈ Finset.range N,
          dyadicWeight (e * (k : ℤ)) * (u t (k : ℤ)) ^ 2) ≤ 0
    nlinarith [hprod]

/-- **The truncated degree-`e` model is globally regular (no finite-time blowup), for every
`e ≥ 0` and every `κ`.**  The enstrophy `H = ∑_{k<N} 4^k u_k²` is bounded on every compact time
interval `[0, T]`; indeed, by `weighted_sq_le_energy` (with `s = 2`) it is controlled by the energy,
which is bounded by `truncated_unforced_energy_bounded_degreeE`. -/
theorem truncated_enstrophy_bounded_degreeE (ν μ κ : ℝ) (hν : 0 < ν) (hμ : 0 ≤ μ)
    (e : ℤ) (he : 0 ≤ e) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ)
    {T : ℝ} (hcont : ContinuousOn (fun t => velocityEnergy (u t) N) (Set.Icc 0 T))
    (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, enstrophy (u t) N ≤ C := by
  obtain ⟨E₀, hE₀⟩ :=
    truncated_unforced_energy_bounded_degreeE ν μ κ hν hμ e he N u θ h hcont hT
  refine ⟨dyadicWeight ((2 : ℤ) * ((N : ℤ) - 1)) * max E₀ 0, ?_⟩
  intro t ht
  have hw := weighted_sq_le_energy (u t) N 2
  have hE : velocityEnergy (u t) N ≤ max E₀ 0 := (hE₀ t ht).trans (le_max_left _ _)
  calc enstrophy (u t) N
      = ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * (u t (k : ℤ)) ^ 2 := by
        rw [enstrophy]
    _ ≤ dyadicWeight ((2 : ℤ) * ((N : ℤ) - 1)) * (∑ k ∈ Finset.range N, (u t (k : ℤ)) ^ 2) := by
        simpa using hw
    _ = dyadicWeight ((2 : ℤ) * ((N : ℤ) - 1)) * velocityEnergy (u t) N := by
        rw [velocityEnergy]
    _ ≤ dyadicWeight ((2 : ℤ) * ((N : ℤ) - 1)) * max E₀ 0 :=
        mul_le_mul_of_nonneg_left hE (dyadicWeight_nonneg _)

/-- **The truncated model is globally regular, trivially.**  This is the headline statement:
no finite-time blowup of the enstrophy (hence of any finite-range weighted norm, by
`weighted_sq_le_energy`) for the truncated degree-`e` model, every `e ≥ 0` and every `κ`. -/
theorem truncated_globally_regular (ν μ κ : ℝ) (hν : 0 < ν) (hμ : 0 ≤ μ)
    (e : ℤ) (he : 0 ≤ e) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ)
    {T : ℝ} (hcont : ContinuousOn (fun t => velocityEnergy (u t) N) (Set.Icc 0 T))
    (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, enstrophy (u t) N ≤ C :=
  truncated_enstrophy_bounded_degreeE ν μ κ hν hμ e he N u θ h hcont hT

/-! ## 5. Non-vacuity

**Read this before trusting any theorem in the library that assumes a solution predicate.** The
episode this file exists to repair happened because every "non-vacuity check" in the library was
performed on the *zero* state — which at the time was the only solution the (inconsistent)
predicate admitted. A satisfied predicate is not a non-vacuity proof: the check that matters is a
genuinely **nonzero** witness. The first example below is that witness. -/

/-- **THE GUARD: the repaired predicate is satisfied by a NONZERO solution.** For `N = 1`, `ν = 1`,
`e = 0`, `κ = 0` the retained shell obeys `u₀' = -ν u₀` exactly — the transfer vanishes because
`u(-1) = u(1) = 0` — so `u₀(t) = exp (-t)` is an explicit nonzero solution, by elementary
differentiation. The old all-`ℤ` predicate rejected exactly this data (its equation at `k = 1`
would read `0 = 2 exp (-2t) ≠ 0`), which is why the old predicate forced `u ≡ 0`. Any future change
to `IsUnforcedTruncatedSolutionE` that breaks this example has reintroduced the bug. -/
example : IsUnforcedTruncatedSolutionE 1 0 0 0 1
    (fun t k => if k = 0 then Real.exp (-t) else 0)
    (fun _ _ => (0 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t k hk0 hkN
    have hk : k = 0 := by omega
    subst hk
    have hderiv : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
    have hrhs : velocityRHSDegreeE 1 0 1 0 0
        (fun j : ℤ => if j = 0 then Real.exp (-t) else 0) (fun _ => (0 : ℝ)) 0
        = -Real.exp (-t) := by
      simp [velocityRHSDegreeE, boussinesqTransferU, dyadicWeight]
    rw [hrhs]
    simpa using hderiv
  · intro t k hk0 hkN
    have hrhs : temperatureRHSDegreeE 0 1 1 0
        (fun j : ℤ => if j = 0 then Real.exp (-t) else 0) (fun _ => (0 : ℝ)) k = 0 := by
      simp [temperatureRHSDegreeE, boussinesqTransferTheta, dyadicWeight]
    rw [hrhs]
    exact hasDerivAt_const t 0
  · intro t
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- The witness above is **nonzero** at time `0`, so it is not the trivial solution. -/
example : (fun t k => if k = 0 then Real.exp (-t) else 0) 0 0 = 1 := by norm_num

/-- The zero state is an equilibrium of the degree-`e` model, so the regularity theorems are
instantiated at a genuine solution. (Kept for interface coverage, but **not** a non-vacuity proof
on its own — see the nonzero witness above.) -/
example : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2 ≤ C := by
  refine truncated_globally_regular 1 1 1 (by norm_num) (by norm_num) 0 (by norm_num) 2
    (fun _ _ => 0) (fun _ _ => 0) (zero_is_unforcedTruncatedSolutionE 1 1 1 0 2) ?_ (by norm_num)
  have hfun : (fun t => velocityEnergy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2)
      = fun _ => (0 : ℝ) := by
    funext t
    simp [velocityEnergy]
  rw [hfun]
  exact continuousOn_const

/-- The weighted domination is sharp at a single-mode state: for `u = δ_1` on the shells
`0, 1, 2` the weighted sum `∑_{k<3} 2^{2k} u_k² = 4` and the energy is `1`, matching the bound
`2^{2·(3−1)}·1 = 16` with room to spare (the bound is not tight here, only correct). -/
example : (∑ k ∈ Finset.range 3,
      dyadicWeight ((2 : ℤ) * (k : ℤ)) * (((fun j : ℤ => if j = 1 then (1 : ℝ) else 0)) (k : ℤ)) ^ 2)
    ≤ dyadicWeight ((2 : ℤ) * ((3 : ℤ) - 1))
      * (∑ k ∈ Finset.range 3, (((fun j : ℤ => if j = 1 then (1 : ℝ) else 0)) (k : ℤ)) ^ 2) :=
  weighted_sq_le_energy (fun j : ℤ => if j = 1 then (1 : ℝ) else 0) 3 2

end Cascade

/-! ## Axiom audit -/

#print axioms Cascade.sum_velocityTransfer_eq_flux
#print axioms Cascade.transfer_pairing_eq_zero
#print axioms Cascade.dyadicWeight_mono
#print axioms Cascade.one_le_dyadicWeight_of_nonneg
#print axioms Cascade.weighted_sq_le_energy
#print axioms Cascade.sum_temperatureTransfer_eq_flux
#print axioms Cascade.sum_velocityRHS_degreeE
#print axioms Cascade.velocity_pairing_degreeE
#print axioms Cascade.temperature_pairing_degreeE_dirichlet
#print axioms Cascade.sum_sq_le_sum_weighted_sq_degreeE
#print axioms Cascade.truncated_energy_hasDerivAt
#print axioms Cascade.truncated_energy_hasDerivAt_degree_zero
#print axioms Cascade.entropy_antitone_degreeE
#print axioms Cascade.velocity_energy_rate_le_of_solution_degreeE
#print axioms Cascade.energy_rate_le_of_solution_degreeE
#print axioms Cascade.truncated_unforced_energy_bounded_degreeE
#print axioms Cascade.energy_antitone_of_kappa_eq_zero
#print axioms Cascade.truncated_enstrophy_bounded_degreeE
#print axioms Cascade.truncated_globally_regular
