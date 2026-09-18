import Cascade.Enstrophy
import Cascade.Riccati
import Cascade.BoussinesqEnergy
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Stage O′ capstone — no finite-time **enstrophy** (`H¹`) blowup

This file is the **capstone of Stage O′**, the enstrophy (`H¹`) companion of the Stage-O energy
capstone `Cascade/NoBlowup.lean`. It closes the chain

* `Cascade/Enstrophy.lean` — the exact enstrophy pairing identity and its pointwise bound,
* `Cascade/Riccati.lean` — the Bernoulli/Riccati barrier engine,
* `Cascade/Gronwall.lean` — the abstract linear Grönwall engine,

into the statement that along an unforced truncated dyadic Boussinesq solution the **enstrophy**
`H = ∑_{k<N} 4^k u_k²` stays bounded on every compact time interval `[0, T]`, i.e. the model has
no finite-time blowup in the norm in which blowup is measured.

## Why energy is not enough, and why the budget is *cubic* versus *quadratic*

The Stage-O capstone bounds the velocity **energy** `E = ∑_{k<N} u_k²`. Energy is the wrong norm:
the velocity transfer conserves energy *exactly* (`∑_{k<N} u_k T^u_k = 0` under Dirichlet, proved
in `Cascade/Boussinesq.lean` as `dyadic_velocity_pairing_eq_flux`), so the energy budget sees no
cascade at all. The **enstrophy** `H = ∑_{k<N} 4^k u_k²` does see it. The identity
`Cascade.enstrophy_pairing` computes the weighted pairing

`∑_{k<N} 4^k u_k T^u_k = 3 ∑_{k<N} a_{k-1}² a_k`,  `a_k = 2^k u_k` (`vorticity u k`),

a pure **cubic** bulk sum: the transfer is *not* enstrophy-conserving (the boundary "enstrophy
flux" vanishes by Dirichlet, but the bulk cubic term survives). Weighting the equation by `4^k u_k`
gives the enstrophy budget

`H' = 2 ∑ 4^k u_k (du_k/dt) ≤ 6 H^{3/2} + κ (H + T) − 2 ν H²/E_max`,

where `T = tempEnstrophy` and `E_max` is an energy ceiling. The transfer enters at **homogeneity
`3/2`** (`H^{3/2}`) while the viscous dissipation enters at **homogeneity `2`** (`H²/E`, by the
interpolation `H² ≤ (∑ 16^k u_k²) E`). Hence the ratio

`H^{3/2} / (H²/E) = E/√H → 0`  as `H → ∞`,

which is the correct, scale-invariant form of "dissipation beats transfer". Above the threshold
`H ~ (E/ν)²` the enstrophy rate is strictly negative, so `H` cannot cross that threshold.

## The Lyapunov correction

The buoyancy source `κ (H + T)` is *not* dissipative: it is proportional to the temperature
enstrophy `T = ∑ 4^k θ_k²`, which is itself only dissipated. The temperature identity
`∑_{k<N} θ_k (dθ_k/dt) = −μ T` (Dirichlet; `Cascade.BoussinesqEnergy`) shows that the corrected
Lyapunov function

`Ψ = H + (κ/(2μ)) S`,  `S = entropy θ N = ∑_{k<N} θ_k²`,

has derivative in which the `+κT` source and the `(κ/2μ)·(−2μT)` sink **cancel exactly**, leaving

`Ψ' ≤ 6 H^{3/2} + κ H − 2 ν H²/E_max`.

The two remaining superlinear sources are absorbed into the quadratic dissipation by Young's
inequality, leaving the explicit constant

`C = 2187/(16 γ³) + κ²/(4γ)`,  `γ = ν/E_max`:

`6 H^{3/2} ≤ γ H² + 2187/(16 γ³)`  and  `κ H ≤ γ H² + κ²/(4γ)`.

Grönwall with `b = 0` then gives `Ψ t ≤ Ψ 0 + C t ≤ Ψ 0 + C T`: the enstrophy is bounded on every
compact `[0, T]` by a constant **linear in `T`**, so there is no finite-time blowup in the
`H¹`/enstrophy norm. For `κ = 0` the source is absent and the Bernoulli barrier
(`Cascade.le_of_deriv_le_bernoulli`) gives the **uniform-in-time** bound
`H t ≤ max (H 0) (3 E_max/ν)²` directly.

The linear-in-`T` form is an artifact of this particular Grönwall route: the argument above never
uses that the range `k < N` is finite, i.e. it never uses the finite-range norm cap. Truncation is
the **safe** direction, not a dangerous one: on a finite range every weighted norm is dominated by
the energy (`Cascade.weighted_sq_le_energy`), so the enstrophy cannot outrun the energy and there is
no blowup at any dissipation degree `e ≥ 0` and any `κ` (`Cascade/TruncatedRegularity.lean`).

## Contents

1. `enstrophy_hasDerivAt` — the time derivative of `H` along a solution.
2. `enstrophy_rate_le_of_solution` — the pointwise rate bound `H' ≤ 6H^{3/2}+κ(H+T)−2νH²/E_max`.
3. `enstrophyLyapunov` + `enstrophyLyapunov_deriv_le` — the corrected Lyapunov function and the
   explicit constant `C`.
4. `truncated_unforced_enstrophy_bounded` — the Stage-O′ capstone.
5. `enstrophy_bounded_isothermal` — the κ = 0 uniform bound.
6. Non-vacuity: the zero solution, the tightness of both Young constants, and concrete numerical
   evaluations.
-/

noncomputable section

-- Several standing hypotheses (`hμ`, `hcont`, the unused `ν` of the Lyapunov definition)
-- document the intended regime but are not all used by the proofs below.
set_option linter.unusedVariables false

open scoped BigOperators

namespace Cascade

/-! ## 1. Differentiating the enstrophy along a solution -/

/-- **The time derivative of the enstrophy along a truncated solution.** Differentiating the
finite sum `∑_{k<N} 4^k (u s k)²` term by term and applying the chain rule gives `2` times the
weighted pairing of the velocity equation. This is the enstrophy analogue of
`velocityEnergy_hasDerivAt`. -/
theorem enstrophy_hasDerivAt (ν μ κ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolution ν μ κ N u θ) (t : ℝ) :
    HasDerivAt (fun s => enstrophy (u s) N)
      (2 * ∑ k ∈ Finset.range N,
        dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
          * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ)) t := by
  have hterm : ∀ k ∈ Finset.range N,
      HasDerivAt (fun s : ℝ => dyadicWeight (2 * (k : ℤ)) * (u s (k : ℤ)) ^ 2)
        (dyadicWeight (2 * (k : ℤ))
          * (2 * u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))) t := by
    intro k hk
    have hd := (h.1 t (k : ℤ) (Int.natCast_nonneg k)
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
      * (2 * u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))) hterm
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
          * (2 * u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ)))
      = 2 * ∑ k ∈ Finset.range N,
          dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
            * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [heq] at hsum
  exact hsum

/-! ## 2. The temperature pairing identity under Dirichlet -/

/-- **The temperature pairing is `−μ T` under Dirichlet conditions.** From the frozen temperature
energy identity `dyadic_temperature_energy_identity`, the two boundary entropy fluxes
(`dyadicTemperatureFlux u θ 0` and at `N`) vanish because `θ(-1) = θ(N) = 0`, leaving only the
thermal dissipation `−μ ∑_{k<N} 4^k θ_k² = −μ T`. This is the exact cancellation partner of the
buoyancy source in the Lyapunov function. -/
theorem temperature_pairing_eq_neg_mu_tempEnstrophy (μ : ℝ) (u θ : ℤ → ℝ) (N : ℕ)
    (hθBot : θ (-1) = 0) (hθTop : θ (N : ℤ) = 0) :
    (∑ k ∈ Finset.range N, θ (k : ℤ) * dyadicTemperatureRHS μ u θ (k : ℤ))
      = - μ * tempEnstrophy θ N := by
  rw [dyadic_temperature_energy_identity]
  have h0 : dyadicTemperatureFlux u θ 0 = 0 := by
    simp [dyadicTemperatureFlux, temperatureFlux, hθBot]
  have hN : dyadicTemperatureFlux u θ (N : ℤ) = 0 := by
    simp [dyadicTemperatureFlux, temperatureFlux, hθTop]
  rw [h0, hN, tempEnstrophy]
  ring

/-! ## 3. The pointwise enstrophy rate bound along a solution -/

/-- **The pointwise enstrophy rate inequality along an unforced truncated solution.** With
`H = enstrophy (u t) N`, `T = tempEnstrophy (θ t) N` and an energy ceiling
`E_max ≥ velocityEnergy (u t) N`,

`2 ∑_{k<N} 4^k u_k (du_k/dt) ≤ 6 H √H + κ (H + T) − 2 ν H²/E_max`.

The cubic transfer is bounded by `3 H √H` (doubled: `6 H √H`), the buoyancy `κ √H √T` is
AM–GM-ed into `κ (H + T)`, and the dissipation `ν H²/E` is weakened to `ν H²/E_max` using
`E ≤ E_max`. When `E = 0` the state vanishes on the retained shells (a sum of squares is zero
only if every term is), so `H = 0` and the pairing is `0`; the estimate then holds trivially. -/
theorem enstrophy_rate_le_of_solution (ν μ κ E_max : ℝ) (hν : 0 < ν) (hμ : 0 < μ) (hκ : 0 ≤ κ)
    (hEpos : 0 < E_max) (N : ℕ) (u θ : ℝ → ℤ → ℝ) (h : IsUnforcedTruncatedSolution ν μ κ N u θ)
    (hEmax : ∀ t ∈ Set.Icc 0 T, velocityEnergy (u t) N ≤ E_max) {t : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) :
    2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
        * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))
      ≤ 6 * (enstrophy (u t) N * Real.sqrt (enstrophy (u t) N))
        + κ * (enstrophy (u t) N + tempEnstrophy (θ t) N)
        - 2 * ν * (enstrophy (u t) N) ^ 2 / E_max := by
  by_cases hE0 : velocityEnergy (u t) N = 0
  · -- Degenerate case: zero energy forces every retained shell to vanish, so `H = 0` and the
    -- pairing is `0`; the right-hand side is `κ T ≥ 0`.
    have hsum0 : (∑ k ∈ Finset.range N, (u t (k : ℤ)) ^ 2) = 0 := by
      simpa [velocityEnergy] using hE0
    have hz : ∀ k ∈ Finset.range N, (u t (k : ℤ)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.range N)
        (f := fun j : ℕ => (u t (j : ℤ)) ^ 2)
        (fun j _ => sq_nonneg (u t (j : ℤ)))).mp hsum0
    have hu0 : ∀ k ∈ Finset.range N, u t (k : ℤ) = 0 := fun k hk =>
      sq_eq_zero_iff.mp (hz k hk)
    have hL : (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
        * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [hu0 k hk]
      ring
    have hH : enstrophy (u t) N = 0 := by
      rw [enstrophy]
      apply Finset.sum_eq_zero
      intro k hk
      rw [hu0 k hk]
      ring
    have hRHS : 6 * ((0 : ℝ) * Real.sqrt 0) + κ * (0 + tempEnstrophy (θ t) N)
        - 2 * ν * (0 : ℝ) ^ 2 / E_max = κ * tempEnstrophy (θ t) N := by
      simp [Real.sqrt_zero]
    rw [hL, hH, hRHS]
    have hmain : 0 ≤ κ * tempEnstrophy (θ t) N :=
      mul_nonneg hκ (tempEnstrophy_nonneg (θ t) N)
    linarith
  · -- Nondegenerate case: the headline pointwise enstrophy inequality.
    have hEpos' : 0 < velocityEnergy (u t) N :=
      lt_of_le_of_ne (velocityEnergy_nonneg (u t) N) (Ne.symm hE0)
    have hpair := enstrophy_pairing_le ν κ hκ hν.le (u t) (θ t) N
      (h.2.2 t).1 (h.2.2 t).2.1 hEpos'
    have h2 := mul_le_mul_of_nonneg_left hpair (by norm_num : (0 : ℝ) ≤ 2)
    have hHnn : 0 ≤ enstrophy (u t) N := enstrophy_nonneg _ _
    have hTEnn : 0 ≤ tempEnstrophy (θ t) N := tempEnstrophy_nonneg _ _
    -- AM–GM: `2 √H √T ≤ H + T`.
    have hamgm : 2 * (Real.sqrt (enstrophy (u t) N) * Real.sqrt (tempEnstrophy (θ t) N))
        ≤ enstrophy (u t) N + tempEnstrophy (θ t) N := by
      have h1 : (Real.sqrt (enstrophy (u t) N) - Real.sqrt (tempEnstrophy (θ t) N)) ^ 2
          = enstrophy (u t) N + tempEnstrophy (θ t) N
            - 2 * (Real.sqrt (enstrophy (u t) N) * Real.sqrt (tempEnstrophy (θ t) N)) := by
        rw [sub_sq, Real.sq_sqrt hHnn, Real.sq_sqrt hTEnn]
        ring
      nlinarith [sq_nonneg (Real.sqrt (enstrophy (u t) N)
        - Real.sqrt (tempEnstrophy (θ t) N))]
    have hκamgm : κ * (2 * (Real.sqrt (enstrophy (u t) N)
          * Real.sqrt (tempEnstrophy (θ t) N)))
        ≤ κ * (enstrophy (u t) N + tempEnstrophy (θ t) N) :=
      mul_le_mul_of_nonneg_left hamgm hκ
    -- Dissipation: `ν H²/E ≤ ν H²/E_max` since `E ≤ E_max`.
    have hEmax' : velocityEnergy (u t) N ≤ E_max := hEmax t ⟨ht, htT⟩
    have hdiv : (enstrophy (u t) N) ^ 2 / E_max
        ≤ (enstrophy (u t) N) ^ 2 / velocityEnergy (u t) N :=
      div_le_div_of_nonneg_left (sq_nonneg _) hEpos' hEmax'
    have hνdiv : 2 * ν * (enstrophy (u t) N) ^ 2 / E_max
        ≤ 2 * ν * (enstrophy (u t) N) ^ 2 / velocityEnergy (u t) N := by
      have h2ν : 0 ≤ 2 * ν := by linarith
      have h := mul_le_mul_of_nonneg_left hdiv h2ν
      calc 2 * ν * (enstrophy (u t) N) ^ 2 / E_max
          = (2 * ν) * ((enstrophy (u t) N) ^ 2 / E_max) := by ring
        _ ≤ (2 * ν) * ((enstrophy (u t) N) ^ 2 / velocityEnergy (u t) N) := h
        _ = 2 * ν * (enstrophy (u t) N) ^ 2 / velocityEnergy (u t) N := by ring
    have hstep : 2 * (3 * (enstrophy (u t) N * Real.sqrt (enstrophy (u t) N))
          + κ * (Real.sqrt (enstrophy (u t) N) * Real.sqrt (tempEnstrophy (θ t) N))
          - ν * (enstrophy (u t) N) ^ 2 / velocityEnergy (u t) N)
        ≤ 6 * (enstrophy (u t) N * Real.sqrt (enstrophy (u t) N))
          + κ * (enstrophy (u t) N + tempEnstrophy (θ t) N)
          - 2 * ν * (enstrophy (u t) N) ^ 2 / E_max := by
      simp only [div_eq_mul_inv] at hνdiv ⊢
      linarith [hκamgm, hνdiv]
    exact h2.trans hstep

/-! ## 4. The Lyapunov function `Ψ = H + (κ/2μ) S` -/

/-- **The enstrophy Lyapunov function** `Ψ = H + (κ/(2μ)) S`, where `H = enstrophy u N` and
`S = entropy θ N = ∑_{k<N} θ_k²`. The entropy term is the correction that absorbs the buoyancy
source: in `Ψ'` the `+κ T` production of the enstrophy budget cancels the `−κ T` contribution of
`(κ/(2μ))·(−2μ T)`. -/
noncomputable def enstrophyLyapunov (ν μ κ : ℝ) (N : ℕ) (u θ : ℤ → ℝ) : ℝ :=
  enstrophy u N + (κ / (2 * μ)) * entropy θ N

/-- **The explicit Young constant** `C = C₁ + C₂ = 2187/(16 γ³) + κ²/(4γ)` with
`γ = ν/E_max`. It is the constant in the derivative bound `Ψ' ≤ C`: `C₁` absorbs the cubic
transfer `6 H^{3/2}` into the quadratic dissipation `γ H²` (taking the exact optimal point
`s = 9/(2γ)`), and `C₂` absorbs the linear buoyancy `κ H`. -/
noncomputable def enstrophyYoungConst (ν κ E_max : ℝ) : ℝ :=
  2187 / (16 * (ν / E_max) ^ 3) + κ ^ 2 / (4 * (ν / E_max))

/-- **The time derivative of the Lyapunov function along a solution.** Summing the enstrophy
derivative (item 1) and `(κ/(2μ))` times the entropy derivative (`entropy_hasDerivAt`). -/
theorem enstrophyLyapunov_hasDerivAt (ν μ κ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolution ν μ κ N u θ) (t : ℝ) :
    HasDerivAt (fun s => enstrophyLyapunov ν μ κ N (u s) (θ s))
      (2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
          * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))
        + (κ / (2 * μ)) * (2 * ∑ k ∈ Finset.range N,
            θ t (k : ℤ) * dyadicTemperatureRHS μ (u t) (θ t) (k : ℤ))) t := by
  have h1 := enstrophy_hasDerivAt ν μ κ N u θ h t
  have h2 := (entropy_hasDerivAt ν μ κ N u θ h t).const_mul (κ / (2 * μ))
  have hfun : (fun s => enstrophyLyapunov ν μ κ N (u s) (θ s))
      = (fun s => enstrophy (u s) N)
        + (fun s => (κ / (2 * μ)) * entropy (θ s) N) := by
    funext s
    simp [enstrophyLyapunov]
  rw [hfun]
  exact h1.add h2

/-- **Young absorption of the cubic transfer.** For `γ > 0` and `s ≥ 0`,
`6 s³ ≤ γ s⁴ + 2187/(16 γ³)`. The constant is optimal: the maximum of `6s³ − γs⁴` over `s ≥ 0` is
attained at `s = 9/(2γ)` and equals `2187/(16γ³)`. Equivalently, multiplying by `16γ³ > 0`,
`16γ⁴s⁴ − 96γ³s³ + 2187 = (2γs − 9)² (4γ²s² + 12γs + 27) ≥ 0`. -/
theorem young_cubic_le {γ s : ℝ} (hγ : 0 < γ) (hs : 0 ≤ s) :
    6 * s ^ 3 ≤ γ * s ^ 4 + 2187 / (16 * γ ^ 3) := by
  have hquad : 0 ≤ 4 * γ ^ 2 * s ^ 2 + 12 * γ * s + 27 := by
    nlinarith [sq_nonneg (2 * γ * s + 3)]
  have hsq : 0 ≤ (2 * γ * s - 9) ^ 2 := sq_nonneg _
  have hprod : 0 ≤ (2 * γ * s - 9) ^ 2 * (4 * γ ^ 2 * s ^ 2 + 12 * γ * s + 27) :=
    mul_nonneg hsq hquad
  have hid : (2 * γ * s - 9) ^ 2 * (4 * γ ^ 2 * s ^ 2 + 12 * γ * s + 27)
      = 16 * γ ^ 4 * s ^ 4 - 96 * γ ^ 3 * s ^ 3 + 2187 := by ring
  have hkey : 96 * γ ^ 3 * s ^ 3 ≤ 16 * γ ^ 4 * s ^ 4 + 2187 := by
    rw [hid] at hprod
    linarith
  have hpos : 0 < 16 * γ ^ 3 := by positivity
  rw [show γ * s ^ 4 + 2187 / (16 * γ ^ 3)
      = (16 * γ ^ 4 * s ^ 4 + 2187) / (16 * γ ^ 3) by field_simp]
  rw [le_div_iff₀ hpos]
  linarith

/-- **Young absorption of the linear buoyancy term.** For `γ > 0` and any real `y`,
`κ y ≤ γ y² + κ²/(4γ)`, with equality at `y = κ/(2γ)`. This is `(2γy − κ)² ≥ 0` divided by
`4γ > 0`. -/
theorem young_linear_le {γ κ y : ℝ} (hγ : 0 < γ) :
    κ * y ≤ γ * y ^ 2 + κ ^ 2 / (4 * γ) := by
  have hsq : 0 ≤ (2 * γ * y - κ) ^ 2 := sq_nonneg _
  have hkey : 4 * γ * κ * y ≤ 4 * γ ^ 2 * y ^ 2 + κ ^ 2 := by nlinarith [hsq]
  have hpos : 0 < 4 * γ := by positivity
  rw [show γ * y ^ 2 + κ ^ 2 / (4 * γ) = (4 * γ ^ 2 * y ^ 2 + κ ^ 2) / (4 * γ) by
    field_simp]
  rw [le_div_iff₀ hpos]
  linarith

/-- **The Lyapunov derivative is bounded by the explicit constant `C`.** Combining the pointwise
en-strophy rate bound (item 3) with the temperature identity, the buoyancy source `κ T` cancels
against `(κ/(2μ))·(−2μ T)`, and the two Young inequalities absorb `6 H^{3/2}` and `κ H` into the
quadratic dissipation `2 (ν/E_max) H²`, leaving `Ψ' ≤ 2187/(16γ³) + κ²/(4γ) = C`. -/
theorem enstrophyLyapunov_deriv_le (ν μ κ E_max : ℝ) (hν : 0 < ν) (hμ : 0 < μ) (hκ : 0 ≤ κ)
    (hEpos : 0 < E_max) (N : ℕ) (u θ : ℝ → ℤ → ℝ) (h : IsUnforcedTruncatedSolution ν μ κ N u θ)
    (hEmax : ∀ t ∈ Set.Icc 0 T, velocityEnergy (u t) N ≤ E_max) {t : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) :
    2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
        * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))
      + (κ / (2 * μ)) * (2 * ∑ k ∈ Finset.range N,
          θ t (k : ℤ) * dyadicTemperatureRHS μ (u t) (θ t) (k : ℤ))
      ≤ enstrophyYoungConst ν κ E_max := by
  have hγ : 0 < ν / E_max := div_pos hν hEpos
  have hrate := enstrophy_rate_le_of_solution ν μ κ E_max hν hμ hκ hEpos N u θ h hEmax ht htT
  have htemp := temperature_pairing_eq_neg_mu_tempEnstrophy μ (u t) (θ t) N
    (h.2.2 t).2.2.1 (h.2.2 t).2.2.2
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have htemp' : (κ / (2 * μ)) * (2 * ∑ k ∈ Finset.range N,
        θ t (k : ℤ) * dyadicTemperatureRHS μ (u t) (θ t) (k : ℤ))
      = - κ * tempEnstrophy (θ t) N := by
    rw [htemp]
    field_simp
  rw [htemp']
  have hHnn : 0 ≤ enstrophy (u t) N := enstrophy_nonneg _ _
  have hs2 : (Real.sqrt (enstrophy (u t) N)) ^ 2 = enstrophy (u t) N :=
    Real.sq_sqrt hHnn
  have hy1 : 6 * (enstrophy (u t) N * Real.sqrt (enstrophy (u t) N))
      ≤ (ν / E_max) * (enstrophy (u t) N) ^ 2 + 2187 / (16 * (ν / E_max) ^ 3) := by
    have h := young_cubic_le (γ := ν / E_max) (s := Real.sqrt (enstrophy (u t) N))
      hγ (Real.sqrt_nonneg _)
    have h3 : (Real.sqrt (enstrophy (u t) N)) ^ 3
        = enstrophy (u t) N * Real.sqrt (enstrophy (u t) N) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hs2]
    have h4 : (Real.sqrt (enstrophy (u t) N)) ^ 4 = (enstrophy (u t) N) ^ 2 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, hs2]
      ring
    rwa [h3, h4] at h
  have hy2 : κ * enstrophy (u t) N
      ≤ (ν / E_max) * (enstrophy (u t) N) ^ 2 + κ ^ 2 / (4 * (ν / E_max)) :=
    young_linear_le (γ := ν / E_max) hγ
  simp only [enstrophyYoungConst]
  simp only [div_eq_mul_inv] at hrate hy1 hy2 ⊢
  linarith [hrate, hy1, hy2]

/-! ## 5. The Stage-O′ capstone -/

/-- The velocity energy is continuous along a solution: each ladder component `fun s => u s k` is
differentiable (it has a derivative at every point by the solution predicate), hence continuous,
and `E` is a finite sum of squares of these. (Enstrophy continuity is built into the capstone's
hypotheses; the energy continuity needed to extract a ceiling is derived here.) -/
theorem velocityEnergy_continuous (ν μ κ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolution ν μ κ N u θ) :
    Continuous fun t => velocityEnergy (u t) N := by
  unfold velocityEnergy
  refine continuous_finsetSum _ fun k hk => ?_
  have hdiff : Differentiable ℝ (fun t : ℝ => (u t (k : ℤ)) ^ 2) := fun t =>
    ((h.1 t (k : ℤ) (Int.natCast_nonneg k)
      (by exact_mod_cast (Finset.mem_range.mp hk))).differentiableAt).pow 2
  exact hdiff.continuous

/-- The enstrophy is continuous along a solution (the capstone carries it as a hypothesis, but it
is in fact automatic; recorded here for the non-vacuity checks). -/
theorem enstrophy_continuous (ν μ κ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolution ν μ κ N u θ) :
    Continuous fun t => enstrophy (u t) N := by
  unfold enstrophy
  refine continuous_finsetSum _ fun k hk => ?_
  have hdiff : Differentiable ℝ (fun t : ℝ => (u t (k : ℤ)) ^ 2) := fun t =>
    ((h.1 t (k : ℤ) (Int.natCast_nonneg k)
      (by exact_mod_cast (Finset.mem_range.mp hk))).differentiableAt).pow 2
  exact continuous_const.mul hdiff.continuous

/-- **The Stage-O′ capstone: no finite-time enstrophy (`H¹`) blowup.** Along any unforced
truncated dyadic Boussinesq solution on the shells `0, …, N-1` with Dirichlet ends, the enstrophy
`H = ∑_{k<N} 4^k u_k²` is bounded on every compact time interval `[0, T]` by an explicit constant
linear in `T`. This is the norm in which blowup is measured: while the transfer conserves energy
exactly, its enstrophy pairing is the cubic `3 ∑ a_{k-1}² a_k` of homogeneity `3/2`, which is beaten
by the quadratic dissipation `ν H²/E` of homogeneity `2` above the threshold `H ~ (E/ν)²`. The
entropy correction `(κ/2μ) S` absorbs the buoyancy source exactly, and Young's inequality turns the
rest into the constant `C = 2187/(16γ³) + κ²/(4γ)`, `γ = ν/E_max`. -/
theorem truncated_unforced_enstrophy_bounded (ν μ κ : ℝ) (hν : 0 < ν) (hμ : 0 < μ) (hκ : 0 ≤ κ)
    (N : ℕ) (u θ : ℝ → ℤ → ℝ) (h : IsUnforcedTruncatedSolution ν μ κ N u θ)
    (hcont : ContinuousOn (fun t => enstrophy (u t) N) (Set.Icc 0 T)) (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, enstrophy (u t) N ≤ C := by
  -- An energy ceiling on `[0, T]`, made strictly positive.
  obtain ⟨E₀, hE₀⟩ := truncated_unforced_energy_bounded ν μ κ hν hμ.le hκ N u θ h
    (velocityEnergy_continuous ν μ κ N u θ h).continuousOn hT
  refine ⟨enstrophyLyapunov ν μ κ N (u 0) (θ 0)
      + enstrophyYoungConst ν κ (max E₀ 1) * T, ?_⟩
  intro t ht
  have hEpos : 0 < max E₀ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hEmax : ∀ s ∈ Set.Icc 0 T, velocityEnergy (u s) N ≤ max E₀ 1 := fun s hs =>
    le_trans (hE₀ s hs) (le_max_left _ _)
  have hCnn : 0 ≤ enstrophyYoungConst ν κ (max E₀ 1) := by
    have hγ : 0 < ν / max E₀ 1 := div_pos hν hEpos
    have h1 : 0 ≤ 2187 / (16 * (ν / max E₀ 1) ^ 3) :=
      div_nonneg (by norm_num) (le_of_lt (mul_pos (by norm_num) (pow_pos hγ 3)))
    have h2 : 0 ≤ κ ^ 2 / (4 * (ν / max E₀ 1)) :=
      div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (by norm_num) hγ))
    simp only [enstrophyYoungConst]
    linarith
  have hderiv : ∀ s ∈ Set.Ico 0 T,
      HasDerivAt (fun r => enstrophyLyapunov ν μ κ N (u r) (θ r))
        (2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u s (k : ℤ)
            * dyadicVelocityRHS ν κ (u s) (θ s) (k : ℤ))
          + (κ / (2 * μ)) * (2 * ∑ k ∈ Finset.range N,
              θ s (k : ℤ) * dyadicTemperatureRHS μ (u s) (θ s) (k : ℤ))) s :=
    fun s _ => enstrophyLyapunov_hasDerivAt ν μ κ N u θ h s
  have hineq : ∀ s ∈ Set.Ico 0 T,
      (2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u s (k : ℤ)
            * dyadicVelocityRHS ν κ (u s) (θ s) (k : ℤ))
          + (κ / (2 * μ)) * (2 * ∑ k ∈ Finset.range N,
              θ s (k : ℤ) * dyadicTemperatureRHS μ (u s) (θ s) (k : ℤ)))
        ≤ enstrophyYoungConst ν κ (max E₀ 1) + 0 * enstrophyLyapunov ν μ κ N (u s) (θ s) :=
    fun s hs => by
      simpa using enstrophyLyapunov_deriv_le ν μ κ (max E₀ 1) hν hμ hκ hEpos N u θ h hEmax
        hs.1 hs.2.le
  have hΨcont : ContinuousOn (fun r => enstrophyLyapunov ν μ κ N (u r) (θ r)) (Set.Icc 0 T) :=
    fun s _ => (enstrophyLyapunov_hasDerivAt ν μ κ N u θ h s).continuousAt.continuousWithinAt
  have hg := le_gronwallBound_of_hasDerivAt (f := fun r => enstrophyLyapunov ν μ κ N (u r) (θ r))
    (a := enstrophyYoungConst ν κ (max E₀ 1)) (b := 0) hΨcont hderiv hineq t ht
  rw [gronwallBound_K0] at hg
  have hCt : enstrophyYoungConst ν κ (max E₀ 1) * t
      ≤ enstrophyYoungConst ν κ (max E₀ 1) * T :=
    mul_le_mul_of_nonneg_left ht.2 hCnn
  have hHleΨ : enstrophy (u t) N ≤ enstrophyLyapunov ν μ κ N (u t) (θ t) := by
    simp only [enstrophyLyapunov]
    have h : 0 ≤ (κ / (2 * μ)) * entropy (θ t) N :=
      mul_nonneg (div_nonneg hκ (by positivity)) (entropy_nonneg _ _)
    linarith
  linarith [hHleΨ, hg, hCt]

/-! ## 6. Bonus — the κ = 0 uniform-in-time bound -/

/-- **Uniform-in-time enstrophy bound in the isothermal case `κ = 0`.** With no buoyancy source
the enstrophy rate is `H' ≤ 6 H √H − (2ν/E_max) H²`, so the Bernoulli/Riccati barrier
(`le_of_deriv_le_bernoulli` with `a = 6`, `b = 2ν/E_max`) gives the threshold
`(6/(2ν/E_max))² = (3E_max/ν)²`, and

`H t ≤ max (H 0) (3 E_max/ν)²`  for all `t ∈ [0, T]`,

uniformly in `T`. -/
theorem enstrophy_bounded_isothermal (ν μ κ E_max : ℝ) (hν : 0 < ν) (hμ : 0 < μ)
    (hκ0 : κ = 0) (hEpos : 0 < E_max) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolution ν μ κ N u θ)
    (hEmax : ∀ t ∈ Set.Icc 0 T, velocityEnergy (u t) N ≤ E_max)
    (hcont : ContinuousOn (fun t => enstrophy (u t) N) (Set.Icc 0 T)) (hT : 0 ≤ T) :
    ∀ t ∈ Set.Icc 0 T, enstrophy (u t) N ≤ max (enstrophy (u 0) N) ((3 * E_max / ν) ^ 2) := by
  subst hκ0
  have hb : 0 < 2 * ν / E_max := div_pos (by linarith) hEpos
  have hbase : 6 / (2 * ν / E_max) = 3 * E_max / ν := by
    field_simp
    ring
  have hineq : ∀ r ∈ Set.Ico 0 T,
      2 * ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u r (k : ℤ)
        * dyadicVelocityRHS ν 0 (u r) (θ r) (k : ℤ)
      ≤ 6 * enstrophy (u r) N * Real.sqrt (enstrophy (u r) N)
        - (2 * ν / E_max) * (enstrophy (u r) N) ^ 2 := by
    intro r hr
    have hrate := enstrophy_rate_le_of_solution ν μ 0 E_max hν hμ le_rfl hEpos N u θ h hEmax
      hr.1 hr.2.le
    simp only [div_eq_mul_inv] at hrate ⊢
    linarith [hrate]
  intro t ht
  have h := le_of_deriv_le_bernoulli (y := fun r => enstrophy (u r) N)
    (y' := fun r => 2 * ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u r (k : ℤ)
      * dyadicVelocityRHS ν 0 (u r) (θ r) (k : ℤ))
    (a := 6) (b := 2 * ν / E_max) (by norm_num) hb hcont
    (fun r _ => enstrophy_hasDerivAt ν μ 0 N u θ h r) hineq t ht
  rwa [hbase] at h

/-! ## 7. Non-vacuity

The solution predicate and every theorem above are instantiated at the zero equilibrium
(`zero_is_unforcedTruncatedSolution`), the Young constants are shown to be **sharp** (both
absorptions are equalities at their optimal points), the temperature identity is computed
numerically at a non-zero state (`−17 ≠ 0`), and the AM–GM step is checked on concrete numbers. -/

/-- The concrete velocity ladder `u = (0, 1, 3, 0)` on the shells `-1, 0, 1, 2`. -/
private def uEx : ℤ → ℝ :=
  fun k => if k = -1 then 0 else if k = 0 then 1 else if k = 1 then 3 else if k = 2 then 0 else 0

/-- The concrete temperature ladder `θ = (0, 1, 2, 0)` on the shells `-1, 0, 1, 2`. -/
private def θEx : ℤ → ℝ :=
  fun k => if k = -1 then 0 else if k = 0 then 1 else if k = 1 then 2 else if k = 2 then 0 else 0

/-- The zero state has zero enstrophy. -/
example : enstrophy ((fun _ _ => (0 : ℝ)) 0) 3 = 0 := by simp [enstrophy]

/-- The Lyapunov function vanishes at the zero state. -/
example : enstrophyLyapunov 1 1 1 3 (fun _ : ℤ => (0 : ℝ)) (fun _ : ℤ => (0 : ℝ)) = 0 := by
  simp [enstrophyLyapunov, enstrophy, entropy]

/-- The enstrophy derivative of the zero solution is `0`, as item 1 asserts. -/
example (t : ℝ) :
    HasDerivAt (fun s => enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) s) 2) 0 t := by
  have h := enstrophy_hasDerivAt 1 1 1 2 (fun _ _ => 0) (fun _ _ => 0)
    (zero_is_unforcedTruncatedSolution 1 1 1 2) t
  have hsum : (2 * ∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ))
      * ((fun _ : ℤ => (0 : ℝ)) (k : ℤ))
      * dyadicVelocityRHS 1 1 (fun _ : ℤ => (0 : ℝ)) (fun _ : ℤ => (0 : ℝ)) (k : ℤ)) = 0 := by simp
  rw [hsum] at h
  exact h

/-- The pointwise rate bound (item 2) at the zero solution: both sides are `0`. -/
example (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    2 * (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ))
        * ((fun _ : ℤ => (0 : ℝ)) (k : ℤ))
        * dyadicVelocityRHS 1 1 (fun _ : ℤ => (0 : ℝ)) (fun _ : ℤ => (0 : ℝ)) (k : ℤ))
      ≤ 6 * (enstrophy ((fun _ _ => (0 : ℝ)) t) 2
          * Real.sqrt (enstrophy ((fun _ _ => (0 : ℝ)) t) 2))
        + 1 * (enstrophy ((fun _ _ => (0 : ℝ)) t) 2
          + tempEnstrophy ((fun _ _ => (0 : ℝ)) t) 2)
        - 2 * 1 * (enstrophy ((fun _ _ => (0 : ℝ)) t) 2) ^ 2 / 1 :=
  enstrophy_rate_le_of_solution 1 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) 2 (fun _ _ => 0) (fun _ _ => 0)
    (zero_is_unforcedTruncatedSolution 1 1 1 2) (fun s hs => by simp [velocityEnergy]) ht.1 ht.2

/-- The Lyapunov derivative bound (item 3) at the zero solution: `0 ≤ C`. -/
example (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    2 * (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ))
        * ((fun _ : ℤ => (0 : ℝ)) (k : ℤ))
        * dyadicVelocityRHS 1 1 (fun _ : ℤ => (0 : ℝ)) (fun _ : ℤ => (0 : ℝ)) (k : ℤ))
      + (1 / (2 * 1)) * (2 * ∑ k ∈ Finset.range 2,
          ((fun _ => 0 : ℤ → ℝ) (k : ℤ))
            * dyadicTemperatureRHS 1 (fun _ : ℤ => (0 : ℝ)) (fun _ : ℤ => (0 : ℝ)) (k : ℤ))
      ≤ enstrophyYoungConst 1 1 1 :=
  enstrophyLyapunov_deriv_le 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    2 (fun _ _ => 0) (fun _ _ => 0) (zero_is_unforcedTruncatedSolution 1 1 1 2)
    (fun s hs => by simp [velocityEnergy]) ht.1 ht.2

/-- The capstone applies to the zero equilibrium, yielding a bound on `[0, 1]`. -/
example : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2 ≤ C := by
  refine truncated_unforced_enstrophy_bounded (T := 1) 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) 2 (fun _ _ => 0) (fun _ _ => 0)
    (zero_is_unforcedTruncatedSolution 1 1 1 2) ?_ (by norm_num)
  have hfun : (fun t => enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2)
      = fun _ => (0 : ℝ) := by
    funext t
    simp [enstrophy]
  rw [hfun]
  exact continuousOn_const

/-- The `κ = 0` uniform bonus applies to the zero equilibrium as well. -/
example (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2
      ≤ max (enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) 0) 2) ((3 * 5 / 1) ^ 2) := by
  refine enstrophy_bounded_isothermal (T := 1) 1 1 0 5 (by norm_num) (by norm_num) rfl
    (by norm_num) 2 (fun _ _ => 0) (fun _ _ => 0)
    (zero_is_unforcedTruncatedSolution 1 1 0 2) ?_ ?_ (by norm_num) t ht
  · intro s hs
    simp [velocityEnergy]
  · have hfun : (fun t => enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2)
        = fun _ => (0 : ℝ) := by
      funext t
      simp [enstrophy]
    rw [hfun]
    exact continuousOn_const

/-- Concrete enstrophy of the non-zero state `u = (0,1,3,0)`: `4⁰·1² + 4¹·3² = 37`. -/
example : enstrophy uEx 2 = 37 := by
  norm_num [enstrophy, Finset.sum_range_succ, Finset.sum_range_zero, uEx, dyadicWeight]

/-- Concrete temperature enstrophy of `θ = (0,1,2,0)`: `1 + 16 = 17`. -/
example : tempEnstrophy θEx 2 = 17 := by
  norm_num [tempEnstrophy, Finset.sum_range_succ, Finset.sum_range_zero, θEx, dyadicWeight]

/-- The temperature pairing at the concrete state is `−17 ≠ 0`, so the identity is not vacuous. -/
example : (∑ k ∈ Finset.range 2, θEx (k : ℤ) * dyadicTemperatureRHS 1 uEx θEx (k : ℤ)) = -17 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uEx, θEx, dyadicTemperatureRHS,
    generalTemperatureRHS, boussinesqTransferTheta, dyadicWeight]

/-- The same identity through `temperature_pairing_eq_neg_mu_tempEnstrophy`: `−μ T = −17`. -/
example : (∑ k ∈ Finset.range 2, θEx (k : ℤ) * dyadicTemperatureRHS 1 uEx θEx (k : ℤ))
    = -1 * tempEnstrophy θEx 2 :=
  temperature_pairing_eq_neg_mu_tempEnstrophy 1 uEx θEx 2 (by norm_num [θEx]) (by norm_num [θEx])

/-- The AM–GM step at the concrete state `H = 37`, `T = 17`: `2√37√17 ≤ 54`. -/
example : 2 * (Real.sqrt 37 * Real.sqrt 17) ≤ 37 + 17 := by
  nlinarith [sq_nonneg (Real.sqrt 37 - Real.sqrt 17),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 37),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)]

/-- `young_cubic_le` is **sharp**: at `s = 9/(2γ)` with `γ = 1` both sides are `4374/8`. -/
example : (6 : ℝ) * (9 / 2) ^ 3 = 1 * (9 / 2) ^ 4 + 2187 / (16 * (1 : ℝ) ^ 3) := by norm_num

/-- `young_linear_le` is **sharp**: at `y = κ/(2γ)` with `γ = κ = 1` both sides are `1/2`. -/
example : (1 : ℝ) * (1 / 2) = 1 * (1 / 2) ^ 2 + 1 ^ 2 / (4 * (1 : ℝ)) := by norm_num

/-- The explicit Young constant at `ν = κ = E_max = 1` is `2187/16 + 1/4 = 2191/16`. -/
example : enstrophyYoungConst 1 1 1 = 2191 / 16 := by
  unfold enstrophyYoungConst
  norm_num

/-- The `κ = 0` Bernoulli threshold at `ν = 1`, `E_max = 10` is `(3·10/1)² = 900`. -/
example : (3 * (10 : ℝ) / 1) ^ 2 = 900 := by norm_num

end Cascade

/-! ## Axiom audit -/

#print axioms Cascade.enstrophy_hasDerivAt
#print axioms Cascade.temperature_pairing_eq_neg_mu_tempEnstrophy
#print axioms Cascade.enstrophy_rate_le_of_solution
#print axioms Cascade.enstrophyLyapunov
#print axioms Cascade.enstrophyYoungConst
#print axioms Cascade.enstrophyLyapunov_hasDerivAt
#print axioms Cascade.young_cubic_le
#print axioms Cascade.young_linear_le
#print axioms Cascade.enstrophyLyapunov_deriv_le
#print axioms Cascade.velocityEnergy_continuous
#print axioms Cascade.enstrophy_continuous
#print axioms Cascade.truncated_unforced_enstrophy_bounded
#print axioms Cascade.enstrophy_bounded_isothermal
