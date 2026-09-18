import Cascade.Boussinesq
import Cascade.Obstruction
import Cascade.Gronwall
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Stage O capstone — no finite-time energy blowup for the unforced truncated dyadic Boussinesq
model

This file is the **capstone of Stage O**. It assembles the two halves that were landed
separately:

* `Cascade/Obstruction.lean` (the *pointwise* obstruction): along a state satisfying the
  truncation / Dirichlet conditions `u(-1) = u(N) = θ(-1) = θ(N) = 0`, the velocity energy
  pairing obeys `∑_{k<N} u_k (du_k/dt) ≤ κ √E √S − ν E` and the temperature entropy pairing is
  `≤ 0`.
* `Cascade/Gronwall.lean` (the *abstract* Grönwall engine): a scalar energy obeying
  `E' ≤ 2κ√S₀√E − 2νE` with `ν > 0` cannot blow up at a finite time.

## The mechanism

The truncated model on the shells `0, …, N-1` is closed by the Dirichlet conditions
`u(-1) = u(N) = θ(-1) = θ(N) = 0`. The nonlinear transfer is **exactly energy-conserving in the
interior**: by `dyadic_velocity_pairing_eq_flux` / `dyadic_temperature_pairing_eq_flux` the
pairing of a ladder with its own nonlinear transfer telescopes into a *difference of boundary
fluxes*, and the Dirichlet conditions kill both boundary fluxes. So the transverse transfer
neither creates nor destroys energy; the only bulk source is **buoyancy**
`κ ∑_{k<N} u_k θ_k`, which Cauchy–Schwarz bounds by `κ √E √S`, while viscosity dissipates at
least `ν E` because `2^{2k} ≥ 1` on the physical shells `k ≥ 0`.

Moreover thermal diffusion makes the **entropy `S = ∑ θ_k²` non-increasing in time** (the
temperature pairing is `≤ 0`, i.e. `S' ≤ 0`). Hence `√S` may be replaced by `√S₀` with
`S₀ = S(0)`, and the energy satisfies the *closed* scalar inequality

`E' ≤ 2κ√S₀√E − 2νE`,  `E ≥ 0`,  `ν > 0`,  `κ ≥ 0`.

Viscosity dominates: the Grönwall engine turns this into a bound on every compact time interval
`[0, T]` (and, when `2ν > κ√S₀`, into the uniform-in-time bound
`max (E 0) (κ√S₀/(2ν − κ√S₀))`). This is the headline conclusion:

**the unforced truncated dyadic Boussinesq model has no finite-time energy blowup.**

## Hypotheses and scope

The statement carries the explicit truncation / Dirichlet hypotheses (the model is *forced* to
be closed at the two ends of the retained range of shells) and the physical sign hypotheses
`ν > 0`, `μ ≥ 0`, `κ ≥ 0`. It is the *unforced* counterpart of the forced Stage-B results of
`Cascade/ForcedModel.lean`: both models are bounded, because the exactly-conserving transfer
provides no interior source and the only source (buoyancy) is dominated by viscosity once the
entropy has been capped by its non-increasing evolution. An earlier version of this paragraph
described a finite-time blowup **for the forced** Stage-B model; no such theorem survives — the
solution-level blowup capstone has been deleted as false (see
`Cascade/TruncatedRegularity.lean`).

The non-vacuity section at the end checks that the solution predicate is inhabited (by the zero
equilibrium) and that the concrete inequality chain is non-trivial at a non-zero state.
-/

noncomputable section

-- The continuity hypothesis `hcont` (and the interval hypothesis `hT`) are part of the intended
-- interface of the two capstones; the first is redundant given that the ladders are differentiable
-- in time, and the second is not needed by `energy_le_max_of_rate_le`.  Silence the linter, as in
-- `Cascade/Gronwall.lean`.
set_option linter.unusedVariables false

open scoped BigOperators

namespace Cascade

/-! ## 1. The truncated unforced solution predicate, energy and entropy -/

/-- **The unforced truncated dyadic Boussinesq solution predicate.** `u θ : ℝ → ℤ → ℝ` are the
velocity and temperature ladders as functions of time; `ν`, `μ`, `κ` are the viscosity, thermal
diffusivity and buoyancy coupling. On the shells `0, …, N-1` the ladders solve the frozen
two-species dyadic Boussinesq ODE `Cascade/Boussinesq.lean`, and the truncation is closed by the
Dirichlet boundary conditions `u(-1) = u(N) = θ(-1) = θ(N) = 0`.

**The equation is imposed only on the retained shells `0 ≤ k < N`.** An earlier version imposed it
on *all* of `ℤ`, which is inconsistent: the boundary value `u t N = 0` holds for every `t`, so the
derivative of `u · N` is `0`, and the equation at `k = N` then forces `2^N (u t (N-1))² = 0`, hence
`u t (N-1) = 0` for all `t` — and the same step cascades downward, so the retained range must vanish
identically. Every theorem assuming that predicate was therefore vacuous. See
`Cascade/TruncatedRegularity.lean` for the (trivial) regularity statement that actually holds. -/
def IsUnforcedTruncatedSolution (ν μ κ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ) : Prop :=
  (∀ t k, 0 ≤ k → k < (N : ℤ) →
    HasDerivAt (fun s => u s k) (dyadicVelocityRHS ν κ (u t) (θ t) k) t) ∧
  (∀ t k, 0 ≤ k → k < (N : ℤ) →
    HasDerivAt (fun s => θ s k) (dyadicTemperatureRHS μ (u t) (θ t) k) t) ∧
  (∀ t, u t (-1) = 0 ∧ u t (N : ℤ) = 0 ∧ θ t (-1) = 0 ∧ θ t (N : ℤ) = 0)

/-- **Velocity energy** on the truncated range: `∑_{k<N} u_k²`. -/
def velocityEnergy (u : ℤ → ℝ) (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, (u (k : ℤ)) ^ 2

/-- **Thermal entropy** on the truncated range: `∑_{k<N} θ_k²`. -/
def entropy (θ : ℤ → ℝ) (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, (θ (k : ℤ)) ^ 2

/-- The velocity energy is nonnegative. -/
theorem velocityEnergy_nonneg (u : ℤ → ℝ) (N : ℕ) : 0 ≤ velocityEnergy u N := by
  rw [velocityEnergy]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-- The thermal entropy is nonnegative. -/
theorem entropy_nonneg (θ : ℤ → ℝ) (N : ℕ) : 0 ≤ entropy θ N := by
  rw [entropy]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-! ## 2. Differentiating the energy and the entropy along a solution -/

/-- Applying a finite sum of functions to a point is the sum of the applications,
`(∑_{i∈s} f_i) x = ∑_{i∈s} f_i x`. This is the plain-function-type case of the generic
`sum_apply` (which requires a `FunLike` instance that plain function types do not carry at this
pin), proved by induction on the finset. -/
theorem finset_sum_apply {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (x : ℝ) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha _ => simp [Finset.sum_insert, ha]

/-- **The time derivative of the velocity energy along a truncated solution.** Differentiating
the finite sum `∑_{k<N} (u s k)²` term by term and using the chain rule
`d/dt (u s k)² = 2 u s k · (du s k/dt)` gives the pairing
`2 ∑_{k<N} u_k (du_k/dt)`, with `du_k/dt = dyadicVelocityRHS ν κ u θ k`. The factor `2` is the
chain-rule factor; note that the Obstruction estimate is stated for the *un-doubled* pairing, so
this is exactly the bridge from the pointwise estimate to the Grönwall engine's `E'`. -/
theorem velocityEnergy_hasDerivAt (ν μ κ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolution ν μ κ N u θ) (t : ℝ) :
    HasDerivAt (fun s => velocityEnergy (u s) N)
      (2 * ∑ k ∈ Finset.range N, u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ)) t := by
  have hsum : HasDerivAt (∑ k ∈ Finset.range N, fun s : ℝ => (u s (k : ℤ)) ^ 2)
      (∑ k ∈ Finset.range N,
        2 * u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ)) t :=
    HasDerivAt.sum (u := Finset.range N)
      (A := fun k s => (u s (k : ℤ)) ^ 2)
      (A' := fun k => 2 * u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))
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
        2 * u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))
      = 2 * ∑ k ∈ Finset.range N,
          u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [heq] at hsum
  exact hsum

/-- **The time derivative of the thermal entropy along a truncated solution.** Same chain rule as
for the velocity energy, with `dθ_k/dt = dyadicTemperatureRHS μ u θ k`; the derivative is `2`
times the temperature pairing. -/
theorem entropy_hasDerivAt (ν μ κ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolution ν μ κ N u θ) (t : ℝ) :
    HasDerivAt (fun s => entropy (θ s) N)
      (2 * ∑ k ∈ Finset.range N,
        θ t (k : ℤ) * dyadicTemperatureRHS μ (u t) (θ t) (k : ℤ)) t := by
  have hsum : HasDerivAt (∑ k ∈ Finset.range N, fun s : ℝ => (θ s (k : ℤ)) ^ 2)
      (∑ k ∈ Finset.range N,
        2 * θ t (k : ℤ) * dyadicTemperatureRHS μ (u t) (θ t) (k : ℤ)) t :=
    HasDerivAt.sum (u := Finset.range N)
      (A := fun k s => (θ s (k : ℤ)) ^ 2)
      (A' := fun k => 2 * θ t (k : ℤ) * dyadicTemperatureRHS μ (u t) (θ t) (k : ℤ))
      (fun k hk => by
        have hd := (h.2.1 t (k : ℤ) (Int.natCast_nonneg k)
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
        2 * θ t (k : ℤ) * dyadicTemperatureRHS μ (u t) (θ t) (k : ℤ))
      = 2 * ∑ k ∈ Finset.range N,
          θ t (k : ℤ) * dyadicTemperatureRHS μ (u t) (θ t) (k : ℤ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [heq] at hsum
  exact hsum

/-! ## 3. The entropy is non-increasing -/

/-- **Thermal entropy is non-increasing along a truncated unforced solution.** By
`temperature_energy_rate_nonpos` the temperature pairing is `≤ 0`, i.e. the derivative of the
entropy is `≤ 0`; since the entropy is differentiable everywhere, the mean-value theorem
(`antitone_of_hasDerivAt_nonpos`) makes it antitone. -/
theorem entropy_antitone (ν μ κ : ℝ) (hμ : 0 ≤ μ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolution ν μ κ N u θ) :
    Antitone fun t => entropy (θ t) N := by
  refine antitone_of_hasDerivAt_nonpos
    (f' := fun t => 2 * ∑ k ∈ Finset.range N,
      θ t (k : ℤ) * dyadicTemperatureRHS μ (u t) (θ t) (k : ℤ)) ?_ ?_
  · intro t
    exact entropy_hasDerivAt ν μ κ N u θ h t
  · intro t
    have hpair := temperature_energy_rate_nonpos μ hμ (u t) (θ t) N
      (h.2.2 t).2.2.1 (h.2.2 t).2.2.2
    simpa using mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 2) hpair

/-! ## 4. The closed scalar rate inequality -/

/-- **The closed Grönwall rate inequality for the velocity energy.** Combining the Obstruction
estimate with the monotonicity of the entropy: for `t ≥ 0`,
`E' = 2 ∑_{k<N} u_k (du_k/dt) ≤ 2κ√S₀√E − 2νE` with `S₀ = entropy (θ 0) N`. The only role of
`hanti` is to replace `√S` by `√S₀` (`S ≤ S₀` and `√·` is monotone). -/
theorem velocity_energy_rate_le_of_solution (ν μ κ : ℝ) (hκ : 0 ≤ κ) (hν : 0 ≤ ν)
    (N : ℕ) (u θ : ℝ → ℤ → ℝ) (h : IsUnforcedTruncatedSolution ν μ κ N u θ)
    (hanti : Antitone fun t => entropy (θ t) N) {t : ℝ} (ht : 0 ≤ t) :
    2 * (∑ k ∈ Finset.range N, u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))
      ≤ 2 * κ * Real.sqrt (entropy (θ 0) N) * Real.sqrt (velocityEnergy (u t) N)
        - 2 * ν * velocityEnergy (u t) N := by
  have hpair := velocity_energy_rate_le ν κ hκ hν (u t) (θ t) N
    (h.2.2 t).1 (h.2.2 t).2.1
  have hSle : entropy (θ t) N ≤ entropy (θ 0) N := hanti ht
  have hsq : Real.sqrt (entropy (θ t) N) ≤ Real.sqrt (entropy (θ 0) N) := Real.sqrt_le_sqrt hSle
  have hcoef : 0 ≤ 2 * κ * Real.sqrt (velocityEnergy (u t) N) :=
    mul_nonneg (mul_nonneg (by norm_num) hκ) (Real.sqrt_nonneg _)
  have h2 : 2 * (∑ k ∈ Finset.range N,
        u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))
      ≤ 2 * (κ * (Real.sqrt (velocityEnergy (u t) N) * Real.sqrt (entropy (θ t) N))
            - ν * velocityEnergy (u t) N) :=
    mul_le_mul_of_nonneg_left hpair (by norm_num)
  have hstep := mul_le_mul_of_nonneg_left hsq hcoef
  simp only [velocityEnergy, entropy] at hpair h2 hstep ⊢
  nlinarith [h2, hstep]

/-! ## 5. The capstone -/

/-- **The unforced truncated dyadic Boussinesq model has no finite-time energy blowup.** Along any
truncated unforced solution on the shells `0, …, N-1` with Dirichlet ends, the velocity energy is
bounded on every compact time interval `[0, T]` by a constant depending only on the data. This is
the Stage-O headline: the transfer is exactly energy-conserving in the interior, the only source
is buoyancy bounded by the non-increasing entropy, and viscosity dominates. -/
theorem truncated_unforced_energy_bounded (ν μ κ : ℝ) (hν : 0 < ν) (hμ : 0 ≤ μ)
    (hκ : 0 ≤ κ) (N : ℕ) (u θ : ℝ → ℤ → ℝ) (h : IsUnforcedTruncatedSolution ν μ κ N u θ)
    {T : ℝ} (hcont : ContinuousOn (fun t => velocityEnergy (u t) N) (Set.Icc 0 T))
    (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, velocityEnergy (u t) N ≤ C := by
  have hanti : Antitone fun t => entropy (θ t) N := entropy_antitone ν μ κ hμ N u θ h
  refine no_finite_time_blowup (E := fun t => velocityEnergy (u t) N)
    (E' := fun t => 2 * ∑ k ∈ Finset.range N,
      u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))
    (S₀ := entropy (θ 0) N) hκ (entropy_nonneg (θ 0) N) hν ?_ ?_ ?_ ?_ T hT
  · exact (velocityEnergy_hasDerivAt ν μ κ N u θ h 0).continuousAt
  · intro t _
    exact velocityEnergy_nonneg (u t) N
  · intro t _
    exact velocityEnergy_hasDerivAt ν μ κ N u θ h t
  · intro t ht
    exact velocity_energy_rate_le_of_solution ν μ κ hκ hν.le N u θ h hanti (le_of_lt ht)

/-- **Uniform-in-time explicit bound in the dissipative case `2ν > κ√S₀`.** Under the hypotheses
of the capstone, if additionally `2ν > κ√(entropy (θ 0) N)` then the velocity energy is bounded
on `[0, T]` by the explicit constant `max (E 0) (κ√S₀/(2ν − κ√S₀))`, which does not depend on
`T`. -/
theorem truncated_unforced_energy_le_max (ν μ κ : ℝ) (hν : 0 < ν) (hμ : 0 ≤ μ)
    (hκ : 0 ≤ κ) (N : ℕ) (u θ : ℝ → ℤ → ℝ) (h : IsUnforcedTruncatedSolution ν μ κ N u θ)
    {T : ℝ} (hcont : ContinuousOn (fun t => velocityEnergy (u t) N) (Set.Icc 0 T))
    (hgap : 0 < 2 * ν - κ * Real.sqrt (entropy (θ 0) N)) (hT : 0 ≤ T) :
    ∀ t ∈ Set.Icc 0 T,
      velocityEnergy (u t) N ≤ max (velocityEnergy (u 0) N)
        (κ * Real.sqrt (entropy (θ 0) N) / (2 * ν - κ * Real.sqrt (entropy (θ 0) N))) := by
  have hanti : Antitone fun t => entropy (θ t) N := entropy_antitone ν μ κ hμ N u θ h
  refine energy_le_max_of_rate_le (S₀ := entropy (θ 0) N)
    (E' := fun t => 2 * ∑ k ∈ Finset.range N,
      u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))
    hκ (entropy_nonneg (θ 0) N) hν hgap hcont ?_ ?_ ?_
  · intro t _
    exact velocityEnergy_nonneg (u t) N
  · intro t _
    exact velocityEnergy_hasDerivAt ν μ κ N u θ h t
  · intro t ht
    exact velocity_energy_rate_le_of_solution ν μ κ hκ hν.le N u θ h hanti ht.1

/-! ## 6. Non-vacuity -/

/-- **The zero state is an equilibrium solution** of the truncated unforced model: every transfer
term and every dissipation term vanishes, so the constant (in time) ladders `u ≡ 0`, `θ ≡ 0`
solve the ODE, and the Dirichlet conditions hold trivially. This witnesses that
`IsUnforcedTruncatedSolution` is inhabited. -/
theorem zero_is_unforcedTruncatedSolution (ν μ κ : ℝ) (N : ℕ) :
    IsUnforcedTruncatedSolution ν μ κ N (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t k _ _
    have h0 : dyadicVelocityRHS ν κ (fun _ : ℤ => (0 : ℝ)) (fun _ : ℤ => (0 : ℝ)) k = 0 := by
      simp [dyadicVelocityRHS, generalVelocityRHS, boussinesqTransferU, dyadicWeight]
    rw [h0]
    exact hasDerivAt_const t 0
  · intro t k _ _
    have h0 : dyadicTemperatureRHS μ (fun _ : ℤ => (0 : ℝ)) (fun _ : ℤ => (0 : ℝ)) k = 0 := by
      simp [dyadicTemperatureRHS, generalTemperatureRHS, boussinesqTransferTheta, dyadicWeight]
    rw [h0]
    exact hasDerivAt_const t 0
  · intro t
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The capstone applies to the zero equilibrium, yielding a bound on `[0, 1]`. -/
example : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    velocityEnergy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2 ≤ C := by
  refine truncated_unforced_energy_bounded (T := 1) 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) 2 (fun _ _ => 0) (fun _ _ => 0)
    (zero_is_unforcedTruncatedSolution 1 1 1 2) ?_ (by norm_num)
  have hfun : (fun t => velocityEnergy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2)
      = fun _ => (0 : ℝ) := by
    funext t
    simp [velocityEnergy]
  rw [hfun]
  exact continuousOn_const

/-- A concrete non-zero state on the shells `-1, 0, 1, 2`: `u = (0, 1, 3, 0)`. -/
private def uConc : ℤ → ℝ :=
  fun k => if k = -1 then 0 else if k = 0 then 1 else if k = 1 then 3 else if k = 2 then 0 else 0

/-- The accompanying temperature state: `θ = (0, 1, 2, 0)`. -/
private def θConc : ℤ → ℝ :=
  fun k => if k = -1 then 0 else if k = 0 then 1 else if k = 1 then 2 else if k = 2 then 0 else 0

/-- Concrete velocity energy: `1² + 3² = 10`. -/
example : velocityEnergy uConc 2 = 10 := by
  norm_num [velocityEnergy, Finset.sum_range_succ, Finset.sum_range_zero, uConc]

/-- Concrete entropy: `1² + 2² = 5`. -/
example : entropy θConc 2 = 5 := by
  norm_num [entropy, Finset.sum_range_succ, Finset.sum_range_zero, θConc]

/-- Concrete velocity pairing: the non-linear transfer does *not* vanish, it equals `-30`. -/
example :
    (∑ k ∈ Finset.range 2, uConc (k : ℤ) * dyadicVelocityRHS 1 1 uConc θConc (k : ℤ)) = -30 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uConc, θConc, dyadicVelocityRHS,
    generalVelocityRHS, boussinesqTransferU, dyadicWeight]

/-- The doubled (`E'`) form of the Obstruction rate inequality at the concrete state:
`-60 ≤ 2√5·√10 − 20`, which is strict, so the estimate used by the capstone is not vacuous. -/
example : 2 * (∑ k ∈ Finset.range 2, uConc (k : ℤ) * dyadicVelocityRHS 1 1 uConc θConc (k : ℤ))
    ≤ 2 * 1 * Real.sqrt (entropy θConc 2) * Real.sqrt (velocityEnergy uConc 2)
      - 2 * 1 * velocityEnergy uConc 2 := by
  have h := velocity_energy_rate_le 1 1 (by norm_num) (by norm_num) uConc θConc 2
    (by norm_num [uConc]) (by norm_num [uConc])
  simp only [velocityEnergy, entropy] at h ⊢
  nlinarith [h]

end Cascade

/-! ## Axiom audit -/

#print axioms Cascade.IsUnforcedTruncatedSolution
#print axioms Cascade.velocityEnergy
#print axioms Cascade.entropy
#print axioms Cascade.velocityEnergy_nonneg
#print axioms Cascade.entropy_nonneg
#print axioms Cascade.finset_sum_apply
#print axioms Cascade.velocityEnergy_hasDerivAt
#print axioms Cascade.entropy_hasDerivAt
#print axioms Cascade.entropy_antitone
#print axioms Cascade.velocity_energy_rate_le_of_solution
#print axioms Cascade.truncated_unforced_energy_bounded
#print axioms Cascade.truncated_unforced_energy_le_max
#print axioms Cascade.zero_is_unforcedTruncatedSolution
