import Cascade.Boussinesq

/-!
# Stage R — the Boussinesq scaling of the dyadic model

Shell `k` of the frozen two-species dyadic Boussinesq model (`Cascade/Boussinesq.lean`) carries
wavenumber `2^k`.  The Boussinesq scaling `x ↦ λ x`, `λ = 2^s`, therefore acts on the ladder by
the shell shift `k ↦ k - s` together with the amplitude factors of the Boussinesq symmetry

    u_λ(x,t) = λ^b · u(λx, λ^{b+1}t),   θ_λ = λ^{2b+1} · θ(λx, λ^{b+1}t),   p_λ = λ^{2b} p.

Writing the amplitude `λ^a` as `dyadicWeight s ^ a = dyadicWeight (s * a)`, this file formalizes
the **RHS covariance** (the algebraic content of scale invariance): the rescaled ladders solve
the same ODE with rescaled parameters.

* `scaleVelocity` / `scaleTemperature` are the scaling act on the two ladders.
* The frozen Stage R model of `Cascade/Boussinesq.lean` (`A = 1`, `B = 0`, `Ã = 1`, `B̃ = 1`) is
  the named model:
  * `scaling_covariant_velocity` : the momentum equation is homogeneous of degree `2b+1`, and the
    viscosity rescales as `ν ↦ ν · λ^{b-1}`.
  * `scaling_covariant_temperature` : the temperature equation is homogeneous of degree `3b+2`,
    and the thermal diffusivity rescales as `μ ↦ μ · λ^{b-1}`.
  * `scaling_covariant` : the pair, i.e. the full frozen model.
  * `scaling_covariant_b_one_velocity` / `scaling_covariant_b_one_temperature` : at the standard
    2D Boussinesq choice `b = 1` the parameters are unchanged (`λ^0 = 1`) and the degrees are `3`
    and `5`.
* The four-parameter version is kept as the general structural result under the `general*` names
  (`general_scaling_covariant_velocity`, `general_scaling_covariant_temperature`,
  `general_scaling_covariant`, and the corollaries
  `general_scaling_covariant_b_one_velocity` / `general_scaling_covariant_b_one_temperature`).
  Each frozen theorem is the immediate specialisation of its general counterpart at
  `A = 1, B = 0` (velocity) or `Ã = 1, B̃ = 1` (temperature).
* `scaling_pressure_gradient_degree` : `p_λ = λ^{2b} p` makes `∇p_λ` homogeneous of degree
  `2b+1`, the common degree of every term of the momentum equation.

Everything is `zpow` arithmetic: `dyadicWeight a * dyadicWeight b = dyadicWeight (a + b)` and
`(dyadicWeight a)^2 = dyadicWeight (2a)`.
-/

noncomputable section

namespace Cascade

/-- The Boussinesq scaling act on the velocity ladder: `u ↦ λ^b · u(· − s)`, `λ = 2^s`. -/
def scaleVelocity (s b : ℤ) (u : ℤ → ℝ) : ℤ → ℝ :=
  fun k => dyadicWeight (s * b) * u (k - s)

/-- The Boussinesq scaling act on the temperature ladder: `θ ↦ λ^{2b+1} · θ(· − s)`. -/
def scaleTemperature (s b : ℤ) (θ : ℤ → ℝ) : ℤ → ℝ :=
  fun k => dyadicWeight (s * (2 * b + 1)) * θ (k - s)

/-- The fixed standard scaling exponent: `b = 1` (2D Boussinesq). -/
def boussinesqB : ℤ := 1

/-! ## `zpow` arithmetic of the dyadic weight -/

/-- The dyadic weight is multiplicative in its exponent: `2^{a+b} = 2^a · 2^b`. -/
private lemma dyadicWeight_add (a b : ℤ) : dyadicWeight (a + b) = dyadicWeight a * dyadicWeight b := by
  simp only [dyadicWeight]
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]

/-- The square of a dyadic weight: `(2^a)^2 = 2^{2a}`. -/
private lemma dyadicWeight_sq (a : ℤ) : (dyadicWeight a) ^ 2 = dyadicWeight (2 * a) := by
  simp only [dyadicWeight]
  rw [sq, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

/-! ## Amplitude identities

The velocity transfer carries `(λ^b)^2 · λ^{2k}` which equals `λ^{2b+1} · λ^{2(k-s)}`; the
temperature transfer carries `λ^b · λ^{2b+1} · λ^{2k}`, equal to `λ^{3b+2} · λ^{2(k-s)}`; and the
dissipation carries `λ^{b-1} · λ^{2k}` times the corresponding ladder amplitude.
-/

/-- Velocity transfer: `2^k · (2^{sb})^2 = 2^{s(2b+1)} · 2^{k-s}`. -/
private lemma dyadicWeight_chain_v (s b k : ℤ) :
    dyadicWeight k * (dyadicWeight (s * b)) ^ 2
      = dyadicWeight (s * (2 * b + 1)) * dyadicWeight (k - s) := by
  rw [dyadicWeight_sq]
  simp only [← dyadicWeight_add]
  congr 1
  ring

/-- Temperature transfer: `2^k · 2^{sb} · 2^{s(2b+1)} = 2^{s(3b+2)} · 2^{k-s}`. -/
private lemma dyadicWeight_chain_t (s b k : ℤ) :
    dyadicWeight k * (dyadicWeight (s * b) * dyadicWeight (s * (2 * b + 1)))
      = dyadicWeight (s * (3 * b + 2)) * dyadicWeight (k - s) := by
  simp only [← dyadicWeight_add]
  congr 1
  ring

/-- Velocity dissipation amplitude: `2^{s(b-1)} · 2^{2s} · 2^{sb} = 2^{s(2b+1)}`. -/
private lemma dyadicWeight_diss_v_amp (s b : ℤ) :
    dyadicWeight (s * (b - 1)) * dyadicWeight (2 * s) * dyadicWeight (s * b)
      = dyadicWeight (s * (2 * b + 1)) := by
  simp only [← dyadicWeight_add]
  congr 1
  ring

/-- Temperature dissipation amplitude:
`2^{s(b-1)} · 2^{2s} · 2^{s(2b+1)} = 2^{s(3b+2)}`. -/
private lemma dyadicWeight_diss_t_amp (s b : ℤ) :
    dyadicWeight (s * (b - 1)) * dyadicWeight (2 * s) * dyadicWeight (s * (2 * b + 1))
      = dyadicWeight (s * (3 * b + 2)) := by
  simp only [← dyadicWeight_add]
  congr 1
  ring

/-- Velocity dissipation: `2^{s(b-1)} · 2^{2k} · 2^{sb}
= 2^{s(2b+1)} · 2^{2(k-s)}`. -/
private lemma dyadicWeight_diss_v (s b k : ℤ) :
    dyadicWeight (s * (b - 1)) * dyadicWeight (2 * k) * dyadicWeight (s * b)
      = dyadicWeight (s * (2 * b + 1)) * dyadicWeight (2 * (k - s)) := by
  have h : (2 : ℤ) * k = 2 * (k - s) + 2 * s := by ring
  rw [h, dyadicWeight_add]
  rw [show dyadicWeight (s * (b - 1)) * (dyadicWeight (2 * (k - s)) * dyadicWeight (2 * s))
            * dyadicWeight (s * b)
        = dyadicWeight (2 * (k - s))
            * (dyadicWeight (s * (b - 1)) * dyadicWeight (2 * s) * dyadicWeight (s * b)) by ring]
  rw [dyadicWeight_diss_v_amp]
  ring

/-- Temperature dissipation: `2^{s(b-1)} · 2^{2k} · 2^{s(2b+1)}
= 2^{s(3b+2)} · 2^{2(k-s)}`. -/
private lemma dyadicWeight_diss_t (s b k : ℤ) :
    dyadicWeight (s * (b - 1)) * dyadicWeight (2 * k) * dyadicWeight (s * (2 * b + 1))
      = dyadicWeight (s * (3 * b + 2)) * dyadicWeight (2 * (k - s)) := by
  have h : (2 : ℤ) * k = 2 * (k - s) + 2 * s := by ring
  rw [h, dyadicWeight_add]
  rw [show dyadicWeight (s * (b - 1)) * (dyadicWeight (2 * (k - s)) * dyadicWeight (2 * s))
            * dyadicWeight (s * (2 * b + 1))
        = dyadicWeight (2 * (k - s))
            * (dyadicWeight (s * (b - 1)) * dyadicWeight (2 * s)
                * dyadicWeight (s * (2 * b + 1))) by ring]
  rw [dyadicWeight_diss_t_amp]
  ring

/-! ## Scaling of the transfer and of the dissipation -/

/-- The velocity transfer is homogeneous of degree `2b+1` under the shell shift. -/
private lemma boussinesqTransferU_scale (s b : ℤ) (A B : ℝ) (u : ℤ → ℝ) (k : ℤ) :
    boussinesqTransferU A B (scaleVelocity s b u) k
      = dyadicWeight (s * (2 * b + 1)) * boussinesqTransferU A B u (k - s) := by
  have h1 : k - 1 - s = (k - s) - 1 := by ring
  have h2 : k + 1 - s = (k - s) + 1 := by ring
  have hfac : boussinesqTransferU A B (scaleVelocity s b u) k
      = dyadicWeight k * (dyadicWeight (s * b)) ^ 2
          * (A * ((u ((k - s) - 1)) ^ 2 - 2 * u (k - s) * u ((k - s) + 1))
              + B * (u (k - s) * u ((k - s) - 1) - 2 * (u ((k - s) + 1)) ^ 2)) := by
    simp only [boussinesqTransferU, scaleVelocity, h1, h2, mul_pow]
    ring
  rw [hfac, dyadicWeight_chain_v]
  simp only [boussinesqTransferU]
  ring

/-- The temperature transfer is homogeneous of degree `3b+2` under the shell shift. -/
private lemma boussinesqTransferTheta_scale (s b : ℤ) (At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    boussinesqTransferTheta At Bt (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight (s * (3 * b + 2)) * boussinesqTransferTheta At Bt u θ (k - s) := by
  have h1 : k - 1 - s = (k - s) - 1 := by ring
  have h2 : k + 1 - s = (k - s) + 1 := by ring
  have hfac : boussinesqTransferTheta At Bt (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight k * (dyadicWeight (s * b) * dyadicWeight (s * (2 * b + 1)))
          * (At * (u ((k - s) - 1) * θ ((k - s) - 1) - 2 * u (k - s) * θ ((k - s) + 1))
              + Bt * (u (k - s) * θ ((k - s) - 1)
                  - 2 * u ((k - s) + 1) * θ ((k - s) + 1))) := by
    simp only [boussinesqTransferTheta, scaleVelocity, scaleTemperature, h1, h2]
    ring
  rw [hfac, dyadicWeight_chain_t]
  simp only [boussinesqTransferTheta]
  ring

/-- The velocity dissipation rescales: `ν · λ^{b-1} · 2^{2k} · u_λ = λ^{2b+1} · ν · 2^{2(k-s)} u`. -/
private lemma diss_v_scale (s b : ℤ) (ν : ℝ) (u : ℤ → ℝ) (k : ℤ) :
    ν * dyadicWeight (s * (b - 1)) * dyadicWeight (2 * k) * scaleVelocity s b u k
      = dyadicWeight (s * (2 * b + 1)) * (ν * dyadicWeight (2 * (k - s)) * u (k - s)) := by
  simp only [scaleVelocity]
  rw [show ν * dyadicWeight (s * (b - 1)) * dyadicWeight (2 * k)
            * (dyadicWeight (s * b) * u (k - s))
        = ν * (dyadicWeight (s * (b - 1)) * dyadicWeight (2 * k) * dyadicWeight (s * b))
            * u (k - s) by ring]
  rw [dyadicWeight_diss_v]
  ring

/-- The temperature dissipation rescales:
`μ · λ^{b-1} · 2^{2k} · θ_λ = λ^{3b+2} · μ · 2^{2(k-s)} θ`. -/
private lemma diss_t_scale (s b : ℤ) (μ : ℝ) (θ : ℤ → ℝ) (k : ℤ) :
    μ * dyadicWeight (s * (b - 1)) * dyadicWeight (2 * k) * scaleTemperature s b θ k
      = dyadicWeight (s * (3 * b + 2))
          * (μ * dyadicWeight (2 * (k - s)) * θ (k - s)) := by
  simp only [scaleTemperature]
  rw [show μ * dyadicWeight (s * (b - 1)) * dyadicWeight (2 * k)
            * (dyadicWeight (s * (2 * b + 1)) * θ (k - s))
        = μ * (dyadicWeight (s * (b - 1)) * dyadicWeight (2 * k)
              * dyadicWeight (s * (2 * b + 1))) * θ (k - s) by ring]
  rw [dyadicWeight_diss_t]
  ring

/-! ## Scaling covariance of the model -/

/-- **Scaling covariance, velocity component (general four-parameter model).** Under the
Boussinesq scaling with exponents `(s, b)` the velocity equation is homogeneous of degree
`2b+1`; the viscosity rescales by `λ^{b-1}`. -/
theorem general_scaling_covariant_velocity (s b : ℤ) (ν κ A B : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    generalVelocityRHS (ν * dyadicWeight (s * (b - 1))) κ A B
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight (s * (2 * b + 1)) * generalVelocityRHS ν κ A B u θ (k - s) := by
  simp only [generalVelocityRHS]
  rw [boussinesqTransferU_scale]
  have hbuoy : κ * scaleTemperature s b θ k
      = dyadicWeight (s * (2 * b + 1)) * (κ * θ (k - s)) := by
    simp only [scaleTemperature]
    ring
  rw [hbuoy, diss_v_scale]
  ring

/-- **Scaling covariance, temperature component (general four-parameter model).** Homogeneous of
degree `3b+2`; the thermal diffusivity rescales by `λ^{b-1}`. -/
theorem general_scaling_covariant_temperature (s b : ℤ) (μ At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    generalTemperatureRHS (μ * dyadicWeight (s * (b - 1))) At Bt
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight (s * (3 * b + 2)) * generalTemperatureRHS μ At Bt u θ (k - s) := by
  simp only [generalTemperatureRHS]
  rw [boussinesqTransferTheta_scale, diss_t_scale]
  ring

/-- **Scaling covariance of the full general four-parameter dyadic Boussinesq model.** -/
theorem general_scaling_covariant (s b : ℤ) (ν μ κ A B At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    generalBoussinesqRHS (ν * dyadicWeight (s * (b - 1))) (μ * dyadicWeight (s * (b - 1)))
        κ A B At Bt (scaleVelocity s b u) (scaleTemperature s b θ) k
      = (dyadicWeight (s * (2 * b + 1)) * (generalBoussinesqRHS ν μ κ A B At Bt u θ (k - s)).1,
         dyadicWeight (s * (3 * b + 2)) * (generalBoussinesqRHS ν μ κ A B At Bt u θ (k - s)).2) := by
  simp only [generalBoussinesqRHS]
  exact Prod.ext (general_scaling_covariant_velocity s b ν κ A B u θ k)
    (general_scaling_covariant_temperature s b μ At Bt u θ k)

/-- **The standard 2D Boussinesq case `b = 1` (general model).** Momentum is homogeneous of
degree `3` with the parameters unchanged. -/
theorem general_scaling_covariant_b_one_velocity (s : ℤ) (ν κ A B : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    generalVelocityRHS ν κ A B (scaleVelocity s boussinesqB u) (scaleTemperature s boussinesqB θ) k
      = dyadicWeight (3 * s) * generalVelocityRHS ν κ A B u θ (k - s) := by
  have h := general_scaling_covariant_velocity s boussinesqB ν κ A B u θ k
  have hν : ν * dyadicWeight (s * (boussinesqB - 1)) = ν := by
    simp [boussinesqB, dyadicWeight]
  have he : s * (2 * boussinesqB + 1) = 3 * s := by
    simp only [boussinesqB]
    ring
  rw [hν, he] at h
  exact h

/-- **The standard 2D Boussinesq case `b = 1` (general model).** Temperature is homogeneous of
degree `5`. -/
theorem general_scaling_covariant_b_one_temperature (s : ℤ) (μ At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    generalTemperatureRHS μ At Bt (scaleVelocity s boussinesqB u) (scaleTemperature s boussinesqB θ) k
      = dyadicWeight (5 * s) * generalTemperatureRHS μ At Bt u θ (k - s) := by
  have h := general_scaling_covariant_temperature s boussinesqB μ At Bt u θ k
  have hμ : μ * dyadicWeight (s * (boussinesqB - 1)) = μ := by
    simp [boussinesqB, dyadicWeight]
  have he : s * (3 * boussinesqB + 2) = 5 * s := by
    simp only [boussinesqB]
    ring
  rw [hμ, he] at h
  exact h

/-! ### Scaling covariance of the frozen Stage R model -/

/-- **Frozen Stage R scaling covariance, velocity component** (`A = 1`, `B = 0`). -/
theorem scaling_covariant_velocity (s b : ℤ) (ν κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    dyadicVelocityRHS (ν * dyadicWeight (s * (b - 1))) κ
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight (s * (2 * b + 1)) * dyadicVelocityRHS ν κ u θ (k - s) := by
  simpa [dyadicVelocityRHS] using general_scaling_covariant_velocity s b ν κ 1 0 u θ k

/-- **Frozen Stage R scaling covariance, temperature component** (`Ã = 1`, `B̃ = 1`). -/
theorem scaling_covariant_temperature (s b : ℤ) (μ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    dyadicTemperatureRHS (μ * dyadicWeight (s * (b - 1)))
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight (s * (3 * b + 2)) * dyadicTemperatureRHS μ u θ (k - s) := by
  simpa [dyadicTemperatureRHS] using general_scaling_covariant_temperature s b μ 1 1 u θ k

/-- **Scaling covariance of the frozen Stage R dyadic Boussinesq model.** -/
theorem scaling_covariant (s b : ℤ) (ν μ κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    dyadicBoussinesqRHS (ν * dyadicWeight (s * (b - 1))) (μ * dyadicWeight (s * (b - 1))) κ
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = (dyadicWeight (s * (2 * b + 1)) * (dyadicBoussinesqRHS ν μ κ u θ (k - s)).1,
         dyadicWeight (s * (3 * b + 2)) * (dyadicBoussinesqRHS ν μ κ u θ (k - s)).2) := by
  simpa [dyadicBoussinesqRHS, dyadicVelocityRHS, dyadicTemperatureRHS, generalBoussinesqRHS] using
    general_scaling_covariant s b ν μ κ 1 0 1 1 u θ k

/-- **The standard 2D Boussinesq case `b = 1` (frozen model).** Momentum is homogeneous of
degree `3` with the parameters unchanged. -/
theorem scaling_covariant_b_one_velocity (s : ℤ) (ν κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    dyadicVelocityRHS ν κ (scaleVelocity s boussinesqB u) (scaleTemperature s boussinesqB θ) k
      = dyadicWeight (3 * s) * dyadicVelocityRHS ν κ u θ (k - s) := by
  have h := scaling_covariant_velocity s boussinesqB ν κ u θ k
  have hν : ν * dyadicWeight (s * (boussinesqB - 1)) = ν := by
    simp [boussinesqB, dyadicWeight]
  have he : s * (2 * boussinesqB + 1) = 3 * s := by
    simp only [boussinesqB]
    ring
  rw [hν, he] at h
  exact h

/-- **The standard 2D Boussinesq case `b = 1` (frozen model).** Temperature is homogeneous of
degree `5`. -/
theorem scaling_covariant_b_one_temperature (s : ℤ) (μ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    dyadicTemperatureRHS μ (scaleVelocity s boussinesqB u) (scaleTemperature s boussinesqB θ) k
      = dyadicWeight (5 * s) * dyadicTemperatureRHS μ u θ (k - s) := by
  have h := scaling_covariant_temperature s boussinesqB μ u θ k
  have hμ : μ * dyadicWeight (s * (boussinesqB - 1)) = μ := by
    simp [boussinesqB, dyadicWeight]
  have he : s * (3 * boussinesqB + 2) = 5 * s := by
    simp only [boussinesqB]
    ring
  rw [hμ, he] at h
  exact h

/-- The pressure scales as `p_λ = λ^{2b} p`, so `∇p_λ` is homogeneous of degree `2b+1` —
the same degree as every term of the momentum equation (which is what
`scaling_covariant_velocity` records). -/
theorem scaling_pressure_gradient_degree (s b : ℤ) :
    dyadicWeight (s * (2 * b)) * dyadicWeight s = dyadicWeight (s * (2 * b + 1)) := by
  rw [← dyadicWeight_add]
  congr 1
  ring

/-! ## Non-vacuity checks

Both sides of the frozen covariance identity are evaluated on a concrete instance.  Take the
standard 2D exponent `b = 1`, shell shift `s = 1` (so `λ = 2`), unit parameters `ν = κ = 1`, and
the constant ladders `u ≡ 1`, `θ ≡ 1`; the scaled ladders are `u_λ ≡ 2`, `θ_λ ≡ 8`.  The
left-hand side of the velocity identity is `2·(4 − 8) + 1·8 − 1·4·2 = −8`, and the right-hand
side is `2^{3}·(2^{0}·(1 − 2) + 1 − 2^{0}) = 8·(−1) = −8`. -/
example :
    dyadicVelocityRHS 1 1 (scaleVelocity 1 1 (fun _ => 1))
        (scaleTemperature 1 1 (fun _ => 1)) 1 = -8 := by
  simp only [dyadicVelocityRHS, generalVelocityRHS, boussinesqTransferU, scaleVelocity,
    scaleTemperature, dyadicWeight]
  norm_num

/-- The right-hand side of the same instance, `dyadicWeight (3·1) · (du_k/dt at k − 1)`. -/
example :
    dyadicWeight (3 * (1 : ℤ)) * dyadicVelocityRHS 1 1 (fun _ => 1) (fun _ => (1 : ℝ))
        ((1 : ℤ) - 1) = -8 := by
  simp only [dyadicVelocityRHS, generalVelocityRHS, boussinesqTransferU, dyadicWeight]
  norm_num

/-- The same two sides are equal, by the frozen `b = 1` covariance theorem. -/
example :
    dyadicVelocityRHS 1 1 (scaleVelocity 1 1 (fun _ => 1))
        (scaleTemperature 1 1 (fun _ => 1)) 1
      = dyadicWeight (3 * (1 : ℤ)) * dyadicVelocityRHS 1 1 (fun _ => 1)
          (fun _ => (1 : ℝ)) ((1 : ℤ) - 1) :=
  scaling_covariant_b_one_velocity 1 1 1 (fun _ => 1) (fun _ => (1 : ℝ)) 1

/-- The temperature side of the same instance.  The scaled transfer is
`2·((16 − 32) + (16 − 32)) = −64` and the dissipation is `1·4·8 = 32`, so the left-hand side is
`−96`.  The right-hand side is `2^{5}·(2^{0}·((1 − 2) + (1 − 2)) − 1) = 32·(−3) = −96`. -/
example :
    dyadicTemperatureRHS 1 (scaleVelocity 1 1 (fun _ => 1))
        (scaleTemperature 1 1 (fun _ => 1)) 1 = -96 := by
  simp only [dyadicTemperatureRHS, generalTemperatureRHS, boussinesqTransferTheta, scaleVelocity,
    scaleTemperature, dyadicWeight]
  norm_num

/-- The same two temperature sides are equal, by the frozen `b = 1` covariance theorem. -/
example :
    dyadicTemperatureRHS 1 (scaleVelocity 1 1 (fun _ => 1))
        (scaleTemperature 1 1 (fun _ => 1)) 1
      = dyadicWeight (5 * (1 : ℤ)) * dyadicTemperatureRHS 1 (fun _ => 1)
          (fun _ => (1 : ℝ)) ((1 : ℤ) - 1) :=
  scaling_covariant_b_one_temperature 1 1 (fun _ => 1) (fun _ => (1 : ℝ)) 1

/-- The amplitude normalization: `dyadicWeight 0 = 2^0 = 1`. -/
example : dyadicWeight 0 = (1 : ℝ) := by
  simp [dyadicWeight]

/-- At `b = 1` the viscosity/diffusivity rescaling `λ^{b-1} = λ^0 = 1` is the identity,
for every shift `s`. -/
example (s : ℤ) (ν : ℝ) : ν * dyadicWeight (s * (boussinesqB - 1)) = ν := by
  simp [boussinesqB, dyadicWeight]

end Cascade

#print axioms Cascade.general_scaling_covariant_velocity
#print axioms Cascade.general_scaling_covariant_temperature
#print axioms Cascade.general_scaling_covariant
#print axioms Cascade.general_scaling_covariant_b_one_velocity
#print axioms Cascade.general_scaling_covariant_b_one_temperature
#print axioms Cascade.scaling_covariant_velocity
#print axioms Cascade.scaling_covariant_temperature
#print axioms Cascade.scaling_covariant
#print axioms Cascade.scaling_covariant_b_one_velocity
#print axioms Cascade.scaling_covariant_b_one_temperature
#print axioms Cascade.scaling_pressure_gradient_degree
