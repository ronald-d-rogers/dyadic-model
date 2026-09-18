import Cascade.DissipationDegree
import Cascade.EnstrophyBound
import Cascade.BuoyancySign
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# The dissipation threshold of the dyadic Boussinesq model

The frozen Stage R model (`Cascade/Boussinesq.lean`) dissipates the velocity with
`ν · 2^{2k} · u_k` — the dyadic Laplacian `−Δ`, dissipation **degree** `e = 2`.  In Cheskidov's
notation the dissipation degree is `α = e/2`, so the library model is `α = 1`.  This file
generalises both dissipation channels to `ν · 2^{e k} · u_k`, `μ · 2^{e k} · θ_k` for an integer
degree `e`, freezes that model, and locates the thresholds at which the enstrophy barrier can be
closed.

## The two thresholds (they are different)

Write `H = Σ_{k<N} 2^{2k}u_k²` (enstrophy), `E = Σ_{k<N} u_k²` (energy),
`D_e = Σ_{k<N} 2^{(2+e)k}u_k²` (dissipation at degree `e`) and
`W_e = Σ_{k<N} 2^{(2−e)k}u_k²` (the backplate weight).

1. **Quadratic domination** `D_e ≥ c·H²/E` (homogeneity `2` in `H`).  This holds for `e ≥ 2`
   (`dissipation_ge_of_two_le`, from `D_e ≥ D_2` and `H² ≤ D_2·E`) and **fails for every `e < 2`**
   (`no_uniform_dissipation_domination`): the single mode `u = δ_{·,k}` gives
   `D_e·E/H² = 2^{(e−2)k} → 0`, so no constant `c > 0` works.
2. **Barrier tractability** — what the enstrophy budget actually needs.  There the transfer enters
   at homogeneity `3/2` and the dissipation at homogeneity `1 + e/2`, so the barrier is
   **unconditionally closable iff `e > 1`**; at `e = 1` the two homogeneities *tie exactly*, and the
   barrier closes only under a size condition (`ν > 3√E_max`), not unconditionally; for `e ≤ 0` the
   dissipation is too weak.  The engine is the interpolated bound
   `D_e ≥ H^{1+e/2}/E^{e/2}` (squared form: `dissipation_interp_sq`), which holds for `0 ≤ e ≤ 2`
   and comes from the two ingredients
   * *weighted Cauchy–Schwarz* `D_e·W_e ≥ H²` (`weighted_cauchy_schwarz`), and
   * *Hölder backplate* `W_e ≤ E^{e/2}·H^{1−e/2}` (squared: `weightedEnstrophy_sq_le`),
   chained as `D_e ≥ H²/W_e ≥ H^{1+e/2}/E^{e/2}`.

**So the barrier threshold is `e = 1`, i.e. `α = 1/2`** — *not* `e = 2`; the latter is the (stronger,
homogeneity-`2`) quadratic-domination threshold.  For integers the picture is: unconditional for
`e ≥ 2`, marginal / conditional at `e = 1`, dead for `e ≤ 0`.  The model's own exponent is `e = 2`,
the lowest integer in the *unconditional* range, so the frozen model sits at the bottom of that
range — but it is *above* the barrier threshold `e = 1`, which coincides with Cheskidov's
global-regularity threshold `α = 1/2` (Cheskidov's finite-time blowup is at `α < 1/3`, i.e.
`e < 2/3`; the 3D Navier–Stokes exponent `α = 2/5` (`e = 4/5`) lies below the barrier threshold and
is not representable by an integer `e`).  The open gap is `α ∈ [1/3, 2/5)`, *not* `[1/3, 1/2)`:
the upper part was closed by Barbato–Morandin–Romito, *Smooth solutions for the dyadic model*,
Nonlinearity **24** (2011) 3083–3097 (arXiv:1007.3401), Theorem A, who prove existence, uniqueness
and smoothness for `β ∈ (2, 5/2]` in their normalisation — i.e. `α = 1/β ∈ [2/5, 1/2)` — and who
state that this is the range "corresponding ... to the three dimensional Navier–Stokes equations".
So the 3D-calibrated exponent `α = 2/5` is a *known regular* endpoint, not an open case.

## Contents

1. The frozen general-degree model: `velocityRHSDegreeE`, `temperatureRHSDegreeE`,
   `boussinesqRHSDegreeE`, recovery at `e = 2`, scaling covariance `ν, μ ↦ · λ^{b+1−e}`, and the
   general-degree truncated solution predicates.
2. The weighted quantities `D_e`, `W_e`, `E`, the arbitrary-degree `D_e ≥ D_2` domination, and the
   quadratic-domination threshold `e ≥ 2 ⇒ D_e ≥ H²/E`.
3. The weighted Cauchy–Schwarz and Hölder backplate, and their synthesis
   `dissipation_interp_sq` (`H^{2+e} ≤ D_e²·E^e` for `0 ≤ e ≤ 2`).
4. The failure of the *quadratic* domination below `e = 2` (single-mode witness) — with the note
   that this does **not** by itself obstruct the barrier, which needs only `e > 1`.
5. Machine-checked numerical evaluations.
-/
noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators

namespace Cascade

/-! ## 1. The frozen general-degree model -/

/-- Velocity component of the dyadic Boussinesq ODE at **dissipation degree** `e`: the viscosity
term is `ν · 2^{e k} · u_k`.  At `e = 2` it is `generalVelocityRHS`. -/
def velocityRHSDegreeE (ν κ A B : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ :=
  boussinesqTransferU A B u k + κ * θ k - ν * dyadicWeight (e * k) * u k

/-- Temperature component at **dissipation degree** `e`: the thermal diffusivity term is
`μ · 2^{e k} · θ_k`.  At `e = 2` it is `generalTemperatureRHS`. -/
def temperatureRHSDegreeE (μ At Bt : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ :=
  boussinesqTransferTheta At Bt u θ k - μ * dyadicWeight (e * k) * θ k

/-- **The general-degree two-species dyadic Boussinesq ODE** as a pair `(du_k/dt, dθ_k/dt)`, with
both dissipations at degree `e`. -/
def boussinesqRHSDegreeE (ν μ κ A B At Bt : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ × ℝ :=
  (velocityRHSDegreeE ν κ A B e u θ k, temperatureRHSDegreeE μ At Bt e u θ k)

/-- **Recovery at degree `2`**: the velocity component is the library's `generalVelocityRHS`. -/
theorem velocityRHSDegreeE_two (ν κ A B : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    velocityRHSDegreeE ν κ A B 2 u θ k = generalVelocityRHS ν κ A B u θ k := by
  rw [velocityRHSDegreeE, generalVelocityRHS]

/-- **Recovery at degree `2`**: the temperature component is the library's
`generalTemperatureRHS`. -/
theorem temperatureRHSDegreeE_two (μ At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    temperatureRHSDegreeE μ At Bt 2 u θ k = generalTemperatureRHS μ At Bt u θ k := by
  rw [temperatureRHSDegreeE, generalTemperatureRHS]

/-- **Recovery of the frozen Stage R pair at degree `2`.** -/
theorem boussinesqRHSDegreeE_two (ν μ κ : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    boussinesqRHSDegreeE ν μ κ 1 0 1 1 2 u θ k = dyadicBoussinesqRHS ν μ κ u θ k := by
  rw [boussinesqRHSDegreeE, velocityRHSDegreeE, temperatureRHSDegreeE, dyadicBoussinesqRHS,
    dyadicVelocityRHS, dyadicTemperatureRHS, generalVelocityRHS, generalTemperatureRHS]

/-! ### Scaling covariance at degree `e` -/

private lemma dW_add (a b : ℤ) : dyadicWeight (a + b) = dyadicWeight a * dyadicWeight b := by
  simp only [dyadicWeight]
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]

private lemma dW_sq (a : ℤ) : (dyadicWeight a) ^ 2 = dyadicWeight (2 * a) := by
  simp only [dyadicWeight]
  rw [sq, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

private lemma dW_chain_v (s b k : ℤ) :
    dyadicWeight k * (dyadicWeight (s * b)) ^ 2
      = dyadicWeight (s * (2 * b + 1)) * dyadicWeight (k - s) := by
  rw [dW_sq]
  simp only [← dW_add]
  congr 1
  ring

private lemma dW_chain_t (s b k : ℤ) :
    dyadicWeight k * (dyadicWeight (s * b) * dyadicWeight (s * (2 * b + 1)))
      = dyadicWeight (s * (3 * b + 2)) * dyadicWeight (k - s) := by
  simp only [← dW_add]
  congr 1
  ring

private lemma dW_diss_v_amp (s b e : ℤ) :
    dyadicWeight (s * (b + 1 - e)) * dyadicWeight (e * s) * dyadicWeight (s * b)
      = dyadicWeight (s * (2 * b + 1)) := by
  simp only [← dW_add]
  congr 1
  ring

private lemma dW_diss_t_amp (s b e : ℤ) :
    dyadicWeight (s * (b + 1 - e)) * dyadicWeight (e * s) * dyadicWeight (s * (2 * b + 1))
      = dyadicWeight (s * (3 * b + 2)) := by
  simp only [← dW_add]
  congr 1
  ring

private lemma dW_diss_v (s b e k : ℤ) :
    dyadicWeight (s * (b + 1 - e)) * dyadicWeight (e * k) * dyadicWeight (s * b)
      = dyadicWeight (s * (2 * b + 1)) * dyadicWeight (e * (k - s)) := by
  have h : e * k = e * (k - s) + e * s := by ring
  rw [h, dW_add]
  rw [show dyadicWeight (s * (b + 1 - e)) * (dyadicWeight (e * (k - s)) * dyadicWeight (e * s))
            * dyadicWeight (s * b)
        = dyadicWeight (e * (k - s))
            * (dyadicWeight (s * (b + 1 - e)) * dyadicWeight (e * s)
                * dyadicWeight (s * b)) by ring]
  rw [dW_diss_v_amp]
  ring

private lemma dW_diss_t (s b e k : ℤ) :
    dyadicWeight (s * (b + 1 - e)) * dyadicWeight (e * k) * dyadicWeight (s * (2 * b + 1))
      = dyadicWeight (s * (3 * b + 2)) * dyadicWeight (e * (k - s)) := by
  have h : e * k = e * (k - s) + e * s := by ring
  rw [h, dW_add]
  rw [show dyadicWeight (s * (b + 1 - e)) * (dyadicWeight (e * (k - s)) * dyadicWeight (e * s))
            * dyadicWeight (s * (2 * b + 1))
        = dyadicWeight (e * (k - s))
            * (dyadicWeight (s * (b + 1 - e)) * dyadicWeight (e * s)
                * dyadicWeight (s * (2 * b + 1))) by ring]
  rw [dW_diss_t_amp]
  ring

private lemma transferU_scale (s b : ℤ) (A B : ℝ) (u : ℤ → ℝ) (k : ℤ) :
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
  rw [hfac, dW_chain_v]
  simp only [boussinesqTransferU]
  ring

private lemma transferTheta_scale (s b : ℤ) (At Bt : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    boussinesqTransferTheta At Bt (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight (s * (3 * b + 2))
          * boussinesqTransferTheta At Bt u θ (k - s) := by
  have h1 : k - 1 - s = (k - s) - 1 := by ring
  have h2 : k + 1 - s = (k - s) + 1 := by ring
  have hfac : boussinesqTransferTheta At Bt (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight k * (dyadicWeight (s * b) * dyadicWeight (s * (2 * b + 1)))
          * (At * (u ((k - s) - 1) * θ ((k - s) - 1) - 2 * u (k - s) * θ ((k - s) + 1))
              + Bt * (u (k - s) * θ ((k - s) - 1)
                  - 2 * u ((k - s) + 1) * θ ((k - s) + 1))) := by
    simp only [boussinesqTransferTheta, scaleVelocity, scaleTemperature, h1, h2]
    ring
  rw [hfac, dW_chain_t]
  simp only [boussinesqTransferTheta]
  ring

private lemma diss_v_scale_degreeE (s b e : ℤ) (ν : ℝ) (u : ℤ → ℝ) (k : ℤ) :
    ν * dyadicWeight (s * (b + 1 - e)) * dyadicWeight (e * k) * scaleVelocity s b u k
      = dyadicWeight (s * (2 * b + 1)) * (ν * dyadicWeight (e * (k - s)) * u (k - s)) := by
  simp only [scaleVelocity]
  rw [show ν * dyadicWeight (s * (b + 1 - e)) * dyadicWeight (e * k)
            * (dyadicWeight (s * b) * u (k - s))
        = ν * (dyadicWeight (s * (b + 1 - e)) * dyadicWeight (e * k)
              * dyadicWeight (s * b)) * u (k - s) by ring]
  rw [dW_diss_v]
  ring

private lemma diss_t_scale_degreeE (s b e : ℤ) (μ : ℝ) (θ : ℤ → ℝ) (k : ℤ) :
    μ * dyadicWeight (s * (b + 1 - e)) * dyadicWeight (e * k) * scaleTemperature s b θ k
      = dyadicWeight (s * (3 * b + 2)) * (μ * dyadicWeight (e * (k - s)) * θ (k - s)) := by
  simp only [scaleTemperature]
  rw [show μ * dyadicWeight (s * (b + 1 - e)) * dyadicWeight (e * k)
            * (dyadicWeight (s * (2 * b + 1)) * θ (k - s))
        = μ * (dyadicWeight (s * (b + 1 - e)) * dyadicWeight (e * k)
              * dyadicWeight (s * (2 * b + 1))) * θ (k - s) by ring]
  rw [dW_diss_t]
  ring

/-- **Scaling covariance, velocity component, degree `e`.**  Homogeneous of degree `2b+1` and the
viscosity rescales by `λ^{b+1−e}`.  At `e = 2` this is `ν ↦ ν · λ^{b−1}`. -/
theorem velocityRHSDegreeE_scaling_covariant (s b : ℤ) (ν κ A B : ℝ) (e : ℤ)
    (u θ : ℤ → ℝ) (k : ℤ) :
    velocityRHSDegreeE (ν * dyadicWeight (s * (b + 1 - e))) κ A B e
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight (s * (2 * b + 1)) * velocityRHSDegreeE ν κ A B e u θ (k - s) := by
  simp only [velocityRHSDegreeE]
  rw [transferU_scale]
  have hbuoy : κ * scaleTemperature s b θ k
      = dyadicWeight (s * (2 * b + 1)) * (κ * θ (k - s)) := by
    simp only [scaleTemperature]
    ring
  rw [hbuoy, diss_v_scale_degreeE]
  ring

/-- **Scaling covariance, temperature component, degree `e`.**  Homogeneous of degree `3b+2` and
the thermal diffusivity rescales by `λ^{b+1−e}`.  At `e = 2` this is `μ ↦ μ · λ^{b−1}`. -/
theorem temperatureRHSDegreeE_scaling_covariant (s b : ℤ) (μ At Bt : ℝ) (e : ℤ)
    (u θ : ℤ → ℝ) (k : ℤ) :
    temperatureRHSDegreeE (μ * dyadicWeight (s * (b + 1 - e))) At Bt e
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight (s * (3 * b + 2)) * temperatureRHSDegreeE μ At Bt e u θ (k - s) := by
  simp only [temperatureRHSDegreeE]
  rw [transferTheta_scale, diss_t_scale_degreeE]
  ring

/-- **Scaling covariance of the full model at degree `e`.** -/
theorem boussinesqRHSDegreeE_scaling_covariant (s b : ℤ) (ν μ κ A B At Bt : ℝ) (e : ℤ)
    (u θ : ℤ → ℝ) (k : ℤ) :
    boussinesqRHSDegreeE (ν * dyadicWeight (s * (b + 1 - e)))
        (μ * dyadicWeight (s * (b + 1 - e))) κ A B At Bt e
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = (dyadicWeight (s * (2 * b + 1))
            * (boussinesqRHSDegreeE ν μ κ A B At Bt e u θ (k - s)).1,
         dyadicWeight (s * (3 * b + 2))
            * (boussinesqRHSDegreeE ν μ κ A B At Bt e u θ (k - s)).2) := by
  simp only [boussinesqRHSDegreeE]
  exact Prod.ext
    (velocityRHSDegreeE_scaling_covariant s b ν κ A B e u θ k)
    (temperatureRHSDegreeE_scaling_covariant s b μ At Bt e u θ k)

/-! ### The general-degree truncated solution predicates -/

/-- **Unforced truncated solution of the degree-`e` model.** The equation is imposed only on the
retained shells `0 ≤ k < N`; see `Cascade/NoBlowup.lean` for why imposing it on all of `ℤ` is
inconsistent with the boundary value `u t N = 0`. -/
def IsUnforcedTruncatedSolutionE (ν μ κ : ℝ) (e : ℤ) (N : ℕ) (u θ : ℝ → ℤ → ℝ) : Prop :=
  (∀ t k, 0 ≤ k → k < (N : ℤ) →
    HasDerivAt (fun s => u s k) (velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) k) t) ∧
  (∀ t k, 0 ≤ k → k < (N : ℤ) →
    HasDerivAt (fun s => θ s k) (temperatureRHSDegreeE μ 1 1 e (u t) (θ t) k) t) ∧
  (∀ t, u t (-1) = 0 ∧ u t (N : ℤ) = 0 ∧ θ t (-1) = 0 ∧ θ t (N : ℤ) = 0)

/-- **Forced truncated solution of the degree-`e` model.** Equations on `0 ≤ k < N` only. -/
def IsForcedTruncatedSolutionE (ν μ κ : ℝ) (e : ℤ) (N : ℕ) (f h : ℤ → ℝ)
    (u θ : ℝ → ℤ → ℝ) : Prop :=
  (∀ t k, 0 ≤ k → k < (N : ℤ) → HasDerivAt (fun s => u s k)
    (velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) k + f k) t) ∧
  (∀ t k, 0 ≤ k → k < (N : ℤ) → HasDerivAt (fun s => θ s k)
    (temperatureRHSDegreeE μ 1 1 e (u t) (θ t) k + h k) t) ∧
  (∀ t, u t (-1) = 0 ∧ u t (N : ℤ) = 0 ∧ θ t (-1) = 0 ∧ θ t (N : ℤ) = 0)

/-- At degree `2` the new unforced predicate is the library predicate. -/
theorem isUnforcedTruncatedSolutionE_two_iff (ν μ κ : ℝ) (N : ℕ) (u θ : ℝ → ℤ → ℝ) :
    IsUnforcedTruncatedSolutionE ν μ κ 2 N u θ ↔ IsUnforcedTruncatedSolution ν μ κ N u θ := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun t k hk0 hkN => ?_, fun t k hk0 hkN => ?_, h3⟩
    · have hh := h1 t k hk0 hkN
      rwa [show velocityRHSDegreeE ν κ 1 0 2 (u t) (θ t) k
          = dyadicVelocityRHS ν κ (u t) (θ t) k by
        rw [velocityRHSDegreeE, dyadicVelocityRHS, generalVelocityRHS]] at hh
    · have hh := h2 t k hk0 hkN
      rwa [show temperatureRHSDegreeE μ 1 1 2 (u t) (θ t) k
          = dyadicTemperatureRHS μ (u t) (θ t) k by
        rw [temperatureRHSDegreeE, dyadicTemperatureRHS, generalTemperatureRHS]] at hh
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun t k hk0 hkN => ?_, fun t k hk0 hkN => ?_, h3⟩
    · have hh := h1 t k hk0 hkN
      rwa [show velocityRHSDegreeE ν κ 1 0 2 (u t) (θ t) k
          = dyadicVelocityRHS ν κ (u t) (θ t) k by
        rw [velocityRHSDegreeE, dyadicVelocityRHS, generalVelocityRHS]]
    · have hh := h2 t k hk0 hkN
      rwa [show temperatureRHSDegreeE μ 1 1 2 (u t) (θ t) k
          = dyadicTemperatureRHS μ (u t) (θ t) k by
        rw [temperatureRHSDegreeE, dyadicTemperatureRHS, generalTemperatureRHS]]

/-- The zero state is an equilibrium of the degree-`e` unforced model. -/
theorem zero_is_unforcedTruncatedSolutionE (ν μ κ : ℝ) (e : ℤ) (N : ℕ) :
    IsUnforcedTruncatedSolutionE ν μ κ e N (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t k _ _
    have h0 : velocityRHSDegreeE ν κ 1 0 e (fun _ : ℤ => (0 : ℝ)) (fun _ : ℤ => (0 : ℝ)) k
        = 0 := by
      simp [velocityRHSDegreeE, boussinesqTransferU, dyadicWeight]
    rw [h0]
    exact hasDerivAt_const t 0
  · intro t k _ _
    have h0 : temperatureRHSDegreeE μ 1 1 e (fun _ : ℤ => (0 : ℝ)) (fun _ : ℤ => (0 : ℝ)) k
        = 0 := by
      simp [temperatureRHSDegreeE, boussinesqTransferTheta, dyadicWeight]
    rw [h0]
    exact hasDerivAt_const t 0
  · intro t
    exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## 2. The weighted quantities and the sharp `e ≥ 2` domination -/

/-- The general-degree enstrophy dissipation `D_e = Σ_{k<N} 2^{(2+e)k} u_k²`. -/
def enstrophyDissipation (e : ℤ) (u : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, dyadicWeight ((2 + e) * (k : ℤ)) * (u (k : ℤ)) ^ 2

/-- The **backplate weight** `W_e = Σ_{k<N} 2^{(2−e)k} u_k²`. -/
def weightedEnstrophy (e : ℤ) (u : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, dyadicWeight ((2 - e) * (k : ℤ)) * (u (k : ℤ)) ^ 2

/-- The **base energy** `Σ_{k<N} u_k²` (the library's `velocityEnergy`). -/
def enstrophyEnergy (u : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (u (k : ℤ)) ^ 2

/-- `D_e ≥ 0`. -/
theorem enstrophyDissipation_nonneg (e : ℤ) (u : ℤ → ℝ) (N : ℕ) :
    0 ≤ enstrophyDissipation e u N := by
  rw [enstrophyDissipation]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (dyadicWeight_nonneg _) (sq_nonneg _)

/-- `E = velocityEnergy`. -/
theorem enstrophyEnergy_eq_velocityEnergy (u : ℤ → ℝ) (N : ℕ) :
    enstrophyEnergy u N = velocityEnergy u N := rfl

/-- `D_e` at `e = 2` is the library's `∑ 16^k u_k²`. -/
theorem enstrophyDissipation_two (u : ℤ → ℝ) (N : ℕ) :
    enstrophyDissipation 2 u N
      = ∑ k ∈ Finset.range N, dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2 := by
  rw [enstrophyDissipation]
  apply Finset.sum_congr rfl
  intro k _
  have h2 : (2 + (2:ℤ)) * (k : ℤ) = 4 * (k : ℤ) := by ring
  rw [h2]

/-- For `e ≥ 2` the retained weight dominates the degree-`2` weight. -/
theorem one_le_dyadicWeight_of_two_le (e : ℤ) (he : 2 ≤ e) (k : ℕ) :
    (1:ℝ) ≤ dyadicWeight ((e - 2) * (k : ℤ)) := by
  rw [dyadicWeight]
  exact one_le_zpow₀ (by norm_num : (1:ℝ) ≤ 2) (by positivity)

/-- **`D_e ≥ D_2` for `e ≥ 2`**: `2^{(2+e)k} = 2^{4k}·2^{(e−2)k}` and `2^{(e−2)k} ≥ 1`. -/
theorem enstrophyDissipation_two_le (e : ℤ) (he : 2 ≤ e) (u : ℤ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2)
      ≤ enstrophyDissipation e u N := by
  rw [enstrophyDissipation]
  apply Finset.sum_le_sum
  intro k _
  have hfac : dyadicWeight ((2 + e) * (k:ℤ))
      = dyadicWeight (4 * (k:ℤ)) * dyadicWeight ((e - 2) * (k:ℤ)) := by
    rw [← dW_add]
    congr 1
    ring
  rw [hfac]
  have h1 : (1:ℝ) ≤ dyadicWeight ((e - 2) * (k:ℤ)) :=
    one_le_dyadicWeight_of_two_le e he k
  have hsq : (0:ℝ) ≤ (u (k:ℤ)) ^ 2 := sq_nonneg _
  have hw4 : (0:ℝ) ≤ dyadicWeight (4 * (k:ℤ)) := dyadicWeight_nonneg _
  calc dyadicWeight (4 * (k:ℤ)) * (u (k:ℤ)) ^ 2
      = dyadicWeight (4 * (k:ℤ)) * (u (k:ℤ)) ^ 2 * 1 := by ring
    _ ≤ dyadicWeight (4 * (k:ℤ)) * (u (k:ℤ)) ^ 2
          * dyadicWeight ((e - 2) * (k:ℤ)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hw4 hsq)
    _ = dyadicWeight (4 * (k:ℤ)) * dyadicWeight ((e - 2) * (k:ℤ))
          * (u (k:ℤ)) ^ 2 := by ring

/-- **The sharp domination at `e ≥ 2`**: `D_e ≥ H²/E`, by `D_e ≥ D_2` and the two-sided
Cauchy–Schwarz `H² ≤ (Σ16^k u_k²)·E` of `Cascade.Enstrophy`. -/
theorem dissipation_ge_of_two_le (e : ℤ) (he : 2 ≤ e) (u : ℤ → ℝ) (N : ℕ)
    (hE : 0 < velocityEnergy u N) :
    (enstrophy u N) ^ 2 / velocityEnergy u N ≤ enstrophyDissipation e u N := by
  have h2 := enstrophy_sq_le_dissipation_mul_energy u N
  have hdiv : (enstrophy u N) ^ 2 / velocityEnergy u N
      ≤ ∑ k ∈ Finset.range N, dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2 := by
    rw [div_le_iff₀ hE]
    exact h2
  exact hdiv.trans (enstrophyDissipation_two_le e he u N)

/-! ## 3. The degree-`e` enstrophy budget and the no-blowup capstones for `e ≥ 2` -/

/-- **The exact enstrophy pairing at degree `e`.**  Weighting the degree-`e` velocity equation by
`4^k u_k` and summing over the Dirichlet-truncated range,
`Σ 4^k u_k (du_k/dt) = 3 Σ a_{k-1}²a_k + κ Σ 4^k u_k θ_k − ν D_e`. -/
theorem enstrophy_pairing_degreeE (ν κ : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (N : ℕ)
    (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0) :
    (∑ k ∈ Finset.range N,
        dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * velocityRHSDegreeE ν κ 1 0 e u θ (k : ℤ))
      = 3 * (∑ k ∈ Finset.range N, (vorticity u ((k : ℤ) - 1)) ^ 2 * vorticity u (k : ℤ))
        + κ * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ))
        - ν * enstrophyDissipation e u N := by
  have hsplit : ∀ k ∈ Finset.range N,
      dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * velocityRHSDegreeE ν κ 1 0 e u θ (k : ℤ)
        = dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * boussinesqTransferU 1 0 u (k : ℤ)
          + κ * (dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ))
          - ν * (dyadicWeight ((2 + e) * (k : ℤ)) * (u (k : ℤ)) ^ 2) := by
    intro k _
    have h4 : dyadicWeight ((2 + e) * (k : ℤ))
        = dyadicWeight (2 * (k : ℤ)) * dyadicWeight (e * (k : ℤ)) := by
      rw [← dW_add]
      congr 1
      ring
    simp only [velocityRHSDegreeE]
    rw [h4]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hκ : (∑ k ∈ Finset.range N,
        κ * (dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ)))
      = κ * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ)) := by
    rw [Finset.mul_sum]
  have hν : (∑ k ∈ Finset.range N,
        ν * (dyadicWeight ((2 + e) * (k : ℤ)) * (u (k : ℤ)) ^ 2))
      = ν * enstrophyDissipation e u N := by
    rw [enstrophyDissipation, Finset.mul_sum]
  rw [hκ, hν, sum_transfer_enstrophy u N huBot huTop]

/-- **The sign-free degree-`e` pointwise enstrophy pairing bound.**  For any real `κ` and
`E = velocityEnergy u N > 0`, `Σ 4^k u_k (du_k/dt) ≤ 3 H √H + |κ| √H √T − ν D_e`. -/
theorem enstrophy_pairing_le_degreeE (ν κ : ℝ) (hν : 0 ≤ ν) (e : ℤ) (u θ : ℤ → ℝ) (N : ℕ)
    (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0) (hE : 0 < velocityEnergy u N) :
    (∑ k ∈ Finset.range N,
        dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * velocityRHSDegreeE ν κ 1 0 e u θ (k : ℤ))
      ≤ 3 * (enstrophy u N * Real.sqrt (enstrophy u N))
        + |κ| * (Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N))
        - ν * enstrophyDissipation e u N := by
  rw [enstrophy_pairing_degreeE ν κ e u θ N huBot huTop]
  have h1 := sum_vorticity_cubic_le u N huBot
  have h4 := buoyancy_enstrophy_le_abs κ u θ N
  have h1' := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3)
  linarith [h1', h4]

/-- **The sign-free degree-`e` enstrophy rate bound** (`e ≥ 2`).  With `H = enstrophy u N`,
`T = tempEnstrophy θ N` and an energy ceiling `E_max ≥ E`,
`2 Σ 4^k u_k (du_k/dt) ≤ 6 H √H + |κ| (H + T) − 2 ν D_e`, so in particular
`− 2 ν H²/E_max` by `dissipation_ge_of_two_le`. -/
theorem enstrophy_rate_le_of_solution_degreeE (ν μ κ E_max : ℝ) (hν : 0 < ν) (hEpos : 0 < E_max)
    (e : ℤ) (he : 2 ≤ e) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ) {t : ℝ}
    (hEmax : velocityEnergy (u t) N ≤ E_max) :
    2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
        * velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ))
      ≤ 6 * (enstrophy (u t) N * Real.sqrt (enstrophy (u t) N))
        + |κ| * (enstrophy (u t) N + tempEnstrophy (θ t) N)
        - 2 * ν * (enstrophy (u t) N) ^ 2 / E_max := by
  by_cases hE0 : velocityEnergy (u t) N = 0
  · have hsum0 : (∑ k ∈ Finset.range N, (u t (k : ℤ)) ^ 2) = 0 := by
      simpa [velocityEnergy] using hE0
    have hz : ∀ k ∈ Finset.range N, (u t (k : ℤ)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.range N)
        (f := fun j : ℕ => (u t (j : ℤ)) ^ 2)
        (fun j _ => sq_nonneg (u t (j : ℤ)))).mp hsum0
    have hu0 : ∀ k ∈ Finset.range N, u t (k : ℤ) = 0 := fun k hk =>
      sq_eq_zero_iff.mp (hz k hk)
    have hL : (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
        * velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ)) = 0 := by
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
    rw [hL, hH]
    have hrhs : 6 * ((0 : ℝ) * Real.sqrt 0) + |κ| * (0 + tempEnstrophy (θ t) N)
        - 2 * ν * (0 : ℝ) ^ 2 / E_max = |κ| * tempEnstrophy (θ t) N := by
      rw [Real.sqrt_zero]
      ring
    rw [hrhs]
    simpa using mul_nonneg (abs_nonneg κ) (tempEnstrophy_nonneg (θ t) N)
  · have hEpos' : 0 < velocityEnergy (u t) N :=
      lt_of_le_of_ne (velocityEnergy_nonneg (u t) N) (Ne.symm hE0)
    have hpair := enstrophy_pairing_le_degreeE ν κ hν.le e (u t) (θ t) N
      (h.2.2 t).1 (h.2.2 t).2.1 hEpos'
    have h2 := mul_le_mul_of_nonneg_left hpair (by norm_num : (0 : ℝ) ≤ 2)
    have hdiv : (enstrophy (u t) N) ^ 2 / E_max
        ≤ enstrophyDissipation e (u t) N := by
      have h1 : (enstrophy (u t) N) ^ 2 / E_max
          ≤ (enstrophy (u t) N) ^ 2 / velocityEnergy (u t) N :=
        div_le_div_of_nonneg_left (sq_nonneg _) hEpos' hEmax
      have h2' : (enstrophy (u t) N) ^ 2 / velocityEnergy (u t) N
          ≤ enstrophyDissipation e (u t) N :=
        dissipation_ge_of_two_le e he (u t) N hEpos'
      exact h1.trans h2'
    have hνdiv : 2 * ν * (enstrophy (u t) N) ^ 2 / E_max
        ≤ 2 * ν * enstrophyDissipation e (u t) N := by
      have h2ν : 0 ≤ 2 * ν := by linarith
      calc 2 * ν * (enstrophy (u t) N) ^ 2 / E_max
          = (2 * ν) * ((enstrophy (u t) N) ^ 2 / E_max) := by ring
        _ ≤ (2 * ν) * enstrophyDissipation e (u t) N := mul_le_mul_of_nonneg_left hdiv h2ν
    have hHnn : 0 ≤ enstrophy (u t) N := enstrophy_nonneg _ _
    have hTEnn : 0 ≤ tempEnstrophy (θ t) N := tempEnstrophy_nonneg _ _
    have hamgm : 2 * (Real.sqrt (enstrophy (u t) N) * Real.sqrt (tempEnstrophy (θ t) N))
        ≤ enstrophy (u t) N + tempEnstrophy (θ t) N := by
      have h1 : (Real.sqrt (enstrophy (u t) N) - Real.sqrt (tempEnstrophy (θ t) N)) ^ 2
          = enstrophy (u t) N + tempEnstrophy (θ t) N
            - 2 * (Real.sqrt (enstrophy (u t) N) * Real.sqrt (tempEnstrophy (θ t) N)) := by
        rw [sub_sq, Real.sq_sqrt hHnn, Real.sq_sqrt hTEnn]
        ring
      nlinarith [sq_nonneg (Real.sqrt (enstrophy (u t) N)
        - Real.sqrt (tempEnstrophy (θ t) N))]
    have hκamgm : |κ| * (2 * (Real.sqrt (enstrophy (u t) N)
          * Real.sqrt (tempEnstrophy (θ t) N)))
        ≤ |κ| * (enstrophy (u t) N + tempEnstrophy (θ t) N) :=
      mul_le_mul_of_nonneg_left hamgm (abs_nonneg κ)
    have hstep : 2 * (3 * (enstrophy (u t) N * Real.sqrt (enstrophy (u t) N))
          + |κ| * (Real.sqrt (enstrophy (u t) N) * Real.sqrt (tempEnstrophy (θ t) N))
          - ν * enstrophyDissipation e (u t) N)
        ≤ 6 * (enstrophy (u t) N * Real.sqrt (enstrophy (u t) N))
          + |κ| * (enstrophy (u t) N + tempEnstrophy (θ t) N)
          - 2 * ν * (enstrophy (u t) N) ^ 2 / E_max := by
      linarith [hκamgm, hνdiv]
    exact h2.trans hstep

/-- Temperature dissipation at degree `e`: `T_e = Σ_{k<N} 2^{ek} θ_k²`. -/
def tempEnstrophyE (e : ℤ) (θ : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, dyadicWeight (e * (k : ℤ)) * (θ (k : ℤ)) ^ 2

/-- `T_e ≥ 0`. -/
theorem tempEnstrophyE_nonneg (e : ℤ) (θ : ℤ → ℝ) (N : ℕ) : 0 ≤ tempEnstrophyE e θ N := by
  rw [tempEnstrophyE]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (dyadicWeight_nonneg _) (sq_nonneg _)

/-- Continuity of `t ↦ T_e(θ t)`. -/
theorem tempEnstrophyE_continuous (ν μ κ : ℝ) (e : ℤ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ) :
    Continuous fun t => tempEnstrophyE e (θ t) N := by
  unfold tempEnstrophyE
  refine continuous_finsetSum _ fun k hk => ?_
  have hdiff : Differentiable ℝ (fun t : ℝ => (θ t (k:ℤ)) ^ 2) := fun t =>
    ((h.2.1 t (k:ℤ) (Int.natCast_nonneg k)
      (by exact_mod_cast (Finset.mem_range.mp hk))).differentiableAt).pow 2
  exact continuous_const.mul hdiff.continuous

/-- Continuity of `t ↦ T(θ t)` (the library temperature enstrophy, weight `2^{2k}`). -/
theorem tempEnstrophy_continuous_degreeE (ν μ κ : ℝ) (e : ℤ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ) :
    Continuous fun t => tempEnstrophy (θ t) N := by
  unfold tempEnstrophy
  refine continuous_finsetSum _ fun k hk => ?_
  have hdiff : Differentiable ℝ (fun t : ℝ => (θ t (k:ℤ)) ^ 2) := fun t =>
    ((h.2.1 t (k:ℤ) (Int.natCast_nonneg k)
      (by exact_mod_cast (Finset.mem_range.mp hk))).differentiableAt).pow 2
  exact continuous_const.mul hdiff.continuous

/-- Continuity of `t ↦ S(θ t)` (`entropy`, weight `1`). -/
theorem entropy_continuous_degreeE (ν μ κ : ℝ) (e : ℤ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ) :
    Continuous fun t => entropy (θ t) N := by
  unfold entropy
  refine continuous_finsetSum _ fun k hk => ?_
  have hdiff : Differentiable ℝ (fun t : ℝ => (θ t (k:ℤ)) ^ 2) := fun t =>
    ((h.2.1 t (k:ℤ) (Int.natCast_nonneg k)
      (by exact_mod_cast (Finset.mem_range.mp hk))).differentiableAt).pow 2
  exact hdiff.continuous

/-- Continuity of `t ↦ E(u t)` (`velocityEnergy`, weight `1`). -/
theorem velocityEnergy_continuous_degreeE (ν μ κ : ℝ) (e : ℤ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ) :
    Continuous fun t => velocityEnergy (u t) N := by
  unfold velocityEnergy
  refine continuous_finsetSum _ fun k hk => ?_
  have hdiff : Differentiable ℝ (fun t : ℝ => (u t (k:ℤ)) ^ 2) := fun t =>
    ((h.1 t (k:ℤ) (Int.natCast_nonneg k)
      (by exact_mod_cast (Finset.mem_range.mp hk))).differentiableAt).pow 2
  exact hdiff.continuous

/-- Continuity of `t ↦ H(u t)` (`enstrophy`, weight `2^{2k}`). -/
theorem enstrophy_continuous_degreeE (ν μ κ : ℝ) (e : ℤ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ) :
    Continuous fun t => enstrophy (u t) N := by
  unfold enstrophy
  refine continuous_finsetSum _ fun k hk => ?_
  have hdiff : Differentiable ℝ (fun t : ℝ => (u t (k:ℤ)) ^ 2) := fun t =>
    ((h.1 t (k:ℤ) (Int.natCast_nonneg k)
      (by exact_mod_cast (Finset.mem_range.mp hk))).differentiableAt).pow 2
  exact continuous_const.mul hdiff.continuous

/-- **The time derivative of the enstrophy along a degree-`e` solution.** -/
theorem enstrophy_hasDerivAt_degreeE (ν μ κ : ℝ) (e : ℤ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ) (t : ℝ) :
    HasDerivAt (fun s => enstrophy (u s) N)
      (2 * ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
        * velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ)) t := by
  have hterm : ∀ k ∈ Finset.range N,
      HasDerivAt (fun s : ℝ => dyadicWeight (2 * (k : ℤ)) * (u s (k : ℤ)) ^ 2)
        (dyadicWeight (2 * (k : ℤ))
          * (2 * u t (k : ℤ) * velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ))) t := by
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
      * (2 * u t (k : ℤ) * velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ))) hterm
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
          * (2 * u t (k : ℤ) * velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ)))
      = 2 * ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
          * velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [heq] at hsum
  exact hsum

/-- **The time derivative of the entropy along a degree-`e` solution.** -/
theorem entropy_hasDerivAt_degreeE (ν μ κ : ℝ) (e : ℤ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ) (t : ℝ) :
    HasDerivAt (fun s => entropy (θ s) N)
      (2 * ∑ k ∈ Finset.range N,
        θ t (k : ℤ) * temperatureRHSDegreeE μ 1 1 e (u t) (θ t) (k : ℤ)) t := by
  have hsum : HasDerivAt (∑ k ∈ Finset.range N, fun s : ℝ => (θ s (k : ℤ)) ^ 2)
      (∑ k ∈ Finset.range N,
        2 * θ t (k : ℤ) * temperatureRHSDegreeE μ 1 1 e (u t) (θ t) (k : ℤ)) t :=
    HasDerivAt.sum (u := Finset.range N)
      (A := fun k s => (θ s (k : ℤ)) ^ 2)
      (A' := fun k => 2 * θ t (k : ℤ) * temperatureRHSDegreeE μ 1 1 e (u t) (θ t) (k : ℤ))
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
  have hfun2 : (fun s : ℝ => ∑ k ∈ Finset.range N, (θ s (k : ℤ)) ^ 2)
      = fun s => entropy (θ s) N := by
    funext s
    rw [entropy]
  rw [hfun2] at hsum
  have heq : (∑ k ∈ Finset.range N,
        2 * θ t (k : ℤ) * temperatureRHSDegreeE μ 1 1 e (u t) (θ t) (k : ℤ))
      = 2 * ∑ k ∈ Finset.range N,
          θ t (k : ℤ) * temperatureRHSDegreeE μ 1 1 e (u t) (θ t) (k : ℤ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [heq] at hsum
  exact hsum

/-- **The temperature pairing at degree `e`**: `Σ θ_k (dθ_k/dt) = −μ T_e` under Dirichlet. -/
theorem temperature_pairing_degreeE (μ : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (N : ℕ)
    (hθBot : θ (-1) = 0) (hθTop : θ (N : ℤ) = 0) :
    (∑ k ∈ Finset.range N, θ (k : ℤ) * temperatureRHSDegreeE μ 1 1 e u θ (k : ℤ))
      = - μ * tempEnstrophyE e θ N := by
  have hsplit : ∀ k ∈ Finset.range N,
      θ (k : ℤ) * temperatureRHSDegreeE μ 1 1 e u θ (k : ℤ)
        = θ (k : ℤ) * boussinesqTransferTheta 1 1 u θ (k : ℤ)
          - μ * (dyadicWeight (e * (k : ℤ)) * (θ (k : ℤ)) ^ 2) := by
    intro k _
    simp only [temperatureRHSDegreeE]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
  have htel : (∑ k ∈ Finset.range N, θ (k : ℤ) * boussinesqTransferTheta 1 1 u θ (k : ℤ))
      = 0 := by
    have hpt : ∀ k ∈ Finset.range N, θ (k : ℤ) * boussinesqTransferTheta 1 1 u θ (k : ℤ)
        = (fun m : ℕ => temperatureFlux 1 1 u θ (m : ℤ)) k
          - (fun m : ℕ => temperatureFlux 1 1 u θ (m : ℤ)) (k + 1) := by
      intro k _
      rw [temperature_pairing_eq_flux]
      push_cast
      ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_range_sub']
    have h0 : temperatureFlux 1 1 u θ (((0 : ℕ) : ℤ)) = 0 := by
      simp [temperatureFlux, hθBot]
    have hN : temperatureFlux 1 1 u θ (N : ℤ) = 0 := by
      simp [temperatureFlux, hθTop]
    rw [h0, hN]
    ring
  have hmu : (∑ k ∈ Finset.range N, μ * (dyadicWeight (e * (k : ℤ)) * (θ (k : ℤ)) ^ 2))
      = μ * tempEnstrophyE e θ N := by
    rw [tempEnstrophyE, Finset.mul_sum]
  rw [htel, hmu]
  ring

/-- **The Lyapunov function derivative along a degree-`e` solution.** -/
theorem enstrophyLyapunov_hasDerivAt_degreeE (ν μ κ : ℝ) (e : ℤ) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ) (t : ℝ) :
    HasDerivAt (fun s => enstrophyLyapunov ν μ κ N (u s) (θ s))
      (2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
          * velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ))
        + (κ / (2 * μ)) * (2 * ∑ k ∈ Finset.range N,
            θ t (k : ℤ) * temperatureRHSDegreeE μ 1 1 e (u t) (θ t) (k : ℤ))) t := by
  have h1 := enstrophy_hasDerivAt_degreeE ν μ κ e N u θ h t
  have h2 := (entropy_hasDerivAt_degreeE ν μ κ e N u θ h t).const_mul (κ / (2 * μ))
  have hfun : (fun s => enstrophyLyapunov ν μ κ N (u s) (θ s))
      = (fun s => enstrophy (u s) N) + (fun s => (κ / (2 * μ)) * entropy (θ s) N) := by
    funext s
    simp [enstrophyLyapunov]
  rw [hfun]
  exact h1.add h2

/-- **The sign-free degree-`e` Lyapunov derivative bound** (`e ≥ 2`):
`Ψ' ≤ enstrophyYoungConst ν κ E_max + |κ|(T_max + T_e^max)`. -/
theorem enstrophyLyapunov_deriv_le_degreeE (ν μ κ E_max T_max Te_max : ℝ) (hν : 0 < ν)
    (hμ : 0 < μ) (hEpos : 0 < E_max) (e : ℤ) (he : 2 ≤ e) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ) {t : ℝ}
    (hEmax : velocityEnergy (u t) N ≤ E_max) (hTmax : tempEnstrophy (θ t) N ≤ T_max)
    (hTemax : tempEnstrophyE e (θ t) N ≤ Te_max) :
    2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
        * velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ))
      + (κ / (2 * μ)) * (2 * ∑ k ∈ Finset.range N,
          θ t (k : ℤ) * temperatureRHSDegreeE μ 1 1 e (u t) (θ t) (k : ℤ))
      ≤ enstrophyYoungConst ν κ E_max + |κ| * (T_max + Te_max) := by
  have hγ : 0 < ν / E_max := div_pos hν hEpos
  have hrate := enstrophy_rate_le_of_solution_degreeE ν μ κ E_max hν hEpos e he N u θ h hEmax
  have htemp := temperature_pairing_degreeE μ e (u t) (θ t) N (h.2.2 t).2.2.1 (h.2.2 t).2.2.2
  have htemp' : (κ / (2 * μ)) * (2 * ∑ k ∈ Finset.range N,
        θ t (k : ℤ) * temperatureRHSDegreeE μ 1 1 e (u t) (θ t) (k : ℤ))
      = - κ * tempEnstrophyE e (θ t) N := by
    rw [htemp]
    field_simp
  rw [htemp']
  have hHnn : 0 ≤ enstrophy (u t) N := enstrophy_nonneg _ _
  have hs2 : (Real.sqrt (enstrophy (u t) N)) ^ 2 = enstrophy (u t) N := Real.sq_sqrt hHnn
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
  have hy2 : |κ| * enstrophy (u t) N
      ≤ (ν / E_max) * (enstrophy (u t) N) ^ 2 + |κ| ^ 2 / (4 * (ν / E_max)) :=
    young_linear_le (γ := ν / E_max) hγ
  have hTe : |κ| * tempEnstrophy (θ t) N - κ * tempEnstrophyE e (θ t) N
      ≤ |κ| * (T_max + Te_max) := by
    have h1 : |κ| * tempEnstrophy (θ t) N ≤ |κ| * T_max :=
      mul_le_mul_of_nonneg_left hTmax (abs_nonneg κ)
    have h2 : -κ * tempEnstrophyE e (θ t) N ≤ |κ| * Te_max := by
      calc -κ * tempEnstrophyE e (θ t) N
          ≤ |κ| * tempEnstrophyE e (θ t) N :=
            mul_le_mul_of_nonneg_right (neg_le_abs κ) (tempEnstrophyE_nonneg e (θ t) N)
        _ ≤ |κ| * Te_max := mul_le_mul_of_nonneg_left hTemax (abs_nonneg κ)
    linarith
  have hsqabs : |κ| ^ 2 = κ ^ 2 := sq_abs κ
  simp only [enstrophyYoungConst]
  rw [hsqabs] at hy2
  simp only [div_eq_mul_inv] at hrate hy1 hy2 ⊢
  linarith [hrate, hy1, hy2, hTe]

/-- **No finite-time enstrophy blowup at degree `e ≥ 2`** (unforced, no sign hypothesis on `κ`).
Along any unforced truncated degree-`e` solution with Dirichlet ends, `H = Σ_{k<N} 4^k u_k²` is
bounded on every compact `[0,T]`.

The energy, temperature, temperature-dissipation and entropy ceilings are maxima on the compact
interval (continuity), so the proof needs no port of the energy budget; the Grönwall engine is then
applied to `Ψ = H + (κ/2μ)S` with constant right-hand side. -/
theorem truncated_unforced_enstrophy_bounded_degreeE (ν μ κ : ℝ) (hν : 0 < ν) (hμ : 0 < μ)
    (e : ℤ) (he : 2 ≤ e) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolutionE ν μ κ e N u θ) (T : ℝ) (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun t => enstrophy (u t) N) (Set.Icc 0 T)) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, enstrophy (u t) N ≤ C := by
  have hK := isCompact_Icc (a := (0:ℝ)) (b := T)
  obtain ⟨E₀, hE₀⟩ := hK.bddAbove_image
    (velocityEnergy_continuous_degreeE ν μ κ e N u θ h).continuousOn
  obtain ⟨T₀, hT₀⟩ := hK.bddAbove_image
    (tempEnstrophy_continuous_degreeE ν μ κ e N u θ h).continuousOn
  obtain ⟨Te₀, hTe₀⟩ := hK.bddAbove_image
    (tempEnstrophyE_continuous ν μ κ e N u θ h).continuousOn
  obtain ⟨S₀, hS₀⟩ := hK.bddAbove_image
    (entropy_continuous_degreeE ν μ κ e N u θ h).continuousOn
  set E_max : ℝ := max E₀ 1 with hE_max
  set T_max : ℝ := max T₀ 0 with hT_max
  set Te_max : ℝ := max Te₀ 0 with hTe_max
  set S_max : ℝ := max S₀ 0 with hS_max
  have hEpos : 0 < E_max := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hEmax : ∀ t ∈ Set.Icc 0 T, velocityEnergy (u t) N ≤ E_max := fun t ht =>
    (hE₀ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  have hTle : ∀ t ∈ Set.Icc 0 T, tempEnstrophy (θ t) N ≤ T_max := fun t ht =>
    (hT₀ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  have hTele : ∀ t ∈ Set.Icc 0 T, tempEnstrophyE e (θ t) N ≤ Te_max := fun t ht =>
    (hTe₀ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  have hSle : ∀ t ∈ Set.Icc 0 T, entropy (θ t) N ≤ S_max := fun t ht =>
    (hS₀ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  set C₀ : ℝ := enstrophyYoungConst ν κ E_max + |κ| * (T_max + Te_max) with hC₀
  have hC₀nn : 0 ≤ C₀ := by
    rw [hC₀]
    have h1 : 0 ≤ enstrophyYoungConst ν κ E_max := by
      unfold enstrophyYoungConst
      have h3 : 0 ≤ 2187 / (16 * (ν / E_max) ^ 3) :=
        div_nonneg (by norm_num) (by positivity)
      have h4 : 0 ≤ κ ^ 2 / (4 * (ν / E_max)) :=
        div_nonneg (sq_nonneg _) (by positivity)
      linarith
    have h2 : 0 ≤ |κ| * (T_max + Te_max) :=
      mul_nonneg (abs_nonneg κ) (by linarith [le_max_right T₀ 0, le_max_right Te₀ 0])
    linarith
  refine ⟨enstrophyLyapunov ν μ κ N (u 0) (θ 0) + C₀ * T + (|κ| / (2 * μ)) * S_max, ?_⟩
  have hderiv : ∀ s ∈ Set.Ico 0 T,
      HasDerivAt (fun r => enstrophyLyapunov ν μ κ N (u r) (θ r))
        (2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u s (k : ℤ)
            * velocityRHSDegreeE ν κ 1 0 e (u s) (θ s) (k : ℤ))
          + (κ / (2 * μ)) * (2 * ∑ k ∈ Finset.range N,
              θ s (k : ℤ) * temperatureRHSDegreeE μ 1 1 e (u s) (θ s) (k : ℤ))) s :=
    fun s _ => enstrophyLyapunov_hasDerivAt_degreeE ν μ κ e N u θ h s
  have hineq : ∀ s ∈ Set.Ico 0 T,
      (2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u s (k : ℤ)
            * velocityRHSDegreeE ν κ 1 0 e (u s) (θ s) (k : ℤ))
          + (κ / (2 * μ)) * (2 * ∑ k ∈ Finset.range N,
              θ s (k : ℤ) * temperatureRHSDegreeE μ 1 1 e (u s) (θ s) (k : ℤ)))
        ≤ C₀ + 0 * enstrophyLyapunov ν μ κ N (u s) (θ s) := by
    intro s hs
    have hsIcc : s ∈ Set.Icc 0 T := ⟨hs.1, le_of_lt hs.2⟩
    have hb := enstrophyLyapunov_deriv_le_degreeE ν μ κ E_max T_max Te_max hν hμ hEpos e he
      N u θ h (hEmax s hsIcc) (hTle s hsIcc) (hTele s hsIcc)
    simpa [hC₀] using hb
  have hΨcont : ContinuousOn (fun r => enstrophyLyapunov ν μ κ N (u r) (θ r)) (Set.Icc 0 T) :=
    fun s _ => (enstrophyLyapunov_hasDerivAt_degreeE ν μ κ e N u θ h s).continuousAt.continuousWithinAt
  have hbar := le_gronwallBound_of_hasDerivAt
    (f := fun r => enstrophyLyapunov ν μ κ N (u r) (θ r))
    (f' := fun r => 2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u r (k : ℤ)
          * velocityRHSDegreeE ν κ 1 0 e (u r) (θ r) (k : ℤ))
        + (κ / (2 * μ)) * (2 * ∑ k ∈ Finset.range N,
            θ r (k : ℤ) * temperatureRHSDegreeE μ 1 1 e (u r) (θ r) (k : ℤ)))
    hΨcont hderiv hineq
  intro t ht
  have h := hbar t ht
  rw [gronwallBound_K0] at h
  have hCt : C₀ * t ≤ C₀ * T := mul_le_mul_of_nonneg_left ht.2 hC₀nn
  have hHle : enstrophy (u t) N
      ≤ enstrophyLyapunov ν μ κ N (u t) (θ t) + (|κ| / (2 * μ)) * S_max := by
    have hcoef : 0 ≤ |κ| / (2 * μ) := div_nonneg (abs_nonneg κ) (by positivity)
    have hcmp : -(κ / (2 * μ)) ≤ |κ| / (2 * μ) := by
      rw [show -(κ / (2 * μ)) = (-κ) / (2 * μ) by ring]
      exact div_le_div_of_nonneg_right (neg_le_abs κ) (by positivity)
    have h1 : -(κ / (2 * μ)) * entropy (θ t) N ≤ (|κ| / (2 * μ)) * S_max :=
      calc -(κ / (2 * μ)) * entropy (θ t) N
          ≤ (|κ| / (2 * μ)) * entropy (θ t) N :=
            mul_le_mul_of_nonneg_right hcmp (entropy_nonneg _ _)
        _ ≤ (|κ| / (2 * μ)) * S_max := mul_le_mul_of_nonneg_left (hSle t ht) hcoef
    simp only [enstrophyLyapunov]
    linarith
  linarith

/-- Continuity of the forced enstrophy. -/
theorem forcedEnstrophy_continuous_degreeE (ν μ κ : ℝ) (e : ℤ) (N : ℕ) (f hf : ℤ → ℝ)
    (u θ : ℝ → ℤ → ℝ) (hsol : IsForcedTruncatedSolutionE ν μ κ e N f hf u θ) :
    Continuous fun t => enstrophy (u t) N := by
  unfold enstrophy
  refine continuous_finsetSum _ fun k hk => ?_
  have hdiff : Differentiable ℝ (fun t : ℝ => (u t (k:ℤ)) ^ 2) := fun t =>
    ((hsol.1 t (k:ℤ) (Int.natCast_nonneg k)
      (by exact_mod_cast (Finset.mem_range.mp hk))).differentiableAt).pow 2
  exact continuous_const.mul hdiff.continuous

/-- Continuity of the forced temperature enstrophy. -/
theorem forcedTempEnstrophy_continuous_degreeE (ν μ κ : ℝ) (e : ℤ) (N : ℕ) (f hf : ℤ → ℝ)
    (u θ : ℝ → ℤ → ℝ) (hsol : IsForcedTruncatedSolutionE ν μ κ e N f hf u θ) :
    Continuous fun t => tempEnstrophy (θ t) N := by
  unfold tempEnstrophy
  refine continuous_finsetSum _ fun k hk => ?_
  have hdiff : Differentiable ℝ (fun t : ℝ => (θ t (k:ℤ)) ^ 2) := fun t =>
    ((hsol.2.1 t (k:ℤ) (Int.natCast_nonneg k)
      (by exact_mod_cast (Finset.mem_range.mp hk))).differentiableAt).pow 2
  exact continuous_const.mul hdiff.continuous

/-- **The time derivative of the forced enstrophy along a degree-`e` forced solution.** -/
theorem forcedEnstrophy_hasDerivAt_degreeE (ν μ κ : ℝ) (e : ℤ) (N : ℕ) (f hf : ℤ → ℝ)
    (u θ : ℝ → ℤ → ℝ) (hsol : IsForcedTruncatedSolutionE ν μ κ e N f hf u θ) (t : ℝ) :
    HasDerivAt (fun s => enstrophy (u s) N)
      (2 * ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
        * (velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ) + f (k : ℤ))) t := by
  have hterm : ∀ k ∈ Finset.range N,
      HasDerivAt (fun s : ℝ => dyadicWeight (2 * (k : ℤ)) * (u s (k : ℤ)) ^ 2)
        (dyadicWeight (2 * (k : ℤ))
          * (2 * u t (k : ℤ)
            * (velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ) + f (k : ℤ)))) t := by
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
      * (2 * u t (k : ℤ)
        * (velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ) + f (k : ℤ)))) hterm
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
          * (2 * u t (k : ℤ)
            * (velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ) + f (k : ℤ))))
      = 2 * ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
          * (velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ) + f (k : ℤ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [heq] at hsum
  exact hsum

/-- **The sign-free forced degree-`e` enstrophy rate bound** (`e ≥ 2`):
`2 Σ 4^k u_k (du_k/dt) ≤ 6 H √H + |κ| (H+T) + 2 √H √He − 2 ν H²/E_max`. -/
theorem forced_enstrophy_rate_le_degreeE (ν κ E_max : ℝ) (hν : 0 ≤ ν) (hEpos : 0 < E_max)
    (e : ℤ) (he : 2 ≤ e) (N : ℕ) (f : ℤ → ℝ) (u θ : ℤ → ℝ)
    (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0) (hEmax : velocityEnergy u N ≤ E_max) :
    2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)
        * (velocityRHSDegreeE ν κ 1 0 e u θ (k : ℤ) + f (k : ℤ)))
      ≤ 6 * (enstrophy u N * Real.sqrt (enstrophy u N))
        + |κ| * (enstrophy u N + tempEnstrophy θ N)
        + 2 * (Real.sqrt (enstrophy u N) * Real.sqrt (forceEnstrophy f N))
        - 2 * ν * (enstrophy u N) ^ 2 / E_max := by
  by_cases hE0 : velocityEnergy u N = 0
  · have hsum0 : (∑ k ∈ Finset.range N, (u (k : ℤ)) ^ 2) = 0 := by
      simpa [velocityEnergy] using hE0
    have hz : ∀ k ∈ Finset.range N, (u (k : ℤ)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.range N)
        (f := fun j : ℕ => (u (j : ℤ)) ^ 2)
        (fun j _ => sq_nonneg (u (j : ℤ)))).mp hsum0
    have hu0 : ∀ k ∈ Finset.range N, u (k : ℤ) = 0 := fun k hk =>
      sq_eq_zero_iff.mp (hz k hk)
    have hL : (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)
        * (velocityRHSDegreeE ν κ 1 0 e u θ (k : ℤ) + f (k : ℤ))) = 0 := by
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
    have hrhs : 6 * ((0 : ℝ) * Real.sqrt 0) + |κ| * (0 + tempEnstrophy θ N)
        + 2 * (Real.sqrt 0 * Real.sqrt (forceEnstrophy f N)) - 2 * ν * (0 : ℝ) ^ 2 / E_max
        = |κ| * tempEnstrophy θ N := by
      rw [Real.sqrt_zero]
      ring
    rw [hrhs]
    simpa using mul_nonneg (abs_nonneg κ) (tempEnstrophy_nonneg θ N)
  · have hEpos' : 0 < velocityEnergy u N :=
      lt_of_le_of_ne (velocityEnergy_nonneg u N) (Ne.symm hE0)
    have hsplit : (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)
        * (velocityRHSDegreeE ν κ 1 0 e u θ (k : ℤ) + f (k : ℤ)))
        = (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)
            * velocityRHSDegreeE ν κ 1 0 e u θ (k : ℤ))
          + (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * f (k : ℤ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsplit]
    have hpair := enstrophy_pairing_le_degreeE ν κ hν e u θ N huBot huTop hEpos'
    have hwork := force_enstrophy_work_le f u N
    have h2pair := mul_le_mul_of_nonneg_left hpair (by norm_num : (0 : ℝ) ≤ 2)
    have h2work := mul_le_mul_of_nonneg_left hwork (by norm_num : (0 : ℝ) ≤ 2)
    have hdiv : (enstrophy u N) ^ 2 / E_max ≤ enstrophyDissipation e u N := by
      have h1 : (enstrophy u N) ^ 2 / E_max
          ≤ (enstrophy u N) ^ 2 / velocityEnergy u N :=
        div_le_div_of_nonneg_left (sq_nonneg _) hEpos' hEmax
      exact h1.trans (dissipation_ge_of_two_le e he u N hEpos')
    have hνdiv : 2 * ν * (enstrophy u N) ^ 2 / E_max
        ≤ 2 * ν * enstrophyDissipation e u N := by
      have h2ν : 0 ≤ 2 * ν := by linarith
      calc 2 * ν * (enstrophy u N) ^ 2 / E_max
          = (2 * ν) * ((enstrophy u N) ^ 2 / E_max) := by ring
        _ ≤ (2 * ν) * enstrophyDissipation e u N := mul_le_mul_of_nonneg_left hdiv h2ν
    have hHnn : 0 ≤ enstrophy u N := enstrophy_nonneg u N
    have hTEnn : 0 ≤ tempEnstrophy θ N := tempEnstrophy_nonneg θ N
    have hamgm : 2 * (Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N))
        ≤ enstrophy u N + tempEnstrophy θ N := by
      have h := sq_nonneg (Real.sqrt (enstrophy u N) - Real.sqrt (tempEnstrophy θ N))
      rw [sub_sq, Real.sq_sqrt hHnn, Real.sq_sqrt hTEnn] at h
      nlinarith
    have hκamgm : |κ| * (2 * (Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N)))
        ≤ |κ| * (enstrophy u N + tempEnstrophy θ N) :=
      mul_le_mul_of_nonneg_left hamgm (abs_nonneg κ)
    linarith [h2pair, h2work, hκamgm, hνdiv]

/-- Continuity of the forced velocity energy. -/
theorem forcedVelocityEnergy_continuous_degreeE (ν μ κ : ℝ) (e : ℤ) (N : ℕ) (f hf : ℤ → ℝ)
    (u θ : ℝ → ℤ → ℝ) (hsol : IsForcedTruncatedSolutionE ν μ κ e N f hf u θ) :
    Continuous fun t => velocityEnergy (u t) N := by
  unfold velocityEnergy
  refine continuous_finsetSum _ fun k hk => ?_
  have hdiff : Differentiable ℝ (fun t : ℝ => (u t (k:ℤ)) ^ 2) := fun t =>
    ((hsol.1 t (k:ℤ) (Int.natCast_nonneg k)
      (by exact_mod_cast (Finset.mem_range.mp hk))).differentiableAt).pow 2
  exact hdiff.continuous

/-- **No finite-time enstrophy blowup at degree `e ≥ 2`, forced case** (no sign hypothesis on `κ`,
arbitrary force ladders): the enstrophy is bounded on every compact `[0,T]`. -/
theorem forced_truncated_enstrophy_bounded_degreeE (ν μ κ : ℝ) (hν : 0 < ν)
    (e : ℤ) (he : 2 ≤ e) (N : ℕ) (f hf : ℤ → ℝ) (u θ : ℝ → ℤ → ℝ)
    (hsol : IsForcedTruncatedSolutionE ν μ κ e N f hf u θ) (T : ℝ) (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun t => enstrophy (u t) N) (Set.Icc 0 T)) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, enstrophy (u t) N ≤ C := by
  have hK := isCompact_Icc (a := (0:ℝ)) (b := T)
  obtain ⟨E₀, hE₀⟩ := hK.bddAbove_image
    (forcedVelocityEnergy_continuous_degreeE ν μ κ e N f hf u θ hsol).continuousOn
  obtain ⟨T₀, hT₀⟩ := hK.bddAbove_image
    (forcedTempEnstrophy_continuous_degreeE ν μ κ e N f hf u θ hsol).continuousOn
  set E_max : ℝ := max E₀ 1 with hE_max
  set T_max : ℝ := max T₀ 0 with hT_max
  have hEpos : 0 < E_max := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hTmaxnn : 0 ≤ T_max := le_max_right _ _
  have hEmax : ∀ t ∈ Set.Icc 0 T, velocityEnergy (u t) N ≤ E_max := fun t ht =>
    (hE₀ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  have hTle : ∀ t ∈ Set.Icc 0 T, tempEnstrophy (θ t) N ≤ T_max := fun t ht =>
    (hT₀ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  set C₀ : ℝ := 2187 / (16 * (ν / (2 * E_max)) ^ 3) + κ ^ 2 / (4 * (ν / (4 * E_max)))
      + (E_max / ν) + forceEnstrophy f N + |κ| * T_max with hC₀
  have hC₀nn : 0 ≤ C₀ := by
    rw [hC₀]
    have h1 : 0 ≤ 2187 / (16 * (ν / (2 * E_max)) ^ 3) :=
      div_nonneg (by norm_num) (by positivity)
    have h2 : 0 ≤ κ ^ 2 / (4 * (ν / (4 * E_max))) :=
      div_nonneg (sq_nonneg _) (by positivity)
    have h3 : 0 ≤ E_max / ν := div_nonneg hEpos.le hν.le
    have h4 : 0 ≤ forceEnstrophy f N := forceEnstrophy_nonneg f N
    have h5 : 0 ≤ |κ| * T_max := mul_nonneg (abs_nonneg κ) hTmaxnn
    linarith
  have hγpos : 0 < ν / E_max := div_pos hν hEpos
  have hderiv : ∀ t ∈ Set.Ico 0 T, HasDerivAt (fun s => enstrophy (u s) N)
      (2 * ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
        * (velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ) + f (k : ℤ))) t :=
    fun t _ => forcedEnstrophy_hasDerivAt_degreeE ν μ κ e N f hf u θ hsol t
  have hineq : ∀ t ∈ Set.Ico 0 T,
      2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
          * (velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ) + f (k : ℤ)))
        ≤ C₀ - (ν / E_max) * (enstrophy (u t) N) ^ 2 := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 T := ⟨ht.1, le_of_lt ht.2⟩
    have hrate := forced_enstrophy_rate_le_degreeE ν κ E_max hν.le hEpos e he N f (u t) (θ t)
      (hsol.2.2 t).1 (hsol.2.2 t).2.1 (hEmax t htIcc)
    have hHnn : 0 ≤ enstrophy (u t) N := enstrophy_nonneg (u t) N
    have hκT : |κ| * (enstrophy (u t) N + tempEnstrophy (θ t) N)
        ≤ |κ| * (enstrophy (u t) N + T_max) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl _) (hTle t htIcc)) (abs_nonneg κ)
    have hyoung := forced_enstrophy_young (ν := ν) (κ := |κ|) (E_max := E_max)
      (He := forceEnstrophy f N) (T_max := T_max) (s := Real.sqrt (enstrophy (u t) N))
      hν hEpos (abs_nonneg κ) (forceEnstrophy_nonneg f N) hTmaxnn (Real.sqrt_nonneg _)
    have hs2 : (Real.sqrt (enstrophy (u t) N)) ^ 2 = enstrophy (u t) N := Real.sq_sqrt hHnn
    have hs3 : (Real.sqrt (enstrophy (u t) N)) ^ 3
        = enstrophy (u t) N * Real.sqrt (enstrophy (u t) N) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, hs2]
    have hs4 : (Real.sqrt (enstrophy (u t) N)) ^ 4 = (enstrophy (u t) N) ^ 2 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, hs2]
      ring
    rw [hs3, hs4, hs2, sq_abs] at hyoung
    rw [mul_comm (Real.sqrt (enstrophy (u t) N)) (Real.sqrt (forceEnstrophy f N))] at hrate
    rw [hC₀]
    simp only [div_eq_mul_inv] at hrate hyoung ⊢
    linarith [hrate, hyoung, hκT]
  have hbar := le_of_deriv_le_const_sub_sq (y := fun t => enstrophy (u t) N)
    (y' := fun t => 2 * ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
      * (velocityRHSDegreeE ν κ 1 0 e (u t) (θ t) (k : ℤ) + f (k : ℤ)))
    hC₀nn hγpos hcont hderiv hineq
  exact ⟨max (enstrophy (u 0) N) (Real.sqrt (C₀ / (ν / E_max))), fun t ht => hbar t ht⟩

/-! ## 2b. The weighted Cauchy–Schwarz and the interpolated bound

All exponents here are integers (`zpow`); no `Real.rpow` is used.

The resulting homogeneity comparison is the point of the whole file: the cubic transfer enters at
`H`-homogeneity `3/2`, while `D_e ≥ H^{1+e/2}/E^{e/2}` gives dissipation homogeneity `1 + e/2`.
So `e > 1` wins unconditionally, `e = 1` **ties exactly** (`3/2` against `3/2`) and the barrier
closes only under a size condition — for `κ = 0` the rate bound reads
`2 Σ 4^k u_k (du_k/dt) ≤ 6 H √H − 2ν H^{3/2}/√E_max`, i.e. `(6 − 2ν/√E_max) H^{3/2}`, which is
negative iff `ν > 3 √E_max` — and `e ≤ 0` loses.  (Item 5 of the brief: the tie is visible in
`dissipation_interp_sq` at `e = 1`, and the threshold is the `ν > 3√E_max` above.) -/

/-- `D_0 = H`: at degree `0` the dissipation is the enstrophy. -/
theorem enstrophyDissipation_zero (u : ℤ → ℝ) (N : ℕ) :
    enstrophyDissipation 0 u N = enstrophy u N := by
  rw [enstrophyDissipation, enstrophy]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (2 + (0:ℤ)) * (k:ℤ) = 2 * (k:ℤ) by ring]

/-- `W_0 = H`. -/
theorem weightedEnstrophy_zero (u : ℤ → ℝ) (N : ℕ) :
    weightedEnstrophy 0 u N = enstrophy u N := by
  rw [weightedEnstrophy, enstrophy]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (2 - (0:ℤ)) * (k:ℤ) = 2 * (k:ℤ) by ring]

/-- `W_2 = E`. -/
theorem weightedEnstrophy_two (u : ℤ → ℝ) (N : ℕ) :
    weightedEnstrophy 2 u N = enstrophyEnergy u N := by
  rw [weightedEnstrophy, enstrophyEnergy]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (2 - (2:ℤ)) * (k:ℤ) = 0 by ring, dyadicWeight, zpow_zero, one_mul]

/-- `E ≥ 0`. -/
theorem enstrophyEnergy_nonneg (u : ℤ → ℝ) (N : ℕ) : 0 ≤ enstrophyEnergy u N := by
  rw [enstrophyEnergy]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-- `W_e ≥ 0`. -/
theorem weightedEnstrophy_nonneg (e : ℤ) (u : ℤ → ℝ) (N : ℕ) :
    0 ≤ weightedEnstrophy e u N := by
  rw [weightedEnstrophy]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (dyadicWeight_nonneg _) (sq_nonneg _)

/-- `D_e = Σ 2^{ek} a_k²` with `a_k = 2^k u_k` (`vorticity u k`). -/
private lemma sum_dissipation_weight_vorticity (e : ℤ) (u : ℤ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, dyadicWeight (e * (k:ℤ)) * (vorticity u (k:ℤ)) ^ 2)
      = enstrophyDissipation e u N := by
  rw [enstrophyDissipation]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [vorticity_sq, ← mul_assoc, ← dW_add]
  congr 1
  ring

/-- `W_e = Σ 2^{−ek} a_k²`. -/
private lemma sum_backplate_weight_vorticity (e : ℤ) (u : ℤ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, dyadicWeight (-(e * (k:ℤ))) * (vorticity u (k:ℤ)) ^ 2)
      = weightedEnstrophy e u N := by
  rw [weightedEnstrophy]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [vorticity_sq, ← mul_assoc, ← dW_add]
  congr 1
  ring

/-- **Weighted Cauchy–Schwarz**: `H² ≤ D_e · W_e` for every integer degree `e`.  This is
Cauchy–Schwarz applied to the splitting `a_k² = (2^{ek/2}a_k)·(2^{−ek/2}a_k)`. -/
theorem weighted_cauchy_schwarz (e : ℤ) (u : ℤ → ℝ) (N : ℕ) :
    (enstrophy u N) ^ 2 ≤ enstrophyDissipation e u N * weightedEnstrophy e u N := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun k : ℕ => Real.sqrt (dyadicWeight (e * (k:ℤ))) * vorticity u (k:ℤ))
    (fun k : ℕ => Real.sqrt (dyadicWeight (-(e * (k:ℤ)))) * vorticity u (k:ℤ))
  have hroot : ∀ k : ℕ, Real.sqrt (dyadicWeight (e * (k:ℤ)))
      * Real.sqrt (dyadicWeight (-(e * (k:ℤ)))) = 1 := by
    intro k
    rw [← Real.sqrt_mul (dyadicWeight_nonneg _)]
    have h : dyadicWeight (e * (k:ℤ)) * dyadicWeight (-(e * (k:ℤ))) = 1 := by
      rw [← dW_add, show e * (k:ℤ) + -(e * (k:ℤ)) = 0 by ring, dyadicWeight, zpow_zero]
    rw [h, Real.sqrt_one]
  have hL : (∑ k ∈ Finset.range N, Real.sqrt (dyadicWeight (e * (k:ℤ))) * vorticity u (k:ℤ)
        * (Real.sqrt (dyadicWeight (-(e * (k:ℤ)))) * vorticity u (k:ℤ)))
      = enstrophy u N := by
    rw [enstrophy]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show Real.sqrt (dyadicWeight (e * (k:ℤ))) * vorticity u (k:ℤ)
          * (Real.sqrt (dyadicWeight (-(e * (k:ℤ)))) * vorticity u (k:ℤ))
        = (Real.sqrt (dyadicWeight (e * (k:ℤ))) * Real.sqrt (dyadicWeight (-(e * (k:ℤ)))))
          * (vorticity u (k:ℤ)) ^ 2 by ring]
    rw [hroot k, one_mul, vorticity_sq]
  have hA : (∑ k ∈ Finset.range N,
        (Real.sqrt (dyadicWeight (e * (k:ℤ))) * vorticity u (k:ℤ)) ^ 2)
      = enstrophyDissipation e u N := by
    rw [← sum_dissipation_weight_vorticity e u N]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, Real.sq_sqrt (dyadicWeight_nonneg _)]
  have hB : (∑ k ∈ Finset.range N,
        (Real.sqrt (dyadicWeight (-(e * (k:ℤ)))) * vorticity u (k:ℤ)) ^ 2)
      = weightedEnstrophy e u N := by
    rw [← sum_backplate_weight_vorticity e u N]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, Real.sq_sqrt (dyadicWeight_nonneg _)]
  rw [hL, hA, hB] at hcs
  exact hcs

/-- **Hölder backplate, squared**: for `0 ≤ e ≤ 2`, `W_e² ≤ E^e · H^{2−e}`.  For integer `e` the
only cases are `e ∈ {0,1,2}`; `e = 1` is Cauchy–Schwarz `(Σ2^k u_k²)² ≤ (Σ2^{2k}u_k²)(Σu_k²)`. -/
theorem weightedEnstrophy_sq_le (e : ℤ) (he0 : 0 ≤ e) (he2 : e ≤ 2) (u : ℤ → ℝ) (N : ℕ) :
    (weightedEnstrophy e u N) ^ 2
      ≤ (enstrophyEnergy u N) ^ e * (enstrophy u N) ^ (2 - e) := by
  have hecases : e = 0 ∨ e = 1 ∨ e = 2 := by omega
  rcases hecases with rfl | rfl | rfl
  · rw [weightedEnstrophy_zero, zpow_zero, one_mul, show (2:ℤ) - 0 = 2 by ring]
    simp
  · have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
      (fun k : ℕ => dyadicWeight (k:ℤ) * u (k:ℤ)) (fun k : ℕ => u (k:ℤ))
    have hL : (∑ k ∈ Finset.range N, dyadicWeight (k:ℤ) * u (k:ℤ) * u (k:ℤ))
        = weightedEnstrophy 1 u N := by
      rw [weightedEnstrophy]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (2 - (1:ℤ)) * (k:ℤ) = (k:ℤ) by ring]
      ring
    have hA : (∑ k ∈ Finset.range N, (dyadicWeight (k:ℤ) * u (k:ℤ)) ^ 2)
        = enstrophy u N := by
      rw [enstrophy]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_pow, dW_sq]
    have hB : (∑ k ∈ Finset.range N, (u (k:ℤ)) ^ 2) = enstrophyEnergy u N := rfl
    rw [hL, hA, hB] at hcs
    have hthis : (enstrophyEnergy u N) ^ (1:ℤ) * (enstrophy u N) ^ (2 - (1:ℤ))
        = enstrophy u N * enstrophyEnergy u N := by
      rw [show (2:ℤ) - 1 = 1 by ring, zpow_one, zpow_one]
      ring
    rw [hthis]
    exact hcs
  · rw [weightedEnstrophy_two, show (2:ℤ) - 2 = 0 by ring, zpow_zero, mul_one]
    exact le_refl _

/-- **The interpolated dissipation bound, squared** — the brief's
`D_e ≥ H^{1+e/2}/E^{e/2}` with all fractional exponents cleared: for `0 ≤ e ≤ 2`,
`H^{2+e} ≤ D_e² · E^e`.  Route: `weighted_cauchy_schwarz` (`H² ≤ D_e W_e`) squared against
`weightedEnstrophy_sq_le` (`W_e² ≤ E^e H^{2−e}`). -/
theorem dissipation_interp_sq (e : ℤ) (he0 : 0 ≤ e) (he2 : e ≤ 2) (u : ℤ → ℝ) (N : ℕ) :
    (enstrophy u N) ^ (2 + e).toNat
      ≤ (enstrophyDissipation e u N) ^ 2 * (enstrophyEnergy u N) ^ e := by
  have hecases : e = 0 ∨ e = 1 ∨ e = 2 := by omega
  rcases hecases with rfl | rfl | rfl
  · rw [enstrophyDissipation_zero, show (2 + (0:ℤ)).toNat = 2 by simp, zpow_zero, mul_one]
  · have hcs := weighted_cauchy_schwarz 1 u N
    have hbl := weightedEnstrophy_sq_le 1 (by norm_num) (by norm_num) u N
    have hbl' : (weightedEnstrophy 1 u N) ^ 2 ≤ enstrophyEnergy u N * enstrophy u N := by
      have hthis : (enstrophyEnergy u N) ^ (1:ℤ) * (enstrophy u N) ^ (2 - (1:ℤ))
          = enstrophyEnergy u N * enstrophy u N := by
        rw [show (2:ℤ) - 1 = 1 by ring, zpow_one, zpow_one]
      rwa [hthis] at hbl
    have h4 : ((enstrophy u N) ^ 2) ^ 2
        ≤ (enstrophyDissipation 1 u N * weightedEnstrophy 1 u N) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) hcs 2
    have h5 : (enstrophyDissipation 1 u N * weightedEnstrophy 1 u N) ^ 2
        ≤ (enstrophyDissipation 1 u N) ^ 2 * (enstrophyEnergy u N * enstrophy u N) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hbl' (sq_nonneg _)
    have h6 : ((enstrophy u N) ^ 2) ^ 2
        ≤ (enstrophyDissipation 1 u N) ^ 2 * enstrophyEnergy u N * enstrophy u N :=
      h4.trans (h5.trans (le_of_eq (by ring)))
    rw [show (2 + (1:ℤ)).toNat = 3 by simp, zpow_one]
    rcases eq_or_lt_of_le (enstrophy_nonneg u N) with hH0 | hHpos
    · rw [← hH0]
      rw [show (0:ℝ) ^ 3 = 0 by norm_num]
      exact mul_nonneg (sq_nonneg _) (enstrophyEnergy_nonneg u N)
    · have h7 : (enstrophy u N) * (enstrophy u N) ^ 3
          ≤ (enstrophy u N) * ((enstrophyDissipation 1 u N) ^ 2 * enstrophyEnergy u N) := by
        calc (enstrophy u N) * (enstrophy u N) ^ 3 = ((enstrophy u N) ^ 2) ^ 2 := by ring
          _ ≤ (enstrophyDissipation 1 u N) ^ 2 * enstrophyEnergy u N * enstrophy u N := h6
          _ = (enstrophy u N) * ((enstrophyDissipation 1 u N) ^ 2 * enstrophyEnergy u N) := by ring
      exact le_of_mul_le_mul_left h7 hHpos
  · have hlib := enstrophy_sq_le_dissipation_mul_energy u N
    have hlib' : (enstrophy u N) ^ 2
        ≤ enstrophyDissipation 2 u N * enstrophyEnergy u N := by
      have h := enstrophy_sq_le_dissipation_mul_energy u N
      rw [← enstrophyDissipation_two] at h
      simpa only [← enstrophyEnergy_eq_velocityEnergy] using h
    have h5 : ((enstrophy u N) ^ 2) ^ 2
        ≤ (enstrophyDissipation 2 u N) ^ 2 * (enstrophyEnergy u N) ^ 2 := by
      calc ((enstrophy u N) ^ 2) ^ 2
          ≤ (enstrophyDissipation 2 u N * enstrophyEnergy u N) ^ 2 :=
            pow_le_pow_left₀ (sq_nonneg _) hlib' 2
        _ = (enstrophyDissipation 2 u N) ^ 2 * (enstrophyEnergy u N) ^ 2 := by rw [mul_pow]
    rw [show (2 + (2:ℤ)).toNat = 4 by simp,
      show (enstrophyEnergy u N) ^ (2:ℤ) = (enstrophyEnergy u N) ^ 2 by norm_num,
      show (enstrophy u N) ^ 4 = ((enstrophy u N) ^ 2) ^ 2 by ring]
    exact h5

/-! ## 3. The threshold: the domination fails below `e = 2` -/

/-- The single-mode ladder `u = δ_{·,k}`. -/
def deltaShell (k : ℤ) : ℤ → ℝ := fun j => if j = k then 1 else 0

private lemma deltaShell_self (k : ℤ) : deltaShell k k = 1 := by simp [deltaShell]

private lemma deltaShell_ne (k j : ℤ) (h : j ≠ k) : deltaShell k j = 0 := by
  simp [deltaShell, h]

/-- The energy of the single mode `δ_{·,k}` is `1`. -/
theorem enstrophyEnergy_deltaShell (k : ℕ) :
    enstrophyEnergy (deltaShell (k : ℤ)) (k + 1) = 1 := by
  rw [enstrophyEnergy, Finset.sum_eq_single k]
  · rw [deltaShell_self, one_pow]
  · intro j _ hj
    rw [deltaShell_ne (k:ℤ) (j:ℤ) (by exact_mod_cast hj), sq_eq_zero_iff.mpr rfl]
  · intro hk
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) hk

/-- The enstrophy of the single mode `δ_{·,k}` is `2^{2k}`. -/
theorem enstrophy_deltaShell (k : ℕ) :
    enstrophy (deltaShell (k : ℤ)) (k + 1) = dyadicWeight (2 * (k : ℤ)) := by
  rw [enstrophy, Finset.sum_eq_single k]
  · rw [deltaShell_self, one_pow, mul_one]
  · intro j _ hj
    rw [deltaShell_ne (k:ℤ) (j:ℤ) (by exact_mod_cast hj), sq_eq_zero_iff.mpr rfl, mul_zero]
  · intro hk
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) hk

/-- The dissipation of the single mode `δ_{·,k}` is `2^{(2+e)k}`. -/
theorem enstrophyDissipation_deltaShell (e : ℤ) (k : ℕ) :
    enstrophyDissipation e (deltaShell (k : ℤ)) (k + 1)
      = dyadicWeight ((2 + e) * (k : ℤ)) := by
  rw [enstrophyDissipation, Finset.sum_eq_single k]
  · rw [deltaShell_self, one_pow, mul_one]
  · intro j _ hj
    rw [deltaShell_ne (k:ℤ) (j:ℤ) (by exact_mod_cast hj), sq_eq_zero_iff.mpr rfl, mul_zero]
  · intro hk
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) hk

/-- **The single-mode ratio** `D_e·E/H² = 2^{(e−2)k}` for `u = δ_{·,k}` on `N = k+1` shells. -/
theorem single_mode_dissipation_ratio (e : ℤ) (k : ℕ) :
    enstrophyDissipation e (deltaShell (k : ℤ)) (k + 1)
        * enstrophyEnergy (deltaShell (k : ℤ)) (k + 1)
      / (enstrophy (deltaShell (k : ℤ)) (k + 1)) ^ 2
      = (2 : ℝ) ^ ((e - 2) * (k : ℤ)) := by
  rw [enstrophyDissipation_deltaShell, enstrophyEnergy_deltaShell, enstrophy_deltaShell, mul_one,
    show (2:ℝ) ^ ((e - 2) * (k:ℤ)) = dyadicWeight ((e - 2) * (k:ℤ)) from rfl]
  rw [div_eq_iff (pow_ne_zero 2 (dyadicWeight_pos _).ne')]
  rw [show (dyadicWeight (2 * (k:ℤ))) ^ 2 = dyadicWeight (2 * (2 * (k:ℤ))) by
    rw [sq, ← dW_add]; congr 1; ring]
  rw [← dW_add]
  congr 1
  ring

/-- **The quadratic domination fails for every `e < 2`.**  For every `c > 0` there is data with
`D_e·E < c·H²`, namely the single mode `u = δ_{·,k}` with `k` large, for which
`D_e·E/H² = 2^{(e−2)k}`.  (This does **not** by itself obstruct the enstrophy barrier: the barrier
needs only the interpolated `D_e ≥ H^{1+e/2}/E^{e/2}`, i.e. `e > 1`; see the module docstring.) -/
theorem no_uniform_dissipation_domination (e : ℤ) (he : e < 2) (c : ℝ) (hc : 0 < c) :
    ∃ (u : ℤ → ℝ) (N : ℕ),
      enstrophyDissipation e u N * enstrophyEnergy u N < c * (enstrophy u N) ^ 2 := by
  have he1 : e ≤ 1 := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (2:ℝ) ^ ((e - 2) * (k:ℤ)) < c := by
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / c)
    refine ⟨k, ?_⟩
    have hklt : (k:ℝ) < (2:ℝ) ^ k := by exact_mod_cast Nat.lt_two_pow_self
    have hk2 : (1:ℝ) / c < (2:ℝ) ^ k := by linarith
    have hk0 : (0:ℤ) ≤ (k:ℤ) := by exact_mod_cast Nat.zero_le k
    have hle : (e - 2) * (k:ℤ) ≤ -(k:ℤ) := by nlinarith
    have h2 : (2:ℝ) ^ ((e - 2) * (k:ℤ)) ≤ (2:ℝ) ^ (-(k:ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hle
    have h3 : (2:ℝ) ^ (-(k:ℤ)) < c := by
      rw [zpow_neg]
      exact (inv_lt_comm₀ (zpow_pos (by norm_num : (0:ℝ) < 2) _) hc).mpr (by
        rw [show c⁻¹ = 1/c by ring]; exact hk2)
    linarith
  refine ⟨deltaShell (k:ℤ), k + 1, ?_⟩
  rw [enstrophyDissipation_deltaShell, enstrophyEnergy_deltaShell, enstrophy_deltaShell, mul_one]
  have hD : dyadicWeight ((2 + e) * (k:ℤ))
      = (2:ℝ) ^ ((e - 2) * (k:ℤ)) * (dyadicWeight (2 * (k:ℤ))) ^ 2 := by
    have h2 : (dyadicWeight (2 * (k:ℤ))) ^ 2 = dyadicWeight (4 * (k:ℤ)) := by
      rw [sq, ← dW_add]; congr 1; ring
    rw [h2, show (2:ℝ) ^ ((e - 2) * (k:ℤ)) = dyadicWeight ((e - 2) * (k:ℤ)) from rfl,
      ← dW_add]
    congr 1
    ring
  rw [hD]
  exact mul_lt_mul_of_pos_right hk (pow_pos (dyadicWeight_pos _) 2)

/-- **Corollary**: the domination `D_e ≥ c·H²/E` cannot be extended below `e = 2`. -/
theorem no_barrier_below_two (e : ℤ) (he : e < 2) (c : ℝ) (hc : 0 < c) :
    ∃ (u : ℤ → ℝ) (N : ℕ),
      ¬ (c * (enstrophy u N) ^ 2 ≤ enstrophyDissipation e u N * enstrophyEnergy u N) := by
  obtain ⟨u, N, h⟩ := no_uniform_dissipation_domination e he c hc
  exact ⟨u, N, not_le.mpr h⟩

/-! ## 4. The quadratic domination fails below `e = 2`

On the concrete state `u = (0,0,3,0)` (`N = 3`) one has `E = 9`, `H = 144`, `D_1 = 576`, so
`D_1·E = 5184 < 20736 = H²`: the **quadratic** domination `D_1 ≥ H²/E` fails.

Note what this does *not* say.  The brief's claim at `e = 1`, `D_1 ≥ H^{3/2}/E^{1/2}`, is equivalent
to `D_1·E ≥ H^{3/2}√E = 1728·3 = 5184`, and on this very state `D_1·E = 5184`: the interpolated
claim holds **with equality**.  The two thresholds are different, and this state separates them. -/

/-- The concrete ladder `u_2 = 3`, all other shells zero. -/
def uThr : ℤ → ℝ := fun k => if k = 2 then 3 else 0

/-- The concrete energy `E = 9`. -/
theorem uThr_energy : enstrophyEnergy uThr 3 = 9 := by
  simp only [enstrophyEnergy, Finset.sum_range_succ, Finset.sum_range_zero, uThr]
  norm_num

/-- The concrete enstrophy `H = 144`. -/
theorem uThr_enstrophy : enstrophy uThr 3 = 144 := by
  simp only [enstrophy, Finset.sum_range_succ, Finset.sum_range_zero, uThr, dyadicWeight]
  norm_num

/-- The concrete degree-`1` dissipation `D_1 = 576`. -/
theorem uThr_D1 : enstrophyDissipation 1 uThr 3 = 576 := by
  simp only [enstrophyDissipation, Finset.sum_range_succ, Finset.sum_range_zero, uThr, dyadicWeight]
  norm_num

/-- The concrete degree-`2` dissipation `D_2 = 2304`. -/
theorem uThr_D2 : enstrophyDissipation 2 uThr 3 = 2304 := by
  simp only [enstrophyDissipation, Finset.sum_range_succ, Finset.sum_range_zero, uThr, dyadicWeight]
  norm_num

/-- **The quadratic domination fails at `e = 1`**: `D_1·E = 5184 < H² = 20736`.  This is the
negation of `D_e ≥ H²/E`, and it does not contradict the interpolated claim
`D_e ≥ H^{1+e/2}/E^{e/2}` (which holds here with equality). -/
theorem quadratic_domination_fails_one :
    enstrophyDissipation 1 uThr 3 * enstrophyEnergy uThr 3 < (enstrophy uThr 3) ^ 2 := by
  rw [uThr_D1, uThr_energy, uThr_enstrophy]
  norm_num

/-! ## 5. Non-vacuity -/

/-- The interpolation backplate endpoint `W_2 = E` on the concrete state. -/
example : weightedEnstrophy 2 uThr 3 = enstrophyEnergy uThr 3 := by
  simp only [weightedEnstrophy, enstrophyEnergy, Finset.sum_range_succ, Finset.sum_range_zero,
    uThr, dyadicWeight]
  norm_num

/-- The `e ≥ 2` domination at `e = 2` on the concrete state: `H²/E = 2304 ≤ D_2 = 2304`. -/
example : (enstrophy uThr 3) ^ 2 / enstrophyEnergy uThr 3
    ≤ enstrophyDissipation 2 uThr 3 := by
  rw [uThr_D2, uThr_enstrophy, uThr_energy]
  norm_num

/-- The domination through the theorem (not just numerically). -/
example : (enstrophy uThr 3) ^ 2 / velocityEnergy uThr 3
    ≤ enstrophyDissipation 2 uThr 3 :=
  dissipation_ge_of_two_le 2 (by norm_num) uThr 3 (by
    simp only [velocityEnergy, Finset.sum_range_succ, Finset.sum_range_zero, uThr]
    norm_num)

/-- The zero state satisfies the degree-`e` unforced predicate. -/
example : IsUnforcedTruncatedSolutionE 1 1 1 3 2 (fun _ _ => (0:ℝ)) (fun _ _ => (0:ℝ)) :=
  zero_is_unforcedTruncatedSolutionE 1 1 1 3 2

/-! ## 6. Non-vacuity of the new results -/

/-- `weighted_cauchy_schwarz` at `e = 1` on `u = (0,0,3,0)`, `N = 3`: `H² = 20736 = D_1·W_1`. -/
example : (enstrophy uThr 3) ^ 2
    ≤ enstrophyDissipation 1 uThr 3 * weightedEnstrophy 1 uThr 3 :=
  weighted_cauchy_schwarz 1 uThr 3

/-- `dissipation_interp_sq` at `e = 1` on `u = (0,0,3,0)`, `N = 3`: `H³ = 2985984 = D_1²·E`. -/
example : (enstrophy uThr 3) ^ (2 + (1:ℤ)).toNat
    ≤ (enstrophyDissipation 1 uThr 3) ^ 2 * (enstrophyEnergy uThr 3) ^ (1:ℤ) :=
  dissipation_interp_sq 1 (by norm_num) (by norm_num) uThr 3

/-- The three interpolation cases as a sanity check. -/
example : (enstrophy uThr 3) ^ (2 + (0:ℤ)).toNat
      ≤ (enstrophyDissipation 0 uThr 3) ^ 2 * (enstrophyEnergy uThr 3) ^ (0:ℤ)
    ∧ (enstrophy uThr 3) ^ (2 + (2:ℤ)).toNat
      ≤ (enstrophyDissipation 2 uThr 3) ^ 2 * (enstrophyEnergy uThr 3) ^ (2:ℤ) :=
  ⟨dissipation_interp_sq 0 (by norm_num) (by norm_num) uThr 3,
   dissipation_interp_sq 2 (by norm_num) (by norm_num) uThr 3⟩

/-- `no_uniform_dissipation_domination` with concrete constants: at `e = 1` and `c = 1` there is a
state with `D_1·E < H²`. -/
example : ∃ (u : ℤ → ℝ) (N : ℕ),
    enstrophyDissipation 1 u N * enstrophyEnergy u N < 1 * (enstrophy u N) ^ 2 :=
  no_uniform_dissipation_domination 1 (by norm_num) 1 (by norm_num)

/-- `single_mode_dissipation_ratio` at `e = 1`, `k = 3`: `D_1·E/H² = 2^{−3}`. -/
example : enstrophyDissipation 1 (deltaShell 3) 4 * enstrophyEnergy (deltaShell 3) 4
    / (enstrophy (deltaShell 3) 4) ^ 2 = (2:ℝ) ^ (-3 : ℤ) := by
  have h := single_mode_dissipation_ratio 1 3
  simpa using h

/-- `tempEnstrophyE` concretely: `T_2(δ_{·,2}) = 2^{4} = 16`. -/
example : tempEnstrophyE 2 (fun j : ℤ => if j = 2 then (1:ℝ) else 0) 3 = 16 := by
  simp only [tempEnstrophyE, Finset.sum_range_succ, Finset.sum_range_zero, dyadicWeight]
  norm_num

/-- **The unforced degree-`e` capstone applies** at the zero equilibrium (`e = 2`, `N = 2`,
`[0,1]`). -/
example : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2 ≤ C := by
  refine truncated_unforced_enstrophy_bounded_degreeE (T := 1) 1 1 1 (by norm_num)
    (by norm_num) 2 (by norm_num) 2 (fun _ _ => 0) (fun _ _ => 0)
    (zero_is_unforcedTruncatedSolutionE 1 1 1 2 2) (by norm_num) ?_
  have hfun : (fun t => enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2)
      = fun _ => (0 : ℝ) := by
    funext t
    simp [enstrophy]
  rw [hfun]
  exact continuousOn_const

end Cascade

/-! ## Axiom audit -/

#print axioms Cascade.velocityRHSDegreeE_scaling_covariant
#print axioms Cascade.temperatureRHSDegreeE_scaling_covariant
#print axioms Cascade.boussinesqRHSDegreeE_scaling_covariant
#print axioms Cascade.isUnforcedTruncatedSolutionE_two_iff
#print axioms Cascade.dissipation_ge_of_two_le
#print axioms Cascade.enstrophyDissipation_zero
#print axioms Cascade.weightedEnstrophy_zero
#print axioms Cascade.weightedEnstrophy_two
#print axioms Cascade.weightedEnstrophy_nonneg
#print axioms Cascade.weighted_cauchy_schwarz
#print axioms Cascade.weightedEnstrophy_sq_le
#print axioms Cascade.dissipation_interp_sq
#print axioms Cascade.single_mode_dissipation_ratio
#print axioms Cascade.no_uniform_dissipation_domination
#print axioms Cascade.no_barrier_below_two
#print axioms Cascade.enstrophyEnergy_nonneg
#print axioms Cascade.enstrophy_pairing_degreeE
#print axioms Cascade.enstrophy_pairing_le_degreeE
#print axioms Cascade.enstrophy_rate_le_of_solution_degreeE
#print axioms Cascade.tempEnstrophyE
#print axioms Cascade.tempEnstrophyE_nonneg
#print axioms Cascade.enstrophy_hasDerivAt_degreeE
#print axioms Cascade.entropy_hasDerivAt_degreeE
#print axioms Cascade.temperature_pairing_degreeE
#print axioms Cascade.enstrophyLyapunov_hasDerivAt_degreeE
#print axioms Cascade.enstrophyLyapunov_deriv_le_degreeE
#print axioms Cascade.truncated_unforced_enstrophy_bounded_degreeE
#print axioms Cascade.forced_enstrophy_rate_le_degreeE
#print axioms Cascade.forced_truncated_enstrophy_bounded_degreeE
#print axioms Cascade.quadratic_domination_fails_one
