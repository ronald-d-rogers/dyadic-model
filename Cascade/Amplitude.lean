/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# The inviscid Rayleigh–Taylor amplitude system `Θ̇ = b Ω`, `Ω̇ = a Θ`

This file isolates the **amplitude–frequency ordinary differential equation** behind the
page-4 reduction of Tao's "remarkably simple" Boussinesq construction: writing `Θ` for
the temperature amplitude and `Ω` for the vertical-velocity amplitude of a single mode,
the linearised Boussinesq equations about a linearly stratified background collapse to

`Θ̇ = b · Ω`,   `Ω̇ = a · Θ`,

i.e. the `2 × 2` companion matrix `rayleighTaylorMatrix a b = !![0, b; a, 0]`.

The two coupling constants are

* `a` — the **signed background temperature gradient** (the vertical derivative of the
  background temperature profile, evaluated at the mode), and
* `b` — the **buoyancy coupling** (the coefficient of `Θ` in the vertical momentum
  equation, proportional to the mode wavenumber).

## What is proved here

1. `rayleighTaylorMatrix_mulVec` — the action `(Θ, Ω) ↦ (b Ω, a Θ)`.
2. `rayleighTaylor_charpoly` — the characteristic polynomial is `X ^ 2 - a * b`
   (the trace vanishes and `det = -a*b`), so the eigenvalues of the companion matrix
   are `±√(a b)`.
3. `rayleighTaylor_eigenvector_pos` / `..._neg` — `![b, ±ω]` are eigenvectors of the
   companion matrix with eigenvalues `±ω` for `a b ≥ 0`.
4. `rayleighTaylorSolution_hasDerivAt_fst` / `..._snd` — the explicit `cosh`/`sinh`
   fundamental solution solves `Θ̇ = b Ω`, `Ω̇ = a Θ` at every time.

   Both cross-coefficients are `b/ω` in `Θ` and `a/ω` in `Ω` (with `ω = √(a b)`);
   these are exactly what the two equations force, and both components satisfy the
   scalar second-order equation `Θ'' = a b Θ`, whose characteristic roots are
   `±√(a b)`.
5. `rayleighTaylorSolution_unbounded` — for `a * b > 0`, `Θ₀ > 0` and `b Ω₀ ≥ 0`, the
   temperature component tends to `+∞`; the divergence is exponentially fast at the
   **Rayleigh–Taylor rate `√(a b)`** (the solution is bounded below by
   `(Θ₀/2) exp(√(a b) t)`).  The scalar companion fact is that both components satisfy
   the second-order equation `Θ'' = a b Θ`, whose characteristic roots are `±√(a b)`.
6. `rayleighTaylorOscillation_*` — for `a * b < 0` the explicit `cos`/`sin` solution
   solves the same system at the Brunt–Väisälä frequency `√(-(a b))` and is bounded
   (no growth), giving the stable/unstable dichotomy.

## Standalone

This file is deliberately **self-contained**: it imports only Mathlib and does not
depend on any part of the `Cascade` model development.  It is pure linear algebra and
calculus of the `2 × 2` companion matrix and its explicit solution.

In the dyadic (lacunary) model of `Cascade/Lacunary.lean` the couplings for the `n`-th
shell are supplied as `a = θ̄_{n-1}` (the previous shell's mean temperature gradient)
and `b = 2 ^ n * κ` (the shell wavenumber times the buoyancy constant).
-/

noncomputable section

open Real Filter
open scoped Topology Matrix

namespace Cascade

/-- The inviscid Rayleigh–Taylor amplitude matrix `!![0, b; a, 0]` acting on `(Θ, Ω)`.

Here `a` is the signed background temperature gradient coupling and `b` the buoyancy
coupling, so that `rayleighTaylorMatrix a b *ᵥ ![Θ, Ω] = ![b * Ω, a * Θ]`. -/
def rayleighTaylorMatrix (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, b; a, 0]

/-- **The action of the amplitude matrix**: `(Θ, Ω) ↦ (b Ω, a Θ)`. -/
theorem rayleighTaylorMatrix_mulVec (a b Θ Ω : ℝ) :
    rayleighTaylorMatrix a b *ᵥ ![Θ, Ω] = ![b * Ω, a * Θ] := by
  ext i
  fin_cases i <;> simp [rayleighTaylorMatrix, Matrix.mulVec]

/-- The characteristic polynomial of the amplitude matrix is `X ^ 2 - a * b`.

Since the matrix has vanishing trace, its characteristic polynomial is `X² - det`,
and its determinant is `-a * b`. -/
theorem rayleighTaylor_charpoly (a b : ℝ) :
    (rayleighTaylorMatrix a b).charpoly = Polynomial.X ^ 2 - Polynomial.C (a * b) := by
  rw [Matrix.charpoly_fin_two]
  have htrace : (rayleighTaylorMatrix a b).trace = 0 := by
    rw [Matrix.trace_fin_two]
    simp [rayleighTaylorMatrix]
  have hdet : (rayleighTaylorMatrix a b).det = -(a * b) := by
    rw [Matrix.det_fin_two]
    simp [rayleighTaylorMatrix]
    ring
  rw [htrace, hdet, Polynomial.C_neg]
  simp only [Polynomial.C_0, zero_mul, sub_zero]
  ring

/-- `![b, ω]` is an eigenvector of the amplitude matrix with eigenvalue `ω`, where
`ω = √(a b)` (for `a * b ≥ 0`). -/
theorem rayleighTaylor_eigenvector_pos (a b : ℝ) (hab : 0 ≤ a * b) :
    rayleighTaylorMatrix a b *ᵥ ![b, Real.sqrt (a * b)]
      = Real.sqrt (a * b) • ![b, Real.sqrt (a * b)] := by
  rw [rayleighTaylorMatrix_mulVec]
  ext i
  fin_cases i
  · show b * Real.sqrt (a * b) = Real.sqrt (a * b) * b
    ring
  · show a * b = Real.sqrt (a * b) * Real.sqrt (a * b)
    nlinarith [Real.sq_sqrt hab]

/-- `![b, -ω]` is an eigenvector of the amplitude matrix with eigenvalue `-ω`, where
`ω = √(a b)` (for `a * b ≥ 0`). -/
theorem rayleighTaylor_eigenvector_neg (a b : ℝ) (hab : 0 ≤ a * b) :
    rayleighTaylorMatrix a b *ᵥ ![b, -Real.sqrt (a * b)]
      = (-Real.sqrt (a * b)) • ![b, -Real.sqrt (a * b)] := by
  rw [rayleighTaylorMatrix_mulVec]
  ext i
  fin_cases i
  · show b * -Real.sqrt (a * b) = -Real.sqrt (a * b) * b
    ring
  · show a * b = -Real.sqrt (a * b) * -Real.sqrt (a * b)
    nlinarith [Real.sq_sqrt hab]

/-! ### The explicit hyperbolic (`a b > 0`) solution -/

/-- Explicit fundamental solution of `Θ̇ = b Ω`, `Ω̇ = a Θ` for `a b > 0`, written with
`cosh`/`sinh` at the Rayleigh–Taylor rate `ω = √(a b)`.

The cross-coefficients are `b/ω` in the `Θ` component and `a/ω` in the `Ω` component,
exactly as the two equations force.  Both components satisfy the scalar second-order
equation `Θ'' = a b Θ`, whose characteristic roots are `±√(a b)`. -/
def rayleighTaylorSolution (a b Θ₀ Ω₀ : ℝ) (t : ℝ) : ℝ × ℝ :=
  (Θ₀ * Real.cosh (Real.sqrt (a*b) * t)
      + (b / Real.sqrt (a*b)) * Ω₀ * Real.sinh (Real.sqrt (a*b) * t),
   Ω₀ * Real.cosh (Real.sqrt (a*b) * t)
      + (a / Real.sqrt (a*b)) * Θ₀ * Real.sinh (Real.sqrt (a*b) * t))

/-- The first (temperature) component of the explicit solution has the derivative
required by `Θ̇ = b Ω`. -/
theorem rayleighTaylorSolution_hasDerivAt_fst (a b Θ₀ Ω₀ : ℝ) (hab : 0 < a * b) (t : ℝ) :
    HasDerivAt (fun s => (rayleighTaylorSolution a b Θ₀ Ω₀ s).1)
      (b * (rayleighTaylorSolution a b Θ₀ Ω₀ t).2) t := by
  have hω : (0:ℝ) < Real.sqrt (a * b) := Real.sqrt_pos.2 hab
  have hωne : Real.sqrt (a * b) ≠ 0 := ne_of_gt hω
  have hcosh : HasDerivAt (fun s : ℝ => Real.cosh (Real.sqrt (a * b) * s))
      (Real.sqrt (a * b) * Real.sinh (Real.sqrt (a * b) * t)) t := by
    have h := (hasDerivAt_cosh (Real.sqrt (a * b) * t)).comp t
      (hasDerivAt_const_mul (Real.sqrt (a * b)))
    rw [Function.comp_def] at h
    exact h.congr_deriv (by ring)
  have hsinh : HasDerivAt (fun s : ℝ => Real.sinh (Real.sqrt (a * b) * s))
      (Real.sqrt (a * b) * Real.cosh (Real.sqrt (a * b) * t)) t := by
    have h := (hasDerivAt_sinh (Real.sqrt (a * b) * t)).comp t
      (hasDerivAt_const_mul (Real.sqrt (a * b)))
    rw [Function.comp_def] at h
    exact h.congr_deriv (by ring)
  have h1 : HasDerivAt
      (fun s : ℝ => Θ₀ * Real.cosh (Real.sqrt (a * b) * s))
      (Θ₀ * (Real.sqrt (a * b) * Real.sinh (Real.sqrt (a * b) * t))) t :=
    hcosh.const_mul Θ₀
  have h2 : HasDerivAt
      (fun s : ℝ => (b / Real.sqrt (a * b)) * Ω₀ * Real.sinh (Real.sqrt (a * b) * s))
      ((b / Real.sqrt (a * b)) * Ω₀ *
        (Real.sqrt (a * b) * Real.cosh (Real.sqrt (a * b) * t))) t :=
    hsinh.const_mul ((b / Real.sqrt (a * b)) * Ω₀)
  have hderiv := h1.add h2
  have hfun : (fun s : ℝ => (rayleighTaylorSolution a b Θ₀ Ω₀ s).1)
      = fun s : ℝ => Θ₀ * Real.cosh (Real.sqrt (a * b) * s)
          + (b / Real.sqrt (a * b)) * Ω₀ * Real.sinh (Real.sqrt (a * b) * s) := by
    funext s
    simp [rayleighTaylorSolution]
  have hval : (rayleighTaylorSolution a b Θ₀ Ω₀ t).2
      = Ω₀ * Real.cosh (Real.sqrt (a * b) * t)
        + (a / Real.sqrt (a * b)) * Θ₀ * Real.sinh (Real.sqrt (a * b) * t) := by
    simp [rayleighTaylorSolution]
  rw [hfun, hval]
  refine (hderiv.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with s
    rfl
  · have hsq : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt (le_of_lt hab)
    field_simp
    ring_nf
    rw [hsq, mul_comm a b]
    ring

/-- The second (velocity) component of the explicit solution has the derivative
required by `Ω̇ = a Θ`. -/
theorem rayleighTaylorSolution_hasDerivAt_snd (a b Θ₀ Ω₀ : ℝ) (hab : 0 < a * b) (t : ℝ) :
    HasDerivAt (fun s => (rayleighTaylorSolution a b Θ₀ Ω₀ s).2)
      (a * (rayleighTaylorSolution a b Θ₀ Ω₀ t).1) t := by
  have hω : (0:ℝ) < Real.sqrt (a * b) := Real.sqrt_pos.2 hab
  have hωne : Real.sqrt (a * b) ≠ 0 := ne_of_gt hω
  have hcosh : HasDerivAt (fun s : ℝ => Real.cosh (Real.sqrt (a * b) * s))
      (Real.sqrt (a * b) * Real.sinh (Real.sqrt (a * b) * t)) t := by
    have h := (hasDerivAt_cosh (Real.sqrt (a * b) * t)).comp t
      (hasDerivAt_const_mul (Real.sqrt (a * b)))
    rw [Function.comp_def] at h
    exact h.congr_deriv (by ring)
  have hsinh : HasDerivAt (fun s : ℝ => Real.sinh (Real.sqrt (a * b) * s))
      (Real.sqrt (a * b) * Real.cosh (Real.sqrt (a * b) * t)) t := by
    have h := (hasDerivAt_sinh (Real.sqrt (a * b) * t)).comp t
      (hasDerivAt_const_mul (Real.sqrt (a * b)))
    rw [Function.comp_def] at h
    exact h.congr_deriv (by ring)
  have h1 : HasDerivAt
      (fun s : ℝ => Ω₀ * Real.cosh (Real.sqrt (a * b) * s))
      (Ω₀ * (Real.sqrt (a * b) * Real.sinh (Real.sqrt (a * b) * t))) t :=
    hcosh.const_mul Ω₀
  have h2 : HasDerivAt
      (fun s : ℝ => (a / Real.sqrt (a * b)) * Θ₀ * Real.sinh (Real.sqrt (a * b) * s))
      ((a / Real.sqrt (a * b)) * Θ₀ *
        (Real.sqrt (a * b) * Real.cosh (Real.sqrt (a * b) * t))) t :=
    hsinh.const_mul ((a / Real.sqrt (a * b)) * Θ₀)
  have hderiv := h1.add h2
  have hfun : (fun s : ℝ => (rayleighTaylorSolution a b Θ₀ Ω₀ s).2)
      = fun s : ℝ => Ω₀ * Real.cosh (Real.sqrt (a * b) * s)
          + (a / Real.sqrt (a * b)) * Θ₀ * Real.sinh (Real.sqrt (a * b) * s) := by
    funext s
    simp [rayleighTaylorSolution]
  have hval : (rayleighTaylorSolution a b Θ₀ Ω₀ t).1
      = Θ₀ * Real.cosh (Real.sqrt (a * b) * t)
        + (b / Real.sqrt (a * b)) * Ω₀ * Real.sinh (Real.sqrt (a * b) * t) := by
    simp [rayleighTaylorSolution]
  rw [hfun, hval]
  refine (hderiv.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with s
    rfl
  · have hsq : Real.sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt (le_of_lt hab)
    field_simp
    ring_nf
    rw [hsq, mul_comm a b]
    ring

/-- The pair form of the two derivative statements: the explicit solution solves the
inviscid amplitude ODE at every time `t`. -/
theorem rayleighTaylorSolution_hasDerivAt (a b Θ₀ Ω₀ : ℝ) (hab : 0 < a * b) (t : ℝ) :
    HasDerivAt (fun s => (rayleighTaylorSolution a b Θ₀ Ω₀ s).1)
      (b * (rayleighTaylorSolution a b Θ₀ Ω₀ t).2) t ∧
    HasDerivAt (fun s => (rayleighTaylorSolution a b Θ₀ Ω₀ s).2)
      (a * (rayleighTaylorSolution a b Θ₀ Ω₀ t).1) t :=
  ⟨rayleighTaylorSolution_hasDerivAt_fst a b Θ₀ Ω₀ hab t,
   rayleighTaylorSolution_hasDerivAt_snd a b Θ₀ Ω₀ hab t⟩

/-! ### Exponential growth of the unstable mode -/

/-- `cosh` tends to `+∞` at `+∞`. -/
theorem tendsto_cosh_atTop : Tendsto (fun t : ℝ => Real.cosh t) atTop atTop := by
  have h2 : Tendsto (fun t : ℝ => Real.exp t + Real.exp (-t)) atTop atTop :=
    tendsto_exp_atTop.atTop_add tendsto_exp_neg_atTop_nhds_zero
  have h := h2.atTop_mul_const (show (0:ℝ) < 1 / 2 by norm_num)
  refine h.congr' ?_
  filter_upwards with t
  rw [Real.cosh_eq]
  ring

/-- `sinh` tends to `+∞` at `+∞`. -/
theorem tendsto_sinh_atTop : Tendsto (fun t : ℝ => Real.sinh t) atTop atTop := by
  have hexp : Tendsto (fun t : ℝ => Real.exp t / 4) atTop atTop := by
    have h := tendsto_exp_atTop.atTop_mul_const (show (0:ℝ) < 1 / 4 by norm_num)
    refine h.congr' ?_
    filter_upwards with t
    ring
  refine tendsto_atTop_mono' atTop ?_ hexp
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  have hB : Real.exp (-t) ≤ 1 := by
    have h := Real.exp_le_exp.2 (show -t ≤ 0 by linarith)
    rwa [Real.exp_zero] at h
  have hA : (2:ℝ) ≤ Real.exp t := by
    have h5 : Real.exp 1 ≤ Real.exp t := Real.exp_le_exp.2 ht
    have h6 : (2:ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
    linarith
  have hmain : Real.exp t / 4 ≤ (Real.exp t - Real.exp (-t)) / 2 := by nlinarith
  calc Real.exp t / 4 ≤ (Real.exp t - Real.exp (-t)) / 2 := hmain
    _ = Real.sinh t := by rw [Real.sinh_eq]

/-- `cosh (ω t) → +∞` for `ω > 0`. -/
theorem tendsto_cosh_const_mul_atTop {ω : ℝ} (hω : 0 < ω) :
    Tendsto (fun t : ℝ => Real.cosh (ω * t)) atTop atTop :=
  tendsto_cosh_atTop.comp ((tendsto_const_mul_atTop_of_pos hω).2 tendsto_id)

/-- `sinh (ω t) → +∞` for `ω > 0`. -/
theorem tendsto_sinh_const_mul_atTop {ω : ℝ} (hω : 0 < ω) :
    Tendsto (fun t : ℝ => Real.sinh (ω * t)) atTop atTop :=
  tendsto_sinh_atTop.comp ((tendsto_const_mul_atTop_of_pos hω).2 tendsto_id)

/-- For `0 ≤ y`, `0 ≤ Real.sinh y`. -/
theorem sinh_nonneg_of_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ Real.sinh y := by
  have h1 : 1 ≤ Real.exp y := by
    have h := Real.exp_le_exp.2 hy
    rwa [Real.exp_zero] at h
  have h2 : Real.exp (-y) ≤ 1 := by
    have h := Real.exp_le_exp.2 (by linarith : -y ≤ 0)
    rwa [Real.exp_zero] at h
  rw [Real.sinh_eq]
  linarith

/-- For `ω > 0` and `t ≥ 0`, `Real.sinh (ω t) ≥ 0`. -/
theorem sinh_const_mul_nonneg {ω t : ℝ} (hω : 0 < ω) (ht : 0 ≤ t) :
    0 ≤ Real.sinh (ω * t) :=
  sinh_nonneg_of_nonneg (mul_nonneg (le_of_lt hω) ht)

/-- `t ↦ (b/ω) Ω₀ sinh (ω t)` is nonnegative when `b Ω₀ ≥ 0` and `t ≥ 0`. -/
theorem div_b_mul_sinh_nonneg {a b Ω₀ t : ℝ} (hab : 0 < a * b) (hbΩ : 0 ≤ b * Ω₀)
    (ht : 0 ≤ t) : 0 ≤ (b / Real.sqrt (a * b)) * Ω₀ * Real.sinh (Real.sqrt (a * b) * t) := by
  have hω : (0:ℝ) < Real.sqrt (a * b) := Real.sqrt_pos.2 hab
  have hsn : 0 ≤ Real.sinh (Real.sqrt (a * b) * t) := sinh_const_mul_nonneg hω ht
  have h1 : (b / Real.sqrt (a * b)) * Ω₀ = b * Ω₀ / Real.sqrt (a * b) := by
    rw [div_mul_eq_mul_div]
  have h2 : 0 ≤ b * Ω₀ / Real.sqrt (a * b) := div_nonneg hbΩ (le_of_lt hω)
  calc 0 ≤ (b / Real.sqrt (a * b)) * Ω₀ * Real.sinh (Real.sqrt (a * b) * t) := by
        rw [h1]; exact mul_nonneg h2 hsn

/-- **Lower bound**: for `t ≥ 0`, `b Ω₀ ≥ 0` and `a b > 0`, the temperature component
dominates `Θ₀ * cosh (√(a b) t)`. -/
theorem rayleighTaylorSolution_fst_lower_bound (a b Θ₀ Ω₀ : ℝ) (hab : 0 < a * b)
    (_hΘ : 0 ≤ Θ₀) (hbΩ : 0 ≤ b * Ω₀) :
    ∀ t : ℝ, 0 ≤ t →
      Θ₀ * Real.cosh (Real.sqrt (a * b) * t)
        ≤ (rayleighTaylorSolution a b Θ₀ Ω₀ t).1 := by
  intro t ht
  have hsinh : 0 ≤ (b / Real.sqrt (a * b)) * Ω₀ * Real.sinh (Real.sqrt (a * b) * t) :=
    div_b_mul_sinh_nonneg hab hbΩ ht
  have hΘcosh : Θ₀ * Real.cosh (Real.sqrt (a * b) * t) ≤
      Θ₀ * Real.cosh (Real.sqrt (a * b) * t)
        + (b / Real.sqrt (a * b)) * Ω₀ * Real.sinh (Real.sqrt (a * b) * t) :=
    le_add_of_nonneg_right hsinh
  simpa [rayleighTaylorSolution] using hΘcosh

/-- **Exponential lower bound**: the temperature component is eventually bounded below
by the diverging expression `(Θ₀/2) exp(√(a b) t)`. -/
theorem rayleighTaylorSolution_exp_lower_bound (a b Θ₀ Ω₀ : ℝ) (hab : 0 < a * b)
    (hΘ : 0 < Θ₀) (hbΩ : 0 ≤ b * Ω₀) :
    ∀ᶠ t : ℝ in atTop,
      (Θ₀ / 2) * Real.exp (Real.sqrt (a * b) * t)
        ≤ (rayleighTaylorSolution a b Θ₀ Ω₀ t).1 := by
  have hω : (0:ℝ) < Real.sqrt (a * b) := Real.sqrt_pos.2 hab
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  have hcosh : Real.exp (Real.sqrt (a * b) * t) / 2
      ≤ Real.cosh (Real.sqrt (a * b) * t) := by
    rw [Real.cosh_eq, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    have hpos : 0 < Real.exp (-(Real.sqrt (a * b) * t)) := Real.exp_pos _
    linarith
  have h1 : (Θ₀ / 2) * Real.exp (Real.sqrt (a * b) * t)
      ≤ Θ₀ * Real.cosh (Real.sqrt (a * b) * t) := by
    calc (Θ₀ / 2) * Real.exp (Real.sqrt (a * b) * t)
        = Θ₀ * (Real.exp (Real.sqrt (a * b) * t) / 2) := by ring
      _ ≤ Θ₀ * Real.cosh (Real.sqrt (a * b) * t) :=
          mul_le_mul_of_nonneg_left hcosh (le_of_lt hΘ)
  exact le_trans h1 (rayleighTaylorSolution_fst_lower_bound a b Θ₀ Ω₀ hab (le_of_lt hΘ) hbΩ t ht)

/-- **Exponential growth / unboundedness.**  If `a * b > 0` (unstably stratified
background gradient), `Θ₀ > 0` and `b Ω₀ ≥ 0`, the temperature component of the
explicit solution tends to `+∞`; the growth is exponential at the Rayleigh–Taylor
rate `√(a b)`. -/
theorem rayleighTaylorSolution_unbounded (a b Θ₀ Ω₀ : ℝ) (hab : 0 < a * b) (hΘ : 0 < Θ₀)
    (hbΩ : 0 ≤ b * Ω₀) :
    Tendsto (fun t : ℝ => (rayleighTaylorSolution a b Θ₀ Ω₀ t).1) atTop atTop := by
  have hω : (0:ℝ) < Real.sqrt (a * b) := Real.sqrt_pos.2 hab
  have hcomp : Tendsto (fun t : ℝ => Real.sqrt (a * b) * t) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hω).2 tendsto_id
  have hexp : Tendsto (fun t : ℝ => Real.exp (Real.sqrt (a * b) * t)) atTop atTop :=
    tendsto_exp_atTop.comp hcomp
  have hbound : Tendsto (fun t : ℝ => (Θ₀ / 2) * Real.exp (Real.sqrt (a * b) * t))
      atTop atTop :=
    hexp.const_mul_atTop (by linarith : (0:ℝ) < Θ₀ / 2)
  exact tendsto_atTop_mono' atTop (rayleighTaylorSolution_exp_lower_bound a b Θ₀ Ω₀ hab hΘ hbΩ)
    hbound

/-! ### The stably stratified (`a b < 0`) oscillatory regime -/

/-- Explicit oscillatory solution of `Θ̇ = b Ω`, `Ω̇ = a Θ` for `a b < 0`, written with
`cos`/`sin` at the Brunt–Väisälä frequency `ν = √(-(a b))`.

Both `sin` cross-coefficients are positive: `b/ν` in `Θ` and `a/ν` in `Ω` (for
`a b > 0` these `cos`/`sin` become `cosh`/`sinh` with the same coefficient pattern). -/
def rayleighTaylorOscillation (a b Θ₀ Ω₀ : ℝ) (t : ℝ) : ℝ × ℝ :=
  (Θ₀ * Real.cos (Real.sqrt (-(a*b)) * t)
      + (b / Real.sqrt (-(a*b))) * Ω₀ * Real.sin (Real.sqrt (-(a*b)) * t),
   Ω₀ * Real.cos (Real.sqrt (-(a*b)) * t)
      + (a / Real.sqrt (-(a*b))) * Θ₀ * Real.sin (Real.sqrt (-(a*b)) * t))

/-- Derivative of `cos (c ·)`. -/
theorem hasDerivAt_cos_const_mul (c t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.cos (c * s)) (-(c * Real.sin (c * t))) t := by
  have h := (Real.hasDerivAt_cos (c * t)).comp t (hasDerivAt_const_mul c)
  rw [Function.comp_def] at h
  have h' : HasDerivAt (fun x : ℝ => Real.cos (c * x)) (-Real.sin (c * t) * c) t := h
  simpa only [neg_mul, mul_comm, mul_neg] using h'

/-- Derivative of `sin (c ·)`. -/
theorem hasDerivAt_sin_const_mul (c t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sin (c * s)) (c * Real.cos (c * t)) t := by
  have h := (Real.hasDerivAt_sin (c * t)).comp t (hasDerivAt_const_mul c)
  rw [Function.comp_def] at h
  simpa only [mul_comm] using h

/-- The oscillatory pair solves the amplitude ODE in the stably stratified regime. -/
theorem rayleighTaylorOscillation_hasDerivAt (a b Θ₀ Ω₀ : ℝ) (hab : a * b < 0) (t : ℝ) :
    HasDerivAt (fun s => (rayleighTaylorOscillation a b Θ₀ Ω₀ s).1)
      (b * (rayleighTaylorOscillation a b Θ₀ Ω₀ t).2) t ∧
    HasDerivAt (fun s => (rayleighTaylorOscillation a b Θ₀ Ω₀ s).2)
      (a * (rayleighTaylorOscillation a b Θ₀ Ω₀ t).1) t := by
  have hν : (0:ℝ) < Real.sqrt (-(a * b)) := Real.sqrt_pos.2 (by linarith)
  have hsq : Real.sqrt (-(a * b)) ^ 2 = -(a * b) :=
    Real.sq_sqrt (le_of_lt (by linarith : (0:ℝ) < -(a * b)))
  constructor
  · have h1 : HasDerivAt
        (fun s : ℝ => Θ₀ * Real.cos (Real.sqrt (-(a*b)) * s))
        (Θ₀ * (-(Real.sqrt (-(a*b)) * Real.sin (Real.sqrt (-(a*b)) * t)))) t :=
      (hasDerivAt_cos_const_mul (Real.sqrt (-(a*b))) t).const_mul Θ₀
    have h2 : HasDerivAt
        (fun s : ℝ => (b / Real.sqrt (-(a*b))) * Ω₀ * Real.sin (Real.sqrt (-(a*b)) * s))
        ((b / Real.sqrt (-(a*b))) * Ω₀ *
          (Real.sqrt (-(a*b)) * Real.cos (Real.sqrt (-(a*b)) * t))) t :=
      (hasDerivAt_sin_const_mul (Real.sqrt (-(a*b))) t).const_mul ((b / Real.sqrt (-(a*b))) * Ω₀)
    have hderiv := h1.add h2
    have hfun : (fun s : ℝ => (rayleighTaylorOscillation a b Θ₀ Ω₀ s).1)
        = fun s : ℝ => Θ₀ * Real.cos (Real.sqrt (-(a*b)) * s)
            + (b / Real.sqrt (-(a*b))) * Ω₀ * Real.sin (Real.sqrt (-(a*b)) * s) := by
      funext s; simp [rayleighTaylorOscillation]
    have hval : (rayleighTaylorOscillation a b Θ₀ Ω₀ t).2
        = Ω₀ * Real.cos (Real.sqrt (-(a*b)) * t)
          + (a / Real.sqrt (-(a*b))) * Θ₀ * Real.sin (Real.sqrt (-(a*b)) * t) := by
      simp [rayleighTaylorOscillation]
    rw [hfun, hval]
    refine (hderiv.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with s; rfl
    · field_simp
      ring_nf
      rw [hsq]
      ring
  · have h1 : HasDerivAt
        (fun s : ℝ => Ω₀ * Real.cos (Real.sqrt (-(a*b)) * s))
        (Ω₀ * (-(Real.sqrt (-(a*b)) * Real.sin (Real.sqrt (-(a*b)) * t)))) t :=
      (hasDerivAt_cos_const_mul (Real.sqrt (-(a*b))) t).const_mul Ω₀
    have h2 : HasDerivAt
        (fun s : ℝ => (a / Real.sqrt (-(a*b))) * Θ₀ * Real.sin (Real.sqrt (-(a*b)) * s))
        ((a / Real.sqrt (-(a*b))) * Θ₀ *
          (Real.sqrt (-(a*b)) * Real.cos (Real.sqrt (-(a*b)) * t))) t :=
      (hasDerivAt_sin_const_mul (Real.sqrt (-(a*b))) t).const_mul ((a / Real.sqrt (-(a*b))) * Θ₀)
    have hderiv := h1.add h2
    have hfun : (fun s : ℝ => (rayleighTaylorOscillation a b Θ₀ Ω₀ s).2)
        = fun s : ℝ => Ω₀ * Real.cos (Real.sqrt (-(a*b)) * s)
            + (a / Real.sqrt (-(a*b))) * Θ₀ * Real.sin (Real.sqrt (-(a*b)) * s) := by
      funext s; simp [rayleighTaylorOscillation]
    have hval : (rayleighTaylorOscillation a b Θ₀ Ω₀ t).1
        = Θ₀ * Real.cos (Real.sqrt (-(a*b)) * t)
          + (b / Real.sqrt (-(a*b))) * Ω₀ * Real.sin (Real.sqrt (-(a*b)) * t) := by
      simp [rayleighTaylorOscillation]
    rw [hfun, hval]
    refine (hderiv.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with s; rfl
    · field_simp
      ring_nf
      rw [hsq]
      ring

/-- **Boundedness in the stably stratified regime.**  For `a b < 0` the oscillatory
solution is bounded by a datum-dependent constant, so there is no growth. -/
theorem rayleighTaylorOscillation_bounded (a b Θ₀ Ω₀ : ℝ) (hab : a * b < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |(rayleighTaylorOscillation a b Θ₀ Ω₀ t).1| ≤ C
      ∧ |(rayleighTaylorOscillation a b Θ₀ Ω₀ t).2| ≤ C := by
  have hν : (0:ℝ) < Real.sqrt (-(a * b)) := Real.sqrt_pos.2 (by linarith)
  refine ⟨max (|Θ₀| + |b / Real.sqrt (-(a*b))| * |Ω₀|)
      (|Ω₀| + |a / Real.sqrt (-(a*b))| * |Θ₀|), ?_, ?_⟩
  · exact le_max_of_le_left (by positivity)
  · intro t
    have hcos : |Real.cos (Real.sqrt (-(a*b)) * t)| ≤ 1 := Real.abs_cos_le_one _
    have hsin : |Real.sin (Real.sqrt (-(a*b)) * t)| ≤ 1 := Real.abs_sin_le_one _
    constructor
    · refine le_trans ?_ (le_max_left _ _)
      calc |(rayleighTaylorOscillation a b Θ₀ Ω₀ t).1|
          = |Θ₀ * Real.cos (Real.sqrt (-(a*b)) * t)
              + (b / Real.sqrt (-(a*b))) * Ω₀ * Real.sin (Real.sqrt (-(a*b)) * t)| := by
            simp [rayleighTaylorOscillation]
        _ ≤ |Θ₀ * Real.cos (Real.sqrt (-(a*b)) * t)|
              + |(b / Real.sqrt (-(a*b))) * Ω₀ * Real.sin (Real.sqrt (-(a*b)) * t)| :=
            abs_add_le _ _
        _ = |Θ₀| * |Real.cos (Real.sqrt (-(a*b)) * t)|
              + (|b / Real.sqrt (-(a*b))| * |Ω₀|) * |Real.sin (Real.sqrt (-(a*b)) * t)| := by
            rw [abs_mul, abs_mul, abs_mul]
        _ ≤ |Θ₀| * 1 + (|b / Real.sqrt (-(a*b))| * |Ω₀|) * 1 := by
            gcongr
        _ = |Θ₀| + |b / Real.sqrt (-(a*b))| * |Ω₀| := by ring
    · refine le_trans ?_ (le_max_right _ _)
      calc |(rayleighTaylorOscillation a b Θ₀ Ω₀ t).2|
          = |Ω₀ * Real.cos (Real.sqrt (-(a*b)) * t)
              + (a / Real.sqrt (-(a*b))) * Θ₀ * Real.sin (Real.sqrt (-(a*b)) * t)| := by
            simp [rayleighTaylorOscillation]
        _ ≤ |Ω₀ * Real.cos (Real.sqrt (-(a*b)) * t)|
              + |(a / Real.sqrt (-(a*b))) * Θ₀ * Real.sin (Real.sqrt (-(a*b)) * t)| := abs_add_le _ _
        _ = |Ω₀| * |Real.cos (Real.sqrt (-(a*b)) * t)|
              + (|a / Real.sqrt (-(a*b))| * |Θ₀|) * |Real.sin (Real.sqrt (-(a*b)) * t)| := by
            rw [abs_mul, abs_mul, abs_mul]
        _ ≤ |Ω₀| * 1 + (|a / Real.sqrt (-(a*b))| * |Θ₀|) * 1 := by gcongr
        _ = |Ω₀| + |a / Real.sqrt (-(a*b))| * |Θ₀| := by ring

/-! ### The dichotomy

For the companion matrix `!![0, b; a, 0]`, the sign of the product `a * b` decides the
qualitative behaviour of the amplitude system:

* `a * b > 0` — **unstably stratified / Rayleigh–Taylor**: the growth rate is the real
  number `√(a b)`, and the temperature component grows exponentially (item 4 above).
* `a * b < 0` — **stably stratified**: the (real) growth rate `√(a b)` is `0` and the
  solution oscillates at the Brunt–Väisälä frequency `√(-(a b))` without growth
  (`rayleighTaylorOscillation_bounded`).
-/

/-- The scalar statement of the dichotomy: the growth rate `√(a b)` is positive exactly
in the unstably stratified regime `a b > 0`, and vanishes in the complementary regime. -/
theorem rayleighTaylor_growthRate_dichotomy (a b : ℝ) :
    (0 < a * b → 0 < Real.sqrt (a * b)) ∧ (a * b ≤ 0 → Real.sqrt (a * b) = 0) :=
  ⟨fun h => Real.sqrt_pos.2 h, fun h => Real.sqrt_eq_zero_of_nonpos h⟩

end Cascade

#print axioms Cascade.rayleighTaylorMatrix_mulVec
#print axioms Cascade.rayleighTaylor_charpoly
#print axioms Cascade.rayleighTaylor_eigenvector_pos
#print axioms Cascade.rayleighTaylor_eigenvector_neg
#print axioms Cascade.rayleighTaylorSolution_hasDerivAt_fst
#print axioms Cascade.rayleighTaylorSolution_hasDerivAt_snd
#print axioms Cascade.rayleighTaylorSolution_hasDerivAt
#print axioms Cascade.tendsto_cosh_atTop
#print axioms Cascade.tendsto_sinh_atTop
#print axioms Cascade.tendsto_cosh_const_mul_atTop
#print axioms Cascade.tendsto_sinh_const_mul_atTop
#print axioms Cascade.sinh_nonneg_of_nonneg
#print axioms Cascade.sinh_const_mul_nonneg
#print axioms Cascade.div_b_mul_sinh_nonneg
#print axioms Cascade.rayleighTaylorSolution_fst_lower_bound
#print axioms Cascade.rayleighTaylorSolution_exp_lower_bound
#print axioms Cascade.rayleighTaylorSolution_unbounded
#print axioms Cascade.hasDerivAt_cos_const_mul
#print axioms Cascade.hasDerivAt_sin_const_mul
#print axioms Cascade.rayleighTaylorOscillation_hasDerivAt
#print axioms Cascade.rayleighTaylorOscillation_bounded
#print axioms Cascade.rayleighTaylor_growthRate_dichotomy
