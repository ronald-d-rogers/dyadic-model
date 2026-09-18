/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cascade formalization
-/

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- Some standing model hypotheses (`0 ≤ a`, `0 ≤ S₀`, `0 < ν`) document the intended regime but
-- are not needed by the proofs below; silence the corresponding linter.
set_option linter.unusedVariables false

/-!
# The Grönwall engine for Stage O

This file is the **abstract engine** of the Stage-O obstruction for the unforced dyadic
Boussinesq model.  It is standalone: it does not import any `Cascade` model file.  Together with
`Cascade/Obstruction.lean` it yields *no finite-time energy blowup*.

## The model's inequality

For the unforced dyadic Boussinesq model one has, along a solution, the differential
inequality for the total energy `E = Σ k u_k²` and total temperature enstrophy
`S₀ = Σ k θ_k²`:

`E' ≤ 2 * κ * √(E t) * √S₀ - 2 * ν * E t`,  with `E ≥ 0`, `S₀ ≥ 0`, `ν > 0`, `κ ≥ 0`.

By AM–GM in the form `2 * √E ≤ 1 + E` (equivalent to `(√E - 1)² ≥ 0`) the buoyancy production
term is linearised:

`2 * κ * √S₀ * √E = κ * √S₀ * (2 * √E) ≤ κ * √S₀ * (1 + E)`,

so that

`E' ≤ a + b * E`,  with  `a := κ * √S₀`  and  `b := κ * √S₀ - 2 * ν`.

## What is proved

* `le_gronwallBound_of_hasDerivAt'` / `le_gronwallBound_of_hasDerivAt` — the linear Grönwall
  comparison, phrased for a plain derivative bound `f' t ≤ a + b * f t` (mathlib's
  `le_gronwallBound_of_liminf_deriv_right_le` is the tool used).
* `gronwallBound_le_max_of_neg` — when `b < 0`, the closed form of `gronwallBound` is bounded
  uniformly in time by `max δ (a / (-b))`.
* `energy_le_gronwallBound_of_rate_le` — the instantaneous Grönwall bound for the model's
  inequality.
* `energy_le_max_of_rate_le` — the *uniform in `T`* bound `E t ≤ max (E 0) (a / (-b))` in the
  dissipative case `b < 0`, i.e. `2ν > κ√S₀`.
* `energy_le_energyBound_of_rate_le` — an explicit finite bounding constant valid in **both**
  cases (uniform in `T` when `2ν > κ√S₀`, exponential in `T` otherwise).
* `no_finite_time_blowup` — the corollary: on every compact time interval `[0, T]` the energy is
  bounded by an explicit constant depending only on `E 0, κ, S₀, ν, T` (and hence cannot blow up
  at a finite time).

## A remark on the hypotheses

The brief asked for a derivative hypothesis on `[0, T)` only.  That is *not sufficient*: the
value at the right endpoint `E T` is then completely unconstrained (e.g. `E t = t` on `[0, T)`
with `E T = 10¹⁰⁰` satisfies every hypothesis), and the behaviour at `t = 0⁺` is likewise
unconstrained (e.g. `E t = exp (-2νt) / t` on `(0, T]`, `E 0 = 0`, satisfies the rate bound with
`S₀ = 0`, yet is unbounded as `t → 0⁺`).  Accordingly the statements below carry a continuity
hypothesis.  For the interval statements this is `ContinuousOn E (Icc 0 T)`.  For
`no_finite_time_blowup` the derivative is assumed on all of `(0, ∞)` (so it already gives
continuity at the right endpoint), and only the minimal `ContinuousAt E 0` is added; the value at
`t = 0` is then controlled by a limiting argument based on continuity at `0`.
-/

namespace Cascade

open Filter Set

open scoped Topology

/-! ### 1. Linear Grönwall comparison -/

/-- **Linear Grönwall comparison (arbitrary left endpoint).**  If `f` is continuous on `[c, T]`,
has derivative `f'` on `[c, T)`, and `f' t ≤ a + b * f t` there, then
`f t ≤ gronwallBound (f c) b a (t - c)` on `[c, T]`.  This is mathlib's
`le_gronwallBound_of_liminf_deriv_right_le` with `a = c`, `b = T`, `δ = f c`, `K = b`, `ε = a`. -/
theorem le_gronwallBound_of_hasDerivAt' {f f' : ℝ → ℝ} {a b c T : ℝ}
    (hcont : ContinuousOn f (Set.Icc c T))
    (hderiv : ∀ t ∈ Set.Ico c T, HasDerivAt f (f' t) t)
    (hineq : ∀ t ∈ Set.Ico c T, f' t ≤ a + b * f t) :
    ∀ t ∈ Set.Icc c T, f t ≤ gronwallBound (f c) b a (t - c) :=
  le_gronwallBound_of_liminf_deriv_right_le (a := c) (b := T) (δ := f c) (K := b) (ε := a)
    hcont
    (fun x hx r hr => by
      simpa only [slope_def_field, div_eq_inv_mul] using
        (hderiv x hx).hasDerivWithinAt.liminf_right_slope_le hr)
    le_rfl (fun x hx => by linarith [hineq x hx])

/-- **Linear Grönwall comparison.**  If `f` is continuous on `[0, T]`, has derivative `f'` on
`[0, T)`, and `f' t ≤ a + b * f t` there, then `f t ≤ gronwallBound (f 0) b a t` on `[0, T]`. -/
theorem le_gronwallBound_of_hasDerivAt {f f' : ℝ → ℝ} {a b T : ℝ}
    (hcont : ContinuousOn f (Set.Icc 0 T))
    (hderiv : ∀ t ∈ Set.Ico 0 T, HasDerivAt f (f' t) t)
    (hineq : ∀ t ∈ Set.Ico 0 T, f' t ≤ a + b * f t) :
    ∀ t ∈ Set.Icc 0 T, f t ≤ gronwallBound (f 0) b a t := by
  intro t ht
  simpa using le_gronwallBound_of_hasDerivAt' (c := 0) hcont hderiv hineq t ht

/-! ### 2. Explicit uniform bound when `b < 0` -/

/-- If `b < 0` and `a ≥ 0`, the Grönwall bound is bounded uniformly in time by
`max δ (a / (-b))`.  Indeed for `c = -b > 0`
`gronwallBound δ b a t = a / c + exp (b * t) * (δ - a / c)`, and `exp (b * t) ∈ (0, 1]` for
`t ≥ 0`. -/
theorem gronwallBound_le_max_of_neg {δ a b t : ℝ} (hb : b < 0) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    gronwallBound δ b a t ≤ max δ (a / (-b)) := by
  have hbne : b ≠ 0 := ne_of_lt hb
  have hbt : b * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hb) ht
  have hexp_le : Real.exp (b * t) ≤ 1 := Real.exp_le_one_iff.mpr hbt
  have hexp_nonneg : 0 ≤ Real.exp (b * t) := (Real.exp_pos _).le
  have hkey : gronwallBound δ b a t = a / (-b) + Real.exp (b * t) * (δ - a / (-b)) := by
    rw [gronwallBound_of_K_ne_0 hbne]
    field_simp
    ring
  rw [hkey]
  rcases le_or_gt δ (a / (-b)) with hδ | hδ
  · have hterm : Real.exp (b * t) * (δ - a / (-b)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hexp_nonneg (sub_nonpos.mpr hδ)
    have : a / (-b) + Real.exp (b * t) * (δ - a / (-b)) ≤ a / (-b) := by linarith
    exact this.trans (le_max_right _ _)
  · have hpos : 0 ≤ δ - a / (-b) := (sub_pos.mpr hδ).le
    have hterm : Real.exp (b * t) * (δ - a / (-b)) ≤ δ - a / (-b) :=
      mul_le_of_le_one_left hpos hexp_le
    have : a / (-b) + Real.exp (b * t) * (δ - a / (-b)) ≤ δ := by linarith
    exact this.trans (le_max_left _ _)

/-- `gronwallBound` is monotone in its initial value `δ`. -/
theorem gronwallBound_mono_left {δ₁ δ₂ a b x : ℝ} (h : δ₁ ≤ δ₂) :
    gronwallBound δ₁ b a x ≤ gronwallBound δ₂ b a x := by
  rcases eq_or_ne b 0 with hb | hb
  · subst hb
    rw [gronwallBound_K0 δ₁ a, gronwallBound_K0 δ₂ a]
    linarith
  · rw [gronwallBound_of_K_ne_0 hb, gronwallBound_of_K_ne_0 hb]
    have := mul_le_mul_of_nonneg_right h (Real.exp_pos (b * x)).le
    linarith

/-- `gronwallBound δ b a x ≥ δ` whenever `δ, a, b, x ≥ 0`. -/
theorem le_gronwallBound_self {δ a b x : ℝ} (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) : δ ≤ gronwallBound δ b a x := by
  rcases eq_or_lt_of_le hb with hb0 | hbpos
  · subst hb0
    rw [gronwallBound_K0 δ a]
    linarith [mul_nonneg ha hx]
  · rw [gronwallBound_of_K_ne_0 (ne_of_gt hbpos)]
    have hexp1 : 1 ≤ Real.exp (b * x) := Real.one_le_exp (by positivity)
    have hterm : 0 ≤ a / b * (Real.exp (b * x) - 1) :=
      mul_nonneg (div_nonneg ha hb) (sub_nonneg.mpr hexp1)
    have : 0 ≤ δ * (Real.exp (b * x) - 1) := mul_nonneg hδ (sub_nonneg.mpr hexp1)
    linarith

/-! ### 3. The model's actual shape -/

/-- **Instantaneous Grönwall bound for the unforced dyadic Boussinesq energy (arbitrary left
endpoint).**  Assuming the energy is nonnegative on `[c, T]`, differentiable on `[c, T)` with
`E' ≤ 2 * κ * √(E t) * √S₀ - 2 * ν * E t`, and continuous on `[c, T]`, the AM–GM step
`2 * √E ≤ 1 + E` yields the linear rate bound `E' ≤ a + b * E` with
`a = κ * √S₀`, `b = κ * √S₀ - 2 * ν`, and hence `E t ≤ gronwallBound (E c) b a (t - c)`. -/
theorem energy_le_gronwallBound_of_rate_le' {E E' : ℝ → ℝ} {κ S₀ ν c T : ℝ}
    (hκ : 0 ≤ κ) (hS : 0 ≤ S₀) (hν : 0 < ν)
    (hcont : ContinuousOn E (Set.Icc c T))
    (hE : ∀ t ∈ Set.Icc c T, 0 ≤ E t)
    (hderiv : ∀ t ∈ Set.Ico c T, HasDerivAt E (E' t) t)
    (hrate : ∀ t ∈ Set.Ico c T,
      E' t ≤ 2 * κ * Real.sqrt S₀ * Real.sqrt (E t) - 2 * ν * E t) :
    ∀ t ∈ Set.Icc c T,
      E t ≤ gronwallBound (E c) (κ * Real.sqrt S₀ - 2 * ν) (κ * Real.sqrt S₀) (t - c) := by
  refine le_gronwallBound_of_hasDerivAt' hcont hderiv ?_
  intro t ht
  have ht0 : 0 ≤ E t := hE t ⟨ht.1, le_of_lt ht.2⟩
  have hamgm : 2 * Real.sqrt (E t) ≤ 1 + E t := by
    have h := sq_nonneg (Real.sqrt (E t) - 1)
    rw [sub_sq, Real.sq_sqrt ht0] at h
    nlinarith
  have hA : 0 ≤ κ * Real.sqrt S₀ := mul_nonneg hκ (Real.sqrt_nonneg S₀)
  have hle : 2 * κ * Real.sqrt S₀ * Real.sqrt (E t) ≤ κ * Real.sqrt S₀ * (1 + E t) := by
    have h := mul_le_mul_of_nonneg_left hamgm hA
    nlinarith [h]
  calc E' t ≤ 2 * κ * Real.sqrt S₀ * Real.sqrt (E t) - 2 * ν * E t := hrate t ht
    _ ≤ κ * Real.sqrt S₀ * (1 + E t) - 2 * ν * E t := by linarith
    _ = κ * Real.sqrt S₀ + (κ * Real.sqrt S₀ - 2 * ν) * E t := by ring

/-- **Instantaneous Grönwall bound for the unforced dyadic Boussinesq energy.** -/
theorem energy_le_gronwallBound_of_rate_le {E E' : ℝ → ℝ} {κ S₀ ν T : ℝ}
    (hκ : 0 ≤ κ) (hS : 0 ≤ S₀) (hν : 0 < ν)
    (hcont : ContinuousOn E (Set.Icc 0 T))
    (hE : ∀ t ∈ Set.Icc 0 T, 0 ≤ E t)
    (hderiv : ∀ t ∈ Set.Ico 0 T, HasDerivAt E (E' t) t)
    (hrate : ∀ t ∈ Set.Ico 0 T,
      E' t ≤ 2 * κ * Real.sqrt S₀ * Real.sqrt (E t) - 2 * ν * E t) :
    ∀ t ∈ Set.Icc 0 T,
      E t ≤ gronwallBound (E 0) (κ * Real.sqrt S₀ - 2 * ν) (κ * Real.sqrt S₀) t := by
  intro t ht
  simpa using
    energy_le_gronwallBound_of_rate_le' (c := 0) hκ hS hν hcont hE hderiv hrate t ht

/-- **Uniform-in-time bound in the dissipative case `2ν > κ√S₀`.**  Under the hypotheses of
`energy_le_gronwallBound_of_rate_le`, if `b = κ√S₀ - 2ν < 0` then
`E t ≤ max (E 0) (κ√S₀ / (2ν - κ√S₀))` for all `t ∈ [0, T]`; the right-hand side does not
depend on `T`. -/
theorem energy_le_max_of_rate_le {E E' : ℝ → ℝ} {κ S₀ ν T : ℝ}
    (hκ : 0 ≤ κ) (hS : 0 ≤ S₀) (hν : 0 < ν)
    (hgap : 0 < 2 * ν - κ * Real.sqrt S₀)
    (hcont : ContinuousOn E (Set.Icc 0 T))
    (hE : ∀ t ∈ Set.Icc 0 T, 0 ≤ E t)
    (hderiv : ∀ t ∈ Set.Ico 0 T, HasDerivAt E (E' t) t)
    (hrate : ∀ t ∈ Set.Ico 0 T,
      E' t ≤ 2 * κ * Real.sqrt S₀ * Real.sqrt (E t) - 2 * ν * E t) :
    ∀ t ∈ Set.Icc 0 T,
      E t ≤ max (E 0) (κ * Real.sqrt S₀ / (2 * ν - κ * Real.sqrt S₀)) := by
  intro t ht
  have hb : κ * Real.sqrt S₀ - 2 * ν < 0 := by linarith
  have hg := gronwallBound_le_max_of_neg (δ := E 0) (a := κ * Real.sqrt S₀)
    (b := κ * Real.sqrt S₀ - 2 * ν) (t := t) hb (mul_nonneg hκ (Real.sqrt_nonneg S₀)) ht.1
  have hle := energy_le_gronwallBound_of_rate_le hκ hS hν hcont hE hderiv hrate t ht
  refine hle.trans ?_
  simpa only [neg_sub] using hg

/-- An explicit finite bounding constant for the energy on `[0, T]`, valid in both cases:
`max (E 0) (a / (-b))` when `b < 0` (uniform in `T`), and the exponential `gronwallBound` at
time `T` when `b ≥ 0`. -/
noncomputable def energyBound (E0 κ S₀ ν T : ℝ) : ℝ :=
  if κ * Real.sqrt S₀ - 2 * ν < 0
    then max E0 (κ * Real.sqrt S₀ / (2 * ν - κ * Real.sqrt S₀))
    else gronwallBound E0 (κ * Real.sqrt S₀ - 2 * ν) (κ * Real.sqrt S₀) T

/-- **The energy is bounded on `[c, T]` by an explicit constant** depending only on
`E c, κ, S₀, ν, T`, in both the dissipative (`2ν > κ√S₀`) and non-dissipative (`2ν ≤ κ√S₀`)
cases. -/
theorem energy_le_energyBound_of_rate_le' {E E' : ℝ → ℝ} {κ S₀ ν c T : ℝ}
    (hκ : 0 ≤ κ) (hS : 0 ≤ S₀) (hν : 0 < ν) (hc : 0 ≤ c) (hcT : c ≤ T)
    (hcont : ContinuousOn E (Set.Icc c T))
    (hE : ∀ t ∈ Set.Icc c T, 0 ≤ E t)
    (hderiv : ∀ t ∈ Set.Ico c T, HasDerivAt E (E' t) t)
    (hrate : ∀ t ∈ Set.Ico c T,
      E' t ≤ 2 * κ * Real.sqrt S₀ * Real.sqrt (E t) - 2 * ν * E t) :
    ∀ t ∈ Set.Icc c T, E t ≤ energyBound (E c) κ S₀ ν T := by
  intro t ht
  by_cases hb : κ * Real.sqrt S₀ - 2 * ν < 0
  · rw [energyBound, ite_eq_left hb]
    have hg := gronwallBound_le_max_of_neg (δ := E c) (a := κ * Real.sqrt S₀)
      (b := κ * Real.sqrt S₀ - 2 * ν) (t := t - c) hb
      (mul_nonneg hκ (Real.sqrt_nonneg S₀)) (by linarith [ht.1])
    have hle := energy_le_gronwallBound_of_rate_le' hκ hS hν hcont hE hderiv hrate t ht
    refine hle.trans ?_
    simpa only [neg_sub] using hg
  · rw [energyBound, ite_eq_right hb]
    have hbnonneg : 0 ≤ κ * Real.sqrt S₀ - 2 * ν := not_lt.mp hb
    have hmono := gronwallBound_mono (δ := E c) (K := κ * Real.sqrt S₀ - 2 * ν)
      (ε := κ * Real.sqrt S₀) (hE c ⟨le_rfl, hcT⟩) (mul_nonneg hκ (Real.sqrt_nonneg S₀))
      hbnonneg
    have ht' : t - c ≤ T := by linarith [ht.2, hc]
    exact (energy_le_gronwallBound_of_rate_le' hκ hS hν hcont hE hderiv hrate t ht).trans
      (hmono ht')

/-- **The energy is bounded on `[0, T]` by an explicit constant** depending only on
`E 0, κ, S₀, ν, T`. -/
theorem energy_le_energyBound_of_rate_le {E E' : ℝ → ℝ} {κ S₀ ν T : ℝ}
    (hκ : 0 ≤ κ) (hS : 0 ≤ S₀) (hν : 0 < ν) (hT : 0 ≤ T)
    (hcont : ContinuousOn E (Set.Icc 0 T))
    (hE : ∀ t ∈ Set.Icc 0 T, 0 ≤ E t)
    (hderiv : ∀ t ∈ Set.Ico 0 T, HasDerivAt E (E' t) t)
    (hrate : ∀ t ∈ Set.Ico 0 T,
      E' t ≤ 2 * κ * Real.sqrt S₀ * Real.sqrt (E t) - 2 * ν * E t) :
    ∀ t ∈ Set.Icc 0 T, E t ≤ energyBound (E 0) κ S₀ ν T :=
  energy_le_energyBound_of_rate_le' hκ hS hν le_rfl hT hcont hE hderiv hrate

/-- `energyBound` is monotone in its initial energy. -/
theorem energyBound_mono_left {E₀ E₁ κ S₀ ν T : ℝ} (h : E₀ ≤ E₁) :
    energyBound E₀ κ S₀ ν T ≤ energyBound E₁ κ S₀ ν T := by
  unfold energyBound
  by_cases hb : κ * Real.sqrt S₀ - 2 * ν < 0
  · rw [ite_eq_left hb, ite_eq_left hb]
    exact max_le_max h le_rfl
  · rw [ite_eq_right hb, ite_eq_right hb]
    exact gronwallBound_mono_left h

/-- The initial energy is below `energyBound`. -/
theorem le_energyBound_self {E₀ κ S₀ ν T : ℝ} (hE₀ : 0 ≤ E₀) (hκ : 0 ≤ κ) (hS : 0 ≤ S₀)
    (hT : 0 ≤ T) : E₀ ≤ energyBound E₀ κ S₀ ν T := by
  unfold energyBound
  split_ifs with hb
  · exact le_max_left _ _
  · exact le_gronwallBound_self hE₀ (mul_nonneg hκ (Real.sqrt_nonneg S₀)) (not_lt.mp hb) hT

/-! ### 4. No finite-time blowup -/

/-- **No finite-time energy blowup.**  If the energy is nonnegative on `[0, ∞)`, continuous at
`0`, differentiable on `(0, ∞)` with the model rate bound there, then on every compact interval
`[0, T]` it is bounded by the explicit constant `energyBound (E 0 + 1) κ S₀ ν T`.  This is the
abstract content of the Stage-O obstruction: the unforced dyadic Boussinesq model cannot develop
a finite-time energy blowup. -/
theorem no_finite_time_blowup {E E' : ℝ → ℝ} {κ S₀ ν : ℝ}
    (hκ : 0 ≤ κ) (hS : 0 ≤ S₀) (hν : 0 < ν)
    (hcont0 : ContinuousAt E 0)
    (hE : ∀ t, 0 ≤ t → 0 ≤ E t)
    (hderiv : ∀ t, 0 < t → HasDerivAt E (E' t) t)
    (hrate : ∀ t, 0 < t → E' t ≤ 2 * κ * Real.sqrt S₀ * Real.sqrt (E t) - 2 * ν * E t)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, E t ≤ C := by
  -- Continuity at `0` bounds the energy near `0` by `E 0 + 1`.
  obtain ⟨ε, hεpos, hε⟩ := Metric.continuousAt_iff.mp hcont0 1 zero_lt_one
  refine ⟨energyBound (E 0 + 1) κ S₀ ν T, ?_⟩
  intro t ht
  rcases eq_or_lt_of_le ht.1 with ht0 | htpos
  · -- `t = 0`: use `E 0 ≤ E 0 + 1 ≤ energyBound (E 0 + 1) …`.
    subst ht0
    have h1 : E 0 + 1 ≤ energyBound (E 0 + 1) κ S₀ ν T :=
      le_energyBound_self (E₀ := E 0 + 1) (by linarith [hE 0 le_rfl]) hκ hS hT
    linarith
  · -- `t > 0`: restart Grönwall from a small time `s > 0` where `E s ≤ E 0 + 1`.
    set s : ℝ := min (t / 2) (ε / 2) with hsdef
    have hspos : 0 < s := lt_min (by linarith) (by linarith)
    have hst : s < t := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hsε : s < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hsT : s < T := lt_of_lt_of_le hst ht.2
    have hEs : E s ≤ E 0 + 1 := by
      have hs_dist : dist s 0 < ε := by
        simpa [Real.dist_eq, abs_of_pos hspos] using hsε
      have h := hε hs_dist
      rw [Real.dist_eq] at h
      linarith [(abs_lt.mp h).2]
    have hcontOn : ContinuousOn E (Set.Icc s T) := fun x hx =>
      (hderiv x (lt_of_lt_of_le hspos hx.1)).continuousAt.continuousWithinAt
    have hres : E t ≤ energyBound (E s) κ S₀ ν T :=
      energy_le_energyBound_of_rate_le' hκ hS hν hspos.le (le_of_lt hsT) hcontOn
        (fun x hx => hE x (le_of_lt (lt_of_lt_of_le hspos hx.1)))
        (fun x hx => hderiv x (lt_of_lt_of_le hspos hx.1))
        (fun x hx => hrate x (lt_of_lt_of_le hspos hx.1))
        t ⟨le_of_lt hst, ht.2⟩
    exact hres.trans (energyBound_mono_left hEs)

/-! ### Axiom audit -/

#print axioms le_gronwallBound_of_hasDerivAt'
#print axioms le_gronwallBound_of_hasDerivAt
#print axioms gronwallBound_le_max_of_neg
#print axioms gronwallBound_mono_left
#print axioms le_gronwallBound_self
#print axioms energy_le_gronwallBound_of_rate_le'
#print axioms energy_le_gronwallBound_of_rate_le
#print axioms energy_le_max_of_rate_le
#print axioms energy_le_energyBound_of_rate_le'
#print axioms energy_le_energyBound_of_rate_le
#print axioms energyBound_mono_left
#print axioms le_energyBound_self
#print axioms no_finite_time_blowup

end Cascade
