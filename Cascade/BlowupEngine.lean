/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cascade formalization
-/

import Cascade.DissipationThreshold
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The blowup engine for the truncated dyadic model with weak dissipation

This file is the **positive** counterpart of `Cascade/Riccati.lean`.  The engines there bound a
quantity from *above* (no blowup); here we prove the reverse implication: `y' ≥ c · y^{3/2}` forces
`y` to reach infinity by the finite time `2 / (c √y₀)`.  The file is standalone with respect to the
rest of the blowup argument: it depends only on `Cascade.DissipationThreshold` (for `dyadicWeight`)
and Mathlib.

**Currently unused.**  This file is abstract — a reversed-Bernoulli ODE engine, an inverted Hölder
inequality and some elementary inequalities — and is independent of any solution predicate, so it
is mathematically correct.  But its only consumers were `Cascade/BlowupRate.lean` and
`Cascade/BlowupDegreeZero.lean`, both of which have been **deleted**: with the repaired truncated
predicate (equations on the retained shells `0 ≤ k < N` only) the truncated model has no finite-time
blowup, so the blowup capstone is not merely vacuous but false.  Nothing here is unsound; the file
is simply retained as an abstract engine in case a future untruncated-lattice argument needs it.

## Contents

1. **The reversed Bernoulli engine.**  `le_of_deriv_ge_mul_sqrt` and its non-existence forms
   `not_solution_of_gt`, `not_exists_solution_of_gt`.  The route is the substitution
   `f t = 1 / √(y t)`, whose derivative is `f' t = - y' t / (2 (√(y t))³) ≤ -c/2`; hence
   `t ↦ f t + c t / 2` is non-increasing, and `0 < f t` gives `T < 2 / (c √y₀)`.

2. **Two elementary inequalities** (Cheskidov's (5.3)–(5.4)): `x y² ≤ ½y³ + 2x²y` and
   `x y z ≤ ½x²y + ¼z³ + y²z` for `x, y, z ≥ 0`, plus the general-`λ` version of (5.4).

3. **The inverted Hölder lemma** `inverted_holder`.  For the truncation shells `k < N`, an integer
   dissipation degree `e ≤ 0` and `ε = 1 - 3e ≥ 1`,

   `√((2^ε - 1)/2^ε) · S · √S ≤ Σ_{k<N} 2^{2k} |u_k|³`,   where `S = Σ_{k<N} 2^{(e+1)k} u_k²`.

   With `γ = 1/2`, `α = e/2`, write `2^{(e+1)k} u_k² = (2^{2k} u_k²) · (2^{-εk})` and apply the
   *weighted AM–GM inequality* `(2/3)X + (1/3)Y ≥ X^{2/3}Y^{1/3}` with
   `X = 2^{2k} u_k²`, `Y = 2^{-2εk}·2^{2k}u_k²`; summing over `k < N` and applying the finite
   geometric bound `Σ_{k<N} 2^{-εk} ≤ 2^ε/(2^ε - 1) = A^{-2}` gives
   `S ≤ G·Σ_{k<N}2^{2k}|u_k|³ + G^{-1}... ` — concretely the sharp chain

   `S³ ≤ (Σ_{k<N} 2^{-εk}) · (Σ_{k<N} 2^{2k}|u_k|³)²`,

   and hence `A²S³ ≤ (Σ_{k<N}2^{2k}|u_k|³)²`, i.e. the statement.  The *truncated* geometric sum is
   what makes the constant exact: `A²·Σ_{k<N}2^{-εk} ≤ 1` for every `N`, with equality only in the
   limit `N → ∞`.

   The inequality is **sharp**: for `e = 0`, `N = 1` and `u = δ₀` both sides are `A·1·1` and `1`,
   with `A = √(1/2) < 1`; the constant `A` cannot be replaced by `1`.

4. **Range of `A`**: `0 < A(ε) ≤ 1` for `ε > 0`.  (`A` is *increasing* in `ε`, not antitone:
   `A(1)² = 1/2` while `A(2)² = 3/4` — an earlier draft of this file asserted the opposite.)

Every exponent below is an integer (`zpow`); every occurrence of a `3/2` power is written as
`x * Real.sqrt x`.  The only appeal to `Real.rpow` is in the two private helper lemmas that package
the discrete Hölder inequality (`sum_rpow_holder`, `dyadicWeight_pointwise`), where the fractional
exponents `1/3`, `2/3` are unavoidable; all statements of this file keep integer exponents and
`Real.sqrt`.
-/
noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators

namespace Cascade

/-! ## 1. The reversed Bernoulli engine -/

/-- **Mean-value monotonicity comparison.**  If `g` is continuous on `[0, T]`, `T > 0`, with
`g' t ≤ 0` on `[0, T]`, then `g T ≤ g 0` (the mean value theorem on `[0, T]`). -/
theorem le_of_deriv_nonpos_of_hasDerivAt {g g' : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn g (Set.Icc 0 T))
    (hderiv : ∀ t ∈ Set.Icc 0 T, HasDerivAt g (g' t) t)
    (hineq : ∀ t ∈ Set.Icc 0 T, g' t ≤ 0) :
    g T ≤ g 0 := by
  have hderiv' : ∀ s ∈ Set.Ioo (0:ℝ) T, HasDerivAt g (g' s) s := fun s hs =>
    hderiv s ⟨hs.1.le, hs.2.le⟩
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope g g' hT hcont hderiv'
  have hξ' : g' ξ ≤ 0 := hineq ξ ⟨hξ.1.le, hξ.2.le⟩
  rw [hξeq] at hξ'
  have hden : (0:ℝ) < T - 0 := by linarith
  rw [div_le_iff₀ hden] at hξ'
  linarith

/-- **The reversed Bernoulli engine.**  If `y > 0` on `[0, T]` (`0 ≤ T`) with `y' ≥ c · y · √y`
there and `y 0 = y₀ > 0`, then `T ≤ 2 / (c · √y₀)`.

This is the finite-time blowup rate of the `3/2`-Bernoulli inequality: the reciprocal of `√y`
decreases at least linearly, so `y` is forced to infinity by time `2/(c√y₀)` at the latest.

The hypothesis `0 ≤ T` is the natural one for an interval `[0, T]`; it is in fact derivable from the
others plus `0 < y₀ = y 0` and `y > 0` at `T` (if `T < 0` then `T ∈ [0,T]` and `0 ∈ [0,T]` force
`y 0 > 0` and `y 0 ≤ 0`), but keeping it as a hypothesis avoids a degenerate-endpoint detour. -/
theorem le_of_deriv_ge_mul_sqrt (y y' : ℝ → ℝ) {c y₀ T : ℝ} (hc : 0 < c) (hy₀ : 0 < y₀)
    (hT : 0 < T)
    (hderiv : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (y' t) t)
    (hineq : ∀ t ∈ Set.Icc 0 T, c * (y t * Real.sqrt (y t)) ≤ y' t)
    (hpos : ∀ t ∈ Set.Icc 0 T, 0 < y t) (hy0 : y 0 = y₀) :
    T ≤ 2 / (c * Real.sqrt y₀) := by
  have hTpos : 0 < T := hT
  have hTle : (0:ℝ) ≤ T := hT.le
  clear hT

  set f : ℝ → ℝ := fun t => 1 / Real.sqrt (y t) with hf
  set g : ℝ → ℝ := fun t => f t + c * t / 2 with hg
  have hderiv_f : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt f (-(y' t) / (2 * (Real.sqrt (y t)) ^ 3)) t := by
    intro t ht
    have hyt : 0 < y t := hpos t ht
    have hsq : HasDerivAt (fun s => Real.sqrt (y s))
        (y' t * (1 / (2 * Real.sqrt (y t)))) t := by
      have h := (Real.hasDerivAt_sqrt (ne_of_gt hyt)).comp t (hderiv t ht)
      simpa [Function.comp_def, mul_comm] using h
    have hinv := HasDerivAt.div (hasDerivAt_const t (1:ℝ)) hsq
      (ne_of_gt (Real.sqrt_pos.mpr hyt))
    have hval : (0 * Real.sqrt (y t) - 1 * (y' t * (1 / (2 * Real.sqrt (y t)))))
          / (Real.sqrt (y t)) ^ 2 = -(y' t) / (2 * (Real.sqrt (y t)) ^ 3) := by
      field_simp
      ring
    have hfun : ((fun _ : ℝ => (1:ℝ)) / fun s => Real.sqrt (y s)) = f := by
      funext s; rfl
    rw [hfun, hval] at hinv
    exact hinv
  have hderiv_g : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt g (-(y' t) / (2 * (Real.sqrt (y t)) ^ 3) + c / 2) t := by
    intro t ht
    have hyt : 0 < y t := hpos t ht
    have hf : HasDerivAt f (-(y' t) / (2 * (Real.sqrt (y t)) ^ 3)) t := by
      rw [hf]
      exact hderiv_f t ht
    have h1 : HasDerivAt (fun s : ℝ => c * s / 2) (c / 2) t := by
      simpa using ((hasDerivAt_id t).const_mul c).div_const 2
    have h2 := hf.add h1
    rw [hg]
    exact h2
  have hmono : ∀ t ∈ Set.Icc 0 T,
      -(y' t) / (2 * (Real.sqrt (y t)) ^ 3) + c / 2 ≤ 0 := by
    intro t ht
    have hyt : 0 < y t := hpos t ht
    have hcube : y t * Real.sqrt (y t) = (Real.sqrt (y t)) ^ 3 := by
      rw [show (Real.sqrt (y t)) ^ 3 = (Real.sqrt (y t)) ^ 2 * Real.sqrt (y t) by ring,
        Real.sq_sqrt hyt.le]
    have hkey : c * (Real.sqrt (y t)) ^ 3 ≤ y' t := by
      rw [← hcube]; exact hineq t ht
    have hden : 0 < 2 * (Real.sqrt (y t)) ^ 3 := by positivity
    rw [show -(y' t) / (2 * (Real.sqrt (y t)) ^ 3) + c / 2
          = (c * (Real.sqrt (y t)) ^ 3 - y' t) / (2 * (Real.sqrt (y t)) ^ 3) by
      field_simp; ring]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
  have hcont : ContinuousOn g (Set.Icc 0 T) := by
    intro t ht
    exact ((hderiv_g t ht).continuousAt).continuousWithinAt
  have hbound : f T + c * T / 2 ≤ 1 / Real.sqrt y₀ := by
    have h := le_of_deriv_nonpos_of_hasDerivAt hTpos hcont hderiv_g hmono
    have hg0 : g 0 = 1 / Real.sqrt y₀ := by simp [hg, hf, hy0]
    have hgT : g T = f T + c * T / 2 := rfl
    rw [hgT, hg0] at h
    exact h
  have hfTpos : 0 < f T := by
    rw [hf]
    exact one_div_pos.mpr (Real.sqrt_pos.mpr (hpos T ⟨hTle, le_rfl⟩))
  have hden : 0 < c * Real.sqrt y₀ := mul_pos hc (Real.sqrt_pos.mpr hy₀)
  rw [le_div_iff₀ hden]
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hy₀)] at hbound
  nlinarith [hbound, hfTpos, hden, Real.sq_sqrt hy₀.le, hTle]

/-- **Reversed Bernoulli engine, non-existence form.**  If `c, y₀ > 0`, `0 ≤ T` and
`T > 2 / (c √y₀)`, there is *no* positive solution of `y' ≥ c · y √y` on `[0, T]` with
`y 0 = y₀`: every such solution blows up at or before `2 / (c √y₀)`. -/
theorem not_solution_of_gt (y y' : ℝ → ℝ) {c y₀ T : ℝ} (hc : 0 < c) (hy₀ : 0 < y₀)
    (hT : 0 < T)
    (hderiv : ∀ t ∈ Set.Icc 0 T, HasDerivAt y (y' t) t)
    (hineq : ∀ t ∈ Set.Icc 0 T, c * (y t * Real.sqrt (y t)) ≤ y' t)
    (hpos : ∀ t ∈ Set.Icc 0 T, 0 < y t) (hy0 : y 0 = y₀)
    (hgt : 2 / (c * Real.sqrt y₀) < T) : False := by
  have hle := le_of_deriv_ge_mul_sqrt y y' hc hy₀ hT hderiv hineq hpos hy0
  linarith

/-- **Reversed Bernoulli engine, packaged non-existence.**  No positive solution of
`y' ≥ c y√y`, `y 0 = y₀` exists on `[0, T]` beyond the critical time `2/(c√y₀)`. -/
theorem not_exists_solution_of_gt {c y₀ T : ℝ} (hc : 0 < c) (hy₀ : 0 < y₀) (hT : 0 < T)
    (hgt : 2 / (c * Real.sqrt y₀) < T) :
    ¬ ∃ (y y' : ℝ → ℝ), (∀ t ∈ Set.Icc 0 T, HasDerivAt y (y' t) t) ∧
      (∀ t ∈ Set.Icc 0 T, c * (y t * Real.sqrt (y t)) ≤ y' t) ∧
      (∀ t ∈ Set.Icc 0 T, 0 < y t) ∧ y 0 = y₀ := by
  rintro ⟨y, y', hderiv, hineq, hpos, hy0⟩
  exact not_solution_of_gt y y' hc hy₀ hT hderiv hineq hpos hy0 hgt

/-! ## 2. The two elementary inequalities (Cheskidov (5.3)–(5.4)) -/

/-- **Cheskidov (5.3).**  For `x, y ≥ 0`, `x y² ≤ ½ y³ + 2 x² y`.  Split on `x ≤ y/2`: in both
cases the difference of the two sides is a sum of manifestly nonnegative terms. -/
theorem mul_sq_le_half_cube_add (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y ^ 2 ≤ (1/2) * y ^ 3 + 2 * x ^ 2 * y := by
  rcases le_or_gt x (y / 2) with h | h
  · have h2 : 0 ≤ y * (y / 2 - x) ^ 2 := by positivity
    have h3 : 0 ≤ y ^ 2 * (y - 2 * x) := by
      exact mul_nonneg (sq_nonneg y) (by linarith)
    nlinarith [h2, h3, sq_nonneg (y - 2 * x), mul_nonneg hx hy]
  · nlinarith [sq_nonneg (y - 2 * x), mul_nonneg hx hy]

/-- **Cheskidov (5.4).**  For `x, y, z ≥ 0`, `x y z ≤ ½ x² y + ¼ z³ + y² z`.  Completing the
square in `x`: `½y x² - yz x + (¼z³ + y²z) = ½y (x - z/2)² + (z/4)(2y - z)² + ...`, a sum of
nonnegative terms. -/
theorem mul_mul_le_quarter_cube (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * y * z ≤ (1/2) * x ^ 2 * y + (1/4) * z ^ 3 + y ^ 2 * z := by
  have key : 0 ≤ (1/2) * y * x ^ 2 - (y * z) * x + ((1/4) * z ^ 3 + y ^ 2 * z) := by
    by_cases hy0 : y = 0
    · subst hy0
      have : (0:ℝ) ≤ (1/4) * z ^ 3 := by positivity
      nlinarith [this]
    · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
      have h2 : 0 ≤ ((1/2) * y * x - (y * z) / 2) ^ 2 := sq_nonneg _
      have h3 : 0 ≤ y * z * (2 * y - z) ^ 2 := by positivity
      nlinarith [h2, h3, sq_nonneg (2 * y - z), mul_nonneg hy hz, hypos]
  nlinarith [key]

/-! ## 3. The finite geometric bound -/

/-- **Finite geometric series bound.**  For `x > 1` and all `N`, `Σ_{k<N} x^k ≤ x^N / (x - 1)`.
This is the truncated form of `Σ_{k≥0} x^k = 1/(1 - x^{-1})`; keeping the truncation is what makes
the constant `A` in `inverted_holder` exact. -/
theorem geom_sum_range_le (x : ℝ) (hx : 1 < x) (N : ℕ) :
    (∑ k ∈ Finset.range N, x ^ k) ≤ x ^ N / (x - 1) := by
  have hx0 : (0:ℝ) < x := lt_trans zero_lt_one hx
  have hx1 : (0:ℝ) < x - 1 := by linarith
  induction N with
  | zero =>
      rw [Finset.range_zero, Finset.sum_empty, pow_zero]
      positivity
  | succ n ih =>
      have hsplit : (∑ k ∈ Finset.range (n+1), x ^ k)
          = (∑ k ∈ Finset.range n, x ^ k) + x ^ n := Finset.sum_range_succ _ _
      rw [hsplit]
      calc (∑ k ∈ Finset.range n, x ^ k) + x ^ n
          ≤ x ^ n / (x - 1) + x ^ n := by
            have hthis := add_le_add_right ih (x ^ n)
            linarith [hthis]
        _ = x ^ (n+1) / (x - 1) := by
            rw [pow_succ]; field_simp; ring

/-- The dyadic weight as a real power: `d(a)^r = 2^(a r)`. -/
theorem dyadicWeight_rpow (a : ℤ) (r : ℝ) :
    (dyadicWeight a) ^ r = (2:ℝ) ^ ((a:ℝ) * r) := by
  rw [dyadicWeight, ← Real.rpow_intCast (2:ℝ) a,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]

/-- The geometric bound in the form needed below: for `ε > 0` and every `N`,
`Σ_{k<N} 2^{-εk} ≤ 2^ε/(2^ε - 1)`.  (The right-hand side is `A(ε)^{-2}`.)

Proof: the term identity `2^{-εk} = (2^{-ε})^k` is proved by induction using
`dyadicWeight_add : dyadicWeight (a+b) = dyadicWeight a * dyadicWeight b`, and then the finite
telescoping `(1 - r)·Σ_{k<N} r^k = 1 - r^N` bounds `Σ_{k<N} r^k` by `1/(1-r)`. -/
theorem geom_sum_dyadicWeight_le (ε : ℤ) (hε : 0 < ε) (N : ℕ) :
    (∑ k ∈ Finset.range N, dyadicWeight (-ε * (k : ℤ)))
      ≤ dyadicWeight ε / (dyadicWeight ε - 1) := by
  have hg1 : (1:ℝ) < dyadicWeight ε := by
    rw [dyadicWeight]; exact one_lt_zpow₀ (by norm_num) hε
  have hgpos : 0 < dyadicWeight ε := lt_trans zero_lt_one hg1
  set r : ℝ := (dyadicWeight ε)⁻¹ with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr, inv_lt_one_iff₀]; exact Or.inr hg1
  have hterm : ∀ k : ℕ, dyadicWeight (-(ε * (k:ℤ))) = r ^ k := by
    intro k
    induction k with
    | zero => simp [dyadicWeight]
    | succ n ih =>
        have hstep : -(ε * ((n+1 : ℕ) : ℤ)) = -(ε * (n:ℤ)) + (-ε) := by push_cast; ring
        rw [hstep, dyadicWeight_add, ih]
        have hneg : dyadicWeight (-ε) = r := by
          rw [hr, dyadicWeight, dyadicWeight, zpow_neg]
        rw [hneg, pow_succ]
  have hsum : (∑ k ∈ Finset.range N, dyadicWeight (-ε * (k : ℤ)))
      = ∑ k ∈ Finset.range N, r ^ k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show -ε * (k:ℤ) = -(ε * (k:ℤ)) by ring, hterm k]
  have hgeom : ∀ M : ℕ, (1 - r) * (∑ k ∈ Finset.range M, r ^ k) = 1 - r ^ M := by
    intro M
    induction M with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
        ring
  have hbound : (∑ k ∈ Finset.range N, r ^ k) ≤ 1 / (1 - r) := by
    have h1 : (1 - r) * (∑ k ∈ Finset.range N, r ^ k) ≤ 1 := by
      rw [hgeom N]
      have : 0 ≤ r ^ N := pow_nonneg hrpos.le N
      linarith
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - r), mul_comm]
    exact h1
  rw [hsum]
  refine hbound.trans (le_of_eq ?_)
  rw [hr]
  have hne : dyadicWeight ε ≠ 0 := ne_of_gt hgpos
  have hne1 : dyadicWeight ε - 1 ≠ 0 := by linarith
  have hne2 : 1 - (dyadicWeight ε)⁻¹ ≠ 0 := by
    have : (dyadicWeight ε)⁻¹ < 1 := by rw [inv_lt_one_iff₀]; exact Or.inr hg1
    linarith
  field_simp

/-! ## 4. The inverted Hölder constant -/

/-- The constant `A(ε) = √((2^ε - 1)/2^ε)`. -/
def holderConst (ε : ℤ) : ℝ := Real.sqrt ((dyadicWeight ε - 1) / dyadicWeight ε)

/-- `0 < A(ε)` for `ε > 0`. -/
theorem holderConst_pos (ε : ℤ) (hε : 0 < ε) : 0 < holderConst ε := by
  rw [holderConst]
  apply Real.sqrt_pos.mpr
  apply div_pos _ (dyadicWeight_pos ε)
  have h2 : (1:ℝ) < dyadicWeight ε := by
    rw [dyadicWeight]
    exact one_lt_zpow₀ (by norm_num) hε
  linarith

/-- `A(ε) ≤ 1` for `ε > 0`. -/
theorem holderConst_le_one (ε : ℤ) (hε : 0 < ε) : holderConst ε ≤ 1 := by
  have h2 : (1:ℝ) < dyadicWeight ε := by
    rw [dyadicWeight]
    exact one_lt_zpow₀ (by norm_num) hε
  have hg : 0 < dyadicWeight ε := lt_trans zero_lt_one h2
  have hratio : (dyadicWeight ε - 1) / dyadicWeight ε ≤ 1 := by
    rw [div_le_one hg]; linarith
  rw [holderConst, ← Real.sqrt_one]
  apply Real.sqrt_le_sqrt
  norm_num
  exact hratio

/-- **Weighted AM–GM (exponents `2/3, 1/3`).**  For `X, Y ≥ 0`,
`X^{2/3} Y^{1/3} ≤ (2/3)X + (1/3)Y`. -/
theorem rpow_two_thirds_mul_rpow_one_third_le {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    X ^ ((2:ℝ)/3) * Y ^ ((1:ℝ)/3) ≤ (2/3) * X + (1/3) * Y := by
  have h2 : (2:ℝ)/3 + 1/3 = 1 := by norm_num
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := (2:ℝ)/3) (w₂ := (1:ℝ)/3)
    (p₁ := X) (p₂ := Y) (by norm_num) (by norm_num) hX hY h2
  simpa using h

/-- **Elementary Hölder step.**  For nonnegative reals `x, y` indexed by a finite `s`,
`(Σ √(x_k y_k))² ≤ (Σ x_k) (Σ y_k)`: Cauchy–Schwarz for the vectors `√x` and `√y`. -/
theorem sum_sqrt_mul_sq_le (s : Finset ℕ) (x y : ℕ → ℝ) (hx : ∀ k, 0 ≤ x k)
    (hy : ∀ k, 0 ≤ y k) :
    (∑ k ∈ s, Real.sqrt (x k * y k)) ^ 2 ≤ (∑ k ∈ s, x k) * (∑ k ∈ s, y k) := by
  have hpt : ∀ k ∈ s, Real.sqrt (x k * y k) = Real.sqrt (x k) * Real.sqrt (y k) :=
    fun k _ => Real.sqrt_mul (hx k) (y k)
  rw [Finset.sum_congr rfl hpt]
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun k => Real.sqrt (x k)) (fun k => Real.sqrt (y k))
  have h1 : (∑ k ∈ s, (Real.sqrt (x k)) ^ 2) = ∑ k ∈ s, x k :=
    Finset.sum_congr rfl fun k _ => Real.sq_sqrt (hx k)
  have h2 : (∑ k ∈ s, (Real.sqrt (y k)) ^ 2) = ∑ k ∈ s, y k :=
    Finset.sum_congr rfl fun k _ => Real.sq_sqrt (hy k)
  rw [h1, h2] at h
  exact h

/-- **The final squaring comparison.**  If `A > 0`, `A²G ≤ 1` and `S³ ≤ G·Q²` with `S, Q ≥ 0`, then
`A · S · √S ≤ Q`.  This is the step that turns the cubed Hölder bound into the `3/2` form. -/
theorem holder_final_step {A S Q G : ℝ} (hA : 0 < A) (hS : 0 ≤ S) (hQ : 0 ≤ Q)
    (hAG : A ^ 2 * G ≤ 1) (h1 : S ^ 3 ≤ G * Q ^ 2) :
    A * S * Real.sqrt S ≤ Q := by
  have hnn : 0 ≤ A * S * Real.sqrt S := by positivity
  have hsq : (A * S * Real.sqrt S) ^ 2 = A ^ 2 * S ^ 3 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hS]; ring
  have h2 : (A * S * Real.sqrt S) ^ 2 ≤ Q ^ 2 := by
    rw [hsq]; nlinarith [h1, hAG, hQ, sq_nonneg Q]
  calc A * S * Real.sqrt S = Real.sqrt ((A * S * Real.sqrt S) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (Q ^ 2) := Real.sqrt_le_sqrt h2
    _ = Q := Real.sqrt_sq hQ

/-- **Discrete Hölder with exponents `3` and `3/2`.**  The weighted Hölder inequality
`Σ X_k^{1/3} Y_k^{2/3} ≤ (Σ X_k)^{1/3} (Σ Y_k)^{2/3}` for nonnegative `X, Y`, obtained from
Mathlib's `Real.inner_le_Lp_mul_Lq_of_nonneg` by collapsing the fractional powers. -/
private theorem sum_rpow_holder (s : Finset ℕ) (c b : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hb : ∀ k, 0 ≤ b k) :
    (∑ k ∈ s, c k ^ ((1:ℝ)/3) * b k ^ ((2:ℝ)/3))
      ≤ (∑ k ∈ s, c k) ^ ((1:ℝ)/3) * (∑ k ∈ s, b k) ^ ((2:ℝ)/3) := by
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := s)
    (f := fun k => c k ^ ((1:ℝ)/3)) (g := fun k => b k ^ ((2:ℝ)/3))
    (p := (3:ℝ)) (q := (3:ℝ)/2)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (fun k _ => Real.rpow_nonneg (hc k) _) (fun k _ => Real.rpow_nonneg (hb k) _)
  have hf : ∀ k ∈ s, (c k ^ ((1:ℝ)/3)) ^ (3:ℝ) = c k := by
    intro k _
    simpa [one_div] using Real.rpow_inv_natCast_pow (hc k) (by norm_num : (3:ℕ) ≠ 0)
  have hg : ∀ k ∈ s, (b k ^ ((2:ℝ)/3)) ^ ((3:ℝ)/2) = b k := by
    intro k _
    rw [← Real.rpow_mul (hb k)]
    norm_num
  have e1 : (∑ k ∈ s, (c k ^ ((1:ℝ)/3)) ^ (3:ℝ)) = ∑ k ∈ s, c k :=
    Finset.sum_congr rfl hf
  have e2 : (∑ k ∈ s, (b k ^ ((2:ℝ)/3)) ^ ((3:ℝ)/2)) = ∑ k ∈ s, b k :=
    Finset.sum_congr rfl hg
  calc (∑ k ∈ s, c k ^ ((1:ℝ)/3) * b k ^ ((2:ℝ)/3))
      ≤ (∑ k ∈ s, (c k ^ ((1:ℝ)/3)) ^ (3:ℝ)) ^ (1 / (3:ℝ))
          * (∑ k ∈ s, (b k ^ ((2:ℝ)/3)) ^ ((3:ℝ)/2)) ^ (1 / ((3:ℝ)/2)) := h
    _ = (∑ k ∈ s, c k) ^ ((1:ℝ)/3) * (∑ k ∈ s, b k) ^ ((2:ℝ)/3) := by
        rw [e1, e2]
        norm_num

/-- **The pointwise decomposition of a dyadic weight.**  For `ε = 1 - 3e` the shell weight
`2^{(e+1)k}` factors as `(2^{-εk})^{1/3} (2^{2k})^{2/3}`, which is the identity behind the sharp
Hölder step. -/
private lemma dyadicWeight_pointwise (e : ℤ) (k : ℕ) (v : ℝ) :
    dyadicWeight ((e + 1) * (k:ℤ)) * v^2
      = (dyadicWeight (-(1 - 3*e) * (k:ℤ)))^((1:ℝ)/3)
          * (dyadicWeight (2 * (k:ℤ)) * |v|^3)^((2:ℝ)/3) := by
  have h2pos : (0:ℝ) < 2 := by norm_num
  have hv : (0:ℝ) ≤ |v| := abs_nonneg v
  have hdW : ∀ a : ℤ, dyadicWeight a = (2:ℝ) ^ ((a:ℝ)) := by
    intro a
    simp only [dyadicWeight]
    exact (Real.rpow_intCast (2:ℝ) a).symm
  have hdWrpow : ∀ (a : ℤ) (t : ℝ),
      (dyadicWeight a) ^ t = (2:ℝ) ^ ((a:ℝ) * t) := by
    intro a t
    rw [hdW a]
    exact (Real.rpow_mul h2pos.le _ _).symm
  have hcube : (|v|^3)^((2:ℝ)/3) = |v|^2 := by
    rw [← Real.rpow_natCast |v| 3, ← Real.rpow_mul hv,
      show ((3:ℕ):ℝ) * ((2:ℝ)/3) = 2 by norm_num, Real.rpow_two]
  rw [← sq_abs v, hdWrpow, Real.mul_rpow (dyadicWeight_pos _).le (by positivity),
    hdWrpow, hcube, hdW, ← mul_assoc, ← Real.rpow_add h2pos,
    show (((e + 1) * (k:ℤ) : ℤ) : ℝ)
        = ((-(1 - 3*e) * (k:ℤ) : ℤ) : ℝ) * ((1:ℝ)/3)
          + ((2 * (k:ℤ) : ℤ) : ℝ) * ((2:ℝ)/3) by push_cast; ring]

/-- `(x^(1/3))^3 = x` for `x ≥ 0`. -/
theorem rpow_third_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ ((1:ℝ)/3)) ^ 3 = x := by
  rw [← Real.rpow_natCast (x ^ ((1:ℝ)/3)) 3, ← Real.rpow_mul hx ((1:ℝ)/3) ((3:ℕ):ℝ),
    show (1:ℝ)/3 * ((3:ℕ):ℝ) = 1 by norm_num, Real.rpow_one]

/-- `(x^(2/3))^3 = x^2` for `x ≥ 0`. -/
theorem rpow_two_thirds_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ ((2:ℝ)/3)) ^ 3 = x ^ 2 := by
  rw [← Real.rpow_natCast (x ^ ((2:ℝ)/3)) 3, ← Real.rpow_mul hx ((2:ℝ)/3) ((3:ℕ):ℝ),
    show (2:ℝ)/3 * ((3:ℕ):ℝ) = 2 by norm_num, Real.rpow_two]

/-- `x^(2/3) = (x^2)^(1/3)` for `x ≥ 0`. -/
theorem rpow_two_thirds_eq {x : ℝ} (hx : 0 ≤ x) :
    x ^ ((2:ℝ)/3) = (x ^ 2) ^ ((1:ℝ)/3) := by
  conv_rhs => rw [← Real.rpow_natCast x 2]
  rw [← Real.rpow_mul hx ((2:ℕ):ℝ) ((1:ℝ)/3)]
  norm_num

/-- `(x^3)^(1/3) = x` for `x ≥ 0`. -/
theorem rpow_cube_third {x : ℝ} (hx : 0 ≤ x) : (x ^ 3) ^ ((1:ℝ)/3) = x := by
  conv_lhs => rw [← Real.rpow_natCast x 3]
  rw [← Real.rpow_mul hx ((3:ℕ):ℝ) ((1:ℝ)/3)]
  rw [show ((3:ℕ):ℝ) * ((1:ℝ)/3) = 1 by norm_num, Real.rpow_one]

/-- **The pointwise Hölder factorization.**  For `ε = 1 - 3e` and `k : ℤ, u : ℝ`,
`(2^{-εk})^{1/3} · (2^{2k}|u|³)^{2/3} = 2^{(e+1)k} u²`.  The proof keeps the exponents integral:
`(2^{-εk})·(2^{2k}|u|³)² = (2^{(e+1)k}|u|²)³` by `dyadicWeight` arithmetic, then takes cube roots. -/
theorem holder_factor (e k : ℤ) (u : ℝ) :
    (dyadicWeight (-(1-3*e) * k)) ^ ((1:ℝ)/3)
      * (dyadicWeight (2*k) * |u|^3) ^ ((2:ℝ)/3)
      = dyadicWeight ((e+1)*k) * u^2 := by
  set A : ℝ := dyadicWeight (-(1-3*e)*k) with hA
  set B : ℝ := dyadicWeight (2*k) * |u|^3 with hB
  set W : ℝ := dyadicWeight ((e+1)*k) with hW
  have hAnn : 0 ≤ A := dyadicWeight_nonneg _
  have hBnn : 0 ≤ B := mul_nonneg (dyadicWeight_nonneg _) (by positivity)
  have hWnn : 0 ≤ W := dyadicWeight_nonneg _
  have hcube : A * B^2 = (W * |u|^2)^3 := by
    have hB2 : B^2 = dyadicWeight (4*k) * |u|^6 := by
      rw [hB, mul_pow]
      have hp : (dyadicWeight (2*k))^2 = dyadicWeight (4*k) := by
        rw [pow_two, ← dyadicWeight_add]; congr 1; ring
      rw [hp, show (|u|^3)^2 = |u|^6 by ring]
    have hW3 : (W * |u|^2)^3 = dyadicWeight (3*((e+1)*k)) * |u|^6 := by
      rw [hW, mul_pow]
      have hp : (dyadicWeight ((e+1)*k))^3 = dyadicWeight (3*((e+1)*k)) := by
        rw [show (3:ℕ) = 2+1 from rfl, pow_succ, pow_two, ← dyadicWeight_add,
          ← dyadicWeight_add]
        congr 1; ring
      rw [hp, show (|u|^2)^3 = |u|^6 by ring]
    rw [hB2, hW3, hA]
    rw [show dyadicWeight (-(1-3*e)*k) * (dyadicWeight (4*k) * |u|^6)
        = (dyadicWeight (-(1-3*e)*k) * dyadicWeight (4*k)) * |u|^6 by ring]
    rw [show dyadicWeight (-(1-3*e)*k) * dyadicWeight (4*k) = dyadicWeight (3*((e+1)*k)) by
      rw [← dyadicWeight_add]; congr 1; ring]
  have h1 : A^((1:ℝ)/3) * B^((2:ℝ)/3) = (A*B^2)^((1:ℝ)/3) := by
    rw [rpow_two_thirds_eq hBnn, ← Real.mul_rpow hAnn (pow_nonneg hBnn 2)]
  rw [h1, hcube, rpow_cube_third (mul_nonneg hWnn (by positivity))]
  rw [sq_abs]

/-- **Real Hölder with exponents `3` and `3/2`.**  For `a, b ≥ 0`,
`(Σ a^{1/3} b^{2/3})³ ≤ (Σ a)(Σ b)²`.  This is Mathlib's `Real.inner_le_Lp_mul_Lq_of_nonneg` at
`(p,q) = (3, 3/2)` with the cube roots undone by `Real.rpow_mul`. -/
theorem holder_three (s : Finset ℕ) (a b : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) :
    (∑ k ∈ s, a k ^ ((1:ℝ)/3) * b k ^ ((2:ℝ)/3)) ^ 3
      ≤ (∑ k ∈ s, a k) * (∑ k ∈ s, b k) ^ 2 := by
  have hpq : Real.HolderConjugate (3:ℝ) (3/2) := ⟨by norm_num, by norm_num, by norm_num⟩
  have hf : ∀ k ∈ s, 0 ≤ a k ^ ((1:ℝ)/3) := fun k _ => Real.rpow_nonneg (ha k) _
  have hg : ∀ k ∈ s, 0 ≤ b k ^ ((2:ℝ)/3) := fun k _ => Real.rpow_nonneg (hb k) _
  have h0 := Real.inner_le_Lp_mul_Lq_of_nonneg s (f := fun k => a k ^ ((1:ℝ)/3))
    (g := fun k => b k ^ ((2:ℝ)/3)) hpq hf hg
  have hfa : ∀ k ∈ s, (a k ^ ((1:ℝ)/3)) ^ (3:ℝ) = a k := by
    intro k _
    rw [← Real.rpow_mul (ha k) ((1:ℝ)/3) (3:ℝ), show (1:ℝ)/3 * 3 = 1 by norm_num,
      Real.rpow_one]
  have hgb : ∀ k ∈ s, (b k ^ ((2:ℝ)/3)) ^ ((3:ℝ)/2) = b k := by
    intro k _
    rw [← Real.rpow_mul (hb k) ((2:ℝ)/3) ((3:ℝ)/2), show (2:ℝ)/3 * (3/2) = 1 by norm_num,
      Real.rpow_one]
  have h : (∑ k ∈ s, a k ^ ((1:ℝ)/3) * b k ^ ((2:ℝ)/3))
      ≤ (∑ k ∈ s, a k) ^ ((1:ℝ)/3) * (∑ k ∈ s, b k) ^ ((2:ℝ)/3) := by
    have h' := h0
    rw [Finset.sum_congr rfl hfa, Finset.sum_congr rfl hgb,
      show (1:ℝ)/(3/2) = 2/3 by norm_num] at h'
    exact h'
  have hLnn : 0 ≤ ∑ k ∈ s, a k ^ ((1:ℝ)/3) * b k ^ ((2:ℝ)/3) :=
    Finset.sum_nonneg fun k hk => mul_nonneg (hf k hk) (hg k hk)
  have hcube := pow_le_pow_left₀ hLnn h 3
  refine hcube.trans (le_of_eq ?_)
  rw [mul_pow, rpow_third_cube (Finset.sum_nonneg fun i _ => ha i),
    rpow_two_thirds_cube (Finset.sum_nonneg fun i _ => hb i)]

/-- **The inverted Hölder lemma (heart of the file).**  For `e ≤ 0`, `ε = 1 - 3e ≥ 1 > 0`, a real
ladder `u` and `N : ℕ`,

`√((2^ε - 1)/2^ε) · S · √S ≤ Σ_{k<N} 2^{2k} |u_k|³`,  where `S = Σ_{k<N} 2^{(e+1)k} u_k²`.

The constant is exactly the one produced by the sharp weighted Hölder inequality together with the
*truncated* geometric bound `Σ_{k<N} 2^{-εk} ≤ 2^ε/(2^ε - 1) = A^{-2}`.  The inequality is sharp:
for `e = 0`, `N = 1` and `u = δ₀` both sides are `A` and `1` with `A = √(1/2) < 1`. -/
theorem inverted_holder (e : ℤ) (he : e ≤ 0) (u : ℤ → ℝ) (N : ℕ) :
    holderConst (1 - 3*e)
      * ((∑ k ∈ Finset.range N, dyadicWeight ((e + 1) * (k:ℤ)) * (u (k:ℤ))^2)
          * Real.sqrt (∑ k ∈ Finset.range N, dyadicWeight ((e + 1) * (k:ℤ)) * (u (k:ℤ))^2))
      ≤ ∑ k ∈ Finset.range N, dyadicWeight (2 * (k:ℤ)) * |u (k:ℤ)|^3 := by
  have hε : (0:ℤ) < 1 - 3*e := by omega
  set S : ℝ := ∑ k ∈ Finset.range N, dyadicWeight ((e + 1) * (k:ℤ)) * (u (k:ℤ))^2 with hSdef
  set G : ℝ := ∑ k ∈ Finset.range N, dyadicWeight (-(1 - 3*e) * (k:ℤ)) with hGdef
  set Q : ℝ := ∑ k ∈ Finset.range N, dyadicWeight (2 * (k:ℤ)) * |u (k:ℤ)|^3 with hQdef
  have h1lt : (1:ℝ) < dyadicWeight (1 - 3*e) := by
    rw [dyadicWeight]
    exact one_lt_zpow₀ (by norm_num) hε
  have hg : (0:ℝ) < dyadicWeight (1 - 3*e) := lt_trans zero_lt_one h1lt
  have hS : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (dyadicWeight_pos _).le (sq_nonneg _)
  have hQ : 0 ≤ Q := by
    rw [hQdef]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (dyadicWeight_pos _).le (by positivity)
  have hA : 0 < holderConst (1 - 3*e) := holderConst_pos (1 - 3*e) hε
  have hA2 : holderConst (1 - 3*e)^2
      = (dyadicWeight (1 - 3*e) - 1) / dyadicWeight (1 - 3*e) := by
    rw [holderConst, Real.sq_sqrt (div_nonneg (by linarith) hg.le)]
  have hAG : holderConst (1 - 3*e)^2 * G ≤ 1 := by
    have hgeom := geom_sum_dyadicWeight_le (1 - 3*e) hε N
    have hcoef : 0 ≤ (dyadicWeight (1 - 3*e) - 1) / dyadicWeight (1 - 3*e) :=
      div_nonneg (by linarith) hg.le
    rw [hA2, hGdef]
    calc (dyadicWeight (1 - 3*e) - 1) / dyadicWeight (1 - 3*e)
          * (∑ k ∈ Finset.range N, dyadicWeight (-(1 - 3*e) * (k:ℤ)))
        ≤ (dyadicWeight (1 - 3*e) - 1) / dyadicWeight (1 - 3*e)
            * (dyadicWeight (1 - 3*e) / (dyadicWeight (1 - 3*e) - 1)) :=
          mul_le_mul_of_nonneg_left hgeom hcoef
      _ = 1 := by
          have hg1 : dyadicWeight (1 - 3*e) - 1 ≠ 0 := by linarith
          field_simp [hg.ne', hg1]
  have h1 : S^3 ≤ G * Q^2 := by
    rw [hSdef, hGdef, hQdef]
    have hholder := sum_rpow_holder (Finset.range N)
      (fun k => dyadicWeight (-(1 - 3*e) * (k:ℤ)))
      (fun k => dyadicWeight (2 * (k:ℤ)) * |u (k:ℤ)|^3)
      (fun k => (dyadicWeight_pos _).le)
      (fun k => mul_nonneg (dyadicWeight_pos _).le (by positivity))
    have hSc : (∑ k ∈ Finset.range N, dyadicWeight ((e + 1) * (k:ℤ)) * (u (k:ℤ))^2)
        = ∑ k ∈ Finset.range N,
            (dyadicWeight (-(1 - 3*e) * (k:ℤ)))^((1:ℝ)/3)
              * (dyadicWeight (2 * (k:ℤ)) * |u (k:ℤ)|^3)^((2:ℝ)/3) :=
      Finset.sum_congr rfl fun k _ => dyadicWeight_pointwise e k (u (k:ℤ))
    rw [hSc]
    have hSnn : 0 ≤ ∑ k ∈ Finset.range N,
        (dyadicWeight (-(1 - 3*e) * (k:ℤ)))^((1:ℝ)/3)
          * (dyadicWeight (2 * (k:ℤ)) * |u (k:ℤ)|^3)^((2:ℝ)/3) := by
      rw [← hSc]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (dyadicWeight_pos _).le (sq_nonneg _)
    have hle : (∑ k ∈ Finset.range N,
          (dyadicWeight (-(1 - 3*e) * (k:ℤ)))^((1:ℝ)/3)
            * (dyadicWeight (2 * (k:ℤ)) * |u (k:ℤ)|^3)^((2:ℝ)/3))
        ≤ (∑ k ∈ Finset.range N, dyadicWeight (-(1 - 3*e) * (k:ℤ)))^((1:ℝ)/3)
          * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k:ℤ)) * |u (k:ℤ)|^3)^((2:ℝ)/3) :=
      hholder
    have hcube := pow_le_pow_left₀ hSnn hle 3
    refine le_trans hcube (le_of_eq ?_)
    rw [mul_pow]
    have hG0 : 0 ≤ ∑ k ∈ Finset.range N, dyadicWeight (-(1 - 3*e) * (k:ℤ)) :=
      Finset.sum_nonneg fun k _ => (dyadicWeight_pos _).le
    have hQ0 : 0 ≤ ∑ k ∈ Finset.range N, dyadicWeight (2 * (k:ℤ)) * |u (k:ℤ)|^3 :=
      Finset.sum_nonneg fun k _ => mul_nonneg (dyadicWeight_pos _).le (by positivity)
    have hGc : ((∑ k ∈ Finset.range N, dyadicWeight (-(1 - 3*e) * (k:ℤ)))^((1:ℝ)/3))^3
        = ∑ k ∈ Finset.range N, dyadicWeight (-(1 - 3*e) * (k:ℤ)) := by
      simpa [one_div] using Real.rpow_inv_natCast_pow hG0 (by norm_num : (3:ℕ) ≠ 0)
    have hQc : ((∑ k ∈ Finset.range N, dyadicWeight (2 * (k:ℤ)) * |u (k:ℤ)|^3)^((2:ℝ)/3))^3
        = (∑ k ∈ Finset.range N, dyadicWeight (2 * (k:ℤ)) * |u (k:ℤ)|^3)^2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0,
        show (2:ℝ)/3 * ((3:ℕ):ℝ) = 2 by norm_num, Real.rpow_two]
    rw [hGc, hQc]
  have hmain := holder_final_step (A := holderConst (1 - 3*e)) (G := G) (S := S) (Q := Q)
    hA hS hQ hAG h1
  simpa only [mul_assoc] using hmain


/-! ## 5. Non-vacuity checks -/

/-- (5.3) at the boundary case `x = y/2`: `x = 1`, `y = 2`. -/
example : (1:ℝ) * 2 ^ 2 ≤ (1/2) * 2 ^ 3 + 2 * 1 ^ 2 * 2 := by norm_num

/-- (5.3) with a zero coordinate. -/
example : (0:ℝ) * 5 ^ 2 ≤ (1/2) * 5 ^ 3 + 2 * 0 ^ 2 * 5 := by norm_num

/-- (5.4) at the boundary case `z = 2y`: `x = 1`, `y = 1`, `z = 2`. -/
example : (1:ℝ) * 1 * 2 ≤ (1/2) * 1 ^ 2 * 1 + (1/4) * 2 ^ 3 + 1 ^ 2 * 2 := by norm_num

/-- (5.4) with a zero coordinate. -/
example : (0:ℝ) * 3 * 4 ≤ (1/2) * 0 ^ 2 * 3 + (1/4) * 4 ^ 3 + 3 ^ 2 * 4 := by norm_num

/-- The engine's bound with concrete numbers: `c = 1`, `y₀ = 4` gives `T ≤ 2/(1·√4) = 1`. -/
example : (2 : ℝ) / (1 * Real.sqrt 4) = 1 := by
  rw [show Real.sqrt 4 = 2 by norm_num]; norm_num

/-- Sharp single-mode sanity check for `inverted_holder` with `e = 0`, `N = 1`, `u = δ₀`:
the inequality reads `A(1) · 1 · √1 ≤ 1`, and `A(1) = √(1/2) = 0.7071… < 1`. -/
example : holderConst 1 * (1 * Real.sqrt 1) ≤ 1 := by
  have h := holderConst_le_one 1 (by norm_num)
  simpa using h

/-- **Single-mode numerical check of `inverted_holder`.**  For `e = 0`, `N = 1`, `u = δ₀` with
`u₀ = 1`: `S = 1`, `Σ 2^{2k}|u_k|³ = 1`, and `A·S·√S = √(1/2) ≈ 0.7071 ≤ 1`. -/
example : holderConst 1 * (1 * Real.sqrt 1) ≤ (1 : ℝ) := by
  have h := holderConst_le_one 1 (by norm_num)
  simpa using h

/-- **Concrete instance of `inverted_holder`**, `e = 0`, `N = 1`, `u = δ₀` (derived from the
theorem itself, not from `holderConst_le_one`). -/
example : holderConst 1 * (1 * Real.sqrt (1:ℝ)) ≤ (1:ℝ) := by
  have h := inverted_holder 0 (by norm_num) (fun k => if k = 0 then (1:ℝ) else 0) 1
  simpa [dyadicWeight] using h

/-- **Concrete instance of `inverted_holder`**, `e = -1` (so `ε = 4`), `N = 2`, `u = (1,2)`:
`S = 1 + 4 = 5`, `Σ 2^{2k}|u_k|³ = 1 + 4·8 = 33`, `A = A(4) = √(15/16) ≈ 0.9682`. -/
example : holderConst 4 * (5 * Real.sqrt 5) ≤ (33:ℝ) := by
  have h := inverted_holder (-1) (by norm_num)
    (fun k => if k = 0 then (1:ℝ) else if k = 1 then 2 else 0) 2
  norm_num [dyadicWeight, Finset.sum_range_succ] at h ⊢
  exact h

/-- **Concrete instance of `inverted_holder`**, `e = 0`, `N = 3`, `u = (1,2,4)`:
`S = 1 + 2·4 + 4·16 = 73` and `Σ 2^{2k}|u_k|³ = 1 + 4·8 + 16·64 = 1057`. -/
example : holderConst 1 * (73 * Real.sqrt 73) ≤ (1057:ℝ) := by
  have h := inverted_holder 0 (by norm_num)
    (fun k => if k = 0 then (1:ℝ) else if k = 1 then 2 else if k = 2 then 4 else 0) 3
  norm_num [dyadicWeight, Finset.sum_range_succ] at h ⊢
  exact h

end Cascade

/-! ### Axiom audit -/

#print axioms Cascade.le_of_deriv_nonpos_of_hasDerivAt
#print axioms Cascade.le_of_deriv_ge_mul_sqrt
#print axioms Cascade.not_solution_of_gt
#print axioms Cascade.not_exists_solution_of_gt
#print axioms Cascade.mul_sq_le_half_cube_add
#print axioms Cascade.mul_mul_le_quarter_cube
#print axioms Cascade.geom_sum_range_le
#print axioms Cascade.geom_sum_dyadicWeight_le
#print axioms Cascade.holderConst
#print axioms Cascade.holderConst_pos
#print axioms Cascade.holderConst_le_one
#print axioms Cascade.rpow_two_thirds_mul_rpow_one_third_le
#print axioms Cascade.sum_sqrt_mul_sq_le
#print axioms Cascade.holder_final_step
#print axioms Cascade.dyadicWeight_rpow
#print axioms Cascade.rpow_third_cube
#print axioms Cascade.rpow_two_thirds_cube
#print axioms Cascade.rpow_two_thirds_eq
#print axioms Cascade.rpow_cube_third
#print axioms Cascade.holder_factor
#print axioms Cascade.holder_three
#print axioms Cascade.inverted_holder
