/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cascade formalization
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Monotone
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Bernoulli/Riccati barrier engine for Stage O′

This file is the **nonlinear companion** of `Cascade/Gronwall.lean`.  It is standalone: it
imports nothing from the `Cascade` model files, only Mathlib.

## Why this engine is needed

At Stage O′ the Stage-O energy obstruction is upgraded to an *enstrophy* (`H¹`) obstruction.
Along the unforced dyadic Boussinesq model the enstrophy `H` obeys an inequality of the shape

`H' ≤ 3 * H * √H + (buoyancy production) - ν * H ^ 2 / E`,

where `E` is the energy and `ν > 0` is the viscosity.  The buoyancy term is absorbed by Young's
inequality, which converts the inequality into the constant-coefficient form

`H' ≤ C - γ * H ^ 2`   (`C ≥ 0`, `γ > 0`),

or, keeping the leading nonlinearity, into the **Bernoulli/Riccati** shape

`H' ≤ a * H * √H - b * H ^ 2`   (`a ≥ 0`, `b > 0`).

In both cases the right-hand side has a positive zero — `(a / b) ^ 2` for the Bernoulli shape and
`√(C / γ)` for the constant-coefficient shape — above which it is *negative*.  The content of this
file is that such a **subsolution can never cross** that threshold, so it is bounded **uniformly in
time** by `max (H 0) (threshold)`, with **no finite-time blowup of the enstrophy** and no exponential
factor in `T`.

## The difference from the linear Grönwall engine

`Cascade/Gronwall.lean` linearises the buoyancy term by AM–GM into `E' ≤ a + b * E` and concludes
with the linear comparison `gronwallBound`, which is uniform in `T` only in the dissipative
case `b < 0`.  Here the dissipation is kept *quadratic* (`- b * y ^ 2`), so the barrier is the
stationary positive root itself and the conclusion holds for **every** `T` whenever `b > 0`,
independent of the size of the destabilising coefficient `a`.

## The argument

Everything rests on one abstract first-crossing lemma, `le_of_deriv_neg_of_lt'`: if `y` is
continuous on `[c, T]`, differentiable on `[c, T)` with `y' t < 0` whenever `y t > M`, and starts at
`y c ≤ M`, then `y` stays `≤ M`.  The proof is the barrier argument, not an ODE-comparison black box:
if `y t₀ > M`, the set `{t ∈ [c, t₀] | y t ≤ M}` is nonempty, closed and bounded above, so its
supremum `t₁` belongs to it.  Then `t₁ < t₀`, `y t₁ ≤ M`, and `y > M` on `(t₁, t₀]`.  The mean value
theorem on `[t₁, t₀]` produces `ξ ∈ (t₁, t₀)` with
`y' ξ = (y t₀ - y t₁) / (t₀ - t₁) > 0`, while `y ξ > M` gives `y' ξ < 0`: contradiction.

The two main theorems instantiate this with the two shapes above.  Note that `y * Real.sqrt y` is
used for the `3/2` power throughout, precisely so that no `Real.rpow` appears.
-/

namespace Cascade

open Set

/-! ### 1. The abstract first-crossing barrier -/

/-- **Abstract barrier lemma (arbitrary left endpoint).**  Let `y` be continuous on `[c, T]` and
differentiable on `[c, T)`.  If `y c ≤ M` and `y' t < 0` at every `t ∈ [c, T)` where `y t > M`, then
`y t ≤ M` on all of `[c, T]`.

Proof by the barrier/first-crossing argument: if `y t₀ > M`, let `t₁` be the supremum of the closed
set `{t ∈ [c, t₀] | y t ≤ M}`, apply the mean value theorem on `[t₁, t₀]`, and contradict
`y' < 0` at the interior point it produces. -/
theorem le_of_deriv_neg_of_lt' {y y' : ℝ → ℝ} {c T M : ℝ}
    (hcont : ContinuousOn y (Set.Icc c T))
    (hderiv : ∀ t ∈ Set.Ico c T, HasDerivAt y (y' t) t)
    (h0 : y c ≤ M)
    (hneg : ∀ t ∈ Set.Ico c T, M < y t → y' t < 0) :
    ∀ t ∈ Set.Icc c T, y t ≤ M := by
  intro t₀ ht₀
  by_contra hcon
  rw [not_le] at hcon
  -- The first-crossing set is nonempty, closed and bounded above; take its supremum.
  obtain ⟨t₁, ht₁S, ht₁max⟩ : ∃ t₁ ∈ Set.Icc c t₀ ∩ y ⁻¹' Set.Iic M,
      ∀ s ∈ Set.Icc c t₀ ∩ y ⁻¹' Set.Iic M, s ≤ t₁ := by
    have hSne : (Set.Icc c t₀ ∩ y ⁻¹' Set.Iic M).Nonempty :=
      ⟨c, ⟨⟨le_rfl, ht₀.1⟩, h0⟩⟩
    have hSbdd : BddAbove (Set.Icc c t₀ ∩ y ⁻¹' Set.Iic M) :=
      ⟨t₀, fun s hs => hs.1.2⟩
    have hSclosed : IsClosed (Set.Icc c t₀ ∩ y ⁻¹' Set.Iic M) := by
      have h1 : IsClosed (Set.Icc c T ∩ y ⁻¹' Set.Iic M) :=
        hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
      have h2 : IsClosed (Set.Icc c t₀) := isClosed_Icc
      have hsub : Set.Icc c t₀ ∩ y ⁻¹' Set.Iic M
          = Set.Icc c t₀ ∩ (Set.Icc c T ∩ y ⁻¹' Set.Iic M) := by
        ext s
        constructor
        · rintro ⟨hs, hy⟩
          exact ⟨hs, ⟨⟨hs.1, le_trans hs.2 ht₀.2⟩, hy⟩⟩
        · rintro ⟨hs, -, hy⟩
          exact ⟨hs, hy⟩
      rw [hsub]
      exact h2.inter h1
    exact ⟨sSup (Set.Icc c t₀ ∩ y ⁻¹' Set.Iic M),
      hSclosed.csSup_mem hSne hSbdd, fun s hs => le_csSup hSbdd hs⟩
  have ht₁_lt : t₁ < t₀ := by
    rcases lt_or_eq_of_le ht₁S.1.2 with h | h
    · exact h
    · exfalso
      rw [h] at ht₁S
      exact absurd ht₁S.2 (not_le.mpr hcon)
  -- Mean value theorem on `[t₁, t₀]`.
  have hcont' : ContinuousOn y (Set.Icc t₁ t₀) :=
    hcont.mono fun s hs => ⟨le_trans ht₁S.1.1 hs.1, le_trans hs.2 ht₀.2⟩
  have hderiv' : ∀ s ∈ Set.Ioo t₁ t₀, HasDerivAt y (y' s) s := fun s hs =>
    hderiv s ⟨le_trans ht₁S.1.1 hs.1.le, lt_of_lt_of_le hs.2 ht₀.2⟩
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope y y' ht₁_lt hcont' hderiv'
  -- `ξ` is strictly above `t₁`, hence strictly above the threshold.
  have hξS : M < y ξ := by
    by_contra hle
    have hle' : y ξ ≤ M := not_lt.mp hle
    have hmem : ξ ∈ Set.Icc c t₀ ∩ y ⁻¹' Set.Iic M :=
      ⟨⟨le_trans ht₁S.1.1 hξ.1.le, le_of_lt hξ.2⟩, hle'⟩
    exact absurd (ht₁max ξ hmem) (not_le.mpr hξ.1)
  have ht₁M : y t₁ ≤ M := ht₁S.2
  have hpos : 0 < y' ξ := by
    rw [hξeq]
    exact div_pos (by linarith [hcon, ht₁M]) (by linarith)
  have hneg' : y' ξ < 0 :=
    hneg ξ ⟨le_trans ht₁S.1.1 hξ.1.le, lt_of_lt_of_le hξ.2 ht₀.2⟩ hξS
  linarith

/-! ### 2. A square-root comparison -/

/-- If `a ≥ 0`, `b > 0` and `y > (a / b) ^ 2`, then `a * √y < b * y`.  This is the algebraic
content of "the Bernoulli right-hand side is negative above its positive root": multiplying by the
positive number `y` gives `a * y * √y < b * y ^ 2`. -/
theorem sqrt_mul_lt_of_sq_div_lt {a b y : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hy : (a / b) ^ 2 < y) : a * Real.sqrt y < b * y := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hypos : 0 < y := lt_of_le_of_lt (sq_nonneg _) hy
  have hy0 : 0 ≤ y := hypos.le
  have hkey : a ^ 2 < b ^ 2 * y := by
    have hb2pos : 0 < b ^ 2 := pow_pos hb 2
    have hb2 : b ^ 2 * (a / b) ^ 2 = a ^ 2 := by
      rw [div_pow]
      field_simp
    have h := mul_lt_mul_of_pos_left hy hb2pos
    rwa [hb2] at h
  have hsq : (a * Real.sqrt y) ^ 2 < (b * y) ^ 2 := by
    have h1 : (a * Real.sqrt y) ^ 2 = a ^ 2 * y := by
      rw [mul_pow, Real.sq_sqrt hy0]
    have h2 : (b * y) ^ 2 = b ^ 2 * y ^ 2 := by ring
    rw [h1, h2]
    calc a ^ 2 * y < (b ^ 2 * y) * y := mul_lt_mul_of_pos_right hkey hypos
      _ = b ^ 2 * y ^ 2 := by ring
  exact (sq_lt_sq₀ (mul_nonneg ha (Real.sqrt_nonneg y)) (mul_nonneg hb.le hy0)).mp hsq

/-! ### 3. The Bernoulli/Riccati barrier -/

/-- **Bernoulli/Riccati barrier.** If `y` is continuous on `[0, T]`, differentiable on `[0, T)`,
and `y' t ≤ a * y t * Real.sqrt (y t) - b * (y t)^2` there, with `a ≥ 0`, `b > 0`, then
`y t ≤ max (y 0) (a / b)^2` on `[0, T]`.

No nonnegativity hypothesis on `y` is needed: for `y < 0` the right-hand side equals `- b * y ^ 2`,
which is already negative, and the barrier argument only ever evaluates the inequality at points
where `y` exceeds the (nonnegative) threshold.  The threshold `(a / b) ^ 2` is the unique positive
zero of `a * y * √y - b * y ^ 2`. -/
theorem le_of_deriv_le_bernoulli {y y' : ℝ → ℝ} {a b T : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (hcont : ContinuousOn y (Set.Icc 0 T))
    (hderiv : ∀ t ∈ Set.Ico 0 T, HasDerivAt y (y' t) t)
    (hineq : ∀ t ∈ Set.Ico 0 T, y' t ≤ a * y t * Real.sqrt (y t) - b * (y t) ^ 2) :
    ∀ t ∈ Set.Icc 0 T, y t ≤ max (y 0) ((a / b) ^ 2) := by
  intro t₀ ht₀
  refine le_of_deriv_neg_of_lt' (c := 0) hcont hderiv (le_max_left _ _) ?_ t₀ ht₀
  intro t ht hMt
  have hthr : (a / b) ^ 2 < y t := lt_of_le_of_lt (le_max_right _ _) hMt
  have hs := sqrt_mul_lt_of_sq_div_lt ha hb hthr
  have hyt : 0 < y t := lt_of_le_of_lt (sq_nonneg _) hthr
  have hprod : a * y t * Real.sqrt (y t) < b * (y t) ^ 2 := by
    calc a * y t * Real.sqrt (y t) = (a * Real.sqrt (y t)) * y t := by ring
      _ < (b * y t) * y t := mul_lt_mul_of_pos_right hs hyt
      _ = b * (y t) ^ 2 := by ring
  linarith [hineq t ht]

/-! ### 4. The constant-coefficient variant -/

/-- If `y' t ≤ C - γ * (y t)^2` with `C ≥ 0`, `γ > 0`, then `y t ≤ max (y 0) (Real.sqrt (C / γ))`.

This is proved **directly** by the same barrier argument, with threshold `√(C / γ)` — the positive
root of `C - γ * y ^ 2`.  Above it, `C - γ * y ^ 2 < 0`, so `y` cannot cross.  (Deriving it from
`le_of_deriv_le_bernoulli` would require the substitution `a = C / L ^ (3/2)`, `b = C / L ^ 2` with
`L = √(C / γ)`, which reintroduces a `Real.rpow`-style `L ^ (3/2)`; the direct barrier is cleaner
and avoids the substitution entirely.) -/
theorem le_of_deriv_le_const_sub_sq {y y' : ℝ → ℝ} {C γ T : ℝ} (hC : 0 ≤ C) (hγ : 0 < γ)
    (hcont : ContinuousOn y (Set.Icc 0 T))
    (hderiv : ∀ t ∈ Set.Ico 0 T, HasDerivAt y (y' t) t)
    (hineq : ∀ t ∈ Set.Ico 0 T, y' t ≤ C - γ * (y t) ^ 2) :
    ∀ t ∈ Set.Icc 0 T, y t ≤ max (y 0) (Real.sqrt (C / γ)) := by
  intro t₀ ht₀
  refine le_of_deriv_neg_of_lt' (c := 0) hcont hderiv (le_max_left _ _) ?_ t₀ ht₀
  intro t ht hMt
  have hthr : Real.sqrt (C / γ) < y t := lt_of_le_of_lt (le_max_right _ _) hMt
  have hyt : 0 < y t := lt_of_le_of_lt (Real.sqrt_nonneg _) hthr
  have hsq : (Real.sqrt (C / γ)) ^ 2 < (y t) ^ 2 :=
    (sq_lt_sq₀ (Real.sqrt_nonneg _) hyt.le).mpr hthr
  rw [Real.sq_sqrt (div_nonneg hC hγ.le)] at hsq
  have hγy : C < γ * (y t) ^ 2 := by
    have h := mul_lt_mul_of_pos_left hsq hγ
    rwa [mul_div_cancel₀ C (ne_of_gt hγ)] at h
  linarith [hineq t ht]

/-! ### 5. Monotonicity above the threshold -/

/-- Above the threshold the subsolution is strictly decreasing: if `y > M` throughout `[t₁, t₂]`
(and `y' < 0` wherever `y > M`), then `y t₂ < y t₁`.  This is the mean value theorem again, and it
is the quantitative form of "the barrier can only be approached from below". -/
theorem lt_of_lt_of_deriv_neg_above {y y' : ℝ → ℝ} {T M t₁ t₂ : ℝ}
    (hcont : ContinuousOn y (Set.Icc 0 T))
    (hderiv : ∀ t ∈ Set.Ico 0 T, HasDerivAt y (y' t) t)
    (hneg : ∀ t ∈ Set.Ico 0 T, M < y t → y' t < 0)
    (h1 : t₁ ∈ Set.Icc 0 T) (h2 : t₂ ∈ Set.Icc 0 T) (h12 : t₁ < t₂)
    (habove : ∀ t ∈ Set.Icc t₁ t₂, M < y t) : y t₂ < y t₁ := by
  have hcont' : ContinuousOn y (Set.Icc t₁ t₂) :=
    hcont.mono fun s hs => ⟨le_trans h1.1 hs.1, le_trans hs.2 h2.2⟩
  have hderiv' : ∀ s ∈ Set.Ioo t₁ t₂, HasDerivAt y (y' s) s := fun s hs =>
    hderiv s ⟨le_trans h1.1 hs.1.le, lt_of_lt_of_le hs.2 h2.2⟩
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope y y' h12 hcont' hderiv'
  have hnegξ : y' ξ < 0 :=
    hneg ξ ⟨le_trans h1.1 hξ.1.le, lt_of_lt_of_le hξ.2 h2.2⟩ (habove ξ ⟨hξ.1.le, hξ.2.le⟩)
  rw [hξeq] at hnegξ
  have hden : 0 < t₂ - t₁ := by linarith
  rw [div_lt_iff₀ hden] at hnegξ
  linarith

/-! ### 6. Sanity check -/

/-- The rearrangement `3 * (H * √H) = 3 * H * √H` used when matching the enstrophy inequality to
the Bernoulli shape. -/
theorem sanity_three_sqrt (H : ℝ) :
    3 * (H * Real.sqrt H) ≤ 3 * H * Real.sqrt H :=
  le_of_eq (mul_assoc 3 H (Real.sqrt H)).symm

/-! ### Axiom audit -/

#print axioms le_of_deriv_neg_of_lt'
#print axioms sqrt_mul_lt_of_sq_div_lt
#print axioms le_of_deriv_le_bernoulli
#print axioms le_of_deriv_le_const_sub_sq
#print axioms lt_of_lt_of_deriv_neg_above
#print axioms sanity_three_sqrt

end Cascade
