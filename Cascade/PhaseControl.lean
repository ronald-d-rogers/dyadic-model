/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Cascade.Phase

/-!
# Stage G″ — steering *both* AB coefficients: the product is an exact sinusoid

`Cascade/PhaseGrowth.lean` studied what happens when **only the buoyancy coupling**
`b = abVortCoeff lam zeta` is steered, holding the temperature coefficient `a = abTempCoeff lam
zeta G` fixed. That is *not* the physical situation: in Alpöge–Buckmaster both coefficients depend
on the wavevector `zeta` (their page-4 system, eq. (3.2)), so steering by a background rotation
`zeta = rotR alpha *ᵥ zeta0` moves `a` and `b` together. This file is the honest version, and it
corrects the conclusion of `PhaseGrowth.lean`.

**The exact product.** For `zeta0 = ![c, 0]` with `c > 0`, `G = ![g0, g1]` and `lam ≠ 0`, the
product of the two steered coefficients is (`ab_both_formula`)

    a(alpha) b(alpha) = -g1/2 + (g0/2) sin (2 alpha) - (g1/2) cos (2 alpha),

an exact sinusoid in `2 alpha`. Its derivation is the one field computation the scalar reductions
avoided: `zeta = (c cos alpha, c sin alpha)`, `J zeta = (-c sin alpha, c cos alpha)`, hence
`(J zeta)·G = c (g1 cos alpha - g0 sin alpha)` and `a = -(g1 cos alpha - g0 sin alpha)/(lam c)`,
`b = lam c cos alpha`, whose product is
`-g1 cos²alpha + g0 sin alpha cos alpha`.

**The correction to `PhaseGrowth.lean`.** Two structural consequences are now theorems rather than
by-products:

* **`lam` and `c` cancel** from the product (`ab_both_eq_of_lambda_c`): the product depends only on
  the background gradient `G` and on the angle. The frequency and the wavevector magnitude, which
  `PhaseGrowth.lean` kept as parameters, are unobservable in the Rayleigh–Taylor sign.
* **The product is `pi`-periodic**, so a **half turn leaves it unchanged** (`ab_both_add_pi`).
  `PhaseGrowth.lean` found that a half turn *flips* the coupling `b = lam c cos alpha`; that was an
  artifact of freezing `a`. With both coefficients steered, `a` also flips sign under the half turn
  (it is an odd function of the angle), and the product is invariant. So the "half-turn control" of
  `PhaseGrowth.lean` is not a control at all in the physical system.

**What survives.** `ab_both_range` pins the range down exactly:
`a b ∈ [-(g1 + R)/2, (R - g1)/2]` with `R = sqrt (g0^2 + g1^2)`, both endpoints attained
(`ab_both_max_attained`, `ab_both_min_attained`). Consequently growth is attainable **iff**
`g0 ≠ 0 ∨ g1 < 0` (`ab_both_positive_iff`): the sign of the product is steerable exactly when the
background gradient is not vertical-and-up. The maximum product is `(R - g1)/2`, so the maximum
growth rate is `sqrt ((R - g1)/2)`. For a purely upward gradient (`g0 = 0`, `g1 ≥ 0`) the phase
cannot produce growth at all (`ab_both_vertical_nonpos`): at `alpha = 0` and `alpha = pi/2` the
product is `-g1` and `0` respectively — steering only makes it more negative.

**Scope (prose).** This is still the two-coefficient scalar/geometric statement for a single
wavevector, with `G` frozen. It does **not** touch the Stage-O/O′ enstrophy budget of
`Cascade/Enstrophy.lean`, which is a *magnitude* comparison (a bound on `∫ |omega|^2`) in which the
wavevector phases do not appear at all: showing that the phase can reverse the instantaneous
Rayleigh–Taylor sign does not move any enstrophy estimate. Building `G` and `D` from the lower
octaves, one steered wavevector per octave as in AB eq. (3.3), remains out of scope.

**Notation.** The binder name `lam` is used for the frequency throughout, because Lean 4 reserves
`λ` as the lambda-abstraction token and therefore will not accept it as an identifier.
-/

noncomputable section

namespace Cascade

open scoped Matrix
theorem l2norm_steered (c : ℝ) (hc : 0 < c) (alpha : ℝ) :
    l2norm (rotR alpha *ᵥ ![c, 0]) = c := by
  rw [rotR_norm_preserving]
  simp only [l2norm]
  rw [show (![c, 0] : Fin 2 → ℝ) 0 = c by simp]
  rw [show (![c, 0] : Fin 2 → ℝ) 1 = 0 by simp]
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq_eq_abs, abs_of_pos hc]

/-- The steered vector `rotR alpha *ᵥ ![c,0]` is nonzero for `c > 0`. -/
theorem steered_ne_zero (c : ℝ) (hc : 0 < c) (alpha : ℝ) :
    rotR alpha *ᵥ ![c, 0] ≠ 0 := by
  intro h
  have h0 : l2norm (rotR alpha *ᵥ ![c, 0]) = 0 := by rw [h]; simp [l2norm]
  rw [l2norm_steered c hc alpha] at h0
  linarith

/-- The AB temperature numerator for the steered vector. -/
theorem rotJ_dot_steered (c : ℝ) (G : Fin 2 → ℝ) (alpha : ℝ) :
    (rotJ *ᵥ (rotR alpha *ᵥ ![c, 0])) ⬝ᵥ G
      = c * (G 1 * Real.cos alpha - G 0 * Real.sin alpha) := by
  rw [rotJ_mulVec, dotProduct, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [rotR_mulVec_zero, rotR_mulVec_one]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **The Rayleigh–Taylor product with both coefficients steered.** -/
theorem ab_both_formula (lam c : ℝ) (hlam : lam ≠ 0) (hc : 0 < c) (G : Fin 2 → ℝ) (alpha : ℝ) :
    abTempCoeff lam (rotR alpha *ᵥ ![c, 0]) G * abVortCoeff lam (rotR alpha *ᵥ ![c, 0])
      = -(G 1) / 2 + (G 0 / 2) * Real.sin (2 * alpha) - (G 1 / 2) * Real.cos (2 * alpha) := by
  have hz := steered_ne_zero c hc alpha
  rw [ab_product lam hlam _ G hz]
  rw [rotJ_dot_steered, l2norm_steered c hc alpha, rotR_mulVec_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Real.sin_two_mul, Real.cos_two_mul]
  have hcne : c ≠ 0 := ne_of_gt hc
  field_simp
  ring

/-! ## 2. The `lam` and `c` cancellation -/

/-- **The product depends only on the background gradient and the angle.** -/
theorem ab_both_eq_of_lambda_c {lam₁ lam₂ c₁ c₂ : ℝ} (hlam₁ : lam₁ ≠ 0) (hlam₂ : lam₂ ≠ 0)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (G : Fin 2 → ℝ) (alpha : ℝ) :
    abTempCoeff lam₁ (rotR alpha *ᵥ ![c₁, 0]) G * abVortCoeff lam₁ (rotR alpha *ᵥ ![c₁, 0])
      = abTempCoeff lam₂ (rotR alpha *ᵥ ![c₂, 0]) G * abVortCoeff lam₂ (rotR alpha *ᵥ ![c₂, 0]) := by
  rw [ab_both_formula lam₁ c₁ hlam₁ hc₁ G alpha, ab_both_formula lam₂ c₂ hlam₂ hc₂ G alpha]

/-! ## 3. Half-turn invariance -/

/-- **Half-turn invariance of the product.** -/
theorem ab_both_add_pi (lam c : ℝ) (hlam : lam ≠ 0) (hc : 0 < c) (G : Fin 2 → ℝ) (alpha : ℝ) :
    abTempCoeff lam (rotR (alpha + Real.pi) *ᵥ ![c, 0]) G
        * abVortCoeff lam (rotR (alpha + Real.pi) *ᵥ ![c, 0])
      = abTempCoeff lam (rotR alpha *ᵥ ![c, 0]) G * abVortCoeff lam (rotR alpha *ᵥ ![c, 0]) := by
  rw [ab_both_formula lam c hlam hc G (alpha + Real.pi), ab_both_formula lam c hlam hc G alpha]
  have h2 : 2 * (alpha + Real.pi) = 2 * alpha + 2 * Real.pi := by ring
  rw [h2, Real.sin_add, Real.cos_add, Real.sin_two_pi, Real.cos_two_pi]
  ring

/-! ## 4. The exact range -/

/-- Cauchy–Schwarz in `ℝ²`: `|a sin θ − b cos θ| ≤ √(a²+b²)`. -/
theorem sin_cos_combination_abs_le (a b theta : ℝ) :
    |a * Real.sin theta - b * Real.cos theta| ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
  have h : (a * Real.sin theta - b * Real.cos theta) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq theta, sq_nonneg (a * Real.cos theta + b * Real.sin theta)]
  calc |a * Real.sin theta - b * Real.cos theta|
      = Real.sqrt ((a * Real.sin theta - b * Real.cos theta) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (a ^ 2 + b ^ 2) := Real.sqrt_le_sqrt h

/-- **The exact range of the product.** -/
theorem ab_both_range (lam c : ℝ) (hlam : lam ≠ 0) (hc : 0 < c) (G : Fin 2 → ℝ) (alpha : ℝ) :
    -(G 1) / 2 - Real.sqrt (G 0 ^ 2 + G 1 ^ 2) / 2
      ≤ abTempCoeff lam (rotR alpha *ᵥ ![c, 0]) G * abVortCoeff lam (rotR alpha *ᵥ ![c, 0])
    ∧ abTempCoeff lam (rotR alpha *ᵥ ![c, 0]) G * abVortCoeff lam (rotR alpha *ᵥ ![c, 0])
      ≤ -(G 1) / 2 + Real.sqrt (G 0 ^ 2 + G 1 ^ 2) / 2 := by
  have h := abs_le.mp (sin_cos_combination_abs_le (G 0) (G 1) (2 * alpha))
  rw [ab_both_formula lam c hlam hc G alpha]
  constructor <;> linarith [h.1, h.2]

/-- `R = √(G₀²+G₁²)` is positive for a nonzero gradient. -/
theorem sqrt_sq_add_sq_pos (G : Fin 2 → ℝ) (hG : G ≠ 0) :
    0 < Real.sqrt (G 0 ^ 2 + G 1 ^ 2) := by
  rw [Real.sqrt_pos]
  by_contra h
  have hle0 : G 0 ^ 2 + G 1 ^ 2 ≤ 0 := le_of_not_gt h
  have h0 : G 0 = 0 := by nlinarith [sq_nonneg (G 0), sq_nonneg (G 1)]
  have h1 : G 1 = 0 := by nlinarith [sq_nonneg (G 0), sq_nonneg (G 1)]
  exact hG (by funext i; fin_cases i <;> simp [h0, h1])

/-- `(√(G₀²+G₁²))² = G₀²+G₁²`. -/
theorem sqrt_sq_add_sq_sq (G : Fin 2 → ℝ) :
    Real.sqrt (G 0 ^ 2 + G 1 ^ 2) ^ 2 = G 0 ^ 2 + G 1 ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The gradient direction is a point of the unit circle: there is `theta` with
`sin theta = G₀/R` and `cos theta = −G₁/R`, `R = √(G₀²+G₁²)`. -/
theorem exists_sin_eq_cos_eq (G : Fin 2 → ℝ) (hG : G ≠ 0) :
    ∃ theta : ℝ, Real.sin theta = G 0 / Real.sqrt (G 0 ^ 2 + G 1 ^ 2) ∧
      Real.cos theta = -(G 1) / Real.sqrt (G 0 ^ 2 + G 1 ^ 2) := by
  set R := Real.sqrt (G 0 ^ 2 + G 1 ^ 2) with hR
  have hRpos : 0 < R := by rw [hR]; exact sqrt_sq_add_sq_pos G hG
  have hRsq : R ^ 2 = G 0 ^ 2 + G 1 ^ 2 := by rw [hR]; exact sqrt_sq_add_sq_sq G
  have hle : |G 1| ≤ R := by
    rw [hR, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (G 0)])
  obtain ⟨h1lo, h1hi⟩ := abs_le.mp hle
  have hmem : -1 ≤ -(G 1) / R ∧ -(G 1) / R ≤ 1 := by
    constructor
    · rw [le_div_iff₀ hRpos]; linarith
    · rw [div_le_iff₀ hRpos]; linarith
  have hsqrt : Real.sqrt (1 - (-(G 1) / R) ^ 2) = |G 0| / R := by
    have h : 1 - (-(G 1) / R) ^ 2 = (G 0 / R) ^ 2 := by
      field_simp
      linarith [hRsq]
    rw [h, Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hRpos]
  by_cases h0 : 0 ≤ G 0
  · refine ⟨Real.arccos (-(G 1) / R), ?_, ?_⟩
    · rw [Real.sin_arccos, hsqrt, abs_of_nonneg h0]
    · exact Real.cos_arccos hmem.1 hmem.2
  · have h0' : G 0 < 0 := not_le.mp h0
    refine ⟨-(Real.arccos (-(G 1) / R)), ?_, ?_⟩
    · rw [Real.sin_neg, Real.sin_arccos, hsqrt, abs_of_neg h0']
      ring
    · rw [Real.cos_neg]
      exact Real.cos_arccos hmem.1 hmem.2

/-- **The maximum of the range is attained.** -/
theorem ab_both_max_attained (lam c : ℝ) (hlam : lam ≠ 0) (hc : 0 < c) (G : Fin 2 → ℝ)
    (hG : G ≠ 0) :
    ∃ alpha, abTempCoeff lam (rotR alpha *ᵥ ![c, 0]) G * abVortCoeff lam (rotR alpha *ᵥ ![c, 0])
          = -(G 1) / 2 + Real.sqrt (G 0 ^ 2 + G 1 ^ 2) / 2 := by
  obtain ⟨theta, hsin, hcos⟩ := exists_sin_eq_cos_eq G hG
  refine ⟨theta / 2, ?_⟩
  rw [ab_both_formula lam c hlam hc G (theta / 2)]
  have h2 : 2 * (theta / 2) = theta := by ring
  rw [h2, hsin, hcos]
  have hRsq := sqrt_sq_add_sq_sq G
  have hRne : Real.sqrt (G 0 ^ 2 + G 1 ^ 2) ≠ 0 := ne_of_gt (sqrt_sq_add_sq_pos G hG)
  field_simp
  nlinarith [hRsq]

/-- **The minimum of the range is attained.** -/
theorem ab_both_min_attained (lam c : ℝ) (hlam : lam ≠ 0) (hc : 0 < c) (G : Fin 2 → ℝ)
    (hG : G ≠ 0) :
    ∃ alpha, abTempCoeff lam (rotR alpha *ᵥ ![c, 0]) G * abVortCoeff lam (rotR alpha *ᵥ ![c, 0])
          = -(G 1) / 2 - Real.sqrt (G 0 ^ 2 + G 1 ^ 2) / 2 := by
  obtain ⟨theta, hsin, hcos⟩ := exists_sin_eq_cos_eq G hG
  refine ⟨(theta + Real.pi) / 2, ?_⟩
  rw [ab_both_formula lam c hlam hc G ((theta + Real.pi) / 2)]
  have h2 : 2 * ((theta + Real.pi) / 2) = theta + Real.pi := by ring
  rw [h2, Real.sin_add, Real.cos_add, Real.sin_pi, Real.cos_pi, hsin, hcos]
  have hRsq := sqrt_sq_add_sq_sq G
  have hRne : Real.sqrt (G 0 ^ 2 + G 1 ^ 2) ≠ 0 := ne_of_gt (sqrt_sq_add_sq_pos G hG)
  field_simp
  nlinarith [hRsq]

/-! ## 5. When can steering produce growth at all? -/

/-- **The sign of the product is steerable iff the gradient is not vertical-and-up.** -/
theorem ab_both_positive_iff (lam c : ℝ) (hlam : lam ≠ 0) (hc : 0 < c) (G : Fin 2 → ℝ) :
    (∃ alpha, 0 < abTempCoeff lam (rotR alpha *ᵥ ![c, 0]) G * abVortCoeff lam (rotR alpha *ᵥ ![c, 0]))
      ↔ (G 0 ≠ 0 ∨ G 1 < 0) := by
  constructor
  · rintro ⟨alpha, hα⟩
    have hb := (ab_both_range lam c hlam hc G alpha).2
    have hG1lt : G 1 < Real.sqrt (G 0 ^ 2 + G 1 ^ 2) := by linarith
    by_contra hcon
    have h0 : G 0 = 0 := by by_contra h0; exact hcon (Or.inl h0)
    have h1 : 0 ≤ G 1 := by by_contra h1; exact hcon (Or.inr (not_le.mp h1))
    have hReq : Real.sqrt (G 0 ^ 2 + G 1 ^ 2) = G 1 := by
      rw [h0, show (0 : ℝ) ^ 2 = 0 by norm_num, zero_add, Real.sqrt_sq_eq_abs, abs_of_nonneg h1]
    linarith
  · intro h
    have hGne : G ≠ 0 := by
      intro hG
      have h1z : G 1 = 0 := by rw [hG]; rfl
      rcases h with h0 | h1
      · exact h0 (by rw [hG]; rfl)
      · rw [h1z] at h1
        exact absurd h1 (lt_irrefl 0)
    obtain ⟨alpha, hα⟩ := ab_both_max_attained lam c hlam hc G hGne
    refine ⟨alpha, ?_⟩
    rw [hα]
    have hR : G 1 < Real.sqrt (G 0 ^ 2 + G 1 ^ 2) := by
      rcases h with h0 | h1
      · have hsq : G 1 ^ 2 < G 0 ^ 2 + G 1 ^ 2 := by
          have : 0 < G 0 ^ 2 := sq_pos_of_ne_zero h0
          nlinarith
        calc G 1 ≤ |G 1| := le_abs_self (G 1)
          _ = Real.sqrt (G 1 ^ 2) := (Real.sqrt_sq_eq_abs (G 1)).symm
          _ < Real.sqrt (G 0 ^ 2 + G 1 ^ 2) := Real.sqrt_lt_sqrt (by positivity) hsq
      · have := Real.sqrt_nonneg (G 0 ^ 2 + G 1 ^ 2)
        linarith
    linarith

/-! ## 6. The stably-stratified case -/

/-- **A purely upward gradient cannot produce growth.** -/
theorem ab_both_vertical_nonpos (lam c : ℝ) (hlam : lam ≠ 0) (hc : 0 < c) (G : Fin 2 → ℝ)
    (h0 : G 0 = 0) (h1 : 0 ≤ G 1) (alpha : ℝ) :
    abTempCoeff lam (rotR alpha *ᵥ ![c, 0]) G * abVortCoeff lam (rotR alpha *ᵥ ![c, 0]) ≤ 0 := by
  rw [ab_both_formula lam c hlam hc G alpha, h0]
  have hcos : Real.cos (2 * alpha) = 2 * Real.cos alpha ^ 2 - 1 := Real.cos_two_mul alpha
  nlinarith [hcos, sq_nonneg (Real.cos alpha), h1]

/-! ## 7. Non-vacuity and the sanity checks -/

/-- Sanity check at `alpha = 0`: the product is `-G₁`. -/
example (lam c : ℝ) (hlam : lam ≠ 0) (hc : 0 < c) (G : Fin 2 → ℝ) :
    abTempCoeff lam (rotR 0 *ᵥ ![c, 0]) G * abVortCoeff lam (rotR 0 *ᵥ ![c, 0]) = -(G 1) := by
  rw [ab_both_formula lam c hlam hc G 0]
  simp [Real.sin_zero, Real.cos_zero]
  ring

/-- Sanity check at `alpha = pi/2`: the product is `0`. -/
example (lam c : ℝ) (hlam : lam ≠ 0) (hc : 0 < c) (G : Fin 2 → ℝ) :
    abTempCoeff lam (rotR (Real.pi / 2) *ᵥ ![c, 0]) G
      * abVortCoeff lam (rotR (Real.pi / 2) *ᵥ ![c, 0]) = 0 := by
  rw [ab_both_formula lam c hlam hc G (Real.pi / 2)]
  have h : 2 * (Real.pi / 2) = Real.pi := by ring
  rw [h, Real.sin_pi, Real.cos_pi]
  ring

/-- Sanity check at `alpha = pi/4`: the product is `(G₀ - G₁)/2`. -/
example (lam c : ℝ) (hlam : lam ≠ 0) (hc : 0 < c) (G : Fin 2 → ℝ) :
    abTempCoeff lam (rotR (Real.pi / 4) *ᵥ ![c, 0]) G
      * abVortCoeff lam (rotR (Real.pi / 4) *ᵥ ![c, 0]) = (G 0 - G 1) / 2 := by
  rw [ab_both_formula lam c hlam hc G (Real.pi / 4)]
  have h : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
  rw [h, Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

/-- Concrete numbers: `G = ![1,0]`, `alpha = pi/4` gives product `1/2`. -/
example : abTempCoeff 1 (rotR (Real.pi / 4) *ᵥ ![1, 0]) ![1, 0]
    * abVortCoeff 1 (rotR (Real.pi / 4) *ᵥ ![1, 0]) = 1 / 2 := by
  rw [ab_both_formula 1 1 (by norm_num) (by norm_num) ![1, 0] (Real.pi / 4)]
  have h : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
  rw [h, Real.sin_pi_div_two, Real.cos_pi_div_two]
  norm_num

/-- `G = ![0,1]`: no steering angle gives growth. -/
example (alpha : ℝ) : abTempCoeff 1 (rotR alpha *ᵥ ![1, 0]) ![0, 1]
    * abVortCoeff 1 (rotR alpha *ᵥ ![1, 0]) ≤ 0 :=
  ab_both_vertical_nonpos 1 1 (by norm_num) (by norm_num) ![0, 1] rfl (by norm_num) alpha

/-- `G = ![0,1]`, `alpha = pi/2`: the product is `0`. -/
example : abTempCoeff 1 (rotR (Real.pi / 2) *ᵥ ![1, 0]) ![0, 1]
    * abVortCoeff 1 (rotR (Real.pi / 2) *ᵥ ![1, 0]) = 0 := by
  rw [ab_both_formula 1 1 (by norm_num) (by norm_num) ![0, 1] (Real.pi / 2)]
  have h : 2 * (Real.pi / 2) = Real.pi := by ring
  rw [h, Real.sin_pi, Real.cos_pi]
  norm_num

/-- The `lam`, `c` cancellation at concrete values `(1,1)` versus `(3,2)`. -/
example : abTempCoeff 1 (rotR (Real.pi / 4) *ᵥ ![1, 0]) ![1, 0]
      * abVortCoeff 1 (rotR (Real.pi / 4) *ᵥ ![1, 0])
    = abTempCoeff 3 (rotR (Real.pi / 4) *ᵥ ![2, 0]) ![1, 0]
      * abVortCoeff 3 (rotR (Real.pi / 4) *ᵥ ![2, 0]) :=
  ab_both_eq_of_lambda_c (by norm_num) (by norm_num) (by norm_num) (by norm_num) ![1, 0]
    (Real.pi / 4)

/-- Half-turn invariance at concrete values, and the contrast with `PhaseGrowth`. -/
example : abTempCoeff 1 (rotR (Real.pi / 2 + Real.pi) *ᵥ ![1, 0]) ![0, 1]
      * abVortCoeff 1 (rotR (Real.pi / 2 + Real.pi) *ᵥ ![1, 0])
    = abTempCoeff 1 (rotR (Real.pi / 2) *ᵥ ![1, 0]) ![0, 1]
      * abVortCoeff 1 (rotR (Real.pi / 2) *ᵥ ![1, 0]) :=
  ab_both_add_pi 1 1 (by norm_num) (by norm_num) ![0, 1] (Real.pi / 2)

/-- The half turn of `PhaseGrowth` no longer flips the product. -/
example : abTempCoeff 1 (rotR 0 *ᵥ ![1, 0]) ![0, 1] * abVortCoeff 1 (rotR 0 *ᵥ ![1, 0]) = -1
    ∧ abTempCoeff 1 (rotR Real.pi *ᵥ ![1, 0]) ![0, 1]
        * abVortCoeff 1 (rotR Real.pi *ᵥ ![1, 0]) = -1 := by
  constructor
  · rw [ab_both_formula 1 1 (by norm_num) (by norm_num) ![0, 1] 0]
    simp [Real.sin_zero, Real.cos_zero]
    norm_num
  · rw [ab_both_formula 1 1 (by norm_num) (by norm_num) ![0, 1] Real.pi]
    rw [Real.sin_two_pi, Real.cos_two_pi]
    norm_num

/-- Non-vacuity of the sign criterion: `G = ![1,0]` admits growth. -/
example : ∃ alpha, 0 < abTempCoeff 1 (rotR alpha *ᵥ ![1, 0]) ![1, 0]
    * abVortCoeff 1 (rotR alpha *ᵥ ![1, 0]) :=
  (ab_both_positive_iff 1 1 (by norm_num) (by norm_num) ![1, 0]).mpr (Or.inl (by norm_num))

/-- Non-vacuity of the sign criterion: `G = ![0,1]` admits no growth. -/
example : ¬ (∃ alpha, 0 < abTempCoeff 1 (rotR alpha *ᵥ ![1, 0]) ![0, 1]
    * abVortCoeff 1 (rotR alpha *ᵥ ![1, 0])) := by
  rw [ab_both_positive_iff 1 1 (by norm_num) (by norm_num) ![0, 1]]
  simp

/-- Non-vacuity of the maximum: for `G = ![1,0]` the maximum `1/2` is attained. -/
example : ∃ alpha, abTempCoeff 1 (rotR alpha *ᵥ ![1, 0]) ![1, 0]
    * abVortCoeff 1 (rotR alpha *ᵥ ![1, 0]) = 1 / 2 := by
  simpa using
    ab_both_max_attained 1 1 (by norm_num) (by norm_num) ![1, 0] (by
      intro h
      have := congrFun h 0
      simp at this)

/-- Non-vacuity of the minimum: for `G = ![1,0]` the minimum `-1/2` is attained. -/
example : ∃ alpha, abTempCoeff 1 (rotR alpha *ᵥ ![1, 0]) ![1, 0]
    * abVortCoeff 1 (rotR alpha *ᵥ ![1, 0]) = -1 / 2 := by
  obtain ⟨alpha, halpha⟩ :=
    ab_both_min_attained 1 1 (by norm_num) (by norm_num) ![1, 0] (by
      intro h
      have := congrFun h 0
      simp at this)
  exact ⟨alpha, by rw [halpha]; norm_num⟩

end Cascade

#print axioms Cascade.l2norm_steered
#print axioms Cascade.steered_ne_zero
#print axioms Cascade.rotJ_dot_steered
#print axioms Cascade.ab_both_formula
#print axioms Cascade.ab_both_eq_of_lambda_c
#print axioms Cascade.ab_both_add_pi
#print axioms Cascade.sin_cos_combination_abs_le
#print axioms Cascade.ab_both_range
#print axioms Cascade.sqrt_sq_add_sq_pos
#print axioms Cascade.sqrt_sq_add_sq_sq
#print axioms Cascade.exists_sin_eq_cos_eq
#print axioms Cascade.ab_both_max_attained
#print axioms Cascade.ab_both_min_attained
#print axioms Cascade.ab_both_positive_iff
#print axioms Cascade.ab_both_vertical_nonpos
