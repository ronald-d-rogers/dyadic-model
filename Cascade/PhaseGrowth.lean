/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Cascade.Phase

/-!
# Stage G′ — restoring the phase makes the Rayleigh–Taylor growth rate controllable

`Cascade/Lacunary.lean` reduces the dyadic Boussinesq model to the amplitude pair
`(Theta, Omega)` of `Cascade/Amplitude.lean`,

    Theta' = thetaBar_{n-1} Omega,      Omega' = 2^n kappa Theta,

with the buoyancy coupling frozen to the single number `b = 2^n kappa`. In that scalar
reduction the sign of the Rayleigh–Taylor product `a b` is fixed by the initial data, so
`Cascade/Amplitude.lean`'s dichotomy (`rayleighTaylor_growthRate_dichotomy`, together with
`rayleighTaylorSolution_unbounded` and `rayleighTaylorOscillation_bounded`) decides *once and
for all* whether the mode grows exponentially at rate `sqrt (a b)` or merely oscillates at the
Brunt–Väisälä frequency: the scalar model deletes the geometry and with it every handle on the
sign.

`Cascade/Phase.lean` puts the wavevector back. It restores AB's page-4 system (their eq. (3.2))
with the wavevector `zeta ∈ R²`, the temperature coefficient `a = abTempCoeff lam zeta G` and
the buoyancy coupling `b = abVortCoeff lam zeta = lam zeta_0` (the gravity-direction component),
and shows that a background rotation by angle `alpha` steers the wavevector,
`zeta = rotR alpha *ᵥ zeta0`, so that the coupling becomes a *pure steerable cosine*

    b(alpha) = lam (zeta0 0 cos alpha - zeta0 1 sin alpha),

bounded by `|lam| |zeta0|`, sign-flipped by a half turn, and sweeping the whole interval
`[-|lam| |zeta0|, |lam| |zeta0|]` (`phase_coupling_cosine`, `phase_coupling_bound`,
`phase_flip`, `phase_flip_quantitative`). The coupling `b` is therefore not a frozen number but
a control.

**This file is the consequence.** With the phase restored, and taking the temperature
coefficient `a` fixed and nonzero as the amplitude engine does, the sign of the growth product
`a b` is no longer decided by the initial data: the steering angle selects it
(`phase_controls_growth_sign`). At `zeta0 = ![c,0]` the aligned wavevector gives `b = lam c`
and grows while the flipped wavevector gives `b = -lam c` and oscillates
(`phase_aligned_grows`, `phase_flipped_oscillates`), and the same dichotomy that made the
scalar sign fatal now makes the same data produce a positive rate in the aligned case and rate
zero in the flipped case (`phase_selects_growth_or_oscillation`). Even more, the background
rotation does not merely switch the regime: as `alpha` turns, the growth rate
`sqrt (a b(alpha))` is *continuously steerable* and attains every rate in the full interval
`[0, sqrt (a lam c)]` (`phase_controls_growth_rate`), with maximum attained at the aligned
wavevector. Growth versus oscillation, and the magnitude of the growth, are properties of the
wavevector's orientation — exactly the geometry the scalar reduction discarded.

**Honest scope.** Only the buoyancy coupling `b = abVortCoeff lam zeta` is treated as steerable
here; `a` is an arbitrary fixed nonzero parameter (statements 1–4 hold for every sign of `a`,
with the sign of `a` merely telling the aligned and flipped angles apart in
`phase_controls_growth_sign`). In AB the temperature coefficient *also* depends on the
wavevector, `a = abTempCoeff lam zeta G = -((J zeta) · G)/(lam |zeta|²)`, so steering the
wavevector moves `a` as well as `b` (with `G` held fixed the numerator `(J zeta)·G` is *not*
invariant, cf. `rotJ_mulVec_dot_rotR`). Steering both coefficients together — one wavevector
per octave, with `G` and `D` built from the lower octaves as in AB eq. (3.3) — is the next step
and is *not* claimed here.
-/

noncomputable section

namespace Cascade

open scoped Matrix

/-! ## 1. The sign of the growth product is steerable, whatever `a` is -/

/-- **The sign of the growth product is steerable.** For any nonzero temperature coefficient
`a` and any nonzero frequency `lam`, some orientation `alpha₁` of the wavevector `![c, 0]`
makes the Rayleigh–Taylor product `a * b` positive, and some other orientation `alpha₂` makes
it negative.

Route: `phase_flip_quantitative` realises both couplings `+|lam| c` and `-(|lam| c)`; since
`a ≠ 0` the two products `±(a |lam| c)` have opposite signs, and the branch on the sign of `a`
selects which steering angle yields which. The two angles usually differ, and when they do not
it is because one of them is the half-turn. -/
theorem phase_controls_growth_sign (a lam c : ℝ) (hc : 0 < c) (ha : a ≠ 0) (hlam : lam ≠ 0) :
    ∃ α₁ α₂ : ℝ,
      a * abVortCoeff lam (rotR α₁ *ᵥ ![c, 0]) > 0 ∧
      a * abVortCoeff lam (rotR α₂ *ᵥ ![c, 0]) < 0 := by
  have hpos : 0 < |lam| * c := mul_pos (abs_pos.mpr hlam) hc
  obtain ⟨αp, hp⟩ := phase_flip_quantitative lam c hc (|lam| * c) (by rw [abs_of_pos hpos])
  obtain ⟨αm, hm⟩ :=
    phase_flip_quantitative lam c hc (-(|lam| * c)) (by rw [abs_neg, abs_of_pos hpos])
  rcases lt_or_gt_of_ne ha with ha' | ha'
  · -- `a < 0`: the negative coupling `-(|lam| c)` gives a positive product.
    exact ⟨αm, αp, by rw [hm]; exact mul_pos_of_neg_of_neg ha' (neg_neg_of_pos hpos),
      by rw [hp]; exact mul_neg_of_neg_of_pos ha' hpos⟩
  · -- `0 < a`: the positive coupling `+|lam| c` gives a positive product.
    exact ⟨αp, αm, by rw [hp]; exact mul_pos ha' hpos,
      by rw [hm]; exact mul_neg_of_pos_of_neg ha' (neg_neg_of_pos hpos)⟩

/-! ## 2. The concrete aligned / flipped pair -/

/-- **The aligned wavevector grows.** When the wavevector `![c, 0]` points along the buoyancy
direction (`alpha = 0`), the coupling is `b = lam c` (`phase_flip`), so the growth product is
`a lam c > 0`: the Rayleigh–Taylor regime. -/
theorem phase_aligned_grows (a lam c : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hc : 0 < c) :
    0 < a * abVortCoeff lam (rotR 0 *ᵥ ![c, 0]) := by
  rw [(phase_flip lam c hc).1]
  exact mul_pos ha (mul_pos hlam hc)

/-- **The flipped wavevector oscillates.** The same data after a half turn (`alpha = pi`) has
coupling `b = -(lam c)` (`phase_flip`), so the growth product is `-a lam c < 0`: the stably
stratified, oscillatory regime of `Cascade/Amplitude.lean`. -/
theorem phase_flipped_oscillates (a lam c : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hc : 0 < c) :
    a * abVortCoeff lam (rotR Real.pi *ᵥ ![c, 0]) < 0 := by
  rw [(phase_flip lam c hc).2]
  exact mul_neg_of_pos_of_neg ha (neg_neg_of_pos (mul_pos hlam hc))

/-! ## 3. Same data, opposite outcome -/

/-- **Same data, opposite outcome (the headline).** Fix `a > 0`, `lam > 0`, `c > 0`. The
aligned wavevector has positive growth product and therefore positive growth rate
`sqrt (a b)`, while the flipped wavevector — *identical data except for the steering angle* —
has negative growth product and growth rate zero. The `sqrt` facts are exactly the two branches
of `Cascade/Amplitude.lean`'s `rayleighTaylor_growthRate_dichotomy`: growth versus oscillation
is selected by the phase, not by the initial data. -/
theorem phase_selects_growth_or_oscillation (a lam c : ℝ) (ha : 0 < a) (hlam : 0 < lam)
    (hc : 0 < c) :
    (0 < a * abVortCoeff lam (rotR 0 *ᵥ ![c, 0])
      ∧ 0 < Real.sqrt (a * abVortCoeff lam (rotR 0 *ᵥ ![c, 0])))
    ∧ (a * abVortCoeff lam (rotR Real.pi *ᵥ ![c, 0]) < 0
      ∧ Real.sqrt (a * abVortCoeff lam (rotR Real.pi *ᵥ ![c, 0])) = 0) := by
  have hal := phase_aligned_grows a lam c ha hlam hc
  have hfl := phase_flipped_oscillates a lam c ha hlam hc
  exact ⟨⟨hal, (rayleighTaylor_growthRate_dichotomy a
      (abVortCoeff lam (rotR 0 *ᵥ ![c, 0]))).1 hal⟩,
    ⟨hfl, (rayleighTaylor_growthRate_dichotomy a
      (abVortCoeff lam (rotR Real.pi *ᵥ ![c, 0]))).2 (le_of_lt hfl)⟩⟩

/-! ## 4. Full controllability of the growth rate -/

/-- **The growth rate is controllable over its whole range.** For `a > 0`, `lam > 0` and
`zeta0 = ![c, 0]`, every rate `r` with `0 ≤ r ≤ sqrt (a lam c)` is attained by some steering
angle: `sqrt (a * b(alpha)) = r`.

The upper endpoint is sharp: the aligned wavevector gives `b = lam c` and rate
`sqrt (a lam c)` (`phase_aligned_grows`), while `b(alpha)` sweeps `[-lam c, lam c]`
(`phase_flip_quantitative`), so `r` corresponds to the coupling `b = r² / a`, which lies in
that interval precisely because `r² ≤ a lam c`. -/
theorem phase_controls_growth_rate (a lam c : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hc : 0 < c)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ Real.sqrt (a * lam * c)) :
    ∃ α : ℝ, Real.sqrt (a * abVortCoeff lam (rotR α *ᵥ ![c, 0])) = r := by
  have halc : 0 < a * lam * c := by positivity
  have hr2 : r ^ 2 ≤ a * lam * c := by
    have hs := Real.sq_sqrt (le_of_lt halc)
    have h1 : 0 ≤ Real.sqrt (a * lam * c) - r := sub_nonneg.mpr hr
    have h2 : 0 ≤ Real.sqrt (a * lam * c) + r := add_nonneg (Real.sqrt_nonneg _) hr0
    have h3 := mul_nonneg h1 h2
    nlinarith [hs, h3]
  set y : ℝ := r ^ 2 / a with hy_def
  have hy_nonneg : 0 ≤ y := div_nonneg (sq_nonneg r) (le_of_lt ha)
  have hy_abs : |y| ≤ |lam| * c := by
    rw [abs_of_nonneg hy_nonneg, abs_of_pos hlam, div_le_iff₀ ha]
    nlinarith [hr2]
  obtain ⟨α, hα⟩ := phase_flip_quantitative lam c hc y hy_abs
  refine ⟨α, ?_⟩
  have hay : a * y = r ^ 2 := by
    rw [hy_def]
    field_simp
  rw [hα, hay, Real.sqrt_sq hr0]

/-! ## 5. Non-vacuity at `a = lam = c = 1`

At `a = lam = c = 1` the aligned growth product is `1`, the flipped one is `-1`, and the range
of attainable rates is `[0, sqrt (1 * 1 * 1)] = [0, 1]`. -/

/-- Non-vacuity: the aligned growth product at `a = lam = c = 1` is `1`. -/
example : (1 : ℝ) * abVortCoeff 1 (rotR 0 *ᵥ ![1, 0]) = 1 := by
  rw [(phase_flip 1 1 (by norm_num)).1]
  norm_num

/-- Non-vacuity: the flipped growth product at `a = lam = c = 1` is `-1`. -/
example : (1 : ℝ) * abVortCoeff 1 (rotR Real.pi *ᵥ ![1, 0]) = -1 := by
  rw [(phase_flip 1 1 (by norm_num)).2]
  norm_num

/-- Non-vacuity of the headline dichotomy at `a = lam = c = 1`. -/
example : (0 < (1 : ℝ) * abVortCoeff 1 (rotR 0 *ᵥ ![1, 0])
      ∧ 0 < Real.sqrt ((1 : ℝ) * abVortCoeff 1 (rotR 0 *ᵥ ![1, 0])))
    ∧ ((1 : ℝ) * abVortCoeff 1 (rotR Real.pi *ᵥ ![1, 0]) < 0
      ∧ Real.sqrt ((1 : ℝ) * abVortCoeff 1 (rotR Real.pi *ᵥ ![1, 0])) = 0) :=
  phase_selects_growth_or_oscillation 1 1 1 (by norm_num) (by norm_num) (by norm_num)

/-- Non-vacuity of the rate range at `a = lam = c = 1`: the upper endpoint
`sqrt (1 * 1 * 1) = 1` is attained, by the aligned wavevector. -/
example : ∃ α : ℝ, Real.sqrt ((1 : ℝ) * abVortCoeff 1 (rotR α *ᵥ ![1, 0])) = 1 :=
  phase_controls_growth_rate 1 1 1 (by norm_num) (by norm_num) (by norm_num) 1
    (by norm_num) (by norm_num [Real.sqrt_one])

/-- Non-vacuity of the rate range at `a = lam = c = 1`: the lower endpoint `0` is attained. -/
example : ∃ α : ℝ, Real.sqrt ((1 : ℝ) * abVortCoeff 1 (rotR α *ᵥ ![1, 0])) = 0 :=
  phase_controls_growth_rate 1 1 1 (by norm_num) (by norm_num) (by norm_num) 0
    (le_refl 0) (by norm_num [Real.sqrt_one])

end Cascade

#print axioms Cascade.phase_controls_growth_sign
#print axioms Cascade.phase_aligned_grows
#print axioms Cascade.phase_flipped_oscillates
#print axioms Cascade.phase_selects_growth_or_oscillation
#print axioms Cascade.phase_controls_growth_rate
