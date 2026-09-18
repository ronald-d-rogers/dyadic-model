import Cascade.ScaleObstruction
import Cascade.TruncatedRegularity

/-!
# The one-mode-per-octave dyadic model is dimension-blind

## What this file records, honestly

`Cascade/ScaleObstruction.lean`'s header observes *in prose* that the shell amplitude bound

`|vorticity u k| ≤ √H`,  `H = enstrophy u N = ∑_{j<N} (vorticity u j)²`,

is dimension-free and therefore strictly stronger than the spatial Bernstein bound
`N_k^{d/2} √E` that produces Palasek's obstruction.  This file turns that observation into
theorems.  **The algebra is elementary — essentially definitional — and the docstring says so on
purpose: the content here is the interpretation, not the inequalities.**  The four statements below
are consequences of `vorticity u k = dyadicWeight k * u k` and `dyadicWeight (2k) = dyadicWeight k ^ 2`
together with monotonicity of `k ↦ 2^k`; none of them uses the dynamics, the transfer, or any
solution predicate.

## The interpretation, in full

Write `N_k = dyadicWeight k = 2^k` and recall the model's amplitude `a_k = vorticity u k = N_k u_k`
and enstrophy `H = enstrophy u N = ∑_{k<N} a_k²`.

(a) **The statements are elementary.**  Squaring the definition gives the *identity*
`a_k² = dyadicWeight (2k) · u_k²` (`bernstein_equality_at_two`), and Bernstein's spatial constraint
in dimension `d` is the same expression with `2k` replaced by `d k`.  The comparison is therefore
only the arithmetic fact `2k ≤ dk` for `k ≥ 0`, `d ≥ 2`.  Nothing dynamical is used.

(b) **Consequence: no Bernstein-type insertion makes the dimension intrinsic.**  For every integer
`d ≥ 2` and every `k ≥ 0` the Bernstein constraint
`a_k² ≤ dyadicWeight (d k) · u_k²` is implied by the definitions alone
(`bernstein_constraint_vacuous`) — it holds for *every* state `u : ℤ → ℝ`.  A constraint that every
state satisfies adds no information to a one-mode-per-octave dyadic model, so inserting a
Bernstein inequality cannot make the spatial dimension an intrinsic parameter of such a model.
At `d = 2` the model *is* exactly the Bernstein-saturated model (`bernstein_equality_at_two`),
and for every `d > 2` the envelope strictly exceeds the model's own amplitude on every nonzero
mode (`bernstein_envelope_strict_of_two_lt`).

(c) **What such an insertion actually does.**  The model's sharp, dimension-free bound
`|vorticity u k| ≤ √H` (proved in `Cascade/ScaleObstruction.lean` as
`vorticity_abs_le_sqrt_enstrophy`; its header is the earlier prose statement of this point) can only
be *replaced* by the weaker, scale-growing envelope `N_k^{d/2} √E`, where `E` is the energy.  That
re-imports by hand exactly the `d/2` the shell model had eliminated.

(d) **Hence the crossover is an artifact.**  The dimensional dichotomy `d/2`-versus-`2` isolated in
`Cascade/BernsteinTransfer.lean` is a property of the inserted Bernstein envelope, not a feature of
the shell dynamics.  A one-mode-per-octave dyadic model has no intrinsic dimension; any dimensional
crossover it appears to exhibit is produced by the constraint that was inserted into it, not by the
model itself.

(e) **The ceiling is the concentration barrier — a see-saw, not a prohibition.**  The envelope
`2^{dk/2}√E` and the `d = 2` saturation identity are the Fourier **concentration barrier** of
Pillar A: `Cascade/ConcentrationBarrier.lean` states the core fact (a Schwartz function's pointwise
value is bounded by the `L¹` norm of its Fourier transform) and `Criticality/Heisenberg.lean` gives
its commutator form.  The *intermittency dimension* `δ` of the turbulence-modelling literature is
defined as the saturation level of exactly this barrier, via
`‖v_j‖_∞ ∼ λ_j^{(n−δ)/2}‖v_j‖_{L²}`; so `δ = 0` — the worst case the calibration assumes — *is* the
barrier, and `δ = n` is no concentration at all.  This is a ceiling on how much can be squeezed into
a small scale, and it is a trade-off: concentrate in space and the frequency spread grows.  It is
**not** the Pauli exclusion principle, which is not an inequality at all but the antisymmetry of a
multi-fermion state and cannot be obtained from any Cauchy–Schwarz estimate.  The two are easily
conflated ("things cannot be on top of each other"); see the scope note in
`Criticality/Heisenberg.lean`.

## Contents

1. `bernstein_constraint_vacuous` — Bernstein in dimension `d ≥ 2` holds for every state.
2. `bernstein_equality_at_two` — the model is exactly Bernstein-saturated in dimension `2`.
3. `bernstein_envelope_strict_of_two_lt` — for `d > 2` the envelope is strictly larger, mode by mode.
4. `bernstein_envelope_factor` — the loss factor is `dyadicWeight ((d - 2) k)`.
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators

namespace Cascade

/-! ## 1. Bernstein's constraint is vacuous

Bernstein's `L² → L∞` amplitude bound in dimension `d` reads, in shell variables and squared,
`a_k² ≤ dyadicWeight (d k) · u_k²`.  Since the model's own amplitude gives
`a_k² = dyadicWeight (2k) · u_k²`, the "constraint" is the arithmetic fact `2k ≤ dk`. -/

/-- **Bernstein's amplitude constraint holds for every state.**  For every integer `d ≥ 2`, every
`k ≥ 0` and every `u : ℤ → ℝ`, the Bernstein envelope in dimension `d` dominates the model's
amplitude squared:

`(vorticity u k)² ≤ dyadicWeight (d k) · (u k)²`.

The proof is the identity `vorticity_sq` followed by `2k ≤ dk` and monotonicity of `dyadicWeight`.
Imposing this "constraint" therefore adds no information: it is satisfied by *every* state. -/
theorem bernstein_constraint_vacuous (d : ℤ) (hd : 2 ≤ d) (k : ℤ) (hk : 0 ≤ k) (u : ℤ → ℝ) :
    (vorticity u k) ^ 2 ≤ dyadicWeight (d * k) * (u k) ^ 2 := by
  rw [vorticity_sq]
  exact mul_le_mul_of_nonneg_right
    (dyadicWeight_mono (mul_le_mul_of_nonneg_right hd hk)) (sq_nonneg _)

/-! ## 2. The model is exactly Bernstein-saturated in dimension `2` -/

/-- **The one-mode-per-octave model is exactly the Bernstein-saturated model in dimension `2`.**
This is the identity `a_k² = dyadicWeight (2k) · u_k²`; it is *definitional* (it is the existing
theorem `vorticity_sq`, restated here under the name this file's narrative uses), so the proof is
one line and carries no mathematical content beyond the definition of `vorticity`. -/
theorem bernstein_equality_at_two (u : ℤ → ℝ) (k : ℤ) :
    (vorticity u k) ^ 2 = dyadicWeight (2 * k) * (u k) ^ 2 :=
  vorticity_sq u k

/-! ## 3. For `d > 2` the envelope strictly exceeds the model's amplitude -/

/-- **Every dimension above `2` loses information.**  For `d > 2`, `k > 0` and a nonzero mode
`u k ≠ 0`, the Bernstein envelope is *strictly* larger than the model's amplitude squared:

`(vorticity u k)² < dyadicWeight (d k) · (u k)²`.

Indeed `2k < dk` and `dyadicWeight` is strictly increasing, while `(u k)² > 0`.  So substituting
the Bernstein envelope for the model's own amplitude is a genuine loss, mode by mode. -/
theorem bernstein_envelope_strict_of_two_lt (d : ℤ) (hd : 2 < d) (k : ℤ) (hk : 0 < k)
    (u : ℤ → ℝ) (hu : u k ≠ 0) :
    (vorticity u k) ^ 2 < dyadicWeight (d * k) * (u k) ^ 2 := by
  rw [vorticity_sq]
  have hw : dyadicWeight (2 * k) < dyadicWeight (d * k) := by
    rw [dyadicWeight, dyadicWeight]
    exact (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr
      (mul_lt_mul_of_pos_right hd hk)
  exact mul_lt_mul_of_pos_right hw (sq_pos_of_ne_zero hu)

/-! ## 4. The loss factor -/

/-- **The loss factor is `dyadicWeight ((d - 2) k)`.**  The ratio between the Bernstein envelope
`dyadicWeight (d k) · u_k²` and the model's amplitude squared `(vorticity u k)²` is
`dyadicWeight ((d - 2) k) = 2^{(d-2)k}`:

`dyadicWeight (d k) · (u k)² = dyadicWeight ((d - 2) k) · (vorticity u k)²`.

This is the exact factor by which the inserted constraint inflates the model's amplitude; it is
`1` precisely at `d = 2` and grows with `k` (and with `d`) otherwise. -/
theorem bernstein_envelope_factor (u : ℤ → ℝ) (d k : ℤ) :
    dyadicWeight (d * k) * (u k) ^ 2 = dyadicWeight ((d - 2) * k) * (vorticity u k) ^ 2 := by
  rw [vorticity_sq]
  have h : ((d - 2) * k) + 2 * k = d * k := by ring
  rw [← mul_assoc, ← dyadicWeight_add, h]

/-! ## 5. Non-vacuity

The strictness in item 3 has content: at `d = 3`, `k = 1` and the single mode `u 1 = 1`, the
model's amplitude squared is `(2 · 1)² = 4` while the Bernstein envelope is `2³ · 1 = 8`.  This
also shows the nonzero-mode hypothesis `u k ≠ 0` of item 3 is satisfiable. -/

/-- The strict inequality at `d = 3`, `k = 1`, `u 1 = 1`: `4 < 8`. -/
example : (vorticity (fun k : ℤ => if k = 1 then (1 : ℝ) else 0) 1) ^ 2
    < dyadicWeight (3 * 1) * ((fun k : ℤ => if k = 1 then (1 : ℝ) else 0) 1) ^ 2 :=
  bernstein_envelope_strict_of_two_lt 3 (by norm_num) 1 (by norm_num) _ (by norm_num)

end Cascade

/-! ## Axiom audit -/

#print axioms Cascade.bernstein_constraint_vacuous
#print axioms Cascade.bernstein_equality_at_two
#print axioms Cascade.bernstein_envelope_strict_of_two_lt
#print axioms Cascade.bernstein_envelope_factor
