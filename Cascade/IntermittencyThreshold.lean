import Cascade.PerShellThreshold

/-!
# The intermittency-dimension threshold: dissipation wins through dimension `4`

## What this file is

The intermittency-dimension dyadic models put the spatial dimension `n` and the intermittency
dimension `δ` into the **nonlinearity exponent**, with the dissipation exponent pinned at `2`.

* `n = 3`: the nonlinearity exponent is `(5 − δ)/2`.  This case is **verified first-hand** in Dai,
  arXiv:2006.15094, eq. (3.7), where the amplitude is `a_j = ‖u_j‖_{L²}` and the dissipation is
  `ν λ_j²`.
* general `n`: the exponent is reported as `(2 + n − δ)/2`.  **The `n`-dependence is the reported
  generalisation and is not verified first-hand here** (see the "Prior art" section of
  `Cascade/PROGRESS.md`).

The only content is the comparison of that exponent against the dissipation exponent `2`:
exponent `< 2` means the nonlinearity loses at small scales (dissipation wins — the "obstruction"
heuristic), `= 2` is critical, `> 2` means the nonlinearity wins (no obstruction).

## What is theorem, and what is measurement

**(a) Every statement here is elementary real arithmetic.**  The mathematical content is the
exponent comparison, not the algebra; each proof is linear arithmetic on `(2 + (n:ℝ) − δ)/2`.

**(b) The empirical input is the hypothesis `2 < δ ≤ 3`** of `palasek_threshold_five`.  That is a
*measured* range, not a theorem.  Dai quotes observed `δ ≈ 2.7` from numerical simulations and
experiments, and states that Kolmogorov's space-filling case is `δ = 3`.  So the "crossover at `5`"
below is a conditional statement about a heuristic model, not a result about the Navier–Stokes
equations.

**(c) The conclusion is sensitive to that measurement.**  With `δ ≤ 2` the crossover would move
down to dimension `4` or lower (at `δ = 2` dissipation wins only through `n = 3`; at `δ = 1` only
through `n = 2`).

**(d) This is the same criticality comparison as the per-shell bar of
`Cascade/PerShellThreshold.lean`**, with the intermittency dimension `δ` playing the role the
dissipation degree `e` plays there: `e = 1` is the critical degree there, and `δ = n − 2` is the
critical intermittency dimension here — in particular `δ = 1` at `n = 3`.  Both compare a
nonlinearity exponent against the dissipation exponent `2`.  (The shared object is the
*criticality*: the bar itself is sector-specific — see `Cascade/PerShellSectorObukhov.lean`.)

## Contents

1. `intermittencyExponent` — the exponent `(2 + n − δ)/2`.
2. `intermittencyExponent_lt_two_iff`, `two_lt_intermittencyExponent_iff`,
   `intermittency_critical_iff` — the comparison against the dissipation exponent `2`.
3. `theta_three`, `three_dim_critical_iff` — the first-hand-verified `n = 3` exponent `(5 − δ)/2`.
4. `palasek_threshold_five` — under `2 < δ ≤ 3`, dissipation wins exactly through `n = 4`.
5. `palasek_threshold_five_boundary` — the `δ = 3`, `n = 5` boundary is critical, not winning.
-/

noncomputable section

namespace Cascade

/-! ## 1. The exponent -/

/-- The intermittency-dimension nonlinearity exponent `(2 + n − δ)/2`, with the spatial dimension
`n`, the intermittency dimension `δ` and the dissipation exponent pinned at `2`.

The case `n = 3` — the physically relevant one — is verified first-hand in Dai,
arXiv:2006.15094, eq. (3.7), as `(5 − δ)/2` (see `theta_three`).  The dependence on general `n` is
the *reported* generalisation `(2 + n − δ)/2`; it is not verified first-hand here. -/
def intermittencyExponent (n : ℕ) (δ : ℝ) : ℝ := (2 + (n : ℝ) - δ) / 2

/-! ## 2. The criticality comparison -/

/-- **Dissipation wins exactly below the critical intermittency dimension.**  The nonlinearity
exponent is `< 2` — the dissipation exponent — iff `(n : ℝ) < δ + 2`, i.e. iff `δ > n − 2`.  Purely
linear arithmetic. -/
theorem intermittencyExponent_lt_two_iff (n : ℕ) (δ : ℝ) :
    intermittencyExponent n δ < 2 ↔ (n : ℝ) < δ + 2 := by
  unfold intermittencyExponent
  constructor <;> intro h <;> linarith

/-- **The nonlinearity wins exactly above the critical intermittency dimension.**  The exponent is
`> 2` iff `δ + 2 < (n : ℝ)`, i.e. iff `δ < n − 2`.  Purely linear arithmetic. -/
theorem two_lt_intermittencyExponent_iff (n : ℕ) (δ : ℝ) :
    2 < intermittencyExponent n δ ↔ δ + 2 < (n : ℝ) := by
  unfold intermittencyExponent
  constructor <;> intro h <;> linarith

/-- **The critical intermittency dimension is `δ = n − 2`.**  The exponent equals the dissipation
exponent `2` exactly there.  At `n = 3` this is `δ = 1`, the model's critical intermittency
dimension.

This is the same *kind* of statement as the per-shell criticality `e = 1` in
`Cascade/PerShellThreshold.lean` (there the transfer bar is scale-invariant exactly at the
dissipation degree `e = 1`); here the intermittency dimension `δ` plays the role of the dissipation
degree `e`, and the critical value is `δ = n − 2`. -/
theorem intermittency_critical_iff (n : ℕ) (δ : ℝ) :
    intermittencyExponent n δ = 2 ↔ δ = (n : ℝ) - 2 := by
  unfold intermittencyExponent
  constructor <;> intro h <;> linarith

/-! ## 3. The first-hand-verified three-dimensional case -/

/-- **The verified `n = 3` exponent appears literally.**  At `n = 3` the general exponent is
`(5 − δ)/2`, the exponent of Dai, arXiv:2006.15094, eq. (3.7). -/
theorem theta_three (δ : ℝ) : intermittencyExponent 3 δ = (5 - δ) / 2 := by
  unfold intermittencyExponent
  ring

/-- **Dissipation wins in `3D` exactly when `δ > 1`.**  The critical value is `δ = 1`, matching
`intermittency_critical_iff` at `n = 3`. -/
theorem three_dim_critical_iff (δ : ℝ) :
    intermittencyExponent 3 δ < 2 ↔ 1 < δ := by
  rw [intermittencyExponent_lt_two_iff]
  -- `linarith` reads `((3 : ℕ) : ℝ)` as an atom, so normalise the cast to a numeral first.
  norm_num
  constructor <;> intro h <;> linarith

/-! ## 4. The integer crossover at dimension `5` -/

/-- **Palasek's threshold: under the observed range `2 < δ ≤ 3`, dissipation wins exactly through
dimension `4`.**  Equivalently, the nonlinearity stops losing at `n ≥ 5` — the integer crossover at
`5`.  This is the threshold in Palasek's unwritten remark "in high dimension, though, there is no
obstruction!".

The proof is the arithmetic seen through items 2 and 3: `intermittencyExponent n δ < 2` iff
`(n : ℝ) < δ + 2`, and on `2 < δ ≤ 3` this is iff `(n : ℝ) < 5`, i.e. iff `n ≤ 4` for `n : ℕ`.

**Boundary care.**  At `δ = 3`, `n = 5` the exponent is exactly `2` — critical, NOT `> 2`.  So the
`n ≥ 5` half of the dichotomy is *not* `2 < intermittencyExponent n δ`; it is the negation of
`< 2`.  This is why the statement is phrased as an `↔` with `n ≤ 4` (see also
`palasek_threshold_five_boundary`).

**Honest scope.**  The hypothesis `2 < δ ≤ 3` is a measured range, not a theorem: Dai quotes
observed `δ ≈ 2.7` and Kolmogorov's space-filling case `δ = 3`.  This is a conditional statement
about a heuristic model, not a result about the Navier–Stokes equations; with `δ ≤ 2` the crossover
moves down to dimension `4` or lower. -/
theorem palasek_threshold_five (n : ℕ) (δ : ℝ) (hδ2 : 2 < δ) (hδ3 : δ ≤ 3) :
    intermittencyExponent n δ < 2 ↔ n ≤ 4 := by
  rw [intermittencyExponent_lt_two_iff]
  constructor
  · intro h
    have h5 : (n : ℝ) < 5 := by linarith
    have : n < 5 := by exact_mod_cast h5
    omega
  · intro h
    have hn : (n : ℝ) ≤ 4 := by exact_mod_cast h
    linarith

/-- **The `δ = 3` boundary is critical, not winning.**  At the space-filling value `δ = 3`,
`n = 4` still loses (`(4 : ℝ) < 3 + 2` strictly) while `n = 5` is exactly critical:
`intermittencyExponent 5 3 = 2` and `¬ intermittencyExponent 5 3 < 2`.  The integer crossover is
therefore genuinely at `5`, and the `n ≥ 5` side must be stated as `¬ (_ < 2)`, never as `2 < _`. -/
theorem palasek_threshold_five_boundary :
    intermittencyExponent 4 3 < 2
      ∧ intermittencyExponent 5 3 = 2
      ∧ ¬ intermittencyExponent 5 3 < 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [intermittencyExponent]

end Cascade

/-! ## Axiom audit -/

#print axioms Cascade.intermittencyExponent
#print axioms Cascade.intermittencyExponent_lt_two_iff
#print axioms Cascade.two_lt_intermittencyExponent_iff
#print axioms Cascade.intermittency_critical_iff
#print axioms Cascade.theta_three
#print axioms Cascade.three_dim_critical_iff
#print axioms Cascade.palasek_threshold_five
#print axioms Cascade.palasek_threshold_five_boundary
