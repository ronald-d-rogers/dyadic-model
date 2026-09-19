/-
# The Kahane / KP arithmetic is blind to the time-scale exponent

Kahane's non-degeneracy criterion for a Mandelbrot cascade is `E [W log W] < log ℓ`, where `ℓ` is the
branching number and `W = ℓ * p_I` with `I` uniform on the branches and `p` a probability vector on
them (Heurteaux, *An introduction to Mandelbrot cascades*, arXiv:1408.6944, Theorem 3.2).  This file
proves the elementary arithmetic behind the fact that the criterion cannot see the *time-scale*
exponent `α` of a dyadic tree cascade.

## What is proved

* `sum_mul_log_le_log`: for a probability vector `p` on `Fin l` with `l ≥ 1`,
  `∑ i, p i * Real.log (l * p i) ≤ Real.log l`.  This is `E [W log W] ≤ log ℓ`.
* `sum_mul_log_eq_log_iff`: equality holds **iff** the mass is concentrated on a single branch,
  i.e. `∃ i, p i = 1 ∧ ∀ j ≠ i, p j = 0`.  So the inequality is strict for every non-degenerate
  weight vector.

## What this does and does not mean

The inequality is a statement about the **weights** `p i`.  It contains no time variable and no
exponent: `l` and `p` are the only inputs, so the criterion is satisfied **identically in `α`** and
can never reproduce the Barbato threshold `α̃ = ½ log₂ N_*` except by a coincidence of definitions.
That is the point recorded in `Cascade/ZETA.md` §2.4.

It is **not** a claim that the criterion is vacuous in general — it is a genuine non-degeneracy
criterion for random multiplicative cascades.  It is a claim that it is blind to the specific
exponent at issue here.

The equality case is stated for `Fin l` with `0 < l`, because `Fin 0` is empty and the hypothesis
`∑ i, p i = 1` is then unsatisfiable; the hypothesis makes the statement non-vacuous rather than
merely convenient.

Numerically (ℓ = p = 2, p₀ = 0.3): `H(p) = 0.610864` nats `= 0.881291` bits, and
`E [W log₂ W] = 1 - H / log 2 = 0.118709 < 1`.  Note that `0.881291` is the **intermittency
dimension** `D = 1 - E [W log₂ W]`, not `H`; an earlier draft conflated the two.  Checked in
`Cascade/zeta_checks.py` section F.
-/

import Mathlib

open scoped BigOperators

namespace PAdicZeta

/-- **`E [W log W] ≤ log ℓ`.**  For a probability vector `p` on `Fin l`, the sum
`∑ i, p i * Real.log (l * p i)` is at most `Real.log l`.

Proof: each `p i` lies in `[0, 1]`, so `0 ≤ l * p i ≤ l` and `Real.log` is monotone; multiplying by
`p i ≥ 0` and summing gives the bound.  The case `p i = 0` is handled separately because
`Real.log 0 = 0` in mathlib rather than `-∞`. -/
theorem sum_mul_log_le_log (l : ℕ) (p : Fin l → ℝ)
    (hnonneg : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∑ i, p i * Real.log (l * p i) ≤ Real.log l := by
  rcases Nat.eq_zero_or_pos l with h0 | hl0
  · subst h0
    simp at hsum
  have hl : (0 : ℝ) < l := by exact_mod_cast hl0
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl0
  have hlogl : 0 ≤ Real.log l := Real.log_nonneg hl1
  have hterm : ∀ i, p i * Real.log (l * p i) ≤ p i * Real.log l := by
    intro i
    rcases eq_or_lt_of_le (hnonneg i) with h | h
    · rw [← h]; simp
    · have h1 : 0 < (l : ℝ) * p i := mul_pos hl h
      have h2 : (l : ℝ) * p i ≤ l := by
        have hle1 : p i ≤ 1 := by
          have := Finset.single_le_sum (f := p) (fun j _ => hnonneg j) (Finset.mem_univ i)
          linarith
        nlinarith
      exact mul_le_mul_of_nonneg_left (Real.log_le_log h1 h2) (le_of_lt h)
  calc ∑ i, p i * Real.log (l * p i)
      ≤ ∑ i, p i * Real.log l := Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, p i) * Real.log l := by rw [Finset.sum_mul]
    _ = Real.log l := by rw [hsum, one_mul]

/-- **Equality holds exactly for a point mass.**  For `0 < l` and a probability vector `p` on
`Fin l`, `∑ i, p i * Real.log (l * p i) = Real.log l` if and only if all the mass sits on one
branch.  In particular the inequality `sum_mul_log_le_log` is strict for every non-degenerate
weight vector. -/
theorem sum_mul_log_eq_log_iff (l : ℕ) (hl0 : 0 < l) (p : Fin l → ℝ)
    (hnonneg : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∑ i, p i * Real.log (l * p i) = Real.log l) ↔ ∃ i, p i = 1 ∧ ∀ j ≠ i, p j = 0 := by
  have hl : (0 : ℝ) < l := by exact_mod_cast hl0
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl0
  have hterm : ∀ i, p i * Real.log (l * p i) ≤ p i * Real.log l := by
    intro i
    rcases eq_or_lt_of_le (hnonneg i) with h | h
    · rw [← h]; simp
    · have h1 : 0 < (l : ℝ) * p i := mul_pos hl h
      have h2 : (l : ℝ) * p i ≤ l := by
        have hle1 : p i ≤ 1 := by
          have := Finset.single_le_sum (f := p) (fun j _ => hnonneg j) (Finset.mem_univ i)
          linarith
        nlinarith
      exact mul_le_mul_of_nonneg_left (Real.log_le_log h1 h2) (le_of_lt h)
  constructor
  · intro heq
    -- the deficits `p i * (log l - log (l * p i))` are nonnegative and sum to zero
    have hdnonneg : ∀ i, 0 ≤ p i * (Real.log l - Real.log (l * p i)) := by
      intro i
      have := hterm i
      nlinarith [hnonneg i]
    have hdsum : ∑ i, p i * (Real.log l - Real.log (l * p i)) = 0 := by
      have hexp : ∀ i, p i * (Real.log l - Real.log (l * p i))
          = p i * Real.log l - p i * Real.log (l * p i) := fun i => by ring
      rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum,
        one_mul, heq, sub_self]
    have hdzero : ∀ i, p i * (Real.log l - Real.log (l * p i)) = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hdnonneg i)).mp hdsum i (Finset.mem_univ i)
    -- some branch carries nonzero mass, since the total is one
    obtain ⟨i₀, hi₀⟩ : ∃ i, p i ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      have hz : ∑ i, p i = 0 := Finset.sum_eq_zero fun i _ => hcon i
      rw [hsum] at hz
      exact one_ne_zero hz
    have hpos : 0 < p i₀ := lt_of_le_of_ne (hnonneg i₀) (Ne.symm hi₀)
    have hbracket : Real.log l - Real.log (l * p i₀) = 0 := by
      rcases mul_eq_zero.mp (hdzero i₀) with h | h
      · exact absurd h hi₀
      · exact h
    have hlogeq : Real.log (l * p i₀) = Real.log l := by linarith
    have h1 : (l : ℝ) * p i₀ = l := Real.log_injOn_pos (mul_pos hl hpos) hl hlogeq
    have hpi : p i₀ = 1 := by
      refine mul_left_cancel₀ (ne_of_gt hl) ?_
      rw [h1, mul_one]
    refine ⟨i₀, hpi, ?_⟩
    intro j hj
    have herase : ∑ k ∈ Finset.univ.erase i₀, p k = 0 := by
      have hs := Finset.sum_erase_add (Finset.univ : Finset (Fin l)) p (Finset.mem_univ i₀)
      rw [hsum, hpi] at hs
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => hnonneg k)).mp herase j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
  · rintro ⟨i, hi1, hiz⟩
    rw [Finset.sum_eq_single i]
    · simp [hi1]
    · intro j _ hj
      rw [hiz j hj]
      simp
    · intro hi
      exact absurd (Finset.mem_univ i) hi

end PAdicZeta

#print axioms PAdicZeta.sum_mul_log_le_log
#print axioms PAdicZeta.sum_mul_log_eq_log_iff
