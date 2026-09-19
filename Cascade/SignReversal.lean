import Cascade.PerShellThreshold

/-!
# Interior sign reversals cannot increase the `e = 1` enstrophy budget

`Cascade/PerShellThreshold.lean` collapses the degree-`1`, zero-buoyancy enstrophy budget to the
shape-dependent sum (`budget_degree_one`)

`2 Σ_{k<N} 2^{2k} u_k u_k' = Σ_{j<N} 2^{3j} u_j² (12 u_{j+1} − 2ν)`.

This file asks **where in the shell index a sign reversal can act**.  The collapsed sum reads each
shell through a square and the next shell through a linear factor, so the answer is structural:

* the shell-`j` term is *even* in `u_j` (`budgetTerm_flip_self`);
* the shell-`j` term is *affine* in `u_{j+1}` with the nonnegative coefficient
  `12 · 2^{3j} · u_j²` (`budgetTerm_eq_affine_next`, `budgetTerm_next_coeff_nonneg`), while the
  shell-`(j+1)` term sees `u_{j+1}` only squared (`budgetTerm_flip_next`);
* consequently the **all-positive profile maximises the budget**:
  `budgetSum ν u N ≤ budgetSum ν (fun k => |u k|) N` for every `ν`, `u`, `N`
  (`budgetSum_le_abs`), with equality exactly on the profiles that have no relevant sign reversal
  (`budgetSum_eq_abs_iff`, `budgetSum_lt_abs_iff`);
* flipping a single shell `j ≥ 1` changes the total by exactly
  `−24 · 2^{3(j−1)} · u_{j−1}² · u_j` (`budgetSum_flip_sub`), so a flip of a positive amplitude
  whose predecessor is nonzero **strictly decreases** the budget (`budgetSum_flip_lt`).

So, at the critical degree, an interior sign reversal is never a blowup trigger: it can only remove
enstrophy growth.  This is a statement about the *sign dependence of one budget identity* only.  It
says nothing about Navier–Stokes, and it does not settle blowup — consistent with this repository's
record of a negative result (`README.md`, `Cascade/OUTCOME.md`).  The scope is `e = 1` (the critical
degree); no general-`e` analogue is claimed here, since the general budget carries more terms.
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators

namespace Cascade

/-! ## 1. The per-shell budget term and its sum -/

/-- **The `e = 1` per-shell budget term.**  This is exactly the summand of the right-hand side of
`budget_degree_one`: shell `j` contributes `2^{3j} u_j² (12 u_{j+1} − 2ν)`, i.e. it sees its own
amplitude `u_j` through a square and the next amplitude `u_{j+1}` linearly. -/
def budgetTerm (ν : ℝ) (u : ℤ → ℝ) (j : ℕ) : ℝ :=
  dyadicWeight (3 * (j : ℤ)) * (u (j : ℤ)) ^ 2 * (12 * u ((j : ℤ) + 1) - 2 * ν)

/-- **The collapsed `e = 1` budget** `Σ_{j<N} 2^{3j} u_j² (12 u_{j+1} − 2ν)`.
`budget_degree_one` identifies `2 Σ_{k<N} 2^{2k} u_k u_k'` with this sum. -/
def budgetSum (ν : ℝ) (u : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, budgetTerm ν u j

/-- **Bridge to `budget_degree_one`.**  Under the Dirichlet ends the actual enstrophy rate *is* the
abstract per-shell sum. -/
theorem budget_degree_one_eq_budgetSum (ν : ℝ) (u θ : ℤ → ℝ) (N : ℕ)
    (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0) :
    2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)
          * velocityRHSDegreeE ν 0 1 0 1 u θ (k : ℤ))
      = budgetSum ν u N := by
  simpa only [budgetSum, budgetTerm] using budget_degree_one ν u θ N huBot huTop

/-! ## 2. Evenness in the shell's own amplitude -/

/-- **The shell-`j` term is even in `u_j`.**  Reversing the sign of the amplitude at shell `j`
leaves the shell-`j` budget term unchanged, because `u_j` enters only as `u_j²`. -/
theorem budgetTerm_flip_self (ν : ℝ) (u : ℤ → ℝ) (j : ℕ) :
    budgetTerm ν (fun k => if k = (j : ℤ) then - u (j : ℤ) else u k) j
      = budgetTerm ν u j := by
  dsimp only [budgetTerm]
  rw [ite_eq_left rfl, neg_sq, ite_eq_right (by omega : (j : ℤ) + 1 ≠ (j : ℤ))]

/-! ## 3. Affineness in the next amplitude, with nonnegative coefficient -/

/-- **The shell-`j` term is affine in the next amplitude.**  Varying `u_{j+1} = v` moves the
shell-`j` term linearly, with coefficient `12 · 2^{3j} · u_j²`. -/
theorem budgetTerm_eq_affine_next (ν : ℝ) (u : ℤ → ℝ) (j : ℕ) (v : ℝ) :
    budgetTerm ν (fun k => if k = (j : ℤ) + 1 then v else u k) j
      = dyadicWeight (3 * (j : ℤ)) * (u (j : ℤ)) ^ 2 * (12 * v - 2 * ν) := by
  dsimp only [budgetTerm]
  rw [ite_eq_right (by omega : (j : ℤ) ≠ (j : ℤ) + 1), ite_eq_left rfl]

/-- **The coefficient of the next amplitude is nonnegative.**  It is
`12 · 2^{3j} · u_j² ≥ 0`, so the affine dependence is monotone. -/
theorem budgetTerm_next_coeff_nonneg (u : ℤ → ℝ) (j : ℕ) :
    0 ≤ 12 * dyadicWeight (3 * (j : ℤ)) * (u (j : ℤ)) ^ 2 :=
  mul_nonneg (mul_nonneg (by norm_num) (dyadicWeight_nonneg _)) (sq_nonneg _)

/-- **Monotonicity in the next amplitude.**  Because the coefficient is nonnegative, raising
`u_{j+1}` can only raise the shell-`j` term. -/
theorem budgetTerm_mono_next (ν : ℝ) (u : ℤ → ℝ) (j : ℕ) {a b : ℝ} (hab : a ≤ b) :
    budgetTerm ν (fun k => if k = (j : ℤ) + 1 then a else u k) j
      ≤ budgetTerm ν (fun k => if k = (j : ℤ) + 1 then b else u k) j := by
  rw [budgetTerm_eq_affine_next, budgetTerm_eq_affine_next]
  exact mul_le_mul_of_nonneg_left (by linarith)
    (mul_nonneg (dyadicWeight_nonneg _) (sq_nonneg _))

/-- **The shell-`(j+1)` term is even in `u_{j+1}`.**  Reversing the sign of `u_{j+1}` leaves the
next shell's own term unchanged, since it too sees `u_{j+1}` only through `(u_{j+1})²`. -/
theorem budgetTerm_flip_next (ν : ℝ) (u : ℤ → ℝ) (j : ℕ) :
    budgetTerm ν (fun k => if k = (j : ℤ) + 1 then - u ((j : ℤ) + 1) else u k) (j + 1)
      = budgetTerm ν u (j + 1) := by
  have hcast : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
  dsimp only [budgetTerm]
  rw [hcast, ite_eq_left rfl, neg_sq, ite_eq_right (by omega : (j : ℤ) + 1 + 1 ≠ (j : ℤ) + 1)]

/-! ## 4. The absolute-value profile dominates -/

/-- **Per-shell domination.**  Replacing `u` by `|u|` can only raise the shell-`j` term: the factor
`u_j²` is unchanged, and `|u_{j+1}| ≥ u_{j+1}` meets the nonnegative coefficient
`12 · 2^{3j} · u_j²`. -/
theorem budgetTerm_le_abs (ν : ℝ) (u : ℤ → ℝ) (j : ℕ) :
    budgetTerm ν u j ≤ budgetTerm ν (fun k => |u k|) j := by
  dsimp only [budgetTerm]
  rw [sq_abs]
  have hw : 0 ≤ dyadicWeight (3 * (j : ℤ)) * (u (j : ℤ)) ^ 2 :=
    mul_nonneg (dyadicWeight_nonneg _) (sq_nonneg _)
  have hle : 12 * u ((j : ℤ) + 1) - 2 * ν ≤ 12 * |u ((j : ℤ) + 1)| - 2 * ν := by
    have := le_abs_self (u ((j : ℤ) + 1))
    linarith
  exact mul_le_mul_of_nonneg_left hle hw

/-- **THE MAIN THEOREM — the absolute-value profile dominates the budget.**  For every viscosity
`ν`, every profile `u` and every truncation `N`, the all-positive profile `|u|` has a budget at
least as large as `u`'s.  Since every sign pattern of a given profile has absolute value `|u|`, no
sign pattern can beat the all-positive one: interior sign reversals can only suppress the `e = 1`
enstrophy budget. -/
theorem budgetSum_le_abs (ν : ℝ) (u : ℤ → ℝ) (N : ℕ) :
    budgetSum ν u N ≤ budgetSum ν (fun k => |u k|) N := by
  dsimp only [budgetSum]
  exact Finset.sum_le_sum (fun j _ => budgetTerm_le_abs ν u j)

/-- **The pointwise defect** of replacing `u` by `|u|` at shell `j`. -/
def budgetDefect (u : ℤ → ℝ) (j : ℕ) : ℝ :=
  dyadicWeight (3 * (j : ℤ)) * (u (j : ℤ)) ^ 2
    * (12 * (|u ((j : ℤ) + 1)| - u ((j : ℤ) + 1)))

/-- The defect is nonnegative. -/
theorem budgetDefect_nonneg (u : ℤ → ℝ) (j : ℕ) : 0 ≤ budgetDefect u j := by
  dsimp only [budgetDefect]
  have h1 : 0 ≤ dyadicWeight (3 * (j : ℤ)) * (u (j : ℤ)) ^ 2 :=
    mul_nonneg (dyadicWeight_nonneg _) (sq_nonneg _)
  have h2 : 0 ≤ 12 * (|u ((j : ℤ) + 1)| - u ((j : ℤ) + 1)) := by
    have := le_abs_self (u ((j : ℤ) + 1))
    linarith
  exact mul_nonneg h1 h2

/-- The defect is strictly positive exactly when shell `j` has a nonzero amplitude *and* the next
amplitude is negative: that is precisely the configuration in which a reversal costs budget. -/
theorem budgetDefect_pos (u : ℤ → ℝ) (j : ℕ) :
    0 < budgetDefect u j ↔ u (j : ℤ) ≠ 0 ∧ u ((j : ℤ) + 1) < 0 := by
  dsimp only [budgetDefect]
  constructor
  · intro h
    have hc : 0 ≤ 12 * (|u ((j : ℤ) + 1)| - u ((j : ℤ) + 1)) := by
      have := le_abs_self (u ((j : ℤ) + 1))
      linarith
    have hw : 0 < dyadicWeight (3 * (j : ℤ)) * (u (j : ℤ)) ^ 2 :=
      pos_of_mul_pos_left h hc
    have hsq : 0 < (u (j : ℤ)) ^ 2 :=
      pos_of_mul_pos_right hw (dyadicWeight_nonneg _)
    have huj : u (j : ℤ) ≠ 0 := by
      intro h0
      rw [h0] at hsq
      norm_num at hsq
    have hcpos : 0 < 12 * (|u ((j : ℤ) + 1)| - u ((j : ℤ) + 1)) :=
      pos_of_mul_pos_right h (mul_nonneg (dyadicWeight_nonneg _) (sq_nonneg _))
    have hd : 0 < |u ((j : ℤ) + 1)| - u ((j : ℤ) + 1) := by linarith
    have hneg : u ((j : ℤ) + 1) < 0 := by
      by_contra hcon
      push Not at hcon
      have habs : |u ((j : ℤ) + 1)| = u ((j : ℤ) + 1) := abs_of_nonneg hcon
      linarith
    exact ⟨huj, hneg⟩
  · rintro ⟨huj, hneg⟩
    have hw : 0 < dyadicWeight (3 * (j : ℤ)) * (u (j : ℤ)) ^ 2 :=
      mul_pos (dyadicWeight_pos _) (sq_pos_of_ne_zero huj)
    have habs : |u ((j : ℤ) + 1)| = -u ((j : ℤ) + 1) := abs_of_neg hneg
    have hc : 0 < 12 * (|u ((j : ℤ) + 1)| - u ((j : ℤ) + 1)) := by
      rw [habs]; linarith
    exact mul_pos hw hc

/-- **Exact defect identity.**  The gain of the absolute-value profile over `u` is the sum of the
per-shell defects. -/
theorem budgetSum_abs_sub (ν : ℝ) (u : ℤ → ℝ) (N : ℕ) :
    budgetSum ν (fun k => |u k|) N - budgetSum ν u N
      = ∑ j ∈ Finset.range N, budgetDefect u j := by
  dsimp only [budgetSum, budgetDefect]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [budgetTerm]
  rw [sq_abs]
  ring

/-- **Strictness criterion.**  The absolute-value profile strictly increases the budget exactly when
some shell `j < N` has a nonzero amplitude whose successor amplitude is negative. -/
theorem budgetSum_lt_abs_iff (ν : ℝ) (u : ℤ → ℝ) (N : ℕ) :
    budgetSum ν u N < budgetSum ν (fun k => |u k|) N
      ↔ ∃ j ∈ Finset.range N, u (j : ℤ) ≠ 0 ∧ u ((j : ℤ) + 1) < 0 := by
  have hsum_pos : 0 < ∑ j ∈ Finset.range N, budgetDefect u j
      ↔ ∃ j ∈ Finset.range N, 0 < budgetDefect u j := by
    constructor
    · intro h
      by_contra hc
      push Not at hc
      have hzero : ∑ j ∈ Finset.range N, budgetDefect u j = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => budgetDefect_nonneg u j)).mpr
          (fun j hj => le_antisymm (hc j hj) (budgetDefect_nonneg u j))
      linarith
    · rintro ⟨j, hj, hjpos⟩
      exact Finset.sum_pos' (fun i _ => budgetDefect_nonneg u i) ⟨j, hj, hjpos⟩
  rw [← sub_pos, budgetSum_abs_sub, hsum_pos]
  constructor
  · rintro ⟨j, hj, hp⟩
    exact ⟨j, hj, (budgetDefect_pos u j).mp hp⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, (budgetDefect_pos u j).mpr h⟩

/-- **Equality criterion (the honest "unless").**  The absolute-value profile leaves the budget
unchanged exactly when every relevant successor amplitude is nonnegative, or the corresponding
weight `2^{3j} u_j²` vanishes. -/
theorem budgetSum_eq_abs_iff (ν : ℝ) (u : ℤ → ℝ) (N : ℕ) :
    budgetSum ν u N = budgetSum ν (fun k => |u k|) N
      ↔ ∀ j ∈ Finset.range N, u (j : ℤ) = 0 ∨ 0 ≤ u ((j : ℤ) + 1) := by
  have hle := budgetSum_le_abs ν u N
  constructor
  · intro heq j hj
    have hnot : ¬ (budgetSum ν u N < budgetSum ν (fun k => |u k|) N) := by
      rw [heq]
      exact lt_irrefl _
    rw [budgetSum_lt_abs_iff] at hnot
    push Not at hnot
    by_cases huj : u (j : ℤ) = 0
    · exact Or.inl huj
    · exact Or.inr (hnot j hj huj)
  · intro h
    have hnot : ¬ (budgetSum ν u N < budgetSum ν (fun k => |u k|) N) := by
      rw [budgetSum_lt_abs_iff]
      rintro ⟨j, hj, huj, hneg⟩
      rcases h j hj with h0 | hpos
      · exact huj h0
      · linarith
    exact le_antisymm hle (not_lt.mp hnot)

/-- **No sign pattern beats the absolute-value profile.**  Multiplying a profile by any sign pattern
`σ` with `|σ k| = 1` cannot raise the `e = 1` budget above that of `|u|`. -/
theorem budgetSum_signPattern_le (ν : ℝ) (u : ℤ → ℝ) (N : ℕ) (σ : ℤ → ℝ)
    (hσ : ∀ k, |σ k| = 1) :
    budgetSum ν (fun k => σ k * u k) N ≤ budgetSum ν (fun k => |u k|) N := by
  calc budgetSum ν (fun k => σ k * u k) N
      ≤ budgetSum ν (fun k => |σ k * u k|) N := budgetSum_le_abs ν (fun k => σ k * u k) N
    _ = budgetSum ν (fun k => |u k|) N := by
        apply congrArg (fun w : ℤ → ℝ => budgetSum ν w N)
        funext k
        rw [abs_mul, hσ k, one_mul]

/-! ## 5. The single-flip corollary -/

/-- **A single interior flip.**  For `1 ≤ j ≤ N`, reversing the sign of the amplitude at shell `j`
changes the budget by exactly `−24 · 2^{3(j−1)} · u_{j−1}² · u_j`.

Two facts combine: the shell-`j` term is even in `u_j` (`budgetTerm_flip_self`), so only the
*previous* shell's term `2^{3(j−1)} u_{j−1}² (12 u_j − 2ν)` reacts, and there it is `u_j` that
enters linearly.  (For `j = 0` there is no previous shell and the flip changes nothing at all —
see `budgetSum_flip_zero`.) -/
theorem budgetSum_flip_sub (ν : ℝ) (u : ℤ → ℝ) (N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N) :
    budgetSum ν (fun k => if k = (j : ℤ) then - u (j : ℤ) else u k) N - budgetSum ν u N
      = - 24 * dyadicWeight (3 * ((j - 1 : ℕ) : ℤ)) * (u ((j - 1 : ℕ) : ℤ)) ^ 2
          * u (j : ℤ) := by
  have hdiff :
      budgetSum ν (fun k => if k = (j : ℤ) then - u (j : ℤ) else u k) N - budgetSum ν u N
        = ∑ i ∈ Finset.range N,
            (budgetTerm ν (fun k => if k = (j : ℤ) then - u (j : ℤ) else u k) i
              - budgetTerm ν u i) := by
    dsimp only [budgetSum]
    rw [← Finset.sum_sub_distrib]
  rw [hdiff, Finset.sum_eq_single (j - 1)]
  · dsimp only [budgetTerm]
    have hprev : ((j - 1 : ℕ) : ℤ) ≠ (j : ℤ) := by
      intro h
      have : j - 1 = j := by omega
      omega
    have hnext : ((j - 1 : ℕ) : ℤ) + 1 = (j : ℤ) := by omega
    rw [ite_eq_right hprev, hnext, ite_eq_left rfl]
    ring
  · intro i _ hne
    have hterm :
        budgetTerm ν (fun k => if k = (j : ℤ) then - u (j : ℤ) else u k) i
          = budgetTerm ν u i := by
      by_cases hij : i = j
      · have hji : (i : ℤ) = (j : ℤ) := by omega
        dsimp only [budgetTerm]
        rw [hji, ite_eq_left rfl, neg_sq, ite_eq_right (by omega : (j : ℤ) + 1 ≠ (j : ℤ))]
      · have h1 : (i : ℤ) ≠ (j : ℤ) := fun h => hij (by omega)
        have h2 : (i : ℤ) + 1 ≠ (j : ℤ) := by
          intro h
          have : i = j - 1 := by omega
          exact hne this
        dsimp only [budgetTerm]
        rw [ite_eq_right h1, ite_eq_right h2]
    rw [hterm, sub_self]
  · intro hmem
    exact absurd (Finset.mem_range.mpr (by omega : j - 1 < N)) hmem

/-- **A single interior flip of a positive amplitude strictly suppresses the budget.**  If
`u_j > 0` and `u_{j−1} ≠ 0`, reversing the sign of shell `j` strictly decreases the total: the exact
change `−24 · 2^{3(j−1)} · u_{j−1}² · u_j` is strictly negative. -/
theorem budgetSum_flip_lt (ν : ℝ) (u : ℤ → ℝ) (N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N)
    (huj : 0 < u (j : ℤ)) (hprev : u ((j - 1 : ℕ) : ℤ) ≠ 0) :
    budgetSum ν (fun k => if k = (j : ℤ) then - u (j : ℤ) else u k) N < budgetSum ν u N := by
  have h := budgetSum_flip_sub ν u N j hj hjN
  have hw : 0 < dyadicWeight (3 * ((j - 1 : ℕ) : ℤ)) * (u ((j - 1 : ℕ) : ℤ)) ^ 2 :=
    mul_pos (dyadicWeight_pos _) (sq_pos_of_ne_zero hprev)
  have hX : 0 < dyadicWeight (3 * ((j - 1 : ℕ) : ℤ)) * (u ((j - 1 : ℕ) : ℤ)) ^ 2 * u (j : ℤ) :=
    mul_pos hw huj
  linarith

/-- **Flipping the top shell does nothing.**  The budget never reads `u_0` linearly — shell `0`'s
term sees it only through `u_0²` — so reversing the sign at shell `0` leaves the total unchanged.
This is why the single-flip formula carries the hypothesis `1 ≤ j`. -/
theorem budgetSum_flip_zero (ν : ℝ) (u : ℤ → ℝ) (N : ℕ) :
    budgetSum ν (fun k => if k = (0 : ℤ) then - u 0 else u k) N = budgetSum ν u N := by
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [budgetTerm]
  rcases i with _ | i
  · have h0 : ((0 : ℕ) : ℤ) = (0 : ℤ) := by norm_num
    rw [h0, ite_eq_left rfl, neg_sq, ite_eq_right (by omega : (0 : ℤ) + 1 ≠ (0 : ℤ))]
  · rw [ite_eq_right (by omega : (((i + 1 : ℕ)) : ℤ) ≠ (0 : ℤ)),
        ite_eq_right (by omega : ((i + 1 : ℕ) : ℤ) + 1 ≠ (0 : ℤ))]

/-! ## 6. Back to the model: the enstrophy rate -/

/-- **The actual `e = 1` enstrophy rate is maximised by the absolute-value profile.**  Specialising
`budget_degree_one` on both sides turns `budgetSum_le_abs` into a statement about the model's
enstrophy rate `2 Σ_{k<N} 2^{2k} u_k u_k'` rather than about the abstract sum.  (The Dirichlet ends
are inherited by `|u|`, since `|u(−1)| = |u(N)| = 0`.) -/
theorem enstrophyRate_le_abs (ν : ℝ) (u θ : ℤ → ℝ) (N : ℕ)
    (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0) :
    2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)
          * velocityRHSDegreeE ν 0 1 0 1 u θ (k : ℤ))
      ≤ 2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * |u (k : ℤ)|
          * velocityRHSDegreeE ν 0 1 0 1 (fun k => |u k|) θ (k : ℤ)) := by
  rw [budget_degree_one ν u θ N huBot huTop,
      budget_degree_one ν (fun k => |u k|) θ N (by simp [huBot]) (by simp [huTop])]
  simpa only [budgetSum, budgetTerm] using budgetSum_le_abs ν u N

/-! ## 7. Non-vacuity -/

/-- The `N = 2` profile `u = (3, 2, 0, …)` has collapsed budget `3²·(12·2 − 2) + 8·2²·(0 − 2)
= 198 − 64 = 134`. -/
theorem budgetSum_witness_pos :
    budgetSum 1 (fun k : ℤ => if k = 0 then 3 else if k = 1 then 2 else 0) 2 = 134 := by
  norm_num [budgetSum, budgetTerm, dyadicWeight, Finset.sum_range_succ, Finset.sum_range_zero]

/-- Flipping the sign of shell `1` of that profile gives `u = (3, −2, 0, …)` with budget
`3²·(−24 − 2) + 8·2²·(0 − 2) = −234 − 64 = −298`, a decrease of exactly `432 = 24·2^{3·0}·3²·2`. -/
theorem budgetSum_witness_flip :
    budgetSum 1 (fun k : ℤ => if k = (1 : ℤ) then -2 else if k = 0 then 3 else 0) 2 = -298 := by
  norm_num [budgetSum, budgetTerm, dyadicWeight, Finset.sum_range_succ, Finset.sum_range_zero]

/-- The flip formula of `budgetSum_flip_sub` evaluated on that witness: the general theorem gives
the change `−24 · 2^{3·0} · 3² · 2 = −432`, matching `budgetSum_witness_flip −
budgetSum_witness_pos` (`−298 − 134`). -/
theorem budgetSum_witness_flip_change :
    budgetSum 1 (fun k : ℤ => if k = ((1 : ℕ) : ℤ) then
        - (if ((1 : ℕ) : ℤ) = 0 then 3 else if ((1 : ℕ) : ℤ) = 1 then 2 else 0) else
        if k = 0 then 3 else if k = 1 then 2 else 0) 2
      - budgetSum 1 (fun k : ℤ => if k = 0 then 3 else if k = 1 then 2 else 0) 2 = -432 := by
  rw [budgetSum_flip_sub 1 (fun k : ℤ => if k = 0 then 3 else if k = 1 then 2 else 0) 2 1
    (by norm_num) (by norm_num)]
  norm_num [dyadicWeight]

/-- The strict domination is witnessed concretely: the reversed profile `(3, −2, 0, …)` has a
strictly smaller budget than its absolute-value profile `(3, 2, 0, …)`. -/
theorem budgetSum_witness_flip_lt :
    budgetSum 1 (fun k : ℤ => if k = 0 then 3 else if k = 1 then -2 else 0) 2
      < budgetSum 1 (fun k : ℤ => |if k = 0 then 3 else if k = 1 then -2 else 0|) 2 := by
  rw [budgetSum_lt_abs_iff]
  exact ⟨0, by norm_num, by norm_num, by norm_num⟩

/-- An all-nonnegative profile is a fixed point of the domination: `|u| = u`, so the budget is
unchanged.  (This is the degenerate case of `budgetSum_eq_abs_iff`.) -/
theorem budgetSum_eq_of_nonneg (ν : ℝ) (u : ℤ → ℝ) (N : ℕ) (hu : ∀ k, 0 ≤ u k) :
    budgetSum ν u N = budgetSum ν (fun k => |u k|) N := by
  apply congrArg (fun w : ℤ → ℝ => budgetSum ν w N)
  funext k
  exact (abs_of_nonneg (hu k)).symm

end Cascade

/-! ## Axiom audit -/

#print axioms Cascade.budgetTerm
#print axioms Cascade.budgetSum
#print axioms Cascade.budget_degree_one_eq_budgetSum
#print axioms Cascade.budgetTerm_flip_self
#print axioms Cascade.budgetTerm_eq_affine_next
#print axioms Cascade.budgetTerm_next_coeff_nonneg
#print axioms Cascade.budgetTerm_mono_next
#print axioms Cascade.budgetTerm_flip_next
#print axioms Cascade.budgetTerm_le_abs
#print axioms Cascade.budgetSum_le_abs
#print axioms Cascade.budgetDefect
#print axioms Cascade.budgetDefect_nonneg
#print axioms Cascade.budgetDefect_pos
#print axioms Cascade.budgetSum_abs_sub
#print axioms Cascade.budgetSum_lt_abs_iff
#print axioms Cascade.budgetSum_eq_abs_iff
#print axioms Cascade.budgetSum_signPattern_le
#print axioms Cascade.budgetSum_flip_sub
#print axioms Cascade.budgetSum_flip_lt
#print axioms Cascade.budgetSum_flip_zero
#print axioms Cascade.enstrophyRate_le_abs
#print axioms Cascade.budgetSum_witness_pos
#print axioms Cascade.budgetSum_witness_flip
#print axioms Cascade.budgetSum_witness_flip_change
#print axioms Cascade.budgetSum_witness_flip_lt
#print axioms Cascade.budgetSum_eq_of_nonneg
