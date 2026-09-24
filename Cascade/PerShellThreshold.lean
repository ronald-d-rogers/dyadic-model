import Cascade.DissipationThreshold

/-!
# The exact per-shell dissipation threshold of the Katz–Pavlović sector

`Cascade/DissipationThreshold.lean` proves that the enstrophy barrier closes unconditionally iff
the dissipation degree satisfies `e > 1`, is marginal at `e = 1`, and cannot close for `e ≤ 1` —
but it records the marginality only vaguely, as "the two homogeneities tie".  This file replaces
that statement by an **exact, computable per-shell criterion** and makes the non-pinnability at
`e = 1` a *theorem*.

Write the velocity equation at degree `e` as

`u_k' = 2^k(u_{k−1}² − 2 u_k u_{k+1}) + κ θ_k − ν · 2^{ek} u_k`

(that is `velocityRHSDegreeE ν κ 1 0 e u θ k`).  Weighting it by `2^{2k} u_k` and summing over
`k < N`, the transfer telescopes: reindexing `j = k − 1` in the first piece contributes `8`, the
second piece contributes `2`, their difference is `6`, and the outer factor `2` turns this into
`12`.  The Dirichlet ends `u(−1) = u(N) = 0` kill both boundary terms.  The result is the exact
identity `enstrophy_pairing_degree`.

Comparing transfer and dissipation **shell by shell**, the transfer wins at shell `j` exactly when

`u_{j+1} > (ν/6) · 2^{(e−1)j}`,

i.e. exactly when the next shell clears the bar `perShellBar ν e j = (ν/6)·2^{(e−1)j}`.  That bar
is scale-invariant in `j` **exactly at `e = 1`** (`bar_scale_invariant`); it strictly increases
with `j` for `e > 1` (`bar_strictMono`) and strictly decreases for `e < 1` (`bar_strictAnti`).
This is the criticality, made exact.

## Scope: one sector of a four-parameter family

The model above is `velocityRHSDegreeE ν κ 1 0` — the **Katz–Pavlović** sector, `A = 1, B = 0` of
`boussinesqTransferU` (`Cascade/Boussinesq.lean:71`). The other named sector, `A = 0, B = 1`, is
**Obukhov**: the model of Palasek (arXiv:2407.06179, eq. (1.2)) and of Looi's global-regularity
theorem. **It has no per-shell bar.** Its budget carries `u_j` linearly rather than as `u_j²`, so no
function of `(ν, e, j)` decides the sign of a shell — `Cascade/PerShellSectorObukhov.lean` proves
both the pairing identity there and the negative (`no_obukhov_perShellBar`). See also
`CASCADE_PALASEK_PRIOR_ART.md` Q1(b).

**The bar is sector-specific; the `e = 1` criticality is not.** The factor `2^{(e−1)j}` is present
in both sectors, so its independence of `j` is governed by `e = 1` either way. What the change of
sector destroys is the *bar* — the reading of each shell's sign off `u_{j+1}` alone.

At `e = 1` the budget collapses (`budget_degree_one`) to
`2 Σ_{k<N} 2^{2k} u_k u_k' = Σ_{j<N} 2^{3j} u_j² (12 u_{j+1} − 2ν)`, whose **sign depends on the
distribution of `u`, not its size**.  Concretely, at `N = 2`, `ν = 1`, `e = 1`, `u_2 = 0`, `κ = 0`,
the states `u = (5,0)` and `v = (3,2)` both have enstrophy `25` while their budgets are `−50` and
`+134`.  Hence `same_enstrophy_opposite_sign`, and therefore `no_enstrophy_only_criterion`: no
predicate of the enstrophy alone can decide the sign of its rate at `e = 1`.

## Contents

1. `perShellBar` — this sector's exact per-shell bar `(ν/6)·2^{(e−1)j}`.
2. `enstrophy_pairing_degree` — the exact degree-`e` enstrophy-pairing identity.
3. `perShell_iff` — the exact per-shell threshold.
4. `bar_scale_invariant`, `bar_strictMono`, `bar_strictAnti` — the criticality of `e = 1`.
5. `budget2`, `budget_degree_one` — the collapsed `e = 1` budget.
6. `same_enstrophy_opposite_sign`, `no_enstrophy_only_criterion` — non-pinnability at `e = 1`.
7. Machine-checked numerical evaluations.
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators

namespace Cascade

/-! ## 1. The per-shell bar -/

/-- The per-shell growth bar `(ν/6)·2^{(e−1)j}`.  The transfer at shell `j` beats the dissipation
at shell `j` exactly when `u_{j+1}` exceeds this bar. -/
def perShellBar (ν : ℝ) (e : ℤ) (j : ℕ) : ℝ := (ν / 6) * dyadicWeight ((e - 1) * (j : ℤ))

/-! ## 2. The exact enstrophy-pairing identity -/

/-- **The exact enstrophy-pairing identity at degree `e`.**  Weighting the degree-`e` velocity
equation by `2^{2k} u_k` and summing over `k < N`, the transfer telescopes (reindexing `j = k−1`
gives `8 − 2 = 6`, doubled by the outer factor `2` to `12`) and the Dirichlet ends kill both
boundary terms:

`2 Σ_{k<N} 2^{2k} u_k u_k' = 12 Σ_{j<N−1} 2^{3j} u_j² u_{j+1}
   + 2κ Σ_{k<N} 2^{2k} u_k θ_k − 2ν Σ_{k<N} 2^{(2+e)k} u_k²`. -/
theorem enstrophy_pairing_degree (ν κ : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (N : ℕ)
    (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0) :
    2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k:ℤ)) * u (k:ℤ)
          * velocityRHSDegreeE ν κ 1 0 e u θ (k:ℤ))
      = 12 * (∑ j ∈ Finset.range (N-1), dyadicWeight (3 * (j:ℤ)) * (u (j:ℤ))^2 * u ((j:ℤ)+1))
        + 2 * κ * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k:ℤ)) * u (k:ℤ) * θ (k:ℤ))
        - 2 * ν * (∑ k ∈ Finset.range N, dyadicWeight ((2+e) * (k:ℤ)) * (u (k:ℤ))^2) := by
  -- The cubic transfer sum of `enstrophy_pairing_degreeE`, reindexed from `k` to `j = k − 1`.
  have hA : (∑ k ∈ Finset.range N, (vorticity u ((k:ℤ)-1))^2 * vorticity u (k:ℤ))
      = 2 * (∑ j ∈ Finset.range (N-1),
          dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2 * u ((j:ℤ)+1)) := by
    cases N with
    | zero => simp
    | succ M =>
      rw [Finset.sum_range_succ']
      have hf0 : (vorticity u (((0:ℕ):ℤ)-1))^2 * vorticity u ((0:ℕ):ℤ) = 0 := by
        have h0 : (((0:ℕ):ℤ)-1) = -1 := by norm_num
        rw [h0, vorticity_neg_one u huBot]
        ring
      have hstep : ∀ k : ℕ,
          (vorticity u (((k+1:ℕ):ℤ)-1))^2 * vorticity u ((k+1:ℕ):ℤ)
            = 2 * (dyadicWeight (3*(k:ℤ)) * (u (k:ℤ))^2 * u ((k:ℤ)+1)) := by
        intro k
        have hk1 : (((k+1:ℕ):ℤ)-1) = (k:ℤ) := by push_cast; ring
        have hk2 : ((k+1:ℕ):ℤ) = (k:ℤ) + 1 := by push_cast; ring
        rw [hk1, hk2]
        simp only [vorticity]
        have hd1 : dyadicWeight ((k:ℤ)+1) = dyadicWeight (k:ℤ) * 2 := by
          rw [show (k:ℤ)+1 = (k:ℤ) + 1 by rfl, dyadicWeight_add]
          norm_num [dyadicWeight]
        rw [hd1, dyadicWeight_three_mul]
        ring
      rw [hf0, add_zero, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => hstep k)
  rw [enstrophy_pairing_degreeE ν κ e u θ N huBot huTop, hA, enstrophyDissipation]
  ring

/-! ## 3. The exact per-shell threshold -/

/-- **The exact per-shell threshold.**  With `u_j ≠ 0` and `0 < ν`, the shell-`j` transfer
`12·2^{3j}u_j²u_{j+1}` strictly exceeds the shell-`j` dissipation `2ν·2^{(2+e)j}u_j²` exactly when
`u_{j+1}` clears the bar `perShellBar ν e j = (ν/6)·2^{(e−1)j}`. -/
theorem perShell_iff (ν : ℝ) (hν : 0 < ν) (e : ℤ) (u : ℤ → ℝ) (j : ℕ) (huj : u (j:ℤ) ≠ 0) :
    2 * ν * dyadicWeight ((2+e) * (j:ℤ)) * (u (j:ℤ))^2
        < 12 * dyadicWeight (3 * (j:ℤ)) * (u (j:ℤ))^2 * u ((j:ℤ)+1)
      ↔ perShellBar ν e j < u ((j:ℤ)+1) := by
  have hsplit : dyadicWeight ((2+e) * (j:ℤ))
      = dyadicWeight (3 * (j:ℤ)) * dyadicWeight ((e-1) * (j:ℤ)) := by
    rw [← dyadicWeight_add]
    congr 1
    ring
  have hbx : 0 < 2 * dyadicWeight (3 * (j:ℤ)) * (u (j:ℤ))^2 :=
    mul_pos (mul_pos (by norm_num) (dyadicWeight_pos _)) (sq_pos_of_ne_zero huj)
  have key : (2 * ν * (dyadicWeight (3*(j:ℤ)) * dyadicWeight ((e-1)*(j:ℤ))) * (u (j:ℤ))^2
        < 12 * dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2 * u ((j:ℤ)+1))
      ↔ ν * dyadicWeight ((e-1)*(j:ℤ)) < 6 * u ((j:ℤ)+1) := by
    constructor
    · intro h
      have h' : (2 * dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2)
            * (ν * dyadicWeight ((e-1)*(j:ℤ)))
          < (2 * dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2) * (6 * u ((j:ℤ)+1)) := by
        nlinarith [h]
      exact (mul_lt_mul_iff_right₀ hbx).mp h'
    · intro h
      have h' : (2 * dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2)
            * (ν * dyadicWeight ((e-1)*(j:ℤ)))
          < (2 * dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2) * (6 * u ((j:ℤ)+1)) :=
        (mul_lt_mul_iff_right₀ hbx).mpr h
      nlinarith [h']
  have key2 : ((ν/6) * dyadicWeight ((e-1)*(j:ℤ)) < u ((j:ℤ)+1))
      ↔ ν * dyadicWeight ((e-1)*(j:ℤ)) < 6 * u ((j:ℤ)+1) := by
    rw [show (ν/6) * dyadicWeight ((e-1)*(j:ℤ))
          = ν * dyadicWeight ((e-1)*(j:ℤ)) / 6 by ring,
        div_lt_iff₀ (by norm_num : (0:ℝ) < 6)]
    constructor <;> intro h <;> linarith
  rw [hsplit, perShellBar, key, key2]

/-! ## 4. The criticality of `e = 1` -/

/-- **The bar is scale-invariant exactly at `e = 1`.**  For `ν ≠ 0` and `j ≠ 0`, the bar at shell
`j` equals the bar at shell `0` iff `e = 1`; otherwise the two homogeneities genuinely differ. -/
theorem bar_scale_invariant (ν : ℝ) (hν : ν ≠ 0) (e : ℤ) (j : ℕ) (hj : j ≠ 0) :
    perShellBar ν e j = perShellBar ν e 0 ↔ e = 1 := by
  have h0 : perShellBar ν e 0 = ν / 6 := by simp [perShellBar, dyadicWeight]
  constructor
  · intro h
    have hc : dyadicWeight ((e-1) * (j:ℤ)) = 1 := by
      have hne : ν / 6 ≠ 0 := div_ne_zero hν (by norm_num)
      have h' : (ν/6) * dyadicWeight ((e-1) * (j:ℤ)) = (ν/6) * 1 := by
        rw [h0] at h
        rw [perShellBar] at h
        rw [mul_one]
        exact h
      exact mul_left_cancel₀ hne h'
    have hz : (e - 1) * (j:ℤ) = 0 := by
      have h2 : (2:ℝ) ^ ((e-1) * (j:ℤ)) = 1 := by simpa [dyadicWeight] using hc
      exact (zpow_eq_one_iff_right₀ (by norm_num : (0:ℝ) ≤ 2)
        (by norm_num : (2:ℝ) ≠ 1)).mp h2
    have hjz : (j:ℤ) ≠ 0 := by exact_mod_cast hj
    have he1 : e - 1 = 0 := by
      rcases mul_eq_zero.mp hz with h1 | h1
      · exact h1
      · exact absurd h1 hjz
    omega
  · intro he
    rw [he]
    simp [perShellBar, dyadicWeight]

/-- **For `e > 1` the bar rises with scale**: small scales face an ever-higher bar, so dissipation
wins at large `j`. -/
theorem bar_strictMono (ν : ℝ) (hν : 0 < ν) {e : ℤ} (he : 1 < e) {j j' : ℕ} (h : j < j') :
    perShellBar ν e j < perShellBar ν e j' := by
  have hν6 : 0 < ν / 6 := by positivity
  have he1 : 0 < e - 1 := by omega
  have hj : (j:ℤ) < (j':ℤ) := by exact_mod_cast h
  have hlt : (e-1) * (j:ℤ) < (e-1) * (j':ℤ) := mul_lt_mul_of_pos_left hj he1
  have h2 : dyadicWeight ((e-1) * (j:ℤ)) < dyadicWeight ((e-1) * (j':ℤ)) := by
    rw [dyadicWeight, dyadicWeight]
    exact (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mpr hlt
  rw [perShellBar, perShellBar]
  exact mul_lt_mul_of_pos_left h2 hν6

/-- **For `e < 1` the bar falls with scale**: small scales grow ever more easily, so the transfer
wins and the cascade runs away. -/
theorem bar_strictAnti (ν : ℝ) (hν : 0 < ν) {e : ℤ} (he : e < 1) {j j' : ℕ} (h : j < j') :
    perShellBar ν e j' < perShellBar ν e j := by
  have hν6 : 0 < ν / 6 := by positivity
  have he1 : e - 1 < 0 := by omega
  have hj : (j:ℤ) < (j':ℤ) := by exact_mod_cast h
  have hlt : (e-1) * (j':ℤ) < (e-1) * (j:ℤ) := mul_lt_mul_of_neg_left hj he1
  have h2 : dyadicWeight ((e-1) * (j':ℤ)) < dyadicWeight ((e-1) * (j:ℤ)) := by
    rw [dyadicWeight, dyadicWeight]
    exact (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mpr hlt
  rw [perShellBar, perShellBar]
  exact mul_lt_mul_of_pos_left h2 hν6

/-! ## 5. The collapsed `e = 1` budget -/

/-- **The `N = 2` enstrophy budget at `e = 1` and zero buoyancy.** -/
def budget2 (ν : ℝ) (u : ℤ → ℝ) : ℝ :=
  2 * ∑ k ∈ Finset.range 2,
    dyadicWeight (2*(k:ℤ)) * u (k:ℤ) * velocityRHSDegreeE ν 0 1 0 1 u 0 (k:ℤ)

/-- **The `e = 1` budget collapses to a shape-dependent sum.**  At `e = 1` and `κ = 0` the exact
identity reads `2 Σ_{k<N} 2^{2k} u_k u_k' = Σ_{j<N} 2^{3j} u_j² (12 u_{j+1} − 2ν)`, a single sum
whose sign is not determined by the size of `u`. -/
theorem budget_degree_one (ν : ℝ) (u θ : ℤ → ℝ) (N : ℕ)
    (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0) :
    2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k:ℤ)) * u (k:ℤ)
          * velocityRHSDegreeE ν 0 1 0 1 u θ (k:ℤ))
      = ∑ j ∈ Finset.range N,
          dyadicWeight (3 * (j:ℤ)) * (u (j:ℤ))^2 * (12 * u ((j:ℤ)+1) - 2*ν) := by
  rw [enstrophy_pairing_degree ν 0 1 u θ N huBot huTop]
  have h23 : (2:ℤ) + 1 = 3 := by norm_num
  rw [h23]
  -- shift the transfer sum from `range (N-1)` to `range N`; the added term carries `u_N = 0`
  have hshift :
      (∑ j ∈ Finset.range (N-1), dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2 * u ((j:ℤ)+1))
        = (∑ j ∈ Finset.range N, dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2 * u ((j:ℤ)+1)) := by
    cases N with
    | zero => simp
    | succ M =>
      rw [Finset.sum_range_succ]
      have hlast :
          dyadicWeight (3*((M:ℕ):ℤ)) * (u ((M:ℕ):ℤ))^2 * u (((M:ℕ):ℤ)+1) = 0 := by
        have hM : (((M:ℕ):ℤ)+1) = ((M+1:ℕ):ℤ) := by push_cast; ring
        rw [hM, huTop]
        ring
      rw [hlast, add_zero]
      simp only [Nat.add_sub_cancel]
  rw [hshift]
  have hsum :
      (∑ j ∈ Finset.range N,
          dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2 * (12*u ((j:ℤ)+1) - 2*ν))
        = 12 * (∑ j ∈ Finset.range N,
              dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2 * u ((j:ℤ)+1))
          - 2*ν * (∑ j ∈ Finset.range N,
              dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2) := by
    have hcongr :
        (∑ j ∈ Finset.range N,
            dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2 * (12*u ((j:ℤ)+1) - 2*ν))
          = ∑ j ∈ Finset.range N,
              (12 * (dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2 * u ((j:ℤ)+1))
                - 2*ν * (dyadicWeight (3*(j:ℤ)) * (u (j:ℤ))^2)) :=
      Finset.sum_congr rfl (fun j _ => by ring)
    rw [hcongr, Finset.sum_sub_distrib]
    simp only [Finset.mul_sum]
  rw [hsum]
  ring

/-! ## 6. Non-pinnability at `e = 1` -/

/-- **Two nonnegative states with the same enstrophy and opposite rates at `e = 1`.**  With
`u = (5,0,0,…)` and `v = (3,2,0,…)` at `N = 2`, `ν = 1`, `κ = 0`, both have enstrophy `25` while
`budget2 1 u = −50 < 0` and `budget2 1 v = 134 > 0`. -/
theorem same_enstrophy_opposite_sign :
    ∃ u v : ℤ → ℝ, (∀ k, 0 ≤ u k) ∧ (∀ k, 0 ≤ v k)
      ∧ enstrophy u 2 = enstrophy v 2
      ∧ budget2 1 u < 0 ∧ 0 < budget2 1 v := by
  refine ⟨(fun k : ℤ => if k = 0 then 5 else 0),
    (fun k : ℤ => if k = 0 then 3 else if k = 1 then 2 else 0), ?_, ?_, ?_, ?_, ?_⟩
  · intro k; dsimp only; split_ifs <;> norm_num
  · intro k; dsimp only; split_ifs <;> norm_num
  · norm_num [enstrophy, dyadicWeight, Finset.sum_range_succ, Finset.sum_range_zero]
  · norm_num [budget2, velocityRHSDegreeE, boussinesqTransferU, dyadicWeight,
      Finset.sum_range_succ, Finset.sum_range_zero]
  · norm_num [budget2, velocityRHSDegreeE, boussinesqTransferU, dyadicWeight,
      Finset.sum_range_succ, Finset.sum_range_zero]

/-- **No criterion reading the enstrophy alone can decide the sign of its rate at `e = 1`.**  There
is no predicate `P` of the enstrophy value such that `P (enstrophy u 2) ↔ 0 < budget2 1 u` for
every nonnegative state `u`: `same_enstrophy_opposite_sign` exhibits two states with the same
enstrophy `25` and rates of opposite sign, so any such `P` would have to be both false and true. -/
theorem no_enstrophy_only_criterion :
    ¬ ∃ P : ℝ → Prop, ∀ u : ℤ → ℝ, (∀ k, 0 ≤ u k) → (P (enstrophy u 2) ↔ 0 < budget2 1 u) := by
  rintro ⟨P, hP⟩
  obtain ⟨u, v, hu, hv, hen, hu', hv'⟩ := same_enstrophy_opposite_sign
  have h1 : ¬ P (enstrophy u 2) := fun hp => absurd ((hP u hu).mp hp) (not_lt.mpr hu'.le)
  have h2 : ¬ P (enstrophy v 2) := by rw [hen] at h1; exact h1
  exact h2 ((hP v hv).mpr hv')

/-! ## 7. Non-vacuity -/

/-- At `e = 1` the bar is constant in `j`: `perShellBar 1 1 0 = 1/6 = perShellBar 1 1 5`. -/
example : perShellBar 1 1 0 = perShellBar 1 1 5 := by norm_num [perShellBar, dyadicWeight]

/-- `perShellBar ν e 0 = ν/6` for `ν = 1`, `e = 1`. -/
example : perShellBar 1 1 0 = 1/6 := by norm_num [perShellBar, dyadicWeight]

/-- At `e = 2` the bar doubles with each shell: `1/6, 1/3, 2/3`. -/
example : perShellBar 1 2 0 = 1/6 ∧ perShellBar 1 2 1 = 1/3 ∧ perShellBar 1 2 2 = 2/3 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [perShellBar, dyadicWeight]

/-- The bar is `(ν/6)·2^{(e−1)j}`: with `ν = 6`, `e = 2`, `j = 3` it is `2³ = 8`. -/
example : perShellBar 6 2 3 = 8 := by norm_num [perShellBar, dyadicWeight]

/-- The two witnesses of `same_enstrophy_opposite_sign` both have enstrophy `25`. -/
example : enstrophy (fun k : ℤ => if k = 0 then 5 else 0) 2 = 25
    ∧ enstrophy (fun k : ℤ => if k = 0 then 3 else if k = 1 then 2 else 0) 2 = 25 := by
  refine ⟨?_, ?_⟩ <;>
    norm_num [enstrophy, dyadicWeight, Finset.sum_range_succ, Finset.sum_range_zero]

/-- The `e = 1` budget of the first witness is `−50`. -/
example : budget2 1 (fun k : ℤ => if k = 0 then 5 else 0) = -50 := by
  norm_num [budget2, velocityRHSDegreeE, boussinesqTransferU, dyadicWeight,
    Finset.sum_range_succ, Finset.sum_range_zero]

/-- The `e = 1` budget of the second witness is `+134`. -/
example : budget2 1 (fun k : ℤ => if k = 0 then 3 else if k = 1 then 2 else 0) = 134 := by
  norm_num [budget2, velocityRHSDegreeE, boussinesqTransferU, dyadicWeight,
    Finset.sum_range_succ, Finset.sum_range_zero]

/-- The `e = 1` collapsed budget at `N = 2` and the first witness: `25·(12·0 − 2) = −50`. -/
example : (∑ j ∈ Finset.range 2, dyadicWeight (3*(j:ℤ))
      * ((fun k : ℤ => if k = 0 then 5 else 0) (j:ℤ))^2
      * (12 * ((fun k : ℤ => if k = 0 then 5 else 0) ((j:ℤ)+1)) - 2*1)) = -50 := by
  norm_num [dyadicWeight, Finset.sum_range_succ, Finset.sum_range_zero]

/-- The `e = 1` collapsed budget at `N = 2` and the second witness: shell `0` gives
`3²·(12·2 − 2) = 198` and shell `1` gives `8·2²·(12·0 − 2) = −64`, total `134`, matching the
direct budget. -/
example : (∑ j ∈ Finset.range 2, dyadicWeight (3*(j:ℤ))
      * ((fun k : ℤ => if k = 0 then 3 else if k = 1 then 2 else 0) (j:ℤ))^2
      * (12 * ((fun k : ℤ => if k = 0 then 3 else if k = 1 then 2 else 0) ((j:ℤ)+1)) - 2*1)) = 134 := by
  norm_num [dyadicWeight, Finset.sum_range_succ, Finset.sum_range_zero]

end Cascade

/-! ## Axiom audit -/

#print axioms Cascade.perShellBar
#print axioms Cascade.enstrophy_pairing_degree
#print axioms Cascade.perShell_iff
#print axioms Cascade.bar_scale_invariant
#print axioms Cascade.bar_strictMono
#print axioms Cascade.bar_strictAnti
#print axioms Cascade.budget2
#print axioms Cascade.budget_degree_one
#print axioms Cascade.same_enstrophy_opposite_sign
#print axioms Cascade.no_enstrophy_only_criterion
