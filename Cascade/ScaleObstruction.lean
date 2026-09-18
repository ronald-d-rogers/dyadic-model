import Cascade.Enstrophy
import Cascade.BernsteinTransfer
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Stage O″ — the scale-localized enstrophy obstruction (Palasek's comparison in shell variables)

## What Palasek's frequency-localized argument says in the spatial setting

Palasek's comparison for the Navier–Stokes enstrophy budget is *spatial*. At frequency scale
`N_k`, Bernstein's `L² → L∞` inequality converts the energy bound `‖u‖_{L²} ≤ √E` into the
amplitude bound

`‖u‖_{L∞} ≲ N_k^{d/2} · ‖u‖_{L²} = N_k^{d/2} √E`,

so the nonlinear transfer at that scale is at most `~ N_k^{3/2}` (with `√E` factors), while viscous
damping acts at the rate `ν N_k²`. In dimension `d ≤ 4` the exponent comparison `d/2 ≤ 2` makes the
damping win (`N_k^{d/2} ≤ N_k²`, the frequency-localized obstruction); in high dimension `d ≥ 5`
one has `2 < d/2`, the comparison fails, and **there is no obstruction at this level**. This
`d/2`-versus-`2` dichotomy is exactly the arithmetic isolated in
`Cascade/BernsteinTransfer.lean`, where the `d ≤ 4` direction is the root-namespace theorem
`bernstein_exponent_le_dissipation`; the present file supplies the missing high-dimensional
direction as `Cascade.bernstein_exponent_gt_dissipation`, side by side with a `Cascade`-namespaced
restatement of the `d ≤ 4` direction.

## Why a shell model does not need Bernstein — and is stronger for it

A shell model **already has explicit amplitudes**: the vorticity amplitude `a_k = 2^k u_k`
(`Cascade.vorticity`) is a number, not a band-limited `L∞` norm. The only ingredient the
frequency-localized argument needs is `a_k² ≤ H`, i.e.

`|a_k| ≤ √H`  (`vorticity_abs_le_sqrt_enstrophy`),

where `H = enstrophy u N = ∑_{k<N} a_k²`. This is *strictly stronger* than the spatial Bernstein
bound `N^{d/2} √E`: there is no `N^{d/2}` loss at all, and the tail cubic transfer is bounded by
`H √H = H^{3/2}` **uniformly in the cutoff `K`**. Consequently

* the frequency factor `N_k^{3/2}` of the spatial comparison **never appears literally** in this
  file, and
* the shell obstruction is *cleaner* than the spatial one: transfer and dissipation are both
  written in the single enstrophy variable `H` and the tail mass, with no dimension and no
  `L² → L∞` conversion.

This is **not** the literal spatial-Bernstein proof; it is Palasek's comparison rewritten in shell
variables. What survives is the mechanism:

* viscous damping acts at rate `N_K²` on the tail `k ≥ K` (`dissipation_tail_ge`),
* the transfer into that tail is `H^{3/2}`, independent of `K` (`tail_transfer_cubic_le`),
* above the explicit threshold `hthr` the damping dominates the transfer
  (`scale_dissipation_dominates`).

## Contents

1. `one_le_dyadicWeight` — `2^m ≥ 1` for `m ≥ 0`.
2. `vorticity_abs_le_sqrt_enstrophy` — the shell replacement for Bernstein: `|a_k| ≤ √H`.
3. `dissipation_tail_ge` — `N_K² · ∑_{k∈[K,N)} 4^k u_k² ≤ ∑_{k∈[K,N)} 16^k u_k²`.
4. `tail_transfer_cubic_le` — `|∑_{k∈[K,N)} a_{k-1}² a_k| ≤ H √H`, uniformly in `K`.
5. `scale_dissipation_dominates` — the scale-localized conclusion with explicit threshold.
6. `bernstein_exponent_le_dissipation`, `bernstein_exponent_gt_dissipation` — the `d/2`-vs-`2`
   dichotomy (`d ≤ 4` versus `d ≥ 5`).
7. Non-vacuity: the numbers at `u = (0,1,3,0)`, `N = 2`, `K = 1`.

## Relation to `Cascade/EnstrophyBound.lean`

`Cascade.truncated_unforced_enstrophy_bounded` concludes the **global** statement "no finite-time
`H¹` blowup" by integrating the pointwise enstrophy budget: the cubic transfer `6 H^{3/2}` and the
buoyancy source are absorbed by Young's inequality into the quadratic dissipation `2ν H²/E_max`,
with `E_max` an energy ceiling, and Grönwall yields a bound linear in `T`. The present file gives
the **local, per-scale** reason that absorption is available: on any frequency tail `k ≥ K` whose
`N_K²` is large enough (the threshold `hthr`), the tail transfer `3 |∑ a_{k-1}² a_k|` is already
dominated by the tail dissipation `ν ∑ 16^k u_k²`, with no energy ceiling and no Young constant.
The global capstone is what one gets by taking the tail to be the whole range and paying for the
boundary with `E_max`; the local statement is the scale at which that payment happens.

## Hypotheses, honestly

`tail_transfer_cubic_le` and `scale_dissipation_dominates` carry the Dirichlet condition
`u (-1) = 0`. It is *necessary* for an arbitrary cutoff `K`: for `K = 0` the tail sum contains the
boundary amplitude `a_{-1}²`, which contributes `a_{-1}² a_0` to the transfer but nothing to `H`.
Without `u (-1) = 0` the statement is false (take `u (-1) = 2000`, `u 0 = 1`, `N = 1`, `K = 0`:
the left side is `10^6` while `H √H = 1`). For `K ≥ 1` the Dirichlet hypothesis is not needed; it
is kept so that a single statement covers every cutoff, matching the standing truncation
condition of the model.
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators

namespace Cascade

/-! ## 1. Elementary dyadic-weight monotonicity -/

/-- `dyadicWeight m ≥ 1` for `m ≥ 0`, i.e. `2^m ≥ 2^0 = 1`. This is the factor by which the
dissipation weight `4^k` exceeds `4^K` on the tail `k ≥ K`. -/
theorem one_le_dyadicWeight {m : ℤ} (hm : 0 ≤ m) : 1 ≤ dyadicWeight m := by
  unfold dyadicWeight
  exact one_le_zpow₀ (a := (2 : ℝ)) (by norm_num) hm

/-! ## 2. The shell replacement for Bernstein: `|a_k| ≤ √H` -/

/-- **The shell replacement for Bernstein's `L² → L∞` amplitude bound.** For every retained shell
`k ∈ [0, N)`, the vorticity amplitude obeys `|a_k| ≤ √H` where `H = enstrophy u N = ∑_{j<N} a_j²`.
Because the shell model has explicit amplitudes, this is an *identity-level* bound (each `a_k²` is
a summand of `H`) and is strictly stronger than the spatial Bernstein bound `N^{d/2} √E`: no
frequency factor is lost. -/
theorem vorticity_abs_le_sqrt_enstrophy (u : ℤ → ℝ) (N : ℕ) {k : ℕ}
    (hk : k ∈ Finset.range N) :
    |vorticity u (k : ℤ)| ≤ Real.sqrt (enstrophy u N) := by
  have hH' : enstrophy u N = ∑ j ∈ Finset.range N, (vorticity u (j : ℤ)) ^ 2 := by
    rw [enstrophy]
    exact Finset.sum_congr rfl fun j _ => (vorticity_sq u (j : ℤ)).symm
  have hterm : (vorticity u (k : ℤ)) ^ 2 ≤ enstrophy u N := by
    rw [hH']
    exact Finset.single_le_sum (s := Finset.range N)
      (f := fun j : ℕ => (vorticity u (j : ℤ)) ^ 2) (a := k)
      (fun j _ => sq_nonneg _) hk
  have h1 : |vorticity u (k : ℤ)| = Real.sqrt ((vorticity u (k : ℤ)) ^ 2) :=
    (Real.sqrt_sq_eq_abs _).symm
  rw [h1]
  exact Real.sqrt_le_sqrt hterm

/-! ## 3. Dissipation acts at rate `N_K²` on the tail -/

/-- **Viscous dissipation acts at rate `N_K²` on the frequency tail `K ≤ k < N`.** Writing
`N_K = dyadicWeight K = 2^K`, the tail dissipation weight factors as
`4^k = 4^K · 4^{k-K}` with `4^{k-K} ≥ 1` for `k ≥ K`, so term by term
`4^K · 4^k u_k² ≤ 4^k · 4^k u_k² = 16^k u_k²`; summing gives

`N_K² · ∑_{k∈[K,N)} 4^k u_k² ≤ ∑_{k∈[K,N)} 16^k u_k²`.

The hypothesis `K ≤ N` is part of the intended interface (for `K > N` the tail is empty and the
inequality is trivial). -/
theorem dissipation_tail_ge (u : ℤ → ℝ) (K N : ℕ) (hKN : K ≤ N) :
    dyadicWeight (2 * (K : ℤ))
        * (∑ k ∈ Finset.Ico K N, dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2)
      ≤ ∑ k ∈ Finset.Ico K N, dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2 := by
  have hterm : ∀ k ∈ Finset.Ico K N,
      dyadicWeight (2 * (K : ℤ)) * (dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2)
        ≤ dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2 := by
    intro k hk
    have hkK : (K : ℤ) ≤ (k : ℤ) := by
      exact_mod_cast (Finset.mem_Ico.mp hk).1
    -- `4^k = 4^K · 4^k · 4^{k-K}` with `4^{k-K} ≥ 1`.
    have hW : 1 ≤ dyadicWeight (2 * ((k : ℤ) - (K : ℤ))) :=
      one_le_dyadicWeight (by linarith)
    have h4 : dyadicWeight (4 * (k : ℤ))
        = dyadicWeight (2 * (K : ℤ)) * dyadicWeight (2 * (k : ℤ))
            * dyadicWeight (2 * ((k : ℤ) - (K : ℤ))) := by
      rw [show (4 : ℤ) * (k : ℤ)
            = 2 * (K : ℤ) + 2 * (k : ℤ) + 2 * ((k : ℤ) - (K : ℤ)) by ring,
        dyadicWeight_add, dyadicWeight_add]
    have hcoef : 0 ≤ dyadicWeight (2 * (K : ℤ)) * dyadicWeight (2 * (k : ℤ)) :=
      mul_nonneg (dyadicWeight_nonneg _) (dyadicWeight_nonneg _)
    calc dyadicWeight (2 * (K : ℤ)) * (dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2)
        = dyadicWeight (2 * (K : ℤ)) * dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2 := by
          ring
      _ ≤ dyadicWeight (2 * (K : ℤ)) * dyadicWeight (2 * (k : ℤ))
            * dyadicWeight (2 * ((k : ℤ) - (K : ℤ))) * (u (k : ℤ)) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hcoef hW) (sq_nonneg _)
      _ = dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2 := by rw [h4]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum hterm

/-! ## 4. The transfer into the tail is `H^{3/2}`, independent of `K` -/

/-- **The tail cubic transfer is bounded by `H √H`, uniformly in the cutoff `K`.** This is the
shell replacement for the spatial Bernstein step: `|a_k| ≤ √H` termwise
(`vorticity_abs_le_sqrt_enstrophy`) gives

`|∑_{k∈[K,N)} a_{k-1}² a_k| ≤ ∑ a_{k-1}² |a_k| ≤ √H · ∑_{k∈[K,N)} a_{k-1}²`,

and the shifted tail mass `∑_{k∈[K,N)} a_{k-1}²` is at most `H = ∑_{j<N} a_j²` (the Dirichlet
condition `u (-1) = 0` removes the only offending term, at `k = 0`). Hence the transfer bound is
`H^{3/2}` and *does not depend on `K`*. -/
theorem tail_transfer_cubic_le (u : ℤ → ℝ) (K N : ℕ) (huBot : u (-1) = 0) :
    |∑ k ∈ Finset.Ico K N, (vorticity u ((k : ℤ) - 1)) ^ 2 * vorticity u (k : ℤ)|
      ≤ enstrophy u N * Real.sqrt (enstrophy u N) := by
  -- `|a_k| ≤ √H` on the tail.
  have htail_le : ∀ k ∈ Finset.Ico K N,
      (vorticity u ((k : ℤ) - 1)) ^ 2 * |vorticity u (k : ℤ)|
        ≤ (vorticity u ((k : ℤ) - 1)) ^ 2 * Real.sqrt (enstrophy u N) := by
    intro k hk
    have hkN : k ∈ Finset.range N := Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
    exact mul_le_mul_of_nonneg_left (vorticity_abs_le_sqrt_enstrophy u N hkN) (sq_nonneg _)
  -- The shifted mass `∑_{k<N} a_{k-1}²` is at most `H`; `u (-1) = 0` handles the `k = 0` term.
  have hshift : (∑ k ∈ Finset.range N, (vorticity u ((k : ℤ) - 1)) ^ 2) ≤ enstrophy u N := by
    have hH' : enstrophy u N = ∑ j ∈ Finset.range N, (vorticity u (j : ℤ)) ^ 2 := by
      rw [enstrophy]
      exact Finset.sum_congr rfl fun j _ => (vorticity_sq u (j : ℤ)).symm
    rw [hH']
    cases N with
    | zero => simp
    | succ M =>
      have heq : (∑ k ∈ Finset.range (M + 1), (vorticity u ((k : ℤ) - 1)) ^ 2)
          = ∑ k ∈ Finset.range M, (vorticity u (k : ℤ)) ^ 2 := by
        rw [Finset.sum_range_succ']
        have hlast : (vorticity u (((0 : ℕ) : ℤ) - 1)) ^ 2 = 0 := by
          have h0 : (((0 : ℕ) : ℤ) - 1) = -1 := by norm_num
          rw [h0, vorticity_neg_one u huBot]
          ring
        have hstep : ∀ k : ℕ,
            (vorticity u (((k + 1 : ℕ) : ℤ) - 1)) ^ 2 = (vorticity u (k : ℤ)) ^ 2 := by
          intro k
          have hidx : (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) := by
            push_cast
            ring
          rw [hidx]
        rw [hlast, add_zero]
        exact Finset.sum_congr rfl fun k _ => hstep k
      rw [heq, Finset.sum_range_succ]
      exact le_add_of_nonneg_right (sq_nonneg _)
  have htail_shift :
      (∑ k ∈ Finset.Ico K N, (vorticity u ((k : ℤ) - 1)) ^ 2) ≤ enstrophy u N := by
    have hsub : Finset.Ico K N ⊆ Finset.range N :=
      fun k hk => Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => sq_nonneg _)).trans hshift
  calc |∑ k ∈ Finset.Ico K N, (vorticity u ((k : ℤ) - 1)) ^ 2 * vorticity u (k : ℤ)|
      ≤ ∑ k ∈ Finset.Ico K N,
          |(vorticity u ((k : ℤ) - 1)) ^ 2 * vorticity u (k : ℤ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ Finset.Ico K N,
          (vorticity u ((k : ℤ) - 1)) ^ 2 * |vorticity u (k : ℤ)| := by
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    _ ≤ ∑ k ∈ Finset.Ico K N,
          (vorticity u ((k : ℤ) - 1)) ^ 2 * Real.sqrt (enstrophy u N) :=
        Finset.sum_le_sum htail_le
    _ = (∑ k ∈ Finset.Ico K N, (vorticity u ((k : ℤ) - 1)) ^ 2)
          * Real.sqrt (enstrophy u N) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ enstrophy u N * Real.sqrt (enstrophy u N) :=
        mul_le_mul_of_nonneg_right htail_shift (Real.sqrt_nonneg _)

/-! ## 5. Scale-localized dissipation dominance -/

/-- **Scale-localized dominance of the transfer by viscous dissipation.** Retaining the tail
`k ∈ [K, N)` and writing `H = enstrophy u N`, `H_tail = ∑_{k∈[K,N)} 4^k u_k²`, if the explicit
threshold

`3 H √H ≤ ν · N_K² · H_tail`

holds, then the tail transfer is dominated by the tail dissipation:

`3 |∑_{k∈[K,N)} a_{k-1}² a_k| ≤ ν ∑_{k∈[K,N)} 16^k u_k²`.

Indeed item 4 bounds the left side by `3 H √H`, the threshold transfers that bound to
`ν N_K² H_tail`, and item 3 (`dissipation_tail_ge`) converts `N_K² H_tail` into the tail
dissipation `∑ 16^k u_k²`. This is Palasek's `N_k^{3/2}`-versus-`ν N_k²` comparison in shell
variables, with the frequency factor absorbed into the threshold and no `N^{3/2}` written
literally. The cleanest equivalent reading of the threshold is

`3 √H ≤ ν · N_K² · H_tail / H`  (for `H > 0`),

i.e. dissipation wins once the tail carries enough enstrophy relative to `H^{3/2}/(ν N_K²)`.

The Dirichlet hypothesis `u (-1) = 0` is inherited from item 4; see the file header for why it is
necessary at the cutoff `K = 0`. -/
theorem scale_dissipation_dominates (ν : ℝ) (hν : 0 < ν) (u : ℤ → ℝ) (K N : ℕ) (hKN : K ≤ N)
    (huBot : u (-1) = 0)
    (hthr : 3 * (enstrophy u N * Real.sqrt (enstrophy u N))
              ≤ ν * dyadicWeight (2 * (K : ℤ))
                  * (∑ k ∈ Finset.Ico K N, dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2)) :
    3 * |∑ k ∈ Finset.Ico K N, (vorticity u ((k : ℤ) - 1)) ^ 2 * vorticity u (k : ℤ)|
      ≤ ν * (∑ k ∈ Finset.Ico K N, dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2) := by
  have htr := tail_transfer_cubic_le u K N huBot
  have htr3 : 3 * |∑ k ∈ Finset.Ico K N,
        (vorticity u ((k : ℤ) - 1)) ^ 2 * vorticity u (k : ℤ)|
      ≤ 3 * (enstrophy u N * Real.sqrt (enstrophy u N)) :=
    mul_le_mul_of_nonneg_left htr (by norm_num)
  have hdiss := dissipation_tail_ge u K N hKN
  have hdissν : ν * (dyadicWeight (2 * (K : ℤ))
        * (∑ k ∈ Finset.Ico K N, dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2))
      ≤ ν * (∑ k ∈ Finset.Ico K N, dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2) :=
    mul_le_mul_of_nonneg_left hdiss hν.le
  linarith

/-! ## 6. The `d/2`-versus-`2` dichotomy

`Cascade/BernsteinTransfer.lean` proves the *low*-dimensional direction at the root namespace:
`bernstein_exponent_le_dissipation : N^{d/2} ≤ N²` for `d ≤ 4`, `N ≥ 1`. We restate it under the
`Cascade` namespace so both directions sit side by side, and add the missing *high*-dimensional
direction `N² < N^{d/2}` for `d ≥ 5`, `N > 1`, which is Palasek's "in high dimension there is no
obstruction". (For `d = 4` the exponents coincide and the two powers are equal; for `d = 5` the
Bernstein amplitude `N^{5/2}` grows strictly faster than the damping `N²`.) -/

/-- The `d ≤ 4` direction of the dichotomy, restated in the `Cascade` namespace from the
root-namespace theorem `bernstein_exponent_le_dissipation` of `Cascade/BernsteinTransfer.lean`: the
Bernstein transfer exponent `d/2` is dominated by the dissipation exponent `2`. -/
theorem bernstein_exponent_le_dissipation {d : ℕ} (hd : d ≤ 4) (N : ℝ) (hN : 1 ≤ N) :
    N ^ ((d : ℝ) / 2) ≤ N ^ (2 : ℝ) :=
  _root_.bernstein_exponent_le_dissipation hd N hN

/-- **In high dimension there is no obstruction.** For `d ≥ 5` and `N > 1` the Bernstein exponent
`d/2` exceeds the dissipation exponent `2`, so the spatial amplitude bound `N^{d/2}` grows strictly
faster than the viscous damping `N²`: the frequency-localized comparison used in dimensions
`d ≤ 4` fails. This is the exact high-dimensional complement of
`bernstein_exponent_le_dissipation`, obtained from `Real.rpow_lt_rpow_of_exponent_lt` and
`2 < d/2`. -/
theorem bernstein_exponent_gt_dissipation {d : ℕ} (hd : 5 ≤ d) (N : ℝ) (hN : 1 < N) :
    N ^ (2 : ℝ) < N ^ ((d : ℝ) / 2) := by
  refine Real.rpow_lt_rpow_of_exponent_lt hN ?_
  have hd' : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  linarith

/-! ## 7. Non-vacuity

The concrete state is `u = (0, 1, 3, 0)` on the shells `-1, 0, 1, 2` (zero elsewhere), i.e. the
vorticity amplitudes `a = (0, 1, 6, 0)`. With `N = 2` and the cutoff `K = 1`:

* `H = enstrophy u 2 = 4^0 · 1² + 4^1 · 3² = 37`;
* the tail mass is `H_tail = 4^1 · 3² = 36` and the tail dissipation is `16^1 · 3² = 144`;
* item 1 reads `N_K² H_tail ≤ ∑ 16^k u_k²`, i.e. `4 · 36 = 144 ≤ 144`, an equality;
* the tail transfer is `a_0² a_1 = 1 · 6 = 6`, and item 2 reads `6 ≤ 37 √37 ≈ 225.06`;
* with `ν = 1` the threshold `hthr` is `3 · 37 √37 = 111 √37 ≈ 675.2 ≤ 4 · 36 = 144`, which is
  **false**: the cutoff `K = 1` is too low for the given state, so item 5 is vacuous there. With
  `ν = 5` the threshold becomes `≤ 5 · 144 = 720`, which holds, and the conclusion is
  `3 · 6 = 18 ≤ 5 · 144 = 720`. A small state that already satisfies the threshold at `ν = 1` is
  `u = (0, 0, 1/2, 0)`, where `H = H_tail = 1` and `3 · 1 · 1 = 3 ≤ 4 · 1 = 4`.
-/

/-- The concrete velocity ladder `u = (0, 1, 3, 0)` on the shells `-1, 0, 1, 2`. -/
private def uEx : ℤ → ℝ :=
  fun k => if k = -1 then 0 else if k = 0 then 1 else if k = 1 then 3 else if k = 2 then 0 else 0

/-- A small concrete ladder `u = (0, 0, 1/2, 0)` on the shells `-1, 0, 1, 2`. -/
private def uSmall : ℤ → ℝ :=
  fun k => if k = -1 then 0 else if k = 0 then 0 else if k = 1 then 1 / 2
    else if k = 2 then 0 else 0

/-- Concrete enstrophy: `H = 4^0 · 1² + 4^1 · 3² = 37`. -/
example : enstrophy uEx 2 = 37 := by
  norm_num [enstrophy, Finset.sum_range_succ, Finset.sum_range_zero, uEx, dyadicWeight]

/-- Concrete vorticity amplitude at the state: `a_0 = 1`, `a_1 = 6`. -/
example : vorticity uEx 0 = 1 ∧ vorticity uEx 1 = 6 := by
  constructor <;> norm_num [vorticity, uEx, dyadicWeight]

/-- The tail mass of item 1: `∑_{k∈[1,2)} 4^k u_k² = 36`. -/
example : (∑ k ∈ Finset.Ico (1 : ℕ) 2, dyadicWeight (2 * (k : ℤ)) * (uEx (k : ℤ)) ^ 2) = 36 := by
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uEx, dyadicWeight]

/-- The left side of item 1: `N_K² H_tail = 4 · 36 = 144`. -/
example : dyadicWeight (2 * (1 : ℤ))
      * (∑ k ∈ Finset.Ico (1 : ℕ) 2, dyadicWeight (2 * (k : ℤ)) * (uEx (k : ℤ)) ^ 2) = 144 := by
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uEx, dyadicWeight]

/-- The right side of item 1: the tail dissipation `∑_{k∈[1,2)} 16^k u_k² = 144`. -/
example : (∑ k ∈ Finset.Ico (1 : ℕ) 2, dyadicWeight (4 * (k : ℤ)) * (uEx (k : ℤ)) ^ 2) = 144 := by
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uEx, dyadicWeight]

/-- **Item 1 at the concrete state: `144 ≤ 144`** (with equality, so the rate `N_K²` is exact
here). -/
example : dyadicWeight (2 * (1 : ℤ))
      * (∑ k ∈ Finset.Ico (1 : ℕ) 2, dyadicWeight (2 * (k : ℤ)) * (uEx (k : ℤ)) ^ 2)
    ≤ ∑ k ∈ Finset.Ico (1 : ℕ) 2, dyadicWeight (4 * (k : ℤ)) * (uEx (k : ℤ)) ^ 2 :=
  dissipation_tail_ge uEx 1 2 (by norm_num)

/-- The tail cubic transfer of item 2: `a_0² a_1 = 1 · 6 = 6`. -/
example :
    (∑ k ∈ Finset.Ico (1 : ℕ) 2, (vorticity uEx ((k : ℤ) - 1)) ^ 2 * vorticity uEx (k : ℤ)) = 6 := by
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uEx, vorticity, dyadicWeight]

/-- **Item 2 at the concrete state: `6 ≤ 37 √37 ≈ 225.06`** (through the theorem). -/
example : |∑ k ∈ Finset.Ico (1 : ℕ) 2,
        (vorticity uEx ((k : ℤ) - 1)) ^ 2 * vorticity uEx (k : ℤ)|
      ≤ enstrophy uEx 2 * Real.sqrt (enstrophy uEx 2) :=
  tail_transfer_cubic_le uEx 1 2 (by norm_num [uEx])

/-- The numerical content of item 2: `6 ≤ 37 √37`. -/
example : (6 : ℝ) ≤ 37 * Real.sqrt 37 := by
  have h6 : (6 : ℝ) ≤ Real.sqrt 37 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  nlinarith [h6]

/-- **The threshold `hthr` fails at `ν = 1`**: `3 · 37 √37 = 111 √37 ≈ 675.2 ≰ 144 = 4 · 36`. -/
example : ¬ (3 * (37 * Real.sqrt 37) ≤ (1 : ℝ) * dyadicWeight (2 * (1 : ℤ))
      * (∑ k ∈ Finset.Ico (1 : ℕ) 2, dyadicWeight (2 * (k : ℤ)) * (uEx (k : ℤ)) ^ 2)) := by
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uEx, dyadicWeight]
  have h6 : (6 : ℝ) ≤ Real.sqrt 37 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  nlinarith [h6]

/-- **The threshold `hthr` holds at `ν = 5`**: `111 √37 ≈ 675.2 ≤ 720 = 5 · 4 · 36`. -/
example : 3 * (37 * Real.sqrt 37) ≤ (5 : ℝ) * dyadicWeight (2 * (1 : ℤ))
      * (∑ k ∈ Finset.Ico (1 : ℕ) 2, dyadicWeight (2 * (k : ℤ)) * (uEx (k : ℤ)) ^ 2) := by
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uEx, dyadicWeight]
  nlinarith [sq_nonneg (111 * Real.sqrt 37 - 720),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 37)]

/-- **Item 5 instantiated at `ν = 5`**: `3 · 6 = 18 ≤ 5 · 144 = 720`. The threshold is
satisfiable at the concrete state once the viscosity is large enough. -/
example : 3 * |∑ k ∈ Finset.Ico (1 : ℕ) 2,
        (vorticity uEx ((k : ℤ) - 1)) ^ 2 * vorticity uEx (k : ℤ)|
      ≤ (5 : ℝ) * (∑ k ∈ Finset.Ico (1 : ℕ) 2,
          dyadicWeight (4 * (k : ℤ)) * (uEx (k : ℤ)) ^ 2) := by
  refine scale_dissipation_dominates 5 (by norm_num) uEx 1 2 (by norm_num) (by norm_num [uEx]) ?_
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uEx, dyadicWeight, enstrophy]
  nlinarith [sq_nonneg (111 * Real.sqrt 37 - 720),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 37)]

/-- Enstrophy of the small state: `H = 4^1 · (1/2)² = 1`. -/
example : enstrophy uSmall 2 = 1 := by
  norm_num [enstrophy, Finset.sum_range_succ, Finset.sum_range_zero, uSmall, dyadicWeight]

/-- **The threshold `hthr` already holds at `ν = 1` for the small state**: `3 · 1 · 1 = 3 ≤ 4 = 4 · 1`. -/
example : 3 * (enstrophy uSmall 2 * Real.sqrt (enstrophy uSmall 2))
      ≤ (1 : ℝ) * dyadicWeight (2 * (1 : ℤ))
        * (∑ k ∈ Finset.Ico (1 : ℕ) 2, dyadicWeight (2 * (k : ℤ)) * (uSmall (k : ℤ)) ^ 2) := by
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uSmall, dyadicWeight, enstrophy]

/-- **Item 5 for the small state at `ν = 1`**: `0 ≤ 4`. -/
example : 3 * |∑ k ∈ Finset.Ico (1 : ℕ) 2,
        (vorticity uSmall ((k : ℤ) - 1)) ^ 2 * vorticity uSmall (k : ℤ)|
      ≤ (1 : ℝ) * (∑ k ∈ Finset.Ico (1 : ℕ) 2,
          dyadicWeight (4 * (k : ℤ)) * (uSmall (k : ℤ)) ^ 2) := by
  refine scale_dissipation_dominates 1 (by norm_num) uSmall 1 2 (by norm_num)
    (by norm_num [uSmall]) ?_
  rw [Finset.sum_Ico_eq_sum_range]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uSmall, dyadicWeight, enstrophy]

/-- **High dimension: no obstruction.** At `N = 2`, `d = 5`: `2² = 4 < 2^{5/2} = 4√2 ≈ 5.657`. -/
example : (2 : ℝ) ^ (2 : ℝ) < (2 : ℝ) ^ ((5 : ℝ) / 2) :=
  bernstein_exponent_gt_dissipation (d := 5) (by norm_num) 2 (by norm_num)

/-- **Low dimension: obstruction.** At `N = 2`, `d = 4` the two exponents coincide, `4 ≤ 4`. -/
example : (2 : ℝ) ^ ((4 : ℝ) / 2) ≤ (2 : ℝ) ^ (2 : ℝ) :=
  bernstein_exponent_le_dissipation (d := 4) (by norm_num) 2 (by norm_num)

end Cascade

/-! ## Axiom audit -/

#print axioms Cascade.one_le_dyadicWeight
#print axioms Cascade.vorticity_abs_le_sqrt_enstrophy
#print axioms Cascade.dissipation_tail_ge
#print axioms Cascade.tail_transfer_cubic_le
#print axioms Cascade.scale_dissipation_dominates
#print axioms Cascade.bernstein_exponent_le_dissipation
#print axioms Cascade.bernstein_exponent_gt_dissipation
