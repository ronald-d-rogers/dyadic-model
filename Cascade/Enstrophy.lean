import Cascade.NoBlowup
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Stage O′ — the enstrophy (H¹) no-blowup inequality for the dyadic Boussinesq model

This file upgrades the Stage-O statement from the velocity **energy** `E = ∑_{k<N} u_k²` to the
**enstrophy** `H = ∑_{k<N} 4^k u_k²`, which is the norm in which H¹ blowup is measured. The
model is the frozen Stage R model of `Cascade/Boussinesq.lean`,
`du_k/dt = 2^k (u_{k-1}² − 2 u_k u_{k+1}) + κ θ_k − ν 4^k u_k`, closed by the truncation /
Dirichlet conditions `u(-1) = u(N) = 0`.

## Why energy conservation is not the whole story

Write `a_k := 2^k u_k` for the **vorticity amplitude** `vorticity u k`. Pairing the velocity
ladder with its nonlinear transfer `T^u_k = 2^k (u_{k-1}² − 2 u_k u_{k+1})`,

* the **energy** pairing telescopes to a boundary flux and vanishes under Dirichlet:
  `∑_{k<N} u_k T^u_k = 0` (`dyadic_velocity_pairing_eq_flux`); but
* the **enstrophy** pairing does *not* vanish. The new identity
  `enstrophy_pairing` (item 1 below) computes it exactly:
  `∑_{k<N} 4^k u_k T^u_k = 3 ∑_{k<N} a_{k-1}² a_k`,
  a pure **cubic** sum with no boundary term (the two boundary contributions of the
  telescoping — the "enstrophy flux" `enstrophyFlux` — vanish by Dirichlet). So enstrophy is
  genuinely transferred across scales: this is the dyadic cascade.

## The balance of transfer and dissipation

The same identity separates the enstrophy pairing into transfer, buoyancy and dissipation:

`∑_{k<N} 4^k u_k (du_k/dt) = 3 ∑ a_{k-1}² a_k + κ ∑ 4^k u_k θ_k − ν ∑ 16^k u_k²`.

The two competing forces are *not* of the same homogeneity:

* the transfer is **cubic**, `∑ a_{k-1}² a_k ≤ H · √H = H^{3/2}` (item 2), while
* the viscous dissipation is bounded below by the **quadratic** interpolation
  `∑ 16^k u_k² ≥ H² / E` (item 3), and
* the buoyancy is bounded by `√H · √T` with `T = ∑ 4^k θ_k²` the temperature enstrophy (item 4).

Hence the headline pointwise inequality (item 5)

`∑ 4^k u_k (du_k/dt) ≤ 3 H^{3/2} + κ √H √T − ν H²/E`.

Since `H^{3/2} / (H²/E) = E / √H → 0`, in the enstrophy budget **dissipation beats transfer**
whenever `H` is large relative to `E`. This is the correct form of the domination statement: the
naive term-by-term comparison of the two sums at shell `N` gives `N^{3/2}` for the transfer versus
`N²` for the dissipation, which is *not* a scale-invariant statement, whereas `H^{3/2}` versus
`H²/E` is exactly the homogeneity of the two terms and yields the cascade exponent.

## Contents

* `enstrophy`, `tempEnstrophy`, `vorticity` — the three basic quantities.
* `enstrophy_pairing` — the exact enstrophy pairing identity (the new mathematics).
* `sum_vorticity_cubic_le` — the cubic bound `∑ a_{k-1}² a_k ≤ H √H`.
* `enstrophy_sq_le_dissipation_mul_energy` — the interpolation `H² ≤ (∑16^k u_k²) E`.
* `buoyancy_enstrophy_le` — the buoyancy Cauchy–Schwarz `∑ 4^k u_k θ_k ≤ √H √T`.
* `enstrophy_pairing_le` — the headline pointwise enstrophy inequality.
* a non-vacuity section evaluating everything at the concrete state `u = (0,1,3,0)`.
-/

noncomputable section

open scoped BigOperators

namespace Cascade

/-! ## 1. Enstrophy, temperature enstrophy and vorticity amplitude -/

/-- Enstrophy `H = Σ_{k<N} 4^k u_k²`. -/
def enstrophy (u : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2

/-- Temperature enstrophy `T = Σ_{k<N} 4^k θ_k²`. -/
def tempEnstrophy (θ : ℤ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * (θ (k : ℤ)) ^ 2

/-- Vorticity amplitude `a_k = 2^k u_k`. -/
def vorticity (u : ℤ → ℝ) (k : ℤ) : ℝ := dyadicWeight k * u k

/-! ## 2. Elementary facts about the dyadic weight

The dyadic weight `dyadicWeight k = 2^k` is multiplicative (`dyadicWeight_add`), strictly
positive, and its values on the multiples used below are `dyadicWeight (2k) = (dyadicWeight k)²`,
`dyadicWeight (3k) = (dyadicWeight k)³`, `dyadicWeight (4k) = (dyadicWeight (2k))²` and
`dyadicWeight (-1) = 1/2`. -/

/-- The dyadic weight is multiplicative in the exponent. -/
theorem dyadicWeight_add (a b : ℤ) : dyadicWeight (a + b) = dyadicWeight a * dyadicWeight b := by
  unfold dyadicWeight
  exact zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) a b

/-- Integer multiples of the exponent become integer powers of the weight. -/
theorem dyadicWeight_mul_int (m k : ℤ) : dyadicWeight (m * k) = (dyadicWeight k) ^ m := by
  unfold dyadicWeight
  rw [mul_comm m k, zpow_mul]

/-- `dyadicWeight (2k) = (dyadicWeight k)²`. -/
theorem dyadicWeight_two_mul (k : ℤ) : dyadicWeight (2 * k) = (dyadicWeight k) ^ 2 := by
  unfold dyadicWeight
  rw [mul_comm 2 k, zpow_mul]
  norm_num

/-- `dyadicWeight (3k) = (dyadicWeight k)³`. -/
theorem dyadicWeight_three_mul (k : ℤ) : dyadicWeight (3 * k) = (dyadicWeight k) ^ 3 := by
  have h := dyadicWeight_mul_int 3 k
  simpa using h

/-- `dyadicWeight (3 (k+1)) = 8 (dyadicWeight k)³`. -/
theorem dyadicWeight_three_mul_succ (k : ℤ) :
    dyadicWeight (3 * (k + 1)) = (dyadicWeight k) ^ 3 * 8 := by
  have h3 : dyadicWeight (3 : ℤ) = 8 := by norm_num [dyadicWeight]
  rw [show 3 * (k + 1) = 3 * k + 3 by ring, dyadicWeight_add, dyadicWeight_three_mul, h3]

/-- `dyadicWeight (4k) = (dyadicWeight (2k))²`. -/
theorem dyadicWeight_four_mul (k : ℤ) : dyadicWeight (4 * k) = (dyadicWeight (2 * k)) ^ 2 := by
  rw [show (4 : ℤ) * k = 2 * k + 2 * k by ring, dyadicWeight_add, sq]

/-- `dyadicWeight (-1) = 1/2`. -/
theorem dyadicWeight_neg_one : dyadicWeight (-1) = (1 / 2 : ℝ) := by
  norm_num [dyadicWeight]

/-- Every dyadic weight is strictly positive. -/
theorem dyadicWeight_pos (k : ℤ) : (0 : ℝ) < dyadicWeight k := by
  unfold dyadicWeight
  exact zpow_pos (by norm_num : (0 : ℝ) < 2) k

/-- Every dyadic weight is nonnegative. -/
theorem dyadicWeight_nonneg (k : ℤ) : (0 : ℝ) ≤ dyadicWeight k := (dyadicWeight_pos k).le

/-! ## 3. Vorticity amplitude facts -/

/-- The square of the vorticity amplitude is a full enstrophy density:
`(a_k)² = 4^k u_k² = dyadicWeight (2k) u_k²`. -/
theorem vorticity_sq (u : ℤ → ℝ) (k : ℤ) :
    (vorticity u k) ^ 2 = dyadicWeight (2 * k) * (u k) ^ 2 := by
  unfold vorticity
  rw [mul_pow, ← dyadicWeight_two_mul]

/-- The Dirichlet condition `u(-1) = 0` kills the vorticity amplitude at the bottom shell. -/
theorem vorticity_neg_one (u : ℤ → ℝ) (h : u (-1) = 0) : vorticity u (-1) = 0 := by
  unfold vorticity
  rw [h, mul_zero]

/-- The enstrophy is nonnegative. -/
theorem enstrophy_nonneg (u : ℤ → ℝ) (N : ℕ) : 0 ≤ enstrophy u N := by
  rw [enstrophy]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (dyadicWeight_nonneg _) (sq_nonneg _)

/-- The temperature enstrophy is nonnegative. -/
theorem tempEnstrophy_nonneg (θ : ℤ → ℝ) (N : ℕ) : 0 ≤ tempEnstrophy θ N := by
  rw [tempEnstrophy]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (dyadicWeight_nonneg _) (sq_nonneg _)

/-! ## 4. The enstrophy flux and the pointwise transfer identity

The whole point of the enstrophy computation is that, unlike the energy pairing, the weighted
pairing of the transfer does **not** telescope to zero: it has a bulk cubic piece plus a
boundary piece. The boundary piece is the *enstrophy flux*
`enstrophyFlux u k = (1/4) 8^k u_{k-1}² u_k`, whose values at `k = 0` and `k = N` vanish by
Dirichlet. The pointwise identity behind the telescoping is
`4^k u_k T^u_k = 3 a_{k-1}² a_k + enstrophyFlux u k − enstrophyFlux u (k+1)`. -/

/-- The enstrophy flux through the shell boundary `k`: `(1/4) 8^k u_{k-1}² u_k`. -/
def enstrophyFlux (u : ℤ → ℝ) (k : ℤ) : ℝ :=
  (1 / 4) * dyadicWeight (3 * k) * (u (k - 1)) ^ 2 * u k

/-- **Pointwise enstrophy transfer identity.** The weighted pairing of the nonlinear velocity
transfer at shell `k` is the cubic enstrophy transfer `3 a_{k-1}² a_k` plus the difference of the
enstrophy flux across the shell. -/
theorem transfer_enstrophy_pointwise (u : ℤ → ℝ) (k : ℤ) :
    dyadicWeight (2 * k) * u k * boussinesqTransferU 1 0 u k
      = 3 * (vorticity u (k - 1)) ^ 2 * vorticity u k
        + enstrophyFlux u k - enstrophyFlux u (k + 1) := by
  simp only [boussinesqTransferU, one_mul, zero_mul, add_zero, vorticity, enstrophyFlux]
  rw [dyadicWeight_three_mul_succ, dyadicWeight_two_mul, dyadicWeight_three_mul,
    show k - 1 = k + (-1) by ring, dyadicWeight_add, dyadicWeight_neg_one]
  ring_nf

/-- **Summed transfer identity.** Summing the pointwise identity over the retained shells and
telescoping, the boundary enstrophy fluxes vanish by the Dirichlet conditions `u(-1) = u(N) = 0`,
leaving only the cubic transfer sum `3 ∑ a_{k-1}² a_k`. -/
theorem sum_transfer_enstrophy (u : ℤ → ℝ) (N : ℕ)
    (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0) :
    (∑ k ∈ Finset.range N,
        dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * boussinesqTransferU 1 0 u (k : ℤ))
      = 3 * (∑ k ∈ Finset.range N, (vorticity u ((k : ℤ) - 1)) ^ 2 * vorticity u (k : ℤ)) := by
  have hpt : ∀ k ∈ Finset.range N,
      dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * boussinesqTransferU 1 0 u (k : ℤ)
        = 3 * ((vorticity u ((k : ℤ) - 1)) ^ 2 * vorticity u (k : ℤ))
          + ((fun m : ℕ => enstrophyFlux u (m : ℤ)) k
              - (fun m : ℕ => enstrophyFlux u (m : ℤ)) (k + 1)) := by
    intro k _
    rw [transfer_enstrophy_pointwise]
    push_cast
    ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_range_sub', ← Finset.mul_sum]
  have h0 : enstrophyFlux u (((0 : ℕ) : ℤ)) = 0 := by
    unfold enstrophyFlux
    rw [show (((0 : ℕ) : ℤ)) - 1 = -1 by norm_num, huBot]
    ring
  have hN : enstrophyFlux u (N : ℤ) = 0 := by
    unfold enstrophyFlux
    rw [huTop]
    ring
  rw [h0, hN]
  ring

/-! ## 5. The enstrophy pairing identity -/

/-- **The enstrophy pairing identity (Stage O′).** Weighting the velocity equation by `4^k u_k`
and summing over the truncated range,

`∑_{k<N} 4^k u_k (du_k/dt) = 3 ∑_{k<N} a_{k-1}² a_k + κ ∑_{k<N} 4^k u_k θ_k − ν ∑_{k<N} 16^k u_k²`.

The novel term is the **cubic** enstrophy transfer `3 ∑ a_{k-1}² a_k`, which does not vanish:
the velocity transfer conserves energy exactly but transfers enstrophy across scales. The
buoyancy and dissipation sums are the immediate `κ`- and `ν`-weighted pieces, the dissipation
being `ν ∑ dyadicWeight (4k) u_k² = ν ∑ 16^k u_k²`. -/
theorem enstrophy_pairing (ν κ : ℝ) (u θ : ℤ → ℝ) (N : ℕ)
    (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0) :
    (∑ k ∈ Finset.range N,
        dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * dyadicVelocityRHS ν κ u θ (k : ℤ))
      = 3 * (∑ k ∈ Finset.range N, (vorticity u ((k : ℤ) - 1)) ^ 2 * vorticity u (k : ℤ))
        + κ * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ))
        - ν * (∑ k ∈ Finset.range N, dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2) := by
  have hsplit : ∀ k ∈ Finset.range N,
      dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * dyadicVelocityRHS ν κ u θ (k : ℤ)
        = dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * boussinesqTransferU 1 0 u (k : ℤ)
          + κ * (dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ))
          - ν * (dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2) := by
    intro k _
    have h4 : dyadicWeight (4 * (k : ℤ))
        = dyadicWeight (2 * (k : ℤ)) * dyadicWeight (2 * (k : ℤ)) := by
      rw [show (4 : ℤ) * (k : ℤ) = 2 * (k : ℤ) + 2 * (k : ℤ) by ring, dyadicWeight_add]
    simp only [dyadicVelocityRHS, generalVelocityRHS]
    rw [h4]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hκ : (∑ k ∈ Finset.range N, κ * (dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ)))
      = κ * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ)) := by
    rw [Finset.mul_sum]
  have hν : (∑ k ∈ Finset.range N, ν * (dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2))
      = ν * (∑ k ∈ Finset.range N, dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2) := by
    rw [Finset.mul_sum]
  rw [hκ, hν, sum_transfer_enstrophy u N huBot huTop]

/-! ## 6. The cubic bound `∑ a_{k-1}² a_k ≤ H √H` -/

/-- **The cubic enstrophy transfer is bounded by `H √H`.** Writing `a_k = 2^k u_k` and
`H = ∑ a_k²`, each term obeys `a_{k-1}² a_k ≤ a_{k-1}² √H` because `a_k² ≤ H`; summing and using
the Dirichlet condition `a_{-1} = 0` to shift the index gives `∑ a_{k-1}² a_k ≤ √H ∑ a_{k-1}² ≤
√H · H`. (This is the elementary version of the Hölder/`(3/2, 3)` estimate
`∑ a_{k-1}² a_k ≤ (∑ a³)^{2/3} (∑ a³)^{1/3} ≤ √H · H`; the termwise bound avoids root
arithmetic.)

The hypothesis `u(-1) = 0` is *necessary*: without it the bottom shell contributes an
uncontrolled `a_{-1}² a_0` to the sum while contributing nothing to `H`. -/
theorem sum_vorticity_cubic_le (u : ℤ → ℝ) (N : ℕ) (huBot : u (-1) = 0) :
    (∑ k ∈ Finset.range N, (vorticity u ((k : ℤ) - 1)) ^ 2 * vorticity u (k : ℤ))
      ≤ enstrophy u N * Real.sqrt (enstrophy u N) := by
  have hH' : enstrophy u N = ∑ k ∈ Finset.range N, (vorticity u (k : ℤ)) ^ 2 := by
    rw [enstrophy]
    exact Finset.sum_congr rfl fun k _ => (vorticity_sq u (k : ℤ)).symm
  have hterm_le : ∀ k ∈ Finset.range N, (vorticity u (k : ℤ)) ^ 2 ≤ enstrophy u N := by
    intro k hk
    rw [hH']
    exact Finset.single_le_sum (s := Finset.range N)
      (f := fun j : ℕ => (vorticity u (j : ℤ)) ^ 2) (a := k)
      (fun j _ => sq_nonneg _) hk
  have hterm : ∀ k ∈ Finset.range N,
      (vorticity u ((k : ℤ) - 1)) ^ 2 * vorticity u (k : ℤ)
        ≤ (vorticity u ((k : ℤ) - 1)) ^ 2 * Real.sqrt (enstrophy u N) := by
    intro k hk
    have hle : vorticity u (k : ℤ) ≤ Real.sqrt (enstrophy u N) :=
      calc vorticity u (k : ℤ) ≤ |vorticity u (k : ℤ)| := le_abs_self _
        _ = Real.sqrt ((vorticity u (k : ℤ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (enstrophy u N) := Real.sqrt_le_sqrt (hterm_le k hk)
    exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
  have hshift : (∑ k ∈ Finset.range N, (vorticity u ((k : ℤ) - 1)) ^ 2) ≤ enstrophy u N := by
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
  calc (∑ k ∈ Finset.range N, (vorticity u ((k : ℤ) - 1)) ^ 2 * vorticity u (k : ℤ))
      ≤ ∑ k ∈ Finset.range N,
          ((vorticity u ((k : ℤ) - 1)) ^ 2 * Real.sqrt (enstrophy u N)) :=
        Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.range N, (vorticity u ((k : ℤ) - 1)) ^ 2)
          * Real.sqrt (enstrophy u N) := by
        rw [Finset.sum_mul]
    _ ≤ enstrophy u N * Real.sqrt (enstrophy u N) :=
        mul_le_mul_of_nonneg_right hshift (Real.sqrt_nonneg _)

/-! ## 7. Interpolation: `H² ≤ (∑ 16^k u_k²) E` -/

/-- **Enstrophy interpolation.** Cauchy–Schwarz applied to the decomposition
`a_k² = (4^k u_k) · u_k` gives
`H² = (∑ 4^k u_k²)² ≤ (∑ 16^k u_k²) (∑ u_k²) = (∑ dyadicWeight (4k) u_k²) E`.
This is the dissipative side of the enstrophy budget: the viscous term `ν ∑ 16^k u_k²` controls
`ν H²/E`. -/
theorem enstrophy_sq_le_dissipation_mul_energy (u : ℤ → ℝ) (N : ℕ) :
    (enstrophy u N) ^ 2
      ≤ (∑ k ∈ Finset.range N, dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2)
        * velocityEnergy u N := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun k : ℕ => dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)) (fun k : ℕ => u (k : ℤ))
  have hL : (∑ k ∈ Finset.range N, (dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)) * u (k : ℤ))
      = ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2 :=
    Finset.sum_congr rfl fun _ _ => by ring
  have hF : (∑ k ∈ Finset.range N, (dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)) ^ 2)
      = ∑ k ∈ Finset.range N, dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow, ← dyadicWeight_four_mul]
  rw [hL, hF] at hcs
  simpa [enstrophy, velocityEnergy] using hcs

/-! ## 8. Buoyancy Cauchy–Schwarz `∑ 4^k u_k θ_k ≤ √H √T` -/

/-- **Buoyancy bound in the enstrophy norm.** Cauchy–Schwarz with `x_k = 2^k u_k`,
`y_k = 2^k θ_k` gives `∑ 4^k u_k θ_k ≤ √(∑ 4^k u_k²) √(∑ 4^k θ_k²) = √H √T`. -/
theorem buoyancy_enstrophy_le (u θ : ℤ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ))
      ≤ Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun k : ℕ => dyadicWeight (k : ℤ) * u (k : ℤ))
    (fun k : ℕ => dyadicWeight (k : ℤ) * θ (k : ℤ))
  have hL : ∀ k : ℕ,
      (dyadicWeight (k : ℤ) * u (k : ℤ)) * (dyadicWeight (k : ℤ) * θ (k : ℤ))
        = dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ) := by
    intro k
    rw [show (dyadicWeight (k : ℤ) * u (k : ℤ)) * (dyadicWeight (k : ℤ) * θ (k : ℤ))
          = (dyadicWeight (k : ℤ)) ^ 2 * (u (k : ℤ) * θ (k : ℤ)) by ring,
      ← dyadicWeight_two_mul]
    ring
  have hX : (∑ k ∈ Finset.range N, (dyadicWeight (k : ℤ) * u (k : ℤ)) ^ 2)
      = enstrophy u N := by
    rw [enstrophy]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow, ← dyadicWeight_two_mul]
  have hY : (∑ k ∈ Finset.range N, (dyadicWeight (k : ℤ) * θ (k : ℤ)) ^ 2)
      = tempEnstrophy θ N := by
    rw [tempEnstrophy]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow, ← dyadicWeight_two_mul]
  have hsq : (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ)) ^ 2
      ≤ enstrophy u N * tempEnstrophy θ N := by
    rw [Finset.sum_congr rfl (fun k _ => hL k), hX, hY] at hcs
    exact hcs
  calc (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ))
      ≤ Real.sqrt (enstrophy u N * tempEnstrophy θ N) := Real.le_sqrt_of_sq_le hsq
    _ = Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N) :=
        Real.sqrt_mul (enstrophy_nonneg u N) _

/-! ## 9. The headline pointwise enstrophy inequality -/

/-- **Headline pointwise enstrophy inequality.** Under the Dirichlet conditions
`u(-1) = u(N) = 0`, nonnegative `ν, κ` and `E = velocityEnergy u N > 0`, the enstrophy pairing
obeys

`∑_{k<N} 4^k u_k (du_k/dt) ≤ 3 H √H + κ √H √T − ν H²/E`,

with `H = enstrophy u N` and `T = tempEnstrophy θ N`. The transfer is cubic (`H^{3/2}`), the
buoyancy is `√H √T`, and viscosity dissipates at least `ν H²/E` by the interpolation
`H² ≤ (∑ 16^k u_k²) E`. This is the enstrophy analogue of `velocity_energy_rate_le`: the correct
sense in which "dissipation beats transfer" is `H^{3/2} ≪ H²/E`, i.e. `√H ≫ E`. -/
theorem enstrophy_pairing_le (ν κ : ℝ) (hκ : 0 ≤ κ) (hν : 0 ≤ ν) (u θ : ℤ → ℝ) (N : ℕ)
    (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0) (hE : 0 < velocityEnergy u N) :
    (∑ k ∈ Finset.range N,
        dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * dyadicVelocityRHS ν κ u θ (k : ℤ))
      ≤ 3 * (enstrophy u N * Real.sqrt (enstrophy u N))
        + κ * (Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N))
        - ν * (enstrophy u N) ^ 2 / velocityEnergy u N := by
  rw [enstrophy_pairing ν κ u θ N huBot huTop]
  have h1 := sum_vorticity_cubic_le u N huBot
  have h4 := buoyancy_enstrophy_le u θ N
  have h3 := enstrophy_sq_le_dissipation_mul_energy u N
  have hdiv : (enstrophy u N) ^ 2 / velocityEnergy u N
      ≤ ∑ k ∈ Finset.range N, dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2 := by
    rw [div_le_iff₀ hE]
    exact h3
  have h1' := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3)
  have h4' := mul_le_mul_of_nonneg_left h4 hκ
  have hν' : ν * (enstrophy u N) ^ 2 / velocityEnergy u N
      ≤ ν * (∑ k ∈ Finset.range N, dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hdiv hν
  linarith [h1', h4', hν']

/-! ## 10. Non-vacuity

The concrete state is `u_{-1}, u_0, u_1, u_2 = 0, 1, 3, 0` (zero elsewhere), i.e. `a_{-1}, a_0,
a_1, a_2 = 0, 1, 6, 0`, on the retained shells `0, 1` (`N = 2`). Its enstrophy is
`4^0 · 1² + 4^1 · 3² = 1 + 36 = 37`, and the cubic transfer sum is `a_{-1}²a_0 + a_0²a_1 = 6`.
Both sides of the enstrophy pairing identity (with `ν = κ = 0`, so that only the transfer
survives) evaluate to `3 · 6 = 18`, and the cubic bound reads `6 ≤ 37 √37`. -/

/-- The concrete velocity ladder `u = (0, 1, 3, 0)` on the shells `-1, 0, 1, 2`. -/
private def uEx : ℤ → ℝ :=
  fun k => if k = -1 then 0 else if k = 0 then 1 else if k = 1 then 3 else if k = 2 then 0 else 0

/-- The concrete temperature ladder `θ = (0, 1, 2, 0)` on the shells `-1, 0, 1, 2`. -/
private def θEx : ℤ → ℝ :=
  fun k => if k = -1 then 0 else if k = 0 then 1 else if k = 1 then 2 else if k = 2 then 0 else 0

/-- Concrete enstrophy: `4^0 · 1² + 4^1 · 3² = 37`. -/
example : enstrophy uEx 2 = 37 := by
  norm_num [enstrophy, Finset.sum_range_succ, Finset.sum_range_zero, uEx, dyadicWeight]

/-- Concrete temperature enstrophy: `4^0 · 1² + 4^1 · 2² = 17`. -/
example : tempEnstrophy θEx 2 = 17 := by
  norm_num [tempEnstrophy, Finset.sum_range_succ, Finset.sum_range_zero, θEx, dyadicWeight]

/-- The vorticity amplitude of the concrete state: `a = (0, 1, 6, 0)`. -/
example : vorticity uEx 0 = 1 ∧ vorticity uEx 1 = 6 := by
  constructor <;> norm_num [vorticity, uEx, dyadicWeight]

/-- The left-hand side of the enstrophy pairing identity at the concrete state with
`ν = κ = 0`: it equals the weighted pairing of the transfer, `18`. -/
example :
    (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uEx (k : ℤ)
        * dyadicVelocityRHS 0 0 uEx θEx (k : ℤ)) = 18 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uEx, θEx, dyadicVelocityRHS,
    generalVelocityRHS, boussinesqTransferU, dyadicWeight]

/-- The transfer sum on the right-hand side of the identity at the concrete state:
`a_{-1}²a_0 + a_0²a_1 = 6`, hence `3 · 6 = 18`. -/
example :
    3 * (∑ k ∈ Finset.range 2, (vorticity uEx ((k : ℤ) - 1)) ^ 2 * vorticity uEx (k : ℤ))
      = 18 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uEx, vorticity, dyadicWeight]

/-- **`18 = 18`**: the enstrophy pairing identity at the concrete state, both sides finite and
equal. -/
example :
    (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uEx (k : ℤ)
        * dyadicVelocityRHS 0 0 uEx θEx (k : ℤ))
      = 3 * (∑ k ∈ Finset.range 2, (vorticity uEx ((k : ℤ) - 1)) ^ 2 * vorticity uEx (k : ℤ))
        + 0 * (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uEx (k : ℤ) * θEx (k : ℤ))
        - 0 * (∑ k ∈ Finset.range 2, dyadicWeight (4 * (k : ℤ)) * (uEx (k : ℤ)) ^ 2) :=
  enstrophy_pairing 0 0 uEx θEx 2 (by norm_num [uEx]) (by norm_num [uEx])

/-- Numerically at the concrete state, the cubic transfer sum `6` is below `H √H = 37 √37`. -/
example :
    (∑ k ∈ Finset.range 2, (vorticity uEx ((k : ℤ) - 1)) ^ 2 * vorticity uEx (k : ℤ))
      ≤ enstrophy uEx 2 * Real.sqrt (enstrophy uEx 2) :=
  sum_vorticity_cubic_le uEx 2 (by norm_num [uEx])

/-- The numerical content of the previous example: `6 ≤ 37 √37`. -/
example : (6 : ℝ) ≤ 37 * Real.sqrt 37 := by
  have h6 : (6 : ℝ) ≤ Real.sqrt 37 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  nlinarith [h6]

/-- The full enstrophy pairing identity at the concrete state with `ν = κ = 1`: the transfer
`18`, buoyancy `25` and dissipation `∑ 16^k u_k² = 1 + 144 = 145` give `18 + 25 − 145 = -102`. -/
example :
    (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uEx (k : ℤ)
        * dyadicVelocityRHS 1 1 uEx θEx (k : ℤ)) = -102 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uEx, θEx, dyadicVelocityRHS,
    generalVelocityRHS, boussinesqTransferU, dyadicWeight]

/-- The headline enstrophy inequality at the concrete state is not vacuous: both sides are
finite and the left-hand side is strictly below the right-hand side (`-102 < 3·37√37 + √37√17 −
37²/10`). -/
example :
    (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uEx (k : ℤ)
        * dyadicVelocityRHS 1 1 uEx θEx (k : ℤ))
      ≤ 3 * (enstrophy uEx 2 * Real.sqrt (enstrophy uEx 2))
        + 1 * (Real.sqrt (enstrophy uEx 2) * Real.sqrt (tempEnstrophy θEx 2))
        - 1 * (enstrophy uEx 2) ^ 2 / velocityEnergy uEx 2 :=
  enstrophy_pairing_le 1 1 (by norm_num) (by norm_num) uEx θEx 2
    (by norm_num [uEx]) (by norm_num [uEx])
    (by norm_num [velocityEnergy, Finset.sum_range_succ, Finset.sum_range_zero, uEx])

end Cascade

/-! ## Axiom audit -/

#print axioms Cascade.enstrophy
#print axioms Cascade.tempEnstrophy
#print axioms Cascade.vorticity
#print axioms Cascade.enstrophyFlux
#print axioms Cascade.dyadicWeight_add
#print axioms Cascade.dyadicWeight_mul_int
#print axioms Cascade.dyadicWeight_two_mul
#print axioms Cascade.dyadicWeight_three_mul
#print axioms Cascade.dyadicWeight_three_mul_succ
#print axioms Cascade.dyadicWeight_four_mul
#print axioms Cascade.dyadicWeight_neg_one
#print axioms Cascade.dyadicWeight_pos
#print axioms Cascade.dyadicWeight_nonneg
#print axioms Cascade.vorticity_sq
#print axioms Cascade.vorticity_neg_one
#print axioms Cascade.enstrophy_nonneg
#print axioms Cascade.tempEnstrophy_nonneg
#print axioms Cascade.transfer_enstrophy_pointwise
#print axioms Cascade.sum_transfer_enstrophy
#print axioms Cascade.enstrophy_pairing
#print axioms Cascade.sum_vorticity_cubic_le
#print axioms Cascade.enstrophy_sq_le_dissipation_mul_energy
#print axioms Cascade.buoyancy_enstrophy_le
#print axioms Cascade.enstrophy_pairing_le
