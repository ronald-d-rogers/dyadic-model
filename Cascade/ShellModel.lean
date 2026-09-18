import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

/-!
# Stage S — the dyadic shell model

The dyadic shell model: one (real) amplitude `u_k` per frequency octave `[2ᵏ, 2ᵏ⁺¹)`,
with an energy-conserving nonlinear coupling `C_k` and viscosity `ν · 2^{2k}`:

    du_k / dt  =  C_k(u)  −  ν · 2^{2k} · u_k.

* **Energy identity:** if the coupling conserves energy (`Σ u_k C_k = 0`), then the
  energy `E = Σ u_k²` dissipates exactly at the viscous rate `−2ν Σ 2^{2k} u_k²`.
* **The obstruction:** Pillar A's Bernstein gives an unforced lacunary cascade a transfer
  rate `O(N^{3/2})` (the `d = 3` exponent `N^{d/2}` of `Cascade.bernstein_L2_to_Linf`),
  while dissipation is `O(N²)`. For `N ≥ 1`, `N^{3/2} ≤ N²`, so dissipation dominates and
  the cascade cannot self-sustain.

This is a *finite* (truncated) shell model, so the identities are pure finite sums.

Originally Pillar D of the `Criticality` skeleton; moved here because a cascade model is a
*model*, not a criticality theorem. The one-species specialisation of stage R.
-/

noncomputable section

namespace Cascade

/-- The right-hand side of the `k`-th shell ODE: coupling `C_k` minus viscous
dissipation `ν · 2^{2k} · u_k`. -/
def shellRHS (ν : ℝ) (C : ℕ → ℝ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  C k - ν * (2 : ℝ) ^ (2 * k) * u k

/-- **Energy identity (stage S).** For an energy-conserving coupling
(`Σ_{k<n} u_k · C_k = 0`), the pairing of the velocity with its time derivative is
exactly the (negative) viscous dissipation:
`Σ_k u_k · (du_k/dt) = −ν · Σ_k 2^{2k} u_k²`.

The full energy balance is `dE/dt = 2 · (that pairing) = −2ν Σ 2^{2k} u_k²`. -/
theorem shell_energy_identity (ν : ℝ) (C : ℕ → ℝ) (u : ℕ → ℝ) (n : ℕ)
    (hC : (Finset.sum (Finset.range n) (fun k => u k * C k)) = 0) :
    (Finset.sum (Finset.range n) (fun k => u k * shellRHS ν C u k))
      = -ν * (Finset.sum (Finset.range n) (fun k => (2 : ℝ) ^ (2 * k) * (u k) ^ 2)) := by
  calc
    (Finset.sum (Finset.range n) (fun k => u k * shellRHS ν C u k))
        = (Finset.sum (Finset.range n) (fun k => u k * (C k - ν * (2 : ℝ) ^ (2 * k) * u k))) := by
            simp [shellRHS]
    _ = (Finset.sum (Finset.range n) (fun k => u k * C k - ν * (2 : ℝ) ^ (2 * k) * (u k) ^ 2)) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = (Finset.sum (Finset.range n) (fun k => u k * C k)) -
          (Finset.sum (Finset.range n) (fun k => ν * (2 : ℝ) ^ (2 * k) * (u k) ^ 2)) := by
            rw [Finset.sum_sub_distrib]
    _ = 0 - ν * (Finset.sum (Finset.range n) (fun k => (2 : ℝ) ^ (2 * k) * (u k) ^ 2)) := by
            rw [hC]
            simp [Finset.mul_sum, mul_assoc]
    _ = -ν * (Finset.sum (Finset.range n) (fun k => (2 : ℝ) ^ (2 * k) * (u k) ^ 2)) := by
            ring

/-- **Dissipation dominates transfer (stage S).** For a frequency octave of
scale `N ≥ 1`, the Bernstein transfer rate `N^{3/2}` (Pillar A, `d = 3`) is dominated by
the viscous dissipation rate `N²`. Their ratio `N^{3/2} / N² = N^{-1/2} → 0` as `N → ∞`,
so an unforced cascade cannot self-sustain. -/
theorem transfer_le_dissipation (N : ℝ) (hN : 1 ≤ N) :
    N ^ ((3 : ℝ) / 2) ≤ N ^ (2 : ℝ) := by
  refine Real.rpow_le_rpow_of_exponent_le hN ?_
  norm_num

end Cascade

#print axioms Cascade.shell_energy_identity
#print axioms Cascade.transfer_le_dissipation
