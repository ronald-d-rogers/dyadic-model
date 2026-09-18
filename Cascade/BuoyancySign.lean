import Cascade.ForcedModel
import Cascade.EnstrophyBound

/-!
# Stage R″ — the sign of the buoyancy coupling is not load-bearing

Every no-blowup theorem in this library (`Cascade/Obstruction.lean`, `Cascade/NoBlowup.lean`,
`Cascade/Enstrophy.lean`, `Cascade/EnstrophyBound.lean`, `Cascade/ForcedModel.lean`) carries the
hypothesis `0 ≤ κ` on the buoyancy coupling `κ` (the term `+ κ θ_k` in the velocity equation).
The hypothesis enters the proofs at exactly one step: pushing the Cauchy–Schwarz bound
`∑ u_k θ_k ≤ √E √S` through the *sign* of `κ` (a `mul_le_mul_of_nonneg_left`).

That step is a **statement artifact**, not mathematics.  This file replaces it everywhere by the
sign-free estimate

`κ · ∑ u_k θ_k ≤ |κ| · √E · √S`,

which follows from `κ x ≤ |κ| |x|` together with the two-sided Cauchy–Schwarz bound.  With `|κ|`
in place of `κ`, every no-blowup argument goes through verbatim: `|κ| ≥ 0`, so the logistic
Grönwall engine, the Young absorptions and the enstrophy barrier apply unchanged.  The physical
consequence is the answer to the question motivating this file:

**unstable stratification (`κ < 0`) does *not* produce a finite-time blowup in the frozen truncated
dyadic Boussinesq model.**  Dissipation is a quadratic (in `H`) sink, the buoyancy source is
linear in the amplitudes (`√E` in the energy budget) resp. of homogeneity `1/2` in `H` in the
enstrophy budget, and the sign of `κ` only ever changes which side of the Cauchy–Schwarz bound the
buoyancy lands on — never its magnitude.

## Contents

1. `buoyancy_energy_le_abs`, `buoyancy_enstrophy_le_abs` — the sign-free Cauchy–Schwarz bounds.
2. `velocity_energy_pairing_le_abs`, `velocity_energy_rate_le_of_solution_abs`,
   `truncated_unforced_energy_bounded_abs`, `truncated_unforced_energy_le_max_abs` — unforced
   energy, for **arbitrary** `κ`.
3. `forced_velocity_pairing_le_abs`, `forced_energy_rate_le_abs`,
   `forced_energy_rate_le_of_entropy_le_abs`, `forced_truncated_energy_bounded_abs`,
   `forced_energy_le_max_unforced_temperature_abs` — forced energy, for **arbitrary** `κ`.
4. `enstrophy_pairing_le_abs`, `enstrophyLyapunov_deriv_le_abs`,
   `truncated_unforced_enstrophy_bounded_abs` — unforced enstrophy, for **arbitrary** `κ`.
5. `forced_enstrophy_rate_le_abs`, `forced_truncated_enstrophy_bounded_abs` — forced enstrophy,
   for **arbitrary** `κ`.
6. Non-vacuity: concrete states with `κ = -1 < 0` **and** `κ = 1 > 0` at which the rate
   inequalities are evaluated numerically and are strict.

## The Stage-O′ Lyapunov bookkeeping, for either sign

The identity behind `enstrophyLyapunov` (`Ψ = H + (κ/2μ) S`, `S = entropy θ N`) is sign-free: the
buoyancy source `+κ T` and the sink `(κ/2μ)·S' = (κ/2μ)·(-2μ T) = -κ T` cancel for *either* sign
of `κ`.  What depends on the sign is only the bookkeeping that recovers `H` from `Ψ`:

* for `κ ≥ 0`, `Ψ ≥ H` (the correction `(κ/2μ) S` is nonnegative), so bounding `Ψ` bounds `H`;
* for `κ < 0`, `H = Ψ - (κ/2μ) S = Ψ + (|κ|/2μ) S ≤ Ψ + (|κ|/2μ) S(0)`, using that `S` is
  non-increasing (`Cascade.entropy_antitone`).

Both are instances of the uniform inequality `H ≤ Ψ + (|κ|/(2μ))·S(0)` proved below; the extra
term is the constant `(|κ| - κ)·T_max` that appears in `enstrophyLyapunov_deriv_le_abs` and
vanishes exactly when `κ ≥ 0`.  No sign hypothesis survives anywhere.
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators

namespace Cascade

/-! ## 1. Phase 1 — general-sign buoyancy bounds -/

/-- **Two-sided Cauchy–Schwarz (generic finset).** `|∑ u_k θ_k| ≤ √(∑ u_k²) √(∑ θ_k²)`.
The upper half is `force_work_le`'s helper `sum_mul_le_sqrt_mul_sqrt'`; the lower half is the same
estimate applied to `-u`, which has the same `ℓ²` norm. -/
theorem abs_sum_mul_le_sqrt_mul_sqrt {ι : Type*} (s : Finset ι) (u θ : ι → ℝ) :
    |∑ k ∈ s, u k * θ k|
      ≤ Real.sqrt (∑ k ∈ s, (u k) ^ 2) * Real.sqrt (∑ k ∈ s, (θ k) ^ 2) := by
  have hle : (∑ k ∈ s, u k * θ k)
      ≤ Real.sqrt (∑ k ∈ s, (u k) ^ 2) * Real.sqrt (∑ k ∈ s, (θ k) ^ 2) :=
    sum_mul_le_sqrt_mul_sqrt' s u θ
  have hge : -(∑ k ∈ s, u k * θ k)
      ≤ Real.sqrt (∑ k ∈ s, (u k) ^ 2) * Real.sqrt (∑ k ∈ s, (θ k) ^ 2) := by
    have h := sum_mul_le_sqrt_mul_sqrt' s (fun k => -u k) θ
    simpa only [neg_mul, Finset.sum_neg_distrib, neg_sq] using h
  exact abs_le.mpr ⟨neg_le.mp hge, hle⟩

/-- The enstrophy is invariant under negating the ladder. -/
theorem enstrophy_neg (u : ℤ → ℝ) (N : ℕ) :
    enstrophy (fun k => -u k) N = enstrophy u N := by
  rw [enstrophy, enstrophy]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The temperature enstrophy is invariant under negating the ladder. -/
theorem tempEnstrophy_neg (θ : ℤ → ℝ) (N : ℕ) :
    tempEnstrophy (fun k => -θ k) N = tempEnstrophy θ N := by
  rw [tempEnstrophy, tempEnstrophy]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Phase 1a: sign-free buoyancy bound in the energy norm.** For *any* real `κ`,

`κ · ∑_{k<N} u_k θ_k ≤ |κ| · √(velocityEnergy u N) · √(entropy θ N)`.

This is the replacement for the `κ ≥ 0` step of `velocity_energy_rate_le`: the sign of `κ` only
decides whether the Cauchy–Schwarz bound is applied to `u` or to `-u`, and `|κ|` handles both. -/
theorem buoyancy_energy_le_abs (κ : ℝ) (u θ : ℤ → ℝ) (N : ℕ) :
    κ * (∑ k ∈ Finset.range N, u (k : ℤ) * θ (k : ℤ))
      ≤ |κ| * (Real.sqrt (velocityEnergy u N) * Real.sqrt (entropy θ N)) := by
  have habs : |∑ k ∈ Finset.range N, u (k : ℤ) * θ (k : ℤ)|
      ≤ Real.sqrt (velocityEnergy u N) * Real.sqrt (entropy θ N) := by
    have h := abs_sum_mul_le_sqrt_mul_sqrt (Finset.range N)
      (fun k : ℕ => u (k : ℤ)) (fun k : ℕ => θ (k : ℤ))
    simpa only [velocityEnergy, entropy] using h
  calc κ * (∑ k ∈ Finset.range N, u (k : ℤ) * θ (k : ℤ))
      ≤ |κ * (∑ k ∈ Finset.range N, u (k : ℤ) * θ (k : ℤ))| := le_abs_self _
    _ = |κ| * |∑ k ∈ Finset.range N, u (k : ℤ) * θ (k : ℤ)| := abs_mul κ _
    _ ≤ |κ| * (Real.sqrt (velocityEnergy u N) * Real.sqrt (entropy θ N)) :=
        mul_le_mul_of_nonneg_left habs (abs_nonneg κ)

/-- **Phase 1b: sign-free buoyancy bound in the enstrophy norm.** For *any* real `κ`,

`κ · ∑_{k<N} 4^k u_k θ_k ≤ |κ| · √(enstrophy u N) · √(tempEnstrophy θ N)`.

This is the replacement for the `κ ≥ 0` step of `enstrophy_pairing_le` and of
`forced_enstrophy_rate_le`. -/
theorem buoyancy_enstrophy_le_abs (κ : ℝ) (u θ : ℤ → ℝ) (N : ℕ) :
    κ * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ))
      ≤ |κ| * (Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N)) := by
  have hle : (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ))
      ≤ Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N) :=
    buoyancy_enstrophy_le u θ N
  have hge : -(∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ))
      ≤ Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N) := by
    have h := buoyancy_enstrophy_le (fun k => -u k) θ N
    rw [enstrophy_neg] at h
    have hcongr : (∑ k ∈ Finset.range N,
          dyadicWeight (2 * (k : ℤ)) * (-u (k : ℤ)) * θ (k : ℤ))
        = -(∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rwa [hcongr] at h
  have habs : |∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ)|
      ≤ Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N) :=
    abs_le.mpr ⟨neg_le.mp hge, hle⟩
  calc κ * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ))
      ≤ |κ * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ))| :=
        le_abs_self _
    _ = |κ| * |∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ)| :=
        abs_mul κ _
    _ ≤ |κ| * (Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N)) :=
        mul_le_mul_of_nonneg_left habs (abs_nonneg κ)

/-! ## 2. Phase 2 — energy: no finite-time blowup for any sign of `κ`

The energy pairing of the velocity equation is the buoyancy plus (in the forced case) the force
work minus the viscous dissipation; the sign-free buoyancy bound of Phase 1 replaces the
`κ ≥ 0` step of `velocity_energy_rate_le` with no other change.  Since the logistic Grönwall
engine `Cascade.no_finite_time_blowup` only ever asks for a *nonnegative* coefficient
`|κ| √S + √F`, the whole Stage-O chain transfers. -/

/-- The velocity energy flux at the bottom boundary vanishes under `u(-1) = 0`. -/
theorem dyadicVelocityFlux_bot_zero (u : ℤ → ℝ) (h : u (-1) = 0) :
    dyadicVelocityFlux u 0 = 0 := by
  simp [dyadicVelocityFlux, velocityFlux, h]

/-- The velocity energy flux at the top boundary vanishes under `u(n) = 0`. -/
theorem dyadicVelocityFlux_top_zero (u : ℤ → ℝ) (n : ℕ) (h : u (n : ℤ) = 0) :
    dyadicVelocityFlux u (n : ℤ) = 0 := by
  simp [dyadicVelocityFlux, velocityFlux, h]

/-- On the physical shells `k ≥ 0` the viscous weight `2^{2k}` is at least `1`, hence
`∑ u_k² ≤ ∑ 2^{2k} u_k²`.  (Reproof of the private helper of `Cascade/Obstruction.lean`.) -/
theorem sum_sq_le_sum_weighted_sq (u : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (u (k : ℤ)) ^ 2)
      ≤ ∑ k ∈ Finset.range n, dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2 := by
  apply Finset.sum_le_sum
  intro k _
  have h2k : (0 : ℤ) ≤ 2 * (k : ℤ) := by
    have : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    linarith
  have h1 : (1 : ℝ) ≤ dyadicWeight (2 * (k : ℤ)) := by
    unfold dyadicWeight
    exact one_le_zpow₀ (by norm_num : (1 : ℝ) ≤ 2) h2k
  calc (u (k : ℤ)) ^ 2 = (u (k : ℤ)) ^ 2 * 1 := (mul_one _).symm
    _ ≤ (u (k : ℤ)) ^ 2 * dyadicWeight (2 * (k : ℤ)) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = dyadicWeight (2 * (k : ℤ)) * (u (k : ℤ)) ^ 2 := mul_comm _ _

/-- **Phase 2a: the sign-free velocity energy pairing bound.**  Under the Dirichlet conditions,
for *any* real `κ`,

`∑_{k<n} u_k (du_k/dt) ≤ |κ| √E √S − ν E`.

The transfer still cancels exactly, the buoyancy is bounded by Phase 1, and the viscous weight
bound is unchanged. -/
theorem velocity_energy_pairing_le_abs (ν κ : ℝ) (hν : 0 ≤ ν) (u θ : ℤ → ℝ) (n : ℕ)
    (hbot : u (-1) = 0) (htop : u (n : ℤ) = 0) :
    (∑ k ∈ Finset.range n, u (k : ℤ) * dyadicVelocityRHS ν κ u θ (k : ℤ))
      ≤ |κ| * (Real.sqrt (velocityEnergy u n) * Real.sqrt (entropy θ n))
        - ν * velocityEnergy u n := by
  rw [dyadic_velocity_energy_identity ν κ u θ n,
    dyadicVelocityFlux_bot_zero u hbot, dyadicVelocityFlux_top_zero u n htop]
  have hCS := buoyancy_energy_le_abs κ u θ n
  have hW := sum_sq_le_sum_weighted_sq u n
  have hνW := mul_le_mul_of_nonneg_left hW hν
  simp only [velocityEnergy, entropy] at hCS ⊢
  linarith

/-- **Phase 2b: the sign-free closed Grönwall rate inequality for the unforced velocity
energy.**  For *any* real `κ`, using that the entropy is non-increasing (`hanti`),

`E' ≤ 2 |κ| √S(0) √E − 2 ν E`.

This is `velocity_energy_rate_le_of_solution` with `|κ|` in place of `κ`; the only place the sign
of `κ` was used (pushing `√S(t) ≤ √S(0)` through the buoyancy coefficient) now uses
`|κ| ≥ 0`. -/
theorem velocity_energy_rate_le_of_solution_abs (ν μ κ : ℝ) (hν : 0 ≤ ν)
    (N : ℕ) (u θ : ℝ → ℤ → ℝ) (h : IsUnforcedTruncatedSolution ν μ κ N u θ)
    (hanti : Antitone fun t => entropy (θ t) N) {t : ℝ} (ht : 0 ≤ t) :
    2 * (∑ k ∈ Finset.range N, u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))
      ≤ 2 * |κ| * Real.sqrt (entropy (θ 0) N) * Real.sqrt (velocityEnergy (u t) N)
        - 2 * ν * velocityEnergy (u t) N := by
  have hpair := velocity_energy_pairing_le_abs ν κ hν (u t) (θ t) N
    (h.2.2 t).1 (h.2.2 t).2.1
  have hSle : entropy (θ t) N ≤ entropy (θ 0) N := hanti ht
  have hsq : Real.sqrt (entropy (θ t) N) ≤ Real.sqrt (entropy (θ 0) N) := Real.sqrt_le_sqrt hSle
  have hcoef : 0 ≤ 2 * |κ| * Real.sqrt (velocityEnergy (u t) N) :=
    mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg κ)) (Real.sqrt_nonneg _)
  have h2 : 2 * (∑ k ∈ Finset.range N,
        u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))
      ≤ 2 * (|κ| * (Real.sqrt (velocityEnergy (u t) N) * Real.sqrt (entropy (θ t) N))
            - ν * velocityEnergy (u t) N) :=
    mul_le_mul_of_nonneg_left hpair (by norm_num)
  have hstep := mul_le_mul_of_nonneg_left hsq hcoef
  simp only [velocityEnergy, entropy] at h2 hstep ⊢
  nlinarith [h2, hstep]

/-- **Phase 2c: no finite-time unforced energy blowup, for *any* real `κ`.**  Along any unforced
truncated solution with Dirichlet ends, the velocity energy is bounded on every compact time
interval `[0, T]`.  This drops the hypothesis `0 ≤ κ` from
`truncated_unforced_energy_bounded`; the Grönwall engine is applied with the nonnegative
coefficient `|κ|`. -/
theorem truncated_unforced_energy_bounded_abs (ν μ κ : ℝ) (hν : 0 < ν) (hμ : 0 ≤ μ)
    (N : ℕ) (u θ : ℝ → ℤ → ℝ) (h : IsUnforcedTruncatedSolution ν μ κ N u θ)
    {T : ℝ} (hcont : ContinuousOn (fun t => velocityEnergy (u t) N) (Set.Icc 0 T))
    (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, velocityEnergy (u t) N ≤ C := by
  have hanti : Antitone fun t => entropy (θ t) N := entropy_antitone ν μ κ hμ N u θ h
  refine no_finite_time_blowup (E := fun t => velocityEnergy (u t) N)
    (E' := fun t => 2 * ∑ k ∈ Finset.range N,
      u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))
    (S₀ := entropy (θ 0) N) (κ := |κ|) (abs_nonneg κ) (entropy_nonneg (θ 0) N) hν ?_ ?_ ?_ ?_
    T hT
  · exact (velocityEnergy_hasDerivAt ν μ κ N u θ h 0).continuousAt
  · intro t _
    exact velocityEnergy_nonneg (u t) N
  · intro t _
    exact velocityEnergy_hasDerivAt ν μ κ N u θ h t
  · intro t ht
    exact velocity_energy_rate_le_of_solution_abs ν μ κ hν.le N u θ h hanti (le_of_lt ht)

/-- **Phase 2d: the uniform-in-time unforced energy bound, for *any* real `κ`.**  If additionally
the dissipation gap `2ν > |κ| √S(0)` holds then

`E(t) ≤ max (E(0)) (|κ| √S(0) / (2ν − |κ| √S(0)))`  for all `t ≥ 0`,

an explicit constant independent of `T`.  This drops `0 ≤ κ` from
`truncated_unforced_energy_le_max`. -/
theorem truncated_unforced_energy_le_max_abs (ν μ κ : ℝ) (hν : 0 < ν) (hμ : 0 ≤ μ)
    (N : ℕ) (u θ : ℝ → ℤ → ℝ) (h : IsUnforcedTruncatedSolution ν μ κ N u θ)
    {T : ℝ} (hcont : ContinuousOn (fun t => velocityEnergy (u t) N) (Set.Icc 0 T))
    (hgap : 0 < 2 * ν - |κ| * Real.sqrt (entropy (θ 0) N)) (hT : 0 ≤ T) :
    ∀ t ∈ Set.Icc 0 T,
      velocityEnergy (u t) N ≤ max (velocityEnergy (u 0) N)
        (|κ| * Real.sqrt (entropy (θ 0) N)
          / (2 * ν - |κ| * Real.sqrt (entropy (θ 0) N))) := by
  have hanti : Antitone fun t => entropy (θ t) N := entropy_antitone ν μ κ hμ N u θ h
  refine energy_le_max_of_rate_le (S₀ := entropy (θ 0) N) (κ := |κ|)
    (E' := fun t => 2 * ∑ k ∈ Finset.range N,
      u t (k : ℤ) * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))
    (abs_nonneg κ) (entropy_nonneg (θ 0) N) hν hgap hcont ?_ ?_ ?_
  · intro t _
    exact velocityEnergy_nonneg (u t) N
  · intro t _
    exact velocityEnergy_hasDerivAt ν μ κ N u θ h t
  · intro t ht
    exact velocity_energy_rate_le_of_solution_abs ν μ κ hν.le N u θ h hanti ht.1

/-! ### Phase 2, forced case -/

/-- **Phase 2e: the sign-free forced velocity energy pairing bound.**  For *any* real `κ`,

`∑_{k<N} u_k (du_k/dt) ≤ |κ| √E √S + √E √F − ν E`.

This is `forced_velocity_pairing_le` with `|κ|` in place of `κ`. -/
theorem forced_velocity_pairing_le_abs (ν κ : ℝ) (hν : 0 ≤ ν) (f : ℤ → ℝ)
    (u θ : ℤ → ℝ) (N : ℕ) (hbot : u (-1) = 0) (htop : u (N : ℤ) = 0) :
    (∑ k ∈ Finset.range N, u (k : ℤ) * forcedVelocityRHS ν κ f u θ (k : ℤ))
      ≤ |κ| * (Real.sqrt (velocityEnergy u N) * Real.sqrt (entropy θ N))
        + Real.sqrt (velocityEnergy u N) * Real.sqrt (forceEnergy f N)
        - ν * velocityEnergy u N := by
  have hsplit : (∑ k ∈ Finset.range N, u (k : ℤ) * forcedVelocityRHS ν κ f u θ (k : ℤ))
      = (∑ k ∈ Finset.range N, u (k : ℤ) * dyadicVelocityRHS ν κ u θ (k : ℤ))
        + (∑ k ∈ Finset.range N, u (k : ℤ) * f (k : ℤ)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by simp only [forcedVelocityRHS, mul_add]
  rw [hsplit]
  have h1 := velocity_energy_pairing_le_abs ν κ hν u θ N hbot htop
  have h2 := force_work_le f u N
  simp only [velocityEnergy, entropy, forceEnergy] at h1 h2 ⊢
  linarith

/-- **Phase 2f: the sign-free forced logistic energy rate inequality.**  Along a forced truncated
solution, for *any* real `κ`,

`E' ≤ 2 (|κ| √S(t) + √F) √E − 2 ν E`.

This is `forced_energy_rate_le` with `|κ|`; the entropy is still evaluated at the current time,
because a temperature force destroys its monotonicity. -/
theorem forced_energy_rate_le_abs (ν μ κ : ℝ) (hν : 0 ≤ ν)
    (N : ℕ) (f h : ℤ → ℝ) (u θ : ℝ → ℤ → ℝ)
    (hsol : IsForcedTruncatedSolution ν μ κ N f h u θ) (t : ℝ) :
    2 * (∑ k ∈ Finset.range N,
        u t (k : ℤ) * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ))
      ≤ 2 * (|κ| * Real.sqrt (entropy (θ t) N) + Real.sqrt (forceEnergy f N))
          * Real.sqrt (velocityEnergy (u t) N)
        - 2 * ν * velocityEnergy (u t) N := by
  have hpair := forced_velocity_pairing_le_abs ν κ hν f (u t) (θ t) N
    (hsol.2.2 t).1 (hsol.2.2 t).2.1
  have h2 : 2 * (∑ k ∈ Finset.range N,
        u t (k : ℤ) * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ))
      ≤ 2 * (|κ| * (Real.sqrt (velocityEnergy (u t) N) * Real.sqrt (entropy (θ t) N))
        + Real.sqrt (velocityEnergy (u t) N) * Real.sqrt (forceEnergy f N)
        - ν * velocityEnergy (u t) N) :=
    mul_le_mul_of_nonneg_left hpair (by norm_num)
  nlinarith [h2]

/-- **Phase 2g: the sign-free forced energy rate inequality with an entropy ceiling.**  For *any*
real `κ`, if `S(t) ≤ S_max` then

`E' ≤ 2 (|κ| √S_max + √F) √E − 2 ν E`,

the form fed to the Grönwall engine.  This is `forced_energy_rate_le_of_entropy_le` with `|κ|`. -/
theorem forced_energy_rate_le_of_entropy_le_abs (ν μ κ : ℝ) (hν : 0 ≤ ν)
    (N : ℕ) (f h : ℤ → ℝ) (u θ : ℝ → ℤ → ℝ)
    (hsol : IsForcedTruncatedSolution ν μ κ N f h u θ) {t S_max : ℝ}
    (hS : entropy (θ t) N ≤ S_max) :
    2 * (∑ k ∈ Finset.range N,
        u t (k : ℤ) * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ))
      ≤ 2 * (|κ| * Real.sqrt S_max + Real.sqrt (forceEnergy f N))
          * Real.sqrt (velocityEnergy (u t) N)
        - 2 * ν * velocityEnergy (u t) N := by
  have hrate := forced_energy_rate_le_abs ν μ κ hν N f h u θ hsol t
  have hsqrt : Real.sqrt (entropy (θ t) N) ≤ Real.sqrt S_max := Real.sqrt_le_sqrt hS
  have hcoef : |κ| * Real.sqrt (entropy (θ t) N) ≤ |κ| * Real.sqrt S_max :=
    mul_le_mul_of_nonneg_left hsqrt (abs_nonneg κ)
  have hcoef' : |κ| * Real.sqrt (entropy (θ t) N) + Real.sqrt (forceEnergy f N)
      ≤ |κ| * Real.sqrt S_max + Real.sqrt (forceEnergy f N) := by linarith
  have hE : 0 ≤ Real.sqrt (velocityEnergy (u t) N) := Real.sqrt_nonneg _
  have hstep : (|κ| * Real.sqrt (entropy (θ t) N) + Real.sqrt (forceEnergy f N))
        * Real.sqrt (velocityEnergy (u t) N)
      ≤ (|κ| * Real.sqrt S_max + Real.sqrt (forceEnergy f N))
        * Real.sqrt (velocityEnergy (u t) N) :=
    mul_le_mul_of_nonneg_right hcoef' hE
  nlinarith [hrate, hstep]

/-- **Phase 2h: no finite-time forced energy blowup, for *any* real `κ`.**  Along any forced
truncated solution with Dirichlet ends the velocity energy is bounded on every compact time
interval `[0, T]`.  This drops `0 ≤ κ` from `forced_truncated_energy_bounded`; the frozen
logistic coefficient is `|κ| √S_max + √F`, which is nonnegative for either sign of `κ`. -/
theorem forced_truncated_energy_bounded_abs (ν μ κ : ℝ) (hν : 0 < ν)
    (N : ℕ) (f h : ℤ → ℝ) (u θ : ℝ → ℤ → ℝ)
    (hsol : IsForcedTruncatedSolution ν μ κ N f h u θ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, velocityEnergy (u t) N ≤ C := by
  obtain ⟨S₀, hS₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).bddAbove_image
    (forcedEntropy_continuous ν μ κ N f h u θ hsol).continuousOn
  set S_max : ℝ := max S₀ 0 with hS_max
  have hS_max_nonneg : 0 ≤ S_max := le_max_right _ _
  have hSle : ∀ t ∈ Set.Icc 0 T, entropy (θ t) N ≤ S_max := fun t ht =>
    (hS₀ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  set A : ℝ := |κ| * Real.sqrt S_max + Real.sqrt (forceEnergy f N) with hA
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    exact add_nonneg (mul_nonneg (abs_nonneg κ) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  refine ⟨energyBound (velocityEnergy (u 0) N) A 1 ν T, ?_⟩
  refine energy_le_energyBound_of_rate_le (E := fun t => velocityEnergy (u t) N)
    (E' := fun t => 2 * ∑ k ∈ Finset.range N,
      u t (k : ℤ) * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ))
    (κ := A) (S₀ := 1) (ν := ν) (T := T) hA_nonneg (by norm_num) hν hT ?_ ?_ ?_ ?_
  · exact (forcedVelocityEnergy_continuous ν μ κ N f h u θ hsol).continuousOn
  · intro t _; exact velocityEnergy_nonneg (u t) N
  · intro t _
    exact forcedVelocityEnergy_hasDerivAt ν μ κ N f h u θ hsol t
  · intro t ht
    have hrate := forced_energy_rate_le_of_entropy_le_abs ν μ κ hν.le N f h u θ hsol
      (hSle t ⟨ht.1, le_of_lt ht.2⟩)
    simpa [hA, Real.sqrt_one] using hrate

/-- **Phase 2i: the uniform-in-time forced energy bound with unforced temperature, for *any* real
`κ`.**  For a velocity force `f`, no temperature force, and dissipation gap
`2ν > |κ| √S(0) + √F`, for all `t ≥ 0`

`E(t) ≤ max (E(0)) ((|κ| √S(0) + √F) / (2ν − |κ| √S(0) − √F))`.

This drops `0 ≤ κ` from `forced_energy_le_max_unforced_temperature`. -/
theorem forced_energy_le_max_unforced_temperature_abs (ν μ κ : ℝ) (hν : 0 < ν) (hμ : 0 ≤ μ)
    (N : ℕ) (f : ℤ → ℝ) (u θ : ℝ → ℤ → ℝ)
    (hsol : IsForcedTruncatedSolution ν μ κ N f 0 u θ)
    (hgap : 0 < 2 * ν - (|κ| * Real.sqrt (entropy (θ 0) N) + Real.sqrt (forceEnergy f N)))
    (t : ℝ) (ht : 0 ≤ t) :
    velocityEnergy (u t) N ≤ max (velocityEnergy (u 0) N)
      ((|κ| * Real.sqrt (entropy (θ 0) N) + Real.sqrt (forceEnergy f N))
        / (2 * ν - (|κ| * Real.sqrt (entropy (θ 0) N) + Real.sqrt (forceEnergy f N)))) := by
  have hanti := forced_entropy_antitone ν μ κ hμ N f u θ hsol
  set A : ℝ := |κ| * Real.sqrt (entropy (θ 0) N) + Real.sqrt (forceEnergy f N) with hA
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    exact add_nonneg (mul_nonneg (abs_nonneg κ) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hgap' : 0 < 2 * ν - A * Real.sqrt (1 : ℝ) := by
    rw [Real.sqrt_one, mul_one]; exact hgap
  have hmain : velocityEnergy (u t) N ≤ max (velocityEnergy (u 0) N)
      (A * Real.sqrt (1 : ℝ) / (2 * ν - A * Real.sqrt (1 : ℝ))) := by
    refine energy_le_max_of_rate_le (E := fun s => velocityEnergy (u s) N)
      (E' := fun s => 2 * ∑ k ∈ Finset.range N,
        u s (k : ℤ) * forcedVelocityRHS ν κ f (u s) (θ s) (k : ℤ))
      (κ := A) (S₀ := 1) (ν := ν) (T := t) hA_nonneg (by norm_num) hν hgap' ?_ ?_ ?_ ?_ t
      ⟨ht, le_rfl⟩
    · exact (forcedVelocityEnergy_continuous ν μ κ N f 0 u θ hsol).continuousOn
    · intro s _; exact velocityEnergy_nonneg (u s) N
    · intro s _
      exact forcedVelocityEnergy_hasDerivAt ν μ κ N f 0 u θ hsol s
    · intro s hs
      have hSle : entropy (θ s) N ≤ entropy (θ 0) N := hanti hs.1
      have hrate := forced_energy_rate_le_of_entropy_le_abs ν μ κ hν.le N f 0 u θ hsol hSle
      simpa [hA, Real.sqrt_one] using hrate
  simpa [hA, Real.sqrt_one] using hmain

/-! ## 3. Phase 3 — enstrophy: no finite-time blowup for any sign of `κ`

The enstrophy pairing is cubic (`3 H^{3/2}`), the buoyancy is sublinear (`√H √T`, homogeneity
`1/2`), the (forced) force work is sublinear (`2 √H √He`), and the viscous dissipation is
quadratic (`2 ν H²/E_max`, homogeneity `2`).  Above the barrier threshold the right-hand side is
negative, so `H` cannot cross it.  Replacing `κ` by `|κ|` costs one extra additive constant,
`(|κ| - κ) T_max`, which **vanishes exactly when `κ ≥ 0`**: that term is the entire bookkeeping
cost of unstable stratification in the Stage-O′ Lyapunov argument. -/

/-- **Phase 3a: the sign-free pointwise enstrophy pairing bound.**  Under the Dirichlet
conditions and `E = velocityEnergy u N > 0`, for *any* real `κ`,

`∑_{k<N} 4^k u_k (du_k/dt) ≤ 3 H √H + |κ| √H √T − ν H²/E`.

This is `enstrophy_pairing_le` with `|κ|` in place of `κ`. -/
theorem enstrophy_pairing_le_abs (ν κ : ℝ) (hν : 0 ≤ ν) (u θ : ℤ → ℝ) (N : ℕ)
    (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0) (hE : 0 < velocityEnergy u N) :
    (∑ k ∈ Finset.range N,
        dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * dyadicVelocityRHS ν κ u θ (k : ℤ))
      ≤ 3 * (enstrophy u N * Real.sqrt (enstrophy u N))
        + |κ| * (Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N))
        - ν * (enstrophy u N) ^ 2 / velocityEnergy u N := by
  rw [enstrophy_pairing ν κ u θ N huBot huTop]
  have h1 := sum_vorticity_cubic_le u N huBot
  have h4 := buoyancy_enstrophy_le_abs κ u θ N
  have h3 := enstrophy_sq_le_dissipation_mul_energy u N
  have hdiv : (enstrophy u N) ^ 2 / velocityEnergy u N
      ≤ ∑ k ∈ Finset.range N, dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2 := by
    rw [div_le_iff₀ hE]
    exact h3
  have h1' := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3)
  have hν' : ν * (enstrophy u N) ^ 2 / velocityEnergy u N
      ≤ ν * (∑ k ∈ Finset.range N, dyadicWeight (4 * (k : ℤ)) * (u (k : ℤ)) ^ 2) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hdiv hν
  linarith [h1', h4, hν']

/-- **Phase 3b: the sign-free pointwise enstrophy rate along an unforced solution.**  With
`H = enstrophy (u t) N`, `T = tempEnstrophy (θ t) N` and `E_max ≥ E(t)`, for *any* real `κ`,

`2 ∑_{k<N} 4^k u_k (du_k/dt) ≤ 6 H √H + |κ| (H + T) − 2 ν H²/E_max`.

This is `enstrophy_rate_le_of_solution` with `|κ|`; the degenerate case `E = 0` is handled as
there (a sum of squares vanishes only if every term does). -/
theorem enstrophy_rate_le_of_solution_abs (ν μ κ E_max : ℝ) (hν : 0 < ν)
    (hEpos : 0 < E_max) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolution ν μ κ N u θ) {t : ℝ}
    (hEmax : velocityEnergy (u t) N ≤ E_max) :
    2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
        * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))
      ≤ 6 * (enstrophy (u t) N * Real.sqrt (enstrophy (u t) N))
        + |κ| * (enstrophy (u t) N + tempEnstrophy (θ t) N)
        - 2 * ν * (enstrophy (u t) N) ^ 2 / E_max := by
  by_cases hE0 : velocityEnergy (u t) N = 0
  · have hsum0 : (∑ k ∈ Finset.range N, (u t (k : ℤ)) ^ 2) = 0 := by
      simpa [velocityEnergy] using hE0
    have hz : ∀ k ∈ Finset.range N, (u t (k : ℤ)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.range N)
        (f := fun j : ℕ => (u t (j : ℤ)) ^ 2)
        (fun j _ => sq_nonneg (u t (j : ℤ)))).mp hsum0
    have hu0 : ∀ k ∈ Finset.range N, u t (k : ℤ) = 0 := fun k hk =>
      sq_eq_zero_iff.mp (hz k hk)
    have hL : (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
        * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [hu0 k hk]
      ring
    have hH : enstrophy (u t) N = 0 := by
      rw [enstrophy]
      apply Finset.sum_eq_zero
      intro k hk
      rw [hu0 k hk]
      ring
    rw [hL, hH]
    have hrhs : 6 * ((0 : ℝ) * Real.sqrt 0) + |κ| * (0 + tempEnstrophy (θ t) N)
        - 2 * ν * (0 : ℝ) ^ 2 / E_max = |κ| * tempEnstrophy (θ t) N := by
      rw [Real.sqrt_zero]
      ring
    rw [hrhs]
    simpa using mul_nonneg (abs_nonneg κ) (tempEnstrophy_nonneg (θ t) N)
  · have hEpos' : 0 < velocityEnergy (u t) N :=
      lt_of_le_of_ne (velocityEnergy_nonneg (u t) N) (Ne.symm hE0)
    have hpair := enstrophy_pairing_le_abs ν κ hν.le (u t) (θ t) N
      (h.2.2 t).1 (h.2.2 t).2.1 hEpos'
    have h2 := mul_le_mul_of_nonneg_left hpair (by norm_num : (0 : ℝ) ≤ 2)
    have hHnn : 0 ≤ enstrophy (u t) N := enstrophy_nonneg _ _
    have hTEnn : 0 ≤ tempEnstrophy (θ t) N := tempEnstrophy_nonneg _ _
    have hamgm : 2 * (Real.sqrt (enstrophy (u t) N) * Real.sqrt (tempEnstrophy (θ t) N))
        ≤ enstrophy (u t) N + tempEnstrophy (θ t) N := by
      have h1 : (Real.sqrt (enstrophy (u t) N) - Real.sqrt (tempEnstrophy (θ t) N)) ^ 2
          = enstrophy (u t) N + tempEnstrophy (θ t) N
            - 2 * (Real.sqrt (enstrophy (u t) N) * Real.sqrt (tempEnstrophy (θ t) N)) := by
        rw [sub_sq, Real.sq_sqrt hHnn, Real.sq_sqrt hTEnn]
        ring
      nlinarith [sq_nonneg (Real.sqrt (enstrophy (u t) N)
        - Real.sqrt (tempEnstrophy (θ t) N))]
    have hκamgm : |κ| * (2 * (Real.sqrt (enstrophy (u t) N)
          * Real.sqrt (tempEnstrophy (θ t) N)))
        ≤ |κ| * (enstrophy (u t) N + tempEnstrophy (θ t) N) :=
      mul_le_mul_of_nonneg_left hamgm (abs_nonneg κ)
    have hdiv : (enstrophy (u t) N) ^ 2 / E_max
        ≤ (enstrophy (u t) N) ^ 2 / velocityEnergy (u t) N :=
      div_le_div_of_nonneg_left (sq_nonneg _) hEpos' hEmax
    have hνdiv : 2 * ν * (enstrophy (u t) N) ^ 2 / E_max
        ≤ 2 * ν * (enstrophy (u t) N) ^ 2 / velocityEnergy (u t) N := by
      have h2ν : 0 ≤ 2 * ν := by linarith
      have h := mul_le_mul_of_nonneg_left hdiv h2ν
      calc 2 * ν * (enstrophy (u t) N) ^ 2 / E_max
          = (2 * ν) * ((enstrophy (u t) N) ^ 2 / E_max) := by ring
        _ ≤ (2 * ν) * ((enstrophy (u t) N) ^ 2 / velocityEnergy (u t) N) := h
        _ = 2 * ν * (enstrophy (u t) N) ^ 2 / velocityEnergy (u t) N := by ring
    have hstep : 2 * (3 * (enstrophy (u t) N * Real.sqrt (enstrophy (u t) N))
          + |κ| * (Real.sqrt (enstrophy (u t) N) * Real.sqrt (tempEnstrophy (θ t) N))
          - ν * (enstrophy (u t) N) ^ 2 / velocityEnergy (u t) N)
        ≤ 6 * (enstrophy (u t) N * Real.sqrt (enstrophy (u t) N))
          + |κ| * (enstrophy (u t) N + tempEnstrophy (θ t) N)
          - 2 * ν * (enstrophy (u t) N) ^ 2 / E_max := by
      simp only [div_eq_mul_inv] at hνdiv ⊢
      linarith [hκamgm, hνdiv]
    exact h2.trans hstep

/-- **Phase 3c: the sign-free Stage-O′ Lyapunov derivative bound.**  For *any* real `κ`, with
`Ψ = enstrophyLyapunov ν μ κ N u θ = H + (κ/2μ) S`, `S = entropy θ N`,

`Ψ' ≤ enstrophyYoungConst ν κ E_max + (|κ| - κ) · T_max`.

The buoyancy source `+κ T` cancels the sink `(κ/2μ)·S' = -κT` for either sign (the identity is
sign-free).  The residual `(|κ| - κ) T` is the bookkeeping cost of recovering `H` from `Ψ` when
`κ < 0`; it vanishes for `κ ≥ 0`, recovering `enstrophyLyapunov_deriv_le` exactly. -/
theorem enstrophyLyapunov_deriv_le_abs (ν μ κ E_max T_max : ℝ) (hν : 0 < ν) (hμ : 0 < μ)
    (hEpos : 0 < E_max) (N : ℕ) (u θ : ℝ → ℤ → ℝ)
    (h : IsUnforcedTruncatedSolution ν μ κ N u θ) {t : ℝ}
    (hEmax : velocityEnergy (u t) N ≤ E_max)
    (hTmax : tempEnstrophy (θ t) N ≤ T_max) :
    2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
        * dyadicVelocityRHS ν κ (u t) (θ t) (k : ℤ))
      + (κ / (2 * μ)) * (2 * ∑ k ∈ Finset.range N,
          θ t (k : ℤ) * dyadicTemperatureRHS μ (u t) (θ t) (k : ℤ))
      ≤ enstrophyYoungConst ν κ E_max + (|κ| - κ) * T_max := by
  have hγ : 0 < ν / E_max := div_pos hν hEpos
  have hrate := enstrophy_rate_le_of_solution_abs ν μ κ E_max hν hEpos N u θ h hEmax
  have htemp := temperature_pairing_eq_neg_mu_tempEnstrophy μ (u t) (θ t) N
    (h.2.2 t).2.2.1 (h.2.2 t).2.2.2
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have htemp' : (κ / (2 * μ)) * (2 * ∑ k ∈ Finset.range N,
        θ t (k : ℤ) * dyadicTemperatureRHS μ (u t) (θ t) (k : ℤ))
      = - κ * tempEnstrophy (θ t) N := by
    rw [htemp]
    field_simp
  rw [htemp']
  have hHnn : 0 ≤ enstrophy (u t) N := enstrophy_nonneg _ _
  have hs2 : (Real.sqrt (enstrophy (u t) N)) ^ 2 = enstrophy (u t) N :=
    Real.sq_sqrt hHnn
  have hy1 : 6 * (enstrophy (u t) N * Real.sqrt (enstrophy (u t) N))
      ≤ (ν / E_max) * (enstrophy (u t) N) ^ 2 + 2187 / (16 * (ν / E_max) ^ 3) := by
    have h := young_cubic_le (γ := ν / E_max) (s := Real.sqrt (enstrophy (u t) N))
      hγ (Real.sqrt_nonneg _)
    have h3 : (Real.sqrt (enstrophy (u t) N)) ^ 3
        = enstrophy (u t) N * Real.sqrt (enstrophy (u t) N) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hs2]
    have h4 : (Real.sqrt (enstrophy (u t) N)) ^ 4 = (enstrophy (u t) N) ^ 2 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, hs2]
      ring
    rwa [h3, h4] at h
  have hy2 : |κ| * enstrophy (u t) N
      ≤ (ν / E_max) * (enstrophy (u t) N) ^ 2 + |κ| ^ 2 / (4 * (ν / E_max)) :=
    young_linear_le (γ := ν / E_max) hγ
  have hsqabs : |κ| ^ 2 = κ ^ 2 := sq_abs κ
  have hTterm : (|κ| - κ) * tempEnstrophy (θ t) N ≤ (|κ| - κ) * T_max :=
    mul_le_mul_of_nonneg_left hTmax (sub_nonneg.mpr (le_abs_self κ))
  simp only [enstrophyYoungConst]
  rw [hsqabs] at hy2
  simp only [div_eq_mul_inv] at hrate hy1 hy2 ⊢
  linarith [hrate, hy1, hy2, hTterm]

/-- **Phase 3d: no finite-time unforced enstrophy blowup, for *any* real `κ`.**  Along any unforced
truncated solution with Dirichlet ends the enstrophy `H = ∑_{k<N} 4^k u_k²` is bounded on every
compact time interval `[0, T]`.  This drops `0 ≤ κ` from `truncated_unforced_enstrophy_bounded`;
the bound is

`H(t) ≤ Ψ(0) + (enstrophyYoungConst ν κ (max E₀ 1) + (|κ| - κ) T_max) · T + (|κ|/(2μ)) S(0)`,

where the last term is the Stage-O′ bookkeeping `H ≤ Ψ + (|κ|/2μ) S(0)` valid for either sign. -/
theorem truncated_unforced_enstrophy_bounded_abs (ν μ κ : ℝ) (hν : 0 < ν) (hμ : 0 < μ)
    (N : ℕ) (u θ : ℝ → ℤ → ℝ) (h : IsUnforcedTruncatedSolution ν μ κ N u θ)
    (hcont : ContinuousOn (fun t => enstrophy (u t) N) (Set.Icc 0 T)) (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, enstrophy (u t) N ≤ C := by
  obtain ⟨E₀, hE₀⟩ := truncated_unforced_energy_bounded_abs ν μ κ hν hμ.le N u θ h
    (velocityEnergy_continuous ν μ κ N u θ h).continuousOn hT
  have hTcont : Continuous fun t => tempEnstrophy (θ t) N := by
    unfold tempEnstrophy
    refine continuous_finsetSum _ fun k hk => ?_
    have hdiff : Differentiable ℝ (fun t : ℝ => (θ t (k : ℤ)) ^ 2) := fun t =>
      ((h.2.1 t (k : ℤ) (Int.natCast_nonneg k)
        (by exact_mod_cast (Finset.mem_range.mp hk))).differentiableAt).pow 2
    exact continuous_const.mul hdiff.continuous
  obtain ⟨T₀, hT₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).bddAbove_image hTcont.continuousOn
  set T_max : ℝ := max T₀ 0 with hT_max
  have hTmax_nonneg : 0 ≤ T_max := le_max_right _ _
  have hTle : ∀ t ∈ Set.Icc 0 T, tempEnstrophy (θ t) N ≤ T_max := fun t ht =>
    (hT₀ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  have hEpos : 0 < max E₀ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hEmax : ∀ s ∈ Set.Icc 0 T, velocityEnergy (u s) N ≤ max E₀ 1 := fun s hs =>
    (hE₀ s hs).trans (le_max_left _ _)
  set C₀ : ℝ := enstrophyYoungConst ν κ (max E₀ 1) + (|κ| - κ) * T_max with hC₀
  have hC₀_nonneg : 0 ≤ C₀ := by
    have hγ : 0 < ν / max E₀ 1 := div_pos hν hEpos
    have h1 : 0 ≤ 2187 / (16 * (ν / max E₀ 1) ^ 3) :=
      div_nonneg (by norm_num) (le_of_lt (mul_pos (by norm_num) (pow_pos hγ 3)))
    have h2 : 0 ≤ κ ^ 2 / (4 * (ν / max E₀ 1)) :=
      div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (by norm_num) hγ))
    have h3 : 0 ≤ (|κ| - κ) * T_max :=
      mul_nonneg (sub_nonneg.mpr (le_abs_self κ)) hTmax_nonneg
    simp only [hC₀, enstrophyYoungConst]
    linarith
  have hderiv : ∀ s ∈ Set.Ico 0 T,
      HasDerivAt (fun r => enstrophyLyapunov ν μ κ N (u r) (θ r))
        (2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u s (k : ℤ)
            * dyadicVelocityRHS ν κ (u s) (θ s) (k : ℤ))
          + (κ / (2 * μ)) * (2 * ∑ k ∈ Finset.range N,
              θ s (k : ℤ) * dyadicTemperatureRHS μ (u s) (θ s) (k : ℤ))) s :=
    fun s _ => enstrophyLyapunov_hasDerivAt ν μ κ N u θ h s
  have hineq : ∀ s ∈ Set.Ico 0 T,
      (2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u s (k : ℤ)
            * dyadicVelocityRHS ν κ (u s) (θ s) (k : ℤ))
          + (κ / (2 * μ)) * (2 * ∑ k ∈ Finset.range N,
              θ s (k : ℤ) * dyadicTemperatureRHS μ (u s) (θ s) (k : ℤ)))
        ≤ C₀ + 0 * enstrophyLyapunov ν μ κ N (u s) (θ s) :=
    fun s hs => by
      have hb := enstrophyLyapunov_deriv_le_abs ν μ κ (max E₀ 1) T_max hν hμ hEpos N u θ h
        (hEmax s ⟨hs.1, hs.2.le⟩) (hTle s ⟨hs.1, hs.2.le⟩)
      simpa [hC₀] using hb
  have hΨcont : ContinuousOn (fun r => enstrophyLyapunov ν μ κ N (u r) (θ r)) (Set.Icc 0 T) :=
    fun s _ => (enstrophyLyapunov_hasDerivAt ν μ κ N u θ h s).continuousAt.continuousWithinAt
  have hg := le_gronwallBound_of_hasDerivAt (f := fun r => enstrophyLyapunov ν μ κ N (u r) (θ r))
    (a := C₀) (b := 0) hΨcont hderiv hineq
  rw [gronwallBound_K0] at hg
  refine ⟨enstrophyLyapunov ν μ κ N (u 0) (θ 0) + C₀ * T
      + (|κ| / (2 * μ)) * entropy (θ 0) N, ?_⟩
  intro t ht
  have hanti : Antitone fun r => entropy (θ r) N := entropy_antitone ν μ κ hμ.le N u θ h
  have hgt : enstrophyLyapunov ν μ κ N (u t) (θ t)
      ≤ enstrophyLyapunov ν μ κ N (u 0) (θ 0) + C₀ * t := hg t ht
  have hCt : C₀ * t ≤ C₀ * T := mul_le_mul_of_nonneg_left ht.2 hC₀_nonneg
  have hHle : enstrophy (u t) N
      ≤ enstrophyLyapunov ν μ κ N (u t) (θ t) + (|κ| / (2 * μ)) * entropy (θ 0) N := by
    have hSle : entropy (θ t) N ≤ entropy (θ 0) N := hanti ht.1
    have hcoef : 0 ≤ |κ| / (2 * μ) := div_nonneg (abs_nonneg κ) (by positivity)
    have h1 : -(κ / (2 * μ)) * entropy (θ t) N ≤ (|κ| / (2 * μ)) * entropy (θ 0) N := by
      have hcmp : -(κ / (2 * μ)) ≤ |κ| / (2 * μ) := by
        rw [show -(κ / (2 * μ)) = (-κ) / (2 * μ) by ring]
        exact div_le_div_of_nonneg_right (neg_le_abs κ) (by positivity)
      calc -(κ / (2 * μ)) * entropy (θ t) N
          ≤ (|κ| / (2 * μ)) * entropy (θ t) N :=
            mul_le_mul_of_nonneg_right hcmp (entropy_nonneg _ _)
        _ ≤ (|κ| / (2 * μ)) * entropy (θ 0) N := mul_le_mul_of_nonneg_left hSle hcoef
    simp only [enstrophyLyapunov]
    linarith
  linarith [hgt, hCt, hHle]

/-! ### Phase 3, forced case -/

/-- **Phase 3e: the sign-free forced pointwise enstrophy rate inequality.**  With
`H = enstrophy u N`, `T = tempEnstrophy θ N`, `He = forceEnstrophy f N` and `E_max ≥ E`, for *any*
real `κ`,

`H' ≤ 6 H √H + |κ| (H + T) + 2 √H √He − 2 ν H²/E_max`.

This is `forced_enstrophy_rate_le` with `|κ|`; the temperature force acts only through `T`. -/
theorem forced_enstrophy_rate_le_abs (ν κ E_max : ℝ) (hν : 0 ≤ ν) (hEpos : 0 < E_max)
    (N : ℕ) (f : ℤ → ℝ) (u θ : ℤ → ℝ) (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0)
    (hEmax : velocityEnergy u N ≤ E_max) :
    2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)
        * forcedVelocityRHS ν κ f u θ (k : ℤ))
      ≤ 6 * (enstrophy u N * Real.sqrt (enstrophy u N))
        + |κ| * (enstrophy u N + tempEnstrophy θ N)
        + 2 * (Real.sqrt (enstrophy u N) * Real.sqrt (forceEnstrophy f N))
        - 2 * ν * (enstrophy u N) ^ 2 / E_max := by
  by_cases hE0 : velocityEnergy u N = 0
  · have hsum0 : (∑ k ∈ Finset.range N, (u (k : ℤ)) ^ 2) = 0 := by
      simpa [velocityEnergy] using hE0
    have hz : ∀ k ∈ Finset.range N, (u (k : ℤ)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.range N)
        (f := fun j : ℕ => (u (j : ℤ)) ^ 2)
        (fun j _ => sq_nonneg (u (j : ℤ)))).mp hsum0
    have hu0 : ∀ k ∈ Finset.range N, u (k : ℤ) = 0 := fun k hk =>
      sq_eq_zero_iff.mp (hz k hk)
    have hL : (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)
        * forcedVelocityRHS ν κ f u θ (k : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [hu0 k hk]
      ring
    have hH : enstrophy u N = 0 := by
      rw [enstrophy]
      apply Finset.sum_eq_zero
      intro k hk
      rw [hu0 k hk]
      ring
    rw [hL, hH]
    have hrhs : 6 * ((0 : ℝ) * Real.sqrt 0) + |κ| * (0 + tempEnstrophy θ N)
        + 2 * (Real.sqrt 0 * Real.sqrt (forceEnstrophy f N))
        - 2 * ν * (0 : ℝ) ^ 2 / E_max = |κ| * tempEnstrophy θ N := by
      rw [Real.sqrt_zero]
      ring
    rw [hrhs]
    simpa using mul_nonneg (abs_nonneg κ) (tempEnstrophy_nonneg θ N)
  · have hEpos' : 0 < velocityEnergy u N :=
      lt_of_le_of_ne (velocityEnergy_nonneg u N) (Ne.symm hE0)
    have hsplit : (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)
        * forcedVelocityRHS ν κ f u θ (k : ℤ))
        = (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)
            * dyadicVelocityRHS ν κ u θ (k : ℤ))
          + (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * f (k : ℤ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by simp only [forcedVelocityRHS, mul_add]
    rw [hsplit]
    have hpair := enstrophy_pairing_le_abs ν κ hν u θ N huBot huTop hEpos'
    have hwork := force_enstrophy_work_le f u N
    have h2pair := mul_le_mul_of_nonneg_left hpair (by norm_num : (0 : ℝ) ≤ 2)
    have h2work := mul_le_mul_of_nonneg_left hwork (by norm_num : (0 : ℝ) ≤ 2)
    have hHnn : 0 ≤ enstrophy u N := enstrophy_nonneg u N
    have hTEnn : 0 ≤ tempEnstrophy θ N := tempEnstrophy_nonneg θ N
    have hamgm : 2 * (Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N))
        ≤ enstrophy u N + tempEnstrophy θ N := by
      have h := sq_nonneg (Real.sqrt (enstrophy u N) - Real.sqrt (tempEnstrophy θ N))
      rw [sub_sq, Real.sq_sqrt hHnn, Real.sq_sqrt hTEnn] at h
      nlinarith
    have hκamgm : |κ| * (2 * (Real.sqrt (enstrophy u N) * Real.sqrt (tempEnstrophy θ N)))
        ≤ |κ| * (enstrophy u N + tempEnstrophy θ N) :=
      mul_le_mul_of_nonneg_left hamgm (abs_nonneg κ)
    have hdiv : (enstrophy u N) ^ 2 / E_max ≤ (enstrophy u N) ^ 2 / velocityEnergy u N :=
      div_le_div_of_nonneg_left (sq_nonneg _) hEpos' hEmax
    have hνdiv : 2 * ν * (enstrophy u N) ^ 2 / E_max
        ≤ 2 * ν * (enstrophy u N) ^ 2 / velocityEnergy u N := by
      have h2ν : 0 ≤ 2 * ν := by linarith
      have h := mul_le_mul_of_nonneg_left hdiv h2ν
      calc 2 * ν * (enstrophy u N) ^ 2 / E_max
          = (2 * ν) * ((enstrophy u N) ^ 2 / E_max) := by ring
        _ ≤ (2 * ν) * ((enstrophy u N) ^ 2 / velocityEnergy u N) := h
        _ = 2 * ν * (enstrophy u N) ^ 2 / velocityEnergy u N := by ring
    simp only [div_eq_mul_inv] at h2pair h2work hνdiv ⊢
    linarith [h2pair, h2work, hκamgm, hνdiv]

/-- **Phase 3f: no finite-time forced enstrophy blowup, for *any* real `κ`.**  Along any forced
truncated solution with Dirichlet ends the enstrophy is bounded on every compact time interval
`[0, T]`.  This drops `0 ≤ κ` from `forced_truncated_enstrophy_bounded`: the transfer is cubic, the
buoyancy and force work are sublinear, viscosity is quadratic, and Young's inequality
(`forced_enstrophy_young` with `|κ|`) absorbs the first two into the third above an explicit
threshold; the barrier `Cascade.le_of_deriv_le_const_sub_sq` then forbids crossing it. -/
theorem forced_truncated_enstrophy_bounded_abs (ν μ κ : ℝ) (hν : 0 < ν)
    (N : ℕ) (f h : ℤ → ℝ) (u θ : ℝ → ℤ → ℝ)
    (hsol : IsForcedTruncatedSolution ν μ κ N f h u θ) (T : ℝ) (hT : 0 ≤ T)
    (hcont : ContinuousOn (fun t => enstrophy (u t) N) (Set.Icc 0 T)) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, enstrophy (u t) N ≤ C := by
  obtain ⟨E₀, hE₀⟩ := forced_truncated_energy_bounded_abs ν μ κ hν N f h u θ hsol T hT
  set E_max : ℝ := max E₀ 1 with hE_max
  have hEpos : 0 < E_max := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hEmax : ∀ t ∈ Set.Icc 0 T, velocityEnergy (u t) N ≤ E_max := fun t ht =>
    (hE₀ t ht).trans (le_max_left _ _)
  have hTcont : Continuous fun t => tempEnstrophy (θ t) N := by
    unfold tempEnstrophy
    refine continuous_finsetSum _ fun k hk => ?_
    have hdiff : Differentiable ℝ (fun t : ℝ => (θ t (k : ℤ)) ^ 2) := fun t =>
      ((hsol.2.1 t (k : ℤ) (Int.natCast_nonneg k)
        (by exact_mod_cast (Finset.mem_range.mp hk))).differentiableAt).pow 2
    exact continuous_const.mul hdiff.continuous
  obtain ⟨T₀, hT₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).bddAbove_image hTcont.continuousOn
  set T_max : ℝ := max T₀ 0 with hT_max
  have hTmax_nonneg : 0 ≤ T_max := le_max_right _ _
  have hTle : ∀ t ∈ Set.Icc 0 T, tempEnstrophy (θ t) N ≤ T_max := fun t ht =>
    (hT₀ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  set C₀ : ℝ := 2187 / (16 * (ν / (2 * E_max)) ^ 3) + κ ^ 2 / (4 * (ν / (4 * E_max)))
      + (E_max / ν) + forceEnstrophy f N + |κ| * T_max with hC₀
  have hC₀_nonneg : 0 ≤ C₀ := by
    rw [hC₀]
    have h1 : 0 ≤ 2187 / (16 * (ν / (2 * E_max)) ^ 3) :=
      div_nonneg (by norm_num) (by positivity)
    have h2 : 0 ≤ κ ^ 2 / (4 * (ν / (4 * E_max))) :=
      div_nonneg (sq_nonneg _) (by positivity)
    have h3 : 0 ≤ E_max / ν := div_nonneg hEpos.le hν.le
    have h4 : 0 ≤ forceEnstrophy f N := forceEnstrophy_nonneg f N
    have h5 : 0 ≤ |κ| * T_max := mul_nonneg (abs_nonneg κ) hTmax_nonneg
    linarith
  have hγpos : 0 < ν / E_max := div_pos hν hEpos
  have hderiv : ∀ t ∈ Set.Ico 0 T, HasDerivAt (fun s => enstrophy (u s) N)
      (2 * ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
        * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ)) t :=
    fun t _ => forcedEnstrophy_hasDerivAt ν μ κ N f h u θ hsol t
  have hineq : ∀ t ∈ Set.Ico 0 T,
      2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
          * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ))
        ≤ C₀ - (ν / E_max) * (enstrophy (u t) N) ^ 2 := by
    intro t ht
    have htIcc : t ∈ Set.Icc 0 T := ⟨ht.1, le_of_lt ht.2⟩
    have hrate := forced_enstrophy_rate_le_abs ν κ E_max hν.le hEpos N f (u t) (θ t)
      (hsol.2.2 t).1 (hsol.2.2 t).2.1 (hEmax t htIcc)
    have hHnn : 0 ≤ enstrophy (u t) N := enstrophy_nonneg _ _
    have hκT : |κ| * (enstrophy (u t) N + tempEnstrophy (θ t) N)
        ≤ |κ| * (enstrophy (u t) N + T_max) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl _) (hTle t htIcc)) (abs_nonneg κ)
    have hyoung := forced_enstrophy_young (ν := ν) (κ := |κ|) (E_max := E_max)
      (He := forceEnstrophy f N) (T_max := T_max) (s := Real.sqrt (enstrophy (u t) N))
      hν hEpos (abs_nonneg κ) (forceEnstrophy_nonneg f N) hTmax_nonneg (Real.sqrt_nonneg _)
    have hsqabs : |κ| ^ 2 = κ ^ 2 := sq_abs κ
    rw [hsqabs] at hyoung
    have hs2 : (Real.sqrt (enstrophy (u t) N)) ^ 2 = enstrophy (u t) N := Real.sq_sqrt hHnn
    have hs3 : (Real.sqrt (enstrophy (u t) N)) ^ 3
        = enstrophy (u t) N * Real.sqrt (enstrophy (u t) N) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, pow_one, hs2]
    have hs4 : (Real.sqrt (enstrophy (u t) N)) ^ 4 = (enstrophy (u t) N) ^ 2 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, hs2]
      ring
    rw [hs3, hs4, hs2] at hyoung
    rw [hC₀]
    simp only [div_eq_mul_inv] at hrate hyoung ⊢
    linarith [hrate, hyoung, hκT]
  have hbar := le_of_deriv_le_const_sub_sq (y := fun t => enstrophy (u t) N)
    (y' := fun t => 2 * ∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u t (k : ℤ)
      * forcedVelocityRHS ν κ f (u t) (θ t) (k : ℤ))
    hC₀_nonneg hγpos hcont hderiv hineq
  exact ⟨max (enstrophy (u 0) N) (Real.sqrt (C₀ / (ν / E_max))), fun t ht => hbar t ht⟩

/-! ## 4. Non-vacuity

The concrete state of `Cascade/ForcedModel.lean` (`u = (0,1,3,0)`, `θ = (0,1,2,0)`,
`f = (0,1,1,0)`, `N = 2`) is used throughout.  Its data are `E = 10`, `S = 5`, `H = 37`,
`T = 17`, `F = 2`, `He = 5`, and the pairings `∑ u θ = 7`, `∑ 4^k u θ = 25`.  Every sign-free
bound is instantiated at **both** `κ = -1 < 0` (unstable stratification) and `κ = 1 > 0`; the
left-hand sides are computed exactly, so no example is vacuous. -/

/-- Concrete velocity ladder `u = (0, 1, 3, 0)` on the shells `-1, 0, 1, 2`. -/
private def uSig : ℤ → ℝ :=
  fun k => if k = -1 then 0 else if k = 0 then 1 else if k = 1 then 3 else if k = 2 then 0 else 0

/-- Concrete temperature ladder `θ = (0, 1, 2, 0)`. -/
private def θSig : ℤ → ℝ :=
  fun k => if k = -1 then 0 else if k = 0 then 1 else if k = 1 then 2 else if k = 2 then 0 else 0

/-- Concrete velocity force `f = (0, 1, 1, 0)`. -/
private def fSig : ℤ → ℝ :=
  fun k => if k = -1 then 0 else if k = 0 then 1 else if k = 1 then 1 else if k = 2 then 0 else 0

example : velocityEnergy uSig 2 = 10 := by
  norm_num [velocityEnergy, Finset.sum_range_succ, Finset.sum_range_zero, uSig]

example : entropy θSig 2 = 5 := by
  norm_num [entropy, Finset.sum_range_succ, Finset.sum_range_zero, θSig]

example : enstrophy uSig 2 = 37 := by
  norm_num [enstrophy, Finset.sum_range_succ, Finset.sum_range_zero, uSig, dyadicWeight]

example : tempEnstrophy θSig 2 = 17 := by
  norm_num [tempEnstrophy, Finset.sum_range_succ, Finset.sum_range_zero, θSig, dyadicWeight]

example : forceEnergy fSig 2 = 2 := by
  norm_num [forceEnergy, Finset.sum_range_succ, Finset.sum_range_zero, fSig]

example : forceEnstrophy fSig 2 = 5 := by
  norm_num [forceEnstrophy, Finset.sum_range_succ, Finset.sum_range_zero, fSig, dyadicWeight]

example : (∑ k ∈ Finset.range 2, uSig (k : ℤ) * θSig (k : ℤ)) = 7 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uSig, θSig]

example :
    (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ) * θSig (k : ℤ)) = 25 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uSig, θSig, dyadicWeight]

/-- `√10 √5 = √50 > 7`: the strictness witness for the energy-norm bound. -/
example : Real.sqrt 10 * Real.sqrt 5 = Real.sqrt 50 := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10)]
  norm_num

/-- The numerical content of the `κ = -1` bound: `-7 ≤ √50`. -/
example : (-7 : ℝ) ≤ Real.sqrt 10 * Real.sqrt 5 := by
  rw [show Real.sqrt 10 * Real.sqrt 5 = Real.sqrt 50 by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 10)]
    norm_num]
  nlinarith [Real.sqrt_nonneg (50 : ℝ)]

/-- **Phase 1a, `κ = -1` (unstable).** The buoyancy pairing is `7`, so the left side is `-7`,
strictly below the bound `√10 √5 ≈ 7.07`. -/
example : -1 * (∑ k ∈ Finset.range 2, uSig (k : ℤ) * θSig (k : ℤ)) = -7
    ∧ -1 * (∑ k ∈ Finset.range 2, uSig (k : ℤ) * θSig (k : ℤ))
      ≤ |-1| * (Real.sqrt (velocityEnergy uSig 2) * Real.sqrt (entropy θSig 2)) := by
  have hL : -1 * (∑ k ∈ Finset.range 2, uSig (k : ℤ) * θSig (k : ℤ)) = -7 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uSig, θSig]
  exact ⟨hL, buoyancy_energy_le_abs (-1) uSig θSig 2⟩

/-- **Phase 1a, `κ = 1` (stable).** The same theorem and state give the left side `+7`; the
stable case is not excluded. -/
example : 1 * (∑ k ∈ Finset.range 2, uSig (k : ℤ) * θSig (k : ℤ)) = 7
    ∧ 1 * (∑ k ∈ Finset.range 2, uSig (k : ℤ) * θSig (k : ℤ))
      ≤ |1| * (Real.sqrt (velocityEnergy uSig 2) * Real.sqrt (entropy θSig 2)) := by
  have hL : 1 * (∑ k ∈ Finset.range 2, uSig (k : ℤ) * θSig (k : ℤ)) = 7 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uSig, θSig]
  exact ⟨hL, buoyancy_energy_le_abs 1 uSig θSig 2⟩

/-- **Phase 1b, `κ = -1` (unstable).** The enstrophy-norm buoyancy pairing is `25`, so the left
side is `-25`, strictly below `√37 √17 ≈ 25.08`. -/
example :
    -1 * (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ) * θSig (k : ℤ)) = -25
    ∧ -1 * (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ) * θSig (k : ℤ))
      ≤ |-1| * (Real.sqrt (enstrophy uSig 2) * Real.sqrt (tempEnstrophy θSig 2)) := by
  have hL : -1 * (∑ k ∈ Finset.range 2,
      dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ) * θSig (k : ℤ)) = -25 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uSig, θSig, dyadicWeight]
  exact ⟨hL, buoyancy_enstrophy_le_abs (-1) uSig θSig 2⟩

/-- **Phase 1b, `κ = 1` (stable).** Same theorem, left side `+25`. -/
example :
    1 * (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ) * θSig (k : ℤ)) = 25
    ∧ 1 * (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ) * θSig (k : ℤ))
      ≤ |1| * (Real.sqrt (enstrophy uSig 2) * Real.sqrt (tempEnstrophy θSig 2)) := by
  have hL : 1 * (∑ k ∈ Finset.range 2,
      dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ) * θSig (k : ℤ)) = 25 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uSig, θSig, dyadicWeight]
  exact ⟨hL, buoyancy_enstrophy_le_abs 1 uSig θSig 2⟩

/-- **Phase 2a, `κ = -1` (unstable).** The unforced velocity pairing is `-44`, while the bound is
`√50 − 10 ≈ -2.93`; the inequality is strict and the pairing is far from zero. -/
example : (∑ k ∈ Finset.range 2, uSig (k : ℤ) * dyadicVelocityRHS 1 (-1) uSig θSig (k : ℤ)) = -44
    ∧ (∑ k ∈ Finset.range 2, uSig (k : ℤ) * dyadicVelocityRHS 1 (-1) uSig θSig (k : ℤ))
      ≤ |-1| * (Real.sqrt (velocityEnergy uSig 2) * Real.sqrt (entropy θSig 2))
        - 1 * velocityEnergy uSig 2 := by
  have hL : (∑ k ∈ Finset.range 2,
      uSig (k : ℤ) * dyadicVelocityRHS 1 (-1) uSig θSig (k : ℤ)) = -44 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uSig, θSig, dyadicVelocityRHS,
      generalVelocityRHS, boussinesqTransferU, dyadicWeight]
  exact ⟨hL, velocity_energy_pairing_le_abs 1 (-1) (by norm_num) uSig θSig 2
    (by norm_num [uSig]) (by norm_num [uSig])⟩

/-- **Phase 2a, `κ = 1` (stable).** The same theorem at `κ = 1` gives the familiar `-30`. -/
example : (∑ k ∈ Finset.range 2, uSig (k : ℤ) * dyadicVelocityRHS 1 1 uSig θSig (k : ℤ)) = -30
    ∧ (∑ k ∈ Finset.range 2, uSig (k : ℤ) * dyadicVelocityRHS 1 1 uSig θSig (k : ℤ))
      ≤ |1| * (Real.sqrt (velocityEnergy uSig 2) * Real.sqrt (entropy θSig 2))
        - 1 * velocityEnergy uSig 2 := by
  have hL : (∑ k ∈ Finset.range 2,
      uSig (k : ℤ) * dyadicVelocityRHS 1 1 uSig θSig (k : ℤ)) = -30 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uSig, θSig, dyadicVelocityRHS,
      generalVelocityRHS, boussinesqTransferU, dyadicWeight]
  exact ⟨hL, velocity_energy_pairing_le_abs 1 1 (by norm_num) uSig θSig 2
    (by norm_num [uSig]) (by norm_num [uSig])⟩

/-- **Phase 2e, `κ = -1` (unstable, forced).** The forced velocity pairing is `-40`. -/
example :
    (∑ k ∈ Finset.range 2, uSig (k : ℤ) * forcedVelocityRHS 1 (-1) fSig uSig θSig (k : ℤ)) = -40
    ∧ (∑ k ∈ Finset.range 2, uSig (k : ℤ) * forcedVelocityRHS 1 (-1) fSig uSig θSig (k : ℤ))
      ≤ |-1| * (Real.sqrt (velocityEnergy uSig 2) * Real.sqrt (entropy θSig 2))
        + Real.sqrt (velocityEnergy uSig 2) * Real.sqrt (forceEnergy fSig 2)
        - 1 * velocityEnergy uSig 2 := by
  have hL : (∑ k ∈ Finset.range 2,
      uSig (k : ℤ) * forcedVelocityRHS 1 (-1) fSig uSig θSig (k : ℤ)) = -40 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uSig, θSig, fSig, forcedVelocityRHS,
      dyadicVelocityRHS, generalVelocityRHS, boussinesqTransferU, dyadicWeight]
  exact ⟨hL, forced_velocity_pairing_le_abs 1 (-1) (by norm_num) fSig uSig θSig 2
    (by norm_num [uSig]) (by norm_num [uSig])⟩

/-- **Phase 2e, `κ = 1` (stable, forced).** Same theorem, the familiar `-26`. -/
example :
    (∑ k ∈ Finset.range 2, uSig (k : ℤ) * forcedVelocityRHS 1 1 fSig uSig θSig (k : ℤ)) = -26
    ∧ (∑ k ∈ Finset.range 2, uSig (k : ℤ) * forcedVelocityRHS 1 1 fSig uSig θSig (k : ℤ))
      ≤ |1| * (Real.sqrt (velocityEnergy uSig 2) * Real.sqrt (entropy θSig 2))
        + Real.sqrt (velocityEnergy uSig 2) * Real.sqrt (forceEnergy fSig 2)
        - 1 * velocityEnergy uSig 2 := by
  have hL : (∑ k ∈ Finset.range 2,
      uSig (k : ℤ) * forcedVelocityRHS 1 1 fSig uSig θSig (k : ℤ)) = -26 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uSig, θSig, fSig, forcedVelocityRHS,
      dyadicVelocityRHS, generalVelocityRHS, boussinesqTransferU, dyadicWeight]
  exact ⟨hL, forced_velocity_pairing_le_abs 1 1 (by norm_num) fSig uSig θSig 2
    (by norm_num [uSig]) (by norm_num [uSig])⟩

/-- **Phase 3a, `κ = -1` (unstable).** The unforced enstrophy pairing is `-152`, far below the
bound `3·37√37 + √37√17 − 37²/10 ≈ 576`. -/
example : (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ)
      * dyadicVelocityRHS 1 (-1) uSig θSig (k : ℤ)) = -152
    ∧ (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ)
        * dyadicVelocityRHS 1 (-1) uSig θSig (k : ℤ))
      ≤ 3 * (enstrophy uSig 2 * Real.sqrt (enstrophy uSig 2))
        + |-1| * (Real.sqrt (enstrophy uSig 2) * Real.sqrt (tempEnstrophy θSig 2))
        - 1 * (enstrophy uSig 2) ^ 2 / velocityEnergy uSig 2 := by
  have hL : (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ)
      * dyadicVelocityRHS 1 (-1) uSig θSig (k : ℤ)) = -152 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uSig, θSig, dyadicVelocityRHS,
      generalVelocityRHS, boussinesqTransferU, dyadicWeight]
  have hE : 0 < velocityEnergy uSig 2 := by
    norm_num [velocityEnergy, Finset.sum_range_succ, Finset.sum_range_zero, uSig]
  exact ⟨hL, enstrophy_pairing_le_abs 1 (-1) (by norm_num) uSig θSig 2
    (by norm_num [uSig]) (by norm_num [uSig]) hE⟩

/-- **Phase 3a, `κ = 1` (stable).** Same theorem; the pairing is the familiar `-102`. -/
example : (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ)
      * dyadicVelocityRHS 1 1 uSig θSig (k : ℤ)) = -102
    ∧ (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ)
        * dyadicVelocityRHS 1 1 uSig θSig (k : ℤ))
      ≤ 3 * (enstrophy uSig 2 * Real.sqrt (enstrophy uSig 2))
        + |1| * (Real.sqrt (enstrophy uSig 2) * Real.sqrt (tempEnstrophy θSig 2))
        - 1 * (enstrophy uSig 2) ^ 2 / velocityEnergy uSig 2 := by
  have hL : (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ)
      * dyadicVelocityRHS 1 1 uSig θSig (k : ℤ)) = -102 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uSig, θSig, dyadicVelocityRHS,
      generalVelocityRHS, boussinesqTransferU, dyadicWeight]
  have hE : 0 < velocityEnergy uSig 2 := by
    norm_num [velocityEnergy, Finset.sum_range_succ, Finset.sum_range_zero, uSig]
  exact ⟨hL, enstrophy_pairing_le_abs 1 1 (by norm_num) uSig θSig 2
    (by norm_num [uSig]) (by norm_num [uSig]) hE⟩

/-- **Phase 3e, `κ = -1` (unstable, forced).** The doubled forced enstrophy pairing is `-278`,
while the rate bound is `6·37√37 + 54 + 2√37√5 − 2·37²/10 ≈ 1158` (with `E_max = 10`). -/
example : 2 * (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ)
      * forcedVelocityRHS 1 (-1) fSig uSig θSig (k : ℤ)) = -278
    ∧ 2 * (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ)
        * forcedVelocityRHS 1 (-1) fSig uSig θSig (k : ℤ))
      ≤ 6 * (enstrophy uSig 2 * Real.sqrt (enstrophy uSig 2))
        + |-1| * (enstrophy uSig 2 + tempEnstrophy θSig 2)
        + 2 * (Real.sqrt (enstrophy uSig 2) * Real.sqrt (forceEnstrophy fSig 2))
        - 2 * 1 * (enstrophy uSig 2) ^ 2 / 10 := by
  have hL : 2 * (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ)
      * forcedVelocityRHS 1 (-1) fSig uSig θSig (k : ℤ)) = -278 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uSig, θSig, fSig, forcedVelocityRHS,
      dyadicVelocityRHS, generalVelocityRHS, boussinesqTransferU, dyadicWeight]
  have hEmax : velocityEnergy uSig 2 ≤ 10 := by
    norm_num [velocityEnergy, Finset.sum_range_succ, Finset.sum_range_zero, uSig]
  exact ⟨hL, forced_enstrophy_rate_le_abs 1 (-1) 10 (by norm_num) (by norm_num) 2 fSig uSig θSig
    (by norm_num [uSig]) (by norm_num [uSig]) hEmax⟩

/-- **Phase 3e, `κ = 1` (stable, forced).** Same theorem; the doubled pairing is `-178`. -/
example : 2 * (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ)
      * forcedVelocityRHS 1 1 fSig uSig θSig (k : ℤ)) = -178
    ∧ 2 * (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ)
        * forcedVelocityRHS 1 1 fSig uSig θSig (k : ℤ))
      ≤ 6 * (enstrophy uSig 2 * Real.sqrt (enstrophy uSig 2))
        + |1| * (enstrophy uSig 2 + tempEnstrophy θSig 2)
        + 2 * (Real.sqrt (enstrophy uSig 2) * Real.sqrt (forceEnstrophy fSig 2))
        - 2 * 1 * (enstrophy uSig 2) ^ 2 / 10 := by
  have hL : 2 * (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ)) * uSig (k : ℤ)
      * forcedVelocityRHS 1 1 fSig uSig θSig (k : ℤ)) = -178 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, uSig, θSig, fSig, forcedVelocityRHS,
      dyadicVelocityRHS, generalVelocityRHS, boussinesqTransferU, dyadicWeight]
  have hEmax : velocityEnergy uSig 2 ≤ 10 := by
    norm_num [velocityEnergy, Finset.sum_range_succ, Finset.sum_range_zero, uSig]
  exact ⟨hL, forced_enstrophy_rate_le_abs 1 1 10 (by norm_num) (by norm_num) 2 fSig uSig θSig
    (by norm_num [uSig]) (by norm_num [uSig]) hEmax⟩

/-! ### The capstones fire with `κ < 0` (and, as a sanity check, with `κ > 0`) -/

/-- Phase 2c fires at `κ = -1`. -/
example : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    velocityEnergy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2 ≤ C := by
  refine truncated_unforced_energy_bounded_abs (T := 1) 1 1 (-1) (by norm_num) (by norm_num) 2
    (fun _ _ => 0) (fun _ _ => 0) (zero_is_unforcedTruncatedSolution 1 1 (-1) 2) ?_ (by norm_num)
  have hfun : (fun t => velocityEnergy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2)
      = fun _ => (0 : ℝ) := by
    funext t
    simp [velocityEnergy]
  rw [hfun]
  exact continuousOn_const

/-- Phase 2h fires at `κ = -1`. -/
example : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    velocityEnergy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2 ≤ C :=
  forced_truncated_energy_bounded_abs 1 1 (-1) (by norm_num) 2 (fun _ => 0) (fun _ => 0)
    (fun _ _ => 0) (fun _ _ => 0) (zero_is_forcedTruncatedSolution 1 1 (-1) 2) 1 (by norm_num)

/-- Phase 3d fires at `κ = -1`. -/
example : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2 ≤ C := by
  refine truncated_unforced_enstrophy_bounded_abs (T := 1) 1 1 (-1) (by norm_num) (by norm_num) 2
    (fun _ _ => 0) (fun _ _ => 0) (zero_is_unforcedTruncatedSolution 1 1 (-1) 2) ?_ (by norm_num)
  have hfun : (fun t => enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2)
      = fun _ => (0 : ℝ) := by
    funext t
    simp [enstrophy]
  rw [hfun]
  exact continuousOn_const

/-- Phase 3f fires at `κ = -1`. -/
example : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2 ≤ C := by
  refine forced_truncated_enstrophy_bounded_abs (T := 1) 1 1 (-1) (by norm_num) 2
    (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    (zero_is_forcedTruncatedSolution 1 1 (-1) 2) (by norm_num) ?_
  have hfun : (fun t => enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2)
      = fun _ => (0 : ℝ) := by
    funext t
    simp [enstrophy]
  rw [hfun]
  exact continuousOn_const

/-- Phase 2d fires at `κ = -1`, with the explicit uniform-in-time constant. -/
example (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    velocityEnergy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2
      ≤ max (velocityEnergy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) 0) 2)
        (|-1| * Real.sqrt (entropy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) 0) 2)
          / (2 * 1 - |-1| * Real.sqrt (entropy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) 0) 2))) := by
  refine truncated_unforced_energy_le_max_abs (T := 1) 1 1 (-1) (by norm_num) (by norm_num) 2
    (fun _ _ => 0) (fun _ _ => 0) (zero_is_unforcedTruncatedSolution 1 1 (-1) 2) ?_ ?_
    (by norm_num) t ht
  · have hfun : (fun t => velocityEnergy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2)
        = fun _ => (0 : ℝ) := by
      funext t
      simp [velocityEnergy]
    rw [hfun]
    exact continuousOn_const
  · simp [entropy]

/-- Phase 2f fires at `κ = -1` (zero forced equilibrium). -/
example (t : ℝ) :
    2 * (∑ k ∈ Finset.range 2, ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) (k : ℤ)
        * forcedVelocityRHS 1 (-1) (fun _ => 0) ((fun _ _ => (0 : ℝ)) t)
          ((fun _ _ => (0 : ℝ)) t) (k : ℤ))
      ≤ 2 * (|-1| * Real.sqrt (entropy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2)
            + Real.sqrt (forceEnergy (fun _ => 0) 2))
          * Real.sqrt (velocityEnergy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2)
        - 2 * 1 * velocityEnergy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2 :=
  forced_energy_rate_le_abs 1 1 (-1) (by norm_num) 2 (fun _ => 0) (fun _ => 0)
    (fun _ _ => 0) (fun _ _ => 0) (zero_is_forcedTruncatedSolution 1 1 (-1) 2) t

/-- Phase 3b fires at `κ = -1` (zero equilibrium). -/
example (t : ℝ) :
    2 * (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ))
        * ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) (k : ℤ)
        * dyadicVelocityRHS 1 (-1) ((fun _ _ => (0 : ℝ)) t) ((fun _ _ => (0 : ℝ)) t) (k : ℤ))
      ≤ 6 * (enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2
          * Real.sqrt (enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2))
        + |-1| * (enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2
          + tempEnstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2)
        - 2 * 1 * (enstrophy ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) 2) ^ 2 / 1 :=
  enstrophy_rate_le_of_solution_abs 1 1 (-1) 1 (by norm_num) (by norm_num) 2
    (fun _ _ => 0) (fun _ _ => 0) (zero_is_unforcedTruncatedSolution 1 1 (-1) 2)
    (t := t) (by simp [velocityEnergy])

/-- Phase 3c fires at `κ = -1` (zero equilibrium); the bookkeeping term `(|κ| - κ) T_max = 2` is
genuinely present. -/
example (t : ℝ) :
    2 * (∑ k ∈ Finset.range 2, dyadicWeight (2 * (k : ℤ))
        * ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) (k : ℤ)
        * dyadicVelocityRHS 1 (-1) ((fun _ _ => (0 : ℝ)) t) ((fun _ _ => (0 : ℝ)) t) (k : ℤ))
      + ((-1) / (2 * 1)) * (2 * ∑ k ∈ Finset.range 2,
          ((fun _ _ => (0 : ℝ) : ℝ → ℤ → ℝ) t) (k : ℤ)
            * dyadicTemperatureRHS 1 ((fun _ _ => (0 : ℝ)) t) ((fun _ _ => (0 : ℝ)) t) (k : ℤ))
      ≤ enstrophyYoungConst 1 (-1) 1 + (|-1| - (-1)) * 1 :=
  enstrophyLyapunov_deriv_le_abs 1 1 (-1) 1 1 (by norm_num) (by norm_num) (by norm_num) 2
    (fun _ _ => 0) (fun _ _ => 0) (zero_is_unforcedTruncatedSolution 1 1 (-1) 2)
    (t := t) (by simp [velocityEnergy]) (by simp [tempEnstrophy])

end Cascade

/-! ## Axiom audit — helper lemmas, Phases 1–3 -/

#print axioms Cascade.abs_sum_mul_le_sqrt_mul_sqrt
#print axioms Cascade.enstrophy_neg
#print axioms Cascade.tempEnstrophy_neg
#print axioms Cascade.dyadicVelocityFlux_bot_zero
#print axioms Cascade.dyadicVelocityFlux_top_zero
#print axioms Cascade.sum_sq_le_sum_weighted_sq
#print axioms Cascade.buoyancy_energy_le_abs
#print axioms Cascade.buoyancy_enstrophy_le_abs
#print axioms Cascade.velocity_energy_pairing_le_abs
#print axioms Cascade.velocity_energy_rate_le_of_solution_abs
#print axioms Cascade.truncated_unforced_energy_bounded_abs
#print axioms Cascade.truncated_unforced_energy_le_max_abs
#print axioms Cascade.forced_velocity_pairing_le_abs
#print axioms Cascade.forced_energy_rate_le_abs
#print axioms Cascade.forced_energy_rate_le_of_entropy_le_abs
#print axioms Cascade.forced_truncated_energy_bounded_abs
#print axioms Cascade.forced_energy_le_max_unforced_temperature_abs
#print axioms Cascade.enstrophy_pairing_le_abs
#print axioms Cascade.enstrophy_rate_le_of_solution_abs
#print axioms Cascade.enstrophyLyapunov_deriv_le_abs
#print axioms Cascade.truncated_unforced_enstrophy_bounded_abs
#print axioms Cascade.forced_enstrophy_rate_le_abs
#print axioms Cascade.forced_truncated_enstrophy_bounded_abs
