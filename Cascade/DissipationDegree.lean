import Cascade.BoussinesqScaling
import Mathlib.Tactic

/-!
# The dissipation degree of the dyadic Boussinesq model

The frozen Stage R dyadic Boussinesq model of `Cascade/Boussinesq.lean` dissipates the velocity
with `ν · 2^{2k} · u_k`, i.e. the dyadic Laplacian `−Δ`.  This file introduces the one-parameter
generalisation in which the dissipation is `ν · 2^{d k} · u_k` for an arbitrary **dissipation
degree** `d : ℤ`:

* `velocityRHSDegree ν κ A B d u θ k = boussinesqTransferU A B u k + κ θ_k − ν 2^{dk} u_k`;
* `velocityRHSDegree_two` recovers the library model `generalVelocityRHS` at `d = 2`;
* `velocityRHSDegree_scaling_covariant` proves the general-degree Boussinesq scaling covariance:
  the viscosity must rescale as `ν ↦ ν · λ^{b+1−d}` for the velocity equation to be homogeneous of
  degree `2b+1`;
* `velocityRHSDegree_scaling_covariant_two` specialises this to `d = 2`, reproducing the law
  `ν ↦ ν · λ^{b−1}` of `Cascade/BoussinesqScaling.lean`.

The headline is that the law is not merely *sufficient* but *necessary*:

* `boussinesq_law_forces_degree_two` : if the velocity equation is covariant under the Boussinesq
  scaling with the standard viscosity law `ν ↦ ν · λ^{b−1}` for **every** velocity and temperature
  ladder, then the dissipation degree must be `d = 2`;
* `boussinesqB_forces_degree_two` : the same at the standard 2D Boussinesq exponent
  `boussinesqB = 1`.

The proof is a single-shell test: taking the ladder supported only on shell `0` and reading the
covariance identity at shell `s` (the image of that shell under the scaling) kills every transfer
and buoyancy term, leaving `2^{s(b−1)} · 2^{ds} · 2^{sb} = 2^{s(2b+1)}`.  Injectivity of
`k ↦ 2^k` (`dyadicWeight_injective`) turns this into the integer identity
`s(b−1) + ds + sb = s(2b+1)`, i.e. `s(d−2) = 0`, whence `d = 2` because `s ≠ 0`.
-/

noncomputable section

namespace Cascade

/-! ## The general-degree velocity RHS -/

/-- The velocity component of the dyadic Boussinesq ODE with a general **dissipation degree** `d`:
the viscosity term is `ν · 2^{d k} · u_k` in place of `ν · 2^{2k} · u_k`. -/
def velocityRHSDegree (ν κ A B : ℝ) (d : ℤ) (u θ : ℤ → ℝ) (k : ℤ) : ℝ :=
  boussinesqTransferU A B u k + κ * θ k - ν * dyadicWeight (d * k) * u k

/-- **Recovery of the existing model.** At dissipation degree `d = 2` the general-degree RHS is
literally the library's `generalVelocityRHS` (the exponent `d * k` becomes `2 * k`). -/
theorem velocityRHSDegree_two (ν κ A B : ℝ) (u θ : ℤ → ℝ) (k : ℤ) :
    velocityRHSDegree ν κ A B 2 u θ k = generalVelocityRHS ν κ A B u θ k := rfl

/-! ## Injectivity of the dyadic weight

The dyadic weight is `k ↦ 2^k`, and `k ↦ 2^k` is injective on `ℤ` because `2 > 1`.
-/

/-- **The dyadic weight is injective**: `2^a = 2^b` forces `a = b` on the integers. -/
theorem dyadicWeight_injective : Function.Injective dyadicWeight := by
  intro a b hab
  exact zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hab

/-! ## `zpow` arithmetic of the dyadic weight (local copies)

The corresponding lemmas in `Cascade/BoussinesqScaling.lean` are `private` to that file, so they are
re-derived here for the general degree.
-/

/-- The dyadic weight is multiplicative in its exponent: `2^{a+b} = 2^a · 2^b`. -/
private lemma dW_add (a b : ℤ) : dyadicWeight (a + b) = dyadicWeight a * dyadicWeight b := by
  simp only [dyadicWeight]
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]

/-- The square of a dyadic weight: `(2^a)^2 = 2^{2a}`. -/
private lemma dW_sq (a : ℤ) : (dyadicWeight a) ^ 2 = dyadicWeight (2 * a) := by
  simp only [dyadicWeight]
  rw [sq, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

/-- Velocity transfer amplitude chain: `2^k · (2^{sb})^2 = 2^{s(2b+1)} · 2^{k-s}`. -/
private lemma dW_chain_v (s b k : ℤ) :
    dyadicWeight k * (dyadicWeight (s * b)) ^ 2
      = dyadicWeight (s * (2 * b + 1)) * dyadicWeight (k - s) := by
  rw [dW_sq]
  simp only [← dW_add]
  congr 1
  ring

/-- The velocity transfer is homogeneous of degree `2b+1` under the shell shift. -/
private lemma transferU_scale (s b : ℤ) (A B : ℝ) (u : ℤ → ℝ) (k : ℤ) :
    boussinesqTransferU A B (scaleVelocity s b u) k
      = dyadicWeight (s * (2 * b + 1)) * boussinesqTransferU A B u (k - s) := by
  have h1 : k - 1 - s = (k - s) - 1 := by ring
  have h2 : k + 1 - s = (k - s) + 1 := by ring
  have hfac : boussinesqTransferU A B (scaleVelocity s b u) k
      = dyadicWeight k * (dyadicWeight (s * b)) ^ 2
          * (A * ((u ((k - s) - 1)) ^ 2 - 2 * u (k - s) * u ((k - s) + 1))
              + B * (u (k - s) * u ((k - s) - 1) - 2 * (u ((k - s) + 1)) ^ 2)) := by
    simp only [boussinesqTransferU, scaleVelocity, h1, h2, mul_pow]
    ring
  rw [hfac, dW_chain_v]
  simp only [boussinesqTransferU]
  ring

/-- Dissipation amplitude at general degree:
`2^{s(b+1-d)} · 2^{ds} · 2^{sb} = 2^{s(2b+1)}`. -/
private lemma dW_diss_v_amp (s b d : ℤ) :
    dyadicWeight (s * (b + 1 - d)) * dyadicWeight (d * s) * dyadicWeight (s * b)
      = dyadicWeight (s * (2 * b + 1)) := by
  simp only [← dW_add]
  congr 1
  ring

/-- Velocity dissipation at general degree:
`2^{s(b+1-d)} · 2^{dk} · 2^{sb} = 2^{s(2b+1)} · 2^{d(k-s)}`. -/
private lemma dW_diss_v (s b d k : ℤ) :
    dyadicWeight (s * (b + 1 - d)) * dyadicWeight (d * k) * dyadicWeight (s * b)
      = dyadicWeight (s * (2 * b + 1)) * dyadicWeight (d * (k - s)) := by
  have h : d * k = d * (k - s) + d * s := by ring
  rw [h, dW_add]
  rw [show dyadicWeight (s * (b + 1 - d))
            * (dyadicWeight (d * (k - s)) * dyadicWeight (d * s)) * dyadicWeight (s * b)
        = dyadicWeight (d * (k - s))
            * (dyadicWeight (s * (b + 1 - d)) * dyadicWeight (d * s)
                * dyadicWeight (s * b)) by ring]
  rw [dW_diss_v_amp]
  ring

/-- The general-degree velocity dissipation rescales:
`ν λ^{b+1-d} · 2^{dk} · u_λ = λ^{2b+1} · ν · 2^{d(k-s)} · u`. -/
private lemma diss_v_scale_degree (s b d : ℤ) (ν : ℝ) (u : ℤ → ℝ) (k : ℤ) :
    ν * dyadicWeight (s * (b + 1 - d)) * dyadicWeight (d * k) * scaleVelocity s b u k
      = dyadicWeight (s * (2 * b + 1)) * (ν * dyadicWeight (d * (k - s)) * u (k - s)) := by
  simp only [scaleVelocity]
  rw [show ν * dyadicWeight (s * (b + 1 - d)) * dyadicWeight (d * k)
            * (dyadicWeight (s * b) * u (k - s))
        = ν * (dyadicWeight (s * (b + 1 - d)) * dyadicWeight (d * k)
              * dyadicWeight (s * b)) * u (k - s) by ring]
  rw [dW_diss_v]
  ring

/-! ## Scaling covariance at general degree -/

/-- **Scaling covariance, velocity component, general dissipation degree.** Under the Boussinesq
scaling with exponents `(s, b)` the velocity equation is homogeneous of degree `2b+1`; the
viscosity rescales by `λ^{b+1-d}`.  At `d = 2` this is the law `ν ↦ ν · λ^{b-1}` of
`general_scaling_covariant_velocity`. -/
theorem velocityRHSDegree_scaling_covariant (s b : ℤ) (ν κ A B : ℝ) (d : ℤ)
    (u θ : ℤ → ℝ) (k : ℤ) :
    velocityRHSDegree (ν * dyadicWeight (s * (b + 1 - d))) κ A B d
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight (s * (2 * b + 1)) * velocityRHSDegree ν κ A B d u θ (k - s) := by
  simp only [velocityRHSDegree]
  rw [transferU_scale]
  have hbuoy : κ * scaleTemperature s b θ k
      = dyadicWeight (s * (2 * b + 1)) * (κ * θ (k - s)) := by
    simp only [scaleTemperature]
    ring
  rw [hbuoy, diss_v_scale_degree]
  ring

/-- **Scaling covariance at degree `d = 2`**, reproducing the existing Boussinesq viscosity law
`ν ↦ ν · λ^{b-1}`: derived from the general-degree theorem by the arithmetic identity
`s * (b + 1 - 2) = s * (b - 1)`. -/
theorem velocityRHSDegree_scaling_covariant_two (s b : ℤ) (ν κ A B : ℝ) (u θ : ℤ → ℝ)
    (k : ℤ) :
    velocityRHSDegree (ν * dyadicWeight (s * (b - 1))) κ A B 2
        (scaleVelocity s b u) (scaleTemperature s b θ) k
      = dyadicWeight (s * (2 * b + 1)) * velocityRHSDegree ν κ A B 2 u θ (k - s) := by
  have h := velocityRHSDegree_scaling_covariant s b ν κ A B 2 u θ k
  have he : s * (b + 1 - 2) = s * (b - 1) := by ring
  rw [he] at h
  exact h

/-! ## The law forces the degree

Every transfer and buoyancy term is killed by testing on a single shell.  Take the ladder
`deltaZero` supported at shell `0`, the zero temperature, and evaluate the covariance hypothesis at
shell `s` — the image of shell `0` under the scaling.  The scaled ladder is supported at shell `s`
with amplitude `2^{sb}`, so all three of its transfer/buoyancy contributions vanish at shell `s`,
while at shell `0` the unscaled ladder has vanishing neighbours, so its transfer vanishes too.
-/

/-- The unit shell mass at shell `0`: the ladder `u_j = δ_{j,0}`. -/
private def deltaZero : ℤ → ℝ := fun j => if j = 0 then 1 else 0

private lemma deltaZero_zero : deltaZero 0 = 1 := by
  simp [deltaZero]

private lemma deltaZero_neg_one : deltaZero (-1) = 0 := by
  have h : (-1 : ℤ) ≠ 0 := by norm_num
  simp [deltaZero, h]

private lemma deltaZero_one : deltaZero 1 = 0 := by
  have h : (1 : ℤ) ≠ 0 := by norm_num
  simp [deltaZero, h]

/-- The nearest-octave velocity transfer vanishes when both neighbours of shell `k` are zero. -/
private lemma transferU_zero_of_neighbours (A B : ℝ) (u : ℤ → ℝ) (k : ℤ)
    (h1 : u (k - 1) = 0) (h3 : u (k + 1) = 0) :
    boussinesqTransferU A B u k = 0 := by
  simp only [boussinesqTransferU, h1, h3]
  ring

/-- **The Boussinesq viscosity law forces the dissipation degree.** If the velocity equation with
general dissipation degree `d` is covariant under the Boussinesq scaling `(s, b)` with the standard
viscosity law `ν ↦ ν · λ^{b-1}` for *every* velocity and temperature ladder, then `d = 2`.

The hypothesis is tested on the single-shell ladder `u = δ_{·,0}`, `θ = 0` at shell `k = s`, which
collapses it to `2^{s(b-1)} · 2^{ds} · 2^{sb} = 2^{s(2b+1)}`; injectivity of the dyadic weight turns
this into `s(b-1) + ds + sb = s(2b+1)`, i.e. `s(d-2) = 0`, and `s ≠ 0` gives `d = 2`. -/
theorem boussinesq_law_forces_degree_two (s b d : ℤ) (hs : s ≠ 0) (ν κ : ℝ) (hν : ν ≠ 0)
    (h : ∀ (u θ : ℤ → ℝ) (k : ℤ),
      velocityRHSDegree (ν * dyadicWeight (s * (b - 1))) κ 1 0 d
          (scaleVelocity s b u) (scaleTemperature s b θ) k
        = dyadicWeight (s * (2 * b + 1)) * velocityRHSDegree ν κ 1 0 d u θ (k - s)) :
    d = 2 := by
  -- the scaled unit shell at shell `s` has vanishing neighbours, and value `2^{sb}` at `s`
  have hs1 : scaleVelocity s b deltaZero (s - 1) = 0 := by
    have h1 : (s - 1 : ℤ) - s = -1 := by ring
    simp only [scaleVelocity, h1, deltaZero_neg_one, mul_zero]
  have hs3 : scaleVelocity s b deltaZero (s + 1) = 0 := by
    have h1 : (s + 1 : ℤ) - s = 1 := by ring
    simp only [scaleVelocity, h1, deltaZero_one, mul_zero]
  have hs0 : scaleVelocity s b deltaZero s = dyadicWeight (s * b) := by
    have h1 : (s : ℤ) - s = 0 := by ring
    simp only [scaleVelocity, h1, deltaZero_zero, mul_one]
  -- the transfer contributions vanish at shell `s` (scaled) and at shell `0` (unscaled)
  have hL_transfer : boussinesqTransferU 1 0 (scaleVelocity s b deltaZero) s = 0 :=
    transferU_zero_of_neighbours 1 0 (scaleVelocity s b deltaZero) s hs1 hs3
  have hR_transfer : boussinesqTransferU 1 0 deltaZero 0 = 0 :=
    transferU_zero_of_neighbours 1 0 deltaZero 0 (by simpa using deltaZero_neg_one)
      (by simpa using deltaZero_one)
  -- left-hand side at shell `s`
  have hL : velocityRHSDegree (ν * dyadicWeight (s * (b - 1))) κ 1 0 d
        (scaleVelocity s b deltaZero) (scaleTemperature s b (fun _ : ℤ => 0)) s
      = -(ν * dyadicWeight (s * (b - 1)) * dyadicWeight (d * s) * dyadicWeight (s * b)) := by
    simp only [velocityRHSDegree, hL_transfer, scaleTemperature, mul_zero, add_zero]
    rw [hs0]
    ring
  -- right-hand side at shell `s - s = 0`
  have hR : dyadicWeight (s * (2 * b + 1))
        * velocityRHSDegree ν κ 1 0 d deltaZero (fun _ : ℤ => 0) (s - s)
      = -(dyadicWeight (s * (2 * b + 1)) * ν) := by
    have hz : s - s = (0 : ℤ) := by ring
    rw [hz]
    have hval : velocityRHSDegree ν κ 1 0 d deltaZero (fun _ : ℤ => 0) (0 : ℤ) = -ν := by
      simp only [velocityRHSDegree, hR_transfer, deltaZero_zero, mul_zero, add_zero,
        dyadicWeight, zpow_zero, mul_one, zero_sub]
    rw [hval]
    ring
  -- the covariance identity collapses to the amplitude identity
  have key := h deltaZero (fun _ : ℤ => 0) s
  rw [hL, hR] at key
  have h1 : ν * (dyadicWeight (s * (b - 1)) * dyadicWeight (d * s) * dyadicWeight (s * b))
      = dyadicWeight (s * (2 * b + 1)) * ν := by
    have h3 : ν * dyadicWeight (s * (b - 1)) * dyadicWeight (d * s) * dyadicWeight (s * b)
        = dyadicWeight (s * (2 * b + 1)) * ν := neg_inj.mp key
    rwa [show ν * (dyadicWeight (s * (b - 1)) * dyadicWeight (d * s) * dyadicWeight (s * b))
          = ν * dyadicWeight (s * (b - 1)) * dyadicWeight (d * s)
              * dyadicWeight (s * b) by ring]
  have hA : dyadicWeight (s * (b - 1)) * dyadicWeight (d * s) * dyadicWeight (s * b)
      = dyadicWeight (s * (2 * b + 1)) := by
    apply mul_left_cancel₀ hν
    rw [h1]
    exact mul_comm _ _
  have hlin : s * (b - 1) + d * s + s * b = s * (2 * b + 1) := by
    apply dyadicWeight_injective
    rw [dW_add (s * (b - 1) + d * s) (s * b), dW_add (s * (b - 1)) (d * s)]
    exact hA
  have hfac : s * (d - 2) = 0 := by
    have hd : s * (b - 1) + d * s + s * b - s * (2 * b + 1) = s * (d - 2) := by ring
    rw [← hd, hlin]
    ring
  rcases mul_eq_zero.mp hfac with h0 | h0
  · exact absurd h0 hs
  · omega

/-- **The law forces the degree, at the standard 2D Boussinesq exponent** `boussinesqB = 1`. -/
theorem boussinesqB_forces_degree_two (s d : ℤ) (hs : s ≠ 0) (ν κ : ℝ) (hν : ν ≠ 0)
    (h : ∀ (u θ : ℤ → ℝ) (k : ℤ),
      velocityRHSDegree (ν * dyadicWeight (s * (boussinesqB - 1))) κ 1 0 d
          (scaleVelocity s boussinesqB u) (scaleTemperature s boussinesqB θ) k
        = dyadicWeight (s * (2 * boussinesqB + 1)) * velocityRHSDegree ν κ 1 0 d u θ (k - s)) :
    d = 2 :=
  boussinesq_law_forces_degree_two s boussinesqB d hs ν κ hν h

/-! ## Non-vacuity

At `d = 2` the hypothesis of `boussinesq_law_forces_degree_two` is *satisfied*: it is exactly the
general-degree scaling covariance with the exponent `s(b+1-2) = s(b-1)`.  So the forcing theorem is
not vacuous — the law does hold at `d = 2`, and the theorem says it holds nowhere else.
-/

/-- The hypothesis of `boussinesq_law_forces_degree_two` is satisfiable at `d = 2` (for every
`ν ≠ 0`, any `s ≠ 0` and any `b`). -/
example (s b : ℤ) (_hs : s ≠ 0) (ν κ : ℝ) (_hν : ν ≠ 0) :
    ∃ d : ℤ,
      (∀ (u θ : ℤ → ℝ) (k : ℤ),
        velocityRHSDegree (ν * dyadicWeight (s * (b - 1))) κ 1 0 d
            (scaleVelocity s b u) (scaleTemperature s b θ) k
          = dyadicWeight (s * (2 * b + 1)) * velocityRHSDegree ν κ 1 0 d u θ (k - s))
        ∧ d = 2 := by
  refine ⟨2, ?_, rfl⟩
  intro u θ k
  have h := velocityRHSDegree_scaling_covariant s b ν κ 1 0 2 u θ k
  have he : s * (b + 1 - 2) = s * (b - 1) := by ring
  rw [he] at h
  exact h

end Cascade

#print axioms Cascade.velocityRHSDegree_two
#print axioms Cascade.dyadicWeight_injective
#print axioms Cascade.velocityRHSDegree_scaling_covariant
#print axioms Cascade.velocityRHSDegree_scaling_covariant_two
#print axioms Cascade.boussinesq_law_forces_degree_two
#print axioms Cascade.boussinesqB_forces_degree_two
