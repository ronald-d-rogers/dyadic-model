import Cascade.Bernstein
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option maxHeartbeats 1000000

/-!
# Bernstein's inequality: the scaled `L² → L∞` and gradient forms (Pillar A, rungs A2, A3)

Starting from `Cascade.Bernstein.bernstein`, which says that for a Schwartz function `f`
whose Fourier transform is supported in `ball (0 : V) N`,

    ‖f‖_∞ ≤ √(volume (ball 0 N)) · ‖f‖₂,

we combine it with the ball-volume scaling `volume (ball 0 N) = N^d · volume (ball 0 1)`
(`Measure.addHaar_ball`) to obtain the classical Bernstein bound with the explicit dimension
power `N^{d/2}` (A2), and with the Fourier-of-derivative identity
(`SchwartzMap.fourier_lineDerivOp_eq`) plus Plancherel to obtain the gradient form
`‖∇f‖_∞ ≲ N^{1 + d/2} · ‖f‖₂` (A3).

Here `V` is a finite-dimensional real inner product space and `F` is a complex inner-product
space (the latter is required for Plancherel, cf. `Cascade/PROGRESS.md`).
-/

noncomputable section

open Real MeasureTheory
open scoped FourierTransform SchwartzMap ENNReal Topology LineDeriv

attribute [local irreducible] Real.rpow
attribute [local irreducible] MeasureTheory.Lp.fourierTransformₗᵢ
attribute [local irreducible] SchwartzMap.fourierTransformCLM

namespace Cascade

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **Ball-volume scaling (square-root form)**: for the normalized Haar measure `volume` on a
finite-dimensional real inner product space, `volume (ball 0 N) = N^d · volume (ball 0 1)`, hence

    √(volume (ball 0 N)) = N^{d/2} · √(volume (ball 0 1)).

*Proof outline*: apply `Measure.addHaar_ball`, take real parts (`ENNReal.toReal_mul`,
`ENNReal.toReal_ofReal`), then use `Real.sqrt_mul` and the computation
`√(N^d) = (N^d)^{1/2} = N^{d/2}` via `Real.sqrt_eq_rpow`, `Real.rpow_natCast`, `Real.rpow_mul`. -/
lemma sqrt_volume_ball_eq_sqrt_volume_unitBall_mul (N : ℝ) (hN : 0 ≤ N) :
    Real.sqrt (volume (Metric.ball (0 : V) N)).toReal =
      Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal *
        N ^ ((Module.finrank ℝ V : ℝ) / 2) := by
  have hvol : volume (Metric.ball (0 : V) N) =
      ENNReal.ofReal (N ^ Module.finrank ℝ V) * volume (Metric.ball (0 : V) 1) :=
    Measure.addHaar_ball (volume : Measure V) (0 : V) hN
  have htoReal : (volume (Metric.ball (0 : V) N)).toReal =
      (N ^ Module.finrank ℝ V) * (volume (Metric.ball (0 : V) 1)).toReal := by
    rw [hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hN (Module.finrank ℝ V))]
  have hsqrt_pow : Real.sqrt (N ^ Module.finrank ℝ V) = N ^ ((Module.finrank ℝ V : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast N (Module.finrank ℝ V),
      ← Real.rpow_mul hN ((Module.finrank ℝ V : ℝ)) (1 / 2 : ℝ)]
    congr 1
    ring
  calc
    Real.sqrt (volume (Metric.ball (0 : V) N)).toReal
        = Real.sqrt ((N ^ Module.finrank ℝ V) * (volume (Metric.ball (0 : V) 1)).toReal) := by
            rw [htoReal]
    _ = Real.sqrt (N ^ Module.finrank ℝ V) * Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal := by
            rw [Real.sqrt_mul (pow_nonneg hN (Module.finrank ℝ V))]
    _ = Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal *
          N ^ ((Module.finrank ℝ V : ℝ) / 2) := by
            rw [hsqrt_pow, mul_comm]

/-- **Bernstein's inequality, `L² → L∞` form (A2)**: if `𝓕 f` is supported in the ball of radius
`N`, then

    ‖f‖_∞ ≤ C_d · N^{d/2} · ‖f‖₂,

where `C_d = √(volume (ball 0 1))` is the dimension-dependent constant (for `V = ℝ^d` this is
`π^{d/4}/√Γ(d/2+1)`). -/
theorem bernstein_L2_to_Linf [CompleteSpace F] (f : 𝓢(V, F)) (N : ℝ) (hN : 0 ≤ N)
    (hband : ∀ x, 𝓕 f x ≠ 0 → ‖x‖ < N) :
    ‖f.toBoundedContinuousFunction‖ ≤
      Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal *
        N ^ ((Module.finrank ℝ V : ℝ) / 2) * ‖f.toLp 2 volume‖ := by
  have hbern := bernstein f N hband
    (measure_ball_lt_top (μ := volume) (x := (0 : V)) (r := N))
  calc
    ‖f.toBoundedContinuousFunction‖ ≤
        Real.sqrt (volume (Metric.ball (0 : V) N)).toReal * ‖f.toLp 2 volume‖ := hbern
    _ = Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal *
          N ^ ((Module.finrank ℝ V : ℝ) / 2) * ‖f.toLp 2 volume‖ := by
            rw [sqrt_volume_ball_eq_sqrt_volume_unitBall_mul N hN]

/-! ### A3: the gradient form of Bernstein's inequality

The gradient (Fréchet derivative) of a band-limited `f` is controlled by `N^{1 + d/2}`: on the
frequency ball `‖ξ‖ < N` the derivative multiplier `2πi·⟨ξ,m⟩` has size `≤ 2π·N·‖m‖`. -/

/-- Pointwise support bound: on the frequency ball `‖x‖ < N`, the inner-product multiplier
`⟨x,m⟩` has size `≤ N·‖m‖`. -/
lemma abs_inner_mul_norm_le (m : V) (N : ℝ) (hN : 0 ≤ N) (f : 𝓢(V, F))
    (hband : ∀ x, 𝓕 f x ≠ 0 → ‖x‖ < N) :
    ∀ x, |inner ℝ x m| * ‖𝓕 f x‖ ≤ N * ‖m‖ * ‖𝓕 f x‖ := by
  intro x
  by_cases hx : 𝓕 f x = 0
  · simp [hx]
  · have hlt : ‖x‖ < N := hband x hx
    have hcs : ‖inner ℝ x m‖ ≤ ‖x‖ * ‖m‖ := norm_inner_le_norm x m
    have habs : |inner ℝ x m| ≤ N * ‖m‖ := by
      rw [← Real.norm_eq_abs]
      exact hcs.trans (mul_le_mul_of_nonneg_right hlt.le (norm_nonneg m))
    exact mul_le_mul_of_nonneg_right habs (norm_nonneg (𝓕 f x))

/-- The `L¹` norm of the Fourier transform of the line derivative `∂_m f` is controlled by
`2π·‖m‖·N·‖𝓕 f‖₁`, using `𝓕 (∂_m f) = (2πi) • (⟨·,m⟩ · 𝓕 f)` (`SchwartzMap.fourier_lineDerivOp_eq`)
and the support bound `|⟨x,m⟩| ≤ N·‖m‖` on `ball 0 N`. -/
lemma norm_toLp_one_fourier_lineDeriv_le (f : 𝓢(V, F)) (m : V) (N : ℝ) (hN : 0 ≤ N)
    (hband : ∀ x, 𝓕 f x ≠ 0 → ‖x‖ < N) :
    ‖(𝓕 (∂_{m} f)).toLp 1 volume‖ ≤ 2 * π * ‖m‖ * N * ‖(𝓕 f).toLp 1 volume‖ := by
  have hpoint : ∀ x, |inner ℝ x m| * ‖𝓕 f x‖ ≤ N * ‖m‖ * ‖𝓕 f x‖ :=
    abs_inner_mul_norm_le m N hN f hband
  have hint_dom : Integrable (fun x => ‖m‖ * (‖x‖ ^ 1 * ‖𝓕 f x‖)) volume :=
    ((𝓕 f).integrable_pow_mul volume 1).const_mul ‖m‖
  have hint : Integrable (fun x => |inner ℝ x m| * ‖𝓕 f x‖) volume := by
    refine hint_dom.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · fun_prop
    · have hcs : ‖inner ℝ x m‖ ≤ ‖x‖ * ‖m‖ := norm_inner_le_norm x m
      have habs : |inner ℝ x m| ≤ ‖x‖ * ‖m‖ := by simpa [Real.norm_eq_abs] using hcs
      calc
        ‖|inner ℝ x m| * ‖𝓕 f x‖‖ = |inner ℝ x m| * ‖𝓕 f x‖ := by
          rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
        _ ≤ (‖x‖ * ‖m‖) * ‖𝓕 f x‖ := mul_le_mul_of_nonneg_right habs (norm_nonneg _)
        _ = ‖m‖ * (‖x‖ * ‖𝓕 f x‖) := by ring
        _ ≤ ‖m‖ * (‖x‖ ^ 1 * ‖𝓕 f x‖) := by rw [pow_one]
  have hint' : Integrable (fun x => N * ‖m‖ * ‖𝓕 f x‖) volume :=
    ((𝓕 f).integrable.norm).const_mul (N * ‖m‖)
  calc
    ‖(𝓕 (∂_{m} f)).toLp 1 volume‖
        = ∫ x, ‖(𝓕 (∂_{m} f)) x‖ ∂volume := by rw [SchwartzMap.norm_toLp_one]
    _ = ∫ x, 2 * π * (|inner ℝ x m| * ‖𝓕 f x‖) ∂volume := by
        congr 1 with x
        rw [SchwartzMap.fourier_lineDerivOp_eq f m]
        simp only [ContinuousLinearMap.smul_apply]
        rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop : (fun y => inner ℝ y m).HasTemperateGrowth)]
        rw [norm_smul, norm_smul]
        have hnormI : ‖(2 * π * Complex.I : ℂ)‖ = 2 * π := by
          rw [Complex.norm_mul, Complex.norm_I, mul_one]
          norm_cast
          exact RCLike.norm_of_nonneg (mul_nonneg zero_le_two Real.pi_pos.le)
        rw [hnormI, Real.norm_eq_abs]
    _ = 2 * π * ∫ x, |inner ℝ x m| * ‖𝓕 f x‖ ∂volume := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ 2 * π * ∫ x, N * ‖m‖ * ‖𝓕 f x‖ ∂volume := by
        exact mul_le_mul_of_nonneg_left
          (MeasureTheory.integral_mono hint hint' hpoint) (by positivity)
    _ = 2 * π * (N * ‖m‖) * ∫ x, ‖𝓕 f x‖ ∂volume := by
        rw [MeasureTheory.integral_const_mul]
        ring
    _ = 2 * π * ‖m‖ * N * ‖(𝓕 f).toLp 1 volume‖ := by
        rw [SchwartzMap.norm_toLp_one]
        ring

/-- **Bernstein's inequality, directional (line) derivative form (A3)**: if `𝓕 f` is supported in
`ball (0 : V) N`, then for every direction `m`,

    ‖∂_m f‖_∞ ≤ C_d · 2π · ‖m‖ · N^{1 + d/2} · ‖f‖₂.

This is the standard `‖∇f‖_∞ ≲ N^{1+d/2} ‖f‖₂`, written for the directional (line) derivatives
whose sup over the unit sphere is the gradient norm. -/
theorem bernstein_lineDeriv [CompleteSpace F] (f : 𝓢(V, F)) (m : V) (N : ℝ) (hN : 0 ≤ N)
    (hband : ∀ x, 𝓕 f x ≠ 0 → ‖x‖ < N) :
    ‖(∂_{m} f).toBoundedContinuousFunction‖ ≤
      Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal * (2 * π) * ‖m‖ *
        N ^ (1 + (Module.finrank ℝ V : ℝ) / 2) * ‖f.toLp 2 volume‖ := by
  have hrpow : N * N ^ ((Module.finrank ℝ V : ℝ) / 2) =
      N ^ (1 + (Module.finrank ℝ V : ℝ) / 2) := by
    nth_rewrite 1 [← Real.rpow_one N]
    exact (Real.rpow_add' hN (by positivity)).symm
  have h1 : ‖(∂_{m} f).toBoundedContinuousFunction‖ ≤ ‖(𝓕 (∂_{m} f)).toLp 1 volume‖ := by
    rw [BoundedContinuousFunction.norm_le (by positivity)]
    intro x
    simpa using pointwise_le_L1_fourier (∂_{m} f) x
  have h2 : ‖(𝓕 (∂_{m} f)).toLp 1 volume‖ ≤ 2 * π * ‖m‖ * N * ‖(𝓕 f).toLp 1 volume‖ :=
    norm_toLp_one_fourier_lineDeriv_le f m N hN hband
  have h3 : ‖(𝓕 f).toLp 1 volume‖ ≤
      Real.sqrt (volume (Metric.ball (0 : V) N)).toReal * ‖(𝓕 f).toLp 2 volume‖ :=
    norm_toLp_one_le_sqrt_measure_mul_norm_toLp_two (𝓕 f)
      Metric.isOpen_ball.measurableSet (measure_ball_lt_top (μ := volume) (x := (0 : V)) (r := N))
      (by
        intro x hx
        have hx' : ‖x‖ < N := hband x hx
        simpa [Metric.mem_ball, dist_eq_norm] using hx')
  have h4 : ‖(𝓕 f).toLp 2 volume‖ = ‖f.toLp 2 volume‖ := SchwartzMap.norm_fourier_toL2_eq f
  calc
    ‖(∂_{m} f).toBoundedContinuousFunction‖
        ≤ ‖(𝓕 (∂_{m} f)).toLp 1 volume‖ := h1
    _ ≤ 2 * π * ‖m‖ * N * ‖(𝓕 f).toLp 1 volume‖ := h2
    _ ≤ 2 * π * ‖m‖ * N *
          (Real.sqrt (volume (Metric.ball (0 : V) N)).toReal * ‖(𝓕 f).toLp 2 volume‖) := by
            exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2 * π * ‖m‖ * N * Real.sqrt (volume (Metric.ball (0 : V) N)).toReal *
          ‖f.toLp 2 volume‖ := by
            rw [h4]
            ring
    _ = Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal * (2 * π) * ‖m‖ *
          N ^ (1 + (Module.finrank ℝ V : ℝ) / 2) * ‖f.toLp 2 volume‖ := by
            rw [sqrt_volume_ball_eq_sqrt_volume_unitBall_mul N hN, ← hrpow]
            ring

/-- **Bernstein's inequality, gradient form (A3)**: if `𝓕 f` is supported in `ball (0 : V) N`,
then the `L∞` norm of the Fréchet derivative (gradient) is controlled by `C_d · 2π · N^{1 + d/2} ·
‖f‖₂`. This is the operator-norm form of `bernstein_lineDeriv`, obtained via
`ContinuousLinearMap.opNorm_le_bound`. -/
theorem bernstein_gradient [CompleteSpace F] (f : 𝓢(V, F)) (N : ℝ) (hN : 0 ≤ N)
    (hband : ∀ x, 𝓕 f x ≠ 0 → ‖x‖ < N) :
    ‖(SchwartzMap.fderivCLM ℝ V F f).toBoundedContinuousFunction‖ ≤
      Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal * (2 * π) *
        N ^ (1 + (Module.finrank ℝ V : ℝ) / 2) * ‖f.toLp 2 volume‖ := by
  let M : ℝ := Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal * (2 * π) *
    N ^ (1 + (Module.finrank ℝ V : ℝ) / 2) * ‖f.toLp 2 volume‖
  have hM : 0 ≤ M := by
    positivity
  rw [BoundedContinuousFunction.norm_le hM]
  intro x
  have hx := ContinuousLinearMap.opNorm_le_bound (fderiv ℝ (⇑f) x) hM (by
    intro m
    calc
      ‖(fderiv ℝ (⇑f) x) m‖ = ‖(∂_{m} f) x‖ := by rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
      _ ≤ ‖(∂_{m} f).toBoundedContinuousFunction‖ := by
            rw [← SchwartzMap.toBoundedContinuousFunction_apply (∂_{m} f) x]
            exact BoundedContinuousFunction.norm_coe_le_norm ((∂_{m} f).toBoundedContinuousFunction) x
      _ ≤ Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal * (2 * π) * ‖m‖ *
            N ^ (1 + (Module.finrank ℝ V : ℝ) / 2) * ‖f.toLp 2 volume‖ :=
              bernstein_lineDeriv f m N hN hband
      _ = M * ‖m‖ := by
            dsimp [M]
            ring)
  simpa [SchwartzMap.fderivCLM_apply] using hx

end Cascade

#print axioms Cascade.sqrt_volume_ball_eq_sqrt_volume_unitBall_mul
#print axioms Cascade.bernstein_L2_to_Linf
#print axioms Cascade.abs_inner_mul_norm_le
#print axioms Cascade.norm_toLp_one_fourier_lineDeriv_le
#print axioms Cascade.bernstein_lineDeriv
#print axioms Cascade.bernstein_gradient
