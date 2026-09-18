import Cascade.ConcentrationBarrier
import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option maxHeartbeats 1000000

/-!
# Bernstein's inequality (Pillar A, rung 2)

The band-limited form of the concentration barrier: if a Schwartz function's
Fourier transform is supported in a ball of radius `N`, then its `L∞` norm is
controlled by the square root of the ball's volume times its `L²` norm. For
`V = ℝ^d` the ball volume scales like `N^d`, so this is exactly the classical
`‖f‖_∞ ≲ N^{d/2} ‖f‖_2` — the place where the dimension `d` (and hence the
`d = 3` knife's edge) first enters.

## Proof chain

1. `‖f‖_∞ ≤ ‖𝓕 f‖_1`   — the core lemma (`pointwise_le_L1_fourier`), taken in sup.
2. `‖𝓕 f‖_1 ≤ √(vol (ball 0 N)) · ‖𝓕 f‖_2`  — Cauchy–Schwarz on the support
   (`norm_toLp_one_le_sqrt_measure_mul_norm_toLp_two`).
3. `‖𝓕 f‖_2 = ‖f‖_2`   — Plancherel (`norm_fourier_eq`).
-/

noncomputable section

open Real MeasureTheory
open scoped FourierTransform SchwartzMap ENNReal Topology

attribute [local irreducible] Real.rpow
attribute [local irreducible] MeasureTheory.Lp.fourierTransformₗᵢ
attribute [local irreducible] SchwartzMap.fourierTransformCLM

namespace Cascade

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **Cauchy–Schwarz with support**: the `L¹` norm of a function supported on a
measurable set `s` is bounded by `√(volume s) · ‖g‖₂`.

*Proof outline*: `‖g‖₁ = ∫ ‖g‖ = ∫_s ‖g‖ = ∫_s ‖g‖·1 ≤ (∫_s ‖g‖²)^{1/2}·(∫_s 1)^{1/2}
≤ ‖g‖₂·√(volume s)`, using `norm_toLp_one`, the support-restricted integral, and
Hölder with `p = q = 2`. -/
theorem norm_toLp_one_le_sqrt_measure_mul_norm_toLp_two
    (g : 𝓢(V, F)) {s : Set V} (hs : MeasurableSet s) (hs_finite : volume s < ⊤)
    (hsupp : ∀ x, g x ≠ 0 → x ∈ s) :
    ‖g.toLp 1‖ ≤ Real.sqrt (volume s).toReal * ‖g.toLp 2‖ := by
  rw [SchwartzMap.norm_toLp_one]
  have hzero : ∀ x, x ∉ s → ‖g x‖ = (0 : ℝ) := by
    intro x hx
    have hg : g x = 0 := by
      by_contra h
      exact hx (hsupp x h)
    simp [hg]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  let μ : Measure V := volume.restrict s
  have h_meas : AEMeasurable (fun x => ENNReal.ofReal ‖g x‖) μ :=
    (ENNReal.measurable_ofReal.comp (g.continuous.norm).measurable).aemeasurable
  have h_meas_one : AEMeasurable (fun _x => (1 : ℝ≥0∞)) μ := by
    fun_prop
  have h_holder : (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal ‖g x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
        (∫⁻ x, (1 : ℝ≥0∞) ∂μ) ^ (1 / 2 : ℝ) := by
    calc
      (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ)
          = (∫⁻ x, (ENNReal.ofReal ‖g x‖) * (1 : ℝ≥0∞) ∂μ) := by
              simp [mul_one]
      _ ≤ (∫⁻ x, (ENNReal.ofReal ‖g x‖) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ x, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
              exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ
                (p := 2) (q := 2) (by refine ⟨?_, ?_, ?_⟩ <;> norm_num : Real.HolderConjugate 2 2)
                (f := fun x => ENNReal.ofReal ‖g x‖) (g := fun _x => (1 : ℝ≥0∞)) h_meas h_meas_one
      _ = (∫⁻ x, ENNReal.ofReal ‖g x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ x, (1 : ℝ≥0∞) ∂μ) ^ (1 / 2 : ℝ) := by
              simp
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (μ := μ) (f := fun x => ‖g x‖)
    (Filter.Eventually.of_forall fun x => norm_nonneg (g x)) (g.continuous.norm).aestronglyMeasurable]
  have hfin_μ : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa [μ, MeasureTheory.Measure.restrict_apply_univ] using hs_finite
  have h_fin1 : (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ) ≠ ⊤ := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (g.integrable.norm.mono_measure MeasureTheory.Measure.restrict_le_self)
      (Filter.Eventually.of_forall fun x => norm_nonneg (g x))]
    exact ENNReal.ofReal_ne_top
  have h_int_sq_vol : Integrable (fun x => ‖g x‖ ^ (2 : ℝ)) volume :=
    (g.memLp 2 volume).integrable_norm_rpow (by norm_num) (by norm_num)
  have h_int_sq : Integrable (fun x => ‖g x‖ ^ (2 : ℝ)) μ :=
    h_int_sq_vol.mono_measure MeasureTheory.Measure.restrict_le_self
  have h_lin_sq : (∫⁻ x, ENNReal.ofReal ‖g x‖ ^ (2 : ℝ) ∂μ) =
      (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ (2 : ℝ)) ∂μ) := by
    refine MeasureTheory.lintegral_congr (f := fun x => ENNReal.ofReal ‖g x‖ ^ (2 : ℝ))
      (g := fun x => ENNReal.ofReal (‖g x‖ ^ (2 : ℝ))) (fun x => ?_)
    exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (g x)) (by norm_num : 0 ≤ (2 : ℝ))
  have h_fin2 : ((∫⁻ x, ENNReal.ofReal ‖g x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
      (∫⁻ x, (1 : ℝ≥0∞) ∂μ) ^ (1 / 2 : ℝ)) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ?_ ?_
    · refine ENNReal.rpow_ne_top_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) ?_
      rw [h_lin_sq]
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_sq
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg (g x)) 2)]
      exact ENNReal.ofReal_ne_top
    · rw [MeasureTheory.lintegral_one, MeasureTheory.Measure.restrict_apply_univ]
      refine ENNReal.rpow_ne_top_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) ?_
      exact hs_finite.ne
  have h_le := (ENNReal.toReal_le_toReal h_fin1 h_fin2).2 h_holder
  refine h_le.trans ?_
  have hμ : μ Set.univ = volume s := by
    rw [MeasureTheory.Measure.restrict_apply_univ]
  rw [ENNReal.toReal_mul, MeasureTheory.lintegral_one, hμ]
  have hsqrt_vol : ((volume s : ℝ≥0∞) ^ (1 / 2 : ℝ)).toReal = Real.sqrt (volume s).toReal := by
    rw [← ENNReal.toReal_rpow]
    rw [Real.sqrt_eq_rpow]
  have hsqrt_lin : ((∫⁻ x, ENNReal.ofReal ‖g x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)).toReal =
      Real.sqrt ((∫⁻ x, ENNReal.ofReal ‖g x‖ ^ (2 : ℝ) ∂μ).toReal) := by
    rw [← ENNReal.toReal_rpow]
    rw [Real.sqrt_eq_rpow]
  rw [hsqrt_vol, hsqrt_lin]
  rw [mul_comm (Real.sqrt (volume s).toReal) (‖g.toLp 2 volume‖)]
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  rw [h_lin_sq]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_sq
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg (g x)) 2)]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg (g x)) 2))]
  rw [SchwartzMap.norm_toLp' (p := 2) (by norm_num) (by norm_num) (μ := volume)]
  norm_num [ENNReal.toReal_ofNat]
  rw [← Real.sqrt_eq_rpow]
  refine Real.sqrt_le_sqrt ?_
  exact MeasureTheory.setIntegral_le_integral
    (by simpa [Real.rpow_natCast] using h_int_sq_vol)
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖g x‖))

/-- **Bernstein's inequality**: if `𝓕 f` is supported in the open ball of radius
`N`, then `‖f‖_∞ ≤ √(volume (ball 0 N)) · ‖f‖₂`.

Note: `F` is assumed to be a complex inner-product space (rather than just a
normed space) because the Plancherel step `h3` — that the `L²` Fourier transform
is an isometry — is only available in mathlib for `[InnerProductSpace ℂ F]`. The
measure is written explicitly as `volume` throughout to avoid a `whnf` timeout in
the `extendOfIsometry` elaboration of `𝓕 (f.toLp 2)`. -/
theorem bernstein [CompleteSpace F] (f : 𝓢(V, F)) (N : ℝ)
    (hband : ∀ x, 𝓕 f x ≠ 0 → ‖x‖ < N)
    (hs_finite : volume (Metric.ball (0 : V) N) < ⊤) :
    ‖f.toBoundedContinuousFunction‖ ≤
      Real.sqrt (volume (Metric.ball (0 : V) N)).toReal * ‖f.toLp 2 volume‖ := by
  have h1 : ‖f.toBoundedContinuousFunction‖ ≤ ‖(𝓕 f).toLp 1 volume‖ := by
    rw [BoundedContinuousFunction.norm_le (by positivity)]
    intro x
    simpa using pointwise_le_L1_fourier f x
  have h2 : ‖(𝓕 f).toLp 1 volume‖ ≤
      Real.sqrt (volume (Metric.ball (0 : V) N)).toReal * ‖(𝓕 f).toLp 2 volume‖ := by
    exact norm_toLp_one_le_sqrt_measure_mul_norm_toLp_two (𝓕 f)
      Metric.isOpen_ball.measurableSet hs_finite (by
        intro x hx
        have hx' : ‖x‖ < N := hband x hx
        simpa [Metric.mem_ball, dist_eq_norm] using hx')
  have h3 : ‖(𝓕 f).toLp 2 volume‖ = ‖f.toLp 2 volume‖ := by
    exact SchwartzMap.norm_fourier_toL2_eq f
  calc
    ‖f.toBoundedContinuousFunction‖ ≤ ‖(𝓕 f).toLp 1 volume‖ := h1
    _ ≤ Real.sqrt (volume (Metric.ball (0 : V) N)).toReal * ‖(𝓕 f).toLp 2 volume‖ := h2
    _ = Real.sqrt (volume (Metric.ball (0 : V) N)).toReal * ‖f.toLp 2 volume‖ := by rw [h3]

end Cascade

#print axioms Cascade.norm_toLp_one_le_sqrt_measure_mul_norm_toLp_two
#print axioms Cascade.bernstein
