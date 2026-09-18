import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.LpSpace

set_option maxHeartbeats 1000000

/-!
# The concentration barrier (Pillar A of the "criticality skeleton")

This module begins the formalization of the Fourier **concentration barrier**:
limiting a function's *frequency* spread forces a minimum *spatial* spread, which
caps how concentrated (and hence how large pointwise) the function can be.

The core fact used by both Bernstein's inequality and the Heisenberg uncertainty
principle is:

> the pointwise value `‖f x‖` of a Schwartz function is bounded by the `L¹` norm
> `‖𝓕 f‖₁` of its Fourier transform.

The forward half (`‖𝓕 f x‖ ≤ ‖f‖₁`) is mathlib's
`norm_fourier_apply_le_toLp_one`. The inverse half is stated and proved here.
Together with Plancherel (`‖𝓕 f‖₂ = ‖f‖₂`) this is exactly what makes the
unforced frequency cascade subcritical against viscous dissipation in 3D.
-/

noncomputable section

open Real MeasureTheory
open scoped FourierTransform SchwartzMap Topology

-- The Schwartz Fourier transform unfolds into a huge `mkCLM` construction; keep it opaque
-- so that elaborating `𝓕 f` in proofs does not trigger a heartbeat explosion.
attribute [local irreducible] SchwartzMap.fourierTransformCLM

namespace Cascade

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The inverse Fourier transform satisfies the same `L¹ → L∞` bound as the
forward one: its pointwise value is controlled by the `L¹` norm of its input. -/
theorem fourierInv_apply_le_toLp_one (f : 𝓢(V, F)) (x : V) :
    ‖𝓕⁻ f x‖ ≤ ‖f.toLp 1‖ := by
  rw [SchwartzMap.fourierInv_apply_eq]
  change ‖(𝓕 f) (-x)‖ ≤ ‖f.toLp 1‖
  exact SchwartzMap.norm_fourier_apply_le_toLp_one f (-x)

/-- **Core concentration lemma**: a Schwartz function's pointwise value is bounded
by the `L¹` norm of its Fourier transform. In words: if the frequency content has
finite total mass `‖𝓕 f‖₁`, the function cannot exceed that mass pointwise.

*Proof outline*: `f = 𝓕⁻ (𝓕 f)` by Fourier inversion, then apply
`fourierInv_apply_le_toLp_one`. -/
theorem pointwise_le_L1_fourier [CompleteSpace F] (f : 𝓢(V, F)) (x : V) :
    ‖f x‖ ≤ ‖(𝓕 f).toLp 1‖ := by
  have h := fourierInv_apply_le_toLp_one (𝓕 f) x
  rwa [FourierTransform.fourierInv_fourier_eq] at h

end Cascade

#print axioms Cascade.fourierInv_apply_le_toLp_one
#print axioms Cascade.pointwise_le_L1_fourier
