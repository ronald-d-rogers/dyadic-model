import Cascade.BernsteinGrowth
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Stage S, rung S2: Bernstein's transfer exponent really is dominated by dissipation

`Cascade/ShellModel.lean` states the scalar inequality `N^{3/2} ≤ N²` under the name
`Cascade.transfer_le_dissipation`. Its exponent `3/2` is *hard-coded*: the file only imports
`Mathlib.Analysis.SpecialFunctions.Pow.Real` and `Mathlib.Tactic.Ring`, so nothing in it refers
to Bernstein's inequality, even though the docstring advertises the link.

This file closes that gap. The `Cascade/` library proves the real Bernstein bound

    theorem Cascade.bernstein_L2_to_Linf (f : 𝓢(V, F)) (N : ℝ) (hN : 0 ≤ N)
        (hband : ∀ x, 𝓕 f x ≠ 0 → ‖x‖ < N) :
        ‖f.toBoundedContinuousFunction‖ ≤
          Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal *
            N ^ ((Module.finrank ℝ V : ℝ) / 2) * ‖f.toLp 2 volume‖

whose transfer exponent is `(Module.finrank ℝ V : ℝ) / 2 = d/2`, with `d = finrank ℝ V` the
*actual* dimension of the ambient space. We do three things:

1. **`bernstein_exponent_le_dissipation`** — the exponent comparison `N^{d/2} ≤ N²` for `d ≤ 4`
   and `N ≥ 1`. This is the purely arithmetic statement that "the Bernstein transfer rate is
   dominated by the viscous dissipation rate".
2. **`finrank_euclideanSpace_fin_three`** and **`transfer_le_dissipation_bernstein`** — the
   physical case `d = 3`: `finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3`, hence `N^{3/2} ≤ N²`.
   Here `3/2` is *not* written literally: it is `(Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))/2`,
   the exact exponent produced by `Cascade.bernstein_L2_to_Linf`.
3. **`bernstein_L2_to_Linf_dissipation`** — the genuine composition: feeding Bernstein's
   `L² → L∞` estimate into the exponent domination yields a sup-norm bound with the
   *dissipation* exponent `N²`, valid in every dimension `d ≤ 4`.

So the arrow "Bernstein transfer is dominated by dissipation" is now an actual theorem about
`bernstein_L2_to_Linf`, not a numeric coincidence about the literal `3/2`.
-/

noncomputable section

open MeasureTheory

open scoped FourierTransform SchwartzMap ENNReal Topology

-- `[local irreducible]` does not propagate across imports, so it must be re-declared here;
-- cf. `Cascade/BernsteinGrowth.lean`.
attribute [local irreducible] Real.rpow

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **The Bernstein exponent is dominated by the dissipation exponent, in dimensions `d ≤ 4`.**

For `d ≤ 4` we have `d/2 ≤ 2`, so for `N ≥ 1` monotonicity of `x ↦ N^x` gives
`N^{d/2} ≤ N²`. Since `Real.rpow` is monotone in the exponent on `[1, ∞)`
(`Real.rpow_le_rpow_of_exponent_le`), this is the whole content: the transfer exponent
`d/2` of Bernstein's inequality is at most the dissipation exponent `2` exactly when `d ≤ 4`.
The bound is sharp — at `d = 5` one gets `N^{5/2} > N²` for `N > 1`. -/
theorem bernstein_exponent_le_dissipation {d : ℕ} (hd : d ≤ 4) (N : ℝ) (hN : 1 ≤ N) :
    N ^ ((d : ℝ) / 2) ≤ N ^ (2 : ℝ) := by
  refine Real.rpow_le_rpow_of_exponent_le hN ?_
  have hd' : (d : ℝ) ≤ 4 := by exact_mod_cast hd
  linarith

/-- The dimension of the physical space `ℝ³` in the form that Bernstein's inequality uses:
`Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3`. -/
theorem finrank_euclideanSpace_fin_three :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 :=
  finrank_euclideanSpace_fin

/-- **Transfer is dominated by dissipation, dimension `d = 3` (stage S).**

This is the exact statement of `Cascade.transfer_le_dissipation`, except that the exponent
`3/2` is no longer a literal: it is `(Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) / 2`,
i.e. the exponent `d/2` that `Cascade.bernstein_L2_to_Linf` actually produces in three
dimensions. The numerical value `3/2` is recovered from `finrank_euclideanSpace_fin_three`,
so it is *derived* from the Bernstein exponent rather than restated. -/
theorem transfer_le_dissipation_bernstein (N : ℝ) (hN : 1 ≤ N) :
    N ^ ((Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) / 2) ≤ N ^ (2 : ℝ) := by
  refine Real.rpow_le_rpow_of_exponent_le hN ?_
  rw [finrank_euclideanSpace_fin_three]
  norm_num

/-- Sanity check: the previous theorem really does specialize to the literal `N^{3/2} ≤ N²`
of `Cascade.transfer_le_dissipation`. -/
example (N : ℝ) (hN : 1 ≤ N) : N ^ ((3 : ℝ) / 2) ≤ N ^ (2 : ℝ) := by
  simpa [finrank_euclideanSpace_fin_three] using transfer_le_dissipation_bernstein N hN

/-- **The real arrow: Bernstein composed with exponent domination, in dimensions `d ≤ 4`.**

`Cascade.bernstein_L2_to_Linf` bounds the sup norm of a band-limited Schwartz function by
`√(volume (ball 0 1)) · N^{d/2} · ‖f‖₂` with `d = Module.finrank ℝ V`. When `d ≤ 4` — the
hypothesis `hf : (Module.finrank ℝ V : ℝ) / 2 ≤ 2` — the middle factor `N^{d/2}` is at most
`N²` for `N ≥ 1` by `bernstein_exponent_le_dissipation`, and multiplying by the nonnegative
factors `√(volume (ball 0 1))` and `‖f.toLp 2 volume‖` preserves the inequality. The result is
the same sup-norm estimate with Bernstein's transfer exponent *replaced by* the viscous
dissipation exponent `2`. -/
theorem bernstein_L2_to_Linf_dissipation (hf : (Module.finrank ℝ V : ℝ) / 2 ≤ 2)
    [CompleteSpace F] (f : 𝓢(V, F)) (N : ℝ) (hN : 1 ≤ N)
    (hband : ∀ x, 𝓕 f x ≠ 0 → ‖x‖ < N) :
    ‖f.toBoundedContinuousFunction‖ ≤
      Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal * N ^ (2 : ℝ) * ‖f.toLp 2 volume‖ := by
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  -- `d ≤ 4` in `ℕ`, recovered from the real exponent hypothesis `d/2 ≤ 2`.
  have hd4 : Module.finrank ℝ V ≤ 4 := by
    have : (Module.finrank ℝ V : ℝ) ≤ 4 := by linarith
    exact_mod_cast this
  -- The exponent domination `N^{d/2} ≤ N²`.
  have hNexp : N ^ ((Module.finrank ℝ V : ℝ) / 2) ≤ N ^ (2 : ℝ) :=
    bernstein_exponent_le_dissipation (d := Module.finrank ℝ V) hd4 N hN
  -- Bernstein itself.
  have hbern := Cascade.bernstein_L2_to_Linf (V := V) (F := F) f N hN0 hband
  have hsqrt_nonneg : 0 ≤ Real.sqrt (volume (Metric.ball (0 : V) 1)).toReal :=
    Real.sqrt_nonneg _
  exact hbern.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNexp hsqrt_nonneg)
      (norm_nonneg _))

end

#print axioms bernstein_exponent_le_dissipation
#print axioms finrank_euclideanSpace_fin_three
#print axioms transfer_le_dissipation_bernstein
#print axioms bernstein_L2_to_Linf_dissipation
