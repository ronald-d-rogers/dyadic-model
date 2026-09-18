import Cascade.Amplitude
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Order.IntermediateValue

/-!
# Stage G — the wavevector phase and the steerable coupling

`Cascade/Lacunary.lean` reduces the dyadic Boussinesq model to the amplitude pair `(Theta, Omega)`
of `Cascade/Amplitude.lean`:

    Theta' = thetaBar_{n-1} Omega,      Omega' = 2^n kappa Theta,

with the **constant** buoyancy coupling `b = 2^n kappa`. That reduction is exact for the ansatz it
postulates, but the ansatz has thrown away the **geometry of the wave**: the lacunary packet is
described only by its amplitudes `(a, b)`, and the wavevector it sits on — its magnitude *and its
direction* — never appears. The coupling `2^n kappa` is then a frozen number.

This file restores the phase. It formalises the page-4 system of Alpöge–Buckmaster (their
eq. (3.2)) for the wavevector `zeta ∈ R²` and the reduced amplitudes `(Theta, Omega)`:

    zeta' = -D^T zeta,   Theta' = -(J zeta · G)/(lam |zeta|²) · Omega,   Omega' = lam zeta_1 Theta,

where `J` is the 90° rotation, `G` the frozen background temperature gradient, `D` the frozen
background velocity gradient and `lam` the frequency. Two structural points are made precise here.

* **The wavevector rotates.** For the `alpha' J` part of AB's background gradient `D_{<q}` (their
  eq. (3.3)), `D t = alpha' t • J` with `D^T = -D`, so `zeta' = -D^T zeta = alpha' • (J zeta)`. The
  solution is `zeta t = rotR (alpha t) *ᵥ zeta0`: the rotation matrix is the exponential of
  `alpha J` (`rotJ * rotR alpha` is the angular derivative of `rotR alpha`, `rotJ_sq = -1`), and
  the wavevector is simply *steered* by the accumulated background rotation `alpha`. This is
  `phase_steering_component`.

* **The coupling is a cosine.** The buoyancy coupling is the first (gravity-direction) component
  `b = lam zeta_1 = abVortCoeff lam zeta`, and under steering it becomes

      abVortCoeff lam (rotR alpha *ᵥ zeta0) = lam (zeta0 0 cos alpha - zeta0 1 sin alpha),

  a pure cosine in the steering angle, bounded by `|lam| |zeta0|` (`phase_coupling_cosine`,
  `phase_coupling_bound`). A half-turn flips its sign (`phase_flip`), and it sweeps the whole
  interval `[-|lam| |zeta0|, |lam| |zeta0|]` (`phase_flip_quantitative`).

Non-degeneracy of AB's two coefficients is also recorded: their product
`abTempCoeff lam zeta G * abVortCoeff lam zeta = -(((J zeta)·G) zeta_1) / |zeta|²` is independent
of `lam` (`ab_product`), and the temperature numerator is invariant under a *simultaneous*
rotation of the wavevector and the frozen gradient,
`(J (rotR alpha zeta0))·(rotR alpha G) = (J zeta0)·G` (`rotJ_mulVec_dot_rotR`). (With the gradient
held fixed the numerator is *not* invariant: the steering rotation changes the angle between
`J zeta0` and `G`, so it changes the temperature coupling as well as the buoyancy one.)

**Consequence (prose, not a theorem).** The scalar obstruction of the previous stages assumes a
constant-coefficient amplitude pair: the sign of `ab` is frozen for all time, so growth versus
oscillation is decided once and for all by the initial data. With the phase restored that
hypothesis *fails*: `b = abVortCoeff lam zeta` is a continuously steerable cosine, so the
background rotation `alpha` can drive the coupling through zero and reverse it, and with `a`
unchanged the sign of the instantaneous Rayleigh–Taylor product `ab` — hence growth versus
oscillation, cf. `Cascade/Amplitude.lean` — is *controllable* rather than fixed. This is exactly
the geometry the scalar model deleted.

**Scope.** This is the phase of a *single* wavevector. A full shell-model realisation — one
wavevector per octave, each steered by the accumulated background of AB eq. (3.3), with the
`lam |zeta|²` denominators and the `G`, `D` built from the lower octaves — is the next step and is
not claimed here.

## Norm convention and a type-theoretic correction

On `Fin 2 → R` Lean's ambient `‖·‖` is the **sup norm** (`Pi.norm_def`, i.e.
`Finset.univ.sup fun i => ‖x i‖`), *not* the Euclidean norm; `Cascade/Amplitude.lean` uses only
matrix algebra and never relies on this. Since AB's `|zeta|²` is the Euclidean length squared,
this file introduces the explicit Euclidean length `l2norm zeta = sqrt (zeta0² + zeta1²)` and
states the length-bounded claims with it. The exact `‖·‖`-statement is refuted by
`rotR_norm_preserving_supNorm_counterexample` below (`x = ![1,1]`, `alpha = pi/4` gives
`‖rotR alpha *ᵥ x‖ = sqrt 2 ≠ 1 = ‖x‖`).

A second correction: `Matrix (Fin 2) (Fin 2) R` carries **no `TopologicalSpace` instance** in
Mathlib (deliberately: matrix multiplication is not submultiplicative for the product norm), so
`HasDerivAt` is not even well-formed at matrix type. The steering lemma is therefore stated
componentwise, `phase_steering_component`, with each component a scalar chain-rule identity; the
algebraic statements elsewhere use `Matrix` freely.
-/

noncomputable section

namespace Cascade

open scoped Matrix

/-! ## The rotations -/

/-- The 90° rotation `J`, as a `2 × 2` real matrix. -/
def rotJ : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The rotation by angle `alpha`, as a `2 × 2` real matrix. -/
def rotR (alpha : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos alpha, -Real.sin alpha; Real.sin alpha, Real.cos alpha]

/-- The Euclidean (L²) length of a two-vector, `sqrt (zeta0² + zeta1²)`. This is AB's `|zeta|`.

It is stated explicitly because Lean's ambient norm on `Fin 2 → ℝ` is the sup norm; see the
module docstring. -/
def l2norm (zeta : Fin 2 → ℝ) : ℝ := Real.sqrt (zeta 0 ^ 2 + zeta 1 ^ 2)

/-- `rotJ` is skew-symmetric: `J^T = -J` (so `D = alpha' J` satisfies `D^T = -D`). -/
theorem rotJ_transpose : rotJᵀ = -rotJ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rotJ, Matrix.transpose_apply]

/-- The action of the 90° rotation on a vector: `J zeta = (-zeta_1, zeta_0)`. -/
theorem rotJ_mulVec (zeta : Fin 2 → ℝ) : rotJ *ᵥ zeta = ![-(zeta 1), zeta 0] := by
  ext i
  fin_cases i <;>
    simp [rotJ, Matrix.mulVec_apply, dotProduct, Fin.sum_univ_two]

/-- `J² = -1`: two quarter turns are a half turn. -/
theorem rotJ_sq : rotJ * rotJ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rotJ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The zero rotation is the identity. -/
theorem rotR_zero : rotR 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rotR]

/-- First component of a rotated vector. -/
theorem rotR_mulVec_zero (alpha : ℝ) (zeta0 : Fin 2 → ℝ) :
    (rotR alpha *ᵥ zeta0) 0 = zeta0 0 * Real.cos alpha - zeta0 1 * Real.sin alpha := by
  rw [Matrix.mulVec_apply, dotProduct, Fin.sum_univ_two]
  simp [rotR]
  ring

/-- Second component of a rotated vector. -/
theorem rotR_mulVec_one (alpha : ℝ) (zeta0 : Fin 2 → ℝ) :
    (rotR alpha *ᵥ zeta0) 1 = zeta0 0 * Real.sin alpha + zeta0 1 * Real.cos alpha := by
  rw [Matrix.mulVec_apply, dotProduct, Fin.sum_univ_two]
  simp [rotR]
  ring

/-- **`J` generates the rotation.** The angular derivative of `rotR` is left multiplication by
`J`: `J * rotR alpha = !![−sin alpha, −cos alpha; cos alpha, −sin alpha]`, whose entries are the
derivatives of the entries of `rotR`. This is the infinitesimal form of
`rotR alpha = exp (alpha J)`. -/
theorem rotJ_mul_rotR (alpha : ℝ) :
    rotJ * rotR alpha = !![-(Real.sin alpha), -(Real.cos alpha); Real.cos alpha, -(Real.sin alpha)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotJ, rotR, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-! ## The steering lemma -/

/-- **Steering lemma, componentwise.** With `D = alpha' • rotJ` (so `Dᵀ = -D`), the rotating
wavevector `zeta(s) = rotR (alpha s) *ᵥ zeta0` satisfies `zeta' = -Dᵀ zeta = alpha' • (rotJ *ᵥ zeta)`
in each component: `(J zeta) 0 = -(zeta 1)` and `(J zeta) 1 = zeta 0`.

The statement is componentwise rather than bundled because `Matrix (Fin 2) (Fin 2) R` carries no
topological (norm) instance in this pin, so `HasDerivAt` is not well-formed at matrix type. Each
component is the scalar chain rule applied to `cos` and `sin`. The only hypothesis is that `alpha`
is differentiable at `t` with derivative `alpha' t`; there is no hypothesis on `zeta0` (the dummy
`∀ s, zeta0 = zeta0` of the sketch is vacuous and has been dropped). -/
theorem phase_steering_component (α α' : ℝ → ℝ) (ζ₀ : Fin 2 → ℝ) (t : ℝ)
    (hα : HasDerivAt α (α' t) t) (i : Fin 2) :
    HasDerivAt (fun s => (rotR (α s) *ᵥ ζ₀) i)
      (α' t * ((rotJ *ᵥ (rotR (α t) *ᵥ ζ₀)) i)) t := by
  have hsin : HasDerivAt (fun s => Real.sin (α s)) (Real.cos (α t) * α' t) t :=
    (Real.hasDerivAt_sin (α t)).comp t hα
  have hcos : HasDerivAt (fun s => Real.cos (α s)) (-Real.sin (α t) * α' t) t :=
    (Real.hasDerivAt_cos (α t)).comp t hα
  have h0 : HasDerivAt (fun s => ζ₀ 0 * Real.cos (α s) - ζ₀ 1 * Real.sin (α s))
      (ζ₀ 0 * (-Real.sin (α t) * α' t) - ζ₀ 1 * (Real.cos (α t) * α' t)) t :=
    (hcos.const_mul (ζ₀ 0)).sub (hsin.const_mul (ζ₀ 1))
  have h1 : HasDerivAt (fun s => ζ₀ 0 * Real.sin (α s) + ζ₀ 1 * Real.cos (α s))
      (ζ₀ 0 * (Real.cos (α t) * α' t) + ζ₀ 1 * (-Real.sin (α t) * α' t)) t :=
    (hsin.const_mul (ζ₀ 0)).add (hcos.const_mul (ζ₀ 1))
  have hJ0 : ∀ v : Fin 2 → ℝ, (rotJ *ᵥ v) 0 = -(v 1) := by
    intro v
    rw [rotJ_mulVec]
    rfl
  have hJ1 : ∀ v : Fin 2 → ℝ, (rotJ *ᵥ v) 1 = v 0 := by
    intro v
    rw [rotJ_mulVec]
    rfl
  fin_cases i
  · show HasDerivAt (fun s => (rotR (α s) *ᵥ ζ₀) 0)
      (α' t * ((rotJ *ᵥ (rotR (α t) *ᵥ ζ₀)) 0)) t
    have hfun : (fun s => (rotR (α s) *ᵥ ζ₀) 0)
        = fun s => ζ₀ 0 * Real.cos (α s) - ζ₀ 1 * Real.sin (α s) := by
      funext s
      rw [rotR_mulVec_zero]
    have hval : α' t * ((rotJ *ᵥ (rotR (α t) *ᵥ ζ₀)) 0)
        = ζ₀ 0 * (-Real.sin (α t) * α' t) - ζ₀ 1 * (Real.cos (α t) * α' t) := by
      rw [hJ0, rotR_mulVec_one]
      ring
    rw [hfun, hval]
    exact h0
  · show HasDerivAt (fun s => (rotR (α s) *ᵥ ζ₀) 1)
      (α' t * ((rotJ *ᵥ (rotR (α t) *ᵥ ζ₀)) 1)) t
    have hfun : (fun s => (rotR (α s) *ᵥ ζ₀) 1)
        = fun s => ζ₀ 0 * Real.sin (α s) + ζ₀ 1 * Real.cos (α s) := by
      funext s
      rw [rotR_mulVec_one]
    have hval : α' t * ((rotJ *ᵥ (rotR (α t) *ᵥ ζ₀)) 1)
        = ζ₀ 0 * (Real.cos (α t) * α' t) + ζ₀ 1 * (-Real.sin (α t) * α' t) := by
      rw [hJ1, rotR_mulVec_zero]
      ring
    rw [hfun, hval]
    exact h1

/-! ## Length -/

/-- Squaring the Euclidean length: `|zeta|² = zeta0² + zeta1²` for `zeta ≠ 0`. -/
theorem l2norm_sq (zeta : Fin 2 → ℝ) (hzeta : zeta ≠ 0) : l2norm zeta ^ 2 = zeta 0 ^ 2 + zeta 1 ^ 2 := by
  rw [l2norm, Real.sq_sqrt]
  by_contra h
  push_neg at h
  have h0 : zeta 0 = 0 := by nlinarith [sq_nonneg (zeta 0), sq_nonneg (zeta 1)]
  have h1 : zeta 1 = 0 := by nlinarith [sq_nonneg (zeta 0), sq_nonneg (zeta 1)]
  exact hzeta (by funext i; fin_cases i <;> simp [h0, h1])

/-- A nonzero vector has nonzero Euclidean length. -/
theorem l2norm_ne_zero (zeta : Fin 2 → ℝ) (hzeta : zeta ≠ 0) : l2norm zeta ≠ 0 := by
  intro h
  have hsq : zeta 0 ^ 2 + zeta 1 ^ 2 = 0 := by
    have h0 : l2norm zeta ^ 2 = 0 := by rw [h]; norm_num
    rw [l2norm, Real.sq_sqrt (by positivity)] at h0
    exact h0
  have h0 : zeta 0 = 0 := by nlinarith [sq_nonneg (zeta 0), sq_nonneg (zeta 1)]
  have h1 : zeta 1 = 0 := by nlinarith [sq_nonneg (zeta 0), sq_nonneg (zeta 1)]
  exact hzeta (by funext i; fin_cases i <;> simp [h0, h1])

/-- **Rotations preserve the Euclidean length**: `|rotR alpha zeta0| = |zeta0|`.

(The ambient sup norm `‖·‖` is *not* preserved; see
`rotR_norm_preserving_supNorm_counterexample`.) -/
theorem rotR_norm_preserving (alpha : ℝ) (zeta0 : Fin 2 → ℝ) :
    l2norm (rotR alpha *ᵥ zeta0) = l2norm zeta0 := by
  have hsq : l2norm (rotR alpha *ᵥ zeta0) ^ 2 = l2norm zeta0 ^ 2 := by
    rw [l2norm, l2norm, rotR_mulVec_zero, rotR_mulVec_one, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    nlinarith [Real.sin_sq_add_cos_sq alpha]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have hrn : 0 ≤ l2norm (rotR alpha *ᵥ zeta0) := Real.sqrt_nonneg _
    rw [h] at hrn
    have hz : l2norm zeta0 = 0 := le_antisymm (by simpa only [neg_nonneg] using hrn) (Real.sqrt_nonneg _)
    rw [hz] at h ⊢
    simpa using h

/-- The Euclidean lengths multiply: `|(a,b)| |zeta| = sqrt ((a²+b²)(zeta0²+zeta1²))`. -/
theorem l2norm_mul_sqrt (a b : ℝ) (zeta : Fin 2 → ℝ) :
    l2norm ![a, b] * l2norm zeta
      = Real.sqrt ((a ^ 2 + b ^ 2) * (zeta 0 ^ 2 + zeta 1 ^ 2)) := by
  have h1 : l2norm ![a, b] = Real.sqrt (a ^ 2 + b ^ 2) := by simp [l2norm]
  rw [h1, l2norm, ← Real.sqrt_mul (show (0:ℝ) ≤ a ^ 2 + b ^ 2 by positivity)]

/-- The rotation matrix's first row is a Euclidean unit vector:
`|(cos alpha, -sin alpha)| = 1`. -/
theorem l2norm_rotR_row_zero (alpha : ℝ) :
    l2norm ![Real.cos alpha, -(Real.sin alpha)] = 1 := by
  have h : Real.cos alpha ^ 2 + (-(Real.sin alpha)) ^ 2 = 1 := by
    rw [neg_sq, add_comm, Real.sin_sq_add_cos_sq]
  simp only [l2norm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [h, Real.sqrt_one]

/-- An elementary Cauchy–Schwarz bound: `|a zeta_0 + b zeta_1| ≤ |(a,b)| |zeta|` in `R²`. -/
theorem abs_mul_add_mul_le (a b : ℝ) (zeta : Fin 2 → ℝ) :
    |a * zeta 0 + b * zeta 1| ≤ l2norm ![a, b] * l2norm zeta := by
  have hcs : (a * zeta 0 + b * zeta 1) ^ 2 ≤ (a ^ 2 + b ^ 2) * (zeta 0 ^ 2 + zeta 1 ^ 2) := by
    nlinarith [sq_nonneg (a * zeta 1 - b * zeta 0)]
  calc |a * zeta 0 + b * zeta 1|
      = Real.sqrt ((a * zeta 0 + b * zeta 1) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((a ^ 2 + b ^ 2) * (zeta 0 ^ 2 + zeta 1 ^ 2)) := Real.sqrt_le_sqrt hcs
    _ = l2norm ![a, b] * l2norm zeta := (l2norm_mul_sqrt a b zeta).symm

/-- Component bound: `|zeta i| ≤ |zeta|`. -/
theorem abs_apply_le_l2norm (zeta : Fin 2 → ℝ) (i : Fin 2) : |zeta i| ≤ l2norm zeta := by
  have h0 : zeta 0 ^ 2 ≤ zeta 0 ^ 2 + zeta 1 ^ 2 := by nlinarith [sq_nonneg (zeta 1)]
  have h1' : zeta 1 ^ 2 ≤ zeta 0 ^ 2 + zeta 1 ^ 2 := by nlinarith [sq_nonneg (zeta 0)]
  have h1 : zeta i ^ 2 ≤ zeta 0 ^ 2 + zeta 1 ^ 2 := by
    fin_cases i
    · exact h0
    · exact h1'
  calc |zeta i| = Real.sqrt (zeta i ^ 2) := by rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (zeta 0 ^ 2 + zeta 1 ^ 2) := Real.sqrt_le_sqrt h1
    _ = l2norm zeta := rfl

/-! ## AB's coefficients and their product -/

/-- AB's temperature coupling `a = -(J zeta · G)/(lam |zeta|²)`. -/
def abTempCoeff (lam : ℝ) (zeta G : Fin 2 → ℝ) : ℝ :=
  -(((rotJ *ᵥ zeta) ⬝ᵥ G) / (lam * l2norm zeta ^ 2))

/-- AB's buoyancy coupling `b = lam zeta_0` (the gravity-direction component). -/
def abVortCoeff (lam : ℝ) (zeta : Fin 2 → ℝ) : ℝ := lam * zeta 0

/-- **The product of AB's couplings is independent of `lam`.** -/
theorem ab_product (lam : ℝ) (hlam : lam ≠ 0) (zeta G : Fin 2 → ℝ) (hzeta : zeta ≠ 0) :
    abTempCoeff lam zeta G * abVortCoeff lam zeta = -(((rotJ *ᵥ zeta) ⬝ᵥ G) * zeta 0) / l2norm zeta ^ 2 := by
  have hne : lam * l2norm zeta ^ 2 ≠ 0 :=
    mul_ne_zero hlam (pow_ne_zero 2 (l2norm_ne_zero zeta hzeta))
  rw [abTempCoeff, abVortCoeff]
  field_simp

/-- **The coupling is a steerable cosine.** The buoyancy coupling of the steered wavevector is
`lam (zeta0 0 cos alpha - zeta0 1 sin alpha)`: a pure cosine in the steering angle with amplitude
`lam |zeta0|`. -/
theorem phase_coupling_cosine (lam alpha : ℝ) (zeta0 : Fin 2 → ℝ) :
    abVortCoeff lam (rotR alpha *ᵥ zeta0) = lam * (zeta0 0 * Real.cos alpha - zeta0 1 * Real.sin alpha) := by
  rw [abVortCoeff, rotR_mulVec_zero]

/-- **The steerable coupling is bounded by `|lam| |zeta0|`.** -/
theorem phase_coupling_bound (lam alpha : ℝ) (zeta0 : Fin 2 → ℝ) :
    |abVortCoeff lam (rotR alpha *ᵥ zeta0)| ≤ |lam| * l2norm zeta0 := by
  rw [phase_coupling_cosine]
  have h := abs_mul_add_mul_le (Real.cos alpha) (-(Real.sin alpha)) zeta0
  have hrow := l2norm_rotR_row_zero alpha
  have h1 : |Real.cos alpha * zeta0 0 + -(Real.sin alpha) * zeta0 1| ≤ l2norm zeta0 := by
    calc |Real.cos alpha * zeta0 0 + -(Real.sin alpha) * zeta0 1|
        ≤ l2norm ![Real.cos alpha, -(Real.sin alpha)] * l2norm zeta0 := h
      _ = l2norm zeta0 := by rw [hrow, one_mul]
  calc |lam * (zeta0 0 * Real.cos alpha - zeta0 1 * Real.sin alpha)|
      = |lam| * |zeta0 0 * Real.cos alpha - zeta0 1 * Real.sin alpha| := by rw [abs_mul]
    _ = |lam| * |Real.cos alpha * zeta0 0 + -(Real.sin alpha) * zeta0 1| := by
        congr 1
        ring
    _ ≤ |lam| * l2norm zeta0 := mul_le_mul_of_nonneg_left h1 (abs_nonneg lam)

/-- **Simultaneous-rotation invariance of AB's temperature numerator.** `rotJ` and `rotR alpha`
commute and `rotR alpha` is orthogonal, so rotating both the wavevector and the frozen gradient
leaves `(J zeta)·G` unchanged: `(J (rotR alpha zeta0))·(rotR alpha G) = (J zeta0)·G`. (With `G`
held fixed the corresponding identity is *false*: a rotation changes the angle between `J zeta0`
and `G`, hence changes the temperature coupling.) -/
theorem rotJ_mulVec_dot_rotR (alpha : ℝ) (zeta0 G : Fin 2 → ℝ) :
    (rotJ *ᵥ (rotR alpha *ᵥ zeta0)) ⬝ᵥ (rotR alpha *ᵥ G) = (rotJ *ᵥ zeta0) ⬝ᵥ G := by
  simp only [dotProduct, Fin.sum_univ_two, rotJ_mulVec, rotR_mulVec_zero, rotR_mulVec_one,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf
  linear_combination (zeta0 0 * G 1 - zeta0 1 * G 0) * Real.sin_sq_add_cos_sq alpha

/-! ## The phase can reverse the coupling -/

/-- **The half-turn flips the buoyancy coupling.** A wavevector aligned with the buoyancy
direction has coupling `lam c` at zero angle and `-(lam c)` after a turn by `pi`. -/
theorem phase_flip (lam c : ℝ) (hc : 0 < c) :
    abVortCoeff lam (rotR 0 *ᵥ ![c, 0]) = lam * c ∧
      abVortCoeff lam (rotR Real.pi *ᵥ ![c, 0]) = -(lam * c) := by
  constructor
  · rw [abVortCoeff, rotR_mulVec_zero]
    simp
  · rw [abVortCoeff, rotR_mulVec_zero]
    simp [Real.cos_pi, Real.sin_pi]

/-- **Quantitative flip.** Every value in `[-|lam| c, |lam| c]` is attained by the steerable
coupling: the coupling sweeps the full interval as the phase turns. -/
theorem phase_flip_quantitative (lam : ℝ) (c : ℝ) (hc : 0 < c) (y : ℝ) (hy : |y| ≤ |lam| * c) :
    ∃ alpha : ℝ, abVortCoeff lam (rotR alpha *ᵥ ![c, 0]) = y := by
  rcases eq_or_ne lam 0 with hlam | hlam
  · subst hlam
    have hy0 : y = 0 := by
      have h : |y| ≤ 0 := by simpa using hy
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg y))
    subst hy0
    exact ⟨0, by rw [abVortCoeff]; simp⟩
  have hk : |y / (lam * c)| ≤ 1 := by
    have hc' : |c| = c := abs_of_pos hc
    rw [abs_div, abs_mul, hc', div_le_one (mul_pos (abs_pos.mpr hlam) hc)]
    exact hy
  have hmem : y / (lam * c) ∈ Set.Icc (Real.cos Real.pi) (Real.cos 0) := by
    rw [Real.cos_pi, Real.cos_zero]
    exact ⟨by linarith [neg_abs_le (y / (lam * c))], by linarith [le_abs_self (y / (lam * c))]⟩
  obtain ⟨alpha, halpha⟩ := (intermediate_value_univ Real.pi 0 Real.continuous_cos) hmem
  refine ⟨alpha, ?_⟩
  rw [abVortCoeff, rotR_mulVec_zero]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [show Real.cos alpha = y / (lam * c) from halpha]
  field_simp [mul_ne_zero hlam (ne_of_gt hc)]
  ring

/-! ## Non-vacuity checks -/

/-- Concrete steering at angle `pi/2`: the wavevector `![1,0]` is turned to `![0,1]`. -/
example : (rotR (Real.pi / 2) *ᵥ ![1, 0] : Fin 2 → ℝ) = ![0, 1] := by
  ext i
  fin_cases i <;>
    simp [rotR_mulVec_zero, rotR_mulVec_one, Real.cos_pi_div_two, Real.sin_pi_div_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- Concrete steering derivative at `alpha = pi/2`, `zeta0 = ![1,0]`:
`zeta' = alpha' • J zeta = alpha' • ![-1, 0]`. -/
example (alphap : ℝ) :
    (alphap • (rotJ *ᵥ (rotR (Real.pi / 2) *ᵥ ![1, 0]) : Fin 2 → ℝ)) = ![-(alphap), 0] := by
  have h : (rotR (Real.pi / 2) *ᵥ ![1, 0] : Fin 2 → ℝ) = ![0, 1] := by
    ext i
    fin_cases i <;>
      simp [rotR_mulVec_zero, rotR_mulVec_one, Real.cos_pi_div_two, Real.sin_pi_div_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [h, rotJ_mulVec]
  ext i
  fin_cases i <;> simp

/-- Non-vacuity of the coupling: at `lam = 1`, `alpha = pi/2`, `zeta0 = ![1,0]` the buoyancy
coupling is `1 * (1 * cos (pi/2) - 0 * sin (pi/2)) = 0`; the wavevector has become orthogonal to
gravity and the coupling has been steered through zero. -/
example : abVortCoeff 1 (rotR (Real.pi / 2) *ᵥ ![1, 0]) = 0 := by
  rw [phase_coupling_cosine]
  norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- Non-vacuity of the bound: at `alpha = 0`, `lam = 1`, `zeta0 = ![1,0]` the coupling is
`|1| * |zeta0| = 1`, so the bound `|lam| |zeta0|` is attained (the inequality is sharp, not
vacuous). -/
example : |abVortCoeff 1 (rotR 0 *ᵥ ![1, 0])| = |(1 : ℝ)| * l2norm ![1, 0] := by
  rw [phase_coupling_cosine]
  norm_num [l2norm, rotR, Real.cos_zero, Real.sin_zero]

/-- Non-vacuity of the flip: `lam = 1`, `c = 1` gives `1` at angle `0` and `-1` at angle `pi`. -/
example : abVortCoeff 1 (rotR 0 *ᵥ ![1, 0]) = 1
    ∧ abVortCoeff 1 (rotR Real.pi *ᵥ ![1, 0]) = -1 := by
  simpa using phase_flip 1 1 (by norm_num)

/-- Non-vacuity of the quantitative sweep at `lam = 1`, `c = 2`: the value `3/2` is attained by
the steerable coupling in `[-2, 2]`. -/
example : ∃ alpha : ℝ, abVortCoeff 1 (rotR alpha *ᵥ ![2, 0]) = (3 / 2 : ℝ) :=
  phase_flip_quantitative 1 2 (by norm_num) (3 / 2) (by norm_num)

/-- The product of the couplings at the concrete configuration `lam = 1`, `zeta = ![1,0]`,
`G = ![0,1]`: `abTempCoeff = -1`, `abVortCoeff = 1`, so `ab = -1` — the stably stratified sign
(`Cascade/Amplitude.lean`), reached with `|zeta| = 1`. -/
example : abTempCoeff 1 ![1, 0] ![0, 1] * abVortCoeff 1 ![1, 0] = -1 := by
  rw [ab_product 1 (by norm_num) ![1, 0] ![0, 1] (by norm_num)]
  rw [l2norm_sq ![1, 0] (by norm_num)]
  rw [rotJ_mulVec]
  norm_num [dotProduct, Fin.sum_univ_two]

/-! ## The `‖·‖` statement is false in the ambient (sup) norm

Lean endows `Fin 2 → R` with the sup norm `‖x‖ = sup_i ‖x i‖ = max (|x 0|) (|x 1|)`
(`Pi.norm_def`), so the literal `‖rotR alpha *ᵥ zeta0‖ = ‖zeta0‖` fails. The Euclidean statement
is `rotR_norm_preserving` above; here is the machine-checked counterexample to the literal one. -/

/-- The sup norm of a two-vector is the max of the absolute values of its components. -/
theorem supNorm_fin_two (x : Fin 2 → ℝ) : ‖x‖ = max (|x 0|) (|x 1|) := by
  rw [Pi.norm_def]
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by
    ext i
    fin_cases i <;> simp
  rw [huniv, Finset.sup_insert, Finset.sup_singleton, NNReal.coe_max, coe_nnnorm, coe_nnnorm]
  simp [Real.norm_eq_abs, max_def]

/-- **Counterexample to the literal `‖·‖` norm-preservation claim.** With `zeta0 = ![1,1]` and
`alpha = pi/4`, `rotR alpha *ᵥ zeta0 = ![0, sqrt 2]`, so `‖rotR alpha *ᵥ zeta0‖ = sqrt 2 ≠ 1 =
‖zeta0‖`: the ambient norm on `Fin 2 → R` is not preserved by rotations. -/
theorem rotR_norm_preserving_supNorm_counterexample :
    ¬ (∀ (alpha : ℝ) (zeta0 : Fin 2 → ℝ), ‖(rotR alpha) *ᵥ zeta0‖ = ‖zeta0‖) := by
  intro h
  have hrot : (rotR (Real.pi / 4)) *ᵥ ![1, 1] = ![0, Real.sqrt 2] := by
    ext i
    fin_cases i <;>
      simp [rotR_mulVec_zero, rotR_mulVec_one, Real.cos_pi_div_four, Real.sin_pi_div_four,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> norm_num
  have hx : ‖(![1, 1] : Fin 2 → ℝ)‖ = 1 := by rw [supNorm_fin_two]; norm_num
  have hy : ‖(![0, Real.sqrt 2] : Fin 2 → ℝ)‖ = Real.sqrt 2 := by
    rw [supNorm_fin_two]; norm_num
  have h1 := h (Real.pi / 4) ![1, 1]
  rw [hrot, hx, hy] at h1
  have hlt : (1 : ℝ) < Real.sqrt 2 := by
    have hsq : (1 : ℝ) ^ 2 < (Real.sqrt 2) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg 2]
  linarith

end Cascade

#print axioms Cascade.rotJ_transpose
#print axioms Cascade.rotJ_mulVec
#print axioms Cascade.rotJ_sq
#print axioms Cascade.rotR_zero
#print axioms Cascade.rotR_mulVec_zero
#print axioms Cascade.rotR_mulVec_one
#print axioms Cascade.rotJ_mul_rotR
#print axioms Cascade.phase_steering_component
#print axioms Cascade.l2norm_sq
#print axioms Cascade.l2norm_ne_zero
#print axioms Cascade.rotR_norm_preserving
#print axioms Cascade.l2norm_mul_sqrt
#print axioms Cascade.l2norm_rotR_row_zero
#print axioms Cascade.abs_mul_add_mul_le
#print axioms Cascade.abs_apply_le_l2norm
#print axioms Cascade.ab_product
#print axioms Cascade.phase_coupling_cosine
#print axioms Cascade.phase_coupling_bound
#print axioms Cascade.rotJ_mulVec_dot_rotR
#print axioms Cascade.phase_flip
#print axioms Cascade.phase_flip_quantitative
#print axioms Cascade.supNorm_fin_two
#print axioms Cascade.rotR_norm_preserving_supNorm_counterexample
