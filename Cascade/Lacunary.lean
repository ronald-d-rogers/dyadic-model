import Cascade.Boussinesq
import Mathlib.Tactic

/-!
# Stage A — the lacunary ansatz and the exact amplitude ODE

The dyadic Boussinesq model of `Cascade/Boussinesq.lean` is a nearest-octave shell system on
`k : ℤ`, shell `k` carrying the wavenumber `2^k`. The **lacunary ansatz** at generation
`n : ℤ` describes a single wave packet sitting on octave `n` above a background that is
strictly supported below `n`:

    u k = u₋ k  for k < n,   u n = a,   u k = 0  for k > n,
    θ k = θ₋ k  for k < n,   θ n = b,   θ k = 0  for k > n,

encoded by `lacunaryVelocity n u_minus a = Function.update u_minus n a` and
`lacunaryTemperature n θ_minus b = Function.update θ_minus n b`, together with the support
hypotheses `u_minus (n + 1) = 0` and `θ_minus (n + 1) = 0`: the ladders vanish strictly above the
packet, so the background is *lacunary* (only octaves `≤ n - 1` are occupied).

(The prose writes the background ladders `u₋`, `θ₋`; the code uses the bound variables
`u_minus`, `θ_minus`, because the subscript-minus glyph is not a legal identifier character in
this Lean pin.)

## The amplitude ODE

Substituting the ansatz into shell `n` of the general four-parameter model gives the
**amplitude ODE** for `(a, b)`:

    ȧ = 2^n (A u₋_{n-1}² + B a u₋_{n-1}) + κ b - ν 4^n a,
    ḃ = 2^n (Ã u₋_{n-1} θ₋_{n-1} + B̃ a θ₋_{n-1}) - μ 4^n b,

which is `lacunaryVelocityRHS` / `lacunaryTemperatureRHS`. The reduction theorems
`lacunary_reduction_velocity` / `lacunary_reduction_temperature` state that the shell-`n`
right-hand side of the model **is** this amplitude ODE with **no linearisation error**: the
ansatz is exact, and the reduced vector field is *affine* in `(a, b)` — the terms
`2^n A u₋_{n-1}²` and `2^n Ã u₋_{n-1} θ₋_{n-1}` are inhomogeneous background forcings that
survive even at `a = b = 0`. The only couplings discarded are the `n + 1` ones, and they
vanish exactly because `u₋ (n + 1) = 0` and `θ₋ (n + 1) = 0` (`hu`, `hth`).

## Dictionary

Writing `Ω_n = 2^n a` for the vorticity amplitude (`lacunaryVorticity`) and `Θ_n = b` for the
temperature amplitude, the terms *linear* in `(Ω, Θ)` are

    Θ̇ = θ̄_{n-1} Ω - μ 4^n Θ,      θ̄_{n-1} := B̃ θ₋_{n-1},
    Ω̇ = 2^n κ Θ - ν 4^n Ω,

which is Tao's reduced Boussinesq system (`Θ̇ = aΩ`, `Ω̇ = bΘ`, Boussinesq, p. 4). The frozen
Stage R coupling `A = 1, B = 0, Ã = 1, B̃ = 1` specialises this to `θ̄_{n-1} = θ₋_{n-1}`.

This file replaces the previously *unformalized* prose motivation of
`Cascade/Boussinesq.lean` ("Motivation (heuristic — unformalized)"): the linearisation argument
sketched there is here an exact, machine-checked reduction theorem.
-/

noncomputable section

namespace Cascade

/-- The wavenumber of generation `n`, `N_n = 2^n`. -/
def lacunaryFrequency (n : ℤ) : ℝ := dyadicWeight n

/-- The lacunary velocity ladder: background `u_minus` overwritten by the wave amplitude `a` at
octave `n`. -/
def lacunaryVelocity (n : ℤ) (u_minus : ℤ → ℝ) (a : ℝ) : ℤ → ℝ := Function.update u_minus n a

/-- The lacunary temperature ladder: background `θ_minus` overwritten by the wave amplitude `b`
at octave `n`. -/
def lacunaryTemperature (n : ℤ) (θ_minus : ℤ → ℝ) (b : ℝ) : ℤ → ℝ :=
  Function.update θ_minus n b

/-- The vorticity amplitude at generation `n`: `Ω_n = 2^n a`. The velocity amplitude `a` is a
*velocity* amplitude, while `2^n a` is the corresponding vorticity amplitude. -/
def lacunaryVorticity (n : ℤ) (a : ℝ) : ℝ := dyadicWeight n * a

/-- The dictionary check `Ω_n = 2^n a` is definitional. -/
theorem lacunaryVorticity_eq (n : ℤ) (a : ℝ) :
    lacunaryVorticity n a = dyadicWeight n * a := rfl

/-- Velocity amplitude RHS of the lacunary reduction (general coupling). -/
def lacunaryVelocityRHS (ν κ A B : ℝ) (n : ℤ) (u_minus : ℤ → ℝ) (a b : ℝ) : ℝ :=
  dyadicWeight n * (A * (u_minus (n - 1)) ^ 2 + B * a * u_minus (n - 1)) + κ * b
    - ν * dyadicWeight (2 * n) * a

/-- Temperature amplitude RHS of the lacunary reduction (general coupling). -/
def lacunaryTemperatureRHS (μ At Bt : ℝ) (n : ℤ) (u_minus θ_minus : ℤ → ℝ) (a b : ℝ) : ℝ :=
  dyadicWeight n * (At * u_minus (n - 1) * θ_minus (n - 1) + Bt * a * θ_minus (n - 1))
    - μ * dyadicWeight (2 * n) * b

/-- The frozen Stage R velocity amplitude RHS: `A = 1`, `B = 0`. -/
def dyadicLacunaryVelocityRHS (ν κ : ℝ) (n : ℤ) (u_minus : ℤ → ℝ) (a b : ℝ) : ℝ :=
  lacunaryVelocityRHS ν κ 1 0 n u_minus a b

/-- The frozen Stage R temperature amplitude RHS: `Ã = 1`, `B̃ = 1`. -/
def dyadicLacunaryTemperatureRHS (μ : ℝ) (n : ℤ) (u_minus θ_minus : ℤ → ℝ) (a b : ℝ) : ℝ :=
  lacunaryTemperatureRHS μ 1 1 n u_minus θ_minus a b

/-- **The lacunary reduction (velocity, general coupling).** The shell-`n` velocity equation of
the general four-parameter dyadic Boussinesq model, evaluated on the lacunary state, is exactly
the velocity amplitude ODE `lacunaryVelocityRHS`. The reduction is exact (the ansatz is not a
linearisation); only the `n + 1` couplings are dropped, and only because `u_minus (n + 1) = 0`. -/
theorem lacunary_reduction_velocity (ν μ κ A B At Bt : ℝ) (n : ℤ) (u_minus θ_minus : ℤ → ℝ)
    (a b : ℝ) (hu : u_minus (n + 1) = 0) :
    (generalBoussinesqRHS ν μ κ A B At Bt (lacunaryVelocity n u_minus a)
        (lacunaryTemperature n θ_minus b) n).1
      = lacunaryVelocityRHS ν κ A B n u_minus a b := by
  change generalVelocityRHS ν κ A B (lacunaryVelocity n u_minus a)
      (lacunaryTemperature n θ_minus b) n
    = lacunaryVelocityRHS ν κ A B n u_minus a b
  simp only [generalVelocityRHS, boussinesqTransferU, lacunaryVelocity, lacunaryTemperature,
    lacunaryVelocityRHS, Function.update_self,
    Function.update_of_ne (show n - 1 ≠ n by omega),
    Function.update_of_ne (show n + 1 ≠ n by omega), hu]
  ring

/-- **The lacunary reduction (temperature, general coupling).** The shell-`n` temperature
equation of the general four-parameter dyadic Boussinesq model, evaluated on the lacunary state,
is exactly the temperature amplitude ODE `lacunaryTemperatureRHS`. -/
theorem lacunary_reduction_temperature (ν μ κ A B At Bt : ℝ) (n : ℤ) (u_minus θ_minus : ℤ → ℝ)
    (a b : ℝ) (hu : u_minus (n + 1) = 0) (hth : θ_minus (n + 1) = 0) :
    (generalBoussinesqRHS ν μ κ A B At Bt (lacunaryVelocity n u_minus a)
        (lacunaryTemperature n θ_minus b) n).2
      = lacunaryTemperatureRHS μ At Bt n u_minus θ_minus a b := by
  change generalTemperatureRHS μ At Bt (lacunaryVelocity n u_minus a)
      (lacunaryTemperature n θ_minus b) n
    = lacunaryTemperatureRHS μ At Bt n u_minus θ_minus a b
  simp only [generalTemperatureRHS, boussinesqTransferTheta, lacunaryVelocity, lacunaryTemperature,
    lacunaryTemperatureRHS, Function.update_self,
    Function.update_of_ne (show n - 1 ≠ n by omega),
    Function.update_of_ne (show n + 1 ≠ n by omega), hu, hth]
  ring

/-- **The lacunary reduction (velocity, frozen Stage R model).** -/
theorem lacunary_reduction_dyadic_velocity (ν μ κ : ℝ) (n : ℤ) (u_minus θ_minus : ℤ → ℝ)
    (a b : ℝ) (hu : u_minus (n + 1) = 0) :
    (dyadicBoussinesqRHS ν μ κ (lacunaryVelocity n u_minus a)
        (lacunaryTemperature n θ_minus b) n).1
      = dyadicLacunaryVelocityRHS ν κ n u_minus a b := by
  change dyadicVelocityRHS ν κ (lacunaryVelocity n u_minus a) (lacunaryTemperature n θ_minus b) n
    = lacunaryVelocityRHS ν κ 1 0 n u_minus a b
  simp only [dyadicVelocityRHS, generalVelocityRHS, boussinesqTransferU, lacunaryVelocity,
    lacunaryTemperature, lacunaryVelocityRHS, Function.update_self,
    Function.update_of_ne (show n - 1 ≠ n by omega),
    Function.update_of_ne (show n + 1 ≠ n by omega), hu]
  ring

/-- **The lacunary reduction (temperature, frozen Stage R model).** -/
theorem lacunary_reduction_dyadic_temperature (ν μ κ : ℝ) (n : ℤ) (u_minus θ_minus : ℤ → ℝ)
    (a b : ℝ) (hu : u_minus (n + 1) = 0) (hth : θ_minus (n + 1) = 0) :
    (dyadicBoussinesqRHS ν μ κ (lacunaryVelocity n u_minus a)
        (lacunaryTemperature n θ_minus b) n).2
      = dyadicLacunaryTemperatureRHS μ n u_minus θ_minus a b := by
  change dyadicTemperatureRHS μ (lacunaryVelocity n u_minus a) (lacunaryTemperature n θ_minus b) n
    = lacunaryTemperatureRHS μ 1 1 n u_minus θ_minus a b
  simp only [dyadicTemperatureRHS, generalTemperatureRHS, boussinesqTransferTheta, lacunaryVelocity,
    lacunaryTemperature, lacunaryTemperatureRHS, Function.update_self,
    Function.update_of_ne (show n - 1 ≠ n by omega),
    Function.update_of_ne (show n + 1 ≠ n by omega), hu, hth]
  ring

/-! ## Non-vacuity checks

Concrete lacunary states at generation `n = 2`, with background `u_minus 1 = 3`, `θ_minus 1 = 5`
(and all other octaves zero, so in particular `u_minus 3 = θ_minus 3 = 0`), wave amplitudes
`a = 2`, `b = 7`, and all couplings set to `1`. Each reduction theorem is instantiated on this
state and the resulting amplitude RHS is evaluated by `norm_num`. -/

/-- A concrete background velocity ladder: `u_minus 1 = 3`, all other octaves zero. -/
def exampleBackgroundU : ℤ → ℝ := fun k => if k = 1 then 3 else 0

/-- A concrete background temperature ladder: `θ_minus 1 = 5`, all other octaves zero. -/
def exampleBackgroundTheta : ℤ → ℝ := fun k => if k = 1 then 5 else 0

/-- The dictionary value `Ω_2 = 2^2 · 2 = 8`. -/
example : lacunaryVorticity 2 2 = 8 := by
  norm_num [lacunaryVorticity, dyadicWeight]

/-- Non-vacuity of `lacunary_reduction_velocity`: the concrete shell-`2` velocity equation is
`35` (general coupling `A = B = Ã = B̃ = 1`), and the amplitude ODE evaluates to the same value
`2^2 · (1 · 3^2 + 1 · 2 · 3) + 1 · 7 - 1 · 2^4 · 2 = 60 + 7 - 32 = 35`. -/
example :
    (generalBoussinesqRHS 1 1 1 1 1 1 1
        (lacunaryVelocity 2 exampleBackgroundU 2)
        (lacunaryTemperature 2 exampleBackgroundTheta 7) 2).1 = 35 := by
  rw [lacunary_reduction_velocity 1 1 1 1 1 1 1 2 exampleBackgroundU exampleBackgroundTheta 2 7
    (by norm_num [exampleBackgroundU])]
  norm_num [lacunaryVelocityRHS, dyadicWeight, exampleBackgroundU]

/-- Non-vacuity of `lacunary_reduction_temperature`: the concrete shell-`2` temperature equation
is `-12`, and the amplitude ODE evaluates to the same value
`2^2 · (3 · 5 + 2 · 5) - 1 · 2^4 · 7 = 100 - 112 = -12`. -/
example :
    (generalBoussinesqRHS 1 1 1 1 1 1 1
        (lacunaryVelocity 2 exampleBackgroundU 2)
        (lacunaryTemperature 2 exampleBackgroundTheta 7) 2).2 = -12 := by
  rw [lacunary_reduction_temperature 1 1 1 1 1 1 1 2 exampleBackgroundU exampleBackgroundTheta 2 7
    (by norm_num [exampleBackgroundU]) (by norm_num [exampleBackgroundTheta])]
  norm_num [lacunaryTemperatureRHS, dyadicWeight, exampleBackgroundU, exampleBackgroundTheta]

/-- Non-vacuity of `lacunary_reduction_dyadic_velocity`: on the frozen Stage R coupling the
concrete shell-`2` velocity equation is `2^2 · 3^2 + 7 - 2^4 · 2 = 36 + 7 - 32 = 11`. -/
example :
    (dyadicBoussinesqRHS 1 1 1
        (lacunaryVelocity 2 exampleBackgroundU 2)
        (lacunaryTemperature 2 exampleBackgroundTheta 7) 2).1 = 11 := by
  rw [lacunary_reduction_dyadic_velocity 1 1 1 2 exampleBackgroundU exampleBackgroundTheta 2 7
    (by norm_num [exampleBackgroundU])]
  norm_num [dyadicLacunaryVelocityRHS, lacunaryVelocityRHS, dyadicWeight, exampleBackgroundU]

/-- Non-vacuity of `lacunary_reduction_dyadic_temperature`: on the frozen Stage R coupling the
concrete shell-`2` temperature equation is `2^2 · (3 · 5 + 2 · 5) - 2^4 · 7 = -12`. -/
example :
    (dyadicBoussinesqRHS 1 1 1
        (lacunaryVelocity 2 exampleBackgroundU 2)
        (lacunaryTemperature 2 exampleBackgroundTheta 7) 2).2 = -12 := by
  rw [lacunary_reduction_dyadic_temperature 1 1 1 2 exampleBackgroundU exampleBackgroundTheta 2 7
    (by norm_num [exampleBackgroundU]) (by norm_num [exampleBackgroundTheta])]
  norm_num [dyadicLacunaryTemperatureRHS, lacunaryTemperatureRHS, dyadicWeight, exampleBackgroundU,
    exampleBackgroundTheta]

end Cascade

#print axioms Cascade.lacunaryVorticity_eq
#print axioms Cascade.lacunary_reduction_velocity
#print axioms Cascade.lacunary_reduction_temperature
#print axioms Cascade.lacunary_reduction_dyadic_velocity
#print axioms Cascade.lacunary_reduction_dyadic_temperature
