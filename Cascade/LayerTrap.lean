import Cascade.Layers

/-!
# The transverse trap: a growth-free equilibrium of the one-wavevector-per-octave layer model

`Cascade/Layers.lean` realises Alpöge–Buckmaster eq. (3.3): one wavevector `ζ_q` and one
amplitude pair `(Θ_q, Ω_q)` per octave, the `q`-th octave being driven one-way by the accumulated
background `G_{<q}`, `D_{<q}` of the octaves below it. This file exhibits and proves a
**configuration of that model at which every right-hand side vanishes at every octave**: an exact
equilibrium with no growth at all.

## The configuration

Let the background direction `e₀` and *every* wavevector `ζ_q` be transverse to the gravity
direction — component `0` of each is zero — and let the common rotation rate be `α' = 0`. Then

* the accumulated gradient `G_{<q}` is transverse as well (`Gprefix_apply_zero`), because it is
  built from `−e₀` and from the unit vectors `e_j = ζ_j/|ζ_j|`, all transverse;
* both AB couplings vanish: the buoyancy coupling `b_q = λ_q (ζ_q)₀` is `0`
  (`abVortCoeff_eq_zero`), and the temperature coupling `a_q` is the dot product of the transverse
  vectors `J ζ_q = (−(ζ_q)₁, 0)` and `G_{<q} = (0, (G_{<q})₁)`, hence `0`
  (`abTempCoeff_eq_zero`);
* the wavevector equation vanishes too (`layerZetaRHS_eq_zero`): with `α' = 0` every term of
  `D_{<q}` is a rank-one matrix `(J e_j) ⊗ e_j` whose *second row is zero*, so `D_{<q}ᵀ` has a zero
  second *column* and `D_{<q}ᵀ ζ_q = 0` because `(ζ_q)₀ = 0`.

`layerRHS_eq_zero_of_transverse` bundles the three: **the transverse configuration is a fixed
point of the layer system**, at every octave. It is the counterpart, for the full
one-wavevector-per-octave model, of the "no growth" configurations of the amplitude models.

## Non-vacuity

The configuration is not the zero state: with `e₀ = ![0,1]`, `λ = w = Θ = Ω = 1` and
`ζ_q = ![0,1]` for all `q`, every `ζ_q` is nonzero, and `G_{<2} = ![0,1]` (the worked computation
at the end of this file). The conclusion of `layerRHS_eq_zero_of_transverse` is instantiated on
this concrete data.

## Self-perpetuation (prose)

Because `layerZetaRHS 0 w Ω ζ q = 0` for *every* `q`, the wavevector field is stationary: the
transverse hypothesis `∀ q, (ζ_q)₀ = 0` is preserved for all time, so the configuration cannot
drift out of the trap. (This is a statement about the right-hand sides, not yet a time-integration
statement: `Layers.lean` records the layer ODEs as right-hand-side functions, not as
`HasDerivAt`.)

## The caveat: `α' ≠ 0` breaks the trap

The equilibrium genuinely requires `α' = 0`. For `α' ≠ 0` the wavevectors do **not** stay
transverse. The `α'`-part of the accumulated deformation is `α' • J`, and `(α' J)ᵀ = −α' J`, whose
contribution to `−D_{<q}ᵀ ζ_q` has component `0` equal to `α' (ζ_q)₁`. The reason is exactly the
one stated in the brief: `J ζ_q = (−(ζ_q)₁, (ζ_q)₀) = (−(ζ_q)₁, 0)` has a **nonzero** component
`0` whenever `(ζ_q)₁ ≠ 0`. This is made precise by `layerZetaRHS_apply_zero`,

    layerZetaRHS α' w Ω ζ q 0 = −(α' * (ζ_q)₁),

valid for every transverse wavevector field `ζ`, together with the concrete `example`s at the end
of the file (`(rotJ *ᵥ (1,1))₀ = −1 ≠ 0` and `layerZetaRHS 1 … 0 0 = −1 ≠ 0`). Thus `α' = 0` is
not a technical convenience but exactly the hypothesis that keeps the trap closed.
-/

noncomputable section

namespace Cascade

open scoped Matrix

/-! ## Phase 1 — the couplings vanish -/

/-- With `e0` and every wavevector transverse to component 0, so is the accumulated gradient. -/
theorem Gprefix_apply_zero (e0 : Fin 2 → ℝ) (lam w : ℕ → ℝ) (Θ : ℕ → ℝ)
    (ζ : ℕ → Fin 2 → ℝ) (he0 : e0 0 = 0) (hζ : ∀ q, ζ q 0 = 0) (q : ℕ) :
    Gprefix e0 lam w Θ ζ q 0 = 0 := by
  show -(e0 0) - ∑ j ∈ Finset.range q, w j * layerGradScalar lam Θ ζ j * unitVec (ζ j) 0 = 0
  rw [he0, Finset.sum_eq_zero (by
    intro j _hj
    simp [unitVec, hζ j])]
  simp

/-- The buoyancy coupling vanishes. -/
theorem abVortCoeff_eq_zero (lam : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ) (hζ : ∀ q, ζ q 0 = 0) (q : ℕ) :
    abVortCoeff (lam q) (ζ q) = 0 := by
  simp [abVortCoeff, hζ q]

/-- The temperature coupling vanishes. -/
theorem abTempCoeff_eq_zero (e0 : Fin 2 → ℝ) (lam w : ℕ → ℝ) (Θ : ℕ → ℝ)
    (ζ : ℕ → Fin 2 → ℝ) (he0 : e0 0 = 0) (hζ : ∀ q, ζ q 0 = 0) (q : ℕ) :
    abTempCoeff (lam q) (ζ q) (Gprefix e0 lam w Θ ζ q) = 0 := by
  have hG : Gprefix e0 lam w Θ ζ q 0 = 0 := Gprefix_apply_zero e0 lam w Θ ζ he0 hζ q
  simp only [abTempCoeff, rotJ_mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, hζ q, hG, mul_zero, zero_mul, add_zero, zero_div, neg_zero]

/-! ## Phase 2 — the wavevector equation also vanishes at `α' = 0` -/

/-- Second component of `J v`: `(J v)₁ = v₀`. -/
theorem rotJ_mulVec_apply_one (v : Fin 2 → ℝ) : (rotJ *ᵥ v) 1 = v 0 := by
  simp [rotJ_mulVec]

/-- A transverse vector has a transverse unit vector. -/
theorem unitVec_apply_zero (v : Fin 2 → ℝ) (hv : v 0 = 0) : unitVec v 0 = 0 := by
  simp [unitVec, hv]

/-- **Every `j < q` term of `D_{<q}` at `α' = 0` has vanishing second row.** Each rank-one term is
`(J e_j) ⊗ e_j`, and `(J e_j)₁ = (e_j)₀ = 0` whenever `ζ_j` is transverse. -/
theorem Dprefix_zero_row_one (w Ω : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ)
    (hζ : ∀ q, ζ q 0 = 0) (q : ℕ) (k : Fin 2) : Dprefix 0 w Ω ζ q 1 k = 0 := by
  have hD : Dprefix 0 w Ω ζ q
      = ∑ j ∈ Finset.range q,
          (w j * Ω j) • Matrix.vecMulVec (rotJ *ᵥ unitVec (ζ j)) (unitVec (ζ j)) := by
    simp only [Dprefix, zero_smul, zero_add]
  rw [hD, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro j _hj
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, rotJ_mulVec_apply_one,
    unitVec_apply_zero (ζ j) (hζ j), zero_mul, mul_zero]

/-- Hence `D_{<q}ᵀ ζ_q = 0` at `α' = 0`: the transpose has a zero second column and `(ζ_q)₀ = 0`. -/
theorem Dprefix_zero_transpose_mulVec_eq_zero (w Ω : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ)
    (hζ : ∀ q, ζ q 0 = 0) (q : ℕ) :
    (Dprefix 0 w Ω ζ q)ᵀ *ᵥ ζ q = 0 := by
  funext i
  simp [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, Matrix.transpose_apply,
    Dprefix_zero_row_one w Ω ζ hζ q, hζ q]

/-- **The wavevector equation vanishes at `α' = 0`** when every wavevector is transverse. -/
theorem layerZetaRHS_eq_zero (w : ℕ → ℝ) (Ω : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ)
    (hζ : ∀ q, ζ q 0 = 0) (q : ℕ) : layerZetaRHS 0 w Ω ζ q = 0 := by
  funext i
  show -((Dprefix 0 w Ω ζ q)ᵀ *ᵥ ζ q) i = 0
  rw [Dprefix_zero_transpose_mulVec_eq_zero w Ω ζ hζ q]
  simp

/-! ## Phase 3 — the trap (headline) -/

/-- **The transverse configuration is a growth-free equilibrium of the layer model.**
With `α' = 0`, `e0 0 = 0` and every wavevector having zero component 0, all three layer
right-hand sides vanish at every octave: no wavevector rotates, and no amplitude grows. -/
theorem layerRHS_eq_zero_of_transverse (e0 : Fin 2 → ℝ) (lam w : ℕ → ℝ) (Θ Ω : ℕ → ℝ)
    (ζ : ℕ → Fin 2 → ℝ) (he0 : e0 0 = 0) (hζ : ∀ q, ζ q 0 = 0) (q : ℕ) :
    layerZetaRHS 0 w Ω ζ q = 0 ∧
    layerThetaRHS e0 lam w Θ Ω ζ q = 0 ∧
    layerOmegaRHS lam Θ ζ q = 0 := by
  refine ⟨layerZetaRHS_eq_zero w Ω ζ hζ q, ?_, ?_⟩
  · simp only [layerThetaRHS, abTempCoeff_eq_zero e0 lam w Θ ζ he0 hζ q, zero_mul]
  · simp only [layerOmegaRHS, abVortCoeff_eq_zero lam ζ hζ q, zero_mul]

/-! ## Phase 4 — non-vacuity, and the `α' ≠ 0` caveat

### The `α'` part of `D_{<q}`

`D_{<q}` splits as `α' • J + D_{<q}|_{α'=0}`, and the second summand has zero second row
(`Dprefix_zero_row_one`). Hence `(D_{<q})ᵀ ζ_q = α' • (Jᵀ ζ_q)` for transverse `ζ`, and the
component `0` of `layerZetaRHS` is `−α' (ζ_q)₁`: for `α' ≠ 0` and `(ζ_q)₁ ≠ 0` the wavevector
leaves the transverse plane. -/

/-- The accumulated deformation splits into its rotation part and its `α' = 0` part. -/
theorem Dprefix_eq_smul_rotJ_add (α' : ℝ) (w Ω : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ) (q : ℕ) :
    Dprefix α' w Ω ζ q = α' • rotJ + Dprefix 0 w Ω ζ q := by
  simp only [Dprefix, zero_smul, zero_add]

/-- The second row of `D_{<q}` is exactly the second row of `α' • J`. -/
theorem Dprefix_row_one_apply (α' : ℝ) (w Ω : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ)
    (hζ : ∀ q, ζ q 0 = 0) (q : ℕ) (k : Fin 2) :
    Dprefix α' w Ω ζ q 1 k = α' * rotJ 1 k := by
  rw [Dprefix_eq_smul_rotJ_add α' w Ω ζ q, Matrix.add_apply, Matrix.smul_apply]
  simp only [smul_eq_mul, Dprefix_zero_row_one w Ω ζ hζ q k, add_zero]

/-- The first component of `Jᵀ v` is `v₁` (equivalently `Jᵀ = −J`). -/
theorem transpose_rotJ_mulVec_apply_zero (v : Fin 2 → ℝ) : (rotJᵀ *ᵥ v) 0 = v 1 := by
  rw [rotJ_transpose, Matrix.neg_mulVec]
  simp [rotJ_mulVec]

/-- **Transpose form of the split.** For transverse `ζ`, the whole `α' = 0` part of `D_{<q}`
contributes nothing to `(D_{<q})ᵀ ζ_q`, so only the rotation term survives. -/
theorem Dprefix_transpose_mulVec (α' : ℝ) (w Ω : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ)
    (hζ : ∀ q, ζ q 0 = 0) (q : ℕ) :
    (Dprefix α' w Ω ζ q)ᵀ *ᵥ ζ q = α' • (rotJᵀ *ᵥ ζ q) := by
  rw [Dprefix_eq_smul_rotJ_add α' w Ω ζ q, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.add_mulVec, Matrix.smul_mulVec, Dprefix_zero_transpose_mulVec_eq_zero w Ω ζ hζ q,
    add_zero]

/-- **The `α' ≠ 0` caveat, quantitatively.** For a transverse wavevector field, the component `0`
of the wavevector right-hand side is `−α' (ζ_q)₁`; it vanishes for all `q` only if `α' = 0` or
every `(ζ_q)₁ = 0`. So `α' = 0` is exactly what keeps the transverse configuration stationary. -/
theorem layerZetaRHS_apply_zero (α' : ℝ) (w Ω : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ)
    (hζ : ∀ q, ζ q 0 = 0) (q : ℕ) :
    layerZetaRHS α' w Ω ζ q 0 = -(α' * ζ q 1) := by
  show -((Dprefix α' w Ω ζ q)ᵀ *ᵥ ζ q) 0 = -(α' * ζ q 1)
  rw [Dprefix_transpose_mulVec α' w Ω ζ hζ q, Pi.smul_apply, smul_eq_mul,
    transpose_rotJ_mulVec_apply_zero]

/-! ### Concrete evaluations -/

/-- **The fixed point is not the zero state.** In the concrete configuration `ζ_q = ![0,1]` every
wavevector is nonzero. -/
example (q : ℕ) : (fun _ : ℕ => (![0, 1] : Fin 2 → ℝ)) q ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  norm_num at h1

/-- **The trap fires on the concrete nonzero configuration.** `e₀ = ![0,1]`,
`λ = w = Θ = Ω = 1`, `ζ_q = ![0,1]`: all three right-hand sides vanish at octave `0`. -/
example :
    layerZetaRHS 0 (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => ![0, 1]) 0 = 0
    ∧ layerThetaRHS ![0, 1] (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
        (fun _ => (1 : ℝ)) (fun _ => ![0, 1]) 0 = 0
    ∧ layerOmegaRHS (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => ![0, 1]) 0 = 0 :=
  layerRHS_eq_zero_of_transverse ![0, 1] (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
    (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => ![0, 1]) (by simp) (fun _ => by simp) 0

/-- **The accumulated gradient in the concrete configuration.** With `e₀ = ![0,1]`,
`λ = w = Θ = 1` and `ζ_j = ![0,1]` (so `e_j = ![0,1]` and `A_j = −λ_j|ζ_j|Θ_j = −1`),

    G_{<2} = −e₀ − (w_0 A_0 e_0 + w_1 A_1 e_1) = −![0,1] − (−![0,1] − ![0,1]) = ![0,1].

So `G_{<2} = ![0,-1 + 2] = ![0,1]`: the two lower octaves each contribute `![0,-1]`, cancelling
the background `−e₀ = ![0,-1]` up to one unit. -/
example :
    Gprefix ![0, 1] (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
        (fun _ => ![0, 1]) 2 = ![0, 1] := by
  funext i
  fin_cases i <;>
    norm_num [Gprefix, layerGradScalar, unitVec, l2norm, Finset.sum_range_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- **The cheap form of the caveat.** `J ![1,1] = ![-1,1]` has nonzero component `0`. -/
example : (rotJ *ᵥ (fun _ : Fin 2 => (1 : ℝ))) 0 ≠ 0 := by
  rw [rotJ_mulVec]
  norm_num [Matrix.cons_val_zero, Matrix.head_cons]

/-- **The caveat at `α' = 1`.** The concrete transverse configuration is *not* stationary once the
rotation rate is turned on: `layerZetaRHS 1 … 0 0 = −1 ≠ 0`. -/
example :
    layerZetaRHS 1 (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => ![0, 1]) 0 0 ≠ 0 := by
  rw [layerZetaRHS_apply_zero 1 (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => ![0, 1])
    (fun _ => by simp) 0]
  norm_num [Matrix.cons_val_one, Matrix.head_cons]

end Cascade

#print axioms Cascade.Gprefix_apply_zero
#print axioms Cascade.abVortCoeff_eq_zero
#print axioms Cascade.abTempCoeff_eq_zero
#print axioms Cascade.rotJ_mulVec_apply_one
#print axioms Cascade.unitVec_apply_zero
#print axioms Cascade.Dprefix_zero_row_one
#print axioms Cascade.Dprefix_zero_transpose_mulVec_eq_zero
#print axioms Cascade.layerZetaRHS_eq_zero
#print axioms Cascade.layerRHS_eq_zero_of_transverse
#print axioms Cascade.Dprefix_eq_smul_rotJ_add
#print axioms Cascade.Dprefix_row_one_apply
#print axioms Cascade.transpose_rotJ_mulVec_apply_zero
#print axioms Cascade.Dprefix_transpose_mulVec
#print axioms Cascade.layerZetaRHS_apply_zero
