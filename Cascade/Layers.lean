import Cascade.Phase
import Cascade.PhaseControl

/-!
# Stage H — one wavevector per octave: AB eq. (3.3) and the triangular layer model

`Cascade/Phase.lean` and `Cascade/PhaseControl.lean` restored the *phase* of a **single**
wavevector. The lacunary ansatz had thrown away the direction of the wave, and the coupling
`b = lam zeta_1 = abVortCoeff lam zeta` was recovered there as a steerable cosine in a **free**
rotation angle `alpha`. In that single-wavevector picture the steering angle is a control
parameter: `phase_flip_quantitative` sweeps the whole interval `[-|lam| |zeta0|, |lam| |zeta0|]`,
so growth versus oscillation can be dialled at will.

Alpöge–Buckmaster eq. (3.3) is a *different* model. There is **one wavevector per octave**: the
`q`-th octave carries amplitudes `(Theta_q, Omega_q)`, its own wavevector `zeta_q`, and a
frequency `lam_q`, and it is driven **one-way** by the accumulated background of the octaves
below it,

    G_{<q} = -e_0 - sum_{j<q} w_j A_j e_j,           A_j = -lam_j |zeta_j| Theta_j,
    D_{<q} = alpha' J + sum_{j<q} w_j Omega_j (J e_j) (x) e_j,

with unit vectors `e_j = zeta_j/|zeta_j|` (AB eq. (3.3)). The `q`-th octave then evolves by
AB eq. (3.2) with **that** accumulated background in place of a frozen one:

    zeta_q' = -D_{<q}^T zeta_q,   Theta_q' = a_q Omega_q,   Omega_q' = b_q Theta_q,
    a_q = abTempCoeff lam_q zeta_q G_{<q},   b_q = abVortCoeff lam_q zeta_q = lam_q (zeta_q)_0.

The `lam_q |zeta_q|^2` denominators and the `G`, `D` assembled from the lower octaves are exactly
what the scope note of `Phase.lean` flagged as "the next step".

Two structural points are the content of this file.

* **The phase is no longer a free control.** In the single-wavevector model the steering angle
  `alpha` was arbitrary. Here `zeta_q'` is forced by `D_{<q}`, which is assembled from the
  *lower* octaves' `Omega_j` and `zeta_j`; the accumulated gradient `G_{<q}` is likewise built
  from the lower octaves' `Theta_j` and `zeta_j`. Only the common rotation rate `alpha'`
  (equivalently the common rotation `alpha`) remains a free background parameter — the
  individual phases are determined by the cascade beneath them. The definitional identities
  `Gprefix_succ` / `Dprefix_succ` make precise how one new octave is appended to the prefix.

* **Triangularity.** `G_{<q}` and `D_{<q}` mention only octaves `j < q`, and octave `q`'s own
  right-hand side mentions `zeta_q`, `Theta_q`, `Omega_q` and nothing higher. Hence altering only
  octaves `j > q` cannot change octave `q`'s equation: this is
  `layerRHS_congr_of_agree_le`. It is Tao's "barely any feedback from high frequency waves back
  into the low frequency components" made structural — the layer model is triangular by
  construction, which is what makes the generation-by-generation (greedy) construction of AB
  possible. The incremental identities `Gprefix_succ` / `Dprefix_succ` are the induction step of
  that construction.

**Scope.** This file is the *realisation* of the one-wavevector-per-octave layer model and of its
one-way structure. It is **not** the blowup: no claim is made here that the coupled system
develops a singularity. The forced blowup (Stage B) is what will use this triangular layer model.

## Conventions

Following `Phase.lean`, `|zeta|` is the explicit Euclidean length `l2norm zeta`, never the
ambient `‖·‖` on `Fin 2 → ℝ` (which is the sup norm). The layer ODEs are recorded as
**right-hand sides** (`layerZetaRHS`, `layerThetaRHS`, `layerOmegaRHS`) rather than `HasDerivAt`
statements: the matrix-valued prefix `D_{<q}` lives in `Matrix (Fin 2) (Fin 2) ℝ`, which carries
no topological (norm) instance at this pin, so a derivative at matrix type is not even
well-formed. The `Nat`-indexed prefix is a `Finset.range q` sum; the theorems below are the base
cases, the increment steps, and the congruence (triangularity) statement.
-/

noncomputable section

namespace Cascade

open scoped Matrix

variable (α' : ℝ) (e0 : Fin 2 → ℝ) (lam w : ℕ → ℝ) (Θ Ω : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ)

/-! ## The layer data and AB (3.3) -/

/-- The unit vector in the direction of `v`: `e_j = ζ_j/|ζ_j|`.

(`l2norm` is the Euclidean length; see the module docstring.) -/
def unitVec (v : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => v i / l2norm v

/-- AB's per-layer temperature-gradient scalar `A_j = −λ_j|ζ_j|Θ_j`. -/
def layerGradScalar (lam : ℕ → ℝ) (Θ : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ) (j : ℕ) : ℝ :=
  -(lam j * l2norm (ζ j) * Θ j)

/-- AB's accumulated lower-octave temperature gradient `G_{<q} = −e₀ − Σ_{j<q} w_j A_j e_j`
(Alpöge–Buckmaster eq. (3.3)).

It is the background seen by octave `q`: only octaves `j < q` contribute, each through its own
gradient scalar `A_j = layerGradScalar lam Θ ζ j` and its own unit wavevector
`e_j = unitVec (ζ j)`. -/
def Gprefix (e0 : Fin 2 → ℝ) (lam w : ℕ → ℝ) (Θ : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ) (q : ℕ) : Fin 2 → ℝ :=
  fun i => -(e0 i) - ∑ j ∈ Finset.range q, w j * layerGradScalar lam Θ ζ j * unitVec (ζ j) i

/-- AB's accumulated lower-octave deformation
`D_{<q} = α' • J + Σ_{j<q} w_j Ω_j • (J e_j) ⊗ e_j` (Alpöge–Buckmaster eq. (3.3)).

`Matrix.vecMulVec u v` is the outer product `(i,j) ↦ u i * v j`, so the `j`-th term is the
rank-one matrix `(J e_j) ⊗ e_j`, weighted by `w_j Ω_j`. -/
def Dprefix (α' : ℝ) (w : ℕ → ℝ) (Ω : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ) (q : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  α' • rotJ + ∑ j ∈ Finset.range q, (w j * Ω j) • Matrix.vecMulVec (rotJ *ᵥ unitVec (ζ j)) (unitVec (ζ j))

/-! ## The layer right-hand sides — AB (3.2) with each octave's own accumulated background -/

/-- `ζ̇_q = −D_{<q}ᵀ ζ_q`: AB's wavevector equation for octave `q`, driven by the accumulated
deformation of the octaves below it. -/
def layerZetaRHS (α' : ℝ) (w : ℕ → ℝ) (Ω : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ) (q : ℕ) : Fin 2 → ℝ :=
  fun i => -(((Dprefix α' w Ω ζ q)ᵀ) *ᵥ ζ q) i

/-- `Θ̇_q = a_q Ω_q`, where `a_q` is AB's temperature coefficient for the accumulated background
`G_{<q}`: `a_q = abTempCoeff (lam q) (ζ q) (Gprefix … q)`. -/
def layerThetaRHS (e0 : Fin 2 → ℝ) (lam w : ℕ → ℝ) (Θ Ω : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ) (q : ℕ) : ℝ :=
  abTempCoeff (lam q) (ζ q) (Gprefix e0 lam w Θ ζ q) * Ω q

/-- `Ω̇_q = b_q Θ_q`, where `b_q = λ_q (ζ_q)₀` is AB's buoyancy coupling: octave `q`'s own
gravity-direction component. -/
def layerOmegaRHS (lam : ℕ → ℝ) (Θ : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ) (q : ℕ) : ℝ :=
  abVortCoeff (lam q) (ζ q) * Θ q

/-! ## Base cases and the incremental (greedy) identities

These are the induction step of AB's generation-by-generation construction: the prefix for
`q + 1` is the prefix for `q` with exactly one new octave appended. -/

/-- The empty prefix has no lower octaves: `G_{<0} = −e₀`. -/
theorem Gprefix_zero : Gprefix e0 lam w Θ ζ 0 = fun i => -(e0 i) := by
  funext i
  simp [Gprefix]

/-- The empty prefix has no lower octaves: `D_{<0} = α' • J`. -/
theorem Dprefix_zero : Dprefix α' w Ω ζ 0 = α' • rotJ := by
  simp [Dprefix]

/-- **Incremental step for `G`.** `G_{<q+1}` is `G_{<q}` with octave `q`'s own contribution
`−w_q A_q e_q` appended — the greedy construction appends one octave at a time. -/
theorem Gprefix_succ (q : ℕ) :
    Gprefix e0 lam w Θ ζ (q + 1)
      = fun i => Gprefix e0 lam w Θ ζ q i
          - w q * layerGradScalar lam Θ ζ q * unitVec (ζ q) i := by
  funext i
  simp only [Gprefix, Finset.sum_range_succ]
  ring

/-- **Incremental step for `D`.** `D_{<q+1}` is `D_{<q}` with octave `q`'s rank-one
contribution `w_q Ω_q • (J e_q) ⊗ e_q` appended. -/
theorem Dprefix_succ (q : ℕ) :
    Dprefix α' w Ω ζ (q + 1)
      = Dprefix α' w Ω ζ q
        + (w q * Ω q) • Matrix.vecMulVec (rotJ *ᵥ unitVec (ζ q)) (unitVec (ζ q)) := by
  simp only [Dprefix, Finset.sum_range_succ]
  abel

/-! ## Triangularity — the headline -/

/-- `G_{<q}` depends on the lower octaves only through the values `Θ j`, `ζ j` for `j < q`. -/
theorem Gprefix_congr {Θ Θ' : ℕ → ℝ} {ζ ζ' : ℕ → Fin 2 → ℝ} {q : ℕ}
    (h : ∀ j, j < q → Θ j = Θ' j ∧ ζ j = ζ' j) :
    Gprefix e0 lam w Θ ζ q = Gprefix e0 lam w Θ' ζ' q := by
  funext i
  simp only [Gprefix]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨hΘ, hζ⟩ := h j (Finset.mem_range.mp hj)
  simp only [layerGradScalar, unitVec]
  rw [hΘ, hζ]

/-- `D_{<q}` depends on the lower octaves only through the values `Ω j`, `ζ j` for `j < q`. -/
theorem Dprefix_congr {Ω Ω' : ℕ → ℝ} {ζ ζ' : ℕ → Fin 2 → ℝ} {q : ℕ}
    (h : ∀ j, j < q → Ω j = Ω' j ∧ ζ j = ζ' j) :
    Dprefix α' w Ω ζ q = Dprefix α' w Ω' ζ' q := by
  have hsum : (∑ j ∈ Finset.range q, (w j * Ω j) • Matrix.vecMulVec (rotJ *ᵥ unitVec (ζ j)) (unitVec (ζ j)))
      = (∑ j ∈ Finset.range q, (w j * Ω' j) • Matrix.vecMulVec (rotJ *ᵥ unitVec (ζ' j)) (unitVec (ζ' j))) := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hΩ, hζ⟩ := h j (Finset.mem_range.mp hj)
    rw [hΩ, hζ]
  simp only [Dprefix]
  rw [hsum]

/-- **No feedback from higher octaves.** The equation of octave `q` is unchanged if only octaves
`j > q` are altered: the layer model is triangular.

`G_{<q}` and `D_{<q}` use only octaves `j < q`, and octave `q`'s own right-hand side uses only
`ζ_q`, `Θ_q`, `Ω_q`; hence agreeing on octaves `j ≤ q` forces the three right-hand sides at `q`
to agree. This is Tao's "barely any feedback from high frequency waves back into the low
frequency components", made structural. -/
theorem layerRHS_congr_of_agree_le {Θ Θ' Ω Ω' : ℕ → ℝ} {ζ ζ' : ℕ → Fin 2 → ℝ} {q : ℕ}
    (h : ∀ j, j ≤ q → Θ j = Θ' j ∧ Ω j = Ω' j ∧ ζ j = ζ' j) :
    layerZetaRHS α' w Ω ζ q = layerZetaRHS α' w Ω' ζ' q
    ∧ layerThetaRHS e0 lam w Θ Ω ζ q = layerThetaRHS e0 lam w Θ' Ω' ζ' q
    ∧ layerOmegaRHS lam Θ ζ q = layerOmegaRHS lam Θ' ζ' q := by
  have hD : Dprefix α' w Ω ζ q = Dprefix α' w Ω' ζ' q :=
    Dprefix_congr α' w (fun j hj => ⟨(h j (le_of_lt hj)).2.1, (h j (le_of_lt hj)).2.2⟩)
  have hG : Gprefix e0 lam w Θ ζ q = Gprefix e0 lam w Θ' ζ' q :=
    Gprefix_congr e0 lam w (fun j hj => ⟨(h j (le_of_lt hj)).1, (h j (le_of_lt hj)).2.2⟩)
  have hq := h q le_rfl
  refine ⟨?_, ?_, ?_⟩
  · funext i
    simp only [layerZetaRHS]
    rw [hD, hq.2.2]
  · simp only [layerThetaRHS]
    rw [hG, hq.2.2, hq.2.1]
  · simp only [layerOmegaRHS]
    rw [hq.2.2, hq.1]

/-! ## The coupling is that octave's own gravity-component -/

/-- **The buoyancy coupling of octave `q` is its own gravity-direction component**, `b_q = λ_q (ζ_q)₀`.
This is where the "phase is determined by the cascade below" enters: `b_q` is read off octave
`q`'s own, lower-octave-driven wavevector. -/
theorem layerOmegaRHS_eq (lam : ℕ → ℝ) (Θ : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ) (q : ℕ) :
    layerOmegaRHS lam Θ ζ q = lam q * ζ q 0 * Θ q := by
  simp [layerOmegaRHS, abVortCoeff]

/-! ## Non-vacuity checks -/

/-- **Non-vacuity of `Gprefix` against AB (3.3), two octaves.** With `e0 = ![1,0]`, `λ = w = 1`,
`ζ_j = ![1,0]` (so `e_j = ![1,0]`) and `Θ_0 = 3`, `Θ_1 = 5`, the AB (3.3) prefix is

    G_{<2} = −e₀ − (w_0 A_0 e_0 + w_1 A_1 e_1) = −![1,0] − ((−3) + (−5)) ![1,0] = ![7,0],

because `A_j = −λ_j |ζ_j| Θ_j = −Θ_j`. -/
example :
    Gprefix ![1,0] (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
        (fun j => if j = 0 then 3 else 5) (fun _ => ![1,0]) 2
      = ![7, 0] := by
  funext i
  fin_cases i <;>
    norm_num [Gprefix, layerGradScalar, unitVec, l2norm, Finset.sum_range_succ, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]

/-- **Non-vacuity of `Dprefix` against AB (3.3), two octaves.** With `α' = 1`, `w_j = 1`,
`ζ_j = ![1,0]` (so `J e_j = ![0,1]`) and `Ω_0 = 2`, `Ω_1 = 4`, the AB (3.3) prefix is

    D_{<2} = α' J + (w_0 Ω_0) (J e_0) ⊗ e_0 + (w_1 Ω_1) (J e_1) ⊗ e_1
           = !![0,−1;1,0] + 2 !![0,0;1,0] + 4 !![0,0;1,0] = !![0,−1;7,0]. -/
example :
    Dprefix (1 : ℝ) (fun _ => (1 : ℝ)) (fun j => if j = 0 then 2 else 4)
        (fun _ => ![1,0]) 2
      = !![0, -1; 7, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Dprefix, unitVec, l2norm, Finset.sum_range_succ, rotJ, Matrix.vecMulVec,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecHead, Matrix.vecTail]

/-- **Non-vacuity of the triangularity theorem.** Taking the two triples of data to be equal
outright satisfies the agreement hypothesis, and then the theorem's conclusion is trivial:
`layerRHS_congr_of_agree_le` is not vacuous. (The content is that the hypothesis is only required
for `j ≤ q`; octaves `j > q` are unconstrained.) -/
example (α' : ℝ) (e0 : Fin 2 → ℝ) (lam w : ℕ → ℝ) (Θ Ω : ℕ → ℝ) (ζ : ℕ → Fin 2 → ℝ) (q : ℕ) :
    layerZetaRHS α' w Ω ζ q = layerZetaRHS α' w Ω ζ q
    ∧ layerThetaRHS e0 lam w Θ Ω ζ q = layerThetaRHS e0 lam w Θ Ω ζ q
    ∧ layerOmegaRHS lam Θ ζ q = layerOmegaRHS lam Θ ζ q :=
  layerRHS_congr_of_agree_le α' e0 lam w (fun _ _ => ⟨rfl, rfl, rfl⟩)

end Cascade

#print axioms Cascade.Gprefix_zero
#print axioms Cascade.Dprefix_zero
#print axioms Cascade.Gprefix_succ
#print axioms Cascade.Dprefix_succ
#print axioms Cascade.Gprefix_congr
#print axioms Cascade.Dprefix_congr
#print axioms Cascade.layerRHS_congr_of_agree_le
#print axioms Cascade.layerOmegaRHS_eq
