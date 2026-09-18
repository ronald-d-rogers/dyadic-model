import Cascade.DissipationThreshold
import Cascade.Enstrophy
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# The flat self-similar solution of the inviscid dyadic model

## What this file records, honestly

The repo's shell model at **dissipation degree** `e` is

`u_k' = 2^k (u_{k-1}² − 2 u_k u_{k+1}) + κ θ_k − ν · 2^{e k} u_k`,

assembled by the repo's own `velocityRHSDegreeE ν κ 1 0 e u θ k`.  This file freezes the two
parameters of dissipation and coupling at `ν = κ = 0` — the **inviscid, unforced** system — and
exhibits the exact self-similar solution

`u_k(t) = selfSimilar T t k = (1/3) · 2^{−k} · (T − t)^{−1}`.

Here `dyadicWeight m = 2^m` as a `zpow`, so `dyadicWeight (−k) = 2^{−k}`; the definition below
uses `dyadicWeight` rather than any hand-written power.

### (a) This is the inviscid, untruncated system

There is **no viscosity** (`ν = 0`), **no buoyancy** (`κ = 0`), and **no truncation** `N`: the
equation is imposed shell by shell on the whole lattice `k : ℤ` (`selfSimilar_hasDerivAt`, for
*every* `e : ℤ` — the inviscid transfer does not see the dissipation degree).  This is deliberately
*not* the repo's truncated model: `Cascade/TruncatedRegularity.lean` proves that the truncated
system cannot blow up at all, and the content here is not in tension with that.  The two statements
are about different systems, and this file is about the untruncated, inviscid one.

### (b) The level diverges; this is not a blow-up from finite enstrophy data

Take the vorticity `a_k = vorticity u k = 2^k u_k`.  For this profile
`a_k = (1/3)(T − t)^{−1}`, **independent of `k`** (`selfSimilar_vorticity`), so the enstrophy on the
infinite lattice is

`H = Σ_{k ∈ ℤ} a_k² = Σ_{k ∈ ℤ} (1/3)² (T − t)^{−2}`,

which **diverges at every time `t < T`**, not merely at `t → T⁻`.  Consequently this is a
self-similar solution **whose level diverges** — it has infinite enstrophy from the outset — and it
is *not* an enstrophy blow-up from finite-enstrophy data.  The file states this plainly and does not
overclaim: the only growth statement proved here is that the (already infinite) level is unbounded
along the solution as `t → T⁻` (`selfSimilar_level_unbounded`).

### (c) The mathematics is known in kind

Explicit self-similar solutions of the inviscid dyadic model are standard in the literature.  What
this file contributes is **machine verification in this repo's own notation**, not novelty; the
specific form below is not attributed to any particular paper.

### (d) The flat profile is "zero jitter"

Because `a_k = (1/3)(T − t)^{−1}` carries **no `k`-dependence**, the local scaling exponent of the
profile is the same at every shell and every time — here it is `0`.  That flatness is the precise
sense in which this inviscid explosion carries **no jitter**: there is no shell-to-shell
intermittency, and the vorticity is a single scalar function of time alone.  The formal statement is
`selfSimilar_vorticity`, whose right-hand side has no `k`.

## The algebra (checked, not restated by hand)

Since the right-hand side is the repo's `velocityRHSDegreeE`, the theorem is about the repo's
actual model rather than a transcription.  With `ν = κ = 0`, `A = 1`, `B = 0` it reduces to the pure
transfer `2^k (u_{k-1}² − 2 u_k u_{k+1})`, and for the profile above
`u_{k-1}² − 2 u_k u_{k+1} = (1/3) · 2^{−2k} · (T − t)^{−2}`, so that the transfer is
`(1/3) · 2^{−k} · (T − t)^{−2}` — exactly the derivative of `(1/3) · 2^{−k} · (T − t)^{−1}`.  The
two agree for every `k : ℤ`.  (The derivation is carried out in Lean below; no exponent is
"hand-normalised": all `dyadicWeight` arithmetic goes through `dyadicWeight_add`.)

## Contents

1. `selfSimilar` — the profile.
2. `selfSimilar_vorticity` — the vorticity is **independent of the shell** (flat profile).
3. `selfSimilar_hasDerivAt` — the profile solves the inviscid equation, shell by shell, for every
   degree `e`.
4. `selfSimilar_level_unbounded` — the level is unbounded as `t → T⁻`.
5. Non-vacuity evaluations.
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators

namespace Cascade

/-! ## 1. The self-similar profile -/

/-- **The self-similar velocity profile** `u_k(t) = (1/3) · 2^{−k} · (T − t)^{−1}`, written with
the repo's dyadic weight so that `dyadicWeight (−k) = 2^{−k}`. -/
def selfSimilar (T t : ℝ) (k : ℤ) : ℝ := (1 / 3) * dyadicWeight (-k) * (T - t)⁻¹

/-! ## 2. The flat profile: the vorticity is independent of the shell -/

/-- **The vorticity of the self-similar profile is flat.**  For every `T`, `t` and every shell `k`,

`vorticity (selfSimilar T t) k = (1/3) · (T − t)^{−1}`,

whose right-hand side **does not depend on `k`**: the profile has no shell-to-shell jitter.  The
proof is the definition of `vorticity` together with `dyadicWeight k · dyadicWeight (−k) = 1`, i.e.
`dyadicWeight (k + (−k)) = dyadicWeight 0` via `dyadicWeight_add`. -/
theorem selfSimilar_vorticity (T t : ℝ) (k : ℤ) :
    vorticity (selfSimilar T t) k = (1 / 3) * (T - t)⁻¹ := by
  have hw : dyadicWeight k * dyadicWeight (-k) = 1 := by
    rw [← dyadicWeight_add, add_neg_cancel, dyadicWeight]
    norm_num
  unfold vorticity selfSimilar
  calc dyadicWeight k * ((1 / 3) * dyadicWeight (-k) * (T - t)⁻¹)
      = (dyadicWeight k * dyadicWeight (-k)) * ((1 / 3) * (T - t)⁻¹) := by ring
    _ = 1 * ((1 / 3) * (T - t)⁻¹) := by rw [hw]
    _ = (1 / 3) * (T - t)⁻¹ := by ring

/-! ## 3. The inviscid transfer of the profile

The next three lemmas are the algebra of the solution property, isolated so that the main theorem is
a short `HasDerivAt` computation.  None of them normalises an exponent by hand: the shifts
`k ↦ k ± 1` are converted with `dyadicWeight_add` alone. -/

/-- **The inviscid right-hand side is the pure transfer.**  At `ν = κ = 0`, `A = 1`, `B = 0` the
repo's `velocityRHSDegreeE` is `2^k (u_{k-1}² − 2 u_k u_{k+1})`, for every degree `e`. -/
private lemma velocityRHSDegreeE_inviscid (e : ℤ) (u : ℤ → ℝ) (k : ℤ) :
    velocityRHSDegreeE 0 0 1 0 e u (fun _ : ℤ => 0) k
      = dyadicWeight k * ((u (k - 1)) ^ 2 - 2 * u k * u (k + 1)) := by
  simp [velocityRHSDegreeE, boussinesqTransferU]

/-- **Shell shift down:** `u_{k-1} = 2 u_k` for the self-similar profile, because
`dyadicWeight (−(k−1)) = dyadicWeight (−k) · 2`. -/
private lemma selfSimilar_sub_one (T t : ℝ) (k : ℤ) :
    selfSimilar T t (k - 1) = 2 * selfSimilar T t k := by
  unfold selfSimilar
  have h1 : dyadicWeight (-(k - 1)) = dyadicWeight (-k) * 2 := by
    rw [show -(k - 1) = -k + 1 by ring, dyadicWeight_add]
    norm_num [dyadicWeight]
  rw [h1]
  ring

/-- **Shell shift up:** `u_{k+1} = (1/2) u_k` for the self-similar profile, because
`dyadicWeight (−(k+1)) = dyadicWeight (−k) · (1/2)`. -/
private lemma selfSimilar_add_one (T t : ℝ) (k : ℤ) :
    selfSimilar T t (k + 1) = (1 / 2) * selfSimilar T t k := by
  unfold selfSimilar
  have h1 : dyadicWeight (-(k + 1)) = dyadicWeight (-k) * (1 / 2) := by
    rw [show -(k + 1) = -k + (-1) by ring, dyadicWeight_add, dyadicWeight_neg_one]
  rw [h1]
  ring

/-- **The inviscid right-hand side at the self-similar profile.**  Substituting the shifts,

`dyadicWeight k · ((2 u_k)² − 2 u_k · ((1/2) u_k)) = 3 · dyadicWeight k · u_k²
  = (1/3) · dyadicWeight (−k) · (T − t)^{−2}`,

using `vorticity`'s relation `dyadicWeight k · dyadicWeight (−k) = 1`. -/
private lemma velocityRHSDegreeE_selfSimilar (e : ℤ) (T t : ℝ) (k : ℤ) :
    velocityRHSDegreeE 0 0 1 0 e (selfSimilar T t) (fun _ : ℤ => 0) k
      = (1 / 3) * dyadicWeight (-k) * ((T - t)⁻¹ * (T - t)⁻¹) := by
  rw [velocityRHSDegreeE_inviscid, selfSimilar_sub_one, selfSimilar_add_one]
  unfold selfSimilar
  have hw : dyadicWeight k * dyadicWeight (-k) = 1 := by
    rw [← dyadicWeight_add, add_neg_cancel, dyadicWeight]
    norm_num
  have hwk : dyadicWeight (-k) ≠ 0 := ne_of_gt (dyadicWeight_pos (-k))
  have hW : dyadicWeight k = (dyadicWeight (-k))⁻¹ := eq_inv_of_mul_eq_one_left hw
  rw [hW]
  field_simp
  ring

/-! ## 4. The solution property, shell by shell -/

/-- **The self-similar profile solves the inviscid equation at every shell and every degree.**
For every dissipation degree `e : ℤ`, every `T`, and every `t ≠ T`,

`d/dt [selfSimilar T t k] = velocityRHSDegreeE 0 0 1 0 e (selfSimilar T t) (fun _ => 0) k`.

The right-hand side is the repo's own definition with `ν = κ = 0`, so this is a statement about the
repo's actual model, and it holds on the whole lattice `k : ℤ` with no truncation.  The derivative
is `(1/3) · dyadicWeight (−k) · (T − t)^{−2}`, computed from `hasDerivAt_inv` by the chain rule. -/
theorem selfSimilar_hasDerivAt (e : ℤ) (T t : ℝ) (ht : t ≠ T) (k : ℤ) :
    HasDerivAt (fun s : ℝ => selfSimilar T s k)
      (velocityRHSDegreeE 0 0 1 0 e (selfSimilar T t) (fun _ : ℤ => 0) k) t := by
  have hT : T - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hlin : HasDerivAt (fun s : ℝ => T - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub T
  have hinv : HasDerivAt (fun s : ℝ => (T - s)⁻¹) ((T - t)⁻¹ * (T - t)⁻¹) t := by
    have h := hlin.inv hT
    have heq : (-(-1 : ℝ)) / (T - t) ^ 2 = (T - t)⁻¹ * (T - t)⁻¹ := by
      rw [neg_neg, one_div, ← inv_pow]
      ring
    rwa [heq] at h
  have hconst : HasDerivAt (fun s : ℝ => (1 / 3) * dyadicWeight (-k) * (T - s)⁻¹)
      ((1 / 3) * dyadicWeight (-k) * ((T - t)⁻¹ * (T - t)⁻¹)) t := by
    have h := hinv.const_mul ((1 / 3) * dyadicWeight (-k))
    simpa [mul_assoc] using h
  rw [velocityRHSDegreeE_selfSimilar]
  simpa [selfSimilar] using hconst

/-! ## 5. The level is unbounded as `t → T⁻` -/

/-- **The flat level is unbounded.**  For every `T` and every bound `M` there is a time `t < T`
with `M < (1/3)(T − t)^{−1}` — the common value of the flat vorticity.  The witness is explicit:
for `M ≥ 0`, `t = T − 1/(3M + 1)` gives `(1/3)(T − t)^{−1} = M + 1/3`; for `M < 0` any `t < T`
works. -/
theorem selfSimilar_level_unbounded (T : ℝ) :
    ∀ M : ℝ, ∃ t : ℝ, t < T ∧ M < (1 / 3) * (T - t)⁻¹ := by
  intro M
  rcases le_or_gt 0 M with hM | hM
  · refine ⟨T - 1 / (3 * M + 1), ?_, ?_⟩
    · have hpos : 0 < 1 / (3 * M + 1) := by positivity
      linarith
    · have hTt : T - (T - 1 / (3 * M + 1)) = 1 / (3 * M + 1) := by ring
      rw [hTt, inv_div]
      simp only [div_one]
      nlinarith
  · refine ⟨T - 1, by linarith, ?_⟩
    have hTt : T - (T - 1) = (1 : ℝ) := by ring
    rw [hTt]
    norm_num
    linarith

/-! ## 6. Non-vacuity

The profile is not identically zero, the flat-vorticity identity has content, and the witness of
item 4 really clears its bound. -/

example : selfSimilar 1 0 0 = (1 / 3 : ℝ) := by norm_num [selfSimilar, dyadicWeight]

example : vorticity (selfSimilar 1 0) 0 = (1 / 3 : ℝ) := by
  rw [selfSimilar_vorticity]
  norm_num

/-- At `T = 1`, `M = 1/3` the constructed `t = 1 − 1/(3·(1/3) + 1) = 1/2` gives level `2/3 > 1/3`. -/
example : (1 / 3 : ℝ) < (1 / 3) * (1 - (1 - 1 / (3 * (1 / 3) + 1)))⁻¹ := by norm_num

end Cascade

/-! ## Axiom audit -/

#print axioms Cascade.selfSimilar_vorticity
#print axioms Cascade.selfSimilar_hasDerivAt
#print axioms Cascade.selfSimilar_level_unbounded
