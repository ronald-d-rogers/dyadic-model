/-
# The isotropic profile of the dyadic tree cascade, and where it fails

The tree cascade of Barbato–Bianchi–Flandoli–Morandin, *A dyadic model on a tree*
(arXiv:1207.2846), eq. (1)/(7), reads

```
dX_j/dt = c_j X_{jbar}^2 - sum_{k in O_j} c_k X_j X_k ,      c_j = 2^{alpha |j|} ,   #O_j = b ,
```

with `X_{0bar}(t) ≡ f` a *forcing alias* for the father of the root: the root has no father, and in
the unforced model its source term is absent.

## What this file proves, and what it does NOT

The **isotropic** profile `X_n = σ / r^n` (generation `n`, `r = 2^alpha`) makes the generation
dependence of the per-node right-hand side cancel exactly, leaving the generation-independent
coefficient

```
r^2 - b = 4^alpha - N_* .
```

That is `isotropic_reduction`, and it holds **at every node that has a father**, i.e. for `n ≥ 1`.

**It does not hold at the root, and this file records that failure rather than hiding it.**
`isotropic_root_obstruction` shows that the root's equation for the profile reads
`-b σ^2 = σ^2 (r^2 - b)`, which holds only when `r = 0`. So:

* the isotropic profile is **not** a solution of the unforced rooted model, at any `α`;
* consequently it is not a counterexample to Theorem 2.1 of the paper, and the reduced coefficient
  `r^2 - b` is a statement about the **translation-invariant bulk recursion**, not about the model.

`isotropic_stationary_forced` gives the one case that *is* a genuine solution: in the **forced** model
with `r^2 = b` and `f = σ r`, both the root equation and every interior equation vanish, and the
profile is the paper's stationary solution — its exponent `α` then coincides with the paper's
`(2 α̃ + α)/3`, since `r^2 = b` means `log_2 b = 2α`.

## The correction this file records

An earlier version of `Cascade/ZETA.md` §6 claimed that "the isotropic manifold reduces the whole
tree to the single scalar ODE `σ' = (4^alpha - b) σ^2`". That is **wrong**: the root breaks the
translation invariance, and the energy balance

```
dE_n/dt = 2 c_0 X_{0bar}^2 X_0 - Pi_n ,      Pi_n = 2 sum_{|k| = n+1} c_k X_{kbar}^2 X_k
```

(for `f = ν = 0`) is violated by exactly the root's missing source, `2 σ^3 r^2` — the value the
profile implicitly assigns to a phantom father `X_{-1} = σ r`. The exact-arithmetic check in
`Cascade/zeta_checks.py` section I tests the interior identity, the root failure, and that residual.

Nothing here claims the isotropic manifold is invariant or attracting.
-/

import Mathlib

namespace Cascade

/-- The isotropic profile of the tree cascade: generation `n` carries amplitude `σ / r^n`. -/
noncomputable def isotropicProfile (σ r : ℝ) (n : ℕ) : ℝ := σ / r ^ n

/-- **The bulk reduction.**  At a node with a father, substituting `X_n = σ / r^n` into
`c_j X_{jbar}^2 - sum_{k in O_j} c_k X_j X_k` (with `c_n = r^n` and `b` sons) makes the generation
dependence cancel: the result is `σ^2 / r^n` times `r^2 - b`.

The coefficient vanishes exactly when `r^2 = b`, i.e. `2^{2 alpha} = N_*`, i.e.
`alpha = (1/2) log_2 N_*`.  That is the marginality of the **translation-invariant recursion**; it is
*not* a statement that the profile solves the rooted model at the root — see
`isotropic_root_obstruction`. -/
theorem isotropic_reduction (σ r : ℝ) (hr : r ≠ 0) (b : ℝ) (n : ℕ) :
    r ^ (n + 1) * (isotropicProfile σ r n) ^ 2
        - b * r ^ (n + 2) * isotropicProfile σ r (n + 1) * isotropicProfile σ r (n + 2)
      = σ ^ 2 / r ^ (n + 1) * (r ^ 2 - b) := by
  have h1 : r ^ (n + 1) ≠ 0 := pow_ne_zero _ hr
  have h2 : r ^ (n + 2) ≠ 0 := pow_ne_zero _ hr
  have h3 : r ^ n ≠ 0 := pow_ne_zero _ hr
  simp only [isotropicProfile]
  field_simp
  ring

/-- **The root obstruction.**  At the root of the unforced model (`f = 0`) the source term is absent,
so the profile's right-hand side there is `-b σ^2` rather than `σ^2 (r^2 - b)`.  The two agree only
when `r = 0` (with `σ ≠ 0`).  Hence the isotropic profile solves the unforced rooted model at no
`r ≠ 0`, and the "blow-up for `r^2 > b`" of the bulk recursion is not a property of the model. -/
theorem isotropic_root_obstruction (σ r b : ℝ) (hσ : σ ≠ 0) :
    -(b * σ ^ 2) = σ ^ 2 * (r ^ 2 - b) ↔ r = 0 := by
  have hσ2 : σ ^ 2 ≠ 0 := pow_ne_zero _ hσ
  constructor
  · intro h
    have : σ ^ 2 * r ^ 2 = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hσ2
    · exact pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h'
  · intro h
    rw [h]
    ring

/-- The threshold, as an equivalence: the bulk coefficient vanishes exactly at `r^2 = b`.  With
`r = 2^alpha` and `b = N_*`, this is `alpha = (1/2) log_2 N_* = alpha_tilde`. -/
theorem isotropic_coefficient_vanishes (r b : ℝ) : r ^ 2 - b = 0 ↔ r ^ 2 = b := by
  constructor <;> intro h <;> linarith

/-- **The multiplier form.**  `r^2 - b` factors as `b * (Λ^2 - 1)` with `Λ = r / sqrt b`, i.e.
`Λ = 2^{alpha - alpha_tilde}`; so marginality of the bulk coefficient is exactly `Λ = 1`. -/
theorem isotropic_multiplier (r b : ℝ) (hb : 0 < b) :
    r ^ 2 - b = b * ((r / Real.sqrt b) ^ 2 - 1) := by
  have hbne : b ≠ 0 := ne_of_gt hb
  rw [div_pow, Real.sq_sqrt (le_of_lt hb)]
  field_simp

/-- **The one case that is a genuine solution.**  In the *forced* model with `r^2 = b` and the forcing
alias set to the consistent phantom value `f = σ r`, the profile is stationary: the root's equation
`f^2 - b r X_0 X_1 = 0` and every interior equation `σ^2 / r^n * (r^2 - b) = 0` both vanish.  Its
exponent is the paper's stationary exponent: `r^2 = b` says `log_2 b = 2α`, so
`(2α̃ + α)/3 = (2α + α)/3 = α`. -/
theorem isotropic_stationary_forced (σ r b : ℝ) (hr : r ≠ 0) (hb : r ^ 2 = b) :
    (σ * r) ^ 2 - b * r * σ * (σ / r) = 0 ∧ σ ^ 2 * (r ^ 2 - b) = 0 := by
  constructor
  · rw [mul_pow, hb]
    field_simp
    ring
  · rw [hb]; ring

end Cascade

#print axioms Cascade.isotropic_reduction
#print axioms Cascade.isotropic_root_obstruction
#print axioms Cascade.isotropic_coefficient_vanishes
#print axioms Cascade.isotropic_multiplier
#print axioms Cascade.isotropic_stationary_forced
