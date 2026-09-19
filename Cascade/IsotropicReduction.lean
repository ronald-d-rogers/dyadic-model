/-
# The isotropic reduction of the dyadic tree cascade

The tree cascade of Barbato–Bianchi–Flandoli–Morandin, *A dyadic model on a tree*
(arXiv:1207.2846), eq. (1)/(7), reads

```
dX_j/dt = c_j X_{jbar}^2 - sum_{k in O_j} c_k X_j X_k ,      c_j = 2^{alpha |j|} ,   #O_j = b .
```

Each node gains from its single father (`c_j X_{jbar}^2`) and loses to its `b` sons
(`sum_{k in O_j} c_k X_j X_k`).  A node has one father and `b` sons.

## What this file proves

The **isotropic** profile `X_n = σ / r^n`, where `n` is the generation and `r = 2^alpha` is the
per-generation time-scale factor, makes the generation dependence cancel exactly:
`isotropic_reduction` says the right-hand side is `σ^2 / r^n` times the generation-independent
coefficient

```
r^2 - b = 4^alpha - N_* .
```

So the isotropic manifold reduces the whole tree to the single scalar ODE `σ' = (4^alpha - b) σ^2`,
and the coefficient vanishes exactly at

```
4^alpha = b = N_*   <=>   2^{2 alpha} = N_*   <=>   alpha = (1/2) log_2 N_* = alpha_tilde .
```

That is Barbato's threshold, and the `1/2` in it is the square in `4^alpha = (2^alpha)^2`: the model
is **quadratic in the amplitude** while the level count enters **linearly**.  Equivalently, the
multiplier is `Λ = 2^alpha / sqrt(N_*) = 2^{alpha - alpha_tilde} = 2^beta`, with `beta` the paper's
own `beta = alpha - alpha_tilde`; criticality is `Λ = 1`.

## Scope

* This is the reduction of the **isotropic** (generation-uniform) manifold only.  Nothing here claims
  the manifold is attracting, or that the full tree flow reduces to it from general data.
* The reduced ODE is **not** stated or proved here; this file proves the algebraic cancellation that
  produces its coefficient.  The ODE and its consequences are recorded, with labels, in
  `Cascade/ZETA.md` §6 and checked exactly in `Cascade/zeta_checks.py` section I.
* The paper contains **no** renormalisation operator (`grep -i renormali` on its LaTeX source returns
  nothing); the reduction here is this repository's, not a quotation.
-/

import Mathlib

namespace Cascade

/-- The isotropic profile of the tree cascade: generation `n` carries amplitude `σ / r^n`. -/
noncomputable def isotropicProfile (σ r : ℝ) (n : ℕ) : ℝ := σ / r ^ n

/-- **The isotropic reduction of the dyadic tree cascade.**  Substituting `X_n = σ / r^n` into
`dX_j/dt = c_j X_{jbar}^2 - sum_{k in O_j} c_k X_j X_k` with `c_j = 2^{alpha|j|}` (so `c_n = r^n`)
and `b` sons makes the generation dependence cancel: the right-hand side is `σ^2 / r^n` times the
generation-independent coefficient `r^2 - b`.

That coefficient is the whole threshold: it vanishes exactly when `r^2 = b`, i.e. when
`2^{2 alpha} = N_*`, i.e. `alpha = (1/2) log_2 N_*`. -/
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

/-- The threshold, as an equivalence: the renormalisation coefficient vanishes exactly at
`r^2 = b`.  With `r = 2^alpha` and `b = N_*`, this is `alpha = (1/2) log_2 N_* = alpha_tilde`. -/
theorem isotropic_coefficient_vanishes (r b : ℝ) : r ^ 2 - b = 0 ↔ r ^ 2 = b := by
  constructor <;> intro h <;> linarith

/-- **The multiplier form.**  `4^alpha - b` factors as `b * (Λ^2 - 1)` with
`Λ = 2^alpha / sqrt b`, i.e. `Λ = 2^{alpha - alpha_tilde} = 2^beta`; so criticality of the isotropic
coefficient is exactly `Λ = 1`. -/
theorem isotropic_multiplier (r b : ℝ) (hb : 0 < b) :
    r ^ 2 - b = b * ((r / Real.sqrt b) ^ 2 - 1) := by
  have hbne : b ≠ 0 := ne_of_gt hb
  rw [div_pow, Real.sq_sqrt (le_of_lt hb)]
  field_simp

end Cascade

#print axioms Cascade.isotropic_reduction
#print axioms Cascade.isotropic_coefficient_vanishes
#print axioms Cascade.isotropic_multiplier
