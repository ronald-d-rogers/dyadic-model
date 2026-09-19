/-
# The weighted Ruelle data of the full `p`-shift, and the rank-one functional equation

The cascade transfer operator carries a weight `w a` on each of the `p` branches.  This file records
the exact combinatorial content of the resulting Ruelle data, and one small lemma about zeta
functions that closes the "self-dual functional equation" question raised in `Cascade/ZETA.md` §4.

## What is proved, and what it means

* `sum_prod_eq_pow_sum`: the weighted periodic-point sum factorises,
  `∑_{f : Fin n → Fin p} ∏ k, w (f k) = (∑ a, w a) ^ n`.  Since `Fix(σ ^ n)` is indexed by the
  `n`-digit blocks (`PAdicZeta.fixEquiv`), this is exactly
  `∑_{x ∈ Fix(σ ^ n)} e ^ (S_n φ x) = (∑ a, w a) ^ n` for the potential `φ x = log (w (x 0))`.
* `rankOne_mulVec_one`: the level-1 transfer operator has matrix `M i j = w j`, and the constant
  vector is a Perron eigenvector with eigenvalue `∑ a, w a`.  With `M * M = (∑ a, w a) • M`
  (rank one) this is the finite spectrum `{∑ a, w a, 0, …, 0}`.
* `rankOne_functionalEquation`: a zeta of the form `1 / (1 - λ T)` **always** satisfies
  `ζ (1 / (λ ^ 2 * T)) = -(λ * T) * ζ T`.  The symmetry axis is `|T| = 1 / λ`, i.e. exactly the pole
  radius: the pole forces the axis, not the other way round.  This is why the hoped-for escape route
  of `Cascade/ZETA.md` §4 is closed — a self-duality that every rank-one zeta satisfies cannot
  select anything.

## Scope — stated narrowly, deliberately

The correct statement about blindness is *scoped to a single zeta of the full shift*:

* a **single** Ruelle zeta `ζ_φ(T) = 1 / (1 - (∑ a, w a) * T)` is a function of `∑ a, w a` alone, so
  two multiplier vectors with the same sum give the same zeta;
* the individual weights are **not** invisible in general: they are recovered from the pole locus
  `T_q = 1 / (∑ a, (w a) ^ q)` of the one-parameter **family** `ζ_{qφ}(T) = 1 / (1 - (∑ a, (w a)^q) * T)`,
  which is a different object.  An earlier draft of the surrounding prose said "the weights are
  invisible" without that qualification; it was wrong, and this is the corrected scope.

Also **not** claimed here: that `ζ_φ(T) = 1 / (1 - (∑ a, w a) * T)` as a zeta-function identity.  The
factorisation of the periodic-point sum is what is proved; converting it into a statement about `exp`
and `log` of formal power series is out of scope and is asserted, with its label, in `Cascade/ZETA.md`.

Note that `PAdicZeta.card_fixed_shift` (in `Shift.lean`) requires `0 < n`; the identity here is for
`f : Fin n → Fin p`, so it is the `n ≥ 0` statement, and at `n = 0` both sides are `1` trivially.
-/

import Mathlib

open scoped BigOperators

namespace PAdicZeta

/-- **The weighted word sum factorises.**  Summing `∏ k, w (f k)` over all `n`-digit blocks `f`
gives the `n`-th power of the total branch weight.  This is the exact content of
`∑_{x ∈ Fix(σ ^ n)} e ^ (S_n φ x) = (∑ a, w a) ^ n` for the symbol potential `φ x = log (w (x 0))`.

Proof: mathlib's `Fintype.sum_pow` is precisely this identity with the two sides exchanged. -/
theorem sum_prod_eq_pow_sum (p n : ℕ) (w : Fin p → ℝ) :
    (∑ f : Fin n → Fin p, ∏ k, w (f k)) = (∑ a, w a) ^ n :=
  (Fintype.sum_pow w n).symm

/-- **The constant vector is a Perron eigenvector of the level-1 transfer operator.**  The operator
has matrix `M i j = w j`, independent of the row index `i` — a rank-one matrix.  Its action on the
constant vector is multiplication by `∑ a, w a`. -/
theorem rankOne_mulVec_one (p : ℕ) (w : Fin p → ℝ) :
    Matrix.mulVec (Matrix.of (fun (_ i : Fin p) => w i)) (fun _ => (1 : ℝ))
      = (∑ a, w a) • (fun _ => (1 : ℝ)) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

/-- **The rank-one functional equation, in the inversion form.**  For `λ ≠ 0` and `T ≠ 0` with
`1 - λ * T ≠ 0`,

```
zeta (1 / (λ ^ 2 * T)) = -(λ * T) * zeta T ,      zeta T = 1 / (1 - λ * T) .
```

Three things this says, and one it does not:

* it **exists**, for every `λ`, so it is automatic for a rank-one zeta and cannot select anything
  within that family;
* the constant is `1 / λ ^ 2`, **not** `λ` — the naive choice `c = λ` gives a ratio that depends on
  `T`, so there is no functional equation of the form `ζ (λ / T) = χ T * ζ T`;
* the symmetry axis is `|T| = 1 / λ`, which is exactly the **pole radius**: the pole determines the
  axis, not the reverse;
* it does **not** say that the constant `1 / λ ^ 2` is unique among all `χ`.  Uniqueness among
  monomials `χ T = κ * T ^ m` is a degree count, written out and checked in
  `Cascade/zeta_checks.py` section E, and is not formalised here.  Note also that the *scaling* form
  `χ T * ζ (a * T) = ζ T` is a **different** symmetry with only the trivial solution `a = 1`;
  conflating the two forms is what made an earlier draft deny the existence of this one. -/
theorem rankOne_functionalEquation (K : Type*) [Field K] (lam T : K)
    (hlam : lam ≠ 0) (hT : T ≠ 0) (h1 : 1 - lam * T ≠ 0) :
    1 / (1 - lam * (1 / (lam ^ 2 * T))) = -lam * T * (1 / (1 - lam * T)) := by
  have key : (-1 + lam * T)⁻¹ * (1 - lam * T) = -1 := by
    rw [show (-1 + lam * T) = -(1 - lam * T) by ring, inv_neg, neg_mul,
      inv_mul_cancel₀ h1]
  field_simp
  rw [← key]
  ring

end PAdicZeta

#print axioms PAdicZeta.sum_prod_eq_pow_sum
#print axioms PAdicZeta.rankOne_mulVec_one
#print axioms PAdicZeta.rankOne_functionalEquation
