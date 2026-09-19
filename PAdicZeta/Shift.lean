/-
# The full `p`-shift and its periodic points

The p-adic integer tree, modelled symbolically.  A point is a digit string `x : ℕ → Fin p`; level `n`
is the residue class mod `p ^ n`, i.e. the first `n` digits; and the self-similarity map is the
one-sided full shift `σ x = fun n => x (n + 1)`, whose `p` inverse branches are the digit prepends.
Nothing here uses `ℤ_[p]` or any analysis: everything is exact combinatorial bookkeeping about
finite words.

The theorem this file exists for is `card_fixed_shift`:

```
Nat.card {x : ℕ → Fin p // (σ^[n]) x = x} = p ^ n      (for 0 < n)
```

`n`-periodic digit strings are exactly the points fixed by `σ ^ n`, and they are in bijection with
their first `n` digits.  This is the *only* input to the Artin–Mazur zeta of `σ`, which is therefore
`1 / (1 - p * T)`; see `Cascade/ZETA.md` for why that zeta can carry nothing but `p`.

## Scope, stated honestly

* **`card_fixed_shift` requires `0 < n`, and the hypothesis is not cosmetic.**  At `n = 0` the
  unrestricted statement is **false** for `p ≥ 2`: `σ ^ 0` is the identity, so *every* digit string
  is fixed, there are infinitely many of them, `Nat.card` of an infinite type is `0`, and `p ^ 0 = 1`.
  An earlier draft of this file asserted the unrestricted version by routing through
  `Nat.card_eq_fintype_card`, which silently produced an axiom-carrying "proof" of a false
  statement — caught by the `#print axioms` audit at the end of this file, not by the absence of an
  error message.  The audit is the load-bearing check, not the build.
* The count is stated with `Nat.card`, not `Fintype.card`, because `ℕ → Fin p` is infinite and the
  fixed-point subtype has no global `Fintype` instance.
* This file proves the **count** of periodic points.  It does **not** prove that the Artin–Mazur
  zeta of `σ` equals `1 / (1 - p * T)`: that identity needs the formal power series `exp` and `log`
  and is deliberately out of scope.  It is asserted, with its label, in `Cascade/ZETA.md`.
* The odometer results are the companion fact that makes the Artin–Mazur invariant *coarse* rather
  than ill-defined: a map with no periodic points at all has zeta `≡ 1`, so the invariant cannot
  distinguish it from any other aperiodic map.
-/

import Mathlib

open scoped BigOperators

namespace PAdicZeta

/-- The one-sided full `p`-shift on digit strings: drop the first digit. -/
def shift (p : ℕ) (x : ℕ → Fin p) : ℕ → Fin p := fun n => x (n + 1)

@[simp]
theorem shift_apply {p : ℕ} (x : ℕ → Fin p) (n : ℕ) : shift p x n = x (n + 1) := rfl

/-- The `n`-th iterate of the shift drops the first `n` digits. -/
theorem shift_pow_apply {p : ℕ} (x : ℕ → Fin p) (n k : ℕ) :
    ((shift p)^[n]) x k = x (k + n) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simp only [shift]
    rw [ih]
    congr 1
    omega

/-- Pointwise form of `shift_pow_apply`. -/
theorem shift_pow_apply' {p : ℕ} (x : ℕ → Fin p) (n : ℕ) :
    (shift p)^[n] x = fun k => x (k + n) := by
  funext k
  exact shift_pow_apply x n k

/-- A point is fixed by the `n`-th iterate of the shift exactly when it is `n`-periodic. -/
theorem fixed_iff_periodic {p : ℕ} (x : ℕ → Fin p) (n : ℕ) :
    ((shift p)^[n]) x = x ↔ ∀ k, x (k + n) = x k := by
  constructor
  · intro h k
    have hk := congrFun h k
    rwa [shift_pow_apply] at hk
  · intro h
    funext k
    rw [shift_pow_apply]
    exact h k

/-- **A fixed point of `σ ^ n` is constant on residue classes mod `n`.**  If `σ ^ n x = x` then
`x (k + n) = x k` for every `k`, and iterating gives `x (k % n + m * n) = x (k % n)`; since
`k = k % n + (k / n) * n`, the value at `k` is the value at `k % n`.  So a periodic point is
determined by its first `n` digits — the injectivity half of `card_fixed_shift`. -/
theorem self_eq_mod_of_fixed {p : ℕ} (x : ℕ → Fin p) (n : ℕ)
    (hx : (shift p)^[n] x = x) (k : ℕ) : x k = x (k % n) := by
  have hstep : ∀ j, x (j + n) = x j := (fixed_iff_periodic x n).mp hx
  have hsum : ∀ m, x (k % n + m * n) = x (k % n) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : k % n + (m + 1) * n = (k % n + m * n) + n := by ring
      rw [h1, hstep, ih]
  have hk : k = k % n + (k / n) * n := by
    conv_lhs => rw [← Nat.mod_add_div k n]
    rw [mul_comm]
  conv_lhs => rw [hk]
  exact hsum (k / n)

/-- The `n`-periodic extension of a block of `n` digits. -/
def periodicExt {p n : ℕ} (hn : 0 < n) (g : Fin n → Fin p) : ℕ → Fin p :=
  fun k => g ⟨k % n, Nat.mod_lt k hn⟩

/-- **Every block of `n` digits extends to a point fixed by `σ ^ n`** — the surjectivity half. -/
theorem periodicExt_fixed {p n : ℕ} (hn : 0 < n) (g : Fin n → Fin p) :
    ((shift p)^[n]) (periodicExt hn g) = periodicExt hn g := by
  funext k
  rw [shift_pow_apply]
  simp only [periodicExt]
  congr 1
  exact Fin.ext (Nat.add_mod_right k n)

/-- **The periodic points of `σ ^ n` are the `n`-digit blocks**: restricting to the first `n` digits
is a bijection onto `Fin n → Fin p`, with inverse the periodic extension. -/
def fixEquiv (p n : ℕ) (hn : 0 < n) :
    {x : ℕ → Fin p // ((shift p)^[n]) x = x} ≃ (Fin n → Fin p) where
  toFun x := fun k => x.1 k
  invFun g := ⟨periodicExt hn g, periodicExt_fixed hn g⟩
  left_inv x := by
    apply Subtype.ext
    funext k
    simp only [periodicExt]
    exact (self_eq_mod_of_fixed x.1 n x.2 k).symm
  right_inv g := by
    funext k
    simp only [periodicExt]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt k.2)

/-- **`σ ^ n` has exactly `p ^ n` fixed points** (for `0 < n`).

Stated with `Nat.card` because `ℕ → Fin p` is infinite, and with `0 < n` because the statement is
false at `n = 0` for `p ≥ 2`; see the module docstring. -/
theorem card_fixed_shift (p n : ℕ) (hn : 0 < n) :
    Nat.card {x : ℕ → Fin p // ((shift p)^[n]) x = x} = p ^ n := by
  rw [Nat.card_congr (fixEquiv p n hn), Nat.card_eq_fintype_card, Fintype.card_fun]
  simp

/-- The same count, in the shape of the zeta computation: the number of points of period dividing
`n` is the cardinality of the level-`n` digit blocks. -/
theorem card_fixed_shift_eq (p n : ℕ) (hn : 0 < n) :
    Nat.card {x : ℕ → Fin p // ((shift p)^[n]) x = x} = Nat.card (Fin n → Fin p) :=
  Nat.card_congr (fixEquiv p n hn)

/-! ## The odometer, and why the Artin–Mazur invariant is coarse -/

/-- The adding-machine map `x ↦ x + 1`. -/
def odometer (x : ℤ) : ℤ := x + 1

/-- The `n`-th iterate of the odometer is translation by `n`. -/
theorem odometer_iterate (x : ℤ) (n : ℕ) : (odometer^[n]) x = x + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [odometer]
    push_cast
    ring

/-- **The odometer on `ℤ` has no periodic points.**  `(x + 1)^[n] x = x` forces `n = 0`, because
`ℤ` is torsion-free.  Consequently its Artin–Mazur zeta would be `exp 0 = 1`, carrying no data —
the correct witness that the Artin–Mazur invariant is *coarse*, not ill-defined.

The honest scope: this is stated on `ℤ`, not on the profinite integers `ℤ_p`, whose API would be a
heavier development.  `ℤ` is torsion-free, which is exactly the property that makes the argument
work, and it sits inside `ℤ_p`; but the statement proved here is the one about `ℤ`. -/
theorem odometer_no_periodic (x : ℤ) (n : ℕ) : (odometer^[n]) x = x ↔ n = 0 := by
  rw [odometer_iterate]
  constructor
  · intro h
    have hn : (n : ℤ) = 0 := by linarith
    exact_mod_cast hn
  · intro h
    subst h
    simp

/-- **The odometer has no fixed points at any finite level.**  For `m ≠ 1`, the adding-machine map
`x ↦ x + 1` on `ZMod m` fixes nothing: `x + 1 = x` would force `1 = 0` in `ZMod m`. -/
theorem odometer_add_one_no_fixed {m : ℕ} (hm : m ≠ 1) (x : ZMod m) : x + 1 ≠ x := by
  intro h
  have h1 : (1 : ZMod m) = 0 := by
    have h' : x + 1 + -x = x + -x := by rw [h]
    simpa [add_assoc] using h'
  have hc : ((1 : ℕ) : ZMod m) = 0 := by simpa using h1
  exact hm (Nat.dvd_one.mp ((CharP.cast_eq_zero_iff (ZMod m) m 1).mp hc))

/-- **The finite-level statement, for every level `m ≠ 1`.**  The hypothesis cannot be dropped: at
`m = 1` the ring `ZMod 1` is trivial, so `1 = 0` and *every* `x` satisfies `x + 1 = x`.  In the
intended application `m = p ^ n` with `p ≥ 2`, so every level is at least `2`.

This is the level-`n` shadow of "the Artin–Mazur zeta of the odometer on `ℤ_p` is `1`"; the inverse
limit statement itself is not formalised here (see the module docstring). -/
theorem card_fixed_odometer_zmod (m : ℕ) (hm : m ≠ 1) :
    Nat.card {x : ZMod m // x + 1 = x} = 0 := by
  haveI : IsEmpty {x : ZMod m // x + 1 = x} :=
    ⟨fun x => odometer_add_one_no_fixed hm x.1 x.2⟩
  exact Nat.card_eq_zero.mpr (Or.inl ‹IsEmpty {x : ZMod m // x + 1 = x}›)

/-- The degenerate level excluded above, recorded so that the hypothesis is visibly necessary rather
than an artefact: in the trivial ring `ZMod 1` the adding-machine map fixes the unique element. -/
theorem card_fixed_odometer_one : Nat.card {x : ZMod 1 // x + 1 = x} = 1 := by
  haveI : Subsingleton {x : ZMod 1 // x + 1 = x} :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim a.1 b.1)⟩
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_ofSubsingleton _

end PAdicZeta

#print axioms PAdicZeta.shift_pow_apply
#print axioms PAdicZeta.fixed_iff_periodic
#print axioms PAdicZeta.self_eq_mod_of_fixed
#print axioms PAdicZeta.periodicExt_fixed
#print axioms PAdicZeta.fixEquiv
#print axioms PAdicZeta.card_fixed_shift
#print axioms PAdicZeta.card_fixed_shift_eq
#print axioms PAdicZeta.odometer_iterate
#print axioms PAdicZeta.odometer_no_periodic
#print axioms PAdicZeta.odometer_add_one_no_fixed
#print axioms PAdicZeta.card_fixed_odometer_zmod
#print axioms PAdicZeta.card_fixed_odometer_one
