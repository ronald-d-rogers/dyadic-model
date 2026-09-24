import Cascade.PerShellSectorObukhov

/-!
# The two sectors' stationary ratio recursions are exact inverses

`Cascade/ZETA.md` §6.3 records that the stationary power law is a **repeller** of the ratio recursion
`s_{n+1} = 1/(b·2^α·s_n²)`, with multiplier exactly `−2`. That recursion is the **Katz–Pavlović**
sector, `A = 1, B = 0`, whose vanishing-interior-transfer condition is `u_{k−1}² = 2 u_k u_{k+1}`.

This file does the same computation in the other named sector, `A = 0, B = 1` — **Obukhov**, the model
of Palasek (arXiv:2407.06179), and (by talks only, no public preprint) of Looi's global-regularity
work — whose vanishing-interior-transfer condition is `u_k u_{k−1} = 2 u_{k+1}²`.

## Result, and the single fact behind it

| sector | recursion | fixed point | multiplier |
|---|---|---|---|
| Katz–Pavlović | `s_{n+1} = K / s_n²` | `s³ = K` | `−2` |
| Obukhov | `s_{n+1} = √(K / s_n)` | `s³ = K` | `−1/2` |

**The two maps are exact inverses** (`ratioStepA_comp_ratioStepB`, `ratioStepB_comp_ratioStepA`). That
one fact explains both rows: a map and its inverse share fixed points, so the stationary ratio is the
same; and their derivatives are reciprocals, so `−1/2 = 1/(−2)`. The multiplier is the exponent of the
recursion, and for a power-law recursion the exponent is independent of `K` — which is why the `−2` of
`ZETA.md` does not see `b` or `α`.

## What this does NOT say

**It does not say the Obukhov sector has non-unique stationary profiles.** The Obukhov fixed point is
attracting and the Katz–Pavlović one is repelling *for the forward iteration*, so forward the Obukhov
recursion converges from every positive start while the Katz–Pavlović one survives only at `s*`. But
the model's index is `ℤ`, and two-sidedness removes the asymmetry: **the backward map of the Obukhov
recursion is the Katz–Pavlović forward map**, since they are inverses. That map is a repeller, so a
bounded two-sided ratio sequence must be exactly `s*` in *either* sector. **Rigidity is shared.**
Checked numerically: forward from any `s₀ > 0` converges, backward diverges unless `s₀ = s*`; only
`s*` survives both directions. An earlier draft of this file claimed a one-parameter family of
stationary profiles in the Obukhov sector — that was an artifact of indexing one-sidedly, and it is
**false** for the model as indexed.

**It is not a statement about a viscous model.** Everything here is the *inviscid*
vanishing-transfer condition, exactly as `ZETA.md` §6.3 is. For `ν > 0` the stationary condition is
`transfer = ν·2^{ek}·u_k` (`Cascade/DissipationThreshold.lean:77`), which no vanishing-transfer
profile satisfies, so the recursion below is not the stationarity condition at all in that case.
**Nothing here should be read as a claim about the viscous Obukhov model or about Looi's theorem.**

**`sector_stability_dichotomy` is arithmetic, not dynamics.** It proves `1 < |−2|` and `|−1/2| < 1`
and contains no theorem about solutions. "Repeller"/"attractor" below are properties of the one-sided
*ratio recursion* only.

## On Barbato's uniqueness

`ZETA.md` §6.3 says the `−2` "is *why* Barbato's uniqueness theorem holds". That inference is **not
proved here and is not claimed here**: it links a `ν = 0` recursion to a forced stationary-solution
theorem, and whether that theorem is a `ν = 0`, a `ν > 0`, or a mixed statement was not determined.

## Why there is no calculus here

The multiplier is computed **algebraically**, as the exact ratio of successive errors rather than as a
derivative. For `f(s) = K/s²` and `s*` the fixed point (`s*³ = K`),

`(f s − s*) / (s − s*) = −K·(s + s*) / (s²·s*²)`   for every `s ≠ s*`,

and evaluating at `s = s*` gives `−2`. For `f(s) = √(K/s)` the rationalisation gives
`−K / (s·s*·(√(K/s) + s*))`, which at `s = s*` is `−1/2`. Both are exact identities.

**Both identities need the fixed-point condition**, and that is not a formality: `f s − s*` only
factorises as `(s − s*)·(something)` once `s*` is pinned to `K`. An earlier hand derivation of the
A-sector identity claimed it held for *every* `s*`; that is false — the residual goal is exactly
`s*³ = K` — and the elaboration caught it. Both statements carry `s*³ = K` explicitly.

## Labels

The two recursions are `[derived]` from the sectors' conditions — one line of algebra each, displayed
in the docstrings of `ratioStepA_fixed` / `ratioStepB_fixed` — but **they are not formalized at the
level of `u`**: this file formalizes the abstract maps only, and the `u`-level derivation carries
silent positivity hypotheses (the A-case needs `u_k ≠ 0`; the B-case needs `u_k > 0` and the principal
root). The multipliers and the inverse identities are `[proved]`.
-/

noncomputable section

namespace Cascade

/-! ## 1. The Katz–Pavlović recursion `s_{n+1} = K / s_n²` -/

/-- **A-sector fixed point.** If `s³ = K` and `s ≠ 0`, then `s` is fixed by `s ↦ K/s²`. -/
theorem ratioStepA_fixed (K s : ℝ) (hs : s ≠ 0) (h3 : s ^ 3 = K) : K / s ^ 2 = s := by
  rw [← h3, div_eq_iff (pow_ne_zero 2 hs)]
  ring

/-- **A-sector error ratio, exactly.** At the fixed point `s*³ = K`, and for every `s ≠ s*` with
`s, s* ≠ 0`, the ratio of successive errors is the displayed rational function; it is the exact (not
linearised) object whose value at `s = s*` is the multiplier. The fixed-point hypothesis is needed:
without it the residual goal is exactly `s*³ = K`. -/
theorem ratioStepA_error_ratio (K s sstar : ℝ) (hs : s ≠ 0) (hsstar : sstar ≠ 0)
    (h3 : sstar ^ 3 = K) (hne : s ≠ sstar) :
    (K / s ^ 2 - sstar) / (s - sstar) = -K * (s + sstar) / (s ^ 2 * sstar ^ 2) := by
  have hsub : s - sstar ≠ 0 := sub_ne_zero.mpr hne
  field_simp
  rw [← h3]
  ring

/-- **The Katz–Pavlović multiplier is `−2`.** At the fixed point `s³ = K` the A-sector error ratio
equals `−2`, whatever `K` is — no `b`, no `α`, no `ν`. -/
theorem ratioStepA_multiplier (K s : ℝ) (hs : s ≠ 0) (h3 : s ^ 3 = K) :
    -K * (s + s) / (s ^ 2 * s ^ 2) = -2 := by
  rw [← h3]
  field_simp
  ring

/-! ## 2. The Obukhov recursion `s_{n+1} = √(K / s_n)` -/

/-- **B-sector fixed point.** If `s³ = K` and `s > 0`, then `s` is fixed by `s ↦ √(K/s)`. Note the
fixed point is the *same* one as in the A-sector. -/
theorem ratioStepB_fixed (K s : ℝ) (hs : 0 < s) (h3 : s ^ 3 = K) : Real.sqrt (K / s) = s := by
  have hsne : s ≠ 0 := hs.ne'
  have h : K / s = s ^ 2 := by
    rw [← h3]
    field_simp
  rw [h, Real.sqrt_sq hs.le]

/-- **B-sector error ratio, exactly.** The rationalisation of `√(K/s) − s*` against `s − s*`, using
the fixed-point condition `s*³ = K`. -/
theorem ratioStepB_error_ratio (K s sstar : ℝ) (hs : 0 < s) (hss : 0 < sstar)
    (h3 : sstar ^ 3 = K) (hne : s ≠ sstar) :
    (Real.sqrt (K / s) - sstar) / (s - sstar)
      = -K / (s * sstar * (Real.sqrt (K / s) + sstar)) := by
  have hK : 0 < K := by rw [← h3]; positivity
  have ht2 : (Real.sqrt (K / s)) ^ 2 = K / s := Real.sq_sqrt (div_pos hK hs).le
  have ht : 0 < Real.sqrt (K / s) := Real.sqrt_pos_of_pos (div_pos hK hs)
  have hts : Real.sqrt (K / s) + sstar ≠ 0 := by positivity
  have hden : s * sstar * (Real.sqrt (K / s) + sstar) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hs.ne' hss.ne') hts
  have hsub : s - sstar ≠ 0 := sub_ne_zero.mpr hne
  have key : (Real.sqrt (K / s) - sstar) * (s * sstar * (Real.sqrt (K / s) + sstar))
      = -K * (s - sstar) := by
    have h1 : (Real.sqrt (K / s) - sstar) * (Real.sqrt (K / s) + sstar)
        = (Real.sqrt (K / s)) ^ 2 - sstar ^ 2 := by ring
    rw [show (Real.sqrt (K / s) - sstar) * (s * sstar * (Real.sqrt (K / s) + sstar))
          = ((Real.sqrt (K / s) - sstar) * (Real.sqrt (K / s) + sstar)) * (s * sstar) by ring,
      h1, ht2, ← h3]
    field_simp
    ring
  rw [div_eq_div_iff hsub hden]
  linarith [key]

/-- **The Obukhov multiplier is `−1/2`.** At the fixed point `s³ = K` the B-sector error ratio equals
`−1/2`, whatever `K` is. Its modulus is below one: an **attractor**, where the A-sector's is a
repeller. -/
theorem ratioStepB_multiplier (K s : ℝ) (hs : 0 < s) (h3 : s ^ 3 = K) :
    -K / (s * s * (Real.sqrt (K / s) + s)) = -1 / 2 := by
  rw [ratioStepB_fixed K s hs h3, ← h3]
  field_simp
  ring

/-! ## 3. The dichotomy -/

/-- **Both sectors pin the same stationary ratio.** If `s > 0` and `s³ = K` then `s` is the fixed
point of *both* recursions. This is not a coincidence: the two maps are inverses, and a map and its
inverse share fixed points (`fixed_point_shared_of_inverse`). -/
theorem stationaryRatio_shared (K s : ℝ) (hs : 0 < s) (h3 : s ^ 3 = K) :
    K / s ^ 2 = s ∧ Real.sqrt (K / s) = s :=
  ⟨ratioStepA_fixed K s hs.ne' h3, ratioStepB_fixed K s hs h3⟩

/-! ### The inverses, and the rigidity they share -/

/-- **The Obukhov step followed by the Katz–Pavlović step is the identity** (`K > 0`, `s > 0`). The
two sectors' recursions are exact inverses of each other, not merely similar. -/
theorem ratioStepA_comp_ratioStepB (K s : ℝ) (hK : 0 < K) (hs : 0 < s) :
    K / (Real.sqrt (K / s)) ^ 2 = s := by
  rw [Real.sq_sqrt (div_pos hK hs).le]
  field_simp

/-- **The Katz–Pavlović step followed by the Obukhov step is the identity** — the other composite. -/
theorem ratioStepB_comp_ratioStepA (K s : ℝ) (hK : 0 < K) (hs : 0 < s) :
    Real.sqrt (K / (K / s ^ 2)) = s := by
  have h : K / (K / s ^ 2) = s ^ 2 := by
    field_simp
  rw [h, Real.sqrt_sq hs.le]

/-- **The shared fixed point is forced by the inverse relation.** If `s` is fixed by the Obukhov step
then it is fixed by the Katz–Pavlović step, because the latter is the former's inverse. This is the
whole reason the two sectors have the same stationary ratio. -/
theorem fixed_point_shared_of_inverse (K s : ℝ) (hK : 0 < K) (hs : 0 < s)
    (h : Real.sqrt (K / s) = s) : K / s ^ 2 = s := by
  have hcomp := ratioStepA_comp_ratioStepB K s hK hs
  rwa [h] at hcomp

/-- **The multipliers are reciprocals, as inverses must be.** `−1/2 = 1/(−2)`. The "stability flip"
is this identity and nothing more. -/
theorem multipliers_reciprocal : (-1 / 2 : ℝ) = 1 / (-2) := by norm_num

/-- **The multipliers exceed / fall below one in modulus.** This is arithmetic about the two numbers
that the error-ratio identities produce. It is **not** a stability theorem about any solution or any
dynamics, and on the model's two-sided `ℤ`-index the rigidity is *shared* rather than flipped (see
`ratioStepB_comp_ratioStepA`, which is the backward map). -/
theorem sector_stability_dichotomy : 1 < |(-2 : ℝ)| ∧ |(-1 / 2 : ℝ)| < 1 := by
  constructor <;> norm_num

/-- **The dichotomy at the model's own value `K = 1/2`** (which is what both sectors' static
conditions give in the single-species model): the stationary ratio is `(1/2)^{1/3}` in both, the
multipliers are `−2` and `−1/2`. -/
theorem sector_multipliers_at_half :
    (∀ s : ℝ, 0 < s → s ^ 3 = 1 / 2 →
        -((1 / 2 : ℝ)) * (s + s) / (s ^ 2 * s ^ 2) = -2)
      ∧ (∀ s : ℝ, 0 < s → s ^ 3 = 1 / 2 →
          -((1 / 2 : ℝ)) / (s * s * (Real.sqrt ((1 / 2) / s) + s)) = -1 / 2) :=
  ⟨fun s hs h3 => ratioStepA_multiplier (1 / 2) s hs.ne' h3,
   fun s hs h3 => ratioStepB_multiplier (1 / 2) s hs h3⟩

end Cascade

#print axioms Cascade.ratioStepA_fixed
#print axioms Cascade.ratioStepA_error_ratio
#print axioms Cascade.ratioStepA_multiplier
#print axioms Cascade.ratioStepB_fixed
#print axioms Cascade.ratioStepB_error_ratio
#print axioms Cascade.ratioStepB_multiplier
#print axioms Cascade.stationaryRatio_shared
#print axioms Cascade.ratioStepA_comp_ratioStepB
#print axioms Cascade.ratioStepB_comp_ratioStepA
#print axioms Cascade.fixed_point_shared_of_inverse
#print axioms Cascade.multipliers_reciprocal
#print axioms Cascade.sector_stability_dichotomy
#print axioms Cascade.sector_multipliers_at_half
