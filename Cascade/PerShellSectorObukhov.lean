import Cascade.PerShellThreshold

/-!
# The Obukhov sector admits no per-shell bar of the Katz–Pavlović kind

`Cascade/PerShellThreshold.lean` derives an **exact per-shell threshold** for the
**Katz–Pavlović** sector of the dyadic transfer, `boussinesqTransferU 1 0`:

`u_{j+1} > perShellBar ν e j`, with `perShellBar ν e j = (ν/6)·2^{(e−1)j}`.

This file asks the same question for the other named sector, `boussinesqTransferU 0 1` — the
**Obukhov** model, which is the model of Palasek (arXiv:2407.06179, eq. (1.2)) and, by talks only
(no public preprint), of Looi's global-regularity work.

**The precise answer: there is no bar that is a function of `(ν, e, j)` alone** — the Katz–Pavlović
kind. What the Obukhov sector has *instead* is a threshold **whose height moves with the state**: for
`u_j > 0`, shell `j` transfers iff

`|u_{j+1}| > √( (ν/6)·2^{(e−1)j}·u_j )`,

a *state-dependent* threshold rather than a fixed bar. So the claim is **"no `(ν,e,j)`-only bar"**,
**not** "no threshold at all": a reader who objects that a threshold depending on `u_j` is still a
threshold is right, and this file does not deny it.

The obstruction is visible in the pointwise identity. In the Katz–Pavlović sector

`4^k u_k T_k = 3·a_{k−1}²·a_k + enstrophyFlux u k − enstrophyFlux u (k+1)`

the cubic carries `a_k` **linearly**, so after factoring `a_k²` out of each summed term the
remaining bracket is linear in `u_{k+1}` — that is what a per-shell *bar* is. In the Obukhov
sector the same computation gives

`4^k u_k T_k = (3/2)·a_{k−1}·a_k² + obukhovEnstrophyFlux u k − obukhovEnstrophyFlux u (k+1)`,

which carries `a_{k−1}` **linearly** and `a_k` **quadratically**. Factoring the summed term then
leaves `u_j` outside the bracket, so the sign of shell `j`'s contribution flips with `sign (u_j)`
and is **not a function of `(ν, e, j)` and `u_{j+1}` alone**. `no_obukhov_perShellBar` makes that
precise.

## An admissibility caveat, stated because it limits the claim

The witness of `obukhovShellTerm_sign_flip` uses `u_j = −1 < 0`, i.e. a **signed** ladder — which the
model admits (`u : ℤ → ℝ`) but which Palasek's own constructed solutions are not: he notes his
`solutions u, v are non-negative` (arXiv:2407.06179, Remark 1.4). **On the non-negative cone the
same conclusion holds, but for a different reason**: the criterion `|u_{j+1}| > √((ν/6)·2^{(e−1)j}u_j)`
is still state-dependent, so it is still not a fixed bar — the negative survives as *"the bar is
state-dependent"*, not as *"there is no threshold"*. Nothing here should be read as excluding a
state-dependent per-shell threshold.

## What survives the change of sector

The `e = 1` criticality. The factor is `2^{(e−1)j}` in both sectors, so its independence of `j` is
governed by `e = 1` either way. **The bar is sector-specific; the criticality is not.**

## Relation to the literature

The repository *defines* both sectors (`Cascade/Boussinesq.lean:71`), labels `A = 1, B = 0` as
Katz–Pavlović and `A = 0, B = 1` as Obukhov (`Cascade/PROGRESS.md`, the intermittency section), and derives every
existing per-shell result in the former. Palasek's `B_k` is the latter. See
`CASCADE_PALASEK_PRIOR_ART.md`, Q1(b).

## Contents

1. `obukhovEnstrophyFlux` — the Obukhov flux `(1/4)·8^k·u_{k-1}·u_k²`.
2. `transfer_enstrophy_pointwise_obukhov` — the pointwise identity.
3. `sum_transfer_enstrophy_obukhov` — its telescoped sum.
4. `sum_vorticity_cubic_obukhov` — the cubic `Σ a_{k−1}a_k²` in `u`-coordinates.
5. `enstrophy_pairing_degreeE_obukhov`, `enstrophy_pairing_obukhov` — the budget.
6. `obukhovShellTerm` — the shell summand.
7. `obukhovShellTerm_sign_flip`, `no_obukhov_perShellBar` — the negative.
-/

noncomputable section

namespace Cascade

open scoped BigOperators

/-! ## 1. The Obukhov enstrophy flux -/

/-- The Obukhov-sector enstrophy flux through the shell boundary `k`: `(1/4)·8^k·u_{k-1}·u_k²`.

This is the Katz–Pavlović flux `enstrophyFlux u k = (1/4)·8^k·u_{k-1}²·u_k` with the square moved
from `u_{k-1}` onto `u_k` — the sector change, concentrated in the flux. -/
def obukhovEnstrophyFlux (u : ℤ → ℝ) (k : ℤ) : ℝ :=
  (1 / 4) * dyadicWeight (3 * k) * u (k - 1) * (u k) ^ 2

/-- **Pointwise enstrophy transfer identity, Obukhov sector.** The weighted pairing of the Obukhov
nonlinearity at shell `k` is `(3/2)·a_{k-1}·a_k²` plus the difference of the Obukhov enstrophy flux
across the shell. -/
theorem transfer_enstrophy_pointwise_obukhov (u : ℤ → ℝ) (k : ℤ) :
    dyadicWeight (2 * k) * u k * boussinesqTransferU 0 1 u k
      = (3 / 2) * vorticity u (k - 1) * (vorticity u k) ^ 2
        + obukhovEnstrophyFlux u k - obukhovEnstrophyFlux u (k + 1) := by
  simp only [boussinesqTransferU, zero_mul, one_mul, zero_add, vorticity,
    obukhovEnstrophyFlux]
  rw [dyadicWeight_three_mul_succ, dyadicWeight_two_mul, dyadicWeight_three_mul,
    show k - 1 = k + (-1) by ring, dyadicWeight_add, dyadicWeight_neg_one]
  ring_nf

/-- **Summed transfer identity, Obukhov sector.** Summing the pointwise identity over the retained
shells and telescoping, the boundary fluxes vanish by the Dirichlet conditions `u(-1) = u(N) = 0`,
leaving the cubic transfer sum `(3/2) ∑ a_{k-1} a_k²`. -/
theorem sum_transfer_enstrophy_obukhov (u : ℤ → ℝ) (N : ℕ)
    (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0) :
    (∑ k ∈ Finset.range N,
        dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * boussinesqTransferU 0 1 u (k : ℤ))
      = (3 / 2) * (∑ k ∈ Finset.range N,
          vorticity u ((k : ℤ) - 1) * (vorticity u (k : ℤ)) ^ 2) := by
  have hpt : ∀ k ∈ Finset.range N,
      dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * boussinesqTransferU 0 1 u (k : ℤ)
        = (3 / 2) * (vorticity u ((k : ℤ) - 1) * (vorticity u (k : ℤ)) ^ 2)
          + ((fun m : ℕ => obukhovEnstrophyFlux u (m : ℤ)) k
              - (fun m : ℕ => obukhovEnstrophyFlux u (m : ℤ)) (k + 1)) := by
    intro k _
    rw [transfer_enstrophy_pointwise_obukhov]
    push_cast
    ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_range_sub', ← Finset.mul_sum]
  have h0 : obukhovEnstrophyFlux u (((0 : ℕ) : ℤ)) = 0 := by
    unfold obukhovEnstrophyFlux
    rw [show (((0 : ℕ) : ℤ)) - 1 = -1 by norm_num, huBot]
    ring
  have hN : obukhovEnstrophyFlux u (N : ℤ) = 0 := by
    unfold obukhovEnstrophyFlux
    rw [huTop]
    ring
  rw [h0, hN]
  ring

/-- **The Obukhov cubic in `u`-coordinates.** `∑_{k<N} a_{k-1} a_k² = 4 ∑_{j<N-1} 8^j u_j u_{j+1}²`,
the Dirichlet end at `j = -1` being dropped. Compare the Katz–Pavlović counterpart
`∑ a_{k-1}² a_k = 2 ∑ 8^j u_j² u_{j+1}` — the same statement with the two factors exchanged. -/
theorem sum_vorticity_cubic_obukhov (u : ℤ → ℝ) (N : ℕ) (huBot : u (-1) = 0) :
    (∑ k ∈ Finset.range N, vorticity u ((k : ℤ) - 1) * (vorticity u (k : ℤ)) ^ 2)
      = 4 * (∑ j ∈ Finset.range (N - 1),
          dyadicWeight (3 * (j : ℤ)) * u (j : ℤ) * (u ((j : ℤ) + 1)) ^ 2) := by
  cases N with
  | zero => simp
  | succ M =>
    rw [Finset.sum_range_succ']
    have hf0 : vorticity u (((0 : ℕ) : ℤ) - 1) * (vorticity u ((0 : ℕ) : ℤ)) ^ 2 = 0 := by
      have h0 : (((0 : ℕ) : ℤ) - 1) = -1 := by norm_num
      rw [h0, vorticity_neg_one u huBot]
      ring
    have hstep : ∀ k : ℕ,
        vorticity u (((k + 1 : ℕ) : ℤ) - 1) * (vorticity u ((k + 1 : ℕ) : ℤ)) ^ 2
          = 4 * (dyadicWeight (3 * (k : ℤ)) * u (k : ℤ) * (u ((k : ℤ) + 1)) ^ 2) := by
      intro k
      have hk1 : (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) := by push_cast; ring
      have hk2 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [hk1, hk2]
      simp only [vorticity]
      have hd1 : dyadicWeight ((k : ℤ) + 1) = dyadicWeight (k : ℤ) * 2 := by
        rw [show (k : ℤ) + 1 = (k : ℤ) + 1 by rfl, dyadicWeight_add]
        norm_num [dyadicWeight]
      rw [hd1, dyadicWeight_three_mul]
      ring
    rw [hf0, add_zero, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => hstep k)

/-! ## 2. The Obukhov enstrophy budget -/

/-- **The exact enstrophy pairing at degree `e`, Obukhov sector.** Weighting the degree-`e` Obukhov
velocity equation by `4^k u_k` and summing over the Dirichlet-truncated range,

`Σ 4^k u_k (du_k/dt) = (3/2) Σ a_{k-1} a_k² + κ Σ 4^k u_k θ_k − ν D_e`. -/
theorem enstrophy_pairing_degreeE_obukhov (ν κ : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (N : ℕ)
    (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0) :
    (∑ k ∈ Finset.range N,
        dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * velocityRHSDegreeE ν κ 0 1 e u θ (k : ℤ))
      = (3 / 2) * (∑ k ∈ Finset.range N,
          vorticity u ((k : ℤ) - 1) * (vorticity u (k : ℤ)) ^ 2)
        + κ * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ))
        - ν * enstrophyDissipation e u N := by
  have hsplit : ∀ k ∈ Finset.range N,
      dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * velocityRHSDegreeE ν κ 0 1 e u θ (k : ℤ)
        = dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * boussinesqTransferU 0 1 u (k : ℤ)
          + κ * (dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ))
          - ν * (dyadicWeight ((2 + e) * (k : ℤ)) * (u (k : ℤ)) ^ 2) := by
    intro k _
    have h4 : dyadicWeight ((2 + e) * (k : ℤ))
        = dyadicWeight (2 * (k : ℤ)) * dyadicWeight (e * (k : ℤ)) := by
      rw [← dyadicWeight_add]
      congr 1
      ring
    simp only [velocityRHSDegreeE]
    rw [h4]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hκ : (∑ k ∈ Finset.range N,
        κ * (dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ)))
      = κ * (∑ k ∈ Finset.range N,
          dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ)) := by
    rw [Finset.mul_sum]
  have hν : (∑ k ∈ Finset.range N,
        ν * (dyadicWeight ((2 + e) * (k : ℤ)) * (u (k : ℤ)) ^ 2))
      = ν * enstrophyDissipation e u N := by
    rw [enstrophyDissipation, Finset.mul_sum]
  rw [hκ, hν, sum_transfer_enstrophy_obukhov u N huBot huTop]

/-- **The outer-factor-`2` Obukhov budget.** Doubling the pairing identity and converting the cubic
with `sum_vorticity_cubic_obukhov`:

`2 Σ_{k<N} 4^k u_k (du_k/dt) = 12 Σ_{j<N-1} 8^j u_j u_{j+1}² + 2κ Σ 4^k u_k θ_k − 2ν D_e`.

This is the exact Obukhov counterpart of `enstrophy_pairing_degree`
(`Cascade/PerShellThreshold.lean`), whose cubic is `12 Σ_{j<N-1} 8^j u_j² u_{j+1}`. **The two
budgets differ only in where the square sits** — that is the whole content of this file.

*To be exact, since this is easy to misread.* Telescoping gives `8 − 2 = 6` in both sectors, doubled
to `12` by the outer factor, so the **constant is the same**. The two shell summands are

```
Katz–Pavlović:   8^j · u_j² · ( 12 u_{j+1}      − 2ν·2^{(e−1)j} )
Obukhov:         8^j · u_j  · ( 12 u_{j+1}²     − 2ν·2^{(e−1)j}·u_j )
```

and **the dissipation pieces coincide identically**, because `u_j² · 2ν·2^{(e−1)j}` and
`u_j · 2ν·2^{(e−1)j} · u_j` are the same expression written two ways. The *only* difference is the
transfer piece — `u_j²u_{j+1}` against `u_ju_{j+1}²` — i.e. the square's position, and with it which
factor sits outside the bracket and hence whose sign the shell term tracks. -/
theorem enstrophy_pairing_obukhov (ν κ : ℝ) (e : ℤ) (u θ : ℤ → ℝ) (N : ℕ)
    (huBot : u (-1) = 0) (huTop : u (N : ℤ) = 0) :
    2 * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ)
          * velocityRHSDegreeE ν κ 0 1 e u θ (k : ℤ))
      = 12 * (∑ j ∈ Finset.range (N - 1),
          dyadicWeight (3 * (j : ℤ)) * u (j : ℤ) * (u ((j : ℤ) + 1)) ^ 2)
        + 2 * κ * (∑ k ∈ Finset.range N, dyadicWeight (2 * (k : ℤ)) * u (k : ℤ) * θ (k : ℤ))
        - 2 * ν * (∑ k ∈ Finset.range N,
            dyadicWeight ((2 + e) * (k : ℤ)) * (u (k : ℤ)) ^ 2) := by
  rw [enstrophy_pairing_degreeE_obukhov ν κ e u θ N huBot huTop]
  rw [sum_vorticity_cubic_obukhov u N huBot]
  rw [enstrophyDissipation]
  ring

/-! ## 3. The shell summand, and the negative -/

/-- The shell-`j` summand of the Obukhov enstrophy budget:
`8^j · u_j · (12 u_{j+1}² − 2ν·2^{(e−1)j}·u_j)`.

Compare the Katz–Pavlović summand `8^j · u_j² · (12 u_{j+1} − 2ν·2^{(e−1)j})` of
`Cascade/PerShellThreshold.lean`: there the `u_j` factor is **squared**, so it can be cancelled
from the criterion; here it is **linear**, so it cannot. -/
def obukhovShellTerm (ν : ℝ) (e : ℤ) (j : ℕ) (u : ℤ → ℝ) : ℝ :=
  dyadicWeight (3 * (j : ℤ)) * u (j : ℤ)
    * (12 * (u ((j : ℤ) + 1)) ^ 2 - 2 * ν * dyadicWeight ((e - 1) * (j : ℤ)) * u (j : ℤ))

/-- **The Obukhov shell sign is not decided by `u_{j+1}`.** Two states with the *same* `u_{j+1}`
whose shell-`j` summands have opposite signs: flip `sign (u_j)` and the summand flips with it, since
`u_j` sits outside the bracket. This is the mechanism that kills every per-shell bar. -/
theorem obukhovShellTerm_sign_flip (j : ℕ) :
    ∃ u v : ℤ → ℝ, u ((j : ℤ) + 1) = v ((j : ℤ) + 1)
      ∧ 0 < obukhovShellTerm 1 1 j u ∧ obukhovShellTerm 1 1 j v < 0 := by
  refine ⟨fun k => if k = (j : ℤ) then 1 else if k = (j : ℤ) + 1 then 1 else 0,
          fun k => if k = (j : ℤ) then -1 else if k = (j : ℤ) + 1 then 1 else 0,
          ?_, ?_, ?_⟩
  · simp
  · simp only [obukhovShellTerm, dyadicWeight]
    norm_num
    positivity
  · simp only [obukhovShellTerm, dyadicWeight]
    norm_num
    positivity

/-- **There is no per-shell bar in the Obukhov sector.** No function of `(ν, e, j)` alone decides
the sign of shell `j`'s contribution to the enstrophy budget, in contrast with the Katz–Pavlović
sector, where `perShellBar` does exactly that (`perShell_iff`). -/
theorem no_obukhov_perShellBar :
    ¬ ∃ bar : ℝ → ℤ → ℕ → ℝ, ∀ (ν : ℝ) (e : ℤ) (j : ℕ) (u : ℤ → ℝ),
      (0 < obukhovShellTerm ν e j u ↔ bar ν e j < u ((j : ℤ) + 1)) := by
  rintro ⟨bar, hbar⟩
  obtain ⟨u, v, huv, hu, hv⟩ := obukhovShellTerm_sign_flip 0
  have h1 : bar 1 1 0 < u (((0 : ℕ) : ℤ) + 1) := (hbar 1 1 0 u).mp hu
  have h2 : ¬ (bar 1 1 0 < v (((0 : ℕ) : ℤ) + 1)) := by
    intro h
    exact absurd ((hbar 1 1 0 v).mpr h) (not_lt.mpr hv.le)
  rw [huv] at h1
  exact h2 h1

end Cascade

#print axioms Cascade.obukhovEnstrophyFlux
#print axioms Cascade.transfer_enstrophy_pointwise_obukhov
#print axioms Cascade.sum_transfer_enstrophy_obukhov
#print axioms Cascade.sum_vorticity_cubic_obukhov
#print axioms Cascade.enstrophy_pairing_degreeE_obukhov
#print axioms Cascade.enstrophy_pairing_obukhov
#print axioms Cascade.obukhovShellTerm
#print axioms Cascade.obukhovShellTerm_sign_flip
#print axioms Cascade.no_obukhov_perShellBar
