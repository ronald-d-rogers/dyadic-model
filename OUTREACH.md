# Outreach: the notes, their status, and what must not be sent

A record of the outbound notes drafted for the dyadic-cascade work, so that nothing depends on a
conversation. **Nothing in this file is a mathematical result**; the results are in `Cascade/` and
`CASCADE_PALASEK_PRIOR_ART.md`.

Public artifact, once the child is pushed: <https://github.com/ronald-d-rogers/dyadic-model>

---

## 1. Status

| recipient | contacted before? | what | status of the note below |
|---|---|---|---|
| **Terence Tao** | **yes** — one earlier email reporting "nothing with the basic dyad; it just leads to Cheskidov" | | **drafted, not sent** |
| **Stan Palasek** | no | | **drafted, not sent** |
| **Sam Looi** | no | | **drafted, not sent** |

The parent branch `holographic-branching` has no upstream and is on no remote, so this file and
`CASCADE_PALASEK_PRIOR_ART.md` are **not publicly reachable**. The child carries only the Lean
library, so recipients can read the mathematics but not the prior-art or this file.

### The correction owed to Tao

The earlier email said the tree cascade *"just leads to Cheskidov"*. That covers the **threshold**
(Cheskidov's `α` range) but **not the obstruction**. Palasek's `N^{3/2}`-versus-`N²` comparison is
his own, is written up nowhere, and is a *different object* from the `α`-threshold. The correction
belongs in the private email, not in a public post.

### The disclosure requirement

If Post 3 tells Tao the analysis was AI-generated, **the same disclosure must go to Palasek and
Looi.** A disclosure present in one of three notes is not a disclosure. One line, identical in all
three:

> Everything below — the analysis, the Lean development and the wording — was produced by an AI
> assistant at my direction. Treat it as machine-generated claims to be checked rather than as
> independent work; the repository documents its own retractions. Three of the structural
> observations are mine, not the assistant's — the loop closure, the isotropic reduction, and the
> scaling orbit — and in each case it had concluded otherwise or not asked. See `PROVENANCE.md`.

---

## 2. Note to Tao — Mastodon thread, replying to his post

His post: <https://mathstodon.xyz/@tao/117236063705269594> (the exercise), in Palasek's thread.

**Post 1.** Reply to his post. Keep `@tao@mathstodon.xyz`.

> @tao@mathstodon.xyz Ran the exercise for the one-mode-per-octave dyadic class. The answer is
> negative, and it's a modelling fact rather than a new theorem. Requiring the model to be
> scaling-covariant the way Boussinesq is pins the dissipation degree to the Laplacian value,
> already inside the known regular range. And the Bernstein factor the high-dimension route needs is
> implied by the definitions in this class, so it cannot be inserted. Write-up + Lean:
> https://github.com/ronald-d-rogers/dyadic-model

**Post 2.** Reply to **Post 1** (self-reply — that is how a Mastodon thread continues; a second reply
to his post makes a sibling, not a continuation). Keep `@tao` in the mention box.

> Two things I'd like checked. (1) The negative rests on 'scaling covariance + the standard viscosity
> law forces the degree to 2' — is there a dyadic class with the same scaling features where it is
> not forced? (2) Palasek's Bernstein N^{3/2}-versus-N^2 comparison and the intermittency bookkeeping
> (2+n-delta)/2 give the same threshold, but the exponents differ by one power of lambda: the
> gradient. Is that dictionary written down?

**Post 3.** Reply to Post 2. The disclosure, with the two observations that are his correspondent's
rather than the assistant's.

> One thing I should say plainly: the analysis above, the Lean development and the wording are all
> AI-generated, produced by an assistant at my direction. Treat them as machine-produced claims to be
> checked, not as my own work. The write-up documents its own retractions, and the whole thing is a
> negative result. The loop closure, the isotropic reduction and the scaling orbit are mine, not the
> assistant's, and in each case it had concluded otherwise or not asked.

**Email (same day, private).** Carries the correction above plus:

> One thing possibly more broadly useful. A Lean file that fails to elaborate can silently receive
> `sorryAx`, so **grepping for `sorry` does not detect an unproved theorem** — a false statement we
> had survived that check and was caught only by `#print axioms`. And the pattern of error is worth
> knowing: in every case here the machine-checked core was right and the *prose sentence built on
> it* was wrong. For anyone running AI-assisted formalization, the checks that bind are zero
> `: error:` lines (not `^error` — Lean prefixes errors with the file path), "Build completed
> successfully", and `#print axioms`.

---

## 3. Note to Palasek

**Subject:** The ℤ→ℕ closure in arXiv:2407.06179, and what I think is its exact version

> Stan,
>
> I've been working through dyadic models and want to run one thing past you.
>
> In arXiv:2407.06179 you note that *"an additive group structure on `I` is necessary to discuss
> exact scale invariance,"* that `I = ℕ` is closed by fixing `u_{−1} = 0`, and that the `ℤ → ℕ`
> transfer works *"not by stability … but rather because the different frequency shells are weakly
> coupled together, so the self-similarity can be interrupted at the low modes."*
>
> I reached the same three-way split from the other direction and wrote down what I believe is the
> exact version. Closing the chain by a self-similar identification **forces** `μ = 2^α` — not chosen
> — and what closes is a helix `X_{n+N} = μ^{−N}X_n`, not a circle. In the unrooted chain (`ℤ`) the
> closing edge is free; in the rooted model it must be supplied, and there are exactly two ways: a
> **clamp** (`u_{−1} = 0`, your case) or a **drive** tied to the state, `f = 2^{αN}X_{N−1}`. The two
> have opposite behaviour — the clamp regularizes; the drive is the scaling orbit.
>
> That makes me think your closure remark and Looi's forcing-necessary result are the same statement:
> a rooted model cannot be closed exactly without a drive, so any blow-up in it has to carry one.
> Viscously the dichotomy is sharp too: exact closure survives only at zero dissipation degree
> (`2^{eN} = 1 ⟺ e = 0`), so the physical `e = 2` is exactly where it fails.
>
> I read this as the exact counterpart of your weak-coupling truncation rather than a competing
> claim — yours is approximate, this is the exact case, so they should be consistent. If they
> aren't, I'd like to know where.
>
> Two questions: (1) is the exact statement written down anywhere? I couldn't find it. (2) You note
> the `I = ℤ` construction comes *"at the cost of yielding infinite energy solutions"* — is that the
> same obstruction as the clamp violation, or a separate price?
>
> *(Disclosure line as in §1.)*
>
> — Ronald

---

## 4. Note to Looi

**Subject:** Does the Obukhov sector's enstrophy pairing give a per-shell threshold?

> Sam,
>
> I saw the abstracts for your dyadic-model talks and want to ask whether two things are the same
> object.
>
> You describe *"a critical rescaling that shows a viscous activation threshold for each shell,"*
> with regularity from two competing scales — viscous damping and nonlinear growth — becoming
> incompatible at high frequencies.
>
> In the **Katz–Pavlović** sector of the same four-parameter family (`A = 1, B = 0`), the enstrophy
> pairing decides shell `j`'s sign through a single number — `u_{j+1} > (ν/6)·2^{(e−1)j}`, a
> function of `(ν,e,j)` alone. Machine-checked in `Cascade/PerShellThreshold.lean`.
>
> In the **Obukhov** sector (`A = 0, B = 1`), the shell-`j` summand of the same budget is
> `8^j · u_j · (12u_{j+1}² − 2ν·2^{(e−1)j}·u_j)`, and its sign is **not** a function of `(ν,e,j)` and
> `u_{j+1}` alone: any `(ν,e,j)`-only bar is refuted (`no_obukhov_perShellBar`), and two states with
> the same `u_{j+1}` give opposite signs (`obukhovShellTerm_sign_flip`).
>
> What that sector has instead is a **state-dependent** threshold: for `u_j > 0`, shell `j`
> transfers iff `|u_{j+1}| > √((ν/6)·2^{(e−1)j}·u_j)` — a genuine threshold, whose height moves with
> `u_j`. The `e = 1` marginality is shared, since the factor `2^{(e−1)j}` is in both.
>
> So: **if your activation threshold is a function of `(ν,e,j)` alone — a fixed number per shell —
> this pairing does not produce it. If it varies with the state, this does not exclude it, and I'm
> not claiming it does.**
>
> One limit I want to flag rather than bury: the two-state witness uses a **signed** ladder
> (`u_j = −1`), while Palasek notes his constructed solutions are non-negative (arXiv:2407.06179,
> Remark 1.4). On the non-negative cone the conclusion survives for a different reason — the height
> still moves — but it weakens to "the bar is state-dependent" rather than "there is no bar".
>
> *(Disclosure line as in §1.)*
>
> — Ronald

---

## 5. What must NOT be sent

| item | why |
|---|---|
| **the stationary multiplier flip** (`−2` repeller vs `−1/2` attractor) | true and now proved (`Cascade/StationarySectorMultiplier.lean`), but trivial: the two sectors' recursions are **exact inverses**, so the flip is a relabelling. And it is the **inviscid** condition, while the recipients' models are viscous. No consequence for anyone. |
| **the Obukhov "family of stationary profiles"** | **false.** An artifact of indexing one-sidedly; on the model's `ℤ`-index two-sidedness restores rigidity, so the stationary profile is unique in both sectors. |
| **anything black-hole** — the bit-to-area ratio `b/(b−1)`, the Planck-area mapping `4G ↔ (b−1)/b`, "no `ℏ`" | a *count* with no dynamics. The area law exists; no first law does. The `4G` dictionary is a choice of labels, not a result. |
| **the torus / scaling-quotient reading of the helix** | dead — the record already forbade it (`ZETA.md` §5.2; `plot_isotropic_helix.py:110,144`). The closure identifies *generations*, not *sizes*. |
| **"no per-shell bar" without the qualifier** | overstates. The proved statement is "no `(ν,e,j)`-only bar" plus a state-dependent threshold. §4 uses the qualified form. |
| **"the repelling is why Barbato's uniqueness holds"** | not proved — here or in `ZETA.md` §6.3. It links a `ν = 0` recursion to a forced stationary-solution theorem, and whether Thm 2.3 is `ν = 0`, `ν > 0`, or mixed was not determined. |

---

## 6. Verification ledger

Which load-bearing claims have been adversarially checked, and which have not. **An unchecked
claim is not a false one, but this project's record is that unverified prose is where the errors
were.**

| claim | where it would go | how it is backed |
|---|---|---|
| degree forced to `e = 2`; Bernstein bound implied by the definitions | Tao Post 1 | Lean (`Cascade/DissipationDegree.lean`, `Cascade/DimensionBlind.lean`). **No adversarial check.** |
| same threshold; exponents differ by the gradient's `+1` | Tao Post 2 | adversarially checked (the δ verifier): same `δ`, `θ_transfer = θ_amplitude + 1`, the `+1` being `∇` — `CASCADE_PALASEK_PRIOR_ART.md` Q2(b) |
| the ℤ/ℕ closure quotes, the clamp/free/drive trichotomy | Palasek | quotes fetched verbatim from the arXiv HTML by me; the trichotomy is `CLOSURE.md` §1/§4.2, machine-checked via `Cascade/SelfSimilarClosure.lean` and `zeta_checks.py` §K |
| `no_obukhov_perShellBar` (the `(ν,e,j)`-only form) and the sign-flip witness | Looi | **adversarially checked.** Verdict `SOUND WITH CORRECTIONS`: claims sound, the *unqualified* "no bar" wording deflated, and the signed-ladder/Remark-1.4 limit surfaced — both now incorporated above |
| the telescoping constant `12` is the same in both sectors | Looi | verified numerically, 600 random runs each, zero mismatches; my own check of the verifier's claim that it *differs* was that the verifier was wrong |

**The `PerShellThreshold` bar is a leaf and so is the ring.** `perShellBar` and all `bar_*` theorems
are referenced nowhere outside `Cascade/PerShellThreshold.lean`; `Cascade/SelfSimilarClosure.lean`
and `Cascade/IsotropicReduction.lean` are imported only by `Cascade.lean`. The bar/multiplier chain
(`DissipationThreshold → PerShellThreshold → PerShellSectorObukhov → StationarySectorMultiplier`)
contains no ring. Neither the `×0.79` per-rung factor nor the `12` goes through the ring: both come
from three neighbouring shells and a clamped cut.

**A build caution.** `lakefile.toml` line 3 sets
`defaultTargets = ["NavierStokes", "Euler", "ComparatorChallenges"]`, so **a bare `lake build` does
not build `Cascade`.** Use `lake build Cascade`. And the error grep that binds is `: error:`, not
`^error` — Lean prefixes errors with the file path, so `^error` silently passes a broken file.
