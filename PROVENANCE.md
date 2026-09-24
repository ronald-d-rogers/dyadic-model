# Provenance: which discoveries were human-led and which were AI-led

A record of attribution for this conversation. **Attribution is not correctness** — "human-led" means
the human raised it first, not that it survived; several human-led guesses were wrong and several
AI-led claims were retracted. Both columns are recorded.

Method: "raised by" = who first put the question or the claim; "established by" = who derived,
formalized or verified it. Where the two differ, both are given.

**Line numbers in this repo drift.** A first draft of this file cited `ZETA.md:745` for the
"two different scales" passage; after the zeta commits of this session it is at `:851`. Citations
below therefore name the **section or the quoted text**, with line numbers only where they were
checked at the time of writing. Do not trust a bare line number in this repository — grep the quote.

The earlier part of the conversation is reconstructed from the repository's own record
(`Cascade/CLOSURE.md` §8, `Cascade/ZETA.md`, `Cascade/OUTCOME.md`, `PROGRESS.md` and the commit
history); the later part is from the conversation directly.

---

## 1. Human-led, and correct

These are the ones where the human raised a claim **and it held**.

| discovery | what the human said | what it became | AI position before |
|---|---|---|---|
| **The loop closure — the ring** | **"close it into a self similar loop"** | the periodic closure `R_{n+N} = R_n` on the isotropic chain, which stabilises **iff `μ = 2^α`** (forced) and closes the tree onto the finite system on `ℤ/N`; at `b = 1` this is exactly §1.3's ring `q_k' = 4q_{k−1}² − q_kq_{k+1}` | **the AI had concluded no finite closure exists.** `CLOSURE.md` §4.2 still opens with that position, *"no finite cyclic quotient exists (§3.2)"*, and the correction is labelled only *"added later"* |
| **Isotropy — bundling a level** | "what if you bundle the 4 into one?" *(paraphrase from the earlier exchange)* | the isotropic reduction `X_j = μ^{−|j|}R_{|j|}`, on which the tree becomes a scalar chain and the branching number `b` survives only as a coefficient | the AI had been treating the tree level-by-level |
| **The size is the scaling orbit** | "can the loop be growing while the flow is happening — and would that be a separate state?" | the closed system is homogeneous of degree 2 **including the driven root**, so `R ↦ λR, t ↦ t/λ` is a symmetry; a growing cycle is the same orbit reparameterised | the AI had not asked |
| **Cauchy–Schwarz is a parallelogram statement** | "I thought Cauchy/Schwarz was about parallelograms really? It can be rearranged into a parallelogram" | the polarisation identity `⟨x,y⟩ = ¼(‖x+y‖² − ‖x−y‖²)` *is* the parallelogram; the `1/2` in `d/2` is the quadraticity the parallelogram law axiomatises | the AI had attributed the `1/2` to Cauchy–Schwarz generically |

The first three each **corrected or supplied a live AI position** — the loop closure overrode an
explicit AI conclusion, and the other two were questions the AI had not asked. These are the
strongest observations of the whole conversation. Where they live in the record:

- the **loop closure** is `Cascade/CLOSURE.md` §4.2's corrigendum, and the AI's overridden position is
  the un-struck sentence three lines above it. **The corrigendum does not record who suggested it** —
  see §6 below;
- the **isotropy** is `CLOSURE.md` §4.1;
- the **scaling orbit** is the final commit, *"A growing cycle is not a separate state: the size is
  the scaling orbit."*

## 2. Human-led, and wrong — but productive

Every one of these was a wrong guess that forced a real correction. Recorded because a wrong
question that produces a right answer is doing work.

| human guess | verdict | what it produced |
|---|---|---|
| "because 2 is the Laplacian" | **half right** | the *dissipation* degree `e = 2` is the Laplacian; the *Bernstein* saturation `d = 2` is not — it is `2 × 1` derivative. The disambiguation is now the clearest way to state both |
| "in high dimensions more arrows need to point the same direction" | **half right** | "more things must be small at once" is exactly right; "the same direction" is near-*orthogonality*, a different high-dimensional fact. Produced the "the cube is all corners" account and `V_d → 0` |
| "is genus 2 the second rung of the Bruhat–Tits?" | **wrong** | genus counts loops (`b₁`), the rung is the translation length — and `w = v(q)` is a *subdivision*, which leaves `b₁` unchanged. The cleanest statement of the distinction |
| "Heisenberg is saying that two clicks cannot coincide" | **wrong** | Heisenberg constrains **one** wave's two spreads; "two things cannot coincide" is Pauli (a sign argument) or statistics. Exactly the conflation `Criticality/Heisenberg.lean` warns against |
| "A + B must sum to a square (or rectangle), i.e. a multiple of something" | **productive** | forced the explicit identification of the telescoping multiple: `12 = 2 × (8 − 2)` |
| "doesn't the path the helix draws become a donut?" | **wrong** | produced the AI's *second* wrong answer, and then the correct one: the closure identifies **generations**, not sizes |

## 3. AI-led

### 3a. AI-led, and it held

| discovery | how it is backed |
|---|---|
| the sector identification — `A=1,B=0` is Katz–Pavlović, `A=0,B=1` is Obukhov, and Palasek eq. (1.2) is the latter | latent in the repo (`Cascade/PROGRESS.md`, the intermittency section: *"`α=1, β=0` is Katz–Pavlović, `α=0, β=1` is Obukhov"*); the match to the arXiv text was checked by me |
| the Palasek-2024 ℤ/ℕ corroboration — he states the group-structure requirement, the clamp `u_{−1}=0`, the weak-coupling approximation and the infinite-energy cost himself | quoted verbatim from the arXiv HTML; now `CASCADE_PALASEK_PRIOR_ART.md` Q1(b) |
| the δ resolution — **same** `δ`; `θ_transfer = θ_amplitude + 1` from the gradient `∇` | adversarially checked; `CASCADE_PALASEK_PRIOR_ART.md` Q2(b), the `∇u_j` derivation |
| the two `2`s are independent — `e = 2` is the Laplacian, `d = 2` is Bernstein saturation, and changing `e` leaves `d = 2` | `Cascade/DimensionBlind.lean` uses no dissipation |
| the `d/2 = d × 1/2` decomposition (dimension × parallelogram) | stated and checked numerically |
| `no_obukhov_perShellBar` — no `(ν,e,j)`-only per-shell bar in the Obukhov sector | machine-checked, axiom-clean, adversarially checked (`SOUND WITH CORRECTIONS`) |
| the telescoping multiple is `12` in **both** sectors | 600 random runs each, zero mismatches |
| the bit-to-area function `S/A = b/(b−1)`, and that holography and self-closure are the same dichotomy (levels grow) | computed exactly; the join is `[inference]` |
| the multiplier flip is the **inverse relation** — `ratioStepA ∘ ratioStepB = id` | machine-checked; this is what killed §3b's claim |
| **the bar is a leaf; so is the ring** | greps + import graph: `perShellBar` and all `bar_*` are read nowhere outside their file; `SelfSimilarClosure`/`IsotropicReduction` are imported only by `Cascade.lean` |
| **`lake build` does not build `Cascade`** (`defaultTargets` excludes it) | found by a build failure |
| **the error grep that binds is `: error:`, not `^error`** | found by a real `sorryAx` incident |
| the model supplies **cutting, not joining**; the shim is the boundary term of a conservation law | framing, `[inference]` |

### 3b. AI-led, and retracted

| claim | how it died | cost |
|---|---|---|
| **the helix's quotient is a torus, "the same construction as `ℂ*/q^ℤ`"** | the record already forbade it (`ZETA.md` §6.3b‴, *"two different scales here and they must not be confused"*; `Cascade/plot_isotropic_helix.py:110,144` — both still accurate); and my own construction has `b₁ = 2` where the p-adic skeleton has `b₁ = 1` | a proposed `CLOSURE.md` §7/§8 edit, killed |
| **the δ off-by-2 alarm** | the conventions are the same `δ`; the discrepancy is the gradient's `+1` | a false alarm about a correct file |
| **the Obukhov sector admits a family of stationary profiles, so Barbato-type uniqueness fails there** | one-sided indexing artifact; two-sidedness restores rigidity because the backward map *is* the other sector's forward map | a candidate addition to the Looi note, killed |
| **"the repelling is why Barbato's uniqueness holds"** | unproved; links a `ν=0` recursion to a forced stationary-solution theorem | flagged unproved in `ZETA.md` and the Lean file |
| **"the Obukhov sector has no per-shell bar at all"** | overstates: the proved claim is "no `(ν,e,j)`-only bar" | fixed in four places |
| the A-sector error-ratio identity holds for *every* `s*` | false — the residual goal is `s*³ = K` | caught by elaboration, and the `sorryAx` by the axiom audit |
| the Looi note has a **viscous scope hole** | my own false alarm — the bar's shell term carries `ν`; I had conflated it with the inviscid multiplier | corrected before it reached the note |

### 3c. Errors in the *verification*, not the work

| claim | verdict |
|---|---|
| the verifier's finding that the two budgets differ "in more than where the square sits" | **wrong.** The dissipation pieces coincide identically (`u_j²·2ν2^{(e−1)j} = u_j·2ν2^{(e−1)j}·u_j`); its report mis-transcribes the exponent as `2^{ej}` |
| the same verifier's "term by term with a uniform factor 2" objection to the prior-art file | **wrong**; the uniform factor 2 is exact |
| the verifier's `no_obukhov_perShellBar` verdict | **right and valuable** — it deflated the claim and surfaced the signed-ladder / Remark 1.4 limit, which was new |
| the verifier's `StationarySectorMultiplier` verdict | **right and decisive** — two-sidedness restores rigidity |

---

## 4. The pattern

1. **The largest single insights were human-led, and both corrected AI positions.** Isotropy closing
   the tree, and the size being the scaling orbit. In both cases the human asked a question the AI
   had not thought to ask.

2. **The AI's errors were all one type: comparing the wrong two objects.** A quotient of *shape*
   against one of *size*. One-sided indexing against a two-sided model. A forced stationary
   condition against a vanishing-transfer one. The mathematics was right each time; the object it
   was applied to was wrong.

3. **Every machine-checked AI claim survived. Every AI prose claim built on one was at risk.** Nine
   clean theorems in `StationarySectorMultiplier.lean`, all correct, and the sentence above them
   false. This is `Lean certifies derivations, not interpretations` with three instances in one
   session.

4. **Human guesses had a higher hit rate on structure than on detail.** "Bundle the 4", "is the loop
   growing", "parallelograms" — all structural, all right. "2 is the Laplacian", "the second rung",
   "two clicks" — all detailed, all wrong or half-wrong.

5. **The verification came from outside the derivation**, not from re-reading it: three adversarial
   subagents, one exact-arithmetic script per claim, and the file's own contradiction
   (`ZETA.md` §6.3b‴ had already forbidden the torus reading). Reading one's own work again does not
   catch this class of error; the record's own guard did.

---

## 5. Consequence for `OUTREACH.md`

The disclosure line says the analysis, the Lean development and the wording are AI-generated, and
gives a count of the structural observations that are the human's. **That count is three, not two** —
the loop closure, the isotropy bundling, and the scaling orbit (with Cauchy–Schwarz's parallelogram
structure as a fourth that is about an existing proof rather than about the model). `OUTREACH.md` §1
and Mastodon Post 3 have both been corrected to that count.

If the count is ever revised, revise it here first.

---

## 6. How the record lost the loop closure, and the fix

`Cascade/CLOSURE.md` §4.2 originally asserted that no finite closure exists. The human then
suggested closing the chain into a self-similar loop, and the closure turned out to work at the
forced `μ = 2^α`. **But the corrigendum that records this was entered as *"added later"* with no
attribution**, so the record preserved the *result* while losing the *source*. A reader of
`CLOSURE.md` alone would credit the AI — which is exactly what a first draft of §1 above did,
rolling the loop closure into a row labelled "Isotropy closes the tree."

That is the general failure mode of an unattributed record, and it is worth naming: **a record that
logs corrections without logging who forced them will systematically credit the wrong party**, and
the party it will credit is the one holding the pen. §4.2 now carries the attribution.
