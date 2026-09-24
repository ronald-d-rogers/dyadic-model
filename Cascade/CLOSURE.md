# The self-similar closure of the dyadic cascade: the chain, the tree, and the genus-1 geometry

**One page of orientation.** This is the written record of a thread that lived in a scratch
directory while this library was left unchanged. It asks three questions: how does a *self-similar
closure* work for the dyadic cascade, why does it not carry from a chain to a tree, and what is the
corresponding geometry? The verdict is negative and consistent with `OUTCOME.md`:

* the closure's finite-time blow-up **is** the repo's existing `Cascade.selfSimilar` re-derived in
  log coordinates — not a new blow-up, and its physical enstrophy is infinite;
* the closure **does not generalise** to a tree, for three structural reasons;
* what does close on a tree is a weaker, *different* condition (**isotropy**), which reduces the
  tree to a scalar chain whose constant mode **decays**;
* the geometry is the genus-1 **Tate curve**, a cycle (the "thermal cycle") with infinite rooted
  trees attached — the funnels — and none of the p-adic holography corpus read here builds a
  multi-funnel wormhole.

**Nothing here is a discovery.** Read this beside `OUTCOME.md`: the exercise's answer is negative,
and this document exists so the reasoning and its corrections are on the record rather than only in
a `/tmp` directory.

## How to read the labels

This repo has a documented history of confident claims that needed correction (see the **WITHDRAWN**
block of `PROGRESS.md` and the two corrections in `OUTCOME.md`). Every mathematical claim below
therefore carries one of these labels, and the citation is given with the label.

| label | means |
|---|---|
| **[proved]** | machine-checked in the named Lean file; the theorem name is given. |
| **[proved — exact computation]** | established for the stated finite cases by exact integer/`Fraction` arithmetic in the named scratch script (no floating point), cross-checked in `sympy` over `ℚ` and certified by full rank modulo two large primes. Exact, but **not** Lean-checked, and bounded by the stated degrees and `N`. |
| **[sourced — …]** | quoted from the named source, with the location in that source. |
| **[derived]** | follows by elementary algebra or a short argument from a [proved] or [sourced] statement; the step is written out where it is not immediate. |
| **[measured — script]** | a numerical check in a scratch script, named; exact-rational where said, floating-point otherwise. **Not a proof.** |
| **[inference]** | the reading of the analysing agent, stated in no source. |
| **[not found]** | we read the corpus in front of us and found no source for the claim. |
| **[extension — added by hand]** | **a different axis from the six above.** Those grade the *epistemic status of a claim*; this grades the *provenance of the model*. It means the structure was put in by the analyst, not forced by the scaling or by the coupling law, so **no `[proved]` or `[derived]` statement about the frozen model transfers to it without re-derivation**. Every claim made under an extension carries this tag, and the extension's own header must list, before any theorem, what it does *not* inherit. |

The scratch scripts named below (`check7.py`, `CMFINAL.py`, `cm2.py`, `CONSOLIDATED.py`,
`handcheck.py`) are in `/tmp/tree_closure/`, not in this repository, and will not survive it; the
names are recorded only so the checks are findable while the scratch lasts. The repo-side companion
figure is `Cascade/dyadic_ring.py` / `.svg`, whose header already states the four caveats of §2.

---

## 1. The closure, for the chain

### 1.1 The model, and why `u_N = u_0` is not a closure

The degree-`e` shell model is `u_k' = T_k + κ θ_k − ν·2^{ek}u_k` with the quadratic transfer

```
T_k = 2^k (u_{k-1}² − 2 u_k u_{k+1})          (boussinesqTransferU 1 0 u k)
```

For the inviscid, unforced case the equation is `u_k' = T_k`. **[sourced — `Cascade/SelfSimilarClosure.lean`, header and `velocityRHSDegreeE`; `Cascade/ShellModel.lean`]**

The transfer is quadratic and carries a `2^k`, so under a matching hypothesis `u_{k+N} = μ·u_k`
one has `T_{k+N} = 2^N μ²·T_k`. **[proved — `transfer_matching`]**

The naive closure `u_{k+N} = u_k` (`μ = 1`) therefore leaves a genuine flux defect:
`T_{k+N} = 2^N T_k ≠ T_k` whenever the transfer does not vanish at shell `k` (`N > 0`). It is not a
closure of the untruncated transfer at all. **[proved — `naive_closure_transfer_defect`]**

### 1.2 The self-similar twist closes the loop

Make the self-similar twist

```
u_{k+N} = 2^{−N} u_k        (μ = 2^{−N})
```

Consistency of the **derivative** relation `u'_{k+N} = μ u'_k` with the transfer relation
`T_{k+N} = 2^N μ² T_k` forces `2^N μ² = μ`, and with `μ ≠ 0` that has the unique solution
`μ = 2^{−N}`. So the twist, not the naive closure, is what makes the seam consistent. **[proved — `selfSimilarMu_closes`, `matching_multiplier_forced`]**

### 1.3 The reduced cyclic model

Write

```
u_k = 2^{−k} q_k ,        q_{k+N} = q_k   (period N)
```

Then `T_k = 2^{−k}(4 q_{k−1}² − q_k q_{k+1})`, so the inviscid cascade **is** the finite cyclic ODE

```
q_k' = 4 q_{k−1}² − q_k q_{k+1}        on ℤ/N
```

The two equations are equivalent at each shell. In reduced variables the self-similar matching is
exactly periodicity of `q`. **[proved — `transfer_twist`, `twist_ode_iff`, `twist_solves_iff`, `twist_matching_iff`, `velocityRHSDegreeE_twist`]**

The reduced budget has **no boundary defect and no cancellation**. For the per-period sum
`H = Σ_{k<N} q_k²` the cyclic reindexing `Σ_k q_k q_{k−1}² = Σ_k q_k² q_{k+1}` gives

```
H' = 6 Σ_{k<N} q_k² q_{k+1} − 2νH
```

The cubic **survives**. This is the exact replacement for the Dirichlet telescoping
`transfer_pairing_eq_zero`, where the clamped ends `u(−1) = u(N) = 0` make the pairing vanish
identically. **[proved — `cyclic_reindex`, `sum_reduced_pairing`, `reduced_enstrophy_hasDerivAt`; contrast `transfer_pairing_eq_zero`]**

### 1.4 The constant mode blows up

For the constant profile `q_k = c`, `4 q_{k−1}² − q_k q_{k+1} = 3c²`, so the cyclic ODE reduces to
the scalar Riccati equation

```
c' = 3c²
```

with solution `c(t) = (1/3)(T−t)^{−1} = c_0/(1 − 3c_0 t)`. For data `c_0 > 0` the level is unbounded
at the finite time `1/(3c_0)`. **[proved — `reducedTransfer_const`, `reduced_constant_ode`, `selfSimilar_scalar_hasDerivAt`, `selfSimilar_scalar_eq`, `const_profile_blowup`]**

A numerical integration of `q_k' = 4q_{k−1}² − q_kq_{k+1}` on `ℤ/5` from constant data was recorded
as blowing up at `t ≈ 0.3344` against the predicted `1/3`. **[measured — scratch RK4, floating point]**

The two opposite outcomes — Dirichlet clamps ⇒ global regularity (`truncated_globally_regular`),
self-similar twist ⇒ the cubic survives ⇒ blow-up — are **two boundary conditions on the same
reduced model**, not a contradiction. This is the interpretation `SelfSimilarClosure.lean` is built
to record.

---

## 2. The caveats that keep that honest

These four are load-bearing and must not be softened. They are the repo's own scope note, and the
companion figure `Cascade/dyadic_ring.py` states the same four in its header.

### 2.1 The blow-up profile is `Cascade.selfSimilar` re-derived

Under the twist the constant profile **is** the repo's existing self-similar solution:

```
twist (fun _ => (1/3)(T−t)^{−1}) k = selfSimilar T t k
```

and `selfSimilar_scalar_hasDerivAt` is obtained by *reusing* `selfSimilar_hasDerivAt` — no
differentiation is redone. So item 1.4 is a **re-derivation in log coordinates**, exactly as the
header of `SelfSimilarClosure.lean` says under "Honesty about novelty". It is not a new blow-up.
**[proved — `twist_const_eq_selfSimilar`, `const_profile_twist_is_selfSimilar`, `selfSimilar_scalar_hasDerivAt`; `Cascade/SelfSimilarSolution.lean`]**

### 2.2 The physical enstrophy is infinite

The physical enstrophy summand is

```
2^{2k} u_k² = q_k²
```

which is `N`-periodic whenever `q` is. So the lattice sum `Σ_{k∈ℤ} 2^{2k}u_k²` is the periodic value
times `Σ_{m∈ℤ} 1` and **diverges**; for the constant profile every window of `M` consecutive shells
carries `M c²`, unbounded in `M`. Therefore `H = Σ_{k<N} q_k²` is a **per-period density**, not the
physical enstrophy, and the closure's blow-up is **not** a finite-data blow-up of the physical model.
**[proved — `twist_physical_enstrophy_term`, `twist_physical_enstrophy_periodic`, `twist_enstrophy`, `constant_profile_enstrophy_block`]**

### 2.3 The profile violates the clamp

The self-similar profile has `u_N = 2^{−N} q ≠ 0` whenever `q ≠ 0`. It does **not** satisfy the
Dirichlet condition and is **not** a solution of the clamped/truncated model. The clamped model's
regularity and the self-similar blow-up are statements about **different systems** and are not in
tension. This is not a counterexample to `truncated_globally_regular`.
**[proved — `selfSimilar_not_dirichlet`, `twist_not_dirichlet_top`]**

### 2.4 Viscosity closes the ring only at `e = 0`

The twisted viscous coefficient is `ν·2^{ek}`, which is a function on the cycle only if `2^{eN} = 1`,
i.e. `e = 0` for `N > 0`. At the physical `e = 2` the ansatz is **not** preserved. The closure is a
**renormalization cycle, not a symmetry**. **[proved — `viscous_periodicity_iff`, `e_two_not_closed`, `viscous_coefficient_not_periodic`]**

### 2.5 Sign results nearby (context, not part of the closure)

The reduced cubic is **not sign-blind**: flipping the successor amplitude at a shell changes
`Σ_k q_k² q_{k+1}` by exactly `−2q_k²q_{k+1}`, and a witness takes `18 ↦ −18`; by contrast the
Dirichlet pairing vanishes for an arbitrary sign pattern. Separately, in the inviscid unforced model
a **global** sign flip is a time reversal, and the viscous term is the odd obstruction to it.
**[proved — `cubic_flip_sub`, `cubic_sign_sensitive`, `dirichlet_pairing_sign_blind`; `Cascade/SignReversal.lean`, `Cascade/SignEquivariance.lean`]**

---

## 3. Why it does not generalise to a tree

The tree model is Barbato–Bianchi–Flandoli–Morandin, *A dyadic model on a tree*, arXiv:1207.2846
(J. Math. Phys. **54**, 021507 (2013)). Nodes `j ∈ J`, root `0`, generation `|j|`, parent `j̄`,
children `O_j`, and `♯O_j = N_* = 2^{2ᾱ}` constant. The unforced inviscid system is eq. (17):

```
dX_j/dt = c_j X_{j̄}² − Σ_{k∈O_j} c_k X_j X_k ,      c_j = 2^{α|j|} ,   X_0̄ ≡ 0 .
```

The chain is the special case `O_j = {j+1}` (`b = 1`), eq. (8). **[sourced — arXiv:1207.2846 §2, eqs. (7), (8), (17)]**

Three reasons, all established, that the chain closure has no tree analogue.

### 3.1 A rooted tree has no level-shifting automorphism

A rooted `b`-ary tree is graded. Any automorphism fixes the root — the unique node with `|j| = 0` —
and preserves the parent map, hence preserves `|·|` by induction. So there is **no** bijection
mapping generation `n` to generation `n+N`, and nothing of the form `X_{k+N} = 2^{−N}X_k` can be a
symmetry to quotient by. Nekrashevych states the underlying fact for self-similar groups as: *"if
`f` is an endomorphism then `f(Xⁿ) ⊆ Xⁿ`"*.
**[sourced — Nekrashevych, *Self-similar groups*, Ch. 1; derived — generation preservation]**

The chain is special precisely here: for `b = 1` every generation contains exactly one node, so the
tree is a single infinite path, which *is* level-homogeneous and does admit the shift.

### 3.2 The branching profile admits no finite level-periodic quotient

The number of nodes per generation is `(1, b, b², b³, …)`, which is not periodic. Imposing a
generation-periodic identification would identify the single level-`0` node with `b^N` level-`N`
nodes — impossible for `b > 1`. Hence no finite cyclic quotient of the tree exists.
**[derived]**

### 3.3 A single infinite branch does not close

Pick a branch `ω = (ω_0, ω_1, …)`. The equation for `X_{ω_n}` sums over **all** children of `ω_n`:

```
c_{ω_n} X_{ω_{n−1}}² − Σ_{k∈O_{ω_n}} c_k X_{ω_n} X_k ,
```

and the sum runs over every child, not only `ω_{n+1}`. A decay relation imposed along the branch is
therefore coupled to the off-branch nodes and cannot close on branch data alone.
**[sourced — the equation is eq. (17); the coupling is read off it]**

Numerically, with `b = 2`, a "special" profile `S_n` on the all-zeros branch and a different profile
`R_n` elsewhere gives

```
X_{(0,)}/X_{()} = 0.615572   vs   X_{(1,)}/X_{()} = 0.307786   → unequal.
```

**[measured — `CONSOLIDATED.py` part D, floating point; the report quoted 0.6156 / 0.3078]**

### 3.4 One supporting structural difference

The **level-wise** energy identity `d/dt Σ_{|j|=n} X_j² = F_{n+1} − F_n` is false on a tree for
`b > 1`: inflow to level `n` is grouped by the parent while outflow from level `n` is grouped by the
child, and these are the same collection of pairs only when every parent has exactly one child (a
chain). The **cumulative** identity `d/dt E_n = F_{n+1}` — the discrete divergence, matching
arXiv:1207.2846 eq. (9) — holds. Exact-rational check over `b = 1..4`, `α = 0..3`: cumulative
identity 0 failures; single-level form 48/48 fail. **[measured — exact rational, `check7.py`; sourced — arXiv:1207.2846 eq. (9)]**

---

## 4. What does close on a tree: isotropy

### 4.1 The invariant manifold

The condition that *does* close is node-wise **isotropy** — the amplitude is a function of generation
alone:

```
X_j = μ^{−|j|} R_{|j|}
```

The angular data is constant on each level. Substituting in eq. (17) shows the right-hand side
depends only on `n = |j|` and on `R`; no angular variable appears, so the isotropic submanifold is
**forward invariant**. This is a *different* condition from a level shift, exactly as the question
anticipated. **[derived — direct substitution in eq. (17); measured — integrating the full finite tree flow from isotropic data leaves the within-level relative spread below `1e−14` for `(b,α) = (2,2), (3,2.5), (4,2.5)` (`CONSOLIDATED.py`)]**

### 4.2 The reduction is a scalar chain, not a finite quotient

On the isotropic manifold the tree reduces to a **scalar recurrence in the generation amplitudes** —
a chain over generations, one degree of freedom per generation. It is *not* a finite `(b+1)`-regular
quotient graph, because no finite cyclic quotient exists (§3.2). The branching number `b` survives
only as a coefficient.

> **Corrigendum (added later): the chain *can* be made periodic, at `μ = 2^α`.** The sentence above is
> right that the tree has no finite **graph** quotient (§3.2 stands), but it is wrong to conclude that
> no finite closure exists.
>
> **Provenance of this correction, recorded because the first entry of it was not.** The closure was
> not found by re-reading the equations; it was **suggested by the human collaborator** in this
> exchange — *"close it into a self similar loop"* — after this document had concluded the opposite.
> The correction below is the working-out. An earlier version of this corrigendum was entered as
> *"added later"* with no attribution, which would have credited the wrong party; see `PROVENANCE.md`
> §6 for why that failure mode is systematic.
>
> The two coefficients collapse to **constants** at exactly one value of the isotropy parameter:
>
> `A_n = 2^{αn}μ^{2−n}` and `B_n = b·2^{α(n+1)}μ^{−(n+1)}` are both independent of `n` **iff `μ = 2^α`**,
> and then
>
> ```
> Ṙ_n = 4^α R_{n−1}² − b R_n R_{n+1} .
> ```
>
> That reduced equation is autonomous and shift-invariant, so **periodic data gives a periodic
> solution**: with `R_{n+N} = R_n` the tree closes onto the finite system on `ℤ/N`. Verified exactly
> against the tree equation `Ẋ_n = 2^{αn}X_{n−1}² − b·2^{α(n+1)}X_nX_{n+1}` for `(α,b,N)` in
> `{(1,2,3),(1,3,4),(2,2,5),(1,2,2),(3,4,3),(1,1,4)}`. At `b = 1` this is *exactly* §1.3's ring
> `q_k' = 4q_{k−1}² − q_kq_{k+1}`. **[proved — exact computation, `zeta_checks.py` section K]**
>
> **What this is and is not.** It is a closure of an **invariant subspace** (isotropy), not of the
> tree as a graph — which is why §3.2 is untouched. And the *chain* closes unforced because its index
> set `ℤ` has no root, so the cycle's closing edge (`N−1 → 0`) is already in the lattice; the *tree*
> has a root at generation 0, so the closing edge must be supplied, and periodicity makes it
> `f = μR_{N−1} = 2^{αN}X_{N−1}` — the **folded-around top level**. So the isotropic periodic tree is
> a **driven** cycle: finite-dimensional and closed, but driven.
>
> Two consequences worth recording. (i) The constant mode of the reduced cycle is
> `ċ = (4^α − b)c²`, so the isotropic periodic cycle is marginal exactly at `4^α = b`, i.e.
> **`α = α̃`** — the coefficient `4^α − b` that `Cascade/ZETA.md` §6.3b′ withdrew is *correct* in this
> frame; what was wrong there was calling the profile a solution of the **rooted unforced** model.
> (ii) It unifies the ring and the top closure: both are one edge short in the tree and complete in
> the chain. **[derived]**

The derivation is two lines. With `X_j = μ^{−n}R_n` (`n = |j|`), the left-hand side is
`μ^{−n}Ṙ_n`; the source term is `2^{αn}·(μ^{−(n−1)}R_{n−1})² = 2^{αn}μ^{−2(n−1)}R_{n−1}²`; and the
sink sums over the `b` children, all at generation `n+1` with the same `R`, giving
`b·2^{α(n+1)}·μ^{−n}μ^{−(n+1)}R_nR_{n+1} = b·2^{α(n+1)}μ^{−(2n+1)}R_nR_{n+1}`. Multiplying through
by `μ^n`:

```
Ṙ_n = A_n R_{n−1}² − B_n R_n R_{n+1} ,
A_n = 2^{αn} μ^{2−n} ,        B_n = b · 2^{α(n+1)} μ^{−(n+1)} .
```

Note the sink uses the **child's** coefficient `c_k = 2^{α(n+1)}`, one factor `2^α` larger than the
parent's `c_j = 2^{αn}`; that factor is where the `2^α` in the ratio comes from. Dividing, both
invariants are elementary:

```
B_n / A_n = b · 2^α · μ^{−3}     (independent of n, proportional to b),
A_{n+1} / A_n = 2^α / μ          (independent of n).
```

So the entire `n`-dependence is a common factor, and `b` enters only through the ratio: a pure
branching gain. **[derived — substitution into eq. (17); measured — exact-rational fit with a third independent profile as verification, `CMFINAL.py`, all six `(b,α,μ)` rows `verified=True`]**

At `b = 1` the tree *is* the chain (with `c_j = 2^{α|j|}`; at `α = 1` this is exactly the repo's
chain), so "the tree reduces to a chain" is not an analogy for the chain case — it is an identity.
The two substitutions `u_k = 2^{−k}q_k` (§1.3) and `u_k = μ^{−k}R_k` used here are related by
`q_k = (2/μ)^k R_k` (at `α = 1`), which is why the same recurrence appears in two coefficient
normalisations.

### 4.3 The constant mode decays on the tree

For the constant isotropic profile `R_n ≡ c`, `Ṙ_n = (A_n − B_n)c²` with

```
K := A_n − B_n = 2^α μ (1 − b·2^α μ^{−3}) .
```

The exact-rational computation gives `K < 0` in **every** case computed:

| `b` | `α` | `μ` | `K` | behaviour |
|---|---|---|---|---|
| 4 | 2 | 1/2 | −254 | decay |
| 1 | 1 | 1/2 | −15 | decay |
| 1 | 1 | 1/3 | −106/3 | decay |
| 2 | 2 | 1/3 | −860/3 | decay |
| 4 | 3 | 1/2 | −1020 | decay |

**[measured — exact rational, `CMFINAL.py` and `cm2.py`; `cm2.py` computes the coefficient directly from the model with no fitting]**

The chain's `+3c²` requires **exactly the cyclic closure** — the identification `q_{k+N} = q_k` on
`ℤ/N` — which the tree cannot have (§3.2). The tree's isotropic chain is the same recurrence
evaluated on a non-cyclic path. **[derived]**

> **Corrigendum (added later; supersedes the `K > 0` criterion below).**
> The analysis above is of the **constant** mode `R_n ≡ c`, i.e. `ρ = 1`, and the quantity
> `K = A_n − B_n` **contains the gauge parameter `μ`** of the ansatz `X_j = μ^{−|j|}R_{|j|}`. That `μ`
> is chosen by the analyst and cancels from physical quantities, so `μ³ > b·2^α` is not a property of
> the model, and `ρ = 1` is not the self-similar mode. **The criterion below is therefore withdrawn.**
>
> A replacement was attempted and also **withdrawn**: substituting the profile `X_n = σ·r^{−n}`
> (`r = 2^α`) into eq. (1) does make the generation dependence cancel, giving the bulk coefficient
> `r² − b` — but only **at nodes that have a father**. The root has no father (`X_{0̄} ≡ f`, and `f = 0`
> when unforced), so the profile is **not** a solution of the unforced rooted model at any `α`; the
> energy balance is violated by exactly the phantom-father term `2σ³r²`. So no criterion of the form
> "the isotropic mode blows up iff …" is available here.
>
> The threshold `α̃` is reached in the paper differently: through the **stationary** profile
> `X_j = f·2^{−(|j|+1)(2α̃+α)/3}` and its ℓ² condition `α > α̃` (Prop. 6.1), which is exact. The
> `b = 1` identity, the ratios `B_n/A_n` and `A_{n+1}/A_n`, and §4.4's lift are unaffected.
> **[proved — exact computation, `Cascade/IsotropicReduction.lean` and `Cascade/zeta_checks.py`
> section I; see `Cascade/ZETA.md` §6.6]**

The original text follows, retained only as the record of what was written and **superseded** by the
corrigendum above:

> The tree's isotropic chain is the same recurrence evaluated on a non-cyclic path, and there the sign
> flips to decay. Blow-up would require `K > 0`, i.e. `μ³ > b·2^α`; no computed case satisfies this.
> **[derived — superseded]**

### 4.4 The source fact: the tree's self-similar solutions are lifts of the chain's

Barbato et al. show that the tree's self-similar (and stationary) solutions are obtained by **lifting
the chain's**:

* §4, Prop. 4.1: if `Y` solves the chain (16), then `X_j(t) := 2^{−(|j|+2)ᾱ} Y_{|j|}(t)` solves the
  tree (15) with `α = β + ᾱ`;
* §5.1, Prop. 5.5: the tree self-similar positive `l²` solution with `a_0 > 0` is obtained by lifting
  the chain's unique self-similar sequence (from their reference [2]);
* §6, Theorem 2.3 gives the inviscid stationary profile
  `X_j = f·2^{−((|j|+1)/3)(2ᾱ+α)}`; the stationary algebra `μ³ = b·2^α = 2^{2ᾱ+α}` reproduces its
  per-generation exponent `(2ᾱ+α)/3`. This is **not** the K41 inertial-range decay
  `X_j ∼ 2^{−11|j|/6}` of §1.1 eq. (4), which is a heuristic: at `α = 5/2, ᾱ = 1` the stationary
  exponent is `3/2` while the K41 heuristic exponent is `11/6`. The scratch report conflated the two,
  and this document records them as distinct.

So the tree's blow-up/self-similar solutions are the chain's, transported: a **re-derivation, not a
new result**. This is the same "no new blow-up" verdict as §2.1, now at the level of the tree.
**[sourced — arXiv:1207.2846 §4 Prop. 4.1, §5.1 Prop. 5.5, §6 Thm 2.3; the stationary algebra `μ³ = b·2^α` is derived]**

---

## 5. Integrability of the reduced ring: no conserved quantity

The reduced cyclic ODE of §1.3 is a finite quadratic system, and the thread left one obvious question
about it unasked: is it integrable? This section records the answer, computed in exact arithmetic in
`/tmp/ring_invariants/` — outside this repository, like the other scratch named in this document —
and cross-checked there. The answer is negative, and it is consistent with the rest of the file: the
ring's finite-time blow-up (§1.4) is unobstructed because there is nothing conserved to obstruct it.
The computation is exact but scratch, not Lean; the labels below say which statements it proves and
which are inferred.

### 5.1 The verdict, and the contrast

> **The reduced self-similar ring `q_k' = 4q_{k−1}² − q_kq_{k+1}` on `ℤ/N` is not Liouville–Arnold
> integrable — and stronger than that, it has no conserved quantity at all beyond constants.**
> **[proved — exact computation for the degrees and `N` of §5.4; inference at all degrees]**

The clearest statement is a contrast with three outcomes — none, exactly one, and `N−1`:

| system | independent invariants | invariant set the flow lies on |
|---|---|---|
| clamped chain | exactly one — the energy `E = Σ_k4^{−k}q_k² = Σ_ku_k²` | a sphere |
| the ring | **none** | nothing; it explores the whole space |

The **clamped chain** is the same recurrence with Dirichlet ends `q_{−1} = q_N = 0` (the clamp of
§2.3): `q_0' = −q_0q_1`, `q_k' = 4q_{k−1}² − q_kq_{k+1}` for `1 ≤ k ≤ N−2`, `q_{N−1}' = 4q_{N−2}²`.
It carries exactly one independent invariant, the weighted energy `E = Σ_k4^{−k}q_k² = Σ_ku_k²`;
that is `N−1` only at `N = 2`, so for `N ≥ 3` the clamped chain is **not** Liouville–Arnold
integrable either. The **ring** is strictly worse: it conserves nothing. A Liouville–Arnold
integrable `N`-degree-of-freedom system would carry `N−1` commuting invariants together with a
Poisson structure; the clamped chain reaches 1 and the ring 0. The third point of comparison is the
Volterra/Kac–van Moerbeke family of §5.6, which the ring cannot be mapped to.

### 5.2 Three different things called "invariant", and two called "torus"

This document uses "invariant" and "torus" in unrelated senses, and the integrability result only
makes sense if they are kept apart:

1. **A forward-invariant manifold** — a *set* mapped into itself by the flow. The isotropic
   submanifold `X_j = μ^{−|j|}R_{|j|}` of §4.1 is forward invariant. This is not a conserved quantity
   and does not confine the flow to the level set of a function.
2. **A conserved quantity (first integral)** — a *function* `F` with `L_V F = 0`, constant along
   orbits. This is what §5.3–§5.8 are about: the ring has none beyond constants; the clamped chain
   has one.
3. **The p-adic Tate torus** — the rigid-analytic quotient `K*/q^ℤ` of §7.1, a genus-1 curve. It is
   unrelated to the Liouville–Arnold tori of item 2: it is not the level set of any invariant of this
   ODE, and no integrable-system torus enters its construction.

So "the ring has no invariant torus" (no `N−1` commuting invariants) and "the geometry is a Tate
torus" (§7) are statements about different objects that happen to share a word. Likewise the
forward-invariance of §4.1 is compatible with the non-integrability here: a manifold can be forward
invariant while the flow on it conserves nothing. **[inference — a disambiguation, not a
mathematical claim]**

### 5.3 The method, and why the negatives are not a solver artifact

Let `V_k = 4q_{k−1}² − q_kq_{k+1}` and `L_V F = Σ_k (∂F/∂q_k)V_k`. The Lie derivative maps
homogeneous polynomials of degree `d` **linearly** to homogeneous polynomials of degree `d+1`,
because the field is quadratic with no linear or constant part. For each `(N,d)` the kernel of that
linear map is exactly the space of homogeneous degree-`d` invariants, and it was computed:

* kernel by exact `Fraction` RREF over `ℚ`;
* nullities cross-checked independently in `sympy` over `ℚ`;
* non-existence certified by full rank modulo two large primes, `p = 2147483647` and
  `p = 1000000007`; full rank mod `p` gives independence over `ℚ`, hence a trivial kernel. The two
  primes agreed in every case.

No floating point is used anywhere. A bug in the exact RREF (pivot normalisation) was caught by a
mandatory back-substitution check, not by inspection.

**The engine was validated by recovering known invariants**, so the negatives are not an artifact of
a broken solver: run on the Volterra ring `q_k' = q_k(q_{k+1} − q_{k−1})` it recovers `Σ_kq_k`
(degree 1, all `N`), the extra quadratics (`q_0q_2`, `q_1q_3` at `N = 4`; the `N = 5` quadratic;
`(Σq)²`), and it recovers the clamped chain's `E` below. **[proved — exact computation; the Volterra
invariants are standard, recovered as a check]**

### 5.4 Results: the ring has none, the clamped chain has exactly one

**The ring.** The dimension of the space of homogeneous polynomial invariants is **0 in every degree
computed**: `d = 1..9` for `N = 2..6`, `d = 1..8` for `N = 7`, and `d = 1..5` for `N = 8..12`. In
particular there is **no linear invariant**, **no degree-2 invariant** (no quadratic form is
conserved) and **no degree-4 invariant** (the other natural candidate for a quadratic system). Since
a polynomial first integral splits into homogeneous parts and `L_V` raises the degree, each
homogeneous part is again a first integral; the degree-by-degree kernel is therefore exhaustive for
*polynomial* invariants. **[proved — exact computation]**

**The clamped chain.** Exactly **one** independent invariant: the dimension is 1 in every even
degree, with basis `E^{d/2}` (e.g. at `N = 3, d = 4` the basis is `E²`), and 0 in every odd degree;
the invariant algebra is `ℚ[E]` through degree 8. The clamp conserves energy but does **not** make the
chain Liouville–Arnold integrable: one invariant is not `N−1` for `N ≥ 3`. **[proved — exact
computation, through degree 8]**

### 5.5 The seam: the ring conserves no energy, confirmed independently

The energy the clamp conserves is not conserved on the ring. Differentiating
`E_u = ½Σ_k4^{−k}q_k² = ½Σ_ku_k²` along the ring gives, exactly, for every `N ≥ 2`,

```
d/dt E_u = (2^{2N} − 1)/4^{N−1} · q_0 q_{N−1}² = (2^{2N} − 1) · u_0 u_{N−1}² ,
```

verified identically (sympy, residual exactly 0) for `N = 2..6`. At `N = 3` this is
`(63/16)·q_0q_2² = 63u_0u_2²`, the nonzero cubic source the thread's earlier hand computation
flagged. **This is an independent confirmation and is worth saying so**: the earlier statement was
made by hand, this is a second, exact machine differentiation of the same seam. The two forms
recorded in this file are different sums — the weighted energy here, and the unweighted per-period
`H = Σ_{k<N}q_k²` of §1.3, where the same phenomenon appears as `H' = 6Σ_{k<N}q_k²q_{k+1}` — but both
are nonzero cubics, which is the content of "the cubic survives". It is also the exact ring analogue
of the Dirichlet telescoping `transfer_pairing_eq_zero` of §1.3: the same `E` has derivative exactly
`0` on the clamped chain, because the two sums telescope, and the single seam term above on the ring.
**[proved — exact computation]**

### 5.6 Why it is not a Volterra / Kac–van Moerbeke lattice

The integrable quadratic lattices satisfy `x_k | V_k` — each component is divisible by its own
coordinate. Equivalently all `N` coordinate hyperplanes `{x_k = 0}` are invariant, and the system is
Hamiltonian for the log-canonical structure `{x_i, x_j} = c_{ij}x_ix_j`. **[derived — from the
defining form `x_k' = x_k(x_{k+1} − x_{k−1})`; the family identification is quoted from the standard
integrable-lattice literature as recorded in the scratch `REPORT.md` §5]** The ring fails this at
every level:

* **No invariant hyperplane.** An exact Gröbner computation over all projective charts of
  `L = Σa_kq_k` with `L | L_V L` finds **zero** invariant hyperplanes for `N ≥ 3`; the only case with
  one is `N = 2`, where it is the diagonal `q_0 = q_1`. A Volterra/KvM lattice in any linear
  coordinates has exactly `N`, so **no invertible linear change of variables carries the ring to a
  Volterra/KvM/Bogoyavlenskij lattice**. **[proved — exact computation]**
* **A pure square can never become a product.** Under `q_k = c_kx_k` with `c_k ≠ 0`,

  ```
  x_k' = (4c_{k−1}²/c_k) x_{k−1}² − c_{k+1} x_kx_{k+1} .
  ```

  The source term is a pure square `x_{k−1}²`, while the Volterra form needs `x_{k−1}x_k`
  (equivalently `V_k` divisible by `q_k`). No choice of the `c_k` turns a square into a product; the
  `4q_{k−1}²` term is exactly what is fatal. **[derived]**
* **No log-canonical structure.** A log-canonical Hamiltonian has `(A∇H)_k` divisible by `q_k`;
  `V_k` is not, so the ring is not Hamiltonian for any log-canonical structure. **[derived]**
* **No constant Poisson structure.** Solving `d(AV)` symmetric for a constant antisymmetric `A`
  gives `A = 0` only, for `N = 2..6`. **[proved — exact computation]** Consequently there is no
  Hamiltonian at all for these `N` via a constant structure. More generally, if `V = A∇H` with `A`
  antisymmetric, then `dH/dt = ∇H^{T}A∇H ≡ 0`, so `H` is itself a first integral — and §5.4 excludes
  polynomial first integrals in every degree `≤ 9`.

A general invertible transformation (not merely linear or diagonal) is not ruled out; that is the
conjecture of §5.8. **[inference]**

### 5.7 What does survive

* **Scaling symmetry.** `q_k(t) ↦ λq_k(λt)` maps solutions to solutions — the field is homogeneous of
  degree 2. This is what makes the degree-by-degree search exhaustive. **[proved — exact
  computation]**
* **The invariant diagonal.** The diagonal `q_k = q` is invariant and reduces to `q' = 3q²`, i.e.
  `q(t) = a/(1 − 3at)`, blowing up at `t = 1/(3a)` for `a > 0`. This is the finite-time blow-up of
  §1.4, and **no invariant constrains it**. **[proved — exact computation; the reduction itself is
  §1.4 and the Lean statements cited there]**
* **No polynomial Hamiltonian of degree `≤ 9`.** Any `V = A∇H` with `A` antisymmetric forces `H` to
  be a first integral, and there is none of degree `≤ 9`. **[proved — exact computation]**
* **No invariant measure with polynomial density of degree `≤ 3`.** `div V = −Σ_kq_k ≠ 0`; solving
  `div(ρV) = 0` for polynomial `ρ` of degree 0–3 gives `ρ = 0` only, `N = 2..6`. **[proved — exact
  computation]**
* **No rational invariant of low bidegree.** There is no nonzero Darboux polynomial
  (`L_V g = λg` with `λ` linear, `λ ≠ 0`) of degree 1–2 for `N = 3..7`, and none of degree 3 for
  `N = 3`. A homogeneous rational first integral `P/Q` would force `P` and `Q` to be Darboux with the
  same cofactor, so there is **no rational first integral of bidegree (1,1), (2,2), or (3,3) at
  `N = 3`**. **[proved — exact computation]**
* **A general Lax pair is left open.** The absence of polynomial invariants up to degree 9 obstructs
  any Lax representation whose `tr L^j` land in those degrees, but a Lax pair with non-polynomial or
  gauge-dependent `L` is neither found nor ruled out, and no claim is made there.

### 5.8 Caveats, stated explicitly

* "No polynomial invariant of degree `≤ 9` for the computed `N`", and the Darboux statements of
  §5.7, are **proved** (exact computation, §5.3).
* "No invariant at any degree, for all `N`" is a **conjecture**: the pattern `dim = 0` is uniform in
  every computed `(N,d)` and the modular ranks are exactly full in every case, but no structural
  proof is offered. **[inference]**
* **Non-polynomial `C¹` first integrals are not excluded.** Locally every nonvanishing vector field
  has one; the result is about polynomial (and low-bidegree rational) invariants, the meaningful
  class for a polynomial ODE.
* `N = 1` is degenerate: the "ring" is the single node `q' = 3q²`, with no polynomial invariant
  beyond constants and no meaningful notion of integrability. It is reported only for completeness.

### 5.9 Consequence for the rest of this file

On the ring there are **no tori** and **not even one** invariant sphere: the flow is unconstrained by
any conserved quantity, which is consistent with the unobstructed finite-time blow-up of §1.4. **Any
argument in this document that rests on a blow-up confined to a subtorus — or on a conserved energy
on the ring — has no support here.** The clamped chain is different but still weak: exactly one
invariant, so its flow lies on spheres and never on tori. And the "torus" of the geometry is only a
homonym: it is the p-adic Tate curve `K*/q^ℤ` of §7, not an invariant manifold of this ODE (§5.2).

### 5.10 The clamped-chain enstrophy excursion, measured in this repo

The companion figure `Cascade/ring_invariants.svg` draws an enstrophy excursion of the
**clamped** chain and labels it a measurement. That computation is recorded here, and its script
is `Cascade/clamped_enstrophy.py` — standard library only, deterministic, and **in this
repository**, unlike the scratch scripts named elsewhere in this file.

**Setup and bound.** Clamped chain of §5.1 at `N = 3`, inviscid and unforced,
`u_k' = 2^k(u_{k−1}² − 2u_ku_{k+1})` with `u_{−1} = u_3 = 0`, from `u(0) = (1,2,3)`:

```
E = u_0² + u_1² + u_2² = 14 ,      H = u_0² + 4u_1² + 16u_2² = 161 ,
weight bound   H ≤ 4^{N−1}E = 16·14 = 224 .
```

`E` is the clamp's one invariant (§5.4); `H` is not conserved. The bound is attained **exactly**
only when all the energy sits on the top shell, `u = (0,0,±√14)`, where `E = 14` and
`H = 16·14 = 224` — so the ceiling measures **concentration of energy onto the smallest resolved
scale**. **[derived — `4^k ≤ 4^{N−1}` for `k < N`; the top-shell datum is the equality case]**

**The measurement.** RK4 at `dt = 1e−4` over `[0,2000]`, with a convergence check at `dt = 2e−5`
over `[0,50]` (the two `H(50)` values agree to `1.3e−11`, so the value is not a step-size
artifact):

| `t` | `H` | `E` | deficit `224 − H` | `2E/t = 28/t` | ratio |
|---|---|---|---|---|---|
| 50 | 223.477305 | 14 | 0.522695 | 0.560000 | 0.933 |
| 100 | 223.729587 | 14 | 0.270413 | 0.280000 | 0.966 |
| 200 | 223.862349 | 14 | 0.137651 | 0.140000 | 0.983 |
| 500 | 223.944319 | 14 | 0.055681 | 0.056000 | 0.994 |
| 1000 | 223.972052 | 14 | 0.027948 | 0.028000 | 0.998 |
| 2000 | 223.985998 | 14 | 0.014002 | 0.014000 | 1.000 |

`H` increases **monotonically** (smallest one-step increment `≈ 7e−10`) and approaches the
ceiling **asymptotically, never crossing it**; `E` is conserved to about `1e−12` over the run.
Across the sampled range the deficit is fit by `4^{N−1}E − H ≃ 2E/t = 28/t` to about three
digits. That fit is an **empirical observation over the six sampled times, not a proved
asymptotic law**. **[measured — clamped_enstrophy.py, in this repo]**

**Interpretation, carefully.** This is the *clamped* chain, where the ceiling `H ≤ 4^{N−1}E` is a
theorem; the `1/t` approach to saturation is the concentration mechanism made visible, and it is
what the ceiling catches — `E` is invariant and `H` cannot escape the box `E` puts it in. It is
**not a blow-up**, and it says nothing about `N = ∞`: the bound `4^{N−1}E` itself diverges as `N`
grows, so no uniform-in-`N` enstrophy bound follows. **[inference]**

**Provenance.** This supersedes the figure label that calls `223.48` a "max": `223.48` is the
value at `t = 50` (rounded), **not a maximum**, because `H` is still rising there. The numbers
are RK4 numerics, **[measured]**, not **[proved]**.

---

## 6. The corresponding geometry, and where the chain is special

The chain is **2-regular**: `b = 1`, each generation is one node, and a single shift is cocompact.
Its quotient is the cycle `ℤ/N` — **the ring**. A single shift already closes the whole lattice into
one circle. **[derived — §1, §3.1]**

For degree ≥ 3 a single loxodromic element does **not** give a finite quotient. Arends–Peterson–Weich
describe exactly what it gives: *"⟨γ⟩\T is isomorphic to a cycle graph of length ℓ (the image of the
geodesic under the projection) with each vertex on the cycle having several attached rooted trees"*,
and they call the underlying object a **hyperbolic cylinder**. The picture is the tree analogue of
`⟨γ⟩\H`: a closed geodesic of translation length `ℓ` whose removal leaves two funnels.
**[sourced — Arends–Peterson–Weich, "Resonances on geometrically finite graphs", arXiv:2603.26443 §3.2 (funnels and convex cocompact groups, Fig. 3.1)]**

Finite quotients need a **cocompact lattice**, not a cyclic group. The non-finiteness of `⟨γ⟩\T` for
degree ≥ 3 is established by the Švarc–Milnor lemma together with Nielsen–Schreier.
**[derived — the standard argument as recorded in the thread]**

> **Sharpening (added later).** Cocompactness alone is **not** the obstruction — cocompact lattices of
> every rank exist for the tree (Schottky groups), and their quotients are finite graphs with any
> `b₁ = g`. What fails is that those groups are **ungraded**: they move generation. Closing the
> *cascade* needs a group satisfying **two** conditions, and only the second is geometric:
>
> **(i) it preserves the equations.** The coefficients are `c_j = 2^{α|j|}` with `α > 0`, and
> `n ↦ 2^{αn}` is injective, so `c_{γj} = c_j` for all `j` forces `|γj| = |j|` for all `j` — i.e.
> preserving the equations forces preserving the **level function** `|·|`.
> **(ii) its quotient is finite.**
>
> If `|γj| = |j|`, the level function **descends** to `Γ\T` and still takes every value `0, 1, 2, …`,
> so `Γ\T` has at least one vertex per level and is **infinite**. Hence (i) and (ii) are
> incompatible: **no grading-preserving cocompact group exists.** The only escape is to *shift* levels
> rather than preserve them — `|γj| = |j| + N`, with the coefficient scaling `2^{αN}` absorbed by the
> twist `u_{k+N} = μu_k` — and that requires levels `n` and `n+N` to be **equinumerous**. Level sizes
> are `1, b, b², …`, so this holds only at `b = 1`.
>
> So every `b₁ = g` quotient the p-adic geometry offers is **ungraded**, and using one would not
> preserve the cascade's equations: **the geometry supplies no closure the cascade did not already
> have.** This is what "the p-adic geometry does not make the cascade close" means.
> **[derived — this document's sharpening; the level-descent argument is a proof, the equinumerosity
> a trivial computation]**
>
> **Figures.** `Cascade/isotropic_closure.py` → `.svg`/`.png` is the record: *braid → rope → twist →
> knot*, four panels plus the algebra and a caveats box (stdlib only, like the other figures here).
> `Cascade/plot_isotropic_helix.py` → `.svg`/`.png` draws the one thing the record panels cannot: the
> physical object itself, a **helix** closing up to the twist rather than a circle. That second script
> is the repository's **only** figure needing `numpy`/`matplotlib` (a repo-local `.venv-plotting`,
> gitignored); it is deterministic (`svg.hashsalt` pinned, no embedded date) and self-checking.
> **[exact for the relation; the drawn periodic profile `R_n` and the parameters are illustrative]**

So the statement is:

> **The chain's ring closes because degree 2 is the only degree at which one element suffices.**
> **[derived]**

This is the geometric face of the failure in §3: the algebraic obstruction (no level shift) and the
geometric one (a level-preserving group cannot be cocompact) are the same fact — and the *shift* that
rescues the chain is exactly the one that needs equinumerous levels, which a tree does not have.

---

## 7. The genus-1 case, with the corrections that were needed

All of the following was checked against the sources read for this thread. The bold "corrections"
are the places where the thread's first reading was wrong and was repaired.

### 7.1 What the Tate curve is

* The Tate curve is `K*/q^ℤ`. It is the p-adic analogue of the complex torus `ℂ*/q^ℤ`, and it has
  **genus 1**. Tate's theorem: there is a surjective homomorphism `φ : K* → E_q(K)` with kernel
  `q^ℤ`. **[sourced — Tate's uniformisation as stated and proved in the Schottky/Mumford-curve notes read (Thm 0.1 and Thm 4.4, "the kernel is `q^ℤ`"); complex model `ℂ*/q^ℤ` ibid.]**
* Keep the two objects **distinguished**: the **rigid-analytic** quotient `K*/q^ℤ`, and the
  **algebraic** Weierstrass cubic `E_q` (`y² + xy = x³ + a_4(q)x + a_6(q)`).
  **[sourced — ibid., Def. 4.2]**
* Reduction is **split multiplicative**. In the Kodaira–Néron classification, type `I_n` gives a
  special fibre that is a loop of `n` copies of `ℙ¹`, so the skeleton is a **loop**.
  **[sourced — type `I_n` loop: Berkovich-skeleton notes read, Example 9; split multiplicative: Schottky notes §5]**

### 7.2 The skeleton is the finite core, not the whole quotient

* The **skeleton** is the finite **minimal / convex-core** graph, not the full quotient.
  **[sourced — Mumford, "An analytic construction of degenerating curves over complete local rings", Compositio Math. 24 (1972) 129–174, Thms 1.23 and 3.3; Heydeman–Marcolli–Saberi–Stoica, arXiv:1605.07639 ("the quotient `T_k/Γ` consists of a finite graph `T_Γ/Γ` with infinite trees appended at the vertices"); Li–Matheus–Pan–Tao, arXiv:2412.20754 Remark 2.15 ("This skeleton `Σ_X` is the analogue of the convex core …")]**
* The two differ **exactly by the funnels** — the infinite trees appended to the finite graph — and
  the first Betti number `b₁` is the same either way, since trees are contractible.
  **[derived — deformation retract]**
* The genus of the curve is the first Betti number of the skeleton.
  **[sourced — Payne, "Tropical Brill–Noether Theory 11: Berkovich Analytification and Skeletons of Curves", Thm 11.26: `g(X) = g(Σ(X,V(X))) + Σ_{x∈V(X)} g(x)`, where `g(Σ(X,V(X)))` is the first Betti number of the skeleton]**

### 7.3 Funnels are NOT cusps, and in characteristic zero there are no cusps

* Funnels and cusps are **distinct** notions, defined separately.
  **[sourced — Arends–Peterson–Weich, arXiv:2603.26443, Def. 2.1 (orbifold funnel) and Def. 2.2 (cusp)]**
* *"Cusps are genuinely a positive characteristic phenomenon"*: in characteristic zero every lattice
  is cocompact, so the quotient has **no cusps at all**.
  **[sourced — arXiv:2603.26443 §3.4]**
* A Mumford curve is smooth projective, hence compact, so there are no archimedean-style cusps
  either. **[derived]**
* The genus-1 quotient is a **cycle of length `w`** — Huang–Jepsen call it the **"thermal cycle"** —
  with infinite rooted trees attached: the funnels.
  **[sourced — Huang–Jepsen, "Finite Temperature at Finite Places", arXiv:2408.04199 (thermal cycle, `w` edges)]**

### 7.4 The boundary: a correction

* The quotient's boundary is **`Ω_Γ/Γ`**, the Mumford curve's `K`-points — the set of ends of the
  quotient graph — **not** the limit set `Λ_Γ`. Mumford: *"C(K), the set of K-rational points of C,
  will be naturally isomorphic to the set of ends of Δ/Γ."* Heydeman–Marcolli–Saberi–Stoica write
  `X_Γ(k) = Ω_Γ(k)/Γ` for the Mumford curve. **[sourced — Mumford, Compositio Math. 24 (1972), p. 130; arXiv:1605.07639]**
* **Both are Cantor sets**, so the conclusion *"the boundary is a Cantor set, not circles"* stands —
  but the earlier **identification was wrong**. This is a correction, not a retraction.
  **[sourced for both being Cantor sets; the correction is the thread's]**

### 7.5 Consequence for any "n-boundary" reading

* There **is** a discrete count of funnels, so the statement *"the p-adic side has no discrete `n`"*
  is **too strong**. **[inference]**
* But a finite disjoint union of Cantor sets is again a Cantor set, so the funnel count is
  **invisible in the boundary's homeomorphism type**, and the funnels are not separate boundary
  components. **[derived]**
* The funnel count `w(q−1)` is **the analysing agent's inference, stated in no source**. It is
  recorded here only as such. **[inference]**

### 7.6 RT does work here

* Heydeman–Marcolli–Parikh–Saberi, arXiv:1812.04057 §5: the bulk dual of boundary entanglement is
  *"the lengths of minimal geodesics homologous to the boundary intervals in the black hole
  background, the analog of the Ryu–Takayanagi formula in this geometry"*; the geodesics wrap the
  horizon, and they verify the match numerically and prove subadditivity, strong subadditivity and
  monogamy. **[sourced — arXiv:1812.04057 §5]**
* Huang–Jepsen: entanglement on the Tate curve scales with `w`, *"which provides a compelling reason
  to associate this variable to a black hole radius."* **[sourced — arXiv:2408.04199]**
* Assembling these: the funnel width = the translation length = the thermal-cycle length = the p-adic
  analogue of a **cuff length**. **[derived — identification across arXiv:2603.26443, arXiv:2408.04199, arXiv:1812.04057]**

### 7.7 The p-adic analogue of a pair of pants

* A `ℙ¹` with three marked points. Brosnan–Fakhruddin: *"Any trivalent graph Γ with 2g−2 vertices
  gives rise to a unique totally degenerate stable curve `C_Γ` of genus g … We choose a copy of
  `P¹_k` with three marked rational points for each vertex of Γ and label the marked points with the
  edges incident on the vertex, a loop being counted twice."*
  **[sourced — Brosnan–Fakhruddin, "Fixed points, local monodromy, and incompressibility of congruence covers", JAG 1449 §4.1.3]**
* The literal phrase **"p-adic pants decomposition" was not found**.
  **[not found]**

### 7.8 Nothing builds a multi-funnel wormhole

No source read builds a p-adic multiboundary / multi-funnel wormhole. The existing p-adic holography
corpus is **single-boundary**: the genus-0 tree, the genus-1 Tate curve, and higher-genus Mumford
curves. **[not found]**

---

## 8. Verdict

* The **chain closes**: the self-similar twist `u_{k+N} = 2^{−N}u_k` is the consistent matching, the
  reduced system is the finite cyclic ODE `q_k' = 4q_{k−1}² − q_kq_{k+1}` on `ℤ/N`, and its constant
  mode obeys `c' = 3c²`, blowing up at `1/(3c_0)`.
* That blow-up is **`Cascade.selfSimilar` re-derived**, with infinite physical enstrophy and a
  profile that violates the clamp. It says nothing about the clamped model and nothing about
  Navier–Stokes.
* The closure **does not generalise to a tree**: no level-shifting automorphism, no finite
  level-periodic quotient, and no branch-local closure.
* What closes instead is **isotropy**, reducing the tree to a scalar chain with the branching number
  as a coefficient; its constant mode **decays** on the non-cyclic path, and the tree's self-similar
  solutions are **lifts of the chain's** (arXiv:1207.2846 §4/§5.1).
* The geometry is the **Tate curve**: a rigid-analytic `K*/q^ℤ` (algebraic model `E_q`), genus 1,
  skeleton a loop, quotient a cycle of length `w` with infinite trees (the funnels). RT works there;
  nothing builds a multi-boundary version. The chain's ring is the degree-2 exception.

**Status: negative, and a record rather than a discovery.** For the tree and the p-adic *geometry*, no
Lean file was added: the only machine-checked content of the closure itself is
`Cascade/SelfSimilarClosure.lean`, which declares its own blow-up a re-derivation. (The companion
question — whether a **zeta** attached to the cascade's tree can carry the critical exponent — is
recorded in `Cascade/ZETA.md`, and its combinatorial core is machine-checked in `PAdicZeta/`.)

**See also `Cascade/ZETA.md`**, the sibling record. Its result: a single Artin–Mazur/Ruelle zeta of the
full `p`-adic shift carries the branching number `p = N_*` and nothing else; the critical exponent
`α̃ = ½ log₂ N_*` needs exactly **one** external ingredient, the factor `½` (`N_* = p` is a definition);
and the one hoped-for escape — a self-dual functional equation with symmetry axis `α̃` — exists, is
unique, and is **forced by the pole**, so it selects nothing.

---

## Corrections to the thread's own record

Recorded here because this repo's history (and this thread's) is that confident numbers need
re-checking. The first is load-bearing; the rest are wording or asides.

1. **The isotropic coefficient ratio — the earlier closed form is WRONG.** An earlier closed form
   `B_n/A_n = b·2^{2α−2}` (with `A_{n+1}/A_n = λ = 4μ^{−2}`) was circulated in the working notes
   and in the conversation that produced this file. **It is wrong and must not be used.** It is
   stated in the scratch `REPORT.md` and reproduces none of the computed cases. The correct,
   verified values are

   ```
   B_n/A_n = b·2^α·μ^{−3} ,        A_{n+1}/A_n = 2^α/μ .
   ```

   For `b=1, α=1, μ=1/2` these give `16` and `4`, which are the numbers in the scratch table; the
   wrong form gives `1` and `16`. The derivation of the correct form is in §4.2 and can be checked
   by hand. The structural claim that survives — that `B_n/A_n` is **independent of `n`** and `b`
   enters **only** through that ratio — is unaffected, as is the decay conclusion
   `K = A_n − B_n < 0`. **[correction]**

   **Evidence, and a warning about the scratch scripts.** The scratch `REPORT.md` is *internally
   inconsistent*: its table lists `B/A = 16` for `b=1, α=1, μ=1/2`, while the line beneath the
   table asserts `b·2^{2α−2} = 1`. Independently, `CONSOLIDATED.py` **fails its own exact check**
   (120/180 failures, and 15/15 in its key case) — the isotropic formula it prints is not the one it
   tests. Of the scratch scripts, **only `CMFINAL.py` verifies** (all six `(b,α,μ)` rows, with a
   third independent profile as a cross-check); `cm2.py` independently confirms the constant-mode
   coefficient directly from the model. The numbers in this document come from `CMFINAL.py` and
   `cm2.py`, both re-run for this record. **The other scratch scripts (`CONSOLIDATED.py`, and the
   superseded `verify*.py` / `final*.py` fitting attempts named in the scratch report) should not be
   relied on.** A future reader must not be able to recover the wrong coefficient from this record,
   so the wrong form is written here explicitly, to be killed rather than inherited.
   **[correction]**

2. **"Same recurrence" wording.** The scratch report's §5 says the chain and the tree reduce to the
   literal constant-coefficient recurrence `S_k' = 4S_{k−1}² − S_kS_{k+1}`. That is the **reduced
   cyclic form** in the variables `q` after the twist `u_k = 2^{−k}q_k`, not the general isotropic
   reduction, whose coefficients `A_n, B_n` are generation-dependent. The identity is exact at
   `b = 1` after the rescaling `q_k = (2/μ)^k R_k` (at `α = 1`). The decay conclusion is unaffected.
   **[correction]**

3. **The "large twist" aside.** The scratch report adds that blow-up "could be restored by a large
   twist `μ`, for which the profile `X_j = μ^{−|j|}R` grows with depth — the unphysical direction."
   The condition `K > 0` is indeed `μ³ > b·2^α`, but `μ > 1` makes `μ^{−|j|}` *decay* with depth, not
   grow, so the parenthetical is at least mislabelled. Left unresolved here rather than repeated.
   **[not verified]**

4. **The stationary profile vs the K41 exponent.** The scratch report presents the stationary
   profile as `2^{−((α+2ᾱ)/3)|j|}` and identifies it with the source's `2^{−11|j|/6}` at
   `α = 5/2, ᾱ = 1`. Those are **two different objects**: Theorem 2.3 gives the exact stationary
   solution `X_j = f·2^{−((|j|+1)/3)(2ᾱ+α)}` (exponent `3/2` at `α = 5/2, ᾱ = 1`), while
   `2^{−11|j|/6}` is the **K41 inertial-range heuristic** of §1.1 eq. (4), derived there by a
   different argument. §4.4 records them separately. **[correction]**

---

## Sources

| source | what is taken from it |
|---|---|
| `Cascade/SelfSimilarClosure.lean` | the entire chain closure of §1, the caveats of §2, the sign contrast |
| `Cascade/SelfSimilarSolution.lean` | the flat self-similar solution that §1.4 re-derives |
| `Cascade/TruncatedRegularity.lean` | `truncated_globally_regular`; the clamped model §2.3 contrasts with |
| `Cascade/SignReversal.lean`, `Cascade/SignEquivariance.lean` | §2.5 |
| `Cascade/OUTCOME.md`, `Cascade/PROGRESS.md` | house style, labelling, the **WITHDRAWN** idiom, the overall negative |
| Barbato–Bianchi–Flandoli–Morandin, *A dyadic model on a tree*, arXiv:1207.2846 (J. Math. Phys. **54**, 021507 (2013)) | tree model §2 eqs. (7), (8), (17); energy identity eq. (9); lift §4 Prop. 4.1; §5.1 Prop. 5.5; stationary profile §6 Thm 2.3 |
| Nekrashevych, *Self-similar groups*, Ch. 1 | the endomorphism/level fact of §3.1 |
| Arends–Peterson–Weich, *Resonances on geometrically finite graphs*, arXiv:2603.26443 | §3.2 hyperbolic cylinder and cycle graph; Defs 2.1/2.2 funnels vs cusps; §3.4 characteristically-positive cusps |
| Mumford, *An analytic construction of degenerating curves over complete local rings*, Compositio Math. **24** (1972) 129–174 | Thms 1.23, 3.3 (finite/core graph); `C(K)` = ends of `Δ/Γ` |
| Heydeman–Marcolli–Saberi–Stoica, arXiv:1605.07639 | finite graph `T_Γ/Γ` with infinite trees appended; `X_Γ(k) = Ω_Γ(k)/Γ` |
| Li–Matheus–Pan–Tao, *Selberg, Ihara and Berkovich*, arXiv:2412.20754 | Remark 2.15, skeleton as convex-core analogue |
| Payne, *Tropical Brill–Noether Theory 11: Berkovich Analytification and Skeletons of Curves* | Thm 11.26 genus = first Betti number of skeleton |
| Heydeman–Marcolli–Parikh–Saberi, *Nonarchimedean Holographic Entropy from Networks of Perfect Tensors*, arXiv:1812.04057 | §5, the Ryu–Takayanagi analogue and its properties |
| Huang–Jepsen, *Finite Temperature at Finite Places*, arXiv:2408.04199 | thermal cycle length `w`; entanglement scales with `w`; "black hole radius" |
| Brosnan–Fakhruddin, *Fixed points, local monodromy, and incompressibility of congruence covers*, JAG 1449 | §4.1.3, trivalent graph ⇒ stable curve, `ℙ¹` with three marked rational points per vertex |
| Berkovich-skeleton seminar notes (Castillejo, *Skeleton of Berkovich spaces*) | Example 9, type `I_n` ⇒ loop of `n` copies of `ℙ¹` |
| Schottky/Mumford-curve notes read for this thread (Tate curve, Thms 0.1/4.4, Def. 4.2, §5) | Tate's theorem, kernel `q^ℤ`, the Weierstrass cubic, split multiplicative reduction |
| scratch: `CMFINAL.py`, `cm2.py`, `CONSOLIDATED.py`, `check7.py`, `handcheck.py` (in `/tmp/tree_closure/`, not in this repo) | the exact-rational fits and the numerical checks of §3, §4 |
| scratch: `inv.py`, `run_all.py`, `more.py`, `structure.py`, `darboux.py`, `extras.py` (in `/tmp/ring_invariants/`, not in this repo) | the exact invariant computation of §5: Lie-derivative kernels and modular certificates, the energy seam, the hyperplane / Hamiltonian / Darboux searches. The `x_k | V_k` property of the Volterra/KvM family is quoted there from the standard integrable-lattice literature |

## What could not be verified

* **The Nekrashevych quotation.** The book was not opened in this session; the quoted sentence of
  §3.1 is recorded as the thread cited it, and the generation-preservation statement it supports was
  re-derived independently.
* **The invariant `B_n/A_n = b·2^{2α−2}`.** It failed re-verification; see correction 1. The verified
  value `b·2^α·μ^{−3}` is recorded instead, with the supporting computation.
* **The literal phrase "p-adic pants decomposition".** Not found.
* **Any p-adic multiboundary / multi-funnel wormhole construction.** Not found.
* **The funnel count `w(q−1)`.** Stated in no source; it is the analysing agent's inference.
* **Tate's theorem from Tate's original paper.** The statement was verified in the standard
  Schottky/Mumford-curve notes read locally, not in Tate's own paper.
* **`CONSOLIDATED.py`'s isotropic formula.** Its own printed expression fails its own check; the
  verified coefficients come from `CMFINAL.py` and from the hand derivation in §4.2. The
  forward-invariance of the isotropic manifold (as opposed to the exact coefficients) is unaffected,
  since the right-hand side depends on the generation alone.
* **The all-degree / all-`N` absence of invariants for the ring.** Proved only for the degrees and
  `N` tabulated in §5.4; the extension to every degree is the analysing agent's **conjecture**, not a
  computation. **[inference]**
* **A general Lax pair for the ring.** Neither exhibited nor ruled out; only polynomial Lax
  invariants up to degree 9 are obstructed (§5.7).
* **A nonlinear equivalence to an integrable lattice.** Only linear (and diagonal) changes of
  variables are excluded (§5.6); a general invertible transformation is not.
* **The §5 integrability scripts are outside this repository** (`/tmp/ring_invariants/`) and will
  not survive it; they are named only so the computation is findable while the scratch lasts. The
  ring's negative results rest on the modular full-rank certificate together with the `sympy`
  over-`ℚ` cross-check, and the engine was validated against known invariants (§5.3).
