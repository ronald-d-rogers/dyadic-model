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
| **[sourced — …]** | quoted from the named source, with the location in that source. |
| **[derived]** | follows by elementary algebra or a short argument from a [proved] or [sourced] statement; the step is written out where it is not immediate. |
| **[measured — script]** | a numerical check in a scratch script, named; exact-rational where said, floating-point otherwise. **Not a proof.** |
| **[inference]** | the reading of the analysing agent, stated in no source. |
| **[not found]** | we read the corpus in front of us and found no source for the claim. |

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
evaluated on a non-cyclic path, and there the sign flips to decay. Blow-up would require
`K > 0`, i.e. `μ³ > b·2^α`; no computed case satisfies this. **[derived]**

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

## 5. The corresponding geometry, and where the chain is special

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

So the statement is:

> **The chain's ring closes because degree 2 is the only degree at which one element suffices.**
> **[derived]**

This is the geometric face of the failure in §3: the algebraic obstruction (no level shift) and the
geometric one (a cyclic group is not cocompact above degree 2) are the same fact.

---

## 6. The genus-1 case, with the corrections that were needed

All of the following was checked against the sources read for this thread. The bold "corrections"
are the places where the thread's first reading was wrong and was repaired.

### 6.1 What the Tate curve is

* The Tate curve is `K*/q^ℤ`. It is the p-adic analogue of the complex torus `ℂ*/q^ℤ`, and it has
  **genus 1**. Tate's theorem: there is a surjective homomorphism `φ : K* → E_q(K)` with kernel
  `q^ℤ`. **[sourced — Tate's uniformisation as stated and proved in the Schottky/Mumford-curve notes read (Thm 0.1 and Thm 4.4, "the kernel is `q^ℤ`"); complex model `ℂ*/q^ℤ` ibid.]**
* Keep the two objects **distinguished**: the **rigid-analytic** quotient `K*/q^ℤ`, and the
  **algebraic** Weierstrass cubic `E_q` (`y² + xy = x³ + a_4(q)x + a_6(q)`).
  **[sourced — ibid., Def. 4.2]**
* Reduction is **split multiplicative**. In the Kodaira–Néron classification, type `I_n` gives a
  special fibre that is a loop of `n` copies of `ℙ¹`, so the skeleton is a **loop**.
  **[sourced — type `I_n` loop: Berkovich-skeleton notes read, Example 9; split multiplicative: Schottky notes §5]**

### 6.2 The skeleton is the finite core, not the whole quotient

* The **skeleton** is the finite **minimal / convex-core** graph, not the full quotient.
  **[sourced — Mumford, "An analytic construction of degenerating curves over complete local rings", Compositio Math. 24 (1972) 129–174, Thms 1.23 and 3.3; Heydeman–Marcolli–Saberi–Stoica, arXiv:1605.07639 ("the quotient `T_k/Γ` consists of a finite graph `T_Γ/Γ` with infinite trees appended at the vertices"); Li–Matheus–Pan–Tao, arXiv:2412.20754 Remark 2.15 ("This skeleton `Σ_X` is the analogue of the convex core …")]**
* The two differ **exactly by the funnels** — the infinite trees appended to the finite graph — and
  the first Betti number `b₁` is the same either way, since trees are contractible.
  **[derived — deformation retract]**
* The genus of the curve is the first Betti number of the skeleton.
  **[sourced — Payne, "Tropical Brill–Noether Theory 11: Berkovich Analytification and Skeletons of Curves", Thm 11.26: `g(X) = g(Σ(X,V(X))) + Σ_{x∈V(X)} g(x)`, where `g(Σ(X,V(X)))` is the first Betti number of the skeleton]**

### 6.3 Funnels are NOT cusps, and in characteristic zero there are no cusps

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

### 6.4 The boundary: a correction

* The quotient's boundary is **`Ω_Γ/Γ`**, the Mumford curve's `K`-points — the set of ends of the
  quotient graph — **not** the limit set `Λ_Γ`. Mumford: *"C(K), the set of K-rational points of C,
  will be naturally isomorphic to the set of ends of Δ/Γ."* Heydeman–Marcolli–Saberi–Stoica write
  `X_Γ(k) = Ω_Γ(k)/Γ` for the Mumford curve. **[sourced — Mumford, Compositio Math. 24 (1972), p. 130; arXiv:1605.07639]**
* **Both are Cantor sets**, so the conclusion *"the boundary is a Cantor set, not circles"* stands —
  but the earlier **identification was wrong**. This is a correction, not a retraction.
  **[sourced for both being Cantor sets; the correction is the thread's]**

### 6.5 Consequence for any "n-boundary" reading

* There **is** a discrete count of funnels, so the statement *"the p-adic side has no discrete `n`"*
  is **too strong**. **[inference]**
* But a finite disjoint union of Cantor sets is again a Cantor set, so the funnel count is
  **invisible in the boundary's homeomorphism type**, and the funnels are not separate boundary
  components. **[derived]**
* The funnel count `w(q−1)` is **the analysing agent's inference, stated in no source**. It is
  recorded here only as such. **[inference]**

### 6.6 RT does work here

* Heydeman–Marcolli–Parikh–Saberi, arXiv:1812.04057 §5: the bulk dual of boundary entanglement is
  *"the lengths of minimal geodesics homologous to the boundary intervals in the black hole
  background, the analog of the Ryu–Takayanagi formula in this geometry"*; the geodesics wrap the
  horizon, and they verify the match numerically and prove subadditivity, strong subadditivity and
  monogamy. **[sourced — arXiv:1812.04057 §5]**
* Huang–Jepsen: entanglement on the Tate curve scales with `w`, *"which provides a compelling reason
  to associate this variable to a black hole radius."* **[sourced — arXiv:2408.04199]**
* Assembling these: the funnel width = the translation length = the thermal-cycle length = the p-adic
  analogue of a **cuff length**. **[derived — identification across arXiv:2603.26443, arXiv:2408.04199, arXiv:1812.04057]**

### 6.7 The p-adic analogue of a pair of pants

* A `ℙ¹` with three marked points. Brosnan–Fakhruddin: *"Any trivalent graph Γ with 2g−2 vertices
  gives rise to a unique totally degenerate stable curve `C_Γ` of genus g … We choose a copy of
  `P¹_k` with three marked rational points for each vertex of Γ and label the marked points with the
  edges incident on the vertex, a loop being counted twice."*
  **[sourced — Brosnan–Fakhruddin, "Fixed points, local monodromy, and incompressibility of congruence covers", JAG 1449 §4.1.3]**
* The literal phrase **"p-adic pants decomposition" was not found**.
  **[not found]**

### 6.8 Nothing builds a multi-funnel wormhole

No source read builds a p-adic multiboundary / multi-funnel wormhole. The existing p-adic holography
corpus is **single-boundary**: the genus-0 tree, the genus-1 Tate curve, and higher-genus Mumford
curves. **[not found]**

---

## 7. Verdict

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

**Status: negative, and a record rather than a discovery.** No Lean file was added for the tree or
the p-adic material; the only machine-checked content is the chain closure of
`Cascade/SelfSimilarClosure.lean`, which itself declares its blow-up a re-derivation.

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
