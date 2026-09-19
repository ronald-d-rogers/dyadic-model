# The zeta question: can a p-adic dynamical zeta carry the cascade's critical exponent?

**One page of orientation.** This is the written record of the second half of the thread whose first half
is `Cascade/CLOSURE.md`. That file asked how the dyadic cascade closes and what its geometry is; this one
asks whether a **zeta function** attached to the cascade's tree can carry the cascade's critical
exponent. It can, the question turned out, be *answered*, and the answer is no — with a mechanism,
not just a failure to find one.

The result, up front:

* The Artin–Mazur zeta of the full `p`-adic shift is `ζ_σ(T) = 1/(1 − pT)`. It has one pole, no zeros,
  and its entire content is the branching number `p = N_*`. **[proved — exact computation]**
* A **single** Ruelle zeta of the same full shift is a function of `Σ_a w_a` alone, and collapses to
  `1/(1 − T)` for a normalised cascade. It cannot distinguish two multiplier vectors with the same sum.
  **[proved — exact computation]** A one-parameter *family* of such zetas can, and does — it carries the
  **intermittency dimension**, which is a different exponent. **[derived]**
* The critical exponent is `α̃ = ½ log₂ N_*`. Recovering it from the zeta needs exactly **one** external
  ingredient, the factor `½`; `N_* = p` is a definition, not an input. **[derived]**
* **The one escape route in the earlier working notes does not exist.** Those notes hoped for a
  "self-dual functional equation with symmetry axis exactly `α̃`". Such an equation *does* exist — it
  always does, for a rank-one zeta — and its axis is the **pole radius** `1/p`, so it is forced by the
  pole and can select nothing. Detecting this required separating the *inversion* form of a functional
  equation from the *scaling* form; conflating them is what made the notes say, wrongly, that no
  functional equation exists. **[proved — exact computation, §4]**
* The dissipation exponent `β` of a p-adic cascade is an **input** in every source read. In this
  repository, read against the theorems rather than the docstrings, **four** different exponents occur
  — `1` (per-shell comparison critical), `2` (quadratic domination threshold), `2` (covariance with the
  prescribed viscosity law) and `0` (preservation of the periodic self-similar ansatz) — and they do
  not converge. Selection, where it exists, is by an imposed requirement, not by the dynamics; the
  zeta's `β` is downstream of that choice. **[proved] + [sourced]**
* **The renormalisation route was attempted and fails** (§6). The tree's isotropic profile
  `X_n = σ(t)2^{−αn}` reduces the **bulk recursion** — the translation-invariant part of the model,
  away from the root — to the marginal coefficient `4^α − N_*`, vanishing exactly at `α̃`. But the root
  has no father, so the profile is **not** a solution of the unforced rooted model; an earlier claim in
  this very file that it "reduces the whole tree" is **withdrawn** (§6.3b′). The Jiang–Wu exponent
  `d = log_p(Σ_a w_a)` lives in the **space/digit** direction and is independent of `α`; `α̃` lives in
  the **level/time** direction. Different objects, so the bridge stays empty.
  **[proved — exact computation] + [inference]**

**Nothing here is a discovery.** What the thread produced is a *verified negative* with its mechanisms,
one small checkable lemma about rank-one zeta functions (§4), one hope removed, and — on the
renormalisation attempt — one of this document's own claims **withdrawn after checking** (§6.3b′). Read
this beside `OUTCOME.md` and `CLOSURE.md`: the exercise's answer is negative and this document exists so
the reasoning, and its corrections, are on the record rather than only in a `/tmp` directory.

## How to read the labels

| label | means |
|---|---|
| **[proved]** | machine-checked in the named Lean file; the theorem name is given. |
| **[proved — exact computation]** | established by exact rational arithmetic in `Cascade/zeta_checks.py` (no floating point) or in the enumerated cases stated. Exact, bounded by the stated `p` and degree, and **not** Lean-checked unless a Lean name is also given. |
| **[sourced — …]** | quoted from the named source, with the location in that source. |
| **[derived]** | follows by elementary algebra or a short argument from a [proved] or [sourced] statement; the step is written out where it is not immediate. |
| **[measured — script]** | a numerical check in a script, named; floating-point. **Not a proof.** |
| **[inference]** | the reading of the analysing agent, stated in no source. |
| **[not found]** | the corpus was read and no source was found for the claim. |

The companion script is `Cascade/zeta_checks.py` — standard library only, deterministic, **in this
repository**, exit status 0 iff every check reproduces. The Lean library is `PAdicZeta/`.

---

## 1. The claim under test, and one correction about the model

The cascade is the dyadic tree model of Barbato–Bianchi–Flandoli–Morandin, *A dyadic model on a tree*,
[arXiv:1207.2846](https://arxiv.org/abs/1207.2846). Their notation, verbatim:

* the tree has a constant number of branches per node, `♯O_j =: N_*` for all `j`;
* `α̃ := ½ log₂ N_*`, so that `N_* = 2^{2α̃}` — **this is a definition in their §2, not a threshold**;
* the threshold is `α > α̃` (equivalently `N_* < 2^{2α}`, their Remark 2), and the dissipation exponent
  is then a *difference*, `β = α − α̃` (their Prop. 4.1);
* Theorem 2.1: for `α > α̃` and `f = ν = 0`, every positive `ℓ²` solution obeys `E(t) < C/t²`.

**[sourced — arXiv:1207.2846 §2, Prop. 4.1, Thm 2.1, Remark 2; all checked verbatim]**

**Correction 1 to the thread's own framing: Barbato's tree is not p-adic.** The full text *and* the
arXiv LaTeX source contain **zero** occurrences of "p-adic", "ultrametric", "non-Archimedean", "ball",
"zeta", and "Kozyrev". It is a purely combinatorial dyadic/`N_*`-ary tree with Euclidean cube supports.
So the p-adic tree of §2 below is a *different object with the same branching combinatorics*, and any
transfer of a threshold from one to the other is a transfer, not a citation. **[sourced — verified in
both the HTML and the LaTeX source]**

The question this document answers is then: *the branching number is the only thing the tree contributes
to `α̃` that a zeta could plausibly see. Does it?*

---

## 2. The zeta, computed

### 2.1 Artin–Mazur zeta of the full shift

Model the `p`-adic integer tree symbolically: a point is a digit string `x : ℕ → Fin p`, and the shift is
`(σ x) n = x (n + 1)`. Fixed points of `σⁿ` are exactly the `n`-periodic strings, one per level-`n` ball:

```
#Fix(σⁿ) = pⁿ ,        #(Fix(σ^m) ∩ Fix(σ^n)) = p^{gcd(m,n)} .
```

**[proved — exact computation, `zeta_checks.py` section A for `p ∈ {2,3,5,7}`; `PAdicZeta.card_fixed_shift`
in `PAdicZeta/Shift.lean`, all 17 theorems of the library axiom-clean]** and the sharper intersection
count `#(Fix(σ^m) ∩ Fix(σ^n)) = p^{gcd(m,n)}`, which says the Artin–Mazur data is *exactly* the level
structure. That second form came from the verification pass and is checked directly in section H, by
enumerating the fixed sets as periodic digit strings and intersecting them, for `p ∈ {2,3,5}`,
`m, n ≤ 7`. **[proved — exact computation, `zeta_checks.py` section H]**

**The formalisation caught a false statement, and only the axiom audit caught it.** An earlier attempt
stated `card_fixed_shift` with *no* hypothesis on `n`. That is **false** at `n = 0` for `p ≥ 2`: the
`0`-th iterate is the identity, every digit string is fixed, and there are infinitely many of them
(`Nat.card = 0`), while `p ^ 0 = 1`. The "proof" passed elaboration by routing through
`Nat.card_eq_fintype_card`, and Lean silently substituted `sorryAx`; there was no error message. The
statement is now `0 < n`, and the module docstring records why. **A build with no `error:` line is not
evidence that a theorem is true.** **[proved — `PAdicZeta/Shift.lean`, and the audit at the end of
that file]**

Artin–Mazur, `ζ_f(T) = exp(Σ_{n≥1} #Fix(fⁿ) Tⁿ/n)`, then gives

```
ζ_σ(T) = exp( Σ_{n≥1} (pT)ⁿ/n ) = 1/(1 − pT) .
```

Consequences, each checked: one simple pole at `T = 1/p` and none elsewhere; **no zeros** in `ℂ` or
`ℂ_p`; `1/ζ_σ(T) = 1 − pT`, whose coefficient sequence is `(1, −p, 0, 0, …)` — a single piece of data;
`h_top = log p`, so the pole radius is `e^{−h_top} = 1/p`. **[proved — exact computation,
`zeta_checks.py` sections A and B, series to degree 14 for `p ∈ {2,3,5,7}`]**

### 2.2 The weighted Ruelle zeta of the cascade transfer operator

With potential `φ(x) = log w_{a₀(x)}` and `S_nφ` its Birkhoff sum, the `pⁿ` periodic words factor:

```
Σ_{x ∈ Fix(σⁿ)} e^{S_nφ(x)} = (Σ_a w_a)ⁿ ,       ζ_φ(T) = 1/(1 − (Σ_a w_a)T) .
```

**[proved — `PAdicZeta.sum_prod_eq_pow_sum` in `PAdicZeta/Ruelle.lean`; exact computation,
`zeta_checks.py` section C]** For a normalised cascade `Σ_a w_a = 1` this collapses to `1/(1 − T)`. On
the level-1 space the transfer operator is rank one — the matrix with the row `w` repeated on every
row — so its spectrum is `{Σ_a w_a, 0, …, 0}` and `det(I − TL) = 1 − (Σ_a w_a)T`. **[proved — the
Perron eigenvector `M *ᵥ 1 = (Σ_a w_a) • 1` is `PAdicZeta.rankOne_mulVec_one`; the determinant itself
is not a Lean theorem, it is [proved — exact computation, `zeta_checks.py` section D] for
`p ∈ {2,3,4,5}`]**

**Correction 2 to the thread's framing — the scope of this.** An earlier draft said "the Ruelle zeta
sees neither `α` nor the individual weights `w_a`, only their sum". That is true of the **single
function** `ζ_φ` and **false** of the one-parameter family defined in §2.3 below, whose pole locus
`T_q = 1/Σ_a w_a^q` recovers the individual weights. The correct statement is: *a single Ruelle zeta of
the full shift is a function of `Σ_a w_a` alone; the individual weights are recovered from the family.*
The verification pass caught this, and it is worth stating because the original notes asserted both
things in different sections. **[sourced — adversarial verification report, overstatement O2]**

### 2.3 The `q`-deformed family, and what it does carry

The family `ζ_{qφ}(T) = 1/(1 − (Σ_a w_a^q)T)` has poles at `T_q = 1/Σ_a w_a^q`, so

```
log_ℓ(1/T_q) − q = log_ℓ Σ_a w_a^q = τ(q) ,        −τ'(1) = 1 − E[W log_ℓ W] = H(p)/log ℓ .
```

Here `τ` is Heurteaux's structure function, `τ(q) = log_ℓ E[W^q] − (q − 1)` (his eq. (9)), and the
last quantity is the **intermittency dimension** `D`. **[derived — Heurteaux, *An introduction to
Mandelbrot cascades*, [arXiv:1408.6944](https://arxiv.org/abs/1408.6944), Thm 3.2, Thm 4.1, eq. (9),
Remark 10, all checked verbatim; [measured — script] for the numerics]**

So a zeta-theoretic carrier of a cascade exponent **does** exist. It carries `D`, the intermittency
dimension, which is a statement about the *weights* `w_a`; it does not carry `α̃`, which is a statement
about *time-scale growth*. These are different exponents and the distinction is the whole point.
**[inference]**

### 2.4 `E[W log W] = log ℓ − H(p)`, the Kahane/KP criterion, is blind to `α`

For weights `p_i ≥ 0` with `Σ p_i = 1` and `W = ℓ p_I`:

```
E[W log W] = log ℓ − H(p) ≤ log ℓ ,   with equality iff the mass is a point mass.
```

**[proved — `PAdicZeta.sum_mul_log_le_log` and `PAdicZeta.sum_mul_log_eq_log_iff` in
`PAdicZeta/Kahane.lean`; [measured — script, `zeta_checks.py` section F, 2000 random weight vectors to
`4.4e−16`]** The criterion `E[W log W] < log ℓ` is therefore satisfied identically in `α` and can
never reproduce `α̃` except by a coincidence of definitions. **[derived]**

---

## 3. What is recoverable, and what is not

The four candidate carriers all reduce to one number:

```
zeta data:    T_★ = 1/p ,   h_top = log p ,   1/ζ(T) = 1 − pT ,   #(finite zeros) = 0
model:        α̃ = ½ log₂ N_* ,   N_* = p
combining:    α̃ = h_top/(2 ln 2) = ½ log₂(1/T_★) .
```

**The pole radius carries `p = N_*` and nothing more; the zeros carry nothing (there are none).** To get
`α̃` from `h_top` one must supply the factor `½`.

**Correction 3 — the count of external inputs is one, not two.** An earlier draft said "two external
inputs, `N_* = p` and the factor `½`". `N_* = p` is a *definition* (§1 above); the only genuinely
external ingredient is the factor `½` — equivalently, that the threshold is `½ log₂ N_*` rather than
`log₂ N_*`. **[sourced — verification report, overstatement O3]**

**Correction 4 — the Ruelle-pole normalisation is vacuous as stated.** One can declare "criticality =
the Ruelle zeta has a pole at `T = 1`", which by §2.2 reads `Σ_a w_a = 1`, i.e. `p·λ(α) = 1` for a
level weight `λ(α)`. With `λ = 2^{−α}` this gives `α* = log₂ p`, whereas `α̃ = ½ log₂ p`; matching `α̃`
needs `λ = 2^{−2α}`. But that is the *same* family reparametrised by `α ↦ 2α`, not an independent act —
and the weight the model actually induces (`c_j = 2^{α|j|}` with constant `N_*`, hence
`w_a = c_a/Σ_b c_b = 1/p`) is **independent of `α`**, so the criterion contains no `α` at all. The
honest statement is plainer and stronger than "the `½` was inserted by hand": *the normalisation
condition is a normalisation condition.* **[sourced — verification report, overstatement O4;
[derived] from arXiv:1207.2846 §1–2]**

---

## 4. The functional equation: the one escape route, closed

The earlier working notes named a single non-trivial possibility and declined to pursue it:

> "This is a *framing*, not an independent encoding, unless a self-dual functional equation
> `ζ_{φ_α}(1/(cT)) = χ_α(T) ζ_{φ_α}(T)` with symmetry axis exactly `α̃` can be exhibited — I see no
> reason to expect one."

**That hope can now be removed, and the removal is a small theorem about rank-one zetas.** For
`ζ(T) = 1/(1 − λT)` and `χ(T) = κ T^m`, the equation `ζ(c/T) = χ(T) ζ(T)` cross-multiplies to
`T(1 − λT) = κ T^m (T − λc)`, a degree count that has exactly one solution:

```
ζ(1/(λ²T)) = −λT · ζ(T) ,        i.e.  κ = −λ ,  m = 1 ,  c = 1/λ² .
```

The constant `c = λ` — the one the earlier notes tested — does **not** work:
`ζ(λ/T)/ζ(T) = T(1 − λT)/(T − λ)` depends on `T`. **[proved — `PAdicZeta.rankOne_functionalEquation`
in `PAdicZeta/Ruelle.lean` for the existence half; exact computation in `zeta_checks.py` section E for
the uniqueness among monomials `χ(T) = κT^m`, for `λ ∈ {2,3,5,7,11}`]**

Three consequences, in order of importance:

1. **The symmetry axis is `|T| = 1/λ`, which is exactly the pole radius.** So the pole determines the
   axis and not the reverse: the functional equation is *forced by* the zeta's single datum. For the
   cascade, `c = 1/p²` and the axis is `1/p = e^{−h_top}`. Reading `α̃` off it still requires the factor
   `½`, exactly as in §3. The escape route is closed. **[derived]**
2. **For a rank-one zeta the functional equation always exists**, for every `λ`. A symmetry that can be
   satisfied by every member of a family cannot select anything within it. [derived]
3. **A genuine constraint would need rank ≥ 2.** For a finite-rank zeta `ζ(T) = ∏_i 1/(1 − λ_i T)`,
   the same computation shows that a self-dual functional equation exists exactly when the nonzero
   spectrum is invariant under `λ ↦ 1/(cλ)` — that is, when it splits into pairs with `λ_i λ_j = 1/c`.
   That is a real constraint. It is not one the full `p`-shift can meet, because the full shift's
   transfer operator is rank one (§2.2). **A proper subshift — a cascade with forbidden words — would
   have a nontrivial transition matrix and hence a possible nontrivial functional equation; the
   multiplicative `p`-adic cascade is not of that kind.** **[derived]**

**A trap worth recording, because it caught this document twice.** The *inversion* form
`ζ(c/T) = χ(T)ζ(T)` and the *scaling* form `χ(T)ζ(aT) = ζ(T)` are **different symmetries**, and the
sentences "there is no functional equation" and "the functional equation exists" were each true of one
form and false of the other. The scaling form has no nontrivial solution at all: `χ(T) = (1 − λaT)/(1 − λT)`
is a monomial only when `a = 1`. This is the same failure mode the rest of this thread has repeatedly
hit — comparing two quantities of different kinds. **[proved — exact computation, `zeta_checks.py`
section E]**

### 4.1 The table

| zeta attached to the `p`-adic tree | explicit form | what it can report |
|---|---|---|
| Artin–Mazur, full shift | `1/(1 − pT)` | `p` only |
| Ruelle, potential `log w_{a₀}`, single zeta | `1/(1 − (Σ_a w_a)T)` | `Σ_a w_a` only |
| Ruelle, `q`-deformed family | `1/(1 − (Σ_a w_a^q)T)` | the weights, hence `D = H(p)/log ℓ` |
| Artin–Mazur of a proper subshift, matrix `A` | `1/det(I − TA)` | the transition graph — and possibly a nontrivial functional equation |
| Spectral zeta of `D^β` on the unit ball, zero average | `(1 − p^{−n})p^{n−βs}/(1 − p^{n−βs})` for `D_T^β` | `β` and `p`; poles `n/β + 2πik/(β ln p)` |

For the **full** tree the transition matrix is all-ones (rank one), so the subshift row degenerates and
the extra structure disappears. **[derived]**

**Correction 5 — an attribution error, and a sharpening of the last row.** The closed form
`(1 − p^{−n})p^{n−βs}/(1 − p^{n−βs})` and the pole lattice `n/β + 2πiℤ/(β ln p)` are **verbatim** in
Chacón-Cortés–Zúñiga-Galindo, *Heat traces and spectral zeta functions for p-adic Laplacians*,
[arXiv:1511.02146](https://arxiv.org/abs/1511.02146) — but in **Example 5.1, for the Taibleson operator
`D_T^β`**, *not* in their Theorem 7.5. For the general `A_β`, Theorem 7.5(ii) gives only a simple pole
at `s = n/β` which "is not necessarily unique" (Remark 7.6), and `N(T) ∼ CT^{n/β}` is their
**Conjecture 7.7**, i.e. open. The formula is true and sourced; the theorem it was attached to is the
wrong one. **[sourced — arXiv:1511.02146 Example 5.1, Thm 7.5(ii), Remark 7.6, Conj. 7.7; the
misattribution was found by the verification pass]**

---

## 5. The two obstacles, restated — the second one is worse than it looked

**Obstacle 1 — no disorder.** The deterministic cascade has no randomness, so Kahane's non-degeneracy
criterion `E[W log W] < log ℓ` is satisfied identically in `α` (§2.4) and cannot be the mechanism. This
is not a technicality to be circumvented; it is evidence that the cascade's criticality is not a
disorder threshold, and so not the kind of thing a topological zeta would see. **[derived]**

**Obstacle 2 — the theorem excludes the shift, but for a different reason than was first recorded, and
the *mechanism* applies.** Jiang–Wu's determinant formula ([arXiv:2508.19374](https://arxiv.org/abs/2508.19374)
Thm 4.8) is stated for a **hyperbolic rational map on `ℙ¹(ℚ_p)`**. The full shift `σ` is not a rational
map, so the theorem may not be cited for it — that is the whole of the exclusion. Two reasons given in
an earlier draft were **wrong** and are corrected here:

* `σ` is **expanding**, not nonexpanding. On the ball `{a₀ = a}` it is the affine bijection
  `x ↦ (x − a)/p` with `|σ′|_p = p > 1`; what is locally constant is the *digit* function `a₀`, not `σ`.
* the denominator `1 − ((σⁿ)′)⁻¹ = 1 − pⁿ` is a `p`-adic **unit** (`|pⁿ|_p = p^{−n}`), and the geometric
  series `Σ_m p^{nm}` **converges**. There is no convergence obstruction; the earlier claim that the
  expansion fails was an arithmetic error.

And the *mechanism* of §5 — weight constant on Markov blocks, hence a finite transfer matrix — survives
the transplant, because its proof uses only a finite Markov partition into discs on which `f` is a
uniform scaling. For `σ` that partition is the `p` residue balls, explicitly. So while the **theorem**
must not be cited for `σ`, the **determinant** can be computed, and §6.3 does compute it. Jiang–Wu's
Remark 4.9 is *not* a convergence statement: it records that there is no Ruelle–Perron–Frobenius
theorem over `ℂ_p`, i.e. possibly several leading eigenvalues. **[sourced — arXiv:2508.19374 Thm 4.8,
Prop. 2.4, §4.3, §5; independent extraction from the v2 LaTeX source. The two corrections are this
document's.]**

**Also relevant, as the one place a zeta *does* encode an exponent over `ℚ_p`:** Jiang–Wu Thm 5.1,
verbatim — *"When `f` is a subhyperbolic rational map on `P¹(ℚ_p)`, and `0 < α < 1` such that
`‖p‖ = α`, then the Hausdorff dimension of `J(f)` … is of the form `log(λ)/log(α)`, where `λ` is an
algebraic number."* The mechanism is theirs: on a dynamical chart the weight is constant on each Markov
block, so `det(I − tL_β)` is the characteristic polynomial of a **finite** matrix with entries `0` or
powers of `α^β`. That is exactly the *shape* of statement one would want for a cascade — an exponent as
a log-ratio read off an operator determinant. But `f` is a rational map, not a cascade, and by
Obstacle 2 the shift is not in the theorem's scope. **[sourced — arXiv:2508.19374 §4.3, §5, Thm 5.1]**

**And a degeneracy result on the other route:** Junghun Lee, [arXiv:1505.04249](https://arxiv.org/abs/1505.04249)
Thm 1.1 — for a rational map of degree `≥ 2` over a non-Archimedean field of characteristic `0`, the
Artin–Mazur zeta is rational over `ℚ` **and all its zeros lie on the unit circle**, with closed form
`(1 − dT)⁻¹(1 − T)⁻¹ ∏_i (1 − T^{n_i q_i})^{r_i}`. So the Artin–Mazur route has no rich zero
distribution available to carry an exponent. Lee's theorem is not *vacuous* here — it is about zeros of
a numerator, and `ζ_σ`'s numerator is `1` — it is simply **inapplicable as a source of content** for
`ζ_σ`. **[sourced — arXiv:1505.04249 Thm 1.1 and the end of its proof]**

### 5.1 Is the dissipation exponent `β` selected, or an input?

**The literature answer is unambiguous: an input, everywhere.**

* The one p-adic Navier–Stokes equation on arXiv (Khrennikov–Kochubei,
  [arXiv:1808.03538](https://arxiv.org/abs/1808.03538)) has no free exponent at all. Eq. (1.1),
  verbatim: `∂u/∂t = u(D¹u) − θ(D²u)`, with `D^α` the Vladimirov operator. The exponents are
  **hard-wired at 1 and 2**; only `θ` is free. **[sourced]**
* Zubarev, [arXiv:2006.05811](https://arxiv.org/abs/2006.05811), has no `D^β` whatsoever — dissipation
  is a general kernel `ν(x,y)` — and his exponents are **fitted to reproduce the 2/3 law**: "a model
  with a quadratic term of the form (19) for `γ = 5/2` and `γ = 5/4` also has a stationary solution
  (17), which corresponds to the 2/3 law." That is fitting to a known answer, not selection.
  **[sourced]**
* In the tree literature `β` is *defined* as the difference `α − α̃` (§1). **[sourced]**
* **No source read derives `β` self-consistently**, and no source attaches a zeta function to a p-adic
  fluid or cascade equation. **[not found — 13 searches, plus full-text keyword counts of Kozyrev,
  Zubarev, Khrennikov–Kochubei, Barbato, Heurteaux: zero occurrences of "zeta".]**

**In this repository, read against the theorems and not the docstrings, four different exponents occur,
and each is the critical value of a *different imposed comparison*.**

1. **Threshold / criticality — `e = 1`.** `Cascade.bar_scale_invariant`
   (`Cascade/PerShellThreshold.lean:153`): `perShellBar ν e j = perShellBar ν e 0 ↔ e = 1` for
   `ν ≠ 0`, `j ≠ 0`, where `perShellBar ν e j = (ν/6)·2^{(e−1)j}`. Through `perShell_iff` (`:114`)
   this reads: *the transfer-versus-dissipation comparison at shell `j` is the same comparison as at
   shell 0, for every `j`, exactly when `e = 1`*. It contains no solution, no ODE, no trajectory.
   `bar_strictMono` (`:182`, `e > 1`: the bar doubles each octave, so dissipation wins at small scales
   — the Navier–Stokes picture) and `bar_strictAnti` (`:196`, `e < 1`: it falls) bracket the regimes.
   **[proved]** The docstrings' "so dissipation wins at large `j`" need an extra growth hypothesis on
   `u_{j+1}` and are heuristics (§5.2, item 4).
2. **Quadratic domination — threshold at `e = 2`.** `Cascade.dissipation_ge_of_two_le`
   (`Cascade/DissipationThreshold.lean:402`) and `Cascade.enstrophyDissipation_two_le` (`:376`) give
   `D_e ≥ D_2 ≥ H²/E` for `e ≥ 2`; conversely `Cascade.no_uniform_dissipation_domination` (`:1380`)
   exhibits, for every `e < 2` and every `c > 0`, a state with `D_e·E/H² = 2^{(e−2)k} → 0`. So
   `e ↦ D_e` is nondecreasing and the quadratic-domination threshold is exactly `e = 2` — but that is
   monotonicity of an **inequality**, i.e. a threshold, not a selection. **[proved]**
3. **Covariance — `d = 2`, and it is an equivalence of encodings, not a derivation.**
   `Cascade.boussinesq_law_forces_degree_two` (`Cascade/DissipationDegree.lean:211`) forces `d = 2`
   from covariance under the `(s,b)` scaling *with the viscosity held to the prescribed law*
   `ν ↦ ν·λ^{b−1}`. But `Cascade.velocityRHSDegree_scaling_covariant` (`:147`) states that the
   degree-`d` equation is covariant **iff** `ν ↦ ν·λ^{b+1−d}`. So the hypothesis is *exactly* the
   `d = 2` law: the theorem says two encodings of `d = 2` agree, and every degree has its own matching
   law. The one non-circular reading is the physical `b = 1`, where `λ^{b−1} = 1` and `ν` is a
   scale-independent material constant; there `Cascade.boussinesqB_forces_degree_two` (`:279`) says
   *scale-invariant `ν` plus covariance forces `d = 2`* — a genuine selection, but from two imposed
   inputs. **[proved]** + **[derived]**
4. **Ansatz preservation — `e = 0`, the opposite of physical.**
   `Cascade.viscous_periodicity_iff` (`Cascade/SelfSimilarClosure.lean:740`): `2^{eN} = 1 ↔ e = 0`
   for `N > 0`. So the periodic self-similar closure `u_k = 2^{−k}q_k`, `q_{k+N} = q_k` of
   `Cascade/CLOSURE.md` §1 is compatible with viscosity **only at `e = 0`**, and
   `Cascade.e_two_not_closed` (`:771`) records that the physical `e = 2` is precisely the case the
   reduction *rejects*. **[proved]**

**Verdict.** The four exponents are `1, 2, 2, 0` depending on which property is demanded, and they do
not converge. So the honest answer to "does the cascade select its dissipation exponent?" is:
**selection, where it exists here, is by the modeller's imposed requirement** — a covariance
convention, an ansatz, or a comparison — and never by the dynamics. In the p-adic dictionary
(`β ↔ e`) that settles the question: the zeta's `β` is downstream of the imposed choice, so the zeta
cannot be the selector. And **no unconditional selection theorem can exist**, because `e` is a
parameter of an ODE family: distinct `e` give distinct models, and singling one out requires an
externally supplied property. The theorem genuinely missing is one *deriving* the law `λ^{b−1}`
rather than positing it; none exists. **[inference]**

**One theorem of the right shape does exist**, and is worth recording because it shows the enterprise
is not hopeless in principle: `viscous_periodicity_iff` is an `⟺`-selection of an exponent by a
property (ansatz preservation) that is not a restatement of covariance. It selects `e = 0`, not
`e = 2`. A selection theorem landing on the physical exponent would need the shape "the degree-`e`
truncated model has a nonzero globally bounded-energy solution **iff** `e = e*`", with no covariance
hypothesis. **[inference]**

**A notation trap.** `Cascade/DissipationThreshold.lean`'s own prose uses `β` for Cheskidov's *inverse*
exponent (`α = 1/β`, `β ∈ (2, 5/2]` there), whereas the p-adic `D^β` has `β = e = 2α`. Same letter,
different objects: the repo's `β` is `1/α = 2/e`. The dictionary `β ↔ e` used in this subsection is a
reader's import, not something the Lean code states or tests.

### 5.2 Docstring over-claims found while checking §5.1

Recorded because this project's standard is that confident prose attached to correct code is exactly
what goes wrong. These are **prose-only** defects: the theorems are true, and the fix is editorial.
They were found by reading the statements and the key proof steps, not the docstrings.

1. **`Cascade/PerShellThreshold.lean:6–7`** says `DissipationThreshold.lean` "proves that the enstrophy
   barrier closes unconditionally iff the dissipation degree satisfies `e > 1`, is marginal at `e = 1`,
   and cannot close for `e ≤ 1`". Checked against the file: the capstone
   `truncated_unforced_enstrophy_bounded_degreeE` (`:812`) takes `he : 2 ≤ e`, and so does every other
   rate theorem in it. Neither `1 < e < 2` nor "cannot close for `e ≤ 1`" is a theorem statement, and
   the `e < 2` result, `no_uniform_dissipation_domination`, is about *quadratic domination* — its own
   docstring says that failure "does **not** by itself obstruct the enstrophy barrier".
2. **`Cascade/DissipationThreshold.lean:29–31`** (repeated as prose at `:1136–1138`) says that at
   `e = 1` the barrier "closes only under a size condition (`ν > 3√E_max`)". Checked: the string
   `3 * Real.sqrt` occurs **zero** times in the file, and no `e = 1` rate theorem exists. The tie of
   homogeneities is real and visible in `dissipation_interp_sq`, but the conditional threshold is
   unproved prose.
3. **`Cascade/DissipationDegree.lean:20, 204–210`** — "forces", "necessary", "not merely sufficient".
   True relative to the *prescribed* law; see item 3 above for why that is an equivalence of encodings.
   (The non-vacuity note at `:289–291`, "holds nowhere else", is scoped to *the law* and is correct as
   written — an earlier draft of this erratum called it false and was wrong to.)
4. **`Cascade/PerShellThreshold.lean:180–181, 194–195`** — "so dissipation wins at large `j`" / "the
   cascade runs away". `bar_strictMono` and `bar_strictAnti` prove monotonicity of the bar and nothing
   else; no growth hypothesis on `u_{j+1}` is assumed, so the dynamical reading needs a further
   argument.
5. **`Cascade/IntermittencyThreshold.lean:37–41`** identifies its `δ = n − 2` criticality with the
   per-shell `e = 1` criticality. Same *shape*, different quantities — a nonlinearity exponent against
   a pinned dissipation exponent `2`, versus transfer homogeneity `3/2` against dissipation homogeneity
   `1 + e/2`. Analogy, not theorem. The file's own honesty flags (a)–(d) are otherwise accurate.

Both §5.1 and this erratum are statements about the *current* text of those files; if they are edited,
re-read them rather than trusting this list.

---

## 6. The renormalisation attempt, and why the bridge is empty

This is a record of *attempting* the one route that would have been new mathematics rather than a
restatement: build the renormalisation transfer operator of the cascade and read the critical exponent
off its spectrum, in the shape of Jiang–Wu's `d = log λ / log α`. It fails, and §6.5 says exactly why.

### 6.1 What was to be shown

> For a p-adic/dyadic cascade, is there a renormalisation map whose transfer-operator determinant is
> finite-dimensional and whose leading eigenvalue `λ` satisfies `d = log λ / log α` for the cascade's
> critical exponent?

### 6.2 What the sources actually permit

* **Barbato defines no renormalisation operator.** Verified against the arXiv LaTeX source: the string
  "renormali" occurs **zero** times, as do any `R`, iteration map on solution space, or fixed-point
  problem. The two operators the paper *does* contain are a **lift** (Prop. 4.1, an embedding of the
  classic chain's solutions into the tree, not an endomorphism) and a **dynamical rescaling**
  `X ↦ ϑX(ϑt+τ)` used inside the proof of Thm 2.1, which rescales time and amplitude but **never
  generation**. So "the spectrum of the paper's renormalisation operator" has no referent, and the
  honest first finding of the attempt is a documented absence. **[sourced — arXiv:1207.2846 LaTeX
  source, `bozza8.tex`; zero occurrences of "renormali"]**
* **The threshold is never derived in the paper.** `α̃ := ½ log₂ N_*` is introduced as a bare definition
  ("To this end we set also…"), and `α > α̃` appears only as a *hypothesis* — in Thms 2.1, 2.3, 5.2,
  Lemma 5.3, Prop. 6.1. The paper's logical route is *transfer from the classic dyadic model* via the
  lift, not a tree computation. The one exact on-tree computation is Prop. 6.1's proof, where the
  level-`n` energy is `2^{2α̃n}f²2^{−(n+1)(4α̃+2α)/3} = C·2^{(2/3)(α̃−α)n}`, summable iff `α > α̃`.
  **[sourced]** Where the `½` enters the paper is the lift amplitude `N_*^{−(|j|+2)/2}`: **each
  generation costs `N_*^{−1/2}` in amplitude, because amplitude is quadratic in energy while the level
  count is linear.** **[sourced — Prop. 4.1 and its proof]**
* **Jiang–Wu's theorems need rationality; their mechanism does not** (§5, Obstacle 2). So there are two
  computable objects, and §6.3 computes both.

### 6.3 The two multipliers, computed

**(a) The digit/space direction — the Jiang–Wu shape.** With blocks `B_a = {a₀ = a}` and weight
`w(a)`, the transfer operator on functions constant on the blocks is the `p × p` matrix
`M_{ca} = w(a)·α^β` with `α = |p|_p = 1/p`. For the full shift it is **rank one**, so
`det(I − tM) = 1 − t·α^β Σ_a w_a` and the exponent is

```
d = log(Σ_a w_a) / log p .
```

Unit weights give `Σ_a w_a = p`, `d = 1 = dim_H ℤ_p`, which is the correct check. This is exact and
cutoff-free, and it agrees with the rank-one computation of §2.2. **[derived — exact; the matrix and
the mechanism are the extraction's, cross-checked against §2.2]**

**(b) The level/time direction — the bulk recursion.** Barbato's eq. (1)/(7) is
`dX_j/dt = c_j X_{j̄}² − Σ_{k∈𝒪_j} c_k X_j X_k` with `c_j = 2^{α|j|}` and `♯𝒪_j = b`. The isotropic
profile `X_n(t) = σ(t)·r^{−n}` with `r = 2^α` makes the generation dependence of the per-node
right-hand side cancel **at every node that has a father**:

```
at n ≥ 1:   c_n X_{n−1}² − b·c_{n+1} X_n X_{n+1} = σ² r^{−n} (r² − b)
```

**[proved — `Cascade.isotropic_reduction` in `Cascade/IsotropicReduction.lean`; also [proved — exact
computation, `zeta_checks.py` section I, 5 `(r, b)` pairs × `n = 1..8`]]** So the **bulk recursion** —
the translation-invariant part of the model, away from the root — has the generation-independent
coefficient `r² − b = 4^α − N_*`, vanishing at

```
4^α = N_*   ⟺   2^{2α} = N_*   ⟺   α = ½log₂N_* = α̃ ,
```

equivalently `Λ = r/√N_* = 2^{α−α̃} = 2^β` with `Λ = 1`. **[proved —
`Cascade.isotropic_coefficient_vanishes`, `Cascade.isotropic_multiplier`]**

**(b′) The root, where the profile FAILS — and a withdrawal.** The root has no father: `X_{0̄} ≡ f`,
and in the unforced model `f = 0`, so the root's source term is absent. There the model gives
`−bσ²`, while the bulk recursion predicts `σ²(r² − b)`; the two agree only at `r = 0`. So **the
isotropic profile is not a solution of the unforced rooted model at any `α`.** The independent check
is the energy balance, eq. (9) with `f = ν = 0`, `dℰ_n/dt = 2c₀X_{0̄}²X₀ − Π_n`: the profile violates
it by exactly `2σ³r²`, which is the term a **phantom father `X_{−1} = σr`** would contribute.
**[proved — `Cascade.isotropic_root_obstruction`; exact computation, `zeta_checks.py` section I]**

> **Withdrawal.** An earlier version of this section claimed that "the isotropic manifold reduces the
> whole tree to the single scalar ODE `σ̇ = (4^α − N_*)σ²`", and that this "reproduces Barbato's
> threshold" as a renormalisation eigenvalue. **The bulk identity is real; the reductive claim is
> wrong**, because the root breaks the translation invariance. The earlier claim rested on an
> exact-arithmetic check that had the same bug — it supplied a phantom father at `n = 0`, so it
> verified the translation-invariant recursion while the model has no source there. **The corrected
> statement is the one above: the *bulk* recursion is marginal at `α̃`; the profile is not a solution
> of the model.** In particular the "blow-up for `α > α̃`" reported below in the earlier version was
> an artefact of dropping the root, and is withdrawn with it.

**(b″) The one case that IS a solution.** In the **forced** model with `r² = b` and the alias set to
the consistent phantom value `f = σr`, both the root equation and every interior equation vanish, so
the profile is stationary. Its exponent is then the paper's stationary exponent: `r² = b` says
`log₂b = 2α`, and `(2α̃+α)/3 = (2α+α)/3 = α`. **[proved — `Cascade.isotropic_stationary_forced`]**
That is a consistency check on the identification, not a new solution: the paper's stationary profile
`X_j = f·2^{−(|j|+1)(2α̃+α)/3}` specialises to this at `4^α = b`.

**(b‴) What the phantom father *is*, and why the profile was the wrong object.** The question "what
if we just supply the father?" has a clean answer, and it turns the withdrawal into a diagnosis.

*It is not a phantom; it is the **driving**.* Three exact cases:

| forcing | is the profile a solution? |
|---|---|
| `f = 0` (unforced) | **no**, at any `α` — the root always drains |
| `f` constant | only at `r² = b`, i.e. `α = α̃`, where the profile is **stationary** |
| `f(t) = σ(t)·r` (time-dependent) | **yes, for every `α`** |

The third case is the content: with a drive that is itself self-similar, the profile is an exact
self-similar response. **[proved — exact computation; the root and interior both reduce to
`σ²(r²−b)`]**

And the root's balance `f² − b·r·X₀X₁ = σ²(r² − b)` is **the same expression as the bulk
coefficient**. So the threshold has a reading: `r² > b` means the influx from above the resolved
range exceeds the outflux to below; `r² < b` means the root drains; `r² = b` means
`r = √b = N_*^{1/2} = 2^{α̃}`. **`α̃` is a top-of-cascade flux balance, and the `½` in it is the
square root because energy is quadratic in the amplitude while the level count is linear** — the same
`½`, now at a physical balance rather than in a definition.

*But the profiles are not merely shifted copies of each other — they differ **qualitatively**.* For a
power profile `X_m = A·2^{−γm}` the flux across level `n` is

```
Π_n / A³ = 2^{ n(2α̃ + α − 3γ) + (2α̃ + α − γ) } .
```

* **Barbato's stationary profile** has `γ = (2α̃+α)/3`: the `n`-coefficient vanishes, `Π_n` is
  **constant**, and with `f = A2^{γ}` it equals the injection `f²X₀ = A³2^{−γ}` **exactly**. A steady
  drive in, a steady flux out. That is a genuine cascade, and it is the paper's *conservative* case.
* **The profile used here** has `γ = α`: then `Π_n ∝ 2^{2n(α̃−α)}`, which for `α > α̃` **vanishes as
  `n → ∞`**. It carries **no flux to infinity at all**.

So the earlier profile was **flux-free**: it has no cascade running through it, which is why it could
not balance any drive, and why the root had to invent a father. The two exponents agree only at
`α = α̃`, which is exactly where the profile became stationary and the phantom father became a
legitimate constant drive. **[proved — exact computation, `zeta_checks.py` section I]**

The flux-constancy condition `3γ = 2α̃ + α` is the same algebra as the paper's stationarity relation
`μ³ = b·2^α = 2^{2α̃+α}`. So the error was not a sign or a boundary convention: **`γ = α` is the
exponent of a flux-free profile, and `(2α̃+α)/3` is the exponent of a flux-carrying one.** The
phantom father was the symptom, not the disease.

**Drive or loop?** Both tests say **loop**, with one exception.

* *Is the forcing independent of the state, or slaved to it?* Barbato's `f` is a free constant
  parameter, and so is `A` in their stationary profile. The forcing used here is not: `f = σr = r·X₀`
  — the root's **own** amplitude, scaled by `r`. That is a feedback, not a source.
* *Does anything reach the small scales?* The energy check settles it. For the `γ = α` profile with
  `α > α̃`, the geometric sum in `dE/dt = 2σ³(r²−b)Σ_n(b/r²)^n` collapses because
  `(1 − b/r²) = (r²−b)/r²`, giving

  ```
  dE/dt = 2σ³r² = the injection f²X₀ (doubled) ,   with flux to infinity = 0 .
  ```

  **Every drop that comes in stays in the profile.** A drive drives something *through*; a loop only
  inflates. **[proved — exact computation]**

So the trichotomy is: for `α < α̃` the profile is not `ℓ²` at all; for `α > α̃` it is a boundary
self-reference (`f = rX₀`) with no flux through it; and at `α = α̃`, where `σ` is constant, the
self-reference degenerates into a genuine constant forcing — Barbato's stationary state. The
"self-similar drive" described *how it scaled*; the loop is *what it was*. They looked alike because
only the scaling was checked.

**Where the rigidity actually sits — the drive is free, the *shape* is not.** `f` in Barbato's model
is a free input; nothing requires it to be self-referential. What is forced is the decay rate, and
there are exactly two forcing power-law shapes:

| demand | decay rate `γ` in `X_n = A·2^{−γn}` | the drive `f` |
|---|---|---|
| time-dependent amplitude `A(t)` | **`γ = α`** forced | **forced**: `f = ±A·2^α` — the loop |
| stationary (`A` constant) | **`γ = (2α̃+α)/3`** forced | **free** — any `f > 0` |

The two forced exponents coincide exactly at `α = α̃`. **[proved — exact exponent arithmetic,
`zeta_checks.py` section I″]** So **the loop was a consequence of the ansatz, not a fact about
cascades**: I demanded a pure power law with a time-dependent amplitude, that shape is rigid at
`γ = α`, and at that exponent the interior closes on itself, leaving the self-reference as the only
drive consistent with the root. The self-reference was downstream of the shape choice.

**A genuinely external drive requires the stationary shape.** There `f` is free, a larger drive gives
a proportionally larger state with the *same* shape, and the flux scales as `f³`. (This is scoped to
pure power laws: the model's other exact solutions, the lifted self-similar ones
`X_j = a_j/(t−t₀)`, are unforced and not power laws.) **[proved — exact computation]**

**The non-locality, which is the real content of the "drive from outside" question.** For a *steady*
state the drive must equal the flux escaping to infinity, `f²X₀ = lim_n Π_n`. That is a **global**
condition: the required drive depends on the *tail* of the profile, not on anything local — the
boundary condition "knows about" the far end. And energy leaves the resolved range through that
channel **with no viscous mechanism at all**: that is *anomalous dissipation*, the phenomenon
Barbato's Theorem 2.1 is about and the dyadic model's whole point as a caricature of turbulence.
`α̃` is exactly where the channel opens — above it a steady state can carry flux to infinity, below it
cannot. **[derived; Thm 2.1 sourced]**

**Not to be confused with the ring.** The dyad ring was a loop in the **index** (`k ≡ k + N`), a
genuinely closed chain — a topological circle. This is a loop in the **signal** (the root's parent set
to the root's own value times `r`), a self-reference at the boundary. Different objects that would
both be called "a loop".[^loop]

**The drive is a one-defect absorber, not a universal adapter.** A natural follow-up is whether, `f`
being free, *any* profile can be hitched to the model by choosing the drive. It cannot, and the reason
is structural. The drive appears in **exactly one equation**:

```
root     :  Ẋ_0 = f² − b·2^α·X_0X_1                     ← the only place f appears
interior :  Ẋ_n = 2^{αn}X_{n−1}² − b·2^{α(n+1)}X_nX_{n+1}     (n ≥ 1)
```

so `Ẋ = F(X) + f²·e_0`: one scalar control, one direction. A candidate trajectory is realizable for
*some* drive iff its **interior residual** vanishes,

```
R_n := Ẋ_n − [2^{αn}X_{n−1}² − b·2^{α(n+1)}X_nX_{n+1}] = 0   for all n ≥ 1 ,
```

and then the drive is not free but *determined*: `f² = Ẋ_0 + b·2^α·X_0X_1`. **The body must already
solve the undriven interior; the drive can repair the root and nothing else.** **[proved — exact
computation, `zeta_checks.py` section I‴; [inference] for the framing]**

And the body is rigid in a strong sense. Putting `s_n := X_n/X_{n−1}`, the stationary interior
condition collapses to a one-dimensional recursion

```
s_{n+1} = 1 / (b·2^α·s_n²) ,
```

whose fixed point is `s³ = 1/(b·2^α)`, i.e. `s = 2^{−γ_stat}` with `γ_stat = (2α̃+α)/3` — Barbato's
exponent again. Its multiplier is

```
f′(s) = −2/(b·2^α·s³) = −2 .
```

**The power law is a repeller.** Any deviation *doubles and flips* each generation: a relative error
of `1e−6` becomes `1e−3` in ten levels, then runs away. So the bounded stationary interior is a
measure-zero set, literally one shape — which is *why* Barbato's uniqueness theorem (Thm 2.3: unique
`ℓ²` positive stationary solution for given `f > 0`) holds, and not merely *that* it does.
**[proved — exact computation, `zeta_checks.py` section I‴]**

So what a free drive buys is the **amplitude** of the one admissible shape, not the shape. "The input
is right" does not mean "anything hangs off it": the input is the single free number setting how large
the already-rigid cascade is.

[^loop]: The distinction is the same one §5.2 draws for "torus", and it is the third time in this
thread that two different things have shared a symbol or a word.

*What this does not buy.* The drive was reverse-engineered (`f(t) = σ(t)r` is chosen to make the
profile exact), so this **interprets** `α̃` rather than deriving it. What it does give is the correct
statement of what `α̃` demarcates: a driven cascade whose top-scale input balances its drain. Barbato's
`α > α̃ ⟹` anomalous dissipation is then the statement that above threshold the cascade can carry a
steady flux out of the resolved range. **[inference]**

*A numerics note, recorded because it failed.* An attempt to check numerically whether the driven
flow relaxes to Barbato's stationary profile from the flux-free one was **abandoned**: every top
boundary tried (Dirichlet, then a ratio-preserving ghost) destabilised the box, to the point that
**the paper's own stationary profile "blew up" instantly** in it. That is a defect of the box, not a
finding about the model, and no numerical claim is made here. The exact algebra above is the evidence.

### 6.4 The `½`, and what is left of it

`4^α = (2^α)²`, and the square reflects that the model is **quadratic in the amplitude** while the
level count enters **linearly** — the same reason the paper's own lift carries `N_*^{−|j|/2}`.
**[sourced — arXiv:1207.2846 Prop. 4.1 and its proof]** With §6.3b′ in hand this cannot be presented
as *this document's* explanation of the `½`: the paper's lift already contains it, and the bulk
reduction adds no independent measurement. What survives is only that the `½` is not mysterious — it
is the reciprocal of the homogeneity degree of the nonlinearity.

### 6.5 Why the bridge is nonetheless empty

The two multipliers are **different objects, in different directions, built from different data**:

| | built from | direction | depends on `α`? |
|---|---|---|---|
| `d = log_p(Σ_a w_a)` | the branch **weights** `w_a` | space / digit | no |
| `r² − N_*`, marginal at `α̃` | the time-scale exponent **`α`** and the branching | level / time | yes |

And with §6.3b′ the second row is weaker than it first appeared: it is the marginality of the
**bulk recursion**, and since `α̃ := ½log₂N_*` is a definition, reading `α̃` off `4^α = N_*` is close
to reading it off `N_* = 2^{2α̃}` — a restatement, not a derivation. What is *not* a restatement is the
direction: the zeta exponent `d` is a **Hausdorff dimension of the tree boundary** (for uniform
weights, `1`, whatever `α` is), while `α̃` is a **time-scale** threshold. **The cascade's `α̃` is not a
Jiang–Wu dimension of the tree, and no zeta of the tree encodes it.** This is the same failure mode
this thread has hit repeatedly: two quantities of different kinds compared because they share a
symbol. **[inference]**

### 6.6 A correction to `CLOSURE.md` §4.3

§4.3 analyses the **constant** mode `R_n ≡ c` of the isotropic chain and reports
`K = A_n − B_n = 2^αμ(1 − b·2^αμ^{−3})`, concluding that "blow-up would require `K > 0`, i.e.
`μ³ > b·2^α`; no computed case satisfies this".

* **The gauge criticism stands.** `μ` is the parameter of the ansatz `X_j = μ^{−|j|}R_{|j|}`, chosen
  by the analyst, and it cancels from physical quantities. A criterion containing `μ` is therefore
  not a property of the model, and `ρ = 1` is not the self-similar mode.
* **The replacement first offered here is withdrawn.** It asserted the gauge-invariant criterion is
  `σ̇ = (4^α − N_*)σ²` with criticality `α = α̃`. Per §6.3b′ that is the **bulk** recursion, not the
  model, so it does not supply the criterion §4.3 lacked either.
* **What should be said instead:** the unforced rooted model has no isotropic solution of this shape
  at all (the root obstruction, §6.3b′), so *no* criterion of the form "the isotropic mode blows up
  iff …" is available. Barbato's own threshold is reached differently — through the stationary
  profile and its ℓ² condition, `α > α̃` (Prop. 6.1) — and that is where the record should point.

**[proved — exact computation; this document's correction, itself corrected]**

### 6.7 Verdict on the attempt

* A finite-dimensional, cutoff-free transfer operator exists in the **digit** direction; its
  determinant is rank one and its exponent `log_p(Σ_a w_a)` says nothing about `α` (§6.3a).
* The cascade's **bulk** recursion has the marginal coefficient `4^α − N_*`, vanishing exactly at
  Barbato's `α̃` — but the isotropic profile is not a solution of the unforced rooted model, so this
  is a statement about the translation-invariant part only (§6.3b′, withdrawal).
* The two directions are independent, so the bridge stays empty (§6.5).
* Gained, and it is little: the Jiang–Wu exclusion is narrowed to its true reason (rationality, not
  convergence — §5, Obstacle 2); `CLOSURE.md` §4.3's criterion is shown to be gauge-dependent and its
  mode wrong (§6.6); and one over-claim of this document's own is withdrawn (§6.3b′).

**Status of the attempt: negative.** The first version of this section reported "negative, with a
positive by-product"; the by-product did not survive checking. **[inference]**

---

## 7. What is *not* claimed

The negative is narrow and should be quoted narrowly:

* **Earned:** a **single** Artin–Mazur/Ruelle zeta of the **full** `p`-shift carries exactly one number,
  `p = N_*`, and therefore cannot encode `α̃ = ½ log₂ N_*`. **[proved — exact computation]**
* **Not earned:** "no zeta-theoretic object carries cascade data." That is false, and §2.3 is the
  counterexample: the `q`-deformed family carries the intermittency dimension `D = H(p)/log ℓ`.
  **[derived]** Earlier working notes asserted the wide version in one section and demonstrated the
  narrow one in another; the narrow one is what the computations support.
* **Not claimed:** that the Artin–Mazur zeta is ill-defined or "not canonical". §1.2 of the earlier
  notes compared three maps and found three zetas, one of them identically `1`; that shows the invariant
  is **coarse** (non-injective — the shift `σ` is a bijection and `x ↦ x^p` is not, yet both have `pⁿ`
  fixed points and hence the same zeta), which is a general and well-known fact. It does not show the
  zeta is not well-defined. **[sourced — verification report, overstatement O1]**
* **Not claimed:** that the spectral-zeta pole lattice has been computed for an *interacting* cascade.
  Nobody has done that, and the free-Laplacian lattice will move under a nonlinear advection term.
  Matching the free lattice against log-periodic intermittency data would be evidence of the weakest
  kind, and is *not* done here. **[inference]**

---

## 8. Verdict

* The Artin–Mazur zeta of the full `p`-adic shift is `1/(1 − pT)`: one pole, no zeros, content `= p`.
  **[proved — exact computation, and `PAdicZeta/`]**
* A single Ruelle zeta of the full shift is `1/(1 − (Σ_a w_a)T)`, hence `1/(1 − T)` when normalised: it
  is blind to the individual weights, but the `q`-family is not, and carries `D`. **[proved — exact
  computation]**
* `α̃` is recoverable from the zeta only by supplying **one** external ingredient, the factor `½`;
  `N_* = p` is a definition. **[derived]**
* **The functional equation exists, is unique, and is forced by the pole**: `ζ(1/(p²T)) = −pT·ζ(T)`,
  axis `= 1/p =` the pole radius. A genuine self-duality constraint would require rank `≥ 2`, i.e. a
  proper subshift, which the full cascade is not. **[proved — exact computation]**
* The non-Archimedean Ruelle theory of Jiang–Wu **does not apply** to the shift (nonexpanding), which
  removes the last route that might have given the rank-one determinant an independent meaning.
  **[sourced]**
* `β` is an input in every source read. Here, four exponents `{1, 2, 2, 0}` arise from four different
  imposed requirements and do not converge; the one `⟺`-selection theorem that exists
  (`Cascade.viscous_periodicity_iff`) selects `e = 0`, the opposite of physical. **[sourced] +
  [proved]**
* **Status: negative, and a record rather than a discovery** — except for one small lemma about
  rank-one zeta functions (§4), which is new here and checkable in five lines.

---

## Corrections to the thread's own record

The original computation was a scratch report written to `/tmp` and never landed. An adversarial
verification pass and a source-scoping pass were run against it before this document was written. The
verification pass also **corrected one of its own attempted refutations** mid-flight (a p-adic
arithmetic harness that reduced numerator and denominator separately, invalid when the denominator has
`p`-adic absolute value `> 1`); the final version of its findings is what is recorded here. The list:

1. **The functional equation.** The scratch report said "there is no functional equation". False in the
   *inversion* form, true in the *scaling* form, and the two were conflated. Corrected in §4, with the
   sharpened consequence (the FE is forced by the pole). **This correction is this document's, not the
   verification pass's** — the pass independently proposed the scaling-form statement, which is
   consistent.
2. **Attribution.** The `(1 − p^{−n})p^{n−βs}/(1 − p^{n−βs})` formula and its pole lattice belong to
   **Example 5.1** of arXiv:1511.02146 (Taibleson operator `D_T^β`), not to Theorem 7.5.
3. **"Sees only `Σ_a w_a`".** Overstated; narrow to a *single* zeta of the *full* shift.
4. **"Not canonical".** Unsupported; the right word is **coarse**.
5. **Numerical mislabels.** `H(p) = 0.610864` **nats** `= 0.881291` **bits**; the string `0.8814` is the
   intermittency dimension `D`, not `H` or `E[W log₂ W]`; exact `E[W log₂ W] = 0.118709`, and the
   report's `0.1186` was a rounding slip in the last digit.
6. **External inputs: one, not two.** `N_* = p` is a definition.
7. **Barbato's tree is not p-adic** — zero occurrences in the full text and the LaTeX source.
8. **"Lee's theorem is vacuous".** Inapplicable as a source of content, not vacuous.
9. **The Jiang–Wu determinant** was quoted without its hyperbolicity hypothesis, its `J(f)`
   restriction, and its `1 − ((fⁿ)′)⁻¹` denominator; with the denominator restored the theorem
   *excludes* the shift. This correction strengthens the negative.
10. **Obstacle 2 was wrong on two counts, and is rewritten in §5.** The shift is **expanding**
    (`|σ′|_p = p > 1` on each residue ball), and the geometric series with ratio `p^{−n}` **converges**,
    with `1 − pⁿ` a `p`-adic unit. The theorem excludes the shift because `σ` is not a *rational* map —
    that, and only that. The *mechanism* does apply, and §6.3a uses it. The error came from an
    independent verification pass that this document had relied on; the relayed claim was not re-derived
    before being written down, which is precisely the discipline this file exists to enforce.
11. **`CLOSURE.md` §4.3 analysed the wrong mode and used a gauge-dependent criterion.** Its `K`
    contains the free ansatz parameter `μ`, which cancels from physical quantities, so `μ³ > b·2^α` is
    not a property of the model and `ρ = 1` is not the self-similar mode (§6.6).
12. **And then this document's own replacement was withdrawn.** Having (correctly) criticised §4.3,
    this file first proposed the gauge-invariant criterion `σ̇ = (4^α − N_*)σ²` and claimed it
    "reproduces Barbato's threshold". **False**: that identity holds at nodes that have a father, and
    the root has none, so the profile is not a solution of the unforced rooted model; the energy
    balance is violated by exactly the phantom-father term `2σ³r²` (§6.3b′). The check that had
    "verified" the claim contained the same bug — it supplied a phantom father at `n = 0`. `ZETA.md`
    §6.3b/§6.4/§6.6/§6.7, `CLOSURE.md`'s corrigendum, `Cascade/IsotropicReduction.lean` and
    `zeta_checks.py` section I are all corrected, and the withdrawn claim is marked as such rather
    than deleted. **This is the third time in this thread that a claim of this document's own has had
    to be retracted, and the second time the retraction was found by checking a *consequence* rather
    than the claim itself** — the energy balance, not the per-node identity.

---

## Sources

| source | relied on for |
|---|---|
| Barbato, Bianchi, Flandoli, Morandin, *A dyadic model on a tree*, [arXiv:1207.2846](https://arxiv.org/abs/1207.2846) | `♯O_j = N_*`; `α̃ := ½ log₂ N_*` (a definition); the threshold `α > α̃`; `β = α − α̃` (Prop. 4.1); Thm 2.1. Verified to contain **zero** occurrences of "p-adic", "ultrametric", "non-Archimedean", "ball", "zeta". |
| Heurteaux, *An introduction to Mandelbrot cascades*, [arXiv:1408.6944](https://arxiv.org/abs/1408.6944) | Kahane's criterion (Thm 3.2, `E[W log W] < log ℓ`); the structure function (eq. (9)); the `L^q` form (Thm 4.1); the Legendre relation (Thm 7.3); `dim(m) = 1 − E[W log_ℓ W]` (Remark 10). Zero occurrences of "zeta", "pole", "functional equation", "log-periodic". |
| Chacón-Cortés & Zúñiga-Galindo, *Heat traces and spectral zeta functions for p-adic Laplacians*, [arXiv:1511.02146](https://arxiv.org/abs/1511.02146) | Example 5.1 (Taibleson `D_T^β`): the closed form and the pole lattice `n/β + 2πiℤ/(β ln p)`. Thm 7.5(ii) guarantees only a simple pole at `n/β`, "not necessarily unique" (Remark 7.6); `N(T) ∼ CT^{n/β}` is Conj. 7.7, open. |
| Jiang & Wu, *Ruelle's zeta function for non-Archimedean rational maps*, [arXiv:2508.19374](https://arxiv.org/abs/2508.19374) | Def. 4.6 and Thm 4.8 (hyperbolic only, with the `1 − ((fⁿ)′)⁻¹` denominator); Remark 4.9 (no RPF over `ℂ_p`); §4.3 and Thm 5.1 (`dim_H J(f) = log λ/log α`). |
| Junghun Lee, *Artin–Mazur zeta functions of certain non-Archimedean dynamical systems*, [arXiv:1505.04249](https://arxiv.org/abs/1505.04249) | Thm 1.1 (rationality, all zeros on the unit circle) and the closed form at the end of its proof. |
| Khrennikov & Kochubei, *On the p-Adic Navier–Stokes Equation*, [arXiv:1808.03538](https://arxiv.org/abs/1808.03538) | Eq. (1.1): exponents hard-wired at 1 and 2. |
| Zubarev, *On p-adic cascade equations of hydrodynamic type*, [arXiv:2006.05811](https://arxiv.org/abs/2006.05811) | general dissipative kernel, no `D^β`; exponents fitted to the 2/3 law; §4 discrete scale invariance. |
| Kozyrev, *Towards ultrametric theory of turbulence*, [arXiv:0803.2719](https://arxiv.org/abs/0803.2719) | the ultrametric cascade equation and its wavelet eigenvalues `η_I`; zero occurrences of "zeta" or "pole". |
| Zhou & Sornette, [arXiv:cond-mat/0110436](https://arxiv.org/abs/cond-mat/0110436) | log-periodic corrections to scaling in turbulence (abstract only; no claim about its body). |

Repo-side: `Cascade/DissipationDegree.lean`, `Cascade/PerShellThreshold.lean`,
`Cascade/DissipationThreshold.lean`, `Cascade/IntermittencyThreshold.lean`.

## What could not be verified

* **Kozyrev's exact wording** for "global Cauchy solution for finite wavelet expansions". The clause is
  not load-bearing and is not used here. **[not found]** — the source itself is not in question.
* **The full text of Zúñiga-Galindo's Springer LNM volume** *Pseudodifferential Equations Over
  Non-Archimedean Spaces*. Only metadata was accessible; no claim is made about its contents.
* **Whether a *cascade* renormalisation map admits a Jiang–Wu-style Markov partition** with a
  finite-dimensional transfer-operator determinant. This is the one opening that would be new
  mathematics rather than a restatement, and it was not attempted. **[not found]**
* **The interacting spectral-zeta pole lattice** for a cascade with a nonlinear advection term.
  Uncomputed; §6 declines to match the free lattice against data.
* **Search quality.** Queries on this topic return arXiv IDs with impossible future dates and
  predatory-looking PDFs claiming Riemann-hypothesis/turbulence/p-adic unifications. None were opened
  or cited.
