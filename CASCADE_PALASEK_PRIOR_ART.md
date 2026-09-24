# Prior-art check: Palasek's lacunary-cascade obstruction remark

Scope: whether the remark and its ingredients are already in the literature, to decide
whether a short negative note is worth writing. Everything below was verified by fetching
the actual sources (Mastodon API, arXiv HTML/ar5iv, seminar pages, blog archives). Where I
found nothing, I say so explicitly.

**Date correction (important).** The exchange is **2026-09-08**, not September 2025.
`Cascade/VISION.md` already has the correct 2026 date. Verified from the Mastodon API
`created_at` fields.

---

## Q1. Original source, and whether it has been written up

### (a) Answer

* **Original source located and verified verbatim.** Stan Palasek, Mastodon post
  `2026-09-08T11:51:03Z`, in reply to Tao's post `117233528517340774`.
* **The specific remark (Bernstein `N_k^{3/2}` vs. dissipation `N_k^2`, plus the
  high-dimension caveat) is, as far as I can find, NOT written up anywhere as such.**
  Critically, the paper Palasek himself links in that same post (`arXiv:2605.13827`) does
  **not** contain it: I fetched the full text and it has **zero** occurrences of
  "Bernstein", no "high dimension", and no `d/2` comparison.
* **What *is* written up** is a closely related but distinct rigorous obstruction, which
  Palasek attributes to **Looi**: the external force is necessary for viscous blow-up in
  the Obukhov model. This appears (i) as a quoted constraint in Palasek's paper, and
  (ii) as Looi's own work, which is "to appear" and **not on arXiv** — only seminar
  abstracts are public.
* **The "high dimension" escape / d = 5 threshold is documented**, but via the
  intermittency-dimension / nonlinearity-exponent route, **not** via Palasek's
  Bernstein-amplitude comparison. See Q4 and below.
* **Tao's proposed Boussinesq-dyadic exercise: nothing found.** Tao's reply has **no
  public descendants** (Mastodon `/context` returns an empty `descendants` list), and web
  searches found no paper/blog/lecture notes taking it up. The closest existing prior art
  is Mailybaev's inviscid convective-turbulence shell model (2012), which is a
  Boussinesq-type shell model but not the proposed exercise.

### (b) Evidence

Palasek's post, verbatim (Mastodon API):

> "@tao Hi Terry, I think there's a serious obstruction to removing the force from a
> Navier-Stokes blow-up (at least whenever it takes the form of a sequence of instabilities
> along a lacunary sequence of frequencies): consider the velocity u_k at frequency N_k. It
> grows at most by a factor \int_0^T \|\sum_{m<k}\nabla u_m\|_\infty dt. By Bernstein's
> inequality and energy, this is O(N_k^{3/2}). This growth is overcome by the energy
> depletion which occurs at rate ~N_k^2. (In high dimension, though, there is no
> obstruction!) This is an argument of Looi and I discussed these issues in depth here:
> https://arxiv.org/pdf/2605.13827"

Tao's reply, verbatim (Mastodon API, `2026-09-08T15:12:46Z`):

> "Ooh, that's a good observation. It might be an illustrative exercise to locate a dyadic
> model with the same scaling features as, say, Boussinesq, and see what the analogue of
> the recent blowup construction is in that model. Hopefully one can create a model in
> which the arguments become significantly shorter and more transparent since one can
> simply remove any unwanted interactions from the model rather than have to estimate
> their contribution."

Palasek, `arXiv:2605.13827` (submitted 13 May 2026; note this **predates** the Mastodon
post, so the post is pointing back at it). §1, quoting the Looi obstruction:

> "One encounters another constraint in the viscous setting which is not connected to
> energy criticality, but is nonetheless unavoidable as recently shown by Looi [16].
> Consider (4) with positive initial data. Then growth or decay of X_k(t) is governed by
> the sign of −ν N_k^2 t + N_{k−1}^α ∫_0^t X_{k−1}. By Cauchy–Schwarz and the energy
> equality, the second term is O(N_{k−1}^{α−1}), so growth is obstructed when α < 3."

Remark 1.4: "The inclusion of an external force is necessary for blow-up in this model, as
shown in [16]." Reference [16] = "S. Looi. to appear, 2026."

Looi's work is public only as talks, e.g. Princeton Analysis of Fluids seminar,
2 April 2026:

> "We prove that the viscous Obukhov model is globally regular for all initial data in the
> critical Sobolev space and above. The proof introduces a critical rescaling that shows a
> viscous activation threshold for each shell, and establishes regularity by showing that
> two competing scales, viscous damping and nonlinear growth, become incompatible at high
> frequencies."

(Caltech talks on the same title: Fluids and Analysis Seminar 17 March 2026; Math Graduate
Student Seminar 21 April 2026.) arXiv API queries (`all:"Obukhov model"`, author Looi)
returned no such preprint.

**Which sector of the family — the repository defines Looi's model but analyses the other one.**
The four-parameter dyadic transfer (`Cascade/Boussinesq.lean:71`) is

```
boussinesqTransferU A B u k = 2^k · ( A·((u_{k−1})² − 2u_k u_{k+1}) + B·(u_k u_{k−1} − 2(u_{k+1})²) )
```

and both named models are **sectors** of it, on the repository's own labels: `A = 1, B = 0` is the
frozen Stage R coupling, called the **Katz–Pavlović** self-interaction at
`Cascade/Boussinesq.lean:95`, while `A = 0, B = 1` is **Obukhov** (`Cascade/PROGRESS.md`, the intermittency section:
*"`α=1, β=0` is Katz–Pavlović, `α=0, β=1` is Obukhov"*). The two sectors differ in **which
neighbour carries the square**: `A` puts it on `u_{k−1}`, `B` on `u_{k+1}`.

Palasek's nonlinearity, arXiv:2407.06179 eq. (1.2), is
`B_k[u,u] = −N_{k−1}^α u_{k−1}u_k + N_k^α u_{k+1}²` — equivalently, up to overall sign,
`N_{k−1}^α u_{k−1}u_k − N_k^α u_{k+1}²`. **The repository's `B = 1` sector is exactly this.** At
`λ = 2, α = 1` the two agree term by term with a uniform factor `2` (`2^k` against `2^{k−1}` on
`u_{k−1}u_k`, and `2^{k+1}` against `2^k` on `u_{k+1}²`), so they are the same equation after a
time rescaling.

**Consequence, and it matters for any note to Looi.** The per-shell bar of
`Cascade/PerShellThreshold.lean` is instantiated at `velocityRHSDegreeE ν κ 1 0 e u θ k` — the
**`A = 1, B = 0`** sector — and `Cascade/IntermittencyThreshold.lean` follows Dai eq. (3.7), which
is also the `α`-term. Looi's theorem and Palasek's remark are about the **`B = 1`** sector.

`Cascade/PerShellSectorObukhov.lean` settles the comparison, and the answer is **negative**. In the
Obukhov sector the same enstrophy pairing gives

```
2 Σ_{k<N} 4^k u_k u_k' = 12 Σ_{j<N−1} 8^j u_j u_{j+1}² + 2κ Σ 4^k u_k θ_k − 2ν D_e
```

— the exact counterpart of `enstrophy_pairing_degree`, with the square moved from `u_j` onto
`u_{j+1}`. The shell summand therefore carries `u_j` **linearly** rather than as `u_j²`, so the sign
of a shell is **not a function of `(ν, e, j)` and `u_{j+1}` alone**: two states with the same
`u_{j+1}` give opposite signs (`obukhovShellTerm_sign_flip`), and consequently no function of
`(ν, e, j)` alone is a bar there (`no_obukhov_perShellBar`). What survives the change of sector is
the `e = 1` criticality, since the factor `2^{(e−1)j}` is present in both.

**The precise form of the negative, because "no bar" overstates it.** What the Obukhov sector has
instead is a **state-dependent threshold**: for `u_j > 0`, shell `j` transfers iff
`|u_{j+1}| > √((ν/6)·2^{(e−1)j}·u_j)` — a genuine threshold, but one whose *height moves with `u_j`*
rather than being fixed by `(ν,e,j)`. A reader who says "a threshold depending on `u_j` is still a
threshold" is right, and the claim must be stated as **"no `(ν,e,j)`-only bar"**. One further limit:
the two-state witness uses a **signed** ladder (`u_j = −1`), while Palasek's own constructed
solutions are non-negative (arXiv:2407.06179, Remark 1.4). On the non-negative cone the conclusion
survives for the different reason above — the height still moves — but it is *weaker*, and a note
must not imply it excludes a state-dependent threshold.

**So the bar is sector-specific; the criticality is not.** Any note to him should state the coupled
criterion rather than offer "there is no bar" as a candidate comparison.

High-dimension threshold, documented via a different route:

* Tao, blog post *Finite time blowup for an averaged three-dimensional Navier–Stokes
  equation*, 4 Feb 2014: "...established by Katz-Pavlovic and by Cheskidov for dyadic
  analogues of the Navier–Stokes equations **in five and higher dimensions** that obeyed the
  energy identity ... this is enough to give a version of Theorem 1 in five and higher
  dimensions."
* Cheskidov–Dai–Friedlander, *Dyadic models for fluid equations: a survey*, J. Math. Fluid
  Mech. 25 (2023), arXiv:2209.10203: "In particular, a blow-up occurs when the dyadic model
  scales as the five-dimensional NSE. **Remarkably, 5D is a common threshold for models
  exhibiting a blow-up**, see [92]." And: "solutions of the classical viscous dyadic model
  blow up when d < −1 ... However blow-up occurs in the five-dimensional case. As Tao
  remarked in his blog [92], this is a common threshold for models where the blow-up is
  known."
* Cheskidov 2008 (see Q4): α = 1/3 "corresponds to the 4D Navier–Stokes equations"; α = 2/5
  is "the same as the Sobolev estimate for the inertial term of the 3D NSE".

So `d/2 > 2` (equivalently `d ≥ 5`) is the right numerical threshold and matches the
literature's 5D threshold — but the literature reaches it through the intermittency /
nonlinearity-exponent bookkeeping, and I found **no source stating Palasek's specific
Bernstein-amplitude-versus-dissipation comparison**.

**A second Palasek paper, on a different point.** `arXiv:2407.06179` (*Non-uniqueness in the
Leray–Hopf class for a dyadic Navier–Stokes model*, 2024) does **not** contain the
`N_k^{3/2}`-versus-`N_k^2` remark either. But fetched from the arXiv HTML it **does** state,
in four separate places, the `ℤ`/`ℕ` closure taxonomy that `Cascade/CLOSURE.md` §1 and §4.2
reach independently. Verbatim:

> "Unless otherwise noted, we take the index set to be `I = ℕ` which models the
> Navier–Stokes on `Ω = 𝕋^d`. In this case **one closes the system by fixing `u_{−1} = 0`**.
> At times we will also refer to (1.2) with `I = ℤ` which models the Navier–Stokes on
> `ℝ^d`. **An additive group structure on `I` is necessary to discuss exact scale
> invariance.**"

> footnote 1: "Transferring the non-uniqueness scenario from `I = ℤ` to `ℕ` is analogous to
> the idea of truncating a self-similar solution of a PDE which is a standard idea (e.g.,
> [19]). In this work the truncation is possible **not by stability** (because the
> non-uniqueness is not stable), but rather because the different frequency shells are
> **weakly coupled** together, so the self-similarity can be **interrupted at the low
> modes** without difficulty."

> "In fact our construction is even simpler in this setting (**at the cost of yielding
> infinite energy solutions**)."

The correspondence below is **this record's mapping, not his** — he does not mention this
repo or the cascade:

| Palasek 2024 | this repo |
|---|---|
| group structure required for exact scale invariance | the chain (`ℤ`) is a group ⇒ the closing edge is **free**; the tree is rooted ⇒ it must be supplied |
| `ℕ` closed by fixing `u_{−1} = 0` | the **clamp** |
| the transfer works by weak coupling, self-similarity "interrupted at the low modes" | the root obstruction; the `ℤ → ℕ` transfer is **approximate**, not exact |
| `I = ℤ` "at the cost of yielding infinite energy solutions" | `CLOSURE.md` §2.2 — the physical enstrophy is infinite |

**Consequence.** The exact-versus-approximate framing of `CLOSURE.md` §4.2 is **not this
repo's invention**. Palasek states the group-structure requirement himself, calls the
`ℤ → ℕ` step a truncation that works only by weak coupling, and acknowledges the
infinite-energy cost that the repo lists among its four caveats. What remains unrecorded is
the *Bernstein* comparison of Q1(a) alone; the closure taxonomy is his. This is the
strongest corroboration the thread has found, and it changes the pitch: what this repo can
offer him is the **exact** version of a step he takes approximately.

### (c) Citations / links

* Palasek post: https://mathstodon.xyz/@palasek/117235270483911935
* Tao reply (the exercise): https://mathstodon.xyz/@tao/117236063705269594
* Tao posts it replies to: https://mathstodon.xyz/@tao/117233527638291447 ,
  https://mathstodon.xyz/@tao/117233528517340774
* Palasek, *Finite-time blow-up in an elementary model of the 3D Navier–Stokes equations*,
  arXiv:2605.13827 — https://arxiv.org/abs/2605.13827
* Palasek, *Non-uniqueness in the Leray–Hopf class for a dyadic Navier–Stokes model*,
  arXiv:2407.06179 — https://arxiv.org/abs/2407.06179 (read as arXiv HTML; source of the
  `ℤ`/`ℕ` closure quotations in Q1(b))
* Looi seminar (Princeton): https://www.math.princeton.edu/events/global-regularity-viscous-dyadic-model-navier-stokes-equations-2026-04-02t190000
* Looi seminar (Caltech): https://www.pma.caltech.edu/events/pma-calendar/analysis-seminar-54
* Tao blog 2014: https://terrytao.wordpress.com/2014/02/04/finite-time-blowup-for-an-averaged-three-dimensional-navier-stokes-equation/
* Tao blog 2026 (context): https://terrytao.wordpress.com/2026/09/07/finite-time-blowup-with-smooth-forcing-term-for-the-incompressible-porous-medium-boussinesq-and-incompressible-euler-equations/
* Cheskidov–Dai–Friedlander survey: https://arxiv.org/abs/2209.10203
* Mailybaev, *Bifurcations of blowup in inviscid shell models of convective turbulence*,
  arXiv:1210.2494 — https://arxiv.org/abs/1210.2494

---

## Q2. Shell-model literature on dimension

### (a) Answer

**Dimension-dependent dyadic models exist, but not in the form asked about.**

* The **standard** one-mode-per-octave dyadic/shell models (Desnyansky–Novikov/Katz–Pavlović,
  Obukhov, GOY, Sabra) are **dimension-free**: the per-shell amplitude is an ℓ²/energy-type
  amplitude and the only bound available is the energy bound, with no `N_k^{d/2}` factor.
* A family of **explicitly dimension-dependent dyadic models does exist**: the
  *intermittency-dimension* dyadic models. The dimension enters as the **nonlinearity
  exponent** `θ = (5−δ)/2` (or, in `n` dimensions, `θ = (2+n−δ)/2`), where `δ` is the
  intermittency dimension defined by the **saturation level of Bernstein's inequality**.
  The amplitude is still `a_j ~ ‖u_j‖_{L²}` — dimension-free — and the dissipation is
  still `ν λ_j² a_j²`.
* The **closest thing to "the amplitude carries the Bernstein factor `N^{d/2}`"** is
  the Katz–Pavlović change of variables in Cheskidov's derivation,
  `u_j = 2^{3j/2} v_j`, i.e. multiplication by `N^{3/2}` — the `d = 3` Bernstein factor.
  But `d` is fixed at 3 there; the model's behaviour does not depend on `d`, and the
  rescaling merely moves the exponent between the nonlinearity and the amplitude.
* Dai notes that the intermittency-dependent MHD dyadic models are **equivalent to a class
  of MHD shell models proposed by physicists** (Plunian–Stepanov–Frick), i.e. the
  dimension parameter corresponds to a coupling parameter already present in physics shell
  models, rather than to an intrinsic per-shell Bernstein factor.

**Not found:** any shell/dyadic model whose *per-shell amplitude* intrinsically carries
`N_k^{d/2}` with variable spatial dimension `d`, as opposed to a dimension-dependent
nonlinearity exponent or a fixed-`d` rescaling.

### (b) Evidence

Cheskidov–Dai–Friedlander survey (arXiv:2209.10203), §2.2 "Intermittency":

> "Mathematically, we can associate intermittency with the level of saturation of
> Bernstein's inequality. ... Recall that Bernstein's inequality in three dimensional space
> takes the form ‖u_j‖_{L^q} ≤ c λ_j^{3(1/p−1/q)}‖u_j‖_{L^p}. Adapting the idea of [19], we
> define the intermittency dimension d for a 3D turbulent vector field u in view of the
> saturation level of Bernstein's inequality ... Thus we have d ∈ [0,3] and the optimal
> Bernstein's relationship ‖u_j‖_{L^∞} ∼ λ_q^{(3−d)/2}‖u_j‖_{L²} (2.6) at each scale λ_j."

Survey eq. (2.7) (the resulting model) and Remark 2.1:

> "d/dt a_j + νλ_j² a_j − α(λ_{j−1}^{(5−d)/2} a_{j−1}² − λ_j^{(5−d)/2} a_j a_{j+1}) − β(...)
> = 0 ... with a_j(t) ∼ ‖u_j(t)‖_{L²}"

> "(i) For 3D flows we have the intermittency dimension d ∈ [0,3]. Thus the nonlinear
> scaling index (5−d)/2 in (2.7) belongs to [1, 5/2] ..."

Survey derivation, showing Bernstein saturation is used only to *fix the exponent*:

> "Next we estimate the size of Q_j and P_j by using Bernstein's relation (2.6) ... Q_j ≲
> ‖u_j‖_{L²}‖∇u_j‖_{L^∞}‖u_{j+1}‖_{L²} ∼ λ_j^{(5−d)/2}‖u_j‖_{L²}²‖u_{j+1}‖_{L²}"

Dai, *Dyadic models with intermittency dependence for the Hall MHD*, arXiv:2006.15094
(Physica D 428:133066, 2021), eq. (3.7) and §2:

> "δ_v := sup{s : ⟨Σ_j λ_q^{−1+s}‖v_j‖_{L^∞}²⟩ ≤ c^{3−s}L^{−s}⟨Σ_j λ_q²‖v_j‖_{L²}²⟩} ... the
> optimal Bernstein's relationship ‖v_j‖_{L^∞} ∼ λ_q^{(3−δ_v)/2}‖v_j‖_{L²} (2.4) at each
> scale λ_j."
> "d/dt a_j + νλ_j² a_j − α(λ_{j−1}^{(5−δ_u)/2}a_{j−1}² − ...) = 0 ... with a_j(t) = ‖u_j(t)‖_{L²}"

Dai, *Kolmogorov's dissipation number and determining wavenumber for dyadic models*,
arXiv:2108.12913 (Nonlinearity 37 (2024) 025015):

> "θ = (2+n−δ)/2 ∈ [1, (2+n)/2], δ ∈ [0,n], with δ being the intermittency dimension of
> the n-dimensional velocity field ... The models (1.3) and (1.4) are equivalent to a class
> of MHD shell models proposed by physicists in [17] ... [23] F. Plunian, R. Stepanov and
> P. Frick, *Shell models of magnetohydrodynamic turbulence*, Physics Reports 523 (2013)."

Katz–Pavlović Bernstein rescaling, Cheskidov 2008 (arXiv:math/0601074), §2:

> "...the change of variables u_j(t) = 2^{3j/2} v_j(t/8) reduces the equations to
> d/dt u_j = −ν̃ 2^{2αj} u_j + 2^j u_{j−1}² − 2^{j+1} u_j u_{j+1}, j ≥ 1."

The intermittency-dimension definition originates in Cheskidov & Dai, *Kolmogorov's
dissipation number and the number of degrees of freedom for the 3D Navier–Stokes
equations*, arXiv:1510.00379 (Proc. Roy. Soc. Edinburgh Sect. A 149(2):429–446, 2019):
"we ... define the itermittency dimension d through the average level of saturation of
Bernstein's inequality".

### (c) Citations / links

* Cheskidov–Dai–Friedlander survey: https://arxiv.org/abs/2209.10203 (J. Math. Fluid Mech.
  25(3):Paper No. 62, 2023)
* Dai, Hall MHD: https://arxiv.org/abs/2006.15094 (Physica D 428:133066, 2021)
* Dai, determining wavenumber: https://arxiv.org/abs/2108.12913 (Nonlinearity 37 (2024) 025015)
* Cheskidov–Dai 2019 (definition origin): https://arxiv.org/abs/1510.00379
* Katz–Pavlović: Trans. Amer. Math. Soc. 357(2):695–708 (2005)
* Kiselev–Zlatoš, *On discrete models of the Euler equation*, Int. Math. Res. Not. (38):2315–2339 (2005)
* Cheskidov–Friedlander–Pavlović, *Inviscid dyadic model of turbulence*,
  J. Math. Phys. 48(6):065503 (2007) and Discrete Contin. Dyn. Syst. 26(3):781–794 (2010)
* Biferale, *Shell models of energy cascade in turbulence*, Annu. Rev. Fluid Mech.
  35:441–468 (2003)
* Bohr, Jensen, Paladin, Vulpiani, *Dynamical Systems Approach to Turbulence*, CUP 1998
* Plunian, Stepanov, Frick, *Shell models of magnetohydrodynamic turbulence*,
  Physics Reports 523 (2013)
* Mailybaev (convective/Boussinesq shell model): https://arxiv.org/abs/1210.2494

---

## Q3. The equivalence "saturating Bernstein per shell = shift of dissipation degree"

### (a) Answer

* The literal displayed identity
  `ν N_k² (a_k²/N_k^d) = ν N_k^{2−d} a_k²`
  is **elementary algebra** (a diagonal change of amplitude variable). I found **no source
  that states it in exactly this "Bernstein-constraint saturation ⟺ shift of the
  dissipation degree" form**. In that form it is folklore/trivial.
* **However, the equivalent statement is explicitly recorded in the literature in
  reciprocal/rescaling form**: the dimension/intermittency parameter and the dissipation
  degree can be traded against each other by a *frequency rescaling*. Two explicit
  statements:
  * Cheskidov–Dai–Friedlander survey: the model with dissipation degree `γ` and
    nonlinearity `λ_j` is "equivalent to the model (3.7)" with dissipation `λ_j²` and
    nonlinearity exponent `θ = 1/γ` — "By rescaling the frequency we note (3.6) is
    equivalent to the model (3.7) with θ = 1/γ."
  * Dai, Remark 6.4 (arXiv:2006.15094): the intermittency-dependent model with exponent
    `θ` is equivalent, "by rescaling the wavenumber λ_j = λ̄_j^{1/θ}", to a model with
    nonlinearity degree 1 and **generalized diffusion `(−Δ)^α` with `α = 1/θ`**. Since
    `θ = (5−δ)/2` carries the dimension, this is precisely "dimension parameter ⟺
    dissipation degree", just written reciprocally.
* So: **found** as a frequency-rescaling trade-off between the intermittency/dimension
  parameter and the dissipation degree; **not found** as the additive per-shell bookkeeping
  `2 ↦ 2−d`. The latter is the same content rearranged, and is not recorded as a named
  observation.

### (b) Evidence

Cheskidov–Dai–Friedlander survey, §3.2:

> "d/dt a_j + νλ_j^{2γ} a_j = λ_j a_{j−1}² − λ_{j+1} a_j a_{j+1} + f_j  (3.6) ... By
> rescaling the frequency we note (3.6) is equivalent to the model d/dt a_j + νλ_j² a_j =
> λ_j^θ a_{j−1}² − λ_{j+1}^θ a_j a_{j+1} + f_j  (3.7) with θ = 1/γ."

Dai, arXiv:2006.15094, Remark 6.4:

> "The dyadic system (3.14) is equivalent to ... d/dt a_j = −ν λ̄_j^{2α} a_j − λ̄_j a_j a_{j+1}
> + λ̄_{j−1} a_{j−1}² + ... (6.22) with α = 1/θ, by rescaling the wavenumber λ_j = λ̄_j^α.
> The system (6.22) can be seen as the dyadic model of the Hall-MHD system with generalized
> diffusions (−Δ)^α u and (−Δ)^α B. Based on Remark 6.3, in the case of d_i > 0, the system
> has a local strong solution for α > 1/2 and a global strong solution for α ≥ 1; when
> d_i = 0, the system has a local strong solution for α > 1/3 and a global strong solution
> for α ≥ 1/2."

The Bernstein saturation relation itself (where the `N^{(3−δ)/2}` factor lives):
CSDF survey eq. (2.6) and Dai eq. (2.4), quoted in Q2.

### (c) Citations / links

* CSDF survey §3.2: https://arxiv.org/abs/2209.10203
* Dai Remark 6.4: https://arxiv.org/abs/2006.15094
* Same trade-off in Dai 2024: https://arxiv.org/abs/2108.12913

---

## Q4. Cheskidov's thresholds (primary source)

### (a) Answer

Primary source: **A. Cheskidov, "Blow-up in finite time for the dyadic model of the
Navier–Stokes equations", Trans. Amer. Math. Soc. 360 (2008), no. 10, 5101–5120**
(arXiv:math/0601074). Model (§2, Katz–Pavlović after the change of variables
`u_j = 2^{3j/2}v_j`):

```
d/dt u_j = −ν 2^{2α j} u_j + 2^j u_{j−1}² − 2^{j+1} u_j u_{j+1},   j ≥ 1.
```

Exact statements (numbering as in the arXiv version; the published numbering may differ):

* **Theorem 4.3** — local regularity for `α > 1/3`.
* **Theorem 4.4** — **global regularity for `α ≥ 1/2`**.
* **Theorem 5.3** — **finite-time blow-up for `α < 1/3`** (nonnegative data; for every
  `γ > 0` there is `M(γ)` such that `‖u(t)‖³_{1/3+γ}` is not locally integrable on
  `[0,∞)` provided `‖u(0)‖_γ > M(γ)`).
* Dimension correspondences: `α = 2/5` corresponds to the **3D NSE**; `α = 1/3`
  corresponds to the **4D NSE**.

**The gap `α ∈ [1/3, 1/2)` is explicitly recorded, not passed over silently.** It is
stated (i) generally by Cheskidov himself, (ii) explicitly in `β`-notation by
Barbato–Morandin–Romito, who narrowed it to `α ∈ [1/3, 2/5)`, and (iii) explicitly in the
survey. **No later paper closing the remaining `[1/3, 2/5)` gap was found.**

### (b) Evidence

Abstract of Cheskidov 2008:

> "They showed a finite time blow-up in the case where the dissipation degree α is less
> than 1/4. In this paper we prove the existence of weak solutions for all α, energy
> inequality ... local regularity for α > 1/3, and global regularity for α ≥ 1/2. In
> addition, we prove a finite time blow-up in the case where α < 1/3. It is remarkable that
> the model with α = 1/3 enjoys the same estimates on the nonlinear term as the 4D
> Navier–Stokes equations."

Theorem 4.3: "If α > 1/3, then for any u⁰ ∈ V there exists a strong solution u(t) to (3.1)
on some time interval [0,T] ..."

Theorem 4.4: "If α ≥ 1/2, then for any u⁰ ∈ V there exists a strong solution u(t) to (3.1)
on [0,∞) with u(0) = u⁰."

Theorem 5.3: "Let u(t) be a solution to (3.1) with u_n(0) ≥ 0 and α < 1/3. Then for every
γ > 0, there exists a constant M(γ), such that ‖u(t)‖³_{1/3+γ} is not locally integrable on
[0,∞), provided ‖u(0)‖_γ > M(γ)."

Gap, Cheskidov §1:

> "Note that there is still a gap between the regions of global regularity and blow-up in
> finite time, which means that the developed technique is not sharp enough to separate
> these two behaviors."

3D/4D correspondence, Cheskidov §4 (after deriving the sharp estimate with `α = 2/5`):

> "|(B(u,u),Au)| ≤ c_b|Au|^{3/2}‖u‖^{3/2}, which is the same as the Sobolev estimate for
> the inertial term of the 3D NSE ... Hence, the model has the same enstrophy estimate as
> the 3D NSE, similar properties, and the same open question concerning the regularity of
> the solutions in the case α = 2/5."

> "Another interesting case is α = 1/3. Then we have ... (4.6) |(B(u,u),Au)| ≤ c_b|Au|²‖u‖,
> which corresponds to the 4D Navier–Stokes equations."

The gap in `β`-notation and its narrowing — Barbato–Morandin–Romito, *Smooth solutions for
the dyadic model*, Nonlinearity 24(11):3083–3097, 2011 (arXiv:1007.3401), §1.1 (their model
has dissipation `νλ_n²` and nonlinearity exponent `β`):

> "The range of values β ∈ (2, 5/2] is essentially the one corresponding, within the
> simplification of the model, to the three dimensional Navier-Stokes equations. ... If
> β ≤ 2 the non linear term is dominated by the dissipative one, in this case Cheskidov [4]
> proved existence of regular global solutions using classical techniques, while if β > 3
> the non–linearity is too strong and all solutions with large enough initial condition
> develop a blow–up [4]. The two results above are based on 'energy methods' and do not
> cover the range β ∈ (2, 5/2], where it becomes crucial to understand how the structure of
> the non–linearity drives the dynamics."

The survey states the gap and its current extent explicitly:

> "We also note the presence of the gap 1/3 ≤ γ < 1/2 between the two scenarios of finite
> time blow-up and global regularity. The gap was made smaller thanks to a regularity result
> of Barbato, Morandin and Romito [9]. The authors showed global regularity for (3.6) with
> γ ≥ 2/5 by finding an invariant region for the vector (a_j, a_{j+1}) through a dynamical
> system argument. It is remarkable that γ ≥ 2/5 corresponds to θ ≤ 5/2 and hence d ≥ 0,
> i.e., this covers the whole physically relevant intermittency regime. Therefore, [9]
> settles that solutions to the dyadic model corresponding to the 3D NSE are globally
> regular."

Here `γ` is the dissipation degree and `α = γ` (Cheskidov's notation). So after BMR the
remaining open range is `α ∈ [1/3, 2/5)` — outside the physically relevant 3D-NS
intermittency regime but still mathematically open.

Related later work (does **not** close the `[1/3, 2/5)` gap):
Cheskidov–Zaya, *Regularizing effect of the forward energy cascade in the inviscid dyadic
model*, Proc. Amer. Math. Soc. 144:73–85 (2016), and Barbato–Morandin–Romito,
*Global regularity for a logarithmically supercritical hyperdissipative dyadic equation*,
Dyn. PDE 11(1):39–52 (2014) — these address the hyperdissipative/Tao-conjecture gap, not
the `α` gap.

### (c) Citations / links

* Cheskidov 2008: https://arxiv.org/abs/math/0601074 (Trans. Amer. Math. Soc. 360(10):5101–5120, 2008)
* Barbato–Morandin–Romito 2011: https://arxiv.org/abs/1007.3401 (Nonlinearity 24(11):3083–3097)
* Cheskidov–Dai–Friedlander survey: https://arxiv.org/abs/2209.10203
* Cheskidov–Zaya 2016: Proc. Amer. Math. Soc. 144:73–85
* Barbato–Morandin–Romito 2014: https://arxiv.org/abs/1403.2852 (Dyn. PDE 11(1):39–52)

---

## Bottom line for the proposed short negative note

**Already in the literature (cite, do not claim as new):**

1. The `d = 5` / `d/2 > 2` threshold for dyadic blow-up, with the explicit statement that
   "5D is a common threshold" (Tao 2014 blog; Cheskidov–Dai–Friedlander 2023).
2. The dimension ↔ dissipation-degree trade-off, explicitly, as a frequency rescaling
   (CSDF survey (3.6)↔(3.7), `θ = 1/γ`; Dai Remark 6.4, `α = 1/θ`, generalized diffusion).
3. The gap `α ∈ [1/3, 1/2)` and its narrowing to `[1/3, 2/5)` — stated explicitly in three
   places.
4. The rigorous shell-model obstruction (forcing necessary; `α < 3` in Palasek's paper's
   notation), attributed to Looi.
5. **The `ℤ`/`ℕ` closure taxonomy** — exact scale invariance needs an additive group
   structure on the index set; the rooted (`ℕ`) model is closed by fixing `u_{−1} = 0`; the
   `ℤ → ℕ` transfer works only by weak coupling, "interrupted at the low modes"; and the `ℤ`
   construction costs infinite energy. All four are Palasek's own, arXiv:2407.06179. See
   Q1(b). `Cascade/CLOSURE.md` §1/§4.2 arrives at the same dichotomy independently, so the
   *exact* version is this repo's only addition to it.

**Not found (where a genuine gap in the literature remains):**

1. Palasek's specific Bernstein-`N_k^{3/2}`-versus-`N_k²` comparison, and the
   "in high dimension there is no obstruction" caveat, are **not written up anywhere**;
   neither the paper he links (arXiv:2605.13827) nor his earlier arXiv:2407.06179 contains
   them. (2407.06179 *does* contain the closure taxonomy — see the item 5 above.)
2. No shell/dyadic model with an **intrinsic per-shell `N_k^{d/2}` Bernstein factor** was
   found; existing dimension-dependent models put `d` in the nonlinearity exponent.
3. The identity `ν N_k² (a_k²/N_k^d) = ν N_k^{2−d} a_k²` is not recorded as an explicit
   observation (it is the same content as (2) rearranged).
4. Nobody has publicly done Tao's Boussinesq-dyadic exercise.

**Assessment.** A note would only be worth writing if it does more than restate the known
intermittency-dimension bookkeeping. The one genuinely unrecorded piece is Palasek's
Bernstein-amplitude heuristic and its relation to the standard `θ = (5−δ)/2` model; but
demonstrating that the heuristic is *equivalent* to the known Cheskidov–Dai/Dai framework
(which Q3's evidence suggests) would make the note a clarification rather than a new
result. As a short "this heuristic is the intermittency-dimension model in disguise, and
here is the precise dictionary" note it has some value; as a claim of a new obstruction it
does not.
