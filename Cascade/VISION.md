# Vision: why formalize dyadic cascade models?

## The trigger

On 2026-09-08 Levent Alpöge and Tristan Buckmaster announced three results: finite-time
blowup **with a smooth forcing term** for incompressible porous media, for Boussinesq, and
for 3D incompressible Euler — pushing the Córdoba–Martínez-Zoroa construction
([announcement](https://mastodon.social/@tristanbuckmaster/117233413705701198), papers at
`cims.nyu.edu/~tristanb/`, Lean formalisation at
[`tristanbuckmaster/fluid_lean`](https://github.com/tristanbuckmaster/fluid_lean)).

[Terence Tao](https://mathstodon.xyz/@tao/117233527638291447) called it "a remarkable
achievement" and noted that "The arguments have been formalized in Lean". In the same
thread [Stan Palasek](https://mathstodon.xyz/@palasek/117235270483911935) raised an
obstruction to *removing* the force: for a lacunary cascade the velocity at frequency
`N_k` grows at most like `O(N_k^{3/2})` (Bernstein + energy) while energy depletion acts
at rate `~N_k²`, so dissipation wins — "(In high dimension, though, there is no
obstruction!)".

Tao's [reply](https://mathstodon.xyz/@tao/117236063705269594) is the seed of this library:

> "It might be an illustrative exercise to locate a dyadic model with the same scaling
> features as, say, Boussinesq, and see what the analogue of the recent blowup
> construction is in that model. Hopefully one can create a model in which the arguments
> become significantly shorter and more transparent since one can simply remove any
> unwanted interactions from the model rather than have to estimate their contribution."

## The question

Can the Alpöge–Buckmaster / Córdoba–Martínez-Zoroa blowup construction be carried out in a
dyadic model carrying the scaling features of Boussinesq — and does the forced/unforced
asymmetry that Palasek identified show up in that model?

Two theorems would answer it:

- **B (blowup):** the dyadic model, with a suitable force, has a finite-time blowup.
- **O (obstruction):** without the force, the same model cannot self-sustain the cascade.

The *contrast* is the content. A model in which the two provably differ is the dyadic
caricature of the Tao/Palasek exchange.

## Why dyadic

A shell model carries one amplitude per dyadic octave, and the nonlinearity couples only
nearest octaves (`k−1, k, k+1`). Unwanted interactions can therefore be **deleted by
definition** rather than estimated — exactly the simplification Tao points at. The cost is
fidelity: we choose the model, so we must *prove* it is the right caricature.

## Scope

**In scope (Lean-able):** the dyadic ODE model and its scaling covariance; the energy
identity; the lacunary ansatz and its amplitude-frequency ODE; the forced blowup; the
unforced obstruction.

**Out of scope:** the PDE. This is a *model*, not Navier–Stokes or Boussinesq, and it
proves nothing about 3D NS regularity. Same honesty rule as `Criticality/VISION.md`.

## Fidelity rules (hard requirements)

Any theorem here is only as good as the model it is stated for. Therefore:

1. **Fix the model from its scaling and coupling alone, before proving anything about its
   solutions.** No "and assume the amplitudes diverge".
2. **Prove scaling covariance** with the chosen Boussinesq exponents, as a theorem — this
   is what makes the model the *right* caricature rather than an arbitrary ODE.
3. **The blowup must come from the dynamics**, not from an inserted singularity or a
   declared divergence.
4. **A negative result counts.** If the construction does not simplify, or the unforced
   model cannot blow up, that is a formalized finding, not a failure.
