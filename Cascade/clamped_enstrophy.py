#!/usr/bin/env python3
"""Reproduce the clamped-chain enstrophy excursion quoted on the ring-invariants figure.

Model: the inviscid, unforced clamped chain at N = 3, with Dirichlet ends
u_{-1} = u_3 = 0,

    u_k' = 2^k (u_{k-1}^2 - 2 u_k u_{k+1}),        k = 0, 1, 2,

i.e. explicitly

    u_0' = -2 u_0 u_1
    u_1' =  2 (u_0^2 - 2 u_1 u_2)
    u_2' =  4 u_1^2

Quantities tracked:

    E = u_0^2 +  u_1^2 +  u_2^2      (conserved; the clamp's one invariant)
    H = u_0^2 + 4u_1^2 + 16u_2^2     (NOT conserved; the enstrophy)

The weight bound is  H <= 4^{N-1} E = 16 E  at N = 3.  It is attained exactly
when all the energy sits on the top shell, u = (0, 0, +-sqrt(14)), since then
H = 16 * 14 = 224 and E = 14.  The ceiling therefore measures concentration of
energy onto the smallest resolved scale.

Initial data (1, 2, 3):  E = 14,  H(0) = 161,  ceiling 4^{N-1} E = 224.

Why this file exists.  The figure `Cascade/ring_invariants.svg`, produced by
`Cascade/plot_ring_invariants.py`, draws a measured enstrophy excursion and
labels it "[measured: 161 -> 223.48 at N = 3]".  That number was computed only in
a /tmp scratch run and recorded nowhere in this repository.  This script is its
permanent home: it is the computation behind the figure label.  Note also that
the figure calls 223.48 a "max"; it is the value at t = 50, NOT a maximum,
because H is still rising there (see the table below).

The bound H <= 4^{N-1} E is a theorem (see `Cascade/CLOSURE.md` section 5 and
`Cascade/TruncatedRegularity.lean`); the excursion reported here is floating
point RK4 numerics and is [measured], not [proved].  See `Cascade/CLOSURE.md`
for the write-up.

Standard library only; deterministic.  Usage:

    python3 Cascade/clamped_enstrophy.py

Exit status is 0 when the run reproduces the recorded values and passes its own
internal checks (energy conservation, monotone H, H strictly below the ceiling);
non-zero otherwise.
"""

import sys

N = 3
CEILING_FACTOR = 4 ** (N - 1)              # 16
U_INIT = (1.0, 2.0, 3.0)
E0 = U_INIT[0] ** 2 + U_INIT[1] ** 2 + U_INIT[2] ** 2          # 14
CEILING = CEILING_FACTOR * E0                                  # 224

# Measured values supplied for reproduction.  The integrator and step sizes are
# fixed by the model (dt = 1e-4 on [0, 2000]); these numbers are NOT used to
# tune anything, only to report agreement or discrepancy.
EXPECTED = {
    50: 223.477305,
    100: 223.729587,
    200: 223.862349,
    500: 223.944319,
    1000: 223.972052,
    2000: 223.985998,
}
SAMPLE_TIMES = (50, 100, 200, 500, 1000, 2000)


def enstrophy(a, b, c):
    return a * a + 4.0 * b * b + 16.0 * c * c


def energy(a, b, c):
    return a * a + b * b + c * c


def integrate(dt, t_end, record_times):
    """Fixed-step RK4 on the clamped N = 3 chain.

    Returns (records, max_energy_error, monotone, min_dH), where records is a
    list of (t, H, E) at the requested times.
    """
    n = int(round(t_end / dt))
    targets = {}
    for t in record_times:
        step = int(round(t / dt))
        if abs(step * dt - t) > 1e-9:
            raise ValueError("record time %r is not a multiple of dt = %r" % (t, dt))
        targets[step] = float(t)

    h2 = 0.5 * dt
    h6 = dt / 6.0
    a, b, c = U_INIT
    H = enstrophy(a, b, c)
    max_energy_error = 0.0
    monotone = True
    min_dH = float("inf")
    records = []
    if 0 in targets:
        records.append((0.0, H, energy(a, b, c)))

    for step in range(1, n + 1):
        # k1
        k10 = -2.0 * a * b
        k11 = 2.0 * (a * a - 2.0 * b * c)
        k12 = 4.0 * b * b
        # k2
        a2 = a + h2 * k10
        b2 = b + h2 * k11
        c2 = c + h2 * k12
        k20 = -2.0 * a2 * b2
        k21 = 2.0 * (a2 * a2 - 2.0 * b2 * c2)
        k22 = 4.0 * b2 * b2
        # k3
        a3 = a + h2 * k20
        b3 = b + h2 * k21
        c3 = c + h2 * k22
        k30 = -2.0 * a3 * b3
        k31 = 2.0 * (a3 * a3 - 2.0 * b3 * c3)
        k32 = 4.0 * b3 * b3
        # k4
        a4 = a + dt * k30
        b4 = b + dt * k31
        c4 = c + dt * k32
        k40 = -2.0 * a4 * b4
        k41 = 2.0 * (a4 * a4 - 2.0 * b4 * c4)
        k42 = 4.0 * b4 * b4

        a += h6 * (k10 + 2.0 * k20 + 2.0 * k30 + k40)
        b += h6 * (k11 + 2.0 * k21 + 2.0 * k31 + k41)
        c += h6 * (k12 + 2.0 * k22 + 2.0 * k32 + k42)

        H_old = H
        H = enstrophy(a, b, c)
        E = energy(a, b, c)

        dH = H - H_old
        if dH < 0.0:
            monotone = False
        if dH < min_dH:
            min_dH = dH
        err = abs(E - E0)
        if err > max_energy_error:
            max_energy_error = err

        if step in targets:
            records.append((step * dt, H, E))

    return records, max_energy_error, monotone, min_dH


def main():
    print(__doc__.splitlines()[0])
    print()
    print("clamped N = 3 chain, u_{-1} = u_3 = 0, initial data (1, 2, 3)")
    print("E0 = %.1f    H(0) = %.1f    weight bound 4^{N-1}E0 = %.1f" %
          (E0, enstrophy(*U_INIT), CEILING))
    print("bound attained exactly at u = (0, 0, +-sqrt(14)):  H = 16*14 = 224")
    print()

    dt = 1e-4
    t_end = 2000.0
    records, max_energy_error, monotone, min_dH = integrate(dt, t_end, SAMPLE_TIMES)

    print("RK4, dt = %g, t in [0, %g]" % (dt, t_end))
    print("  t          H                 E                deficit 224-H"
          "     2E/t = 28/t     deficit/(2E/t)")
    for t, H, E in records:
        deficit = CEILING - H
        two_e_over_t = 2.0 * E0 / t
        ratio = deficit / two_e_over_t
        print("  %-9g  %-16.6f  %-15.10f  %-16.6f  %-14.6f  %.6f"
              % (t, H, E, deficit, two_e_over_t, ratio))
    print()

    print("internal checks (dt = 1e-4):")
    print("  max |E - E0|            = %.3e   (E conserved)" % max_energy_error)
    print("  H monotone increasing   = %s" % ("yes" if monotone else "NO"))
    print("  min one-step dH         = %.3e" % min_dH)
    print("  max H over the run      = %.6f < %.1f (ceiling, strict)" %
          (max(r[1] for r in records), CEILING))
    print("  deficit > 0 throughout  = %s" %
          ("yes" if all(CEILING - r[1] > 0.0 for r in records) else "NO"))
    print()

    # convergence check: the same quantity at a five-times smaller step
    dt_small = 2e-5
    t_small = 50.0
    small_records, small_e_err, small_monotone, _ = integrate(dt_small, t_small, (50,))
    H_small = small_records[0][1]
    H_coarse = records[0][1]  # H at t = 50, dt = 1e-4
    print("convergence check at t = 50:")
    print("  dt = 1e-4   H(50) = %.9f" % H_coarse)
    print("  dt = 2e-5   H(50) = %.9f   (max |E - E0| = %.2e)" %
          (H_small, small_e_err))
    print("  |difference|      = %.3e   (not a step-size artifact if tiny)" %
          abs(H_small - H_coarse))
    print()

    print("comparison with the recorded measured values (t, H):")
    ok = True
    for t in SAMPLE_TIMES:
        got = dict((r[0], r[1]) for r in records)[float(t)]
        want = EXPECTED[t]
        diff = got - want
        flag = "ok" if abs(diff) < 5e-4 else "DISCREPANCY"
        if abs(diff) >= 5e-4:
            ok = False
        print("  t = %-5d recorded H = %.6f   computed H = %.6f   diff = %+.2e   %s"
              % (t, want, got, diff, flag))
    print()

    checks_ok = (
        ok
        and max_energy_error < 1e-9
        and monotone
        and all(CEILING - r[1] > 0.0 for r in records)
        and abs(H_small - H_coarse) < 1e-6
    )
    print("RESULT:", "PASS - all recorded values reproduced within 5e-4" if checks_ok
          else "FAIL - see DISCREPANCY/check lines above")
    return 0 if checks_ok else 1


if __name__ == "__main__":
    sys.exit(main())
