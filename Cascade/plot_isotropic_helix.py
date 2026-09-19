#!/usr/bin/env python3
"""The rope looping back onto itself -- and why it is a helix, not a circle.

Companion to Cascade/plot_isotropic_closure.py, which carries the record panels.  This figure
draws the one thing that one is not good at: the physical object itself, in three dimensions.

WHAT IS BEING DRAWN

Cascade/CLOSURE.md Sec. 4.2 (corrigendum).  The tree cascade

        Xdot_n = 2^{alpha n} X_{n-1}^2 - b 2^{alpha(n+1)} X_n X_{n+1}

closes on the ISOTROPIC subspace: every node at a level shares one amplitude, X_n = mu^{-n} R_n.
The two chain coefficients A_n = 2^{alpha n} mu^{2-n} and B_n = b 2^{alpha(n+1)} mu^{-(n+1)} are
both independent of n **iff mu = 2^alpha**, and then

        Rdot_n = 4^alpha R_{n-1}^2 - b R_n R_{n+1}        on Z/N ,    R_{n+N} = R_n .

The point of this figure is the difference between the two variables:

  * R is genuinely PERIODIC in the index -- the reduced chain is a circle, Z/N;
  * X is NOT: X_{n+N} = mu^{-N} X_n.  Going once round returns you to the same angular
    position at a SMALLER radius.

So the physical object is a HELIX closing up to a twist, not a circle.  Drawing it as a circle
would be wrong, and that rescaling-by-mu^{-N} IS the self-similarity (the twist
u_{k+N} = 2^{-N} u_k of CLOSURE.md Sec. 1.2).  That is the whole content of the picture.

HONESTY

  * X_{n+N} = mu^{-N} X_n is exact and is checked exactly in Cascade/zeta_checks.py section K.
  * The RING the helix is drawn around carries an ILLUSTRATIVE periodic profile R_n (a cosine of
    amplitude 0.25); no particular R is claimed.  The figure is a picture of the RELATION between
    X and R, not of a particular solution.
  * alpha, b, N are chosen for legibility (alpha = 0.5, b = 2, N = 4).  The relation holds for
    every alpha > 0.
  * This is the tree's isotropic subspace, and the tree closure is DRIVEN -- see the companion
    figure.  Nothing here is a blow-up result.

USAGE

    ./.venv-plotting/bin/python Cascade/plot_isotropic_helix.py

Writes Cascade/isotropic_helix.svg and Cascade/isotropic_helix.png next to this script.
Unlike the other figures in this repository this one needs numpy and matplotlib (see the
note in CLOSURE.md Sec. 4.2); a repo-local venv provides them.
"""

import os
import sys

# Matplotlib and fontconfig both want writable cache directories; point them somewhere safe
# BEFORE importing matplotlib, or the run emits warnings and can be slow.
for _v in ("MPLCONFIGDIR", "XDG_CACHE_HOME"):
    os.environ.setdefault(_v, "/tmp/mplcache")
os.makedirs(os.environ["MPLCONFIGDIR"], exist_ok=True)
os.makedirs(os.environ["XDG_CACHE_HOME"], exist_ok=True)

import numpy as np
import matplotlib
matplotlib.use("Agg")
# Matplotlib derives SVG element ids from a salted hash, so two runs produce byte-different
# files unless the salt is pinned.  Every other figure in this repository is deterministic;
# this one must be too.
matplotlib.rcParams["svg.hashsalt"] = "isotropic-helix"
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D  # noqa: F401  (registers the 3d projection)

ALPHA, B, N = 0.15, 2, 4
MU = 2.0 ** ALPHA
TURNS = 3

INK = "#252525"
BLUE = "#1f4e79"
RED = "#b03030"
GREEN = "#2e7d32"
GREY = "#6b6b6b"
LBLUE = "#dce9f7"
FAIL = []


def check(name, ok, detail=""):
    if not ok:
        FAIL.append(name)
    print(f"  [{'ok  ' if ok else 'FAIL'}] {name}{('  ' + detail) if detail else ''}")


def main():
    # --- the geometry ----------------------------------------------------------------
    # one level per step; a turn per N levels; radius falls by mu^{-1} per level
    n = np.linspace(0.0, TURNS * N, 48 * TURNS * N + 1)
    theta = 2.0 * np.pi * n / N                      # one full turn every N levels
    R = 1.0 + 0.25 * np.cos(2.0 * np.pi * n / N)     # ILLUSTRATIVE periodic reduced profile
    X = MU ** (-n) * R                               # the exact scaling relation
    x, y = X * np.cos(theta), X * np.sin(theta)
    zmax = TURNS * N

    fig = plt.figure(figsize=(13.6, 7.4), dpi=110)

    # ---- header: title block LEFT, relation block RIGHT (kept clear of each other) ----
    fig.text(0.030, 0.975, "The rope loops back onto itself",
             color=INK, fontsize=19, weight="bold", va="top")
    fig.text(0.030, 0.925, "— up to a twist",
             color=INK, fontsize=19, weight="bold", va="top")
    fig.text(0.030, 0.872,
             f"$\\alpha={ALPHA}$, $b={B}$, $N={N}$:  one turn per $N$ levels,"
             f"\nradius $\\times\\mu^{{-1}}$ per level.  $\\mu=2^{{\\alpha}}$ is FORCED.",
             color=GREY, fontsize=12, va="top")

    fig.text(0.470, 0.975, "the identification is SCALED, not periodic",
             color=INK, fontsize=14.5, weight="bold", va="top")
    fig.text(0.470, 0.926,
             "$X_{n+N}\;=\;\\mu^{-N}\\,X_n$",
             color=BLUE, fontsize=17, va="top")
    fig.text(0.470, 0.872,
             "In the reduced variable it really is a circle:  $R_{n+N}=R_n$.",
             color=INK, fontsize=12, va="top")
    fig.text(0.470, 0.832,
             "So the rope closes — up to the twist.  That twist IS the\n"
             "self-similarity:  $u_{k+N}=2^{-N}u_k$  (CLOSURE.md \u00a71.2).",
             color=INK, fontsize=12, va="top")

    # ---- panel A: the helix ---------------------------------------------------------
    ax = fig.add_axes([0.020, 0.075, 0.455, 0.700], projection="3d")
    # the spine and the radial spokes make the radius visible, so the coil reads as a coil
    ax.plot([0, 0], [0, 0], [0, zmax], lw=1.0, color=GREY, ls=(0, (3, 3)))
    for k in range(TURNS + 1):
        i = int(round(k * N * 48))
        ax.plot([0, x[i]], [0, y[i]], [n[i], n[i]], lw=0.9, color=GREY, ls=(0, (2, 3)))
    ax.plot(x, y, n, lw=2.6, color=BLUE, solid_capstyle="round")
    for k in range(TURNS + 1):
        i = int(round(k * N * 48))
        ax.scatter([x[i]], [y[i]], [n[i]], s=62, color=RED, depthshade=False, zorder=6)
        ax.text(x[i], y[i], n[i] + 0.30, f"$X_{{{k*N}}}$", color=RED, fontsize=12.5,
                ha="center", va="bottom")
    ax.set_axis_off()
    ax.view_init(elev=24, azim=-56)
    lim = 1.12
    ax.set_xlim(-lim, lim); ax.set_ylim(-lim, lim); ax.set_zlim(0, zmax)
    ax.set_box_aspect((1.0, 1.0, 1.25))
    ax.set_title("the physical object:  $X_n=\\mu^{-n}R_n$", color=INK, fontsize=14, pad=0)
    ax.text2D(0.00, 0.005,
              "one turn per $N$ levels.  After a turn the radius is $\\mu^{-N}$\n"
              "of what it was: the ends do NOT meet — they meet UP TO SCALE.",
              transform=ax.transAxes, color=INK, fontsize=11.5, va="bottom")

    # ---- panel B: looking down the axis --------------------------------------------
    bx = fig.add_axes([0.505, 0.075, 0.235, 0.700])
    tt = np.linspace(0, 2 * np.pi, 400)
    for k in range(TURNS + 1):
        rad = MU ** (-k * N)
        bx.plot(rad * np.cos(tt), rad * np.sin(tt), lw=2.1, color=BLUE,
                alpha=0.22 + 0.78 * (1 - k / (TURNS + 2)))
        bx.scatter([rad], [0], s=64, color=RED, zorder=6)
    bx.plot([0, 1.08], [0, 0], lw=0.9, color=GREY, ls=(0, (4, 4)))
    bx.text(1.12, 0.04, "$X_0$", color=RED, fontsize=12.5, va="center")
    bx.text(MU ** (-N) * 0.62, -0.30, "$X_N=\\mu^{-N}X_0$", color=RED, fontsize=12.5, ha="left")
    bx.set_xlim(-1.55, 1.55); bx.set_ylim(-1.55, 1.55)
    bx.set_aspect("equal"); bx.axis("off")
    bx.text(0.0, -1.44, "seen down the axis: concentric rings,\neach turn smaller.",
            color=INK, fontsize=11.5, ha="center", va="top")
    bx.text(0.0, -1.90, "a circle would retrace\nthe SAME ring.",
            color=RED, fontsize=11.5, ha="center", va="top")

    # ---- right-hand notes (lines kept short: the column is only ~0.24 wide) ----------
    fig.text(0.757, 0.700, "what the picture says", color=INK, fontsize=12.5, weight="bold",
             va="top")
    fig.text(0.757, 0.666,
             "\u2022  $R$ is periodic in the\n"
             "    index; $X$ is not.\n"
             "\u2022  each turn multiplies $X$\n"
             "    by $\\mu^{-N}$.\n"
             "\u2022  that rescaling IS the\n"
             "    self-similarity.\n"
             "\u2022  the coil never retraces\n"
             "    itself; a circle would.",
             color=INK, fontsize=10.5, va="top")
    fig.text(0.757, 0.430, "what it does NOT say", color=INK, fontsize=12.5, weight="bold",
             va="top")
    fig.text(0.757, 0.396,
             "\u2022  not a circle, and not\n"
             "    closed at fixed scale.\n"
             "\u2022  the tree's closure is\n"
             "    DRIVEN: the closing\n"
             "    edge is $f=2^{\\alpha N}X_{N-1}$.\n"
             "\u2022  $R_n$ here is illustra-\n"
             "    tive; only $X_{n+N}=\\mu^{-N}X_n$\n"
             "    is exact.",
             color=INK, fontsize=10.5, va="top")

    # ---- footnote -------------------------------------------------------------------
    fig.text(0.030, 0.062,
             "exact:  $X_{n+N}=\\mu^{-N}X_n$, and $\\mu=2^{\\alpha}$ forced  "
             "(Cascade/zeta_checks.py \u00a7K).",
             color=GREY, fontsize=9.5, va="top")
    fig.text(0.030, 0.034,
             "illustrative:  the profile $R_n$ and the parameters above — "
             "the relation holds for every $\\alpha>0$.",
             color=GREY, fontsize=9.5, va="top")
    fig.text(0.560, 0.062,
             "record panels:  Cascade/isotropic_closure.svg",
             color=GREY, fontsize=9.5, va="top")
    fig.text(0.560, 0.034,
             "(braid \u2192 rope \u2192 twist \u2192 knot)",
             color=GREY, fontsize=9.5, va="top")

    here = os.path.dirname(os.path.abspath(__file__))
    svg = os.path.join(here, "isotropic_helix.svg")
    png = os.path.join(here, "isotropic_helix.png")
    fig.savefig(svg, format="svg", metadata={"Date": None})   # no date -> deterministic
    fig.savefig(png, format="png", dpi=150)
    print(f"wrote {svg}")
    print(f"wrote {png}")

    # --- self-checks -----------------------------------------------------------------
    print("self-checks:")
    check("mu^{-N} is the per-turn scale factor", abs(MU ** (-N) - 2.0 ** (-ALPHA * N)) < 1e-15,
          f"alpha={ALPHA}, N={N} -> mu^-N = {MU ** (-N):.6f}")
    # the scaling relation, exactly as drawn
    nn = np.arange(0, 2 * N)
    Rv = 1.0 + 0.25 * np.cos(2.0 * np.pi * nn / N)
    Xv = MU ** (-nn) * Rv
    lhs = MU ** (-(nn + N)) * np.roll(Rv, -N)
    check("X_{n+N} == mu^{-N} X_n on the drawn profile",
          np.allclose(lhs, MU ** (-N) * Xv, rtol=0, atol=1e-15))
    check("X is NOT N-periodic (a circle would be)",
          not np.allclose(Xv[:N], Xv[N:2 * N]))
    check("R IS N-periodic",
          np.allclose(Rv[:N], np.roll(Rv, -N)[:N], atol=1e-15))
    check("successive turns sit at radii differing by exactly mu^{-N}",
          all(abs(MU ** (-(k + 1) * N) / MU ** (-k * N) - MU ** (-N)) < 1e-15
              for k in range(TURNS)),
          f"per-turn factor = {MU ** (-N):.6f}")
    check("the record figure it accompanies is on disk",
          os.path.exists(os.path.join(here, "plot_isotropic_closure.py")))
    if FAIL:
        print(f"RESULT: FAIL - {len(FAIL)}")
        return 1
    print("RESULT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
