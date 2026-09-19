#!/usr/bin/env python3
r"""Isotropy closes the tree -- but only as a DRIVEN cycle, and only R is periodic.

Companion to plot_ring_invariants.py and plot_dyadic_ring.py, on the same typographic and
layout discipline.  It draws one structural result about the tree cascade of
Barbato-Bianchi-Flandoli-Morandin, arXiv:1207.2846, recorded in Cascade/CLOSURE.md Sec. 4.2
in the block the document itself heads "Corrigendum (added later)":

  * The tree has NO finite quotient as a graph -- the per-generation node counts
    (1, b, b^2, ...) are not equinumerous, so nothing bijects generation n to generation
    n+N; and any level-preserving graph automorphism fixes the root and descends, so its
    quotient on levels is infinite.  (CLOSURE.md Sec. 3.1, 3.2.)
  * Node-wise ISOTROPY, X_j = mu^{-|j|} R_{|j|}, is a forward-invariant SUBSPACE on which
    the tree collapses to one scalar recurrence in the generation amplitudes.  That is a
    bundling of a level into one value -- NOT a quotient of the tree.
  * Substituting the ansatz makes the two chain coefficients
        A_n = 2^{an} mu^{2-n},     B_n = b 2^{a(n+1)} mu^{-(n+1)}
    both independent of n if and only if mu = 2^a -- a FORCED value, not a choice.  Then
        Rdot_n = 4^a R_{n-1}^2 - b R_n R_{n+1}     on Z/N,   R_{n+N} = R_n,
    a finite cyclic system; at b = 1 (alpha = 1) this is exactly the repo's dyadic ring
    q_k' = 4 q_{k-1}^2 - q_k q_{k+1} of CLOSURE.md Sec. 1.3.
  * WHAT IS PERIODIC IS R, NOT X.  The physical identification is the SCALED one
    X_{n+N} = mu^{-N} X_n.  So the physical object is a spiral that closes only up to a
    scale factor, and the reduced variable R is the thing that closes into a genuine
    circle.  The figure draws both and says which is which.
  * KNOT.  The cycle needs its closing edge N-1 -> 0.  For the chain (b = 1) the index set
    is Z, which has no root, so that edge is already in the lattice and the ring is
    UNFORCED.  For the tree (b >= 2) generation 0 IS a root, so the edge must be SUPPLIED:
    f = mu R_{N-1} = 2^{aN} X_{N-1}.  The isotropic periodic tree is therefore a DRIVEN
    cycle -- finite-dimensional and closed, but driven.  This is the honest caveat and the
    one thing a reader is most likely to get wrong, so it is drawn twice.

WHAT IS EXACT HERE ON THE FIGURE.  Every equation, both coefficient identities, the
iff-condition on mu, the reduced cyclic system, the drive f, the constant mode and its
marginality at 4^a = b are exact-rational statements about the tree equation.  They are
labelled [proved] on the figure in the sense of CLOSURE.md's label table ("proved -- exact
computation", Cascade/zeta_checks.py section K, no floating point), or [derived] where they
are elementary algebra done in the figure's own arithmetic.  The tree equation itself is
[sourced -- arXiv:1207.2846 Sec. 2, eqs. (7), (8), (17)].  Nothing on the figure is a
floating-point measurement.

WHAT IS NOT CLAIMED.  This is NOT a closure of the tree as a graph: CLOSURE.md Sec. 3.2 (no
graph quotient) is untouched by anything drawn here.  The word "closure" on the figure
always means "closure on the isotropic invariant subspace".

SCOPE NOTES THE FIGURE ITSELF CARRIES, in the caveats box:
  1. No graph quotient (Sec. 3.2 untouched).  The bundle is a projection onto a subspace.
  2. The tree closure is DRIVEN; the chain closure is UNFORCED.
  3. mu = 2^a is forced, not chosen.
  4. The "exactly the ring at b = 1" identity is at alpha = 1 (the doc's Sec. 1.3 uses
     u_k = 2^{-k} q_k, which fixes alpha = 1).  For general alpha the same equation
     carries 4^a in place of 4; rescaling time by 4^{a-1} restores the exact form.  The
     CLOSURE.md Sec. 4.2 corrigendum states the b = 1 identity without that proviso.
  5. The constants A_n, B_n collapse only for alpha > 0 (equivalently mu = 2^a > 1).  At
     alpha = 0 the forced value is mu = 1 and both coefficients are constant while the
     ratio B_n/A_n = b mu^{-3} = b, so "iff" can fail there in a degenerate gauge.  Every
     case verified in zeta_checks.py section K has alpha > 0, and the figure states
     alpha > 0.
  6. Marginality is a statement about the constant mode of the REDUCED cycle.  It is not
     the withdrawn criterion: ZETA.md Sec. 6.3b' withdrew "mu^3 > b 2^a" because mu is a
     gauge parameter (it cancels from physical quantities) and because the constant
     profile is not a solution of the UNFORCED rooted model.  That withdrawal stands and
     is drawn on the figure.  What is correct in this frame is the reduced coefficient
     4^a - b.

Layout.  The generator registers every string it draws (text()/para()), refuses to emit an
SVG whose text leaves the canvas margin, overlaps another registered string, or collides
with a registered diagram node or bead; any failure exits 3 and emits nothing.  A new label
must go through text()/para().

Standard library only; deterministic; emits SVG on stdout.  Regenerate with:

    python3 plot_isotropic_closure.py > isotropic_closure.svg
    rsvg-convert -w 1800 -o isotropic_closure.png isotropic_closure.svg
"""
import sys, math

W, H = 1500, 2850
BG = "#ffffff"
INK = "#252525"; GREY = "#737373"; MGREY = "#bdbdbd"; LGREY = "#f4f4f4"
BLUE = "#08519c"; LBLUE = "#c6dbef"
RED = "#a50f15"; LRED = "#fcbba1"
GREEN = "#238b45"; LGREEN = "#d9f0d3"
PURPLE = "#6a51a3"; LPURPLE = "#dadaeb"
ORANGE = "#d94801"; LORANGE = "#fee6ce"
WALL = "#969696"
YTINT = "#fffdf2"; YTINT2 = "#fffaf6"

PAD = 30                                   # canvas margin
o = []
def esc(s):
    return s.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')

MARK = {'ink': INK, 'grey': GREY, 'blue': BLUE, 'red': RED, 'green': GREEN,
        'purple': PURPLE, 'orange': ORANGE}
MID = {'ink': 'm_ink', 'grey': 'm_grey', 'blue': 'm_blue', 'red': 'm_red',
       'green': 'm_green', 'purple': 'm_purple', 'orange': 'm_orange'}

def defs():
    s = ['<defs>']
    for k, c in MARK.items():
        s.append(f'<marker id="{MID[k]}" viewBox="0 0 10 10" refX="8.5" refY="5" '
                 f'markerWidth="6.5" markerHeight="6.5" orient="auto-start-reverse">'
                 f'<path d="M 0 0 L 10 5 L 0 10 z" fill="{c}"/></marker>')
    s.append('<pattern id="hatch" width="14" height="14" patternUnits="userSpaceOnUse" '
             'patternTransform="rotate(45)">'
             f'<line x1="0" y1="0" x2="0" y2="14" stroke="{WALL}" stroke-width="3"/></pattern>')
    s.append('</defs>')
    return ''.join(s)

# ---------------------------------------------------------------------------
# text -- markup with _{...} subscripts and ^{...} superscripts, exactly as
# plot_ring_invariants.py does it, so the figures share a typographic voice.
# ---------------------------------------------------------------------------
def _segs(markup):
    segs = []; i = 0
    while i < len(markup):
        c = markup[i]
        if c in '_^' and i + 1 < len(markup) and markup[i + 1] == '{':
            j = markup.index('}', i + 2)
            segs.append(('sub' if c == '_' else 'sup', markup[i + 2:j]))
            i = j + 1
        else:
            j = i
            while j < len(markup) and not (markup[j] in '_^' and j + 1 < len(markup)
                                           and markup[j + 1] == '{'):
                j += 1
            segs.append(('n', markup[i:j])); i = j
    return segs

def rich(x, y, markup, size=14, anchor='middle', fill=INK, weight='normal',
         opacity=1.0, rotate=None):
    segs = _segs(markup); cur = 0; parts = []
    for kind, t in segs:
        if t == '':
            continue
        t = t.replace(' ', '\u00a0')
        target = 0 if kind == 'n' else (4 if kind == 'sub' else -6)
        fs = size if kind == 'n' else size * 0.68
        dy = target - cur
        parts.append(f'<tspan font-size="{fs:.1f}" dy="{dy:.1f}">{esc(t)}</tspan>')
        cur = target
    rot = f' transform="rotate({rotate:.1f} {x} {y})"' if rotate is not None else ''
    return (f'<text x="{x}" y="{y}" text-anchor="{anchor}" fill="{fill}" font-weight="{weight}" '
            f'opacity="{opacity}" font-family="Helvetica, Arial, sans-serif"{rot}>'
            + ''.join(parts) + '</text>')

# ---------------------------------------------------------------------------
# approximate text metrics -- used ONLY to wrap text and to CHECK bounds
# ---------------------------------------------------------------------------
class _W:
    NARROW = ".,:;'|!ijltfr()[]-"
    WIDE = "MWmw@"
    UPPER = "ABCDEFGHIJKLNOPQRSTUVXYZ"
    def __init__(self):
        self.c = {}
    def __call__(self, s):
        if s not in self.c:
            t = 0.0
            for ch in s:
                if ch in '\u00a0 ':
                    t += 0.34
                elif ch.isdigit():
                    t += 0.55
                elif ch in '−+':
                    t += 0.60
                elif ch == '×':
                    t += 0.62
                elif ch == '≤':
                    t += 0.62
                elif ch in self.NARROW:
                    t += 0.34
                elif ch in self.WIDE:
                    t += 0.95
                elif ch in self.UPPER:
                    t += 0.70
                elif ch in 'Σ∈≡≈→ℚℝℤλ′':
                    t += 0.70
                else:
                    t += 0.565
            self.c[s] = t
        return self.c[s]
_w = _W()

def tw(s, size):
    return _w(s) * size

def w_rich(markup, size):
    return sum(_w(t) * (size if k == 'n' else size * 0.68) for k, t in _segs(markup) if t)

def wrap(text, size, maxw):
    lines = []
    for para in text.split('\n'):
        cur = ''
        for word in para.split(' '):
            trial = word if not cur else cur + ' ' + word
            if cur and tw(trial, size) > maxw:
                lines.append(cur); cur = word
            else:
                cur = trial
        lines.append(cur)
    return lines

_CHECK = []        # registered text boxes
_OBST = []         # registered diagram primitives (nodes / beads) as (x, y, r, name)

def text(x, y, markup, size=14, anchor='start', fill=INK, weight='normal'):
    """draw + register a bounds check against the canvas margin and the obstacles"""
    w = w_rich(markup, size)
    left = x if anchor == 'start' else (x - w if anchor == 'end' else x - w / 2)
    _CHECK.append((left, left + w, y - size * 0.78, y + size * 0.26, markup[:44]))
    return rich(x, y, markup, size=size, anchor=anchor, fill=fill, weight=weight)

def para(x, y, body, size, maxw, fill=INK, lh=None, weight='normal'):
    """wrapped paragraph; returns the markup.  Use nlines() for the height."""
    lh = lh or size * 1.45
    lines = wrap(body, size, maxw)
    return ''.join(text(x, y + i * lh, ln, size=size, fill=fill, weight=weight)
                   for i, ln in enumerate(lines))

def nlines(body, size, maxw):
    return len(wrap(body, size, maxw))

# ---------------------------------------------------------------------------
# primitives
# ---------------------------------------------------------------------------
def line(x1, y1, x2, y2, stroke=INK, sw=2, dash=None, opacity=1.0, cap='round'):
    d = f' stroke-dasharray="{dash}"' if dash else ''
    return (f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="{stroke}" stroke-width="{sw}" '
            f'stroke-linecap="{cap}"{d} opacity="{opacity}"/>')

def arrow(x1, y1, x2, y2, color='ink', sw=2, dash=None, opacity=1.0):
    d = f' stroke-dasharray="{dash}"' if dash else ''
    return (f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="{MARK[color]}" stroke-width="{sw}" '
            f'stroke-linecap="round" marker-end="url(#{MID[color]})"{d} opacity="{opacity}"/>')

def carrow(x1, y1, cx, cy, x2, y2, color='ink', sw=2, dash=None, opacity=1.0):
    d = f' stroke-dasharray="{dash}"' if dash else ''
    return (f'<path d="M {x1} {y1} Q {cx} {cy} {x2} {y2}" fill="none" stroke="{MARK[color]}" '
            f'stroke-width="{sw}" stroke-linecap="round" '
            f'marker-end="url(#{MID[color]})"{d} opacity="{opacity}"/>')

def qpath(x1, y1, cx, cy, x2, y2, color='ink', sw=2, dash=None, opacity=1.0, arrow_end=False):
    d = f' stroke-dasharray="{dash}"' if dash else ''
    m = f' marker-end="url(#{MID[color]})"' if arrow_end else ''
    return (f'<path d="M {x1} {y1} Q {cx} {cy} {x2} {y2}" fill="none" stroke="{MARK[color]}" '
            f'stroke-width="{sw}" stroke-linecap="round"{d}{m} opacity="{opacity}"/>')

def poly(pts, color='ink', sw=2, dash=None, opacity=1.0, arrow_end=False, fill='none'):
    d = f' stroke-dasharray="{dash}"' if dash else ''
    m = f' marker-end="url(#{MID[color]})"' if arrow_end else ''
    body = 'M ' + ' L '.join(f'{x:.1f} {y:.1f}' for x, y in pts)
    return (f'<path d="{body}" fill="{fill}" stroke="{MARK[color]}" stroke-width="{sw}" '
            f'stroke-linecap="round" stroke-linejoin="round"{d}{m} opacity="{opacity}"/>')

def circle(cx, cy, r, fill=LBLUE, stroke=BLUE, sw=2, dash=None, opacity=1.0):
    d = f' stroke-dasharray="{dash}"' if dash else ''
    return (f'<circle cx="{cx}" cy="{cy}" r="{r}" fill="{fill}" stroke="{stroke}" '
            f'stroke-width="{sw}"{d} opacity="{opacity}"/>')

def ellipse(cx, cy, rx, ry, fill='none', stroke=MGREY, sw=1.5, dash=None, opacity=1.0):
    d = f' stroke-dasharray="{dash}"' if dash else ''
    return (f'<ellipse cx="{cx}" cy="{cy}" rx="{rx}" ry="{ry}" fill="{fill}" '
            f'stroke="{stroke}" stroke-width="{sw}"{d} opacity="{opacity}"/>')

def rect(x, y, w, h, fill='none', stroke=MGREY, sw=1.5, rx=14, dash=None, opacity=1.0):
    d = f' stroke-dasharray="{dash}"' if dash else ''
    return (f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="{rx}" fill="{fill}" '
            f'stroke="{stroke}" stroke-width="{sw}"{d} opacity="{opacity}"/>')

def dot(x, y, r, fill=BLUE, stroke=BLUE, sw=1.2, name=''):
    """a diagram node / bead: drawn AND registered as a text obstacle"""
    _OBST.append((x, y, r, name))
    return circle(x, y, r, fill=fill, stroke=stroke, sw=sw)

def clock_node(x, y, r, label, fill=LBLUE, stroke=BLUE, tcol=BLUE, fs=15):
    return dot(x, y, r, fill=fill, stroke=stroke, name=label) \
        + rich(x, y + fs * 0.35, label, size=fs, fill=tcol)

def panel(x, y, w, h, title, sub='', fill=BG):
    s = [rect(x, y, w, h, fill=fill, stroke=MGREY, sw=1.5, rx=16)]
    if title:
        s.append(text(x + 26, y + 34, title, size=20, weight='bold'))
    if sub:
        s.append(text(x + 30, y + 62, sub, size=13.5, fill=GREY))
    return ''.join(s)

def step(P, Q, shrink):
    dx, dy = Q[0] - P[0], Q[1] - P[1]
    L = math.hypot(dx, dy)
    ux, uy = dx / L, dy / L
    return (P[0] + ux * shrink, P[1] + uy * shrink), (Q[0] - ux * shrink, Q[1] - uy * shrink)

def down_arrow(x, ytop, ybot, color='blue', sw=2.0):
    return arrow(x, ytop, x, ybot, color=color, sw=sw)

# ===========================================================================
o.append(f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" '
         f'viewBox="0 0 {W} {H}">')
o.append(defs())
o.append(f'<rect width="{W}" height="{H}" fill="{BG}"/>')

# ---- masthead --------------------------------------------------------------
o.append(rich(750, 50, "Isotropy closes the tree —", size=29, weight='bold'))
o.append(rich(750, 84, "but only as a driven cycle, and only R is periodic",
              size=29, weight='bold'))
o.append(rich(750, 112, "the branching number survives only as a coefficient;  the tree "
                        "itself is never quotiented", size=15, fill=GREY))

# ---- equation strip + label legend -----------------------------------------
o.append(rect(60, 132, 1380, 80, fill=LGREY, stroke=MGREY, sw=1.2, rx=12))
o.append(rich(750, 164, "tree equation:   Ẋ_{n} = 2^{αn}·X_{n−1}^{2} − b·2^{α(n+1)}·X_{n}"
                        "·X_{n+1}      on every node of generation n", size=17))
o.append(rich(750, 194, "b = branching number   α = time-scale exponent   μ = isotropy rate   "
                        "N = period   α̃ = ½·log_{2}b   f = the root's parent-alias (its "
                        "phantom parent)", size=12.5, fill=GREY))
o.append(rect(60, 220, 1380, 32, fill=BG, stroke=MGREY, sw=1.2, rx=10))
o.append(text(74, 242, "claims on this figure:", size=12, weight='bold', fill=INK))
tx = 244
for tag, why, col in [("[proved]", "exact computation, Cascade/zeta_checks.py §K", GREEN),
                      ("[sourced]", "arXiv:1207.2846 §2", BLUE),
                      ("[derived]", "elementary algebra", PURPLE),
                      ("[exact]", "exact arithmetic, no floating point", ORANGE)]:
    o.append(text(tx, 242, tag, size=12, weight='bold', fill=col))
    tx += tw(tag, 12) + 7
    o.append(text(tx, 242, why, size=11, fill=GREY))
    tx += tw(why, 11) + 24

# ===========================================================================
# BEAT 1  BRAID
# ===========================================================================
AY, AH = 272, 400
o.append(panel(PAD, AY, 1440, AH,
               "1.  BRAID — a tree that is rooted and not equinumerous"))
o.append(rich(1440, AY + 34, "b = 2, generations 0..3, drawn", size=12.5,
              anchor='end', fill=GREY))

LROOT = 560.0
LSTEP = 86.0
LPOS = [AY + 80.0, AY + 150.0, AY + 220.0, AY + 290.0]
LEVELS = []
for n in range(4):
    cnt = 1 << n
    span = LSTEP * (cnt - 1)
    LEVELS.append([(LROOT - span / 2.0 + i * LSTEP, LPOS[n]) for i in range(cnt)])
for n in range(3):
    for (x, y) in LEVELS[n]:
        for (cx, cy) in LEVELS[n + 1]:
            if abs(cx - x) < LSTEP * 0.6:
                o.append(line(x, y, cx, cy, stroke=WALL, sw=1.7, opacity=0.95))
for n, pts in enumerate(LEVELS):
    for (x, y) in pts:
        o.append(dot(x, y, 8.0, fill=LBLUE, stroke=BLUE, sw=2.0, name=f'node n={n}'))
o.append(text(160, AY + 320, "level-size  (strands)   1     2     4     8     —  b^{n} at "
                             "level n: the sizes never repeat for b ≥ 2", size=12.5,
              fill=BLUE))
o.append(text(160, AY + 344, "generation 0 is the ROOT: it has no parent, and 8 strands sit "
                             "at the bottom", size=12.5, fill=GREY))

o.append(text(880, AY + 80, "b = 2, generations 0..3 drawn;  the sizes grow as 1, 2, 4, 8",
              size=12.5, fill=GREY))
o.append(text(880, AY + 106, "the obstruction", size=14, weight='bold', fill=RED))
o.append(text(880, AY + 128, "a level-n set has b^{n} nodes, so the sizes 1, b, b^{2}, … are "
                             "not equinumerous for b ≥ 2.", size=12.5))
o.append(text(880, AY + 148, "A level SHIFT |γj| = |j| + N is therefore impossible, and a "
                             "level-PRESERVING", size=12.5))
o.append(text(880, AY + 168, "group gives an infinite quotient: the level function descends "
                             "to it.", size=12.5))
o.append(text(880, AY + 188, "Hence no closure of the tree as a graph.  "
                             "[derived — CLOSURE.md §3.1, §3.2]", size=12.5, fill=PURPLE))

# ===========================================================================
# BEAT 2  ROPE
# ===========================================================================
BY, BH = 692, 400
o.append(panel(PAD, BY, 1440, BH,
               "2.  ROPE — isotropy bundles each generation into ONE value",
               "the isotropy ansatz is a bundling of a level, not a quotient of the tree"))
o.append(rich(1440, BY + 34, "a bundling, not a quotient", size=12.5,
              anchor='end', fill=GREEN))

CONV = [0.34, 0.26, 0.20, 0.155]
LP2 = [BY + 82.0, BY + 152.0, BY + 222.0, BY + 292.0]
GATH = [[(LROOT + (x - LROOT) * CONV[n], LP2[n]) for (x, y) in pts]
        for n, pts in enumerate(LEVELS)]
for n in range(4):
    xs = [X for (X, Y) in GATH[n]]
    o.append(line(min(xs) - 4, LP2[n], max(xs) + 4, LP2[n], stroke=GREEN, sw=7,
                  opacity=0.35))
for n in range(3):
    for i, (sx, sy) in enumerate(GATH[n]):
        for j, (cx, cy) in enumerate(GATH[n + 1]):
            if j // 2 == i:
                o.append(line(sx, sy, cx, cy, stroke=WALL, sw=1.7, opacity=0.95))
for n, pts in enumerate(GATH):
    for (x, y) in pts:
        o.append(dot(x, y, 8.0, fill=LGREEN, stroke=GREEN, sw=2.0, name=f'bundle n={n}'))
for n in range(4):
    xs = [X for (X, Y) in GATH[n]]
    lx = sum(xs) / len(xs)
    o.append(rect(lx - 20, LP2[n] + 30, 40, 19, fill=BG, stroke='none', sw=0, rx=5))
    o.append(text(lx, LP2[n] + 44, f"R_{n}", size=14, weight='bold',
                  fill=GREEN, anchor='middle'))
o.append(text(160, BY + 106, "one value per level — b^{n} nodes bundled onto one value, "
                             "none of them deleted", size=12.5, fill=GREEN))

o.append(text(880, BY + 80, "the bundling", size=14, weight='bold', fill=GREEN))
o.append(text(880, BY + 104, "isotropy:  every node at a level shares one amplitude, "
                             "X_{j} = μ^{−|j|}R_{|j|}.", size=12.5))
o.append(text(880, BY + 126, "Substituting, no angular variable appears, so the isotropic "
                             "set is FORWARD INVARIANT.", size=12.5))
o.append(text(880, BY + 148, "This is a projection onto an invariant SUBSPACE — now one "
                             "value per level, so the", size=12.5))
o.append(text(880, BY + 168, "levels are effectively equinumerous.  [derived — §3.2 is "
                             "untouched: no graph quotient.]", size=12.5, fill=PURPLE))

# ===========================================================================
# BEAT 3  TWIST
# ===========================================================================
CY3, CH3 = 1112, 480
o.append(panel(PAD, CY3, 1440, CH3,
               "3.  TWIST — μ = 2^{α} is forced, and the levels collapse to constants",
               "the reduced variable R closes into a circle;  the physical X does not"))
o.append(rich(1440, CY3 + 34, "both coefficients, n-independent", size=12.5,
              anchor='end', fill=BLUE))

o.append(text(60, CY3 + 92, "substituting the ansatz  X_{n} = μ^{−n}R_{n},  the two chain "
                            "coefficients are", size=13.5, weight='bold'))
o.append(text(60, CY3 + 114, "A_{n} = 2^{αn}μ^{2−n}     B_{n} = b·2^{α(n+1)}μ^{−(n+1)}     "
                             "A_{n}, B_{n} both independent of n  ⟺  μ = 2^{α}   (α > 0)",
              size=13.5, fill=BLUE))
o.append(text(60, CY3 + 136, "μ is FORCED, not chosen — and then  Ṙ_{n} = 4^{α}R_{n−1}^{2} − "
                             "b·R_{n}R_{n+1}  on ℤ/N.", size=12.5, fill=GREY))

# --- reduced circle (R) ---
RCX, RCY, RR = 262.0, CY3 + 330.0, 100.0
o.append(ellipse(RCX, RCY, RR, RR, fill="none", stroke=MGREY, sw=1.2, dash="5 6",
                 opacity=0.85))
o.append(circle(RCX, RCY, RR, fill='none', stroke=BLUE, sw=1.8, dash="8 6",
                opacity=0.5))
o.append(text(RCX, RCY - RR - 24, "R — the reduced variable", size=13, weight='bold',
              fill=BLUE, anchor='middle'))
o.append(text(RCX, RCY + RR + 26, "a genuine circle: R_{n+N} = R_{n}   [exact]", size=12.5,
              fill=BLUE, anchor='middle'))
for i in range(6):
    th = math.pi / 2.0 - 2.0 * math.pi * i / 6.0
    bx, by = RCX + RR * math.cos(th), RCY - RR * math.sin(th)
    o.append(clock_node(bx, by, 13.0, f"{i}", fill=LBLUE, stroke=BLUE, tcol=BLUE, fs=13))
bx0, by0 = RCX, RCY - RR
bx5, by5 = RCX + RR * math.cos(math.pi / 2.0 - 5.0 * math.pi / 3.0), \
           RCY - RR * math.sin(math.pi / 2.0 - 5.0 * math.pi / 3.0)
mx, my = (bx0 + bx5) / 2.0, (by0 + by5) / 2.0
mx, my = RCX + (mx - RCX) * 0.74, RCY + (my - RCY) * 0.74
o.append(text(mx + 4, my + 4, "N", size=12.5, weight='bold', fill=RED, anchor='middle'))
o.append(text(RCX, RCY + 5, "n mod N", size=12.5, fill=BLUE, anchor='middle'))
o.append(carrow(490, RCY, 570, RCY + 26, 650, RCY, color='grey', sw=1.6))
o.append(rect(532, RCY - 19, 80, 25, fill=BG, stroke="none", sw=0, rx=4))
o.append(text(572, RCY - 1, "× μ^{n}", size=12.5, weight='bold', fill=BLUE,
              anchor='middle'))

# --- physical spiral (X) ---
o.append(text(920, RCY - 100 - 24, "X — the physical variable", size=13, weight='bold',
              fill=ORANGE, anchor='middle'))
o.append(line(680, RCY, 1440, RCY, stroke=GREY, sw=1.2, dash="6 6", opacity=0.7))
pts = []
BEADS = []
for k in range(241):
    t = 6.0 * k / 240.0
    spx = 820.0 + t * 103.0
    spy = RCY - 90.0 * math.sin(2.0 * math.pi * t / 3.0)
    pts.append((spx, spy))
    if k % 40 == 0:
        BEADS.append((spx, spy, k // 40))
o.append(poly(pts, color='orange', sw=2.4, opacity=0.95))
for bx, by, i in BEADS:
    col = RED if i == 6 else ORANGE
    o.append(dot(bx, by, 7.5, fill=LRED, stroke=col, sw=1.6, name=f'X bead {i}'))
for bx, by, i in BEADS:
    if i == 0:
        o.append(text(bx - 12, by + 5, "X_{0}", size=12.5, fill=ORANGE, anchor='end'))
    elif i == 5:
        o.append(text(bx, by + 36, "X_{N−1}", size=12.5, fill=ORANGE, anchor='middle'))
    elif i == 6:
        o.append(text(1440, by - 104, "X_{N} = μ^{−N}·X_{0} — the same node, scaled:",
                      size=12.5, fill=RED, anchor='end'))
        o.append(text(1440, by - 84, "it does NOT come back to X_{0}",
                      size=12.5, fill=RED, anchor='end'))
o.append(text(920, RCY - 104, "a spiral, not a circle", size=12.5, fill=ORANGE,
              anchor='middle'))
o.append(text(880, CY3 + 440, "Ṙ_{n} = 4^{α}R_{n−1}^{2} − b·R_{n}R_{n+1}   on ℤ/N   "
                              "[proved — exact, §K]", size=12.5, fill=GREEN))
o.append(text(880, CY3 + 462, "What is periodic is R, NOT X:  X_{n+N} = μ^{−N}X_{n}   [exact]",
              size=12.5, fill=RED))

# ===========================================================================
# BEAT 4  KNOT
# ===========================================================================
DY, DH = 1612, 520
o.append(panel(PAD, DY, 1440, DH,
               "4.  KNOT — who supplies the closing edge N−1 → 0?",
               "chain b = 1: the edge is intrinsic.   tree b ≥ 2: the edge must be supplied"))
o.append(rich(1440, DY + 34, "chain: FREE      tree: DRIVEN", size=12.5,
              anchor='end', fill=RED))

o.append(text(60, DY + 92, "The cycle needs the closing edge  (N−1) → 0.  Whether that edge "
                           "exists in the lattice is exactly where the chain", size=13))
o.append(text(60, DY + 114, "and the tree part company — and it is the one thing a reader is "
                           "most likely to get wrong.", size=13, fill=GREY))
o.append(text(60, DY + 138, "In X (physical) the closing edge is the root of the tree: the "
                            "root's source term uses f, the amplitude at its parent-alias,",
              size=13))
o.append(text(60, DY + 160, "which does not exist.  In R (reduced) the same edge is supplied "
                            "as the forced root datum.", size=13))

# --- left: the chain ---
LX0, LX1 = 60, 700
LY0 = DY + 188.0
o.append(rect(LX0, LY0, LX1 - LX0, 320, fill='#f5faff', stroke=BLUE, sw=1.5, rx=14))
o.append(rich((LX0 + LX1) / 2.0, LY0 + 30, "chain   b = 1", size=17, weight='bold',
              fill=BLUE))
o.append(text(LX0 + 20, LY0 + 54, "index set ℤ — one node per level", size=12.5, fill=GREY))
o.append(text(LX0 + 20, LY0 + 78, "the index set has NO root, so the closing", size=12.5))
o.append(text(LX0 + 20, LY0 + 100, "edge (N−1) → 0 is already in the lattice.", size=12.5))
o.append(line(134, LY0 + 148, 466, LY0 + 148, stroke=MGREY, sw=1.6, dash="7 5"))
o.append(dot(120, LY0 + 148, 14.0, fill=LBLUE, stroke=BLUE, sw=2.0, name='chain 0'))
o.append(dot(480, LY0 + 148, 14.0, fill=LBLUE, stroke=BLUE, sw=2.0, name='chain N-1'))
o.append(text(100, LY0 + 153, "0", size=13.5, weight='bold', fill=BLUE, anchor='end'))
o.append(text(500, LY0 + 153, "N−1", size=13.5, weight='bold', fill=BLUE, anchor='start'))
o.append(carrow(460, LY0 + 168, 300, LY0 + 208, 140, LY0 + 168, color='blue', sw=2.8))
o.append(text(300, LY0 + 232, "the closing edge is FREE — already there", size=12.5,
              fill=BLUE, anchor='middle'))
o.append(rect(250, LY0 + 246, 100, 30, fill=LGREEN, stroke=GREEN, sw=1.6, rx=8))
o.append(text(300, LY0 + 267, "FREE", size=15, weight='bold', fill=GREEN, anchor='middle'))
o.append(text(LX0 + 20, LY0 + 296, "f = 0: no phantom father, no drive — the ring is "
                                   "UNFORCED.   [proved — §K]", size=12, fill=GREEN))

# --- right: the tree ---
RX0, RX1 = 760, 1440
o.append(rect(RX0, LY0, RX1 - RX0, 320, fill=YTINT2, stroke=RED, sw=1.5, rx=14))
o.append(rich((RX0 + RX1) / 2.0, LY0 + 30, "tree   b ≥ 2", size=17, weight='bold',
              fill=RED))
o.append(text(RX0 + 20, LY0 + 54, "generation 0 IS a root", size=12.5, fill=GREY))
o.append(text(RX0 + 20, LY0 + 78, "the root has no parent in the tree, so the", size=12.5))
o.append(text(RX0 + 20, LY0 + 100, "closing edge must be SUPPLIED:", size=12.5))
o.append(line(RX0 + 64, LY0 + 148, RX0 + 406, LY0 + 148, stroke=MGREY, sw=1.6, dash="7 5"))
o.append(dot(RX0 + 50, LY0 + 148, 14.0, fill=LRED, stroke=RED, sw=2.0, name='tree 0'))
o.append(dot(RX0 + 420, LY0 + 148, 14.0, fill=LRED, stroke=RED, sw=2.0, name='tree N-1'))
o.append(text(RX0 + 30, LY0 + 153, "0", size=13.5, weight='bold', fill=RED, anchor='end'))
o.append(text(RX0 + 440, LY0 + 153, "N−1", size=13.5, weight='bold', fill=RED,
              anchor='start'))
o.append(carrow(RX0 + 400, LY0 + 168, RX0 + 235, LY0 + 208, RX0 + 70, LY0 + 168,
                color='red', sw=2.8))
o.append(text(RX0 + 235, LY0 + 232, "the drive:   f = μ·R_{N−1} = 2^{αN}·X_{N−1}",
              size=12.5, fill=RED, anchor='middle'))
o.append(rect(RX0 + 180, LY0 + 246, 130, 30, fill=LORANGE, stroke=ORANGE, sw=1.6, rx=8))
o.append(text(RX0 + 245, LY0 + 267, "DRIVEN", size=15, weight='bold', fill=ORANGE,
              anchor='middle'))
o.append(text(RX0 + 20, LY0 + 296, "f = 0 ⇒ X_{N−1} = 0 ⇒ X ≡ 0: no closure — the tree "
                                   "does not tie its own knot.   [derived]", size=12,
              fill=RED))

# ===========================================================================
# ALGEBRA STRIP
# ===========================================================================
EY, EH = 2152, 300
o.append(panel(PAD, EY, 1440, EH,
               "5.  The algebra in one place",
               "the twin of CLOSURE.md §4.2's corrigendum;  every line is exact"))
o.append(rich(1440, EY + 34, "everything below is exact", size=12.5, anchor='end',
              fill=GREEN))

o.append(text(60, EY + 92, "the reduced ODE", size=13, weight='bold', fill=GREEN))
o.append(text(400, EY + 94, "Ṙ_{n} = 4^{α}·R_{n−1}^{2} − b·R_{n}·R_{n+1}   on ℤ/N,   "
                            "R_{n+N} = R_{n}", size=17))
o.append(text(60, EY + 132, "the constant mode", size=13, weight='bold', fill=GREEN))
o.append(text(400, EY + 134, "R_{n} ≡ c  ⇒  ċ = (4^{α} − b)·c^{2}     "
                             "⟹  marginal exactly at 4^{α} = b", size=17))
o.append(text(60, EY + 172, "the threshold", size=13, weight='bold', fill=GREEN))
o.append(text(400, EY + 174, "α = α̃ = ½·log_{2}b     the coefficient 4^{α} − b, withdrawn in "
                             "ZETA.md §6.3b′, is CORRECT in this frame", size=14))
o.append(text(60, EY + 212, "at b = 1", size=13, weight='bold', fill=GREEN))
o.append(text(400, EY + 214, "the reduced ODE is the repo's dyadic ring  q_{k}′ = "
                             "4q_{k−1}^{2} − q_{k}q_{k+1}   (CLOSURE.md §1.3, α = 1)",
              size=14))
o.append(text(60, EY + 252, "what is periodic", size=13, weight='bold', fill=RED))
o.append(text(400, EY + 254, "R is periodic (R_{n+N} = R_{n});  X is only scaled-periodic "
                             "(X_{n+N} = μ^{−N}X_{n})", size=14, fill=RED))

# ===========================================================================
# CAVEATS
# ===========================================================================
FY, FH = 2472, 340
o.append(panel(PAD, FY, 1440, FH,
               "CAVEATS — read before believing 1–5",
               "what the picture does NOT say", fill=YTINT2))
o.append(rich(1440, FY + 34, "the tree does not tie its own knot", size=12.5,
              anchor='end', fill=RED))
CAV = [
    ("1", "The bundle is a projection onto a SUBSPACE, not a quotient: §3.2 (no graph "
          "quotient) is untouched.", RED),
    ("2", "Tree closure DRIVEN, chain closure UNFORCED.  If a reader takes one thing away: "
          "the tree does not tie its own knot.", RED),
    ("3", "μ = 2^{α} is FORCED, not chosen.", BLUE),
    ("4", "“exactly the ring at b = 1” holds at α = 1; general α carries 4^{α} and rescales "
          "time by 4^{α−1}.", PURPLE),
    ("5", "The n-independence ⟺ μ = 2^{α} needs α > 0; every case in §K has α > 0.", PURPLE),
    ("6", "ZETA.md §6.3b′'s withdrawal stands: μ is gauge and the constant PROFILE is not a "
          "solution of the unforced rooted model.", ORANGE),
    ("7", "“Marginal” is about the constant mode of the reduced cycle only — not a blow-up "
          "criterion.", ORANGE),
    ("8", "The tree equation is sourced, not proved in this repo;  nothing here is a new "
          "blow-up result.", GREY),
]
cy = FY + 96
for i, (num, body, col) in enumerate(CAV):
    colx = 68 if i % 2 == 0 else 768
    roww = 656
    o.append(circle(colx + 18, cy + 3, 15, fill="#ffffff", stroke=col, sw=1.8))
    o.append(rich(colx + 18, cy + 8, num, size=13, fill=col))
    o.append(para(colx + 44, cy + 8, body, 11.5, roww - 52, fill=INK, lh=15.2))
    if i % 2 == 1:
        cy += 58
o.append(line(60, FY + 300, 1440, FY + 300, stroke=MGREY, sw=1.2))
o.append(text(750, FY + 322, "Isotropy closes an invariant subspace and forces μ = 2^{α}, "
                             "but the closing edge is a DRIVE the tree does not have: "
                             "finite, closed, and driven.  (CLOSURE.md §1.3, §3.2, §4.2)",
              size=12.5, fill=GREY, anchor='middle'))

o.append('</svg>')
# ---------------------------------------------------------------------------
# self-check: (i) every registered string inside the canvas margin; (ii) no two
# registered strings overlap; (iii) no registered string sits on a registered
# diagram node or bead.  All three are hard failures (exit 3).
# ---------------------------------------------------------------------------
bad = [c for c in _CHECK if c[0] < PAD - 6 or c[1] > W - PAD + 6]
bad += [c for c in _CHECK if c[2] < PAD - 6 or c[3] > H - PAD + 6]
if bad:
    sys.stderr.write("LAYOUT: %d string(s) outside the canvas margin:\n" % len(bad))
    for left, right, top, bot, s in bad:
        sys.stderr.write("   y=[%7.1f,%7.1f]  x=[%7.1f,%7.1f]  %r\n"
                         % (top, bot, left, right, s))
    raise SystemExit(3)

clash = []
for i in range(len(_CHECK)):
    for j in range(i + 1, len(_CHECK)):
        a, b = _CHECK[i], _CHECK[j]
        dx = min(a[1], b[1]) - max(a[0], b[0])
        dy = min(a[3], b[3]) - max(a[2], b[2])
        if dx > 2.0 and dy > 2.0:
            clash.append((a, b, dx, dy))
if clash:
    sys.stderr.write("LAYOUT: %d overlapping string pair(s):\n" % len(clash))
    for a, b, dx, dy in clash:
        sys.stderr.write("   overlap %.1f x %.1f:  %r   vs   %r\n"
                         % (dx, dy, a[4], b[4]))
        sys.stderr.write("        A x=[%.1f,%.1f] y=[%.1f,%.1f]   "
                         "B x=[%.1f,%.1f] y=[%.1f,%.1f]\n"
                         % (a[0], a[1], a[2], a[3], b[0], b[1], b[2], b[3]))
    raise SystemExit(3)

hit = []
for left, right, top, bot, s in _CHECK:
    for (ox, oy, orr, onm) in _OBST:
        # closest point of the box to the node centre
        cx = min(max(ox, left), right)
        cyy = min(max(oy, top), bot)
        if math.hypot(ox - cx, oy - cyy) < orr + 1.0:
            hit.append((s, onm, ox, oy, orr, left, right, top, bot))
if hit:
    sys.stderr.write("LAYOUT: %d string(s) sitting on a diagram node/bead:\n" % len(hit))
    for s, onm, ox, oy, orr, left, right, top, bot in hit:
        sys.stderr.write("   %r on %r at (%.1f,%.1f) r=%.1f   "
                         "box x=[%.1f,%.1f] y=[%.1f,%.1f]\n"
                         % (s, onm, ox, oy, orr, left, right, top, bot))
    raise SystemExit(3)

sys.stdout.write('\n'.join(o) + '\n')
