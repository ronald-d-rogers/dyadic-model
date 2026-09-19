#!/usr/bin/env python3
"""What the flow is constrained by: one invariant for the clamped chain, none for the ring.

Companion to plot_dyadic_ring.py and plot_truncated_model.py.  Those two draw the ring and
the chain; this one draws the INTEGRABILITY QUESTION that was just settled in exact
arithmetic, and it is deliberately careful about what was settled and what was not.

Panel A  the clamped chain (u_{-1} = u_N = 0).  It conserves exactly one independent
         quantity, the energy E = sum_k u_k^2, and the invariant algebra is Q[E].  So the
         flow lies on the sphere sum_k u_k^2 = E_0 in R^N -- drawn schematically for N = 3
         with a trajectory wandering on it.  The same weights give an enstrophy ceiling
         H = sum_k 4^k u_k^2 <= 4^{N-1} E, and that ceiling is what regularises the chain:
         E bounds H, and H bounds every weighted norm the transfer needs.  H is MONOTONE
         INCREASING and approaches the ceiling only asymptotically -- the measured deficit
         4^{N-1}E - H falls like 2E/t (log-log inset in panel A) -- and the ceiling is
         attained exactly when all the energy sits on the top shell, u = (0,0,+-sqrt(E)),
         which is the saturation the approach climbs toward.  The red dot is H AT t = 50,
         NOT the maximum: there is no maximum, only that supremum.
Panel B  the reduced ring q_k' = 4 q_{k-1}^2 - q_k q_{k+1} on Z/N.  It has ZERO conserved
         quantities.  No sphere, no tori, no level set constrains it.  Exactly two
         structures survive, and neither is an invariant: the scaling symmetry
         q_k(t) -> lambda q_k(lambda t) (the field is homogeneous of degree 2), and the
         invariant diagonal q_k = q, on which q' = 3q^2 and q blows up at t = 1/(3a).
Panel C  the structural reason: the ring is not a Volterra / Kac-van Moerbeke lattice.
         Those families have x_k | V_k, i.e. N invariant coordinate hyperplanes; the ring
         has zero for N >= 3.  Under q_k = c_k x_k the source term is a pure square, and a
         pure square can never become a product x_{k-1}x_k.  Nor is the ring Hamiltonian
         for any log-canonical or constant Poisson structure.  The scoping is the ARCHIVED
         one: no invertible LINEAR change of variables reaches that family; a general
         nonlinear transformation is left open (CLOSURE.md Sec. 5.6, 5.8).
Panel D  the honest caveats, prominent: the polynomial null is proved only for degrees
         <= 9 and only for the computed N; non-polynomial C^1 first integrals are NOT
         excluded; N = 1 is degenerate; and the exact method was validated by recovering
         the KNOWN Volterra invariants, because a negative result is only as good as its
         engine.

PROVENANCE.  The invariant null, the degree/N table, the hyperplane count and the Volterra
validation are archived in Cascade/CLOSURE.md Sec. 5 (exact Fraction RREF over Q, sympy
cross-check, non-existence certified mod two large primes).  Note the archived scope: the
clamped chain's invariant algebra is Q[E] THROUGH DEGREE 8, not in all degrees, and the
Volterra exclusion is for invertible LINEAR changes of variables.  By contrast the
161 -> 223.48 excursion and the 2E/t deficit law of panel A are now recorded in this
repository: Cascade/CLOSURE.md Sec. 5.10, with the script Cascade/clamped_enstrophy.py.
They are numerical RK4 measurements (converged at dt = 1e-4 and dt = 2e-5, with E conserved
to 1e-12) and are labelled measured on the figure.  "223.48" is the value at t = 50, not a
maximum.

HONESTY -- the same discipline as the sibling figure.
  * Nothing here is a discovery.  The diagonal blow-up q_k = c with c' = 3c^2 is the
    repo's existing Cascade.selfSimilar re-derived in the reduced variables; its physical
    enstrophy is infinite (4^k u_k^2 = q_k^2 is periodic in k), so it is not a blow-up
    from finite-enstrophy data.  The repo's overall verdict is negative.
  * The blow-up times and the H excursion are NUMERICAL measurements, and are labelled as
    such on the figure.  The inequality H <= 4^{N-1}E, the top-shell equality case and the
    substitution q_k = c_k x_k are exact.
  * LABEL DISCIPLINE: [proved] / [exact] / [measured] / [conjecture] / [not excluded]
    tags appear on the figure; nothing measured is drawn as if proved.

Layout note.  The generator registers every string it draws (text()/para()) and refuses to
emit an SVG whose text (i) falls outside the canvas margin or (ii) overlaps another
registered string; either failure exits 3.  A new label should go through text()/para().

Standard library only; emits SVG on stdout.  Regenerate with:

    python3 plot_ring_invariants.py > ring_invariants.svg
    rsvg-convert -w 1800 -o ring_invariants.png ring_invariants.svg
"""
import sys, math

# Panel A grows by SHIFT to hold the deficit inset; every panel below it is drawn
# once and then shifted down by SHIFT as a group, so the layout constants of B, C, D
# need not be renumbered.  The registered text boxes are shifted with it.
SHIFT = 150
W, H = 1500, 2500 + SHIFT
BG = "#ffffff"
INK = "#252525"; GREY = "#737373"; MGREY = "#bdbdbd"; LGREY = "#f4f4f4"
BLUE = "#08519c"; LBLUE = "#c6dbef"
RED = "#a50f15"; LRED = "#fcbba1"
GREEN = "#238b45"; LGREEN = "#d9f0d3"
PURPLE = "#6a51a3"; LPURPLE = "#dadaeb"
ORANGE = "#d94801"; LORANGE = "#fee6ce"
WALL = "#969696"
YTINT = "#fffdf2"

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
# text -- markup with _{...} subscripts and ^{...} superscripts, exactly as the
# sibling figure does it, so the figures share a typographic voice.
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
# approximate text metrics -- used ONLY to wrap text and to CHECK canvas bounds
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

_CHECK = []

def text(x, y, markup, size=14, anchor='start', fill=INK, weight='normal'):
    """draw + register a bounds check against the canvas margin"""
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

def node(x, y, r, label, fill=LBLUE, stroke=BLUE, tcol=BLUE, fs=16, dash=None,
         opacity=1.0):
    return (circle(x, y, r, fill=fill, stroke=stroke, dash=dash, opacity=opacity)
            + rich(x, y + fs * 0.35, label, size=fs, fill=tcol, opacity=opacity))

def vclamp(x, ytop, ybot):
    """hatched vertical wall, matching the sibling figure's vclamp()"""
    s = [line(x, ytop, x, ybot, stroke=WALL, sw=9)]
    n = int((ybot - ytop) // 15)
    for i in range(n + 1):
        yy = ytop + i * 15
        s.append(line(x - 12, yy + 9, x + 12, yy - 9, stroke=WALL, sw=2))
    return ''.join(s)

def panel(x, y, w, h, title, fill=BG):
    s = [rect(x, y, w, h, fill=fill, stroke=MGREY, sw=1.5, rx=16)]
    if title:
        s.append(text(x + 26, y + 34, title, size=20, weight='bold'))
    return ''.join(s)

def step(P, Q, shrink):
    dx, dy = Q[0] - P[0], Q[1] - P[1]
    L = math.hypot(dx, dy)
    ux, uy = dx / L, dy / L
    return (P[0] + ux * shrink, P[1] + uy * shrink), (Q[0] - ux * shrink, Q[1] - uy * shrink)

def cross_out(cx, cy, rx, ry, color='red', sw=3.4):
    """a red stroke through a ghost shape: 'this structure is absent'"""
    return (line(cx - rx * 0.70, cy + ry * 0.70, cx + rx * 0.70, cy - ry * 0.70,
                 stroke=MARK[color], sw=sw)
            + line(cx - rx * 0.70, cy - ry * 0.70, cx + rx * 0.70, cy + ry * 0.70,
                   stroke=MARK[color], sw=sw))

# ===========================================================================
o.append(f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" '
         f'viewBox="0 0 {W} {H}">')
o.append(defs())
o.append(f'<rect width="{W}" height="{H}" fill="{BG}"/>')

# ---- masthead --------------------------------------------------------------
o.append(rich(750, 50, "What the flow is constrained by: one invariant for the chain, "
                       "none for the ring", size=27, weight='bold'))
o.append(rich(750, 78, "the clamped chain's invariant algebra is ℚ[E] and it lives on a "
                       "sphere;  the reduced ring's is trivial and it lives on nothing",
              size=14, fill=GREY))

# ---- equation strip --------------------------------------------------------
o.append(rect(60, 100, 1380, 94, fill=LGREY, stroke=MGREY, sw=1.2, rx=12))
o.append(rich(750, 142, "clamped chain:  u_{−1} = u_{N} = 0,     E = Σ u_{k}^{2},     "
                        "H = Σ 4^{k}u_{k}^{2} ≤ 4^{N−1}E", size=20))
o.append(rich(750, 174, "ring on ℤ/N:  q_{k}′ = 4q_{k−1}^{2} − q_{k}q_{k+1},     "
                        "0 independent conserved quantities          "
                        "[proved for the stated N and degree; see panel D]",
              size=13.5, fill=GREY))

# ================= PANEL A: the clamped chain, one invariant ===============
AY, AH = 214, 560 + SHIFT
o.append(panel(PAD, AY, 1440, AH,
               "A.  The clamped chain: one invariant, ℚ[E] — the flow is caught on a sphere"))
o.append(rich(1440, AY + 34, "N = 3, drawn", size=12.5, anchor='end', fill=GREY))

# --- left: the sphere -------------------------------------------------------
o.append(text(60, 288, "the one invariant is the energy, and ℚ[E] is the whole algebra",
              size=14, weight='bold'))
CX, CY, CR = 372.0, 502.0, 142.0
o.append(circle(CX, CY, CR, fill=LBLUE, stroke=BLUE, sw=2, opacity=0.55))
# the trajectory: an orthographic projection of a wandering curve on the sphere
TR = []
NPT = 110
for i in range(NPT + 1):
    s = 2.0 * math.pi * i / NPT
    th = 4.2 * s + 0.7 * math.sin(3.0 * s)
    ph = 1.04 + 0.54 * math.sin(2.3 * s + 0.4)
    TR.append((CX + CR * math.sin(ph) * math.cos(th), CY - CR * math.cos(ph)))
o.append(poly(TR, color='red', sw=2.4, dash="8 5", opacity=0.95, arrow_end=True))
# coordinate frame, so the ball reads as R^3 (axes drawn over the sphere)
AXL = CR * 1.24
for ux, uy in ((-0.80, 0.60), (0.80, 0.60), (0.0, -1.0)):
    o.append(line(CX, CY, CX + ux * AXL, CY + uy * AXL, stroke=GREY, sw=1.3, opacity=0.75))
o.append(circle(CX, CY, 3.2, fill=INK, stroke=INK, sw=1))
o.append(text(CX - 0.80 * AXL - 10, CY + 0.60 * AXL + 12, "u_{0}", size=13, fill=GREY,
              anchor='end'))
o.append(text(CX + 0.80 * AXL + 10, CY + 0.60 * AXL + 12, "u_{1}", size=13, fill=GREY))
o.append(text(CX + 16, CY - AXL - 12, "u_{2}", size=13, fill=GREY))
o.append(line(CX - CR, CY, CX + CR, CY, stroke=MGREY, sw=1.0, dash="4 5", opacity=0.7))
o.append(ellipse(CX, CY, CR, CR * 0.30, stroke=MGREY, sw=1.0, dash="4 5", opacity=0.7))
o.append(ellipse(CX, CY, CR * 0.34, CR, stroke=MGREY, sw=1.0, dash="4 5", opacity=0.7))
# start point and its label
o.append(circle(TR[0][0], TR[0][1], 5.5, fill=RED, stroke=RED, sw=1))
o.append(text(TR[0][0] + 14, TR[0][1] - 12, "(1,2,3)", size=12.5, fill=RED))
o.append(text(CX - 20, CY - CR - 48, "Σ_{k}u_{k}^{2} = E_{0} = 14", size=14, fill=BLUE,
              anchor='end'))
o.append(text(60, 668, "the single invariant:  E = Σ u_{k}^{2} = 14 along the whole flow",
              size=13, fill=BLUE))
o.append(text(60, 692, "a level set of E is a sphere in ℝ^{3}, and the flow never leaves it",
              size=13, fill=GREY))
o.append(text(60, 716, "no second independent invariant through degree 8 — not E^{2}, "
                       "not any polynomial of E", size=12.5, fill=GREY))
o.append(text(60, 740, "[proved through degree 8: the invariant algebra is ℚ[E]]",
              size=12.5, fill=GREEN))

# --- right: the enstrophy ceiling ------------------------------------------
o.append(text(790, 288, "the enstrophy ceiling — and it is what regularises the chain",
              size=14, weight='bold'))
o.append(text(790, 318, "H = Σ_{k=0}^{N−1}4^{k}u_{k}^{2} ≤ 4^{N−1}E   "
                        "(4^{N−1} = 16 at N = 3, E = 14)", size=14))
o.append(text(790, 344, "not an invariant — a bound: whatever the flow does, H stays "
                        "below the ceiling", size=12.5, fill=GREY))
BAR0, BAR1 = 812.0, 1400.0
SC = (BAR1 - BAR0) / 240.0
BY0 = 420.0
o.append(line(BAR0, BY0, BAR1, BY0, stroke=GREY, sw=1.6))
for tv in (0, 100, 200):
    tx = BAR0 + tv * SC
    o.append(line(tx, BY0 - 6, tx, BY0 + 6, stroke=GREY, sw=1.3))
    o.append(text(tx, BY0 + 28, f"{tv}", size=11, fill=GREY, anchor='middle'))
X161, X223, X224 = BAR0 + 161 * SC, BAR0 + 223.48 * SC, BAR0 + 224 * SC
o.append(line(X161, BY0, X223, BY0, stroke=GREEN, sw=9))
o.append(circle(X161, BY0, 6, fill=BLUE, stroke=BLUE, sw=1))
o.append(circle(X223, BY0, 6, fill=RED, stroke=RED, sw=1))
o.append(line(X224, BY0 - 30, X224, BY0 + 30, stroke=RED, sw=2.0, dash="6 5"))
o.append(text(1440, BY0 - 42, "ceiling  4^{N−1}E = 224", size=12.5, fill=RED,
              anchor='end'))
o.append(text(BAR0, BY0 + 56, "H = 161 at (1,2,3),  E = 14", size=12.5, fill=BLUE))
o.append(text(1440, BY0 + 56, "red dot: H at t = 50 — 223.48, still rising (measured, RK4)",
              size=12.5, fill=ORANGE, anchor='end'))
o.append(text(790, 512, "H is monotone increasing and approaches the ceiling "
                        "asymptotically; it never crosses it.", size=13))
o.append(text(790, 536, "measured (RK4):  t = 50 → 223.48,   t = 200 → 223.862,   "
                        "t = 2000 → 223.986", size=12.5, fill=GREY))
o.append(text(790, 560, "the deficit 4^{N−1}E − H falls like 2E/t = 28/t:  "
                        "0.560 predicted vs 0.523 measured at t = 50", size=12.5,
              fill=GREY))
o.append(text(790, 584, "the ceiling is attained exactly when all the energy sits on the "
                        "top shell,", size=12.5))
o.append(text(790, 608, "u = (0, 0, ±√14) — the saturation this approach is climbing "
                        "toward.", size=12.5))
o.append(text(790, 634, "[proved: H ≤ 4^{N−1}E, equality at the top shell]", size=12.5,
              fill=GREEN))
o.append(text(1440, 634, "[measured: the 2E/t approach — CLOSURE.md §5.10]", size=12.5,
              fill=ORANGE, anchor='end'))
# --- inset: the deficit against time, log-log, where the 1/t slope is visible
IX0, IX1 = 880.0, 1370.0
IY0, IY1 = 696.0, 856.0                # 2 decades each: t 30..3000, deficit 0.01..1
IXD, IYD = (IX1 - IX0) / 2.0, (IY1 - IY0) / 2.0
def ix(t): return IX0 + math.log10(t / 30.0) * IXD
def iy(d): return IY1 - math.log10(d / 0.01) * IYD
o.append(rect(790, 650, 650, 268, fill=YTINT, stroke=MGREY, sw=1.2, rx=12))
o.append(text(806, 676, "the deficit  4^{N−1}E − H  against t — log-log, slope −1",
              size=12.5, weight='bold'))
o.append(line(IX0, IY1, IX1, IY1, stroke=GREY, sw=1.3))
o.append(line(IX0, IY0, IX0, IY1, stroke=GREY, sw=1.3))
for d, lab in ((1.0, "1"), (0.1, "0.1"), (0.01, "0.01")):
    o.append(text(IX0 - 6, iy(d) + 4, lab, size=11, fill=GREY, anchor='end'))
for t, lab in ((100, "100"), (1000, "1000")):
    o.append(text(ix(t), IY1 + 20, lab, size=11, fill=GREY, anchor='middle'))
o.append(text(IX1 + 10, IY1 + 20, "t", size=11.5, fill=GREY))
LAW = [(ix(t), iy(28.0 / t)) for t in [30.0 * (3000.0 / 30.0) ** (i / 60.0)
                                       for i in range(61)]]
o.append(poly(LAW, color='grey', sw=2.2, arrow_end=False))
MEAS = [(50, 0.522695), (100, 0.2704), (200, 0.1377), (500, 0.0557),
        (1000, 0.0279), (2000, 0.0140)]
for t, d in MEAS:
    o.append(circle(ix(t), iy(d), 5, fill=RED, stroke=RED, sw=1))
o.append(text(1000, 902, "dots: measured (RK4)        line: 2E/t = 28/t", size=11.5,
              fill=GREY))
# column rule, centred in the gap between the sphere (right edge ~600) and the
# enstrophy column (left edge 790)
o.append(line(700, 264, 700, 900, stroke=MGREY, sw=1.2, dash="6 6"))

# everything from here to the footer is emitted with panel-A coordinates and then
# shifted down by SHIFT as one group, so B, C and D keep their own numbering
_SHO, _SHC = len(o), len(_CHECK)

# ================= PANEL B: the ring, no invariant at all ==================
BY, BH = 792, 500
o.append(panel(PAD, BY, 1440, BH,
               "B.  The reduced ring on ℤ/N: zero conserved quantities — the flow lives on nothing"))
o.append(rich(1440, BY + 34, "0 invariants", size=13, anchor='end', fill=RED))

# --- left: the contrast, and the counts ------------------------------------
o.append(text(60, 872, "the contrast: nothing constrains this flow", size=14, weight='bold'))
o.append(circle(150, 962, 50, fill="none", stroke=MGREY, sw=2, dash="7 6"))
o.append(ellipse(150, 962, 50, 16, stroke=MGREY, sw=1.4, dash="7 6"))
o.append(cross_out(150, 962, 50, 50))
o.append(text(150, 1034, "no sphere", size=12.5, fill=GREY))
o.append(ellipse(378, 962, 62, 34, stroke=MGREY, sw=2, dash="7 6"))
o.append(ellipse(378, 962, 26, 13, stroke=MGREY, sw=1.4, dash="7 6"))
o.append(cross_out(378, 962, 62, 34))
o.append(text(378, 1034, "no tori", size=12.5, fill=GREY))
o.append(text(60, 1072, "no level set, no invariant manifold to confine the blow-up:",
              size=13, fill=RED))
o.append(text(60, 1096, "the ring has no conserved quantity at all, so there is no "
                        "subtorus to lean on.", size=13, fill=GREY))
# the counts
o.append(text(60, 1140, "model", size=12, fill=GREY, weight='bold'))
o.append(text(340, 1140, "invariants", size=12, fill=GREY, weight='bold'))
o.append(text(470, 1140, "the flow lies on", size=12, fill=GREY, weight='bold'))
o.append(line(60, 1150, 740, 1150, stroke=MGREY, sw=1.2))
ROWS = [("ring on ℤ/N", "0", "nothing — no level set at all", RED),
        ("clamped chain", "1", "the sphere Σ_{k}u_{k}^{2} = E_{0}   (ℚ[E])", BLUE),
        ("full integrability", "N−1", "tori — never reached, not even by the chain", GREY)]
ry = 1180
for name, cnt, where, col in ROWS:
    o.append(text(60, ry, name, size=13))
    o.append(text(340, ry, cnt, size=14, fill=col, weight='bold'))
    o.append(text(470, ry, where, size=12.5, fill=col))
    o.append(line(60, ry + 12, 740, ry + 12, stroke=LGREY, sw=1.2))
    ry += 36
o.append(text(60, 1276, "N − 1 invariants would be needed for a full torus; the chain "
                         "reaches 1, the ring 0.", size=12.5, fill=GREY))

# --- right: the two structures that do survive -----------------------------
o.append(text(800, 872, "(i) the one symmetry that survives: scaling", size=14,
              weight='bold'))
o.append(text(800, 898, "q_{k}(t) ⟼ λq_{k}(λt),  λ > 0:  the field is homogeneous of "
                        "degree 2", size=13))
o.append(text(800, 918, "a symmetry, not a conserved quantity — it moves the clock and "
                        "the amplitude together", size=12, fill=GREY))
# mini-plot of the two profiles
PX0, PX1, PY0, PY1 = 812.0, 992.0, 928.0, 1002.0
o.append(line(PX0, PY0, PX0, PY1, stroke=GREY, sw=1.3))
o.append(line(PX0, PY1, PX1, PY1, stroke=GREY, sw=1.3))
for q, col in (((1, 2, 3), 'blue'), ((2, 4, 6), 'orange')):
    pts = [(PX0 + i * (PX1 - PX0) / 2.0, PY1 - v * 9.4) for i, v in enumerate(q)]
    o.append(poly(pts, color=col, sw=2.0))
    for px, py in pts:
        o.append(circle(px, py, 4, fill=MARK[col], stroke=MARK[col], sw=1))
o.append(text(PX1 + 10, PY0 + 22, "λ = 2", size=11.5, fill=ORANGE))
o.append(text(PX1 + 10, PY1 - 2, "λ = 1", size=11.5, fill=BLUE))
o.append(text(PX0 - 6, PY0 + 4, "q", size=11.5, fill=GREY, anchor='end'))
o.append(text(PX1 + 10, PY1 + 20, "k", size=11.5, fill=GREY))
o.append(text(800, 1040, "(ii) the one invariant manifold that survives: the diagonal",
              size=14, weight='bold'))
o.append(text(800, 1066, "q_{k} = q for all k  ⇒  q′ = 4q^{2} − q^{2} = 3q^{2}", size=13))
o.append(text(800, 1090, "q(t) = a/(1 − 3at):  blow-up at t = 1/(3a),  a = q(0)   "
                         "[exact; measured t*]", size=13, fill=BLUE))
# mini-plot of the blow-up
TX0, TX1, TY0, TY1 = 812.0, 1120.0, 1112.0, 1216.0
o.append(line(TX0, TY1, TX1, TY1, stroke=GREY, sw=1.3))
o.append(line(TX0, TY0, TX0, TY1, stroke=GREY, sw=1.3))
TSC, QSC = (TX1 - TX0) / 1.15, (TY1 - TY0) / 7.2
ASYM = TX0 + 1.0 * TSC
o.append(line(ASYM, TY0 - 4, ASYM, TY1 + 6, stroke=RED, sw=1.6, dash="5 5"))
CURVE = [(TX0 + t * TSC, TY1 - (1.0 / 3.0) / (1 - t) * QSC) for t in
         [i * 0.9 / 24 for i in range(25)]]
CURVE = [(x, max(TY0 - 6, y)) for x, y in CURVE]
o.append(poly(CURVE, color='blue', sw=2.4, arrow_end=True))
o.append(text(ASYM + 6, TY0 + 10, "t = 1/(3a)", size=11.5, fill=RED))
o.append(text(TX1 + 6, TY1 + 4, "t", size=11.5, fill=GREY, anchor='start'))
o.append(text(TX0 - 6, TY0 + 4, "q", size=11.5, fill=GREY, anchor='end'))
o.append(text(800, 1240, "the diagonal is a genuine invariant submanifold — but not an "
                         "invariant:", size=12.5, fill=GREY))
o.append(text(800, 1258, "it is one slice, and on it the flow blows up in finite time, "
                         "unconstrained.", size=12.5, fill=GREY))
o.append(text(800, 1280, "the blow-up is Cascade.selfSimilar re-derived; its physical "
                         "enstrophy is infinite.", size=12.5, fill=RED))
# column rule, centred in the gap between the counts (right edge ~760) and the
# two surviving structures (left edge 800)
o.append(line(775, 830, 775, 1286, stroke=MGREY, sw=1.2, dash="6 6"))

# ================= PANEL C: not Volterra / Kac–van Moerbeke ================
CY2, CH2 = 1310, 520
o.append(panel(PAD, CY2, 1440, CH2,
               "C.  Why it is not a Volterra / Kac–van Moerbeke lattice"))
o.append(rich(1440, CY2 + 34, "0 invariant hyperplanes for N ≥ 3", size=13,
              anchor='end', fill=RED))

# --- left: the two diagrams -------------------------------------------------
o.append(text(240, 1378, "Volterra / Kac–van Moerbeke", size=14, weight='bold',
              anchor='middle'))
OX, OY = 165.0, 1650.0
o.append(rect(OX, 1400, 245, 250, fill=LGREEN, stroke="none", sw=0, rx=0, opacity=0.55))
o.append(arrow(OX - 30, OY, OX + 270, OY, color='grey', sw=1.8))
o.append(arrow(OX, OY + 30, OX, OY - 240, color='grey', sw=1.8))
o.append(text(OX + 272, OY + 20, "x_{k}", size=12, fill=GREY))
o.append(text(OX - 8, OY - 246, "x_{k+1}", size=12, fill=GREY, anchor='end'))
o.append(text(OX + 10, OY - 230, "x_{k} = 0", size=11.5, fill=GREEN))
o.append(text(OX + 262, OY + 24, "x_{k+1} = 0", size=11.5, fill=GREEN, anchor='end'))
o.append(carrow(OX + 30, OY - 40, OX + 120, OY - 190, OX + 200, OY - 190, color='green',
                sw=2.2))
o.append(text(OX + 118, OY - 14, "the flow is walled in", size=11.5, fill=GREEN))
o.append(text(240, 1696, "x_{k} | V_{k}:  N invariant coordinate hyperplanes", size=12.5,
              fill=GREEN, anchor='middle'))
o.append(text(240, 1718, "every axis is a wall the flow cannot cross", size=11.5, fill=GREY,
              anchor='middle'))

o.append(text(620, 1378, "the ring on ℤ/N", size=14, weight='bold', anchor='middle'))
QX = 545.0
o.append(arrow(QX - 30, OY, QX + 220, OY, color='grey', sw=1.8))
o.append(arrow(QX, OY + 30, QX, OY - 240, color='grey', sw=1.8))
o.append(text(QX + 225, OY + 20, "q_{k}", size=12, fill=GREY))
o.append(text(QX - 8, OY - 246, "q_{k+1}", size=12, fill=GREY, anchor='end'))
o.append(text(QX + 10, OY - 230, "q_{k} = 0", size=11.5, fill=RED))
o.append(poly([(QX + 150, OY - 200), (QX + 100, OY - 140), (QX + 40, OY - 60),
               (QX - 40, OY + 10), (QX - 100, OY + 40)], color='red', sw=2.4,
              arrow_end=True))
o.append(cross_out(QX + 4, OY - 30, 12, 12, sw=3.0))
o.append(text(QX + 118, OY - 14, "the flow crosses it", size=11.5, fill=RED))
o.append(text(620, 1696, "x_{k} ∤ V_{k}:  0 invariant hyperplanes for N ≥ 3", size=12.5,
              fill=RED, anchor='middle'))
o.append(text(620, 1718, "no wall exists for the flow to be trapped behind", size=11.5,
              fill=GREY, anchor='middle'))

# --- right: the substitution and the punchline ------------------------------
o.append(text(810, 1378, "the structural test, in normalized variables", size=14,
              weight='bold'))
o.append(text(810, 1412, "substitute  q_{k} = c_{k}x_{k}  with every c_{k} ≠ 0:", size=13.5))
o.append(text(810, 1450, "x_{k}′ = (4c_{k−1}^{2}/c_{k}) x_{k−1}^{2} − c_{k+1} x_{k}x_{k+1}",
              size=17, weight='bold'))
o.append(rect(810, 1470, 630, 108, fill=LORANGE, stroke=ORANGE, sw=1.4, rx=12))
o.append(text(830, 1502, "a pure square can never become a product x_{k−1}x_{k}",
              size=15, weight='bold', fill=RED))
o.append(text(830, 1528, "Volterra needs x_{k} | V_{k}: every monomial must carry a "
                         "factor x_{k}.", size=12.5))
o.append(text(830, 1552, "The source 4c_{k−1}^{2}x_{k−1}^{2}/c_{k} carries none, so "
                         "x_{k} = 0 is not invariant.", size=12.5))
o.append(text(830, 1576, "A normalization rescales the coordinates; it cannot change "
                         "which monomials appear.", size=12.5, fill=GREY))
o.append(text(810, 1614, "so no invertible linear change of variables makes the ring a "
                         "Volterra/KvM lattice;", size=13))
o.append(text(810, 1640, "nor is it Hamiltonian for any log-canonical or constant Poisson "
                         "structure.  (CLOSURE §5.6)", size=13))
o.append(text(810, 1666, "a general nonlinear transformation is left open (the §5.8 "
                         "conjecture), as is a general Lax pair.", size=12.5, fill=GREY))
o.append(text(810, 1690, "note the count once more: N hyperplanes for Volterra, 0 for the "
                         "ring when N ≥ 3.", size=12.5, fill=GREY))
o.append(text(810, 1716, "[proved for N ≥ 3: x_{k} = 0 is not invariant for any k]",
              size=12.5, fill=GREEN))
# column rule, centred in the gap between the two diagrams (right edge ~780) and
# the structural-test column (left edge 810)
o.append(line(792, 1352, 792, 1818, stroke=MGREY, sw=1.2, dash="6 6"))

# ================= PANEL D: the honest caveats =============================
DY, DH = 1848, 440
o.append(panel(PAD, DY, 1440, DH,
               "D.  The honest caveats — read before believing A, B, C", fill="#fff8f4"))
o.append(rich(1440, DY + 34, "a negative result, reported as one", size=13,
              anchor='end', fill=RED))
CAV = [
    ("1", "PROVED, AND ONLY THUS FAR.  Polynomial invariants are excluded for degrees ≤ 9 "
          "and for the computed N — N = 2..6 to degree 9, N = 7 to degree 8, N = 8..12 to "
          "degree 5.  “No invariant at any degree for all N” is a CONJECTURE, not a "
          "theorem.  (CLOSURE §5.4)", RED),
    ("2", "NOT EXCLUDED.  Non-polynomial C^{1} first integrals.  Locally every nonvanishing "
          "field has one (flow-box straightening), so the null is about polynomial and "
          "global invariants only.  (CLOSURE §5.8)", ORANGE),
    ("3", "DEGENERATE.  N = 1, where q′ = 3q^{2}, has no meaningful invariant to count.",
          PURPLE),
    ("4", "EXACT, AND VALIDATED.  Fraction RREF over ℚ, cross-checked in sympy, "
          "non-existence certified mod two large primes.  The engine was validated by "
          "recovering the KNOWN Volterra invariants — a negative result is only as good as "
          "its engine.  (CLOSURE §5.3)", BLUE),
    ("5", "NOT A DISCOVERY.  The diagonal blow-up re-derives the repo's existing "
          "Cascade.selfSimilar, whose physical enstrophy is infinite; the repo's overall "
          "verdict is negative.", GREEN),
]
DL_DX = 0
o.append(f'<g transform="translate({DL_DX},0)">')
ry = DY + 72
for num, body, col in CAV:
    o.append(circle(86, ry + 3, 19, fill="#ffffff", stroke=col, sw=2))
    o.append(rich(86, ry + 8, num, size=15, fill=col))
    o.append(para(124, ry + 8, body, 15, 1310, fill=INK, lh=21))
    ry += nlines(body, 15, 1310) * 21 + 24
o.append('</g>')

# ---- disambiguation strip --------------------------------------------------
o.append(text(750, 2320, "three different things that the surrounding document names "
                         "alike", size=13, fill=GREY, anchor='middle'))
DZ = [("a forward-invariant manifold", "a set the flow cannot leave — isotropy, a different "
       "notion (CLOSURE §5.2; isotropy §4.1)", GREEN),
      ("a conserved quantity", "a function constant along the flow — the chain's E; the "
       "ring has none", BLUE),
      ("the p-adic Tate torus K*/q^{ℤ}", "a geometric object of genus 1 — unrelated to "
       "either of the above", PURPLE)]
for i, (head, body, col) in enumerate(DZ):
    bx = 60 + i * 460
    o.append(rect(bx, 2336, 440, 84, fill=BG, stroke=col, sw=1.4, rx=12))
    o.append(text(bx + 16, 2364, head, size=13.5, weight='bold', fill=col))
    o.append(para(bx + 16, 2388, body, 12, 408, fill=GREY, lh=17))

# ---- footer ----------------------------------------------------------------
o.append(line(60, 2448, 1440, 2448, stroke=MGREY, sw=1.2))
o.append(text(750, 2466, "The clamped chain has one invariant and lives on a sphere; the "
                         "ring has none and lives on nothing — no tori, and no subtorus "
                         "confinement to lean on for a blow-up argument.  (CLOSURE §5.9)",
              size=12.5, fill=GREY, anchor='middle'))

# ---- shift the whole B/C/D/footer block down to clear panel A's inset --------
o[_SHO:] = ([f'<g transform="translate(0,{SHIFT})">'] + o[_SHO:] + ['</g>'])
for _i in range(_SHC, len(_CHECK)):
    _l, _r, _t, _b, _s = _CHECK[_i]
    _CHECK[_i] = (_l, _r, _t + SHIFT, _b + SHIFT, _s)

o.append('</svg>')

# ---------------------------------------------------------------------------
# self-check: every registered string must sit inside the canvas margin, and no
# two registered strings may overlap.  Both are hard failures (exit 3).
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

sys.stdout.write('\n'.join(o) + '\n')
