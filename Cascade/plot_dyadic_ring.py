#!/usr/bin/env python3
"""The smallest dyadic ring: the self-similar closure at N = 3.

Companion to plot_truncated_model.py, which draws the CLAMPED chain.  This one draws
the closed loop -- the ring.  The difference is one edge.

In the chain, shell k's transfer 2^{k}(u_{k-1}^2 - 2 u_k u_{k+1}) is clamped at both
ends, u_{-1} = u_N = 0, so the two end fluxes die and the pairing sum_k u_k T_k
cancels identically, whatever the signs.  In the ring the edge that would close the
lattice is retained and carries the twist factor 2^{-N} = 1/8.  Going once around
multiplies the transfer by 2^N = 8 and the twist by 2^{-N} = 1/8, so the product is 1
and the loop closes -- but only up to the scaling.  A seam survives, and this figure
is about that seam.

Panels:
  A  the ring of three shells k = 0,1,2, weights 2^{2k} = 1,4,16, with the closing
     edge marked x2^{-3}, beside the same three shells drawn as the clamped chain.
  B  the holonomy cancellation 2^N * 2^{-N} = 1, the seam that survives it (and its
     mirror on the low side, u_{-1} = 8u_2), drawn as a defect on the closing edge
     against the clamp's clean cut.
  C  the reduced cyclic ODE q_k' = 4 q_{k-1}^2 - q_k q_{k+1} on Z/3, the constant mode
     c' = 3c^2 with c(t) = c_0/(1 - 3 c_0 t), the measured blow-up times, and the
     minimality of N = 3.
  D  the caveats.  Read that panel before believing panel C.

HONESTY -- the point of the figure.
  * The blow-up profile IS the repo's existing Cascade.selfSimilar re-derived in log
    coordinates.  It is not a new blow-up.
  * Its physical enstrophy is infinite: 4^k u_k^2 = q_k^2 is periodic in k, so the
    lattice sum diverges.  H = sum_{k<N} q_k^2 is a per-period DENSITY, not the
    physical enstrophy.
  * The profile does NOT satisfy the clamp (u_N = 2^{-N} q != 0), so it is not a
    solution of the clamped model, and the clamped model's regularity is not in
    tension with it.
  * Viscosity closes the ring only at e = 0; at the physical e = 2 the ansatz is a
    renormalization cycle, not a symmetry.

The blow-up times in panel C are NUMERICAL measurements of the reduced ODE (classical
RK4, N = 1,2,3 with the stated initial data) and are labelled as such; integrated here
they reproduce 0.333, 0.333, 0.217 and 0.160.  The substitution u_k = 2^{-k} q_k, the
reduced ODE and the closed form 1/(3 c_0) are exact.  The seam term
(2^{2N} - 1) u_{N-1}^2 u_0 was originally carried over on trust; it is now verified by
hand at N = 3, and the derivation is recorded here because an earlier attempt at the same
substitution produced a quadratic.  With u_{-1} = 8u_2 and u_3 = u_0/8 the three transfers
are

    T_0 = (8u_2)^2 - 2u_0u_1      = 64u_2^2 - 2u_0u_1
    T_1 = 2(u_0^2 - 2u_1u_2)      = 2u_0^2 - 4u_1u_2
    T_2 = 4(u_1^2 - 2u_2 u_0/8)   = 4u_1^2 - u_0u_2

so pairing each with its own u_k the interior cross terms cancel in pairs
(-2u_0^2u_1 + 2u_0^2u_1 = 0 and -4u_1^2u_2 + 4u_1^2u_2 = 0), leaving only the two
substitutions:

    sum_k u_k T_k = 64 u_0u_2^2 - u_0u_2^2 = 63 u_0u_2^2,

which is (2^{2N} - 1) u_{N-1}^2 u_0 at N = 3.  The cubic comes entirely from the boundary
terms: 64 from u_{-1} = 8u_2 (squared) and -1 from the u_3 = u_0/8 term.

Layout note.  The generator registers every string it draws and refuses to emit an SVG
whose text falls outside the canvas margin (exit status 3); text()/para() do the
registering, so a new label should be added with those rather than with rich().

Standard library only; emits SVG on stdout.  Regenerate with:

    python3 plot_dyadic_ring.py > dyadic_ring.svg
    rsvg-convert -w 1800 -o dyadic_ring.png dyadic_ring.svg
"""
import sys, math

W, H = 1500, 2150
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
# sibling figure does it, so the two figures share a typographic voice.
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
                elif ch in self.NARROW:
                    t += 0.34
                elif ch in self.WIDE:
                    t += 0.95
                elif ch in self.UPPER:
                    t += 0.70
                elif ch in 'Σ∈≡≈→':
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
    _CHECK.append((left, left + w, y, markup[:40]))
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

def circle(cx, cy, r, fill=LBLUE, stroke=BLUE, sw=2, dash=None, opacity=1.0):
    d = f' stroke-dasharray="{dash}"' if dash else ''
    return (f'<circle cx="{cx}" cy="{cy}" r="{r}" fill="{fill}" stroke="{stroke}" '
            f'stroke-width="{sw}"{d} opacity="{opacity}"/>')

def rect(x, y, w, h, fill='none', stroke=MGREY, sw=1.5, rx=14, dash=None, opacity=1.0):
    d = f' stroke-dasharray="{dash}"' if dash else ''
    return (f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="{rx}" fill="{fill}" '
            f'stroke="{stroke}" stroke-width="{sw}"{d} opacity="{opacity}"/>')

def node(x, y, r, label, fill=LBLUE, stroke=BLUE, tcol=BLUE, fs=16, dash=None,
         opacity=1.0):
    return (circle(x, y, r, fill=fill, stroke=stroke, dash=dash, opacity=opacity)
            + rich(x, y + fs * 0.35, label, size=fs, fill=tcol, opacity=opacity))

def vclamp(x, ytop, ybot):
    """hatched vertical wall, matching the sibling figure's clamps()"""
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

# ===========================================================================
o.append(f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" '
         f'viewBox="0 0 {W} {H}">')
o.append(defs())
o.append(f'<rect width="{W}" height="{H}" fill="{BG}"/>')

# ---- masthead --------------------------------------------------------------
o.append(rich(750, 50, "The smallest dyadic ring: self-similar closure at N = 3",
              size=27, weight='bold'))
o.append(rich(750, 78, "the clamped chain, closed — every shell's transfer scales as "
                       "2^{k}, and one edge carries the reverse twist 2^{−N}",
              size=14, fill=GREY))

# ---- equation strip --------------------------------------------------------
o.append(rect(60, 100, 1380, 94, fill=LGREY, stroke=MGREY, sw=1.2, rx=12))
o.append(rich(750, 142, "T_{k} = 2^{k}(u_{k-1}^{2} − 2u_{k}u_{k+1}),     "
                        "E = Σ u_{k}^{2},     H = Σ 4^{k}u_{k}^{2},     "
                        "ring:  u_{k+N} = u_{k}", size=20))
o.append(rich(750, 174, "weights 2^{2k} = 4^{k}:   1, 4, 16          "
                        "clamp  u_{−1} = u_{N} = 0          "
                        "twist  ×2^{−N} on the closing edge",
              size=13.5, fill=GREY))

# =========================== PANEL A: ring vs clamp ========================
AY, AH = 214, 560
o.append(panel(PAD, AY, 1440, AH,
               "A.  The ring of three shells — and the same shells clamped"))
o.append(rich(1440, AY + 34, "weights 2^{2k} = 4^{k}", size=12.5, anchor='end', fill=GREY))

# --- the ring (left half of panel A) ----------------------------------------
# Each figure is centred on both axes: in the card, or in its half of a
# two-column card.  The ring block measures 324 wide and the clamped chain 630,
# so with the rule centred in the gap it sits at 750 + (324-630)/2 = 597 and the
# two figures centre on 313 and 1044.  Card A's body runs from the foot of the
# title (253) to the rule at 702, centre ~477.
RA_DX, RA_DY = 91, -14
CA_DX, CA_DY = 74, -5
o.append(f'<g transform="translate({RA_DX},{RA_DY})">')
RX, RY, RH = 235.0, 356.0, 175.0            # apex x, apex y, height
RGRP = 32
P0 = (RX, RY)                                # u_0  (apex)
P1 = (RX - RH / math.sqrt(3.0), RY + RH)     # u_1  (bottom left)
P2 = (RX + RH / math.sqrt(3.0), RY + RH)     # u_2  (bottom right)

ra1, ra2 = step(P0, P1, 29 + 6)
o.append(arrow(ra1[0], ra1[1], ra2[0], ra2[1], color='ink', sw=2.4))
rb1, rb2 = step(P1, P2, 29 + 6)
o.append(arrow(rb1[0], rb1[1], rb2[0], rb2[1], color='ink', sw=2.4))
# the closing edge u_2 -> u_0, bowed out well clear of the triangle
rc1, rc2 = step(P2, P0, 32 + 8)
o.append(carrow(rc1[0], rc1[1], 400.0, 410.0, rc2[0], rc2[1],
                color='orange', sw=3.4, dash="9 6"))
o.append(text(300, 622, "×2^{−3}", size=14, fill=ORANGE))
o.append(text(300, 638, "the closing edge", size=11.5, fill=GREY))

o.append(node(P0[0], P0[1], RGRP, "u_{0}"))
o.append(node(P1[0], P1[1], RGRP, "u_{1}"))
o.append(node(P2[0], P2[1], RGRP, "u_{2}"))
o.append(text(P0[0], P0[1] - RGRP - 14, "u_{2} closes onto u_{0}", size=11.5, fill=GREY))
# the edge transfers, and the weight band under the ring
o.append(rich(172, 440, "T_{0}", size=14, fill=GREEN))
o.append(rich(308, 448, "T_{1}", size=14, fill=GREEN))
o.append(rich(346, 494, "T_{2}", size=13, fill=ORANGE))
o.append(text(P0[0], 596, "weight 2^{0} = 1", size=12.5, fill=GREY))
o.append(text(P1[0], 596, "2^{2} = 4", size=12.5, fill=GREY))
o.append(text(P2[0], 596, "2^{4} = 16", size=12.5, fill=GREY))
# legend under the ring
o.append(text(60, 656, "each edge carries one transfer", size=12.5, fill=GREY))
o.append(text(60, 676, "T_{k} = 2^{k}(u_{k-1}^{2} − 2u_{k}u_{k+1})", size=12.5, fill=GREY))
o.append('</g>')

# --- the clamped chain (right half of panel A) ------------------------------
# column rule, centred in the gap between the ring (right edge ~384) and the
# clamped chain (left edge ~644)
o.append(line(597, 262, 597, 692, stroke=MGREY, sw=1.2, dash="6 6"))
o.append(f'<g transform="translate({CA_DX},{CA_DY})">')
o.append(text(662, 296, "clamp:  cut the ring, kill both end fluxes", size=14, weight='bold'))
o.append('</g>')
o.append(line(60, 702, 1440, 702, stroke=MGREY, sw=1.2))
# the card-level note under the rule is content too: centred in the card
AN_DX = 360
o.append(f'<g transform="translate({AN_DX},0)">')
o.append(text(60, 726, "the ring closes only up to the scaling: the closing edge folds the "
                       "^k-weighting back on itself, and the fold leaves a seam",
              size=12.5, fill=GREY))
o.append(text(60, 744, "the clamp has no fold and no seam; the price of the seam is that "
                       "u_{N} = 2^{−N}q_{N} ≠ 0, so the profile is not a clamped solution",
              size=12.5, fill=GREY))
o.append('</g>')

o.append(f'<g transform="translate({CA_DX},{CA_DY})">')
CCY = 430
NX = [735, 935, 1135]
o.append(vclamp(NX[0] - 73, CCY - 34, CCY + 34))
o.append(vclamp(NX[2] + 73, CCY - 34, CCY + 34))
o.append(arrow(NX[0] - 91, CCY, NX[1] - 30, CCY, color='grey', sw=2.4, opacity=0.85))
o.append(arrow(NX[1] + 30, CCY, NX[2] + 91, CCY, color='grey', sw=2.4, opacity=0.85))
o.append(text(653, 370, "u_{−1} = 0", size=13, fill=GREY))
o.append(text(1217, 370, "u_{3} = 0", size=13, fill=GREY))
# the absent closing edge, struck out
o.append(carrow(NX[2] + 40, CCY + 52, (NX[2] + NX[0]) / 2, CCY + 150,
                NX[0] - 40, CCY + 52, color='grey', sw=2.2, dash="6 8", opacity=0.5))
MXM = (NX[0] + NX[2]) / 2
o.append(line(MXM - 13, CCY + 146, MXM + 13, CCY + 172, stroke=RED, sw=3.4))
o.append(line(MXM + 13, CCY + 146, MXM - 13, CCY + 172, stroke=RED, sw=3.4))
o.append(text(MXM + 26, CCY + 174, "closing edge absent", size=12.5, fill=RED))
for i, mx in enumerate(NX):
    o.append(node(mx, CCY, 30, f"u_{i}"))
    o.append(text(mx, CCY + 52, ["2^{0} = 1", "2^{2} = 4", "2^{4} = 16"][i],
                  size=12, fill=GREY))
o.append(text(NX[0] - 73, CCY + 104, "clamped end", size=11.5, fill=GREY))
o.append(text(NX[2] + 73, CCY + 104, "clamped end", size=11.5, fill=GREY))
o.append(text(662, 656, "only two edges;  both end fluxes are zero:   "
                        "Σ_{k} u_{k}T_{k} = 0", size=13, fill=GREEN))
o.append(text(662, 676, "the same three shells, closing edge removed", size=12, fill=GREY))
o.append('</g>')

# ==================== PANEL B: holonomy and the seam ========================
BY, BH = 792, 494
o.append(panel(PAD, BY, 1440, BH,
               "B.  Holonomy cancels — the seam survives"))

# --- left column: the turn, then the clamp ----------------------------------
# Card B's body runs from the foot of the title (831) to the card bottom (1286),
# centre ~1058.  The flow column measures 680 wide and the ring 409, so the rule
# sits at 750 + (680-409)/2 = 886 and the two columns centre on 458 and 1178.
BL_DX, BL_DY = 58, 12
BR_DX, BR_DY = 17, -32
o.append(f'<g transform="translate({BL_DX},{BL_DY})">')
o.append(text(60, 900, "one turn around the loop, from u_{2} back to u_{2}:", size=14))
BX = [60, 300, 540]
BW = 200
o.append(rect(BX[0], 920, BW, 58, fill=LGREY, stroke=MGREY, sw=1.4, rx=10))
o.append(rich(BX[0] + BW / 2, 956, "transfer ×2^{N} = ×8", size=13.5))
o.append(arrow(BX[0] + BW + 6, 949, BX[1] - 8, 949, color='grey', sw=2.2))
o.append(rect(BX[1], 920, BW, 58, fill=LGREY, stroke=MGREY, sw=1.4, rx=10))
o.append(rich(BX[1] + BW / 2, 956, "twist ×2^{−N} = ×1/8", size=13.5))
o.append(arrow(BX[1] + BW + 6, 949, BX[2] - 8, 949, color='grey', sw=2.2))
o.append(rect(BX[2], 920, BW, 58, fill=LGREEN, stroke=GREEN, sw=1.8, rx=10))
o.append(rich(BX[2] + BW / 2, 956, "product = 1", size=13.5))
o.append(text(60, 1030, "the twist reverses exactly the 2^{N} the transfer picks up, so "
                        "2^{N}·2^{−N} = 1 and the loop closes.", size=12.5, fill=GREY))
o.append(text(60, 1052, "But only up to the scaling — a seam survives:",
              size=12.5, fill=GREY))
o.append(line(60, 1076, 740, 1076, stroke=MGREY, sw=1.2, dash="5 6"))
# the two cuts, side by side: the clamp is clean, the twist is a defect
o.append(text(60, 1116, "clamp:  the cut is clean", size=13.5, fill=GREEN))
o.append(text(60, 1138, "F_{0} = F_{N} = 0 — no source", size=12.5, fill=GREY))
o.append(rect(60, 1152, 162, 52, fill=LGREY, stroke=MGREY, sw=1.4, rx=10))
o.append(vclamp(80, 1164, 1192))
o.append(rich(148, 1184, "clean cut", size=12.5))
o.append(text(420, 1116, "twist:  the cut is a defect", size=13.5, fill=ORANGE))
o.append(text(420, 1138, "(2^{2N} − 1)u_{N-1}^{2}u_{0} = 63u_{2}^{2}u_{0}",
              size=12.5, fill=ORANGE))
o.append(rect(420, 1152, 162, 52, fill=LORANGE, stroke=ORANGE, sw=1.4, rx=10))
o.append(carrow(438, 1188, 464, 1162, 470, 1188, color='orange', sw=3, dash="8 6"))
o.append(line(457, 1166, 471, 1180, stroke=RED, sw=3.2))
o.append(line(471, 1166, 457, 1180, stroke=RED, sw=3.2))
o.append(rich(508, 1184, "a defect", size=12.5, fill=ORANGE))
o.append('</g>')

# column rule, centred in the gap between the left column (right edge 740) and
# the ring figure (left edge ~957)
o.append(line(886, 890, 886, 1226, stroke=MGREY, sw=1.2, dash="6 6"))

# --- right column: the ring, closing edge carrying the defect ---------------
# same ring as panel A (radius 32, height 175), centred in the right column
o.append(f'<g transform="translate({BR_DX},{BR_DY})">')
SRX, SRY, SRH, SRR = 1090.0, 980.0, 175.0, 32
S0 = (SRX, SRY)
S1 = (SRX - SRH / math.sqrt(3.0), SRY + SRH)
S2 = (SRX + SRH / math.sqrt(3.0), SRY + SRH)
for U, V in ((S0, S1), (S1, S2)):
    rp, rq = step(U, V, SRR + 3)
    o.append(arrow(rp[0], rp[1], rq[0], rq[1], color='ink', sw=2.4, opacity=0.85))
rp, rq = step(S2, S0, SRR + 8)
o.append(carrow(rp[0], rp[1], (S2[0] + S0[0]) / 2 + 52, (S2[1] + S0[1]) / 2 - 100,
                rq[0], rq[1], color='orange', sw=3.4, dash="9 6"))
for U, lab in ((S0, "u_{0}"), (S1, "u_{1}"), (S2, "u_{2}")):
    o.append(node(U[0], U[1], SRR, lab, fs=16))
o.append(text(SRX + 168, SRY + 66, "closes onto u_{0}", size=11.5, fill=GREY))
o.append(text(S0[0] + 52, S0[1] + 4, "u_{−1} = 8u_{2}", size=12.5, anchor='start',
              fill=ORANGE))
o.append(rich(S2[0] + 52, S2[1] - 30, "seam: ×2^{−3}", size=12.5, anchor='start',
              fill=ORANGE))
o.append(rich(S2[0] + 52, S2[1] - 12, "a cubic, sign-dependent", size=11.5, anchor='start',
              fill=ORANGE))
o.append(rich(S2[0] + 52, S2[1] + 4, "energy source", size=11.5, anchor='start',
              fill=ORANGE))
o.append(text(SRX - 105, 1210, "the fold is not free: the closure holds only", size=11.5,
              fill=GREY))
o.append(text(SRX - 105, 1228, "up to the scaling, so u_{N} = 2^{−N}q_{N} ≠ 0.", size=11.5,
              fill=GREY))
o.append('</g>')

# ========================= PANEL C: reduced ODE ============================
CY2, CH2 = 1306, 490
o.append(panel(PAD, CY2, 1440, CH2, "C.  The reduced ODE, and the blow-up"))

# Card C's body runs from the foot of the title (1345) to the card bottom (1796),
# centre ~1570.  The statistics column measures 660 wide and the prose 544, so
# the rule sits at 750 + (660-544)/2 = 808 and the columns centre on 419 and 1139.
CL_DX, CL_DY = 29, -10
CR_DX, CR_DY = 43, -14
o.append(f'<g transform="translate({CL_DX},{CL_DY})">')
o.append(rect(60, 1390, 660, 88, fill=LGREY, stroke=MGREY, sw=1.2, rx=12))
o.append(text(84, 1422, "u_{k} = 2^{−k}q_{k},  q periodic on ℤ/3:", size=15))
o.append(text(84, 1458, "q_{k}′ = 4q_{k-1}^{2} − q_{k}q_{k+1},     k ∈ ℤ/3",
              size=20, weight='bold'))
o.append(text(60, 1512, "a solution family:  q_{k} ≡ c  ⇒  c′ = 4c^{2} − c^{2} = 3c^{2}",
              size=14))
o.append(text(60, 1540, "c(t) = c_{0}/(1 − 3c_{0}t)      blow-up time  t* = 1/(3c_{0})",
              size=14, fill=BLUE))

# numerically measured blow-up times
o.append(rect(60, 1568, 660, 202, fill=YTINT, stroke=MGREY, sw=1.2, rx=12))
o.append(text(84, 1598, "blow-up times of the reduced ODE — numerical (RK4), not proved:",
              size=12, fill=GREY))
BAR0, BAR1 = 96.0, 644.0
SCALE = (BAR1 - BAR0) / 0.36
o.append(line(BAR0, 1648, BAR1, 1648, stroke=GREY, sw=1.6))
for tv in (0.0, 0.1, 0.2, 0.3):
    tx = BAR0 + tv * SCALE
    o.append(line(tx, 1642, tx, 1654, stroke=GREY, sw=1.4))
    o.append(rich(tx, 1674, f"{tv:.1f}", size=11, fill=GREY))
DOTS = (("N=1  (1)", 0.333, BLUE), ("N=2  (1,1)", 0.333, GREEN),
        ("N=2  (1,2)", 0.217, PURPLE), ("N=3  (1,2,3)", 0.160, RED))
for lab, tv, col in DOTS:
    px = BAR0 + tv * SCALE
    o.append(circle(px, 1648, 7, fill=col, stroke=col, sw=1.2))
# every measurement, listed once, so the two coincident 0.333 s stay readable
o.append(text(84, 1722, "N=1 (1)  →  0.333        N=2 (1,1)  →  0.333        "
                        "N=2 (1,2)  →  0.217        N=3 (1,2,3)  →  0.160",
              size=12.5, fill=INK))
o.append(text(84, 1750, "the constant mode is the slowest of the four; the more shells carry "
                        "the profile, the sooner it turns over.", size=12, fill=GREY))
o.append('</g>')

# minimality of N = 3
# column rule, centred in the gap between the statistics block (right edge 720)
# and the prose column (left edge 824)
o.append(line(808, 1372, 808, 1768, stroke=MGREY, sw=1.2, dash="6 6"))
o.append(f'<g transform="translate({CR_DX},{CR_DY})">')
o.append(text(824, 1426, "Why N = 3 is the smallest ring that matters", size=15,
              weight='bold'))
o.append(para(824, 1462, "N = 1 — the minimum ring, and degenerate: there is no "
                         "interior triad, so the profile is pinned to 2^{−k}, a "
                         "function of k alone.", 13, 606))
o.append(para(824, 1534, "N = 2 — the smallest ring with two genuinely distinct "
                         "shells: u_{0} ≠ u_{1}.", 13, 606))
o.append(para(824, 1594, "N = 3 — the smallest ring with a full interior triad: "
                         "shell 1 is fed by shell 0 and drained by shell 2, and the "
                         "closing edge carries shell 2 back to shell 0.", 13, 606))
o.append(text(824, 1726, "so the smallest non-degenerate ring is N = 3.", size=14,
              fill=BLUE))
o.append(text(824, 1752, "everything drawn above is the N = 3 picture.", size=12, fill=GREY))
o.append('</g>')

# ========================= PANEL D: the caveats ============================
DY, DH = 1820, 250
o.append(panel(PAD, DY, 1440, DH, "D.  The honest caveats — read before believing C",
               fill="#fff8f4"))
o.append(rich(1440, DY + 34, "N = 3, drawn: a re-derivation, not a new blow-up",
              size=13, anchor='end', fill=RED))

CAV = [
    ("1", "The blow-up profile IS the repo's existing Cascade.selfSimilar, re-derived in "
          "log coordinates — not a new blow-up.", RED),
    ("2", "Its physical enstrophy is infinite: 4^{k}u_{k}^{2} = q_{k}^{2} is periodic, so "
          "the lattice sum diverges; H = Σ_{k<N}q_{k}^{2} is a per-period density, not the "
          "physical enstrophy.", ORANGE),
    ("3", "The profile does not satisfy the clamp (u_{N} = 2^{−N}q ≠ 0), so it is not a "
          "solution of the clamped model, and the clamped model's regularity is not in "
          "tension with it.", PURPLE),
    ("4", "Viscosity closes the ring only at e = 0; at the physical e = 2 the ansatz is a "
          "renormalization cycle, not a symmetry.", BLUE),
]
# Card D's body runs from the foot of the title (1859) to the card bottom (2070),
# centre ~1964; the caveat list is shifted onto that axis.
# Card D's body runs from the foot of the title (1859) to the card bottom (2070),
# centre ~1964.  The caveat list measures 1099 wide, so it is centred in the
# 1440-wide card: left edge 30 + (1440-1099)/2 = 200.
DL_DX, DL_DY = 146, 4
o.append(f'<g transform="translate({DL_DX},{DL_DY})">')
ry = DY + 70
for num, body, col in CAV:
    # the bullet is centred on the first line of its caveat: the line's optical
    # centre is baseline - 0.35*size, so the circle centre sits at ry + 3 and the
    # number shares the paragraph's baseline.
    o.append(circle(74, ry + 3, 19, fill="#ffffff", stroke=col, sw=2))
    o.append(rich(74, ry + 8, num, size=15, fill=col))
    o.append(para(112, ry + 8, body, 15, 1320, fill=INK, lh=21))
    ry += nlines(body, 15, 1320) * 21 + 24
o.append('</g>')

# ---- footer ----------------------------------------------------------------
o.append(line(60, 2092, 1440, 2092, stroke=MGREY, sw=1.2))
o.append(rich(750, 2122, "The clamped chain is regular at every finite N;  blow-up requires "
                         "N = ∞;  the ring is the self-similar closure, and the singularity "
                         "lives in the weights rather than in the nonlinearity.",
              size=12.5, fill=GREY))

o.append('</svg>')

# ---------------------------------------------------------------------------
# self-check: every registered string must sit inside the canvas margin
# ---------------------------------------------------------------------------
bad = [c for c in _CHECK if c[0] < PAD - 6 or c[1] > W - PAD + 6]
if bad:
    sys.stderr.write("LAYOUT: %d string(s) outside the canvas margin:\n" % len(bad))
    for left, right, y, s in bad:
        sys.stderr.write("   y=%6.1f  x=[%7.1f,%7.1f]  %r\n" % (y, left, right, s))
    raise SystemExit(3)

sys.stdout.write('\n'.join(o) + '\n')
