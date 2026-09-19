#!/usr/bin/env python3
"""Schematic of the truncated dyadic shell model.

Standard library only; emits SVG on stdout.  Regenerate with:

    python3 plot_truncated_model.py > truncated_dyadic_model.svg
    rsvg-convert -w 1800 -o truncated_dyadic_model.png truncated_dyadic_model.svg

The picture is a diagram, not a solution plot: it shows the ladder of N retained
shells, the nearest-neighbour coupling, the Dirichlet clamps that define the
truncation, and the two structural facts that make the truncated model regular
(the transfer pairing cancels identically, and a finite range lets the energy
dominate every weighted norm) versus the untruncated lattice where both fail.
"""
import sys, math

W, H = 1500, 1310
BG = "#ffffff"
INK = "#252525"; GREY = "#737373"; MGREY = "#bdbdbd"; LGREY = "#f4f4f4"
BLUE = "#08519c"; LBLUE = "#c6dbef"
RED = "#a50f15"; LRED = "#fcbba1"
GREEN = "#238b45"; LGREEN = "#d9f0d3"
PURPLE = "#6a51a3"; LPURPLE = "#dadaeb"
WALL = "#969696"

o = []
def esc(s):
    return s.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')

MARK = {'ink': INK, 'grey': GREY, 'blue': BLUE, 'red': RED, 'green': GREEN, 'purple': PURPLE}
MID = {'ink': 'm_ink', 'grey': 'm_grey', 'blue': 'm_blue', 'red': 'm_red',
       'green': 'm_green', 'purple': 'm_purple'}

def defs():
    s = ['<defs>']
    for k, c in MARK.items():
        s.append(f'<marker id="{MID[k]}" viewBox="0 0 10 10" refX="8.5" refY="5" '
                 f'markerWidth="6.5" markerHeight="6.5" orient="auto-start-reverse">'
                 f'<path d="M 0 0 L 10 5 L 0 10 z" fill="{c}"/></marker>')
    s.append('</defs>')
    return ''.join(s)

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

def rich(x, y, markup, size=14, anchor='middle', fill=INK, weight='normal', opacity=1.0):
    """Text with _{...} subscripts and ^{...} superscripts, rendered via dy tspans."""
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
    return (f'<text x="{x}" y="{y}" text-anchor="{anchor}" fill="{fill}" font-weight="{weight}" '
            f'opacity="{opacity}" font-family="Helvetica, Arial, sans-serif">'
            + ''.join(parts) + '</text>')

def line(x1, y1, x2, y2, stroke=INK, sw=2, dash=None, opacity=1.0, cap='round'):
    d = f' stroke-dasharray="{dash}"' if dash else ''
    return (f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="{stroke}" stroke-width="{sw}" '
            f'stroke-linecap="{cap}"{d} opacity="{opacity}"/>')

def arrow(x1, y1, x2, y2, color='ink', sw=2, dash=None, opacity=1.0):
    d = f' stroke-dasharray="{dash}"' if dash else ''
    return (f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="{MARK[color]}" stroke-width="{sw}" '
            f'stroke-linecap="round" marker-end="url(#{MID[color]})"{d} opacity="{opacity}"/>')

def carrow(x1, y1, x2, y2, color='ink', sw=2, bend=-80, dash=None, opacity=1.0):
    dx = x2 - x1; dy = y2 - y1; L = math.hypot(dx, dy) or 1.0
    px, py = -dy / L, dx / L
    mx, my = (x1 + x2) / 2, (y1 + y2) / 2
    qx, qy = mx + 2 * bend * px, my + 2 * bend * py
    d = f' stroke-dasharray="{dash}"' if dash else ''
    return (f'<path d="M {x1} {y1} Q {qx:.1f} {qy:.1f} {x2} {y2}" fill="none" stroke="{MARK[color]}" '
            f'stroke-width="{sw}" stroke-linecap="round" marker-end="url(#{MID[color]})"{d} '
            f'opacity="{opacity}"/>')

def circle(cx, cy, r, fill=LBLUE, stroke=BLUE, sw=2, dash=None, opacity=1.0):
    d = f' stroke-dasharray="{dash}"' if dash else ''
    return (f'<circle cx="{cx}" cy="{cy}" r="{r}" fill="{fill}" stroke="{stroke}" '
            f'stroke-width="{sw}"{d} opacity="{opacity}"/>')

def rect(x, y, w, h, fill='none', stroke=MGREY, sw=1.5, rx=14, dash=None, opacity=1.0):
    d = f' stroke-dasharray="{dash}"' if dash else ''
    return (f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="{rx}" fill="{fill}" '
            f'stroke="{stroke}" stroke-width="{sw}"{d} opacity="{opacity}"/>')

def node(x, y, r, label, fill=LBLUE, stroke=BLUE, tcol=BLUE, fs=15, dash=None, opacity=1.0):
    return (circle(x, y, r, fill=fill, stroke=stroke, dash=dash, opacity=opacity)
            + rich(x, y + fs * 0.35, label, size=fs, fill=tcol, opacity=opacity))

def clamps(x, y0, y1, label, labely):
    s = [line(x, y0, x, y1, stroke=WALL, sw=9)]
    n = int((y1 - y0) // 15)
    for i in range(n + 1):
        yy = y0 + i * 15
        s.append(line(x - 12, yy + 9, x + 12, yy - 9, stroke=WALL, sw=2))
    if label:
        s.append(rich(x, labely, label, size=13, fill=GREY))
    return ''.join(s)

def panel(x, y, w, h, title):
    s = [rect(x, y, w, h, fill=BG, stroke=MGREY, sw=1.5, rx=16)]
    if title:
        s.append(rich(x + 26, y + 33, title, size=20, anchor='start', weight='bold'))
    return ''.join(s)

# ----------------------------------------------------------------------------
o.append(f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" '
         f'viewBox="0 0 {W} {H}">')
o.append(defs())
o.append(f'<rect width="{W}" height="{H}" fill="{BG}"/>')

# ---- masthead --------------------------------------------------------------
o.append(rich(750, 46, "The truncated dyadic shell model", size=27, weight='bold'))
o.append(rich(750, 74, "one amplitude per octave, nearest-neighbour coupling, N retained shells clamped at both ends",
              size=14, fill=GREY))

# ---- equation strip --------------------------------------------------------
o.append(rect(60, 92, 1380, 108, fill=LGREY, stroke=MGREY, sw=1.2, rx=12))
o.append(rich(750, 132, "u_{k}′ = 2^{k}(u_{k-1}^{2} − 2u_{k}u_{k+1}) + κθ_{k} − ν2^{ek}u_{k}"
                        ",      0 ≤ k ≤ N−1,      u_{−1} = u_{N} = 0",
              size=20))
o.append(rich(300, 172, "transfer: EVEN in u  (sign-blind)", size=13, fill=GREEN))
o.append(rich(760, 172, "viscosity: −ν2^{ek}u_{k}, ODD in u", size=13, fill=BLUE))
o.append(rich(1215, 172, "buoyancy: κθ_{k}, reads no u", size=13, fill=PURPLE))

# ============================ PANEL A: the ladder ==========================
o.append(panel(30, 220, 1440, 370, "A.  The ladder of retained shells, with clamped ends"))
o.append(rich(1450, 252, "nearest-neighbour coupling only: shell k feels k−1 and k+1",
              size=13, anchor='end', fill=GREY))

def X(k):
    return 150 + (k + 1) * 172

YB = 452
# bracket over the retained range
o.append(line(322, 276, 322, 284, stroke=GREY, sw=2))
o.append(line(1182, 276, 1182, 284, stroke=GREY, sw=2))
o.append(line(322, 280, 1182, 280, stroke=GREY, sw=2))
o.append(rich(752, 270, "retained shells k = 0 … N−1   (N = 6 drawn)", size=13, fill=GREY))

# coupling chain
for k in range(-1, 6):
    o.append(arrow(X(k) + 30, YB, X(k + 1) - 30, YB, color='grey', sw=2.6, opacity=0.55))

# clamps
o.append(clamps(150, 300, 480, "", 0))
o.append(clamps(1354, 300, 480, "", 0))
o.append(rich(150, 290, "u_{−1} = 0", size=13, fill=GREY))
o.append(rich(1354, 290, "u_{N} = 0", size=13, fill=GREY))
o.append(rich(150, 512, "clamped end", size=12, fill=GREY))
o.append(rich(1354, 512, "clamped end", size=12, fill=GREY))

# retained nodes
for k in range(6):
    o.append(node(X(k), YB, 27, f"u_{k}"))
# the two Dirichlet nodes
o.append(node(150, YB, 27, "0", fill="#ffffff", stroke=WALL, tcol=GREY, dash="5 4"))
o.append(node(1354, YB, 27, "0", fill="#ffffff", stroke=WALL, tcol=GREY, dash="5 4"))

# highlighted shell k = 2 and its two coupling arrows
o.append(circle(X(2), YB, 37, fill='none', stroke=INK, sw=1.6, dash="4 4"))
o.append(carrow(X(1) + 30, YB, X(2) - 30, YB, color='green', sw=3.2, bend=-125))
o.append(carrow(X(3) - 30, YB, X(2) + 30, YB, color='red', sw=3.2, bend=125))
o.append(rich(580, 302, "gain:  2^{k}u_{k-1}^{2}", size=14, fill=GREEN))
o.append(rich(752, 302, "loss:  −2·2^{k}u_{k}u_{k+1}", size=14, fill=RED))

# weights
for k in range(6):
    o.append(rich(X(k), 502, f"2^{{{k}}}" + (f" = {2**k}" if k else " = 1"), size=13, fill=GREY))
o.append(arrow(322, 540, 1182, 540, color='grey', sw=2.2, opacity=0.8))
o.append(rich(752, 564, "shell weight 2^{k} increases to the right  →  smaller scales",
              size=13, fill=GREY))

# ============================ PANEL B: the triad ===========================
o.append(panel(30, 610, 700, 330, "B.  Zoom: shell k is fed by k−1 and drained with k+1"))
o.append(rich(90, 800, "⋯", size=24, fill=GREY))
o.append(rich(690, 800, "⋯", size=24, fill=GREY))
o.append(node(170, 800, 31, "u_{k-1}"))
o.append(node(390, 800, 31, "u_{k}", fill=LRED, stroke=RED, tcol=RED))
o.append(node(610, 800, 31, "u_{k+1}"))
o.append(carrow(170 + 33, 800, 390 - 33, 800, color='green', sw=3.2, bend=-75))
o.append(carrow(610 - 33, 800, 390 + 33, 800, color='red', sw=3.2, bend=75))
o.append(rich(280, 685, "gain:  2^{k}u_{k-1}^{2}", size=14, fill=GREEN))
o.append(rich(500, 685, "loss:  −2·2^{k}u_{k}u_{k+1}", size=14, fill=RED))
o.append(rich(60, 872, "viscosity:  −ν2^{ek}u_{k}   drains shell k", size=13,
              anchor='start', fill=BLUE))
o.append(rich(60, 898, "buoyancy:  κθ_{k}   forces shell k", size=13,
              anchor='start', fill=PURPLE))
o.append(rich(60, 924, "no coupling beyond nearest neighbours", size=13,
              anchor='start', fill=GREY))

# ============================ PANEL C: cancellation ========================
o.append(panel(750, 610, 720, 330, "C.  Truncation regularizes: the transfer cancels"))
o.append(clamps(812, 692, 792, "", 0))
o.append(clamps(1408, 692, 792, "", 0))
mxs = [872, 977, 1082, 1187, 1292]
for a, b in zip(mxs, mxs[1:]):
    o.append(arrow(a + 20, 742, b - 20, 742, color='grey', sw=2.4, opacity=0.7))
for i, mx in enumerate(mxs):
    o.append(node(mx, 742, 15, "", fill=LBLUE, stroke=BLUE, tcol=BLUE, fs=1))
    o.append(rich(mx, 778, f"{i}", size=12, fill=GREY))
o.append(rich(1110, 672, "internal fluxes cancel pairwise; the end fluxes are killed by the clamps",
              size=13, fill=GREY))
o.append(rich(775, 838, "along any solution:", size=15, anchor='start'))
o.append(rich(775, 872, "E′ = 2κ Σ u_{k}θ_{k} − 2ν Σ 2^{ek}u_{k}^{2}", size=19,
              anchor='start', weight='bold'))
o.append(rich(775, 902, "the transfer term is identically 0 — for every sign pattern",
              size=13, anchor='start', fill=GREEN))
o.append(rich(775, 926, "finite range  ⇒  every weighted norm ≤ 2^{s(N−1)}E",
              size=13, anchor='start', fill=GREY))

# ============================ PANEL D: truncated vs not ====================
o.append(panel(30, 960, 1440, 300, "D.  Where the regularity comes from — and where it stops"))
o.append(line(750, 1010, 750, 1240, stroke=MGREY, sw=1.5, dash="6 6"))
o.append(rich(400, 1022, "Truncated:  k = 0, …, N−1   (finite)", size=16, weight='bold'))
o.append(rich(1100, 1022, "Untruncated:  k ∈ ℕ   (no wall at ∞)", size=16, weight='bold'))
# left ladder
o.append(clamps(100, 1052, 1128, "", 0))
o.append(clamps(680, 1052, 1128, "", 0))
lx = [215, 340, 465, 590]
for a, b in zip(lx, lx[1:]):
    o.append(arrow(a + 18, 1090, b - 18, 1090, color='grey', sw=2.2, opacity=0.7))
for i, mx in enumerate(lx):
    o.append(node(mx, 1090, 15, "", fill=LBLUE, stroke=BLUE, tcol=BLUE, fs=1))
o.append(rich(400, 1160, "weights 2^{k} finite:   Σ 2^{sk}u_{k}^{2} ≤ 2^{s(N−1)}E", size=13))
o.append(rich(400, 1186, "no finite-time blowup for e ≥ 0, ν > 0, any κ", size=13))
o.append(rich(400, 1214, "(truncated_globally_regular)", size=12, fill=GREY))
# right ladder
rx = [830, 930, 1030, 1130, 1230]
for i, mx in enumerate(rx):
    op = 1.0 - 0.13 * i
    o.append(node(mx, 1090, 15, "", fill=LBLUE, stroke=BLUE, tcol=BLUE, fs=1, opacity=op))
    o.append(arrow(mx + 18, 1090, mx + 82, 1090, color='grey', sw=2.2, opacity=0.65 * op))
    o.append(rich(mx, 1122, f"{2**i}", size=11, fill=GREY, opacity=op))
o.append(arrow(1265, 1090, 1420, 1090, color='red', sw=2.6))
o.append(rich(1345, 1070, "flux escapes", size=13, fill=RED))
o.append(rich(1100, 1160, "weights 4^{k} unbounded; E no longer dominates enstrophy", size=13))
o.append(rich(1100, 1186, "genuine blowup scenarios live beyond the truncation", size=13))
o.append(rich(1100, 1214, "(not proved in this repo — OUTCOME.md)", size=12, fill=GREY))

o.append(rich(750, 1288, "The transfer is even in u, so this cancellation is sign-blind: no schedule of sign flips "
                         "creates an energy source.  The sign-sensitive object is the e = 1 enstrophy budget "
                         "(SignReversal.lean).", size=12.5, fill=GREY))

o.append('</svg>')
sys.stdout.write('\n'.join(o) + '\n')
