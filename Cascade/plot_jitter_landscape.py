#!/usr/bin/env python3
"""The jitter landscape: a dense waterfall, and the map of the same terrain.

Left panel -- the landscape seen from the side.  Twenty-one ribbons, one per spatial
dimension n from 1.5 to 6.5.  Each ribbon is the local exponent against octave; the
grey dashed line under it is that dimension's MEAN, (n - delta)/2 at delta = 2.7, and
the vertical gap is the jitter depth.  The faint floor is the critical level, slope 1.
Ribbons are coloured by their mean, so the blue-to-red progression is the
classification and the wiggles are the jitter.

Right panel -- the map (top view) of the same terrain.  Axes are octave across and
spatial dimension n up; colour is the local exponent, diverging about 1.  The straight
line is where the MEAN crosses the critical slope, at n = 2 + delta = 4.7; the ragged
curve is where the realised exponent crosses it.  The gap between the two is the whole
effect of the jitter.

The roughness is synthetic -- the real jitter statistics are not known to the author.
The mean plane, its identity as (n - delta)/2, and the crossing at n = 2 + delta are
exact.

Standard library only.  Regenerate with:

    python3 plot_jitter_landscape.py > jitter_landscape.svg
    rsvg-convert -w 1600 -o jitter_landscape.png jitter_landscape.svg
"""
import math
import random
import sys

W, H = 1200, 780
DELTA = 2.7
DEPTH = 0.22                     # jitter depth in slope units (1 s.d.)
K = 45                           # octave samples
NS = [1.5 + 0.25 * i for i in range(21)]
NMIN, NMAX = 1.5, 6.5
SLO, SHI = -1.0, 2.4

def mean_slope(n):
    return (n - DELTA) / 2.0

random.seed(9)
modes = [(random.uniform(1.0, 6.0), random.uniform(0.0, 2.0),
          random.uniform(0.0, 6.283), random.uniform(0.5, 1.3)) for _ in range(11)]

def raw(u, v):
    return sum(a * math.sin(2 * math.pi * (p * u + q * v) + ph) for (p, q, ph, a) in modes)

_grid = [raw(i / (K - 1), j / 20.0) for i in range(K) for j in range(21)]
_m = sum(_grid) / len(_grid)
_sd = (sum((x - _m) ** 2 for x in _grid) / len(_grid)) ** 0.5

def jit(u, v):
    return DEPTH * (raw(u, v) - _m) / _sd

def ramp(s, mid=(200, 200, 200)):
    """diverging about slope 1; the midpoint is a light grey so it stays visible."""
    t = max(-1.0, min(1.0, (s - 1.0) / 0.7))
    u = abs(t)
    end = (33, 102, 172) if t < 0 else (178, 24, 43)
    return "#%02x%02x%02x" % tuple(int(round(mid[k] + u * (end[k] - mid[k]))) for k in range(3))

# ---------------- projections ----------------
def AX(u, v):
    return 105.0 + 300.0 * u + 195.0 * v

def AY(u, v, s):
    w = max(0.0, min(1.0, (s - SLO) / (SHI - SLO)))
    return 520.0 + 45.0 * u - 108.0 * v - 265.0 * w

BX0, BX1 = 720.0, 1120.0
BY0, BY1 = 560.0, 460.0 - 330.0     # BY1 is the top (n = NMAX)

def by(n):
    return BY0 + (n - NMIN) * (BY1 - BY0) / (NMAX - NMIN)

def frontier(pts):
    s = " ".join(pts)
    return ('<polyline fill="none" stroke="#111" stroke-width="4.5" points="%s"/>' % s,
            '<polyline fill="none" stroke="#ffffff" stroke-width="2.2" points="%s"/>' % s)

o = []
o.append('<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d" viewBox="0 0 %d %d"'
         ' font-family="Helvetica Neue, Helvetica, Arial, sans-serif">' % (W, H, W, H))
o.append('<rect width="%d" height="%d" fill="#ffffff"/>' % (W, H))
o.append('<text x="60" y="44" font-size="22" font-weight="bold" fill="#111">'
         'The jitter landscape: twenty-one dimensions, and its map</text>')
o.append('<text x="60" y="72" font-size="13" fill="#444">'
         'Left: one ribbon per dimension n from 1.5 to 6.5; the vertical axis is the local exponent, and the grey dashed line under each ribbon is that dimension\'s mean (n - delta)/2.</text>')
o.append('<text x="60" y="92" font-size="13" fill="#444">'
         'Right: the same terrain from above. Colour is the local exponent, diverging about the critical slope 1. The straight line is the mean crossing at n = 2 + delta = 4.7; the white curve is the realised one.</text>')

# ================= LEFT: the waterfall =================
o.append('<text x="105" y="126" font-size="15" font-weight="bold" fill="#111">the landscape, from the side</text>')

# critical floor at slope = 1
o.append('<polygon points="%s" fill="#f4f4f4" opacity="0.8"/>'
         % " ".join("%.1f,%.1f" % (AX(u, v), AY(u, v, 1.0)) for (u, v) in ((0, 0), (1, 0), (1, 1), (0, 1))))
for t in (0.25, 0.5, 0.75):
    a = (AX(t, 0.0), AY(t, 0.0, 1.0))
    b = (AX(t, 1.0), AY(t, 1.0, 1.0))
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#ccc" stroke-width="0.9"/>' % (a + b))
for t in (0.25, 0.5, 0.75):
    a = (AX(0.0, t), AY(0.0, t, 1.0))
    b = (AX(1.0, t), AY(1.0, t, 1.0))
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#ccc" stroke-width="0.9"/>' % (a + b))

for n in sorted(NS, reverse=True):
    v = (n - NMIN) / (NMAX - NMIN)
    # mean line
    a = (AX(0.0, v), AY(0.0, v, mean_slope(n)))
    b = (AX(1.0, v), AY(1.0, v, mean_slope(n)))
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#999" stroke-width="1.1"'
             ' stroke-dasharray="5,4"/>' % (a + b))
    pts = []
    for i in range(K):
        u = i / (K - 1)
        pts.append("%.1f,%.1f" % (AX(u, v), AY(u, v, mean_slope(n) + jit(u, v))))
    o.append('<polyline fill="none" stroke="%s" stroke-width="2.2" points="%s"/>'
             % (ramp(mean_slope(n)), " ".join(pts)))

# axes of the left panel
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="2"/>'
         % (AX(0, 0), AY(0, 0, 0), AX(1, 0), AY(1, 0, 0)))
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="2"/>'
         % (AX(0, 0), AY(0, 0, 0), AX(0, 1), AY(0, 1, 0)))
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="2"/>'
         % (AX(0, 0), AY(0, 0, 0), AX(0, 0), AY(0, 0, 1)))
o.append('<text x="%.1f" y="%.1f" font-size="13" fill="#333">octave &#8594; smaller scales</text>' % (AX(1, 0) + 10, AY(1, 0, 0) + 4))
o.append('<text x="%.1f" y="%.1f" font-size="13" fill="#333">dimension n &#8594;</text>' % (AX(0, 1) + 6, AY(0, 1, 0) - 4))
o.append('<text x="%.1f" y="%.1f" font-size="13" fill="#333">local exponent (slope) &#8593;</text>' % (AX(0, 0) - 10, AY(0, 0, 1) - 12))
for s in (0.0, 1.0, 2.0):
    y = AY(0, 0, s)
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="1.4"/>' % (AX(0, 0) - 7, y, AX(0, 0), y))
    o.append('<text x="%.1f" y="%.1f" font-size="11.5" fill="#555" text-anchor="end">%d</text>' % (AX(0, 0) - 11, y + 4, int(s)))
o.append('<text x="%.1f" y="%.1f" font-size="12" fill="#666">the faint floor is slope 1, the critical level</text>' % (AX(0, 0) - 40, 600))

# ================= RIGHT: the map =================
o.append('<text x="%.1f" y="126" font-size="15" font-weight="bold" fill="#111">the map (top view)</text>' % BX0)

COLS, ROWS = 64, 44
CW = (BX1 - BX0) / COLS
CH = (BY0 - BY1) / ROWS
for r in range(ROWS):
    n = NMIN + (NMAX - NMIN) * (r + 0.5) / ROWS
    for c in range(COLS):
        u = (c + 0.5) / COLS
        s = mean_slope(n) + jit(u, (n - NMIN) / (NMAX - NMIN))
        o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="%s"/>'
                 % (BX0 + c * CW, BY0 - (r + 1) * CH, CW + 0.6, CH + 0.6, ramp(s)))

# mean frontier: n = 2 + delta
for nn in (2.0 + DELTA,):
    y = by(nn)
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#111" stroke-width="3"/>' % (BX0, y, BX1, y))

# realised frontier
seg = []
for c in range(COLS):
    u = (c + 0.5) / COLS
    prev = mean_slope(NMIN) + jit(u, 0.0) - 1.0
    hit = None
    for r in range(1, ROWS):
        n = NMIN + (NMAX - NMIN) * (r + 0.5) / ROWS
        cur = mean_slope(n) + jit(u, (n - NMIN) / (NMAX - NMIN)) - 1.0
        if (prev < 0) != (cur < 0):
            f = -prev / (cur - prev)
            nn = NMIN + (NMAX - NMIN) * (r - 0.5 + f) / ROWS
            hit = nn
            break
        prev = cur
    if hit is None:
        if len(seg) > 1:
            o.extend(frontier(seg))
        seg = []
    else:
        seg.append("%.1f,%.1f" % (BX0 + (c + 0.5) * CW, by(hit)))
if len(seg) > 1:
    o.extend(frontier(seg))

o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="none" stroke="#222" stroke-width="1.6"/>'
         % (BX0, BY1, BX1 - BX0, BY0 - BY1))
for nn in (2, 3, 4, 5, 6):
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222"/>' % (BX0 - 6, by(nn), BX0, by(nn)))
    o.append('<text x="%.1f" y="%.1f" font-size="12" fill="#555" text-anchor="end">%d</text>' % (BX0 - 10, by(nn) + 4, nn))
for u in (0.0, 0.25, 0.5, 0.75, 1.0):
    x = BX0 + u * (BX1 - BX0)
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222"/>' % (x, BY0, x, BY0 + 6))
o.append('<text x="%.1f" y="%.1f" font-size="13" text-anchor="middle" fill="#333">octave &#8594; smaller scales</text>'
         % ((BX0 + BX1) / 2, BY0 + 24))
o.append('<text x="%.1f" y="%.1f" font-size="13" text-anchor="middle" fill="#333" transform="rotate(-90 %.1f %.1f)">spatial dimension n</text>'
         % (BX0 - 44, (BY0 + BY1) / 2, BX0 - 44, (BY0 + BY1) / 2))
o.append('<text x="%.1f" y="%.1f" font-size="12.5" font-weight="bold" fill="#7b0f14">the white curve is the realised frontier</text>'
         % (BX0 + 6, BY1 + 16))

o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#111" stroke-width="3"/>' % (BX0, 602, BX0 + 40, 602))
o.append('<text x="%.1f" y="602" font-size="12" fill="#111" dominant-baseline="middle">mean frontier, n = 2 + delta = 4.7 (exact)</text>' % (BX0 + 48))
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#111" stroke-width="4.5"/>' % (BX0, 622, BX0 + 40, 622))
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#ffffff" stroke-width="2.2"/>' % (BX0, 622, BX0 + 40, 622))
o.append('<text x="%.1f" y="622" font-size="12" fill="#111" dominant-baseline="middle">realised frontier: where the local exponent crosses 1</text>' % (BX0 + 48))

o.append('<text x="60" y="654" font-size="11.5" fill="#777">Left: ribbons coloured by their MEAN, so the blue-to-red progression is the classification; the wiggle about each grey dashed mean line is the jitter depth.</text>')
o.append('<text x="60" y="672" font-size="11.5" fill="#777">Right: the same terrain from above. The straight black line is exact, n = 2 + delta; the width of the white curve\'s wander about it is the jitter depth.</text>')
o.append('<text x="60" y="690" font-size="11.5" fill="#777">The roughness is synthetic &#8212; the real jitter statistics are not known to me.</text>')
o.append('<text x="60" y="708" font-size="11.5" fill="#777">Exact: the mean plane (n - delta)/2, its crossing of slope 1 at n = 2 + delta, and the depth as the vertical gap.</text>')

o.append('</svg>')
sys.stdout.write("\n".join(o) + "\n")
