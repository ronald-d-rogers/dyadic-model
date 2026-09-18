#!/usr/bin/env python3
"""Why delta = 2.7, in 3-D: the jitter DEPTH on the Z axis (ribbon version).

Axes:

    X (u) = octave k  -- going to smaller scales
    Y (v) = spatial dimension n  -- real, from 2 to 6
    Z (w) = the local log-log exponent (slope of the peak/average asymptote)

Each ribbon is one dimension.  Its straight grey line is the MEAN, (n - delta)/2 at
the measured delta = 2.7; the coloured wiggly curve is the exponent actually realised
at that scale.  The vertical gap between the two IS the jitter depth, and the short
stalks mark it on one ribbon.

The ribbon at n = 4.7 = 2 + delta has mean exactly 1 -- the critical slope -- so its
wiggles straddle the boundary.  That is what makes a boundary case undecided octave
by octave, while the mean still fixes the classification.

The roughness is synthetic -- the real jitter statistics are not known to the author.
The mean plane and the identity of the crossing at 2 + delta are exact.

Standard library only.  Regenerate with:

    python3 plot_jitter_surface.py > jitter_surface.svg
    rsvg-convert -w 1600 -o jitter_surface.png jitter_surface.svg
"""
import math
import random
import sys

W, H = 1200, 700
DELTA = 2.7
DEPTH = 0.22                      # jitter depth, in slope units (1 s.d.)
K = 41                            # octave samples
NS = [2.0, 2.7, 3.4, 4.1, 4.7, 5.4, 6.0]
NMIN, NMAX = 2.0, 6.0
SLO, SHI = -0.6, 2.0

def mean_slope(n):
    return (n - DELTA) / 2.0

random.seed(9)
modes = [(random.uniform(1.0, 6.0), random.uniform(0.0, 2.0),
          random.uniform(0.0, 6.283), random.uniform(0.5, 1.3)) for _ in range(11)]

def raw(u, v):
    return sum(a * math.sin(2 * math.pi * (p * u + q * v) + ph) for (p, q, ph, a) in modes)

_grid = [raw(i / (K - 1), j / 10.0) for i in range(K) for j in range(11)]
_m = sum(_grid) / len(_grid)
_sd = (sum((x - _m) ** 2 for x in _grid) / len(_grid)) ** 0.5

def jit(u, v):
    return DEPTH * (raw(u, v) - _m) / _sd

def w_of(s):
    return max(0.0, min(1.0, (s - SLO) / (SHI - SLO)))

def PX(u, v):
    return 210.0 + 370.0 * u + 240.0 * v

def PY(u, v, w):
    return 560.0 + 55.0 * u - 130.0 * v - 300.0 * w

def proj(u, v, s):
    return (PX(u, v), PY(u, v, w_of(s)))

def colour(mean):
    t = max(-1.0, min(1.0, (mean - 1.0) / 0.6))
    u = abs(t)
    c0, c1 = ((250, 250, 250), (33, 102, 172)) if t < 0 else ((250, 250, 250), (178, 24, 43))
    return "#%02x%02x%02x" % tuple(int(round(c0[k] + u * (c1[k] - c0[k]))) for k in range(3))

o = []
o.append('<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d" viewBox="0 0 %d %d"'
         ' font-family="Helvetica Neue, Helvetica, Arial, sans-serif">' % (W, H, W, H))
o.append('<rect width="%d" height="%d" fill="#ffffff"/>' % (W, H))
o.append('<text x="60" y="44" font-size="22" font-weight="bold" fill="#111">'
         'Why delta = 2.7, in 3-D: the jitter depth on the Z axis</text>')
o.append('<text x="60" y="72" font-size="14" fill="#444">'
         'Z is the local exponent. Each ribbon is one spatial dimension: its straight grey line is the mean (n - delta)/2 at del'
         'ta = 2.7, and the wiggly curve is what is actually realised at that scale.</text>')
o.append('<text x="60" y="92" font-size="14" fill="#444">'
         'The vertical gap between a grey line and its curve is the jitter DEPTH. The ribbon at n = 4.7 = 2 + delta has mean exactly 1, the critical slope, so its wiggles straddle the boundary.</text>')

# --- the critical level: a faint wireframe floor at slope = 1 ---
w1 = w_of(1.0)
o.append('<rect x="0" y="0" width="0" height="0" fill="none"/>')
o.append('<polygon points="%s" fill="#f2f2f2" opacity="0.65"/>'
         % " ".join("%.1f,%.1f" % proj(u, v, 1.0) for (u, v) in ((0, 0), (1, 0), (1, 1), (0, 1))))
for t in (0.0, 0.25, 0.5, 0.75, 1.0):
    a = proj(t, 0.0, 1.0)
    b = proj(t, 1.0, 1.0)
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#bbb" stroke-width="0.9"/>' % (a[0], a[1], b[0], b[1]))
    a = proj(0.0, t, 1.0)
    b = proj(1.0, t, 1.0)
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#bbb" stroke-width="0.9"/>' % (a[0], a[1], b[0], b[1]))

# --- mean fan: straight grey lines, drawn far to near ---
for n in sorted(NS, key=lambda x: -(x - NMIN)):
    v = (n - NMIN) / (NMAX - NMIN)
    a = proj(0.0, v, mean_slope(n))
    b = proj(1.0, v, mean_slope(n))
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#888" stroke-width="1.6"'
             ' stroke-dasharray="6,4"/>' % (a[0], a[1], b[0], b[1]))

# --- the ribbons, far to near ---
for n in sorted(NS, key=lambda x: -(x - NMIN)):
    v = (n - NMIN) / (NMAX - NMIN)
    pts = []
    for i in range(K):
        u = i / (K - 1)
        x, y = proj(u, v, mean_slope(n) + jit(u, v))
        pts.append("%.1f,%.1f" % (x, y))
    o.append('<polyline fill="none" stroke="%s" stroke-width="2.6" points="%s"/>'
             % (colour(mean_slope(n)), " ".join(pts)))
    if n in (2.0, 4.7, 6.0):
        x, y = proj(1.0, v, mean_slope(n) + jit(1.0, v))
        o.append('<text x="%.1f" y="%.1f" font-size="12.5" font-weight="bold" fill="%s">n = %.1f</text>'
                 % (x + 8, y + 4, colour(mean_slope(n)), n))

# --- depth stalks on the ribbon at n = 2 + delta ---
vn = (2.0 + DELTA - NMIN) / (NMAX - NMIN)
for i in (6, 16, 26, 36):
    u = i / (K - 1)
    a = proj(u, vn, mean_slope(2.0 + DELTA))
    b = proj(u, vn, mean_slope(2.0 + DELTA) + jit(u, vn))
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#111" stroke-width="2"/>' % (a[0], a[1], b[0], b[1]))
    o.append('<circle cx="%.1f" cy="%.1f" r="2.6" fill="#111"/>' % (b[0], b[1]))
o.append('<line x1="60" y1="632" x2="60" y2="612" stroke="#111" stroke-width="2"/>')
o.append('<text x="72" y="628" font-size="12.5" fill="#111">the short dark stalks on the n = 4.7 ribbon mark the jitter depth at sample octaves</text>')

# --- axes ---
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="2"/>' % (PX(0, 0), PY(0, 0, 0), PX(1, 0), PY(1, 0, 0)))
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="2"/>' % (PX(0, 0), PY(0, 0, 0), PX(0, 1), PY(0, 1, 0)))
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="2"/>' % (PX(0, 0), PY(0, 0, 0), PX(0, 0), PY(0, 0, 1)))
o.append('<text x="%.1f" y="%.1f" font-size="13.5" fill="#333">octave &#8594; smaller scales</text>' % (PX(1, 0) + 14, PY(1, 0, 0) + 6))
o.append('<text x="%.1f" y="%.1f" font-size="13.5" fill="#333">spatial dimension n &#8594;</text>' % (PX(0, 1) + 8, PY(0, 1, 0) - 6))
o.append('<text x="%.1f" y="%.1f" font-size="13.5" fill="#333">local exponent (slope) &#8593;</text>' % (PX(0, 0) - 6, PY(0, 0, 1) - 14))
for s in (0.0, 1.0, 2.0):
    y = PY(0, 0, w_of(s))
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="1.5"/>' % (PX(0, 0) - 8, y, PX(0, 0), y))
    o.append('<text x="%.1f" y="%.1f" font-size="12" fill="#555" text-anchor="end">%d</text>' % (PX(0, 0) - 12, y + 4, int(s)))
o.append('<text x="%.1f" y="%.1f" font-size="12" fill="#666">the grey floor is slope = 1, the critical level</text>'
         % (proj(0.0, 1.0, 1.0)[0] + 6, proj(0.0, 1.0, 1.0)[1] + 14))

o.append('<text x="60" y="652" font-size="11.5" fill="#777">The ribbon at n = 4.7 = 2 + delta has mean exactly the critical slope 1, so its wiggles cross the critical floor both ways: that dimension is marginal octave by octave, while the mean still classifies it.</text>')
o.append('<text x="60" y="671" font-size="11.5" fill="#777">The roughness is synthetic &#8212; the real jitter statistics are not known to me. Exact: the mean plane (n - delta)/2, its crossing of slope 1 at n = 2 + delta, and the reading of the depth as the vertical gap.</text>')

o.append('</svg>')
sys.stdout.write("\n".join(o) + "\n")
