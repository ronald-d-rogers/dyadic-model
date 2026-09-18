#!/usr/bin/env python3
"""The wide view: jitter out to high octaves, and why width decides the question.

Left panel -- the landscape stretched over 128 octaves (38 decades of scale).  One
ribbon per dimension, the vertical axis being the local exponent, the faint floor the
critical slope 1.  At this width the jitter is no longer a gentle swell: it oscillates
many times along each ribbon.

Right panel -- the point of the width.  For three dimensions the RUNNING MEAN of the
local exponent is plotted against the number of octaves averaged over, with the
+-1 s.d. band of that mean.  At few octaves the bands of n = 4.0, 4.7 and 5.4 overlap
the critical line and the classification is undecided; by many octaves they have
separated and the verdict is fixed.  The mean is what decides, and the mean only
becomes visible by looking wide.

HONESTY.  The roughness is synthetic: the real jitter statistics are not known to the
author.  More importantly, 128 octaves is an extrapolation of the FORMULA, not of any
flow -- real turbulence has an inertial range of order ten octaves, beyond which
viscosity cuts the cascade off.  And in our own shell model there is no jitter at all.
Exact here: the mean plane (n - delta)/2, its crossing of slope 1 at n = 2 + delta, and
the fact that the running mean converges to the mean.

Standard library only.  Regenerate with:

    python3 plot_jitter_wide.py > jitter_wide.svg
    rsvg-convert -w 1600 -o jitter_wide.png jitter_wide.svg
"""
import math
import random
import sys

W, H = 1200, 720
DELTA = 2.7
DEPTH = 0.22
NS = [2.0, 2.5, 3.0, 3.5, 4.0, 4.5, 5.0, 5.5, 6.0]
NMIN, NMAX = 1.8, 6.2
SLO, SHI = -1.0, 2.4
KOCT = 128                       # octaves shown
K = 513                          # samples along the octave axis
CORR = 5.0                       # jitter correlation length, in octaves

def mean_slope(n):
    return (n - DELTA) / 2.0

random.seed(17)
modes = [(random.uniform(2.0, 40.0), random.uniform(0.0, 2.0),
          random.uniform(0.0, 6.283), random.uniform(0.5, 1.3)) for _ in range(16)]

def raw(u, v):
    return sum(a * math.sin(2 * math.pi * (p * u + q * v) + ph) for (p, q, ph, a) in modes)

_grid = [raw(i / (K - 1), j / 12.0) for i in range(K) for j in range(13)]
_m = sum(_grid) / len(_grid)
_sd = (sum((x - _m) ** 2 for x in _grid) / len(_grid)) ** 0.5

def jit(u, v):
    return DEPTH * (raw(u, v) - _m) / _sd

def ramp(s, mid=(200, 200, 200)):
    t = max(-1.0, min(1.0, (s - 1.0) / 0.7))
    u = abs(t)
    end = (33, 102, 172) if t < 0 else (178, 24, 43)
    return "#%02x%02x%02x" % tuple(int(round(mid[k] + u * (end[k] - mid[k]))) for k in range(3))

def AX(u, v):
    return 100.0 + 340.0 * u + 175.0 * v

def AY(u, v, s):
    w = max(0.0, min(1.0, (s - SLO) / (SHI - SLO)))
    return 500.0 + 40.0 * u - 95.0 * v - 250.0 * w

BX0, BX1 = 700.0, 1140.0
BSLO, BSHI = 0.4, 1.6
BYB, BYT = 520.0, 150.0

def by(s):
    return BYB - (s - BSLO) * (BYB - BYT) / (BSHI - BSLO)

o = []
o.append('<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d" viewBox="0 0 %d %d"'
         ' font-family="Helvetica Neue, Helvetica, Arial, sans-serif">' % (W, H, W, H))
o.append('<rect width="%d" height="%d" fill="#ffffff"/>' % (W, H))
o.append('<text x="60" y="44" font-size="22" font-weight="bold" fill="#111">'
         'The wide view: jitter out to high octaves</text>')
o.append('<text x="60" y="72" font-size="13" fill="#444">'
         'Left: the landscape stretched over 128 octaves &#8212; 38 decades of scale. At this width the jitter oscillates many times along every ribbon; the faint floor is the critical slope 1.</text>')
o.append('<text x="60" y="92" font-size="13" fill="#444">'
         'Right: the running mean of the local exponent against the number of octaves averaged over, for three dimensions, with its band. Few octaves: undecided. Many: separated.</text>')

# ---------------- LEFT: the wide fan ----------------
o.append('<text x="100" y="126" font-size="15" font-weight="bold" fill="#111">128 octaves, nine dimensions</text>')
o.append('<polygon points="%s" fill="#f4f4f4" opacity="0.8"/>'
         % " ".join("%.1f,%.1f" % (AX(u, v), AY(u, v, 1.0)) for (u, v) in ((0, 0), (1, 0), (1, 1), (0, 1))))
for n in sorted(NS, reverse=True):
    v = (n - NMIN) / (NMAX - NMIN)
    a = (AX(0.0, v), AY(0.0, v, mean_slope(n)))
    b = (AX(1.0, v), AY(1.0, v, mean_slope(n)))
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#aaa" stroke-width="1"'
             ' stroke-dasharray="5,4"/>' % (a + b))
    pts = ["%.1f,%.1f" % (AX(i / (K - 1), v), AY(i / (K - 1), v, mean_slope(n) + jit(i / (K - 1), v)))
           for i in range(K)]
    o.append('<polyline fill="none" stroke="%s" stroke-width="1.5" points="%s"/>'
             % (ramp(mean_slope(n)), " ".join(pts)))
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="2"/>'
         % (AX(0, 0), AY(0, 0, 0), AX(1, 0), AY(1, 0, 0)))
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="2"/>'
         % (AX(0, 0), AY(0, 0, 0), AX(0, 1), AY(0, 1, 0)))
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="2"/>'
         % (AX(0, 0), AY(0, 0, 0), AX(0, 0), AY(0, 0, 1)))
o.append('<text x="%.1f" y="%.1f" font-size="12.5" fill="#333">octave 1 &#8594; 128</text>' % (AX(1, 0) - 90, 574))
o.append('<text x="%.1f" y="%.1f" font-size="12.5" fill="#333">dimension n &#8594;</text>' % (AX(0, 1) + 4, AY(0, 1, 0) - 6))
o.append('<text x="%.1f" y="%.1f" font-size="12.5" fill="#333">slope &#8593;</text>' % (AX(0, 0) - 8, AY(0, 0, 1) - 10))
for s in (0.0, 1.0, 2.0):
    y = AY(0, 0, s)
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="1.3"/>' % (AX(0, 0) - 6, y, AX(0, 0), y))
    o.append('<text x="%.1f" y="%.1f" font-size="11" fill="#555" text-anchor="end">%d</text>' % (AX(0, 0) - 10, y + 4, int(s)))
o.append('<text x="100" y="606" font-size="11.5" fill="#777">nothing settles; only the average does</text>')

# ---------------- RIGHT: running mean ----------------
o.append('<text x="%.1f" y="126" font-size="15" font-weight="bold" fill="#111">the running mean, and its band</text>' % BX0)
o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="#f7f7f7" stroke="#222" stroke-width="1.5"/>'
         % (BX0, BYT, BX1 - BX0, BYB - BYT))
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#c0392b" stroke-width="2.4"/>' % (BX0, by(1.0), BX1, by(1.0)))
o.append('<text x="%.1f" y="%.1f" font-size="12" font-weight="bold" fill="#c0392b">critical slope 1</text>' % (BX1 - 118, by(1.0) - 7))

for n, col in ((4.0, (33, 102, 172)), (4.7, (90, 90, 90)), (5.4, (178, 24, 43))):
    v = (n - NMIN) / (NMAX - NMIN)
    colr = "#%02x%02x%02x" % col
    run, up, lo = [], [], []
    for i in range(1, K + 1):
        s = sum(mean_slope(n) + jit(j / (K - 1), v) for j in range(i)) / i
        band = DEPTH * math.sqrt(CORR / i)
        x = BX0 + (i - 1) * (BX1 - BX0) / (K - 1) * (KOCT / KOCT)
        run.append("%.1f,%.1f" % (x, by(s)))
        up.append("%.1f,%.1f" % (x, by(s + band)))
        lo.append("%.1f,%.1f" % (x, by(s - band)))
    o.append('<polygon fill="%s" opacity="0.16" points="%s %s"/>'
             % (colr, " ".join(up), " ".join(reversed(lo))))
    o.append('<polyline fill="none" stroke="%s" stroke-width="2.2" points="%s"/>' % (colr, " ".join(run)))
    o.append('<text x="%.1f" y="%.1f" font-size="12" font-weight="bold" fill="%s">n = %.1f</text>'
             % (BX1 + 4, by(mean_slope(n)) + 4, colr, n))

for k in (1, 16, 32, 64, 96, 128):
    x = BX0 + (k - 1) * (BX1 - BX0) / (KOCT - 1)
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="1.3"/>' % (x, BYB, x, BYB + 6))
    o.append('<text x="%.1f" y="%.1f" font-size="11.5" fill="#555" text-anchor="middle">%d</text>' % (x, BYB + 20, k))
for s in (0.6, 0.8, 1.0, 1.2, 1.4):
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="1.3"/>' % (BX0 - 6, by(s), BX0, by(s)))
    o.append('<text x="%.1f" y="%.1f" font-size="11.5" fill="#555" text-anchor="end">%.1f</text>' % (BX0 - 10, by(s) + 4, s))
o.append('<text x="%.1f" y="%.1f" font-size="13" text-anchor="middle" fill="#333">octaves averaged over</text>' % ((BX0 + BX1) / 2, BYB + 44))
o.append('<text x="%.1f" y="%.1f" font-size="13" text-anchor="middle" fill="#333" transform="rotate(-90 %.1f %.1f)">running mean of the exponent</text>'
         % (BX0 - 46, (BYB + BYT) / 2, BX0 - 46, (BYB + BYT) / 2))
o.append('<text x="%.1f" y="606" font-size="11.5" fill="#777">band = &#177;1 s.d. of the running mean, shrinking like 1/sqrt(octaves)</text>' % BX0)

o.append('<text x="60" y="632" font-size="11.5" fill="#777">The content of the wide view: the instantaneous jitter never settles, but its RUNNING MEAN does.</text>')
o.append('<text x="60" y="650" font-size="11.5" fill="#777">So the verdict at high octaves depends only on the mean &#8212; exactly what Cascade/IntermittencyThreshold.lean formalises.</text>')
o.append('<text x="60" y="668" font-size="11.5" fill="#777">Honest limits: 128 octaves is an extrapolation of the formula, not of a flow &#8212; a real inertial range is about ten octaves, beyond which viscosity cuts the cascade off.</text>')
o.append('<text x="60" y="686" font-size="11.5" fill="#777">The roughness is synthetic; the real jitter statistics are not known to me. And in our own shell model there is no jitter at all &#8212; its per-shell bar is an exact power law.</text>')

o.append('</svg>')
sys.stdout.write("\n".join(o) + "\n")
