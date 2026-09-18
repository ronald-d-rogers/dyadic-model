#!/usr/bin/env python3
"""The jitter field: how deep the fluctuation is, made visible.

In the phase diagram of plot_phase_diagram.py the boundary is the straight line
delta = n - 2, i.e. margin m := n - delta - 2 = 0.  That is the DETERMINISTIC
boundary.  The real scaling exponent also fluctuates from octave to octave, so at
each scale the local margin is

    m_local(k) = m + xi(k),

with xi a fluctuating field over octaves.  The frontier -- where the local margin
changes sign -- is therefore not straight: it wanders by the depth of xi.  This
figure plots the sign of m_local, so the frontier IS the jitter field and its
vertical wander is the depth.

Only the boundary region is shown.  Note how narrow it is: at the measured
delta ~ 2.7, a depth of 0.25 in margin is +/- 0.5 in n - delta, which is why the
jitter is invisible in the full (n, delta) plane.

The wobble here is synthetic: one realisation, the SAME shape scaled to three
depths so that the effect of depth alone is visible.  The real jitter's statistics
are not known to the author.

Standard library only.  Regenerate with:

    python3 plot_jitter_field.py > jitter_field.svg
    rsvg-convert -w 1600 -o jitter_field.png jitter_field.svg
"""
import random
import sys

W, H = 1200, 620
X0S = [100.0, 480.0, 860.0]      # left edge of each panel
PW = 320.0                       # panel width
PY0, PY1 = 120.0, 480.0          # top (margin +1.5) and bottom (margin -1.5)
KMAX = 48
DEPTHS = [0.10, 0.25, 0.50]      # depth of the jitter, in margin units (1 s.d.)
SAFE, DANGER = "#2166ac", "#b2182b"

def py(m):
    return PY0 + (1.5 - m) * (PY1 - PY0) / 3.0

# one realisation, unit standard deviation, correlated over ~5 octaves
random.seed(5)
e, es = 0.0, []
for _ in range(KMAX):
    e = 0.82 * e + random.gauss(0.0, 1.0)
    es.append(e)
sd = (sum(x * x for x in es) / len(es)) ** 0.5
es = [x / sd for x in es]

o = []
o.append('<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d" viewBox="0 0 %d %d"'
         ' font-family="Helvetica Neue, Helvetica, Arial, sans-serif">' % (W, H, W, H))
o.append('<rect width="%d" height="%d" fill="#ffffff"/>' % (W, H))
o.append('<text x="60" y="44" font-size="22" font-weight="bold" fill="#111">'
         'The jitter field: the boundary wanders, and the wander is the depth</text>')
o.append('<text x="60" y="72" font-size="14" fill="#444">'
         'Colour is the sign of the local margin m + xi(k) against octave, where m = n - delta - 2. The frontier is where it changes sign.</text>')
o.append('<text x="60" y="92" font-size="14" fill="#444">'
         'One realisation, the same shape scaled to three depths, so the effect of depth alone is visible. The straight dashed line is the deterministic boundary m = 0.</text>')

for i, (x0, depth) in enumerate(zip(X0S, DEPTHS)):
    xk = [x0 + k * PW / (KMAX - 1) for k in range(KMAX)]
    fr = [max(-1.45, min(1.45, -depth * es[k])) for k in range(KMAX)]
    line = " L ".join("%.1f %.1f" % (xk[k], py(fr[k])) for k in range(KMAX))
    o.append('<path d="M %.1f %.1f L %s L %.1f %.1f Z" fill="%s"/>'
             % (xk[0], PY1, line, xk[-1], PY1, SAFE))
    o.append('<path d="M %.1f %.1f L %s L %.1f %.1f Z" fill="%s"/>'
             % (xk[0], PY0, line, xk[-1], PY0, DANGER))
    # panel frame and deterministic boundary
    o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="none" stroke="#222" stroke-width="1.5"/>'
             % (x0, PY0, PW, PY1 - PY0))
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#111" stroke-width="2"'
             ' stroke-dasharray="8,5" opacity="0.85"/>' % (x0, py(0.0), x0 + PW, py(0.0)))
    # depth indicator
    xi = x0 + PW * 0.12
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#111" stroke-width="1.6"/>'
             % (xi, py(0.0), xi, py(-depth)))
    o.append('<text x="%.1f" y="%.1f" font-size="12.5" font-weight="bold" fill="#111" text-anchor="middle">'
             'depth %.2f</text>' % (x0 + PW / 2, 108, depth))
    o.append('<text x="%.1f" y="%.1f" font-size="11.5" fill="#555" text-anchor="middle">octave &#8594; smaller scales</text>'
             % (x0 + PW / 2, 502))
    if i == 0:
        o.append('<text x="%.1f" y="%.1f" font-size="13" fill="#555" text-anchor="end">+1.5</text>' % (x0 - 8, py(1.5) + 4))
        o.append('<text x="%.1f" y="%.1f" font-size="13" fill="#555" text-anchor="end">0</text>' % (x0 - 8, py(0.0) + 4))
        o.append('<text x="%.1f" y="%.1f" font-size="13" fill="#555" text-anchor="end">-1.5</text>' % (x0 - 8, py(-1.5) + 4))

# shared labels
o.append('<text x="%.1f" y="%.1f" font-size="14" text-anchor="middle" fill="#333" transform="rotate(-90 46 300)">'
         'margin  m = n - delta - 2</text>' % (46, 300))
o.append('<text x="%.1f" y="%.1f" font-size="13" font-weight="bold" fill="#2166ac">'
         'below the frontier: dissipation wins (safe)</text>' % (100, 552))
o.append('<text x="%.1f" y="%.1f" font-size="13" font-weight="bold" fill="#b2182b">'
         'above the frontier: the nonlinearity wins</text>' % (620, 552))

o.append('<text x="60" y="582" font-size="11.5" fill="#777">'
         'Only the boundary region is shown, and it is narrow: a depth of 0.25 in margin is +/- 0.5 in n - delta, which is why the jitter is invisible in the full (n, delta) plane.</text>')
o.append('<text x="60" y="601" font-size="11.5" fill="#777">'
         'The wobble is synthetic: the real jitter statistics are not known to me. What is exact is the deterministic boundary m = 0 and the fact that the frontier is where the LOCAL margin changes sign.</text>')

o.append('</svg>')
sys.stdout.write("\n".join(o) + "\n")
