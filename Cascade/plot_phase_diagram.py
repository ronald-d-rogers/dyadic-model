#!/usr/bin/env python3
"""Phase diagram of the intermittency-dimension criterion, over real (n, delta).

The nonlinearity exponent of the intermittency dyadic models is

    theta(n, delta) = (2 + n - delta) / 2

and the dissipation exponent is 2 (the honest Laplacian).  The nonlinearity wins at
small scales -- "no obstruction" -- exactly when theta > 2, i.e. when

    n - delta > 2,     equivalently   delta < n - 2.

Colour is the margin  (n - delta - 2)/2, so blue = dissipation wins (the obstruction
holds), red = the nonlinearity wins, white = critical.  Because every quantity depends
only on the COMBINATION n - delta, the picture is diagonal stripes and the boundary is
the straight line delta = n - 2.

This is exact arithmetic, extended from integer dimension to real n.  The physical
spatial dimension is an integer, so the real-n picture is a property of the FORMULA,
not a claim about fractional-dimensional space.

Standard library only.  Regenerate with:

    python3 plot_phase_diagram.py > phase_diagram.svg
    rsvg-convert -w 1600 -o phase_diagram.png phase_diagram.svg
"""
import sys

W, H = 1200, 660
X0, Y0 = 100.0, 460.0          # plot origin: (n, delta) = (0, 0)
PW, PH = 900.0, 340.0          # plot extent in pixels
NMAX, DMAX = 8.0, 3.0          # n in [0,8], delta in [0,3]
COLS, ROWS = 120, 60
CW, CH = PW / COLS, PH / ROWS

def colour(x):
    """diverging blue -> white -> red for x = n - delta - 2, clipped to [-3, 3]."""
    t = max(-1.0, min(1.0, x / 3.0))
    c0, c1 = ((8, 81, 156), (255, 255, 255)) if t < 0 else ((255, 255, 255), (165, 15, 21))
    u = abs(t)
    return "#%02x%02x%02x" % tuple(int(round(c0[i] + u * (c1[i] - c0[i]))) for i in range(3))

def px(n):
    return X0 + n * PW / NMAX

def py(d):
    return Y0 - d * PH / DMAX

o = []
o.append('<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d" viewBox="0 0 %d %d"'
         ' font-family="Helvetica Neue, Helvetica, Arial, sans-serif">' % (W, H, W, H))
o.append('<rect width="%d" height="%d" fill="#ffffff"/>' % (W, H))
o.append('<text x="60" y="44" font-size="22" font-weight="bold" fill="#111">'
         'The criterion over real dimension: a phase diagram in (n, delta)</text>')
o.append('<text x="60" y="72" font-size="14" fill="#444">'
         'Colour is the margin (n - delta - 2)/2 of the nonlinearity exponent (2 + n - delta)/2 against the dissipation exponent 2.</text>')
o.append('<text x="60" y="92" font-size="14" fill="#444">'
         'Everything depends only on the combination n - delta, so the picture is diagonal stripes; the boundary is the straight line delta = n - 2.</text>')

# heat cells
for r in range(ROWS):
    d = DMAX * (r + 0.5) / ROWS
    for c in range(COLS):
        n = NMAX * (c + 0.5) / COLS
        o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="%s"/>'
                 % (X0 + c * CW, Y0 - (r + 1) * CH, CW + 0.6, CH + 0.6, colour(n - d - 2)))

# jitter band (schematic) around the critical line
o.append('<path d="M %.1f %.1f L %.1f %.1f L %.1f %.1f L %.1f %.1f Z" fill="none"'
         ' stroke="#111" stroke-width="0" />' % (0, 0, 0, 0, 0, 0, 0, 0))
for sgn in (-1, 1):
    pass
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#111" stroke-width="2.6"'
         ' stroke-dasharray="9,6" opacity="0.55"/>' % (px(1.7), py(0.0), px(5.3), py(3.0)))
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#111" stroke-width="2.6"'
         ' stroke-dasharray="9,6" opacity="0.55"/>' % (px(2.3), py(0.0), px(5.9), py(3.0)))

# the critical line itself
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#111" stroke-width="2.6"/>'
         % (px(2.0), py(0.0), px(5.0), py(3.0)))

# space-filling (Kolmogorov) line delta = n
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#ffffff" stroke-width="2.4"'
         ' stroke-dasharray="2,5" opacity="0.9"/>' % (px(0.0), py(0.0), px(3.0), py(3.0)))
o.append('<text x="%.1f" y="%.1f" font-size="12.5" font-weight="bold" fill="#ffffff" opacity="0.95">delta = n (Kolmogorov, space-filling)</text>'
         % (px(1.35) + 6, py(1.28)))

# measured delta line
o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#f1c40f" stroke-width="3"/>'
         % (X0, py(2.7), X0 + PW, py(2.7)))
o.append('<text x="%.1f" y="%.1f" font-size="13" font-weight="bold" fill="#b7950b">measured delta &#8776; 2.7</text>'
         % (X0 + 6, py(2.7) - 7))

# crossing marker
o.append('<circle cx="%.1f" cy="%.1f" r="7" fill="none" stroke="#111" stroke-width="2.8"/>'
         % (px(4.7), py(2.7)))
o.append('<text x="%.1f" y="%.1f" font-size="13.5" font-weight="bold" fill="#111">crosses at n = 2 + delta = 4.7</text>'
         % (px(4.7) + 14, py(2.7) + 5))
o.append('<text x="%.1f" y="%.1f" font-size="12" fill="#333">&#8594; integer crossover at dimension 5</text>'
         % (px(4.7) + 14, py(2.7) + 23))

# axis frame
o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="none" stroke="#222" stroke-width="1.6"/>'
         % (X0, py(DMAX), PW, PH))
for n in range(0, 9, 2):
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222"/>' % (px(n), Y0, px(n), Y0 + 6))
    o.append('<text x="%.1f" y="%.1f" font-size="12" fill="#555" text-anchor="middle">%d</text>' % (px(n), Y0 + 22, n))
for d in range(0, 4):
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222"/>' % (X0 - 6, py(d), X0, py(d)))
    o.append('<text x="%.1f" y="%.1f" font-size="12" fill="#555" text-anchor="end">%d</text>' % (X0 - 10, py(d) + 4, d))

# region labels
o.append('<text x="%.1f" y="%.1f" font-size="15" font-weight="bold" fill="#0b3d6b">dissipation wins</text>' % (px(0.3), py(2.55)))
o.append('<text x="%.1f" y="%.1f" font-size="12.5" fill="#0b3d6b">the obstruction holds</text>' % (px(0.3), py(2.35)))
o.append('<text x="%.1f" y="%.1f" font-size="12.5" fill="#0b3d6b">(heuristic regularity)</text>' % (px(0.3), py(2.16)))
o.append('<text x="%.1f" y="%.1f" font-size="15" font-weight="bold" fill="#ffffff" text-anchor="end">nonlinearity wins</text>' % (px(7.85), py(0.30)))
o.append('<text x="%.1f" y="%.1f" font-size="12.5" fill="#ffffff" text-anchor="end">no obstruction</text>' % (px(7.85), py(0.10)))

o.append('<text x="%.1f" y="%.1f" font-size="14" text-anchor="middle" fill="#333">spatial dimension n (real)</text>' % (X0 + PW / 2, Y0 + 48))
o.append('<text x="46" y="%.1f" font-size="14" text-anchor="middle" fill="#333" transform="rotate(-90 46 %.1f)">intermittency dimension delta</text>'
         % (py(1.5), py(1.5)))

# colour bar
bx, by, bw, bh = X0, 540.0, 300.0, 18.0
for i in range(100):
    o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="%s"/>'
             % (bx + i * bw / 100, by, bw / 100 + 0.6, bh, colour(-3 + 6 * i / 99)))
o.append('<rect x="%.1f" y="%.1f" width="%.1f" height="%.1f" fill="none" stroke="#222"/>' % (bx, by, bw, bh))
o.append('<text x="%.1f" y="%.1f" font-size="11.5" fill="#555" text-anchor="end">-3 &#8594; safe</text>' % (bx, by + 32))
o.append('<text x="%.1f" y="%.1f" font-size="11.5" fill="#555" text-anchor="middle">0 &#8594; critical</text>' % (bx + bw / 2, by + 32))
o.append('<text x="%.1f" y="%.1f" font-size="11.5" fill="#555">+3 &#8594; dangerous</text>' % (bx + bw + 8, by + 32))

o.append('<text x="%.1f" y="%.1f" font-size="12" fill="#666">the dashed black band is where a jitter of the measured size would blur the boundary &#8212; schematic, since the real jitter statistics are not known</text>'
         % (X0, 596))
o.append('<text x="%.1f" y="%.1f" font-size="11.5" fill="#777">The heat map is exact arithmetic extended from integer n to real n; the physical spatial dimension is an integer, so this is a property of the formula, not a claim about fractional-dimensional space.</text>' % (60, 622))
o.append('<text x="%.1f" y="%.1f" font-size="11.5" fill="#777">The empirical input is the measured intermittency delta &#8776; 2.7 (Dai, arXiv:2006.15094); the crossing with the boundary is the integer crossover at dimension 5 formalised in Cascade/IntermittencyThreshold.lean.</text>' % (60, 641))

o.append('</svg>')
sys.stdout.write("\n".join(o) + "\n")
