#!/usr/bin/env python3
"""The jitters of an explosion.

The inviscid shell model  u_k' = 2^k (u_{k-1}^2 - 2 u_k u_{k+1})  has the exact
self-similar solution

    u_k(t) = (1/3) * 2^{-k} * (T - t)^{-1},

since  u_k' = (1/3) 2^{-k} (T-t)^{-2}  and  2^k (u_{k-1}^2 - 2 u_k u_{k+1})
= 3 (1/9) 2^{-k} (T-t)^{-2} = (1/3) 2^{-k} (T-t)^{-2},  matching exactly.
Its vorticity is  a_k = 2^k u_k = (1/3)(T-t)^{-1},  FLAT in k: the local exponent is
0 at every shell, so the jitter is exactly ZERO, while the level diverges as t -> T.

Left panel: that exact explosion, in 3-D -- shell k against time t, height a_k. A flat
sheet rising to infinity at T.

Right panel: the same explosion with a jitter profile riding on it, a_k = (1/3)(T-t)^{-1}
* 2^{phi(k)}.  The profile phi is frozen in time, so the shape is fixed and only the
level diverges -- the jitter rides along, geometrically unchanged.

The point of the pair: during an explosion the jitter does not grow, shrink, or decide
anything. The explosion is the LEVEL. The jitter cannot cause it and cannot prevent it.

HONESTY.  The left panel is the exact solution. The right panel's roughness is
synthetic (the real jitter statistics are not known to the author). This is the
untruncated inviscid model: our truncated model provably cannot blow up at all, and
the flat profile means the enstrophy sum diverges at every time on the infinite
lattice, so this is a self-similar solution rather than a blow-up from finite enstrophy.

Standard library only.  Regenerate with:

    python3 plot_explosion.py > explosion.svg
    rsvg-convert -w 1600 -o explosion.png explosion.svg
"""
import math
import random
import sys

W, H = 1200, 760
KMAX = 24
TCLIP = 0.90                    # time shown, as a fraction of T
PANELS = (90.0, 650.0)
PW, PH = 250.0, 150.0

random.seed(3)
_ph = []
e = 0.0
for k in range(KMAX + 1):
    e = 0.75 * e + random.gauss(0.0, 1.0)
    _ph.append(e)
_m = sum(_ph) / len(_ph)
_sd = (sum((x - _m) ** 2 for x in _ph) / len(_ph)) ** 0.5
PHI = [0.25 * (x - _m) / _sd for x in _ph]

def height(u, v):
    """normalised vorticity level: 1 at t = 0, 10 at the clip."""
    t = v * TCLIP
    return 1.0 / (1.0 - t)

def AX(u, v, x0):
    return x0 + PW * u + PH * v

def AY(u, v, z):
    return 514.0 + 35.0 * u - 80.0 * v - 300.0 * (z - 1.0) / 9.0

def shade(z):
    t = max(0.0, min(1.0, (z - 1.0) / 9.0))
    c0, c1 = (254, 229, 217), (103, 0, 13)
    return "#%02x%02x%02x" % tuple(int(round(c0[k] + t * (c1[k] - c0[k]))) for k in range(3))

o = []
o.append('<svg xmlns="http://www.w3.org/2000/svg" width="%d" height="%d" viewBox="0 0 %d %d"'
         ' font-family="Helvetica Neue, Helvetica, Arial, sans-serif">' % (W, H, W, H))
o.append('<rect width="%d" height="%d" fill="#ffffff"/>' % (W, H))
o.append('<text x="60" y="44" font-size="22" font-weight="bold" fill="#111">'
         'The jitters of an explosion</text>')
o.append('<text x="60" y="72" font-size="13" fill="#444">'
         'The inviscid shell model has the exact self-similar solution u_k(t) = (1/3) 2^(-k) (T - t)^(-1).</text>')
o.append('<text x="60" y="90" font-size="13" fill="#444">'
         'Its vorticity a_k = 2^k u_k = (1/3)(T - t)^(-1) is FLAT in k, so the local exponent is 0 at every shell and the jitter is exactly zero.</text>')
o.append('<text x="60" y="108" font-size="13" fill="#444">'
         'Both panels show shell k against time t, height = vorticity level. Left: the exact solution. Right: the same explosion with a frozen jitter profile riding on it.</text>')

def surface(x0, phi_on, label):
    quads = []
    NU, NV = 25, 16
    for j in range(NV - 1):
        for i in range(NU - 1):
            pts = []
            for (iu, iv) in ((i, j), (i + 1, j), (i + 1, j + 1), (i, j + 1)):
                u, v = iu / (NU - 1), iv / (NV - 1)
                z = height(u, v) * (2.0 ** PHI[iu] if phi_on else 1.0)
                z = min(z, 11.0)
                pts.append("%.1f,%.1f" % (AX(u, v, x0), AY(u, v, z)))
            zc = height((i + 0.5) / (NU - 1), (j + 0.5) / (NV - 1)) * (2.0 ** PHI[i] if phi_on else 1.0)
            quads.append((j - i, '<polygon points="%s" fill="%s" stroke="%s" stroke-width="0.4"/>'
                          % (" ".join(pts), shade(zc), shade(zc))))
    quads.sort(key=lambda t: -t[0])
    o.extend(q for _, q in quads)
    # frame and the wall at t = T
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="2"/>'
             % (AX(0, 0, x0), AY(0, 0, 1.0), AX(1, 0, x0), AY(1, 0, 1.0)))
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="2"/>'
             % (AX(0, 0, x0), AY(0, 0, 1.0), AX(0, 1, x0), AY(0, 1, 1.0)))
    o.append('<line x1="%.1f" y1="%.1f" x2="%.1f" y2="%.1f" stroke="#222" stroke-width="2"/>'
             % (AX(0, 0, x0), AY(0, 0, 1.0), AX(0, 0, x0), AY(0, 0, 10.0)))
    o.append('<text x="%.1f" y="%.1f" font-size="14" font-weight="bold" fill="#111">%s</text>'
             % (x0, 140, label))

surface(PANELS[0], False, 'the exact solution: zero jitter')
surface(PANELS[1], True, 'with a frozen jitter profile (synthetic)')

# shared labels
for x0, cap in ((PANELS[0], 'shell k &#8594;'), (PANELS[1], 'shell k &#8594;')):
    o.append('<text x="%.1f" y="%.1f" font-size="12.5" fill="#333">%s</text>' % (x0 + PW - 10, 578, cap))
    o.append('<text x="%.1f" y="%.1f" font-size="12.5" fill="#333">time t &#8594; T</text>' % (x0 + PW + 6, AY(0, 1, 1.0) + 4))
    o.append('<text x="%.1f" y="%.1f" font-size="12.5" fill="#333">level &#8593;</text>' % (x0 - 6, AY(0, 0, 10.0) - 8))
o.append('<text x="%.1f" y="%.1f" font-size="12" fill="#666">height = 1/(1 - t), clipped at t = 0.9 T; the level diverges at T</text>' % (PANELS[0] - 20, 614))

o.append('<text x="60" y="652" font-size="11.5" fill="#777">The profile is a perfect power law at every instant, so the jitter is exactly zero: what explodes is the LEVEL, not the shape. The right panel\'s frozen jitter keeps the same shape while the level diverges.</text>')
o.append('<text x="60" y="670" font-size="11.5" fill="#777">The lesson of the pair: during an explosion the jitter does not grow, shrink, or decide anything. It cannot cause the blow-up and cannot prevent it &#8212; only the level moves.</text>')
o.append('<text x="60" y="688" font-size="11.5" fill="#777">Honest limits: left panel exact, right panel\'s roughness synthetic. This is the untruncated inviscid model &#8212; our truncated model provably cannot blow up at all, and the flat profile makes the enstrophy diverge at every time.</text>')

o.append('</svg>')
sys.stdout.write("\n".join(o) + "\n")
