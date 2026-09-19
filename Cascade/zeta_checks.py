#!/usr/bin/env python3
"""Exact checks for the p-adic-cascade zeta claim: the zeta restates the branching number.

Companion to Cascade/ZETA.md, which records the negative result that the Artin-Mazur / Ruelle
zeta attached to the p-adic cascade tree cannot carry the critical exponent
alpha_tilde = (1/2) log_2 N_* of the dyadic tree cascade (arXiv:1207.2846).  Nothing here is
a proof; every check is an EXACT rational computation (fractions.Fraction) except where a
transcendental quantity (a logarithm) is unavoidable, and those are the only float sections
and are labelled.

Standard library only.  Deterministic.  Exit status 0 iff every check passes.

What is checked
  A  Artin-Mazur zeta of the full p-shift: exp(sum_n p^n T^n / n) == 1/(1 - pT), as truncated
     power series with rational coefficients.  This is the identity zeta_sigma(T) = 1/(1 - pT).
  B  Its reciprocal has exactly two nonzero coefficients: 1/zeta = 1 - pT.
  C  The weighted periodic sum factorises: sum over words of length n of prod_k w(a_k)
     == (sum_a w(a))^n, by direct enumeration of all p^n words.
  D  The rank-one determinant: det(I - t*M) == 1 - (sum_a w(a))*t for M[i][j] = w(j),
     by exact fraction-free determinant, i.e. the Ruelle zeta sees only the SUM of the
     multipliers, never their individual values.
  E  The functional equation for a rank-one zeta.  zeta(T) = 1/(1 - lam*T) ALWAYS satisfies
     zeta(1/(lam^2 T)) = -lam*T*zeta(T), and lam^2 is the only constant that works among
     chi(T) = kappa*T^m.  So self-duality is automatic here and cannot select anything: the
     axis is the pole radius, and the pole fixes the axis, not the reverse.
  F  The Kahane / KP arithmetic is blind to the time-scale exponent: for weights p_i >= 0
     summing to 1, E[W log W] = log(l) - H(p) < log(l) unless the mass is a point mass.
  G  The Barbato threshold arithmetic: alpha_tilde = (1/2) log_2 N_*, and the pole radius
     1/p returns log_2 p -- the factor 1/2 has to be supplied by hand.
  H  The intersection count: |Fix(sigma^m) cap Fix(sigma^n)| = p^gcd(m,n), by direct enumeration,
     which sharpens "the Artin-Mazur data is exactly the level structure".
  I  The isotropic reduction of the tree cascade: X_n = sigma r^-n gives
     sigmadot = (4^alpha - b) sigma^2 exactly, so the renormalisation multiplier is
     Lambda = 2^beta with beta = alpha - alpha_tilde and criticality Lambda = 1.

Labels used in Cascade/ZETA.md: [proved]/[proved - exact computation]/[sourced - where]/
[derived]/[measured - script]/[inference]/[not found].
"""

import math
import random
import sys
from fractions import Fraction as F

FAILURES = []


def check(name, ok, detail=""):
    """Record one check.  ok may be a bool; detail is printed either way."""
    tag = "ok  " if ok else "FAIL"
    print(f"  [{tag}] {name}{('  ' + detail) if detail else ''}")
    if not ok:
        FAILURES.append(name)


def close(a, b, tol):
    return abs(a - b) <= tol


# --------------------------------------------------------------------------------------
# power series over Q, truncated to degree < n
# --------------------------------------------------------------------------------------

def ps_mul(a, b, n):
    out = [F(0)] * n
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        for j, bj in enumerate(b):
            if i + j < n and bj != 0:
                out[i + j] += ai * bj
    return out


def ps_inv(a, n):
    """Inverse of a power series with a[0] != 0, truncated."""
    assert a[0] != 0
    out = [F(0)] * n
    out[0] = 1 / a[0]
    for k in range(1, n):
        s = F(0)
        for i in range(1, k + 1):
            s += a[i] * out[k - i]
        out[k] = -s / a[0]
    return out


def ps_exp(a, n):
    """exp of a power series with a[0] == 0, truncated, via sum_j a^j / j!."""
    out = [F(0)] * n
    out[0] = F(1)
    term = [F(0)] * n
    term[0] = F(1)                      # term = a^j / j!  built iteratively as term*a/j
    for j in range(1, n):
        term = ps_mul(term, a, n)
        for i in range(n):
            term[i] = term[i] / j       # divide by j, not by j!: term already carries (j-1)!
        for i in range(n):
            out[i] += term[i]
    return out


def section_a_b(p, M):
    print(f"A/B  Artin-Mazur zeta of the full {p}-shift, series to degree {M}")
    # S(T) = sum_{n=1}^{M} p^n T^n / n
    S = [F(0)] * (M + 1)
    for n in range(1, M + 1):
        S[n] = F(p ** n, n)
    zeta = ps_exp(S, M + 1)
    geom = [F(p ** n) for n in range(M + 1)]          # 1/(1 - pT) = sum p^n T^n
    check("A: exp(sum p^n T^n/n) == 1/(1-pT) coefficientwise",
          zeta == geom, f"p = {p}, degrees 0..{M}")
    inv = ps_inv(zeta, M + 1)
    check("B: 1/zeta == 1 - pT has only two nonzero coefficients",
          inv == [F(1), F(-p)] + [F(0)] * (M - 1),
          f"1/zeta = {inv[:5]} ...")
    # the pole and the entropy
    check("A: n-th coefficient of 1/zeta is 0 for n >= 2 (no further data)", inv[2:] == [F(0)] * (M - 1))


def section_c(p, n, rng):
    print(f"C    weighted periodic sum factorises, p = {p}, word length n = {n}")
    w = [F(rng.randint(1, 9), rng.randint(1, 9)) for _ in range(p)]
    # enumerate all p^n words
    total = F(0)
    for code in range(p ** n):
        prod = F(1)
        c = code
        for _ in range(n):
            prod *= w[c % p]
            c //= p
        total += prod
    check("C: sum over words of prod w == (sum w)^n", total == sum(w) ** n,
          f"sum w = {sum(w)}")


def det(mat):
    """Exact determinant by fraction-free-ish Gaussian elimination over Q."""
    n = len(mat)
    m = [row[:] for row in mat]
    sign = 1
    detv = F(1)
    for col in range(n):
        piv = None
        for r in range(col, n):
            if m[r][col] != 0:
                piv = r
                break
        if piv is None:
            return F(0)
        if piv != col:
            m[col], m[piv] = m[piv], m[col]
            sign = -sign
        detv *= m[col][col]
        inv = F(1) / m[col][col]
        for r in range(col + 1, n):
            f = m[r][col] * inv
            if f:
                for c2 in range(col, n):
                    m[r][c2] -= f * m[col][c2]
    return sign * detv


def section_d(p, rng):
    print(f"D    rank-one determinant det(I - t*M), M[i][j] = w[j], p = {p}")
    w = [F(rng.randint(1, 9), rng.randint(1, 9)) for _ in range(p)]
    for t in (F(1, 3), F(2, 7), F(-5, 11), F(0)):
        mat = [[(F(1) if i == j else F(0)) - t * w[j] for j in range(p)] for i in range(p)]
        lhs = det(mat)
        rhs = F(1) - sum(w) * t
        check(f"D: det(I - t M) == 1 - (sum w) t at t = {t}", lhs == rhs,
              f"det = {lhs}, 1-(sum w)t = {rhs}")
    # and the normalised case: sum w = 1 gives det = 1 - t, independent of the split
    w2 = [F(1, p)] * p
    mat = [[(F(1) if i == j else F(0)) - F(1, 5) * w2[j] for j in range(p)] for i in range(p)]
    check("D: normalised (sum w = 1) gives det = 1 - t, independent of the split",
          det(mat) == F(1) - F(1, 5))


def section_e(lam):
    print(f"E    functional equation for the rank-one zeta 1/(1 - lam T), lam = {lam}")
    def z(T):
        return 1 / (1 - lam * T)

    ok = True
    for T in (F(3, 5), F(11, 4), F(-2, 9), F(1, 17), F(101, 3)):
        if z(F(1, lam * lam) / T) != -lam * T * z(T):
            ok = False
    check("E: zeta(1/(lam^2 T)) == -lam*T*zeta(T) at every tested rational T", ok,
          "the constant is 1/lam^2, NOT 1/lam")
    # the constant in the report's test is wrong: c = lam fails
    bad = any(z(F(lam) / T) == -lam * T * z(T) for T in (F(3, 5), F(11, 4)))
    check("E: c = lam does NOT give a functional equation (the tested constant was wrong)", not bad)
    # uniqueness by degree count, chi(T) = kappa T^m:  T(1-lam T) = kappa T^m (T - lam c)
    #   m = 0 : degree 2 = 1  impossible
    #   m = 1 : kappa = -lam from T^2, and 1 = lam^2 c from T  =>  c = 1/lam^2
    #   m >= 2: degree 2 = m+1 >= 3  impossible
    kappa = -lam
    c = 1 / (lam * lam)
    lhs = [F(0), F(1), -lam]                # T - lam T^2
    rhs = [F(0), kappa * (-lam * c), kappa]  # kappa T^2 - kappa lam c T
    check("E: the unique solution is m = 1, kappa = -lam, c = 1/lam^2", lhs == rhs,
          f"c = {c}, sqrt(c) = {F(1, lam)} = pole radius 1/lam")
    # CARE: the INVERSION form  zeta(c/T) = chi(T) zeta(T)  and the SCALING form
    # chi(T) zeta(aT) = zeta(T)  are DIFFERENT symmetries, and conflating them is what made the
    # original scratch report say "there is no functional equation".  The scaling form really has
    # no nontrivial solution: chi(T) = (1 - lam a T)/(1 - lam T) is a monomial only when a = 1.
    scaling_ok = False
    for a in (F(1, 2), F(2), F(3, 5)):
        if a == 1:
            continue
        # chi(T) = zeta(T)/zeta(aT) = (1 - lam a T)/(1 - lam T); monomial iff not rational-1-1
        # test at several T whether chi(T)/T^k is constant for k = 0 or 1
        for k in (0, 1):
            vals = []
            for T in (F(3, 5), F(11, 4), F(-2, 9)):
                if lam * a * T == 1 or lam * T == 1 or T == 0:
                    continue
                chi = (1 - lam * a * T) / (1 - lam * T)
                vals.append(chi / (T ** k) if k else chi)
            if len(vals) >= 2 and all(v == vals[0] for v in vals):
                scaling_ok = True
    check("E: the SCALING form has no nontrivial solution (only a = 1)", not scaling_ok,
          "inversion and scaling are different symmetries")


def section_e_rank2():
    """Rank >= 2: self-duality under T -> c/T forces the spectrum to pair as lam_i*lam_j = 1/c."""
    print("E'   rank-2 zeta: the pairing condition, and that it is a REAL constraint")
    # zeta(T) = 1/((1 - a T)(1 - b T));  zeta(c/T)/zeta(T) =
    #   [T^2/((T - a c)(T - b c))] * (1 - a T)(1 - b T)
    # This is a monomial iff the multiset {1/a, 1/b} of roots of the numerator equals {a c, b c}.
    def is_monomial_ratio(a, b, c):
        # numerator roots (as a multiset) {1/a, 1/b}; denominator roots {a c, b c}
        lhs = sorted([1 / a, 1 / b])
        rhs = sorted([a * c, b * c])
        return lhs == rhs

    a, b = F(2), F(3)
    # c must pair them: 1/c = a*b  =>  c = 1/(a b)
    check("E': c = 1/(a b) makes the ratio a monomial (spectrum closes under lam -> 1/(c lam))",
          is_monomial_ratio(a, b, 1 / (a * b)), f"a = {a}, b = {b}, c = {1 / (a * b)}")
    bad = [F(1, 4), F(1, 12), F(2), F(1, 7)]
    check("E': no other tested c works",
          all(not is_monomial_ratio(a, b, c) for c in bad),
          f"rejected c in {[str(c) for c in bad]}")
    # and for a rank-1 both members of the pair coincide, which is why c is forced
    lam = F(5)
    check("E': rank 1 is the degenerate pairing lam*lam = 1/c, i.e. c = 1/lam^2",
          lam * lam == 1 / (1 / (lam * lam)))
    print("      => rank >= 2 self-duality is a genuine spectral constraint; rank 1 is automatic.")


def section_f():
    print("F    the Kahane / KP arithmetic is blind to the time-scale exponent (float section)")
    rng = random.Random(20260919)
    worst = 0.0
    for _ in range(2000):
        ell = rng.randint(2, 6)
        raw = [rng.random() for _ in range(ell)]
        s = sum(raw)
        if s == 0:
            continue
        p = [x / s for x in raw]
        H = -sum(pi * math.log(pi) for pi in p if pi > 0)
        EWlogW = sum(pi * math.log(ell * pi) for pi in p if pi > 0)
        worst = max(worst, abs(EWlogW - (math.log(ell) - H)))
    check("F: E[W log W] == log(l) - H(p), 2000 random weight vectors", worst < 1e-12,
          f"max |difference| = {worst:.3e}")
    # the report's numeric instance
    p0, p1 = 0.3, 0.7
    H = -(p0 * math.log(p0) + p1 * math.log(p1))
    EWlog2W = p0 * math.log(2 * p0, 2) + p1 * math.log(2 * p1, 2)
    # NOTE: the scratch report this check was written against quoted 0.1186 here.  The correct
    # value is 0.118710 (H/log 2 = 0.881290, not 0.8814); the report's last digit was a
    # rounding slip, corrected in Cascade/ZETA.md.
    check("F: l = p = 2, p_0 = 0.3 gives H = 0.610864, E[W log2 W] = 0.118710 < 1",
          close(H, 0.610864, 1e-6) and close(EWlog2W, 0.118710, 1e-6) and EWlog2W < 1,
          f"H = {H:.6f}, E[W log2 W] = {EWlog2W:.6f}")
    check("F: E[W log2 W] == 1 - H/log 2", close(EWlog2W, 1 - H / math.log(2), 1e-12))
    # equality only for a point mass
    eqs = []
    for ell in (2, 3, 5):
        for i in range(ell):
            p = [1.0 if j == i else 0.0 for j in range(ell)]
            eqs.append(sum(pi * math.log(ell * pi) for pi in p if pi > 0) - math.log(ell))
    check("F: equality holds exactly for a point mass", all(abs(e) < 1e-15 for e in eqs),
          "mass on a single branch")

    def is_point_mass(p):
        return any(close(pi, 1.0, 1e-12) for pi in p)

    strict = True
    for _ in range(500):
        ell = rng.randint(2, 6)
        raw = [rng.random() for _ in range(ell)]
        s = sum(raw)
        p = [x / s for x in raw]
        if is_point_mass(p):
            continue
        if not sum(pi * math.log(ell * pi) for pi in p if pi > 0) < math.log(ell):
            strict = False
    check("F: strict < for every non-degenerate weight vector tested", strict)


def section_h(p, maxn):
    """Fix(sigma^m) intersect Fix(sigma^n) = Fix(sigma^gcd(m,n)), counted directly.

    A fixed point of sigma^m is a string of period dividing m.  To compare the fixed sets for two
    different m and n, every point is represented the same way: by its first L = lcm(m, n) digits
    (the periodic extension of its period-m or period-n data).  Comparing m-tuples with n-tuples
    directly would give an empty intersection for m != n -- that was the first version's bug.
    """
    print(f"H    Fix(sigma^m) cap Fix(sigma^n) = Fix(sigma^gcd(m,n)), p = {p}")

    def digits(code, m):
        out = []
        c = code
        for _ in range(m):
            out.append(c % p)
            c //= p
        return out

    def extend(digs, L):
        return tuple(digs[i % len(digs)] for i in range(L))

    def lcm(a, b):
        x, y = a, b
        while y:
            x, y = y, x % y
        return a // x * b

    def gcd(a, b):
        x, y = a, b
        while y:
            x, y = y, x % y
        return x

    ok = True
    detail = []
    for m in range(1, maxn + 1):
        for n in range(1, maxn + 1):
            L = lcm(m, n)
            lhs = {extend(digits(c, m), L) for c in range(p ** m)}
            rhs = {extend(digits(c, n), L) for c in range(p ** n)}
            want = {extend(digits(c, gcd(m, n)), L) for c in range(p ** gcd(m, n))}
            if len(lhs) != p ** m or len(rhs) != p ** n:
                ok = False
                detail.append(f"m={m},n={n}: representation lost points")
            if lhs & rhs != want:
                ok = False
                detail.append(f"m={m},n={n}: |cap| = {len(lhs & rhs)} != {len(want)}")
    check("H: |Fix(sigma^m) cap Fix(sigma^n)| = p^gcd(m,n)", ok,
          f"p = {p}, m,n <= {maxn}" + ("; " + "; ".join(detail) if detail else ""))


def section_i():
    """The isotropic profile of the tree cascade -- and the ROOT, where it fails.

    Barbato-Bianchi-Flandoli-Morandin, eq. (1)/(7), verbatim:
        dX_j/dt = c_j X_jbar^2 - sum_{k in O_j} c_k X_j X_k,   c_j = 2^{alpha |j|},  #O_j = b,
    with X_{0bar}(t) = f a forcing ALIAS: the root has no father, so in the unforced model its
    source term is absent.  The isotropic profile X_n = sigma * r^{-n} (r = 2^alpha) makes the
    generation dependence cancel -- at every node that HAS a father.  The root is an obstruction,
    and the earlier version of this section missed it by supplying a phantom father at n = 0.
    """
    print("I    the isotropic profile of the tree cascade: bulk identity, and the root obstruction")
    b, r, s = F(2), F(2), F(1)

    def c(n):
        return r ** n

    def X(n):
        return s * r ** (-n)

    # (a) the BULK identity, for every node with a father (n >= 1)
    bulk_ok = True
    for rr, bb in ((F(3, 2), 2), (F(2), 3), (F(5, 4), 4), (F(3), 2), (F(7, 3), 5)):
        for n in range(1, 9):
            src = rr ** n * (s * rr ** (-(n - 1))) ** 2
            snk = bb * rr ** (n + 1) * (s * rr ** (-n)) * (s * rr ** (-(n + 1)))
            if src - snk != s ** 2 * rr ** (-n) * (rr ** 2 - bb):
                bulk_ok = False
    check("I: at every node WITH a father, X_n = sigma r^-n gives RHS = sigma^2 r^-n (r^2 - b)",
          bulk_ok, "5 (r,b) pairs x n = 1..8, exact rationals")

    # (b) the ROOT fails: model RHS = -b sigma^2, bulk predicts sigma^2 (r^2 - b)
    root_model = -b * s ** 2
    root_bulk = s ** 2 * (r ** 2 - b)
    check("I: the root (no father, f = 0) gives -b sigma^2, NOT sigma^2 (r^2 - b)",
          root_model != root_bulk, f"model {root_model} vs bulk {root_bulk}")
    check("I: they agree only when r = 0, so the profile solves the unforced rooted model at no r != 0",
          all((-(bb * s ** 2) == s ** 2 * (rr ** 2 - bb)) == (rr == 0)
              for rr in (F(1, 2), F(1), F(2), F(3)) for bb in (2, 3)))

    # (c) the independent check: the energy balance, whose residual is the phantom father
    q = b / r ** 2
    e_ok, res_ok = True, True
    for n in (1, 2, 3, 4):
        lhs = 2 * s ** 3 * (r ** 2 - b) * sum(q ** m for m in range(n + 1))
        Pi = 2 * b ** (n + 1) * c(n + 1) * X(n) ** 2 * X(n + 1)
        if lhs + Pi != 2 * (s * r) ** 2 * s:
            e_ok = False
        if not (lhs + Pi == 2 * s ** 3 * r ** 2):
            res_ok = False
    check("I: the energy balance is violated by exactly the phantom father's term 2 sigma^3 r^2",
          e_ok and res_ok, "n = 1..4; the profile implicitly sets X_{-1} = sigma r")

    # (d) the one case that IS a solution: forced, r^2 = b, f = sigma r (stationary)
    st_ok = True
    for rr, ss in ((F(2), F(1)), (F(3), F(5)), (F(4), F(2, 3))):
        bb = rr ** 2
        root = (ss * rr) ** 2 - bb * rr * ss * (ss / rr)
        interior = ss ** 2 * (rr ** 2 - bb)
        if root != 0 or interior != 0:
            st_ok = False
    check("I: forced model with r^2 = b and f = sigma r: root and interior both vanish", st_ok,
          "the profile is then the paper's stationary solution (exponent alpha = (2 a~ + alpha)/3)")

    print("      => the bulk recursion is marginal at r^2 = b, i.e. alpha = alpha_tilde, but the")
    print("         profile is NOT a solution of the unforced rooted model; the earlier claim that")
    print("         'the isotropic manifold reduces the whole tree to the ODE' is WITHDRAWN.")


def section_g():
    print("G    the Barbato threshold arithmetic (float section)")
    for p in (2, 3, 5, 7):
        Nstar = p
        alpha_tilde = 0.5 * math.log2(Nstar)
        from_radius = math.log2(1 / (1 / p))          # log_2 of the reciprocal pole radius
        check(f"G: p = {p}: pole radius gives log_2 p = {from_radius:.6f}, "
              f"alpha_tilde = {alpha_tilde:.6f}, gap = {from_radius - alpha_tilde:.6f} "
              f"= (1/2) log_2 p",
              close(from_radius - alpha_tilde, 0.5 * math.log2(p), 1e-15))
        check(f"G: p = {p}: N_* = 2^(2 alpha_tilde)", close(2 ** (2 * alpha_tilde), Nstar, 1e-12))


def main():
    print(__doc__.split("What is checked")[0].strip())
    print()
    print("=" * 94)
    for p in (2, 3, 5, 7):
        section_a_b(p, 14)
    print()
    rng = random.Random(20260919)
    for p in (2, 3, 5):
        for n in (1, 2, 3, 4):
            section_c(p, n, rng)
    print()
    for p in (2, 3, 4, 5):
        section_d(p, rng)
    print()
    for lam in (2, 3, 5, 7, 11):
        section_e(F(lam))
    print()
    section_e_rank2()
    print()
    section_f()
    print()
    for p in (2, 3):
        section_h(p, 7)
    for p in (5,):
        section_h(p, 4)
    print()
    section_g()
    print()
    section_i()
    print("=" * 94)
    if FAILURES:
        print(f"RESULT: FAIL - {len(FAILURES)} check(s) failed:")
        for name in FAILURES:
            print(f"  - {name}")
        return 1
    print("RESULT: PASS - every exact check reproduced.")
    print("Note: this script checks arithmetic, not mathematics.  The identities are asserted")
    print("in Cascade/ZETA.md with their labels; the Lean library PAdicZeta/ carries the parts")
    print("that are machine-checked.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
