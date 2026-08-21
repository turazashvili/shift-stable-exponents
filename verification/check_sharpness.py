#!/usr/bin/env python3
"""
What the constant terms must satisfy (Section 6.2 of the paper).

Two successive errors were made here, and this script is what settles both.

ERROR 1 (ours, corrected): we claimed "sharpness confirmed -- dropping F(0)=1 or
G(0)=1 breaks the congruence". FALSE. In the diagonal slice W=1, A=M=id the
necessary condition is F(0)*G(0) = 1, which over Z also allows
(F(0), G(0)) = (-1, -1); and there is an infinite surviving family there:
if F = -F~ and G = -G~ with F~, G~ EVEN series (functions of x^2) and
F~(0)=G~(0)=1, then b_{F,G} = b_{F~,G~} identically, so the congruence holds.

Necessity derivation: at n=0, k=p prime, (p)_i == 0 mod p for i >= 1, so
    b(p) == F0^p * G0^{p^2} == F0*G0 (mod p)   [Fermat]
and b(0) = 1, forcing F0*G0 == 1 mod p for every prime p, hence F0*G0 = 1.

ERROR 2 (ours, corrected): we then over-corrected and claimed F(0)*G(0) = 1 could
simply REPLACE F(0)=G(0)=1 -- i.e. that it was sufficient. Also FALSE. The evenness
above is a real constraint, not a convenience: block E1(c) below exhibits
product-one pairs carrying an ODD term for which the congruence fails
(e.g. F = -1+x, G = -1 gives b(4)-b(1) = -17, not divisible by 3).

So: F0 = G0 = 1 is sufficient (the theorem); F0*G0 = 1 is necessary in that slice;
and on the (-1,-1) branch sufficiency holds for the even subfamily only.

This script decides the matter with exact integer arithmetic.
"""

from fractions import Fraction
from math import factorial
import random


def mul(a, b, deg):
    out = [Fraction(0)] * (deg + 1)
    for i, ai in enumerate(a[:deg + 1]):
        if ai:
            for j, bj in enumerate(b[:deg + 1 - i]):
                if bj:
                    out[i + j] += ai * bj
    return out


def powr(a, e, deg):
    r = [Fraction(1)] + [Fraction(0)] * deg
    for _ in range(e):
        r = mul(r, a, deg)
    return r


def as_series(c, deg):
    c = [Fraction(x) for x in c[:deg + 1]]
    return c + [Fraction(0)] * (deg + 1 - len(c))


def b_direct(F, G, N):
    """b(n) = n![x^n] F^n exp(x G^n). Returns None if any term is non-integral."""
    out = []
    for n in range(N + 1):
        deg = n
        Gn = powr(G, n, deg)
        xGn = [Fraction(0)] + Gn[:deg]
        A = [Fraction(0)] * (deg + 1)
        A[0] = Fraction(1)
        for m in range(deg):
            acc = Fraction(0)
            for kk in range(1, m + 2):
                if kk <= deg and xGn[kk]:
                    acc += Fraction(kk) * xGn[kk] * A[m + 1 - kk]
            A[m + 1] = acc / Fraction(m + 1)
        Fn = powr(F, n, deg)
        tot = Fraction(0)
        for j in range(deg + 1):
            if Fn[j]:
                tot += Fn[j] * A[deg - j]
        v = tot * factorial(n)
        if v.denominator != 1:
            return None
        out.append(int(v))
    return out


def violations(a, maxk=None):
    L = len(a) - 1
    maxk = maxk or L // 2
    return [(n, k) for k in range(1, maxk + 1) for n in range(0, L - k + 1)
            if (a[n + k] - a[n]) % k != 0]


# --- regression tracking -------------------------------------------------
# Checks recorded here MUST hold. The script exits non-zero if any fails, so CI
# detects a mathematical regression and not merely a crash.
REGRESSIONS = []


def must(label, ok):
    if not ok:
        REGRESSIONS.append(label)
    return ok


def main():
    DEG, N = 24, 24
    print("=" * 78)
    print("E1(a)  F = G = -1  : referee says b(n) == 1 identically, congruence HOLDS")
    print("=" * 78)
    F = as_series([-1], DEG)
    G = as_series([-1], DEG)
    a = b_direct(F, G, N)
    if a is None:
        print("  non-integral")
    else:
        v = violations(a)
        print(f"  b(0..8) = {a[:9]}")
        print(f"  all ones: {all(x == 1 for x in a)}")
        print(f"  violations: {len(v)}   -> MY SHARPNESS CLAIM IS "
              f"{'FALSE' if not v else 'intact here'}")
        must("E1(a) F=G=-1 satisfies the congruence", len(v) == 0)

    print()
    print("=" * 78)
    print("E1(b)  F = -F~, G = -G~ with F~, G~ EVEN and F~(0)=G~(0)=1")
    print("       referee predicts b_{F,G} == b_{F~,G~} identically")
    print("=" * 78)
    evens = [
        ([1, 0, 3, 0, -7], [1, 0, -5, 0, 0, 0, 1]),
        ([1, 0, -1], [1, 0, 0, 0, 2]),
        ([1, 0, 9, 0, 0, 0, 4], [1, 0, -3, 0, 0, 0, 0, 0, -6]),
    ]
    for Ft, Gt in evens:
        Fp = as_series([-c for c in Ft], DEG)
        Gp = as_series([-c for c in Gt], DEG)
        Ftt = as_series(Ft, DEG)
        Gtt = as_series(Gt, DEG)
        a_neg = b_direct(Fp, Gp, N)
        a_pos = b_direct(Ftt, Gtt, N)
        if a_neg is None or a_pos is None:
            print(f"  F~={Ft[:5]} G~={Gt[:5]}: non-integral")
            continue
        same = a_neg == a_pos
        v = violations(a_neg)
        print(f"  F~={Ft[:5]} G~={Gt[:5]}")
        print(f"      b_-  = {a_neg[:6]}")
        print(f"      b_+  = {a_pos[:6]}")
        print(f"      identical: {same}   violations(b_-): {len(v)}")
        must(f"E1(b) even branch identical {Ft[:3]}", same)
        must(f"E1(b) even branch congruence {Ft[:3]}", len(v) == 0)

    print()
    print("=" * 78)
    print("E1(c)  CONTROL: F0*G0 = 1 but with an ODD term -> should FAIL")
    print("=" * 78)
    for Ft, Gt in [([1, 1, 3], [1, 0, -5]), ([1, 0, -1], [1, 2, 0, 0, 2])]:
        Fp = as_series([-c for c in Ft], DEG)
        Gp = as_series([-c for c in Gt], DEG)
        a = b_direct(Fp, Gp, N)
        if a is None:
            print(f"  F~={Ft} G~={Gt}: non-integral")
            continue
        v = violations(a)
        print(f"  F~={Ft} G~={Gt} -> violations: {len(v)}  (expect > 0)")
        must(f"E1(c) odd-term control DOES fail {Ft}", len(v) > 0)

    print()
    print("=" * 78)
    print("E1(d)  Is F0*G0 = 1 really NECESSARY? scan all small (F0,G0)")
    print("=" * 78)
    rng = random.Random(5)
    for F0 in (-3, -2, -1, 0, 1, 2, 3):
        for G0 in (-3, -2, -1, 0, 1, 2, 3):
            # use even tails so the (-1,-1) branch has a chance
            F = as_series([F0, 0, rng.randint(-2, 2)], DEG)
            G = as_series([G0, 0, rng.randint(-2, 2)], DEG)
            a = b_direct(F, G, 16)
            if a is None:
                stat = "non-integral"
            else:
                v = violations(a)
                stat = "HOLDS" if not v else f"fails ({len(v)})"
            flag = "  <-- F0*G0=1" if F0 * G0 == 1 else ""
            print(f"  F0={F0:2d} G0={G0:2d}  product={F0*G0:3d}  {stat}{flag}")


if __name__ == "__main__":
    main()
    if REGRESSIONS:
        print()
        print("=" * 78)
        print(f"REGRESSION: {len(REGRESSIONS)} required check(s) FAILED")
        for r in REGRESSIONS:
            print(f"  - {r}")
        print("=" * 78)
        raise SystemExit(1)
    print()
    print("All required checks passed.")
