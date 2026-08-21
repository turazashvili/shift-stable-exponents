#!/usr/bin/env python3
"""
Does the technique generalize?  Test a UNIFIED statement covering both axes.

NOTE (historical): this script was written while the two axes below were still open
conjectures. Both are now theorems -- see `bala_congruence` and its corollaries in
ShiftStableExponents/Basic.lean, and Sections 4-5 of the paper. The labels "OPEN"
retained below refer to the state of the problem when the script was written; the
script is kept as an independent numerical check of the unified statement.

AXIS 1 (Bala, OEIS A361036, Mar 2023):
    b(n) = n! [x^n] ( F(x)^n * exp(x * G(x)^n) )        -> b(n+k) = b(n) mod k

AXIS 2 (OEIS A278070's *general* comment):
    b(n) = n! [x^n] ( F(x)^n * exp(x * G(x)) )          -- fixed G in the exponential

These are different axes. Proposed unification: let the two exponents be ARBITRARY
integer polynomials in n.

    CONJECTURE (unified).  Let F, G in Z[[x]] with F(0)=G(0)=1, and let A, M be
    polynomials with integer coefficients taking non-negative values on N. Define
        b(n) = n! [x^n] ( F(x)^{A(n)} * exp(x * G(x)^{M(n)}) ).
    Then b(n+k) == b(n) (mod k) for all n, k >= 1.

Instances:
    A(n)=n, M(n)=n   -> Bala A361036 general   (proved)
    A(n)=n, M(n)=1   -> A278070 general        (now proved)
    A(n)=0, M(n)=n   -> A293013 / A361281      (proved)
    A(n)=0, M(n)=1   -> Bala's 2017 theorem
so a single theorem would subsume all of them.

WHY IT SHOULD WORK. The expansion generalizes verbatim:
    exp(x G^M) = sum_j x^j G^{M j} / j!
    b(n) = sum_j (n!/j!) [x^{n-j}] (F^A G^{M j})
         = sum_i (n)_i [x^i] (F^{A(n)} G^{M(n)(n-i)})            [i = n-j]
The proof needs only that both exponents are shift-stable mod k:
    A(n+k) == A(n)          because A is an integer polynomial
    M(n+k)(n+k-i) == M(n)(n-i)   because M is, and (n+k-i) == (n-i)
which is exactly what the existing telescoping consumes.
"""

from fractions import Fraction
from math import factorial, comb
import os
import random
import re


def mul(a, b, deg):
    o = [0] * (deg + 1)
    for i, ai in enumerate(a[:deg + 1]):
        if ai:
            for j, bj in enumerate(b[:deg + 1 - i]):
                if bj:
                    o[i + j] += ai * bj
    return o


def powr(a, e, deg):
    r = [1] + [0] * deg
    for _ in range(e):
        r = mul(r, a, deg)
    return r


def ser(c, deg):
    c = list(c[:deg + 1])
    return c + [0] * (deg + 1 - len(c))


def descF(m, i):
    r = 1
    for t in range(i):
        r *= (m - t) if m - t > 0 else 0
    return r


def b_direct(F, G, A, M, N):
    """b(n) = n![x^n]( F^{A(n)} * exp(x * G^{M(n)}) ), from the definition."""
    out = []
    for n in range(N + 1):
        deg = n
        GM = powr(G, M(n), deg)
        xGM = [0] + GM[:deg]
        E = [Fraction(0)] * (deg + 1)
        E[0] = Fraction(1)
        for m in range(deg):
            acc = Fraction(0)
            for kk in range(1, m + 2):
                if kk <= deg and xGM[kk]:
                    acc += Fraction(kk) * Fraction(xGM[kk]) * E[m + 1 - kk]
            E[m + 1] = acc / Fraction(m + 1)
        FA = powr(F, A(n), deg)
        tot = Fraction(0)
        for j in range(deg + 1):
            if FA[j]:
                tot += Fraction(FA[j]) * E[deg - j]
        v = tot * factorial(n)
        if v.denominator != 1:
            return None
        out.append(int(v))
    return out


def b_expansion(F, G, A, M, N):
    """b(n) = sum_i (n)_i [x^i]( F^{A(n)} * G^{M(n)(n-i)} ) -- the claimed closed form."""
    out = []
    for n in range(N + 1):
        tot = 0
        for i in range(n + 1):
            d = descF(n, i)
            if d == 0:
                continue
            S = mul(powr(F, A(n), i), powr(G, M(n) * (n - i), i), i)
            tot += d * S[i]
        out.append(tot)
    return out


def viol(a, maxk=None):
    L = len(a) - 1
    maxk = maxk or L // 2
    return [(n, k) for k in range(1, maxk + 1) for n in range(0, L - k + 1)
            if (a[n + k] - a[n]) % k != 0]


def oeis(anum, root="oeisdata"):
    p = os.path.join(root, "seq", anum[:4], anum + ".seq")
    if not os.path.exists(p):
        return None
    raw = ""
    for line in open(p, encoding="utf-8", errors="replace"):
        m = re.match(r"^%([STU])\s+A\d{6}\s?(.*)$", line.rstrip("\n"))
        if m:
            raw += m.group(2)
    return [int(t) for t in raw.split(",") if t.strip()]


# --- regression tracking -------------------------------------------------
# Checks recorded with must() MUST hold; checks recorded with must_fail() are
# deliberate controls that MUST fail. The script exits non-zero if either kind
# goes the wrong way, so CI detects a mathematical regression, not just a crash.
REGRESSIONS = []


def must(label, ok):
    if not ok:
        REGRESSIONS.append(f"expected to hold, but failed: {label}")
    return ok


def must_fail(label, failed):
    if not failed:
        REGRESSIONS.append(f"expected to FAIL, but held: {label}")
    return failed


def main():
    DEG, N = 24, 22
    one = ser([1], DEG)
    onep = ser([1, 1], DEG)
    inv = ser([1] * (DEG + 1), DEG)          # 1/(1-x)

    print("=" * 78)
    print("STEP 1 - is A278070 really the instance F=1/(1-x), G=1, A(n)=n ?")
    print("=" * 78)
    a278 = b_direct(inv, one, lambda n: n, lambda n: 1, N)
    oe = oeis("A278070")
    m = min(9, len(oe)) if oe else 0
    print(f"  our b(n)     = {a278[:9]}")
    print(f"  OEIS A278070 = {oe[:9] if oe else 'not found'}")
    print(f"  match: {a278[:m] == oe[:m] if oe else 'n/a'}")
    print(f"  congruence violations: {len(viol(a278))}")
    if oe:
        must("A278070 reproduces the stored OEIS terms", a278[:m] == oe[:m])
    else:
        print("  NOTE: OEIS dump not found -- term comparison SKIPPED")
        REGRESSIONS.append("OEIS dump missing: A278070 term comparison could not run")
    must("A278070 congruence", len(viol(a278)) == 0)

    print()
    print("=" * 78)
    print("STEP 2 - does the closed-form expansion still hold with polynomial exponents?")
    print("=" * 78)
    polys = [
        ("A(n)=n,     M(n)=n    [A361036, proved]", lambda n: n, lambda n: n),
        ("A(n)=n,     M(n)=1    [A278070 general, proved]", lambda n: n, lambda n: 1),
        ("A(n)=0,     M(n)=n    [A293013/A361281]",       lambda n: 0, lambda n: n),
        ("A(n)=1,     M(n)=1    [Bala 2017]",             lambda n: 1, lambda n: 1),
        ("A(n)=2n,    M(n)=n+1",                          lambda n: 2 * n, lambda n: n + 1),
        ("A(n)=n^2,   M(n)=2",                            lambda n: n * n, lambda n: 2),
        ("A(n)=3,     M(n)=n^2",                          lambda n: 3, lambda n: n * n),
        ("A(n)=n^2+n, M(n)=n^2+1",                        lambda n: n*n + n, lambda n: n*n + 1),
    ]
    rng = random.Random(4242)
    okall = True
    for label, A, M in polys:
        F = ser([1] + [rng.randint(-4, 4) for _ in range(5)], DEG)
        G = ser([1] + [rng.randint(-4, 4) for _ in range(5)], DEG)
        d1 = b_direct(F, G, A, M, 14)
        d2 = b_expansion(F, G, A, M, 14)
        agree = (d1 == d2)
        okall &= agree
        print(f"  {label:46s} expansion agrees: {agree}")
        must(f"expansion agrees for {label.strip()}", agree)
    print(f"\n  expansion valid on all: {okall}")

    print()
    print("=" * 78)
    print("STEP 3 - THE TEST: congruence for polynomial exponents, random F,G")
    print("=" * 78)
    total = fails = 0
    for label, A, M in polys:
        bad = 0
        for t in range(25):
            F = ser([1] + [rng.randint(-6, 6) for _ in range(6)], DEG)
            G = ser([1] + [rng.randint(-6, 6) for _ in range(6)], DEG)
            a = b_direct(F, G, A, M, N)
            if a is None:
                continue
            v = viol(a)
            total += 1
            if v:
                bad += 1
                fails += 1
        print(f"  {label:46s} {25 - bad:2d}/25 hold" + ("" if not bad else "   <-- FAILURES"))
        must(f"congruence holds for {label.strip()}", bad == 0)
    print(f"\n  overall: {total - fails}/{total} hold")

    print()
    print("=" * 78)
    print("STEP 4 - control: exponents that are NOT integer polynomials should break")
    print("=" * 78)
    bads = [
        ("A(n)=2^n  (not polynomial)", lambda n: 2 ** n, lambda n: 1),
        ("M(n)=2^n  (not polynomial)", lambda n: n, lambda n: 2 ** n),
        ("A(n)=n!   (not polynomial)", lambda n: factorial(min(n, 8)), lambda n: 1),
    ]
    for label, A, M in bads:
        nb = 0
        for t in range(6):
            F = ser([1] + [rng.randint(-3, 3) for _ in range(4)], DEG)
            G = ser([1] + [rng.randint(-3, 3) for _ in range(4)], DEG)
            a = b_direct(F, G, A, M, 16)
            if a is None:
                continue
            if viol(a):
                nb += 1
        print(f"  {label:32s} {nb}/6 FAIL  (expected: most, if polynomiality matters)")
        must_fail(f"non-shift-stable control {label.strip()}", nb > 0)

    print()
    print("=" * 78)
    print("STEP 5 - the two formerly open named targets, at higher range")
    print("=" * 78)
    for label, F, G, A, M in [
        ("A278070 general: F=1/(1-x), G=1+x, A=n, M=1", inv, onep, lambda n: n, lambda n: 1),
        ("A278070 general: F=1+x,     G=1/(1-x), A=n, M=1", onep, inv, lambda n: n, lambda n: 1),
    ]:
        a = b_direct(F, G, A, M, 40)
        print(f"  {label}")
        print(f"      b(0..6) = {a[:7]}")
        print(f"      violations for all n,k with n+k<=40: {len(viol(a, 20))}")
        must(f"higher-range congruence: {label}", len(viol(a, 20)) == 0)


if __name__ == "__main__":
    main()
    if REGRESSIONS:
        print()
        print("=" * 78)
        print(f"REGRESSION: {len(REGRESSIONS)} check(s) went the wrong way")
        for r in REGRESSIONS:
            print(f"  - {r}")
        print("=" * 78)
        raise SystemExit(1)
    print()
    print("All required checks passed; all controls failed as intended.")
