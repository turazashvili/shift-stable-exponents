#!/usr/bin/env python3
"""
VERIFY every step of a proposed elementary proof of Bala's 2023 conjecture.

THE CONJECTURE (Peter Bala, OEIS A361036 comment, 13 Mar 2023):
    Let F, G in Z[[x]] with F(0) = G(0) = 1. Define
        b(n) = n! * [x^n] ( F(x)^n * exp( x * G(x)^n ) ).
    Then b(n+k) == b(n) (mod k) for all n, k >= 1.
Open instances: A293013, A361281, A361036.  (NOT covered by Bala's 2017 Theorem 1,
which needs a FIXED G with G(0)=1; here the exponent moves with n.)

PROPOSED PROOF
--------------
Step 1 (expansion). exp(x G^n) = sum_j x^j G^{nj}/j!, so
    b(n) = sum_j (n!/j!) [x^{n-j}] ( F^n G^{nj} )
         = sum_i (n)_i [x^i] ( F(x)^n G(x)^{n(n-i)} ),      i = n-j,
with (n)_i = n!/(n-i)! the falling factorial.

Step 2 (Newton expansion; uses F(0)=G(0)=1). With F = 1+P, G = 1+Q, P(0)=Q(0)=0,
    F^A G^B = sum_{r,s} C(A,r) C(B,s) P^r Q^s,
and [x^i] P^r Q^s = 0 unless r+s <= i. Hence
    [x^i] F^A G^B = sum_{r+s<=i} d(i,r,s) C(A,r) C(B,s),   d(i,r,s) = [x^i]P^r Q^s in Z.
So
    b(n) = sum_i sum_{r+s<=i} d(i,r,s) * (n)_i * C(n, r) * C(n(n-i), s).      (*)

Step 3 (the two shift facts). Put A=n, B=n(n-i), A'=n+k, B'=(n+k)(n+k-i). Then
    A' - A = k                                   so A' == A (mod k)
    B' - B = k(2n + k - i)                       so B' == B (mod k)

Step 4 (three divisibility lemmas).
  (L1) (X)_i is in Z[X], so (n+k)_i == (n)_i (mod k).
  (L2) m! | (n)_i whenever m <= i   [since (n)_i = i!*C(n,i) and m! | i!].
       In particular r! | (n)_i and s! | (n)_i when r+s <= i.
  (L3) If N' == N (mod k) then m!*(C(N',m) - C(N,m)) = (N')_m - (N)_m == 0 (mod k).
       NOTE: the gcd corollary "(k/gcd(k,m!)) | C(N',m)-C(N,m)" is checked below for
       historical reasons but is NOT what was formalized; the Lean development uses the
       division-free form: m! | (n)_i, so (n)_i*(C(N',m)-C(N,m)) = u*((N')_m - (N)_m).

Step 5 (telescoping). With X=(n)_i, Y=C(A,r), Z=C(B,s):
    X'Y'Z' - XYZ = (X'-X)Y'Z' + X(Y'-Y)Z' + XY(Z'-Z)
  * (X'-X) == 0 mod k by (L1); rest integral.
  * X is divisible by r! (L2) and (Y'-Y) by k/gcd(k,r!) (L3); the product is
    divisible by r! * k/gcd(k,r!) = k * (r!/gcd(k,r!)), a multiple of k.
  * likewise for s!.
  So every term of (*) is shift-stable mod k, hence b(n+k) == b(n) (mod k).  QED

Step 6 (edge terms). For i > n we have (n)_i = 0 while (n+k)_i need not vanish;
we must check k | (n+k)_i there. If i >= k this holds (product of >= k consecutive
integers). If i < k then n < i < k, and (n+k)_i is the product over the range
[n+k-i+1, n+k], which contains k because n+k-i+1 <= k <= n+k. So k | (n+k)_i.

This script checks Steps 1, 2, 4, 5, 6 numerically and independently, then checks
the conclusion against the three OEIS target sequences.
"""

from fractions import Fraction
from math import comb, factorial, gcd
import random


# ---------------------------------------------------------------- series utils

def mul(a, b, deg):
    out = [0] * (deg + 1)
    for i, ai in enumerate(a[:deg + 1]):
        if ai:
            for j, bj in enumerate(b[:deg + 1 - i]):
                if bj:
                    out[i + j] += ai * bj
    return out


def powr(a, e, deg):
    r = [1] + [0] * deg
    for _ in range(e):
        r = mul(r, a, deg)
    return r


def falling(n, i):
    """(n)_i = n(n-1)...(n-i+1); 0 if 0 <= n < i."""
    r = 1
    for t in range(i):
        r *= (n - t)
    return r


def b_direct(F, G, N):
    """b(n) = n![x^n] F^n exp(x G^n), computed straight from the definition."""
    out = []
    for n in range(N + 1):
        deg = n
        Gn = powr(G, n, deg)
        xGn = [0] + Gn[:deg]
        # exp(xGn) with rational coefficients
        A = [Fraction(0)] * (deg + 1)
        A[0] = Fraction(1)
        for m in range(deg):
            acc = Fraction(0)
            for kk in range(1, m + 2):
                if kk <= deg and xGn[kk]:
                    acc += Fraction(kk) * Fraction(xGn[kk]) * A[m + 1 - kk]
            A[m + 1] = acc / Fraction(m + 1)
        Fn = powr(F, n, deg)
        tot = Fraction(0)
        for j in range(deg + 1):
            if Fn[j]:
                tot += Fraction(Fn[j]) * A[deg - j]
        v = tot * factorial(n)
        assert v.denominator == 1, (n, v)
        out.append(int(v))
    return out


def b_step1(F, G, N):
    """Step 1: b(n) = sum_i (n)_i [x^i]( F^n G^{n(n-i)} )."""
    out = []
    for n in range(N + 1):
        tot = 0
        for i in range(0, n + 1):
            fi = falling(n, i)
            if fi == 0:
                continue
            deg = i
            P = mul(powr(F, n, deg), powr(G, n * (n - i), deg), deg)
            tot += fi * P[i]
        out.append(tot)
    return out


def b_step2(F, G, N):
    """Step 2 / eq (*): b(n) = sum_i sum_{r+s<=i} d(i,r,s) (n)_i C(n,r) C(n(n-i),s)."""
    out = []
    for n in range(N + 1):
        tot = 0
        for i in range(0, n + 1):
            fi = falling(n, i)
            if fi == 0:
                continue
            P = [F[t] - (1 if t == 0 else 0) for t in range(i + 1)]   # F-1
            Q = [G[t] - (1 if t == 0 else 0) for t in range(i + 1)]   # G-1
            for r in range(i + 1):
                Pr = powr(P, r, i)
                for s in range(i - r + 1):
                    Qs = powr(Q, s, i)
                    d = mul(Pr, Qs, i)[i]
                    if d:
                        tot += d * fi * comb(n, r) * comb(n * (n - i), s)
        out.append(tot)
    return out


def as_series(c, deg):
    c = list(c[:deg + 1])
    return c + [0] * (deg + 1 - len(c))


def rand_F(deg, rng, const1=True):
    return as_series([1 if const1 else rng.randint(-4, 4)]
                     + [rng.randint(-5, 5) for _ in range(6)], deg)


# --- regression tracking -------------------------------------------------
# Checks recorded here MUST hold. main() exits non-zero if any of them fails,
# so CI detects a mathematical regression and not merely a crash.
REGRESSIONS = []


def must(label, ok):
    """Record a check that is required to hold."""
    if not ok:
        REGRESSIONS.append(label)
    return ok


def main():
    rng = random.Random(20260820)
    DEG = 26

    print("=" * 80)
    print("STEP 1 & 2 - the two expansions must agree with the direct definition")
    print("=" * 80)
    ok12 = True
    for t in range(6):
        F = rand_F(DEG, rng)
        G = rand_F(DEG, rng)
        N = 12
        d0 = b_direct(F, G, N)
        d1 = b_step1(F, G, N)
        d2 = b_step2(F, G, N)
        a1, a2 = (d0 == d1), (d0 == d2)
        ok12 &= a1 and a2
        print(f"  trial {t}: F={F[:4]} G={G[:4]}")
        print(f"      direct  {d0[:6]}")
        print(f"      step1 agrees: {a1}   step2 (eq *) agrees: {a2}")
        must(f"closed form agrees (trial {t})", a1 and a2)
    print(f"\n  expansions valid: {ok12}")

    print()
    print("=" * 80)
    print("STEP 4 - the three divisibility lemmas, checked exhaustively on ranges")
    print("=" * 80)
    # (L1) (X)_i in Z[X]  =>  (n+k)_i == (n)_i mod k
    bad = 0
    for k in range(1, 30):
        for n in range(0, 40):
            for i in range(0, 14):
                if (falling(n + k, i) - falling(n, i)) % k != 0:
                    bad += 1
    print(f"  (L1) (n+k)_i == (n)_i mod k                       violations: {bad}")
    must("L1 (n+k)_i == (n)_i mod k", bad == 0)

    # (L2) m! | (n)_i for m <= i
    bad = 0
    for n in range(0, 60):
        for i in range(0, 16):
            for m in range(0, i + 1):
                if falling(n, i) % factorial(m) != 0:
                    bad += 1
    print(f"  (L2) m! | (n)_i for m <= i                        violations: {bad}")
    must("L2 m! | (n)_i", bad == 0)

    # (L3) N'==N mod k  =>  (k/gcd(k,m!)) | C(N',m)-C(N,m)
    bad = 0
    for k in range(1, 26):
        for m in range(0, 10):
            d = gcd(k, factorial(m))
            for N in range(m, m + 40):
                for mult in range(1, 4):
                    Np = N + k * mult
                    if (comb(Np, m) - comb(N, m)) % (k // d) != 0:
                        bad += 1
    print(f"  (L3) (k/gcd(k,m!)) | C(N',m)-C(N,m)               violations: {bad}")
    must("L3 binomial difference", bad == 0)

    # (L2)+(L3) combined: r! | (n)_i and product is a multiple of k
    bad = 0
    for k in range(1, 20):
        for i in range(0, 12):
            for m in range(0, i + 1):
                d = gcd(k, factorial(m))
                for n in range(i, i + 25):
                    N, Np = n * (n - i), (n + k) * (n + k - i)
                    lhs = falling(n, i) * (comb(Np, m) - comb(N, m))
                    if lhs % k != 0:
                        bad += 1
    print(f"  (L2)x(L3) => k | (n)_i*(C(N',m)-C(N,m))           violations: {bad}")
    must("L2xL3 key divisibility", bad == 0)

    print()
    print("=" * 80)
    print("STEP 6 - edge terms i > n: need k | (n+k)_i")
    print("=" * 80)
    bad = 0
    for k in range(1, 40):
        for n in range(0, 40):
            for i in range(n + 1, n + k + 1):
                if falling(n + k, i) % k != 0:
                    bad += 1
    print(f"  k | (n+k)_i for all n < i <= n+k                  violations: {bad}")
    must("edge case k | (n+k)_i", bad == 0)

    print()
    print("=" * 80)
    print("STEP 5 - TERMWISE shift-stability of eq (*) (the heart of the proof)")
    print("=" * 80)
    bad = 0
    tested = 0
    for k in range(1, 16):
        for i in range(0, 10):
            for r in range(0, i + 1):
                for s in range(0, i - r + 1):
                    for n in range(i, i + 14):
                        X, Xp = falling(n, i), falling(n + k, i)
                        Y, Yp = comb(n, r), comb(n + k, r)
                        Z = comb(n * (n - i), s)
                        Zp = comb((n + k) * (n + k - i), s)
                        tested += 1
                        if (Xp * Yp * Zp - X * Y * Z) % k != 0:
                            bad += 1
                            if bad <= 3:
                                print(f"      VIOLATION k={k} i={i} r={r} s={s} n={n}")
    print(f"  termwise X'Y'Z' == XYZ mod k    tested {tested}   violations: {bad}")
    must("termwise shift-stability (heart of the proof)", bad == 0)

    print()
    print("=" * 80)
    print("STEP 5b - the r <= i constraint is load-bearing, not decorative")
    print("=" * 80)
    # Same statement as STEP 5 over the same (k, i, n) ranges, but with r and s allowed
    # to exceed i. The arithmetic claim must then FAIL: without r <= i there is no
    # guarantee that r! divides (n)_i, so the binomial denominators are not absorbed.
    # This is the check behind the claim in REVIEWING.md that the hypothesis is
    # essential; the count below is what this range actually produces.
    bad_nc = 0
    tested_nc = 0
    RMAX = 12
    for k in range(1, 16):
        for i in range(0, 10):
            for r in range(0, RMAX):
                for s in range(0, RMAX - r):
                    if r <= i and s <= i - r:
                        continue          # that is STEP 5, already checked
                    for n in range(i, i + 14):
                        X, Xp = falling(n, i), falling(n + k, i)
                        Y, Yp = comb(n, r), comb(n + k, r)
                        Z = comb(n * (n - i), s)
                        Zp = comb((n + k) * (n + k - i), s)
                        tested_nc += 1
                        if (Xp * Yp * Zp - X * Y * Z) % k != 0:
                            bad_nc += 1
    print(f"  with r <= i REMOVED             tested {tested_nc}   violations: {bad_nc}")
    print("  (violations here are the point: the constraint cannot be dropped)")
    must("dropping r <= i breaks the termwise claim", bad_nc > 0)

    print()
    print("=" * 80)
    print("CONCLUSION - full congruence on the three OEIS targets + random F,G")
    print("=" * 80)
    inv = as_series([1] * (DEG + 1), DEG)
    onep = as_series([1, 1], DEG)
    one = as_series([1], DEG)
    targets = [
        ("A293013  F=1,     G=1/(1-x)", one, inv, [1, 1, 5, 55, 961, 24101]),
        ("A361281  F=1,     G=1+x",     one, onep, [1, 1, 5, 37, 481, 10001]),
        ("A361036  F=1+x,   G=1+x",     onep, onep, [1, 2, 11, 124, 2225, 56546]),
    ]
    for label, F, G, head in targets:
        a = b_direct(F, G, 24)
        okhead = a[:len(head)] == head
        viol = [(n, k) for k in range(1, 13) for n in range(0, 24 - k + 1)
                if (a[n + k] - a[n]) % k != 0]
        print(f"  {label}")
        print(f"      matches OEIS terms: {okhead}   congruence violations: {len(viol)}")
        must(f"{label}: matches OEIS terms", okhead)
        must(f"{label}: congruence holds", len(viol) == 0)

    nbad = 0
    for t in range(10):
        F, G = rand_F(DEG, rng), rand_F(DEG, rng)
        a = b_direct(F, G, 20)
        viol = [(n, k) for k in range(1, 11) for n in range(0, 20 - k + 1)
                if (a[n + k] - a[n]) % k != 0]
        if viol:
            nbad += 1
            print(f"  random F={F[:3]} G={G[:3]} -> VIOLATIONS {viol[:3]}")
    print(f"\n  random (F,G) with F(0)=G(0)=1: {10 - nbad}/10 satisfy the congruence")

    print()
    print("=" * 80)
    print("SHARPNESS - *** THE CLAIM THIS BLOCK ORIGINALLY MADE WAS WRONG ***")
    print("  The necessary condition is F(0)*G(0) = 1, NOT F(0) = G(0) = 1.")
    print("  (F(0),G(0)) = (-1,-1) also satisfies the congruence, and with EVEN F~,G~")
    print("  it gives an infinite family for which it HOLDS. Randomising only the")
    print("  constant term, as below, never samples that family, which is why this")
    print("  block reported a false 'sharpness'. See check_sharpness.py for the")
    print("  correct statement and counterexamples. The trials below are retained")
    print("  only to show what the flawed test actually measured.")
    print("=" * 80)
    for which in ("F", "G"):
        nb = 0
        for t in range(6):
            F = rand_F(DEG, rng, const1=(which != "F"))
            G = rand_F(DEG, rng, const1=(which != "G"))
            if (which == "F" and F[0] == 1) or (which == "G" and G[0] == 1):
                continue
            try:
                a = b_direct(F, G, 16)
            except AssertionError:
                continue
            viol = [(n, k) for k in range(1, 9) for n in range(0, 16 - k + 1)
                    if (a[n + k] - a[n]) % k != 0]
            if viol:
                nb += 1
        print(f"  {which}(0) != 1  ->  {nb}/6 trials FAIL the congruence (expected: most)")


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
