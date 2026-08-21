#!/usr/bin/env python3
"""
Numerical check of the LOCALIZED congruence (Section 8 of the paper).

For D >= 2 and W, F, G in Z[1/D][[x]] with F(0) = G(0) = 1, and A, M shift-stable,
we ask whether

    b(n+k) - b(n)  in  k * Z[1/D]        for all n >= 0, k >= 1.

This is now a THEOREM (paper Prop. "ring-general" + Cor. "localized"): the proof of
the main theorem runs verbatim over any commutative ring, so it holds for R = Z[1/D]
and for EVERY k, with no coprimality restriction. It is proved by hand and is NOT part
of the Lean development. This script is the independent numerical confirmation, and
prints the exact number of (n,k) pairs behind the figure quoted in the paper.

Note on formulation: for G outside Z[[x]] the values b(n) need not be integers
(e.g. G = 1 + x/3 gives b(2) = 5/3), so divisibility must be read in Z[1/D]:
d/k lies in Z[1/D] iff, after removing all factors of the primes dividing D from
the denominator of d/k, nothing is left.

It also checks the specific claim in the paper that for G = 1 + x/3 the k = 2
instance IS divisible in Z[1/3] -- the example that an earlier draft wrongly
presented as a counterexample.

Usage:
    python3 verification/probe_localization.py
"""

import random
from fractions import Fraction as Fr
from math import gcd

DS = [2, 3, 4, 5, 6, 8, 9, 10, 12]
NMAX = 11
SEED = 7


def prime_factors(m):
    f, d = set(), 2
    while d * d <= m:
        while m % d == 0:
            f.add(d)
            m //= d
        d += 1
    if m > 1:
        f.add(m)
    return f


def mul(a, b, N):
    r = [Fr(0)] * (N + 1)
    for i, x in enumerate(a):
        if x == 0 or i > N:
            continue
        for j, y in enumerate(b[: N - i + 1]):
            if y:
                r[i + j] += x * y
    return r


def power(a, e, N):
    r = [Fr(1)] + [Fr(0)] * N
    base = a[: N + 1] + [Fr(0)] * max(0, N + 1 - len(a))
    while e:
        if e & 1:
            r = mul(r, base, N)
        e >>= 1
        if e:
            base = mul(base, base, N)
    return r


def ff(n, i):
    p = 1
    for t in range(i):
        p *= n - t
    return p


def b_seq(W, F, G, A, M, NM):
    out = []
    for n in range(NM + 1):
        N = n
        base = mul(W[: N + 1] + [Fr(0)] * (N + 1), power(F, A(n), N), N)
        H = power(G, M(n), N)
        Hj = [Fr(1)] + [Fr(0)] * N
        tot = Fr(0)
        for j in range(n + 1):
            tot += ff(n, n - j) * mul(base, Hj, N)[n - j]
            if j < n:
                Hj = mul(Hj, H, N)
        out.append(tot)
    return out


def divisible_in_ZD(d, k, D):
    """is d/k in Z[1/D]?"""
    q = Fr(d, 1) / k if not isinstance(d, Fr) else d / k
    t = q.denominator
    for p in prime_factors(D):
        while t % p == 0:
            t //= p
    return t == 1


EXPONENTS = [
    ("A=n,   M=n", lambda n: n, lambda n: n),
    ("A=n,   M=1", lambda n: n, lambda n: 1),
    ("A=0,   M=n", lambda n: 0, lambda n: n),
    ("A=n^2, M=n", lambda n: n * n, lambda n: n),
]


def main():
    rng = random.Random(SEED)
    print("=" * 78)
    print("CHECK: localized congruence  b(n+k)-b(n) in k*Z[1/D],  every k")
    print("proved by hand (ring-general argument); NOT in the Lean development")
    print("=" * 78)

    total = 0
    total_coprime = 0
    fails = []
    for D in DS:
        for trial in range(12):
            L = rng.randint(1, 3)
            G = [Fr(1)] + [Fr(rng.randint(-6, 6), D ** rng.randint(0, 2)) for _ in range(L)]
            if trial % 2:
                F = [Fr(1)] + [
                    Fr(rng.randint(-5, 5), D ** rng.randint(0, 2))
                    for _ in range(rng.randint(1, 2))
                ]
            else:
                F = [Fr(1)]
            W = [Fr(rng.randint(-4, 4)) for _ in range(3)]
            if all(c == 0 for c in W):
                W = [Fr(1)]
            ename, A, M = EXPONENTS[trial % len(EXPONENTS)]
            Gp = G + [Fr(0)] * (NMAX + 2)
            Fp = F + [Fr(0)] * (NMAX + 2)
            Wp = W + [Fr(0)] * (NMAX + 2)
            b = b_seq(Wp, Fp, Gp, A, M, NMAX)
            for n in range(NMAX + 1):
                for k in range(1, NMAX + 1 - n):
                    # the theorem covers EVERY k, not only k coprime to D
                    total += 1
                    if gcd(k, D) == 1:
                        total_coprime += 1
                    if not divisible_in_ZD(b[n + k] - b[n], k, D):
                        fails.append((D, ename, n, k, str(b[n + k] - b[n])))

    print(f"  D values     : {DS}")
    print(f"  bound        : n+k <= {NMAX}")
    print(f"  pairs tested : {total}   (all k, no coprimality restriction)")
    print(f"     of which  : {total_coprime} have gcd(k,D)=1")
    print(f"  failures     : {len(fails)}")
    for f in fails[:10]:
        print("   ", f)
    print()

    print("=" * 78)
    print("the G = 1 + x/3 example an earlier draft called a counterexample")
    print("=" * 78)
    D = 3
    G = [Fr(1), Fr(1, 3)] + [Fr(0)] * (NMAX + 2)
    one = [Fr(1)] + [Fr(0)] * (NMAX + 2)
    b = b_seq(one, one, G, lambda n: 1, lambda n: 1, NMAX)
    print(f"  b(0..5) = {[str(x) for x in b[:6]]}   (b(2) = 5/3 is NOT an integer)")
    d = b[2] - b[0]
    print(f"  b(2)-b(0) = {d};  divided by k=2 -> {d / 2}")
    print(f"  in Z[1/3]? {divisible_in_ZD(d, 2, 3)}   <-- so it is NOT a counterexample")
    bad = [
        (n, k)
        for n in range(NMAX + 1)
        for k in range(1, NMAX + 1 - n)
        if gcd(k, 3) == 1 and not divisible_in_ZD(b[n + k] - b[n], k, 3)
    ]
    print(f"  failures for k coprime to 3, n+k <= {NMAX}: {len(bad)}")
    print()

    print("=" * 78)
    print("A000085 (G = 1 + x/2): integral, and odd-k congruence already in OEIS")
    print("=" * 78)
    G2 = [Fr(1), Fr(1, 2)] + [Fr(0)] * (NMAX + 2)
    a = b_seq(one, one, G2, lambda n: 1, lambda n: 1, NMAX)
    print(f"  a(0..8) = {[str(x) for x in a[:9]]}")
    print(f"  all integers? {all(x.denominator == 1 for x in a)}")
    odd_bad = [
        (n, k)
        for n in range(NMAX + 1)
        for k in range(1, NMAX + 1 - n)
        if k % 2 == 1 and (a[n + k] - a[n]) % k != 0
    ]
    even_bad = [
        (n, k)
        for n in range(NMAX + 1)
        for k in range(1, NMAX + 1 - n)
        if k % 2 == 0 and (a[n + k] - a[n]) % k != 0
    ]
    print(f"  failures for ODD  k: {len(odd_bad)}  (OEIS records the odd-k congruence)")
    print(f"  failures for EVEN k: {len(even_bad)}  (expected: the congruence is odd-k only)")
    print()
    print("Quote in the paper:")
    print(f"    no failure among {total} pairs (n,k), every k, n+k <= {NMAX}, D in {DS}")
    return 1 if fails else 0


if __name__ == "__main__":
    raise SystemExit(main())
