#!/usr/bin/env python3
"""
A GENERALIZATION OF BALA'S THEOREM, targeting three OEIS conjectures that his
theorem provably does not cover.

Background. Bala (Dec 2017, "Integer sequences that become periodic on reduction
modulo k for all k", linked from OEIS A047974) proves:

    THEOREM 1 (Bala).  If A(x) = sum a(n) x^n/n! = F(x) exp(x G(x)) with
    F, G in Z[[x]] and G(0) = 1, then a(n+k) == a(n) (mod k) for all n,k.

This settled A000262, A082579, A255807, A255819, A294361, A294362, A294363
(all annotated "The above conjecture is true - see the Bala link").

Three sequences carrying the SAME conjecture are NOT annotated as resolved:

    A293013  a(n) = n! [x^n] exp( x/(1-x)^n )
    A361281  a(n) = n! sum_k C(nk, n-k)/k!  =  n! [x^n] exp( x (1+x)^n )
    A361036  a(n) = n! [x^n] (1+x)^n exp( x (1+x)^n )

Bala's theorem does not apply: the inner series depends on n, so there is no
FIXED G. Writing H for the base series, all three have the shape

    a(n) = n! [x^n] H(x)^(alpha*n) * exp( x * H(x)^n ),      H in Z[[x]], H(0)=1

  A293013: H = 1/(1-x), alpha = 0
  A361281: H = 1 + x,   alpha = 0
  A361036: H = 1 + x,   alpha = 1

CONJECTURE (generalized Bala). For H in Z[[x]] with H(0) = 1, any integer
alpha >= 0, and any fixed F in Z[[x]], the diagonal sequence
    a(n) = n! [x^n] F(x) H(x)^(alpha*n) exp( x H(x)^n )
satisfies a(n+k) == a(n) (mod k) for all n, k.

NOTE the general n-dependent statement is FALSE without structure: taking
G_n = 1 and F_n arbitrary makes a(n) essentially arbitrary. So the H(x)^n form
is doing real work, and that is exactly what this script probes.
"""

from fractions import Fraction
from math import factorial
import random


def series_mul(a, b, deg):
    out = [Fraction(0)] * (deg + 1)
    for i, ai in enumerate(a[:deg + 1]):
        if ai:
            for j, bj in enumerate(b[:deg + 1 - i]):
                if bj:
                    out[i + j] += ai * bj
    return out


def series_pow(a, e, deg):
    r = [Fraction(1)] + [Fraction(0)] * deg
    for _ in range(e):
        r = series_mul(r, a, deg)
    return r


def exp_of(f, deg):
    """exp(f) for f with f[0]=0, via A' = f' A."""
    A = [Fraction(0)] * (deg + 1)
    A[0] = Fraction(1)
    for m in range(deg):
        acc = Fraction(0)
        for k in range(1, m + 2):
            if k <= deg and f[k]:
                acc += Fraction(k) * f[k] * A[m + 1 - k]
        A[m + 1] = acc / Fraction(m + 1)
    return A


def diag_seq(H, alpha, F, N):
    """a(n) = n! [x^n] F(x) H(x)^(alpha*n) exp(x H(x)^n)."""
    out = []
    for n in range(N + 1):
        deg = n
        Hn = series_pow(H, n, deg)                     # H^n
        xHn = [Fraction(0)] + Hn[:deg]                 # x*H(x)^n
        E = exp_of(xHn, deg)
        pref = series_pow(H, alpha * n, deg)
        S = series_mul(pref, E, deg)
        if F is not None:
            S = series_mul(F, S, deg)
        v = S[n] * factorial(n)
        if v.denominator != 1:
            return None
        out.append(int(v))
    return out


def gauss_fail(a, maxk=None):
    L = len(a) - 1
    maxk = maxk or L // 2
    for k in range(1, maxk + 1):
        for n in range(0, L - k + 1):
            if (a[n + k] - a[n]) % k != 0:
                return (n, k)
    return None


def as_series(coeffs, deg):
    c = [Fraction(x) for x in coeffs[:deg + 1]]
    c += [Fraction(0)] * (deg + 1 - len(c))
    return c


def main():
    N = 30
    print("=" * 78)
    print("PART 1 - reproduce the three target sequences and confirm the conjecture")
    print("=" * 78)
    inv1mx = as_series([1] * (N + 1), N)          # 1/(1-x)
    onepx = as_series([1, 1], N)                  # 1+x
    targets = [
        ("A293013  H=1/(1-x), alpha=0", inv1mx, 0, None,
         [1, 1, 5, 55, 961, 24101]),
        ("A361281  H=1+x,     alpha=0", onepx, 0, None,
         [1, 1, 5, 37, 481, 10001]),
        ("A361036  H=1+x,     alpha=1", onepx, 1, None,
         [1, 2, 11, 124, 2225, 56546]),
    ]
    for label, H, al, F, head in targets:
        a = diag_seq(H, al, F, N)
        ok = a[:len(head)] == head
        f = gauss_fail(a)
        print(f"  {label}")
        print(f"      terms {a[:6]}  matches OEIS: {ok}")
        print(f"      Gauss congruence: {'HOLDS' if not f else f'FAILS at {f}'}")

    print()
    print("=" * 78)
    print("PART 2 - THE TEST: random integral H with H(0)=1, various alpha")
    print("=" * 78)
    random.seed(20260820)
    fails = 0
    trials = 0
    for alpha in (0, 1, 2):
        for t in range(14):
            coeffs = [1] + [random.randint(-6, 6) for _ in range(8)]
            H = as_series(coeffs, N)
            a = diag_seq(H, alpha, None, N)
            trials += 1
            if a is None:
                print(f"  alpha={alpha} H={coeffs[:5]} -> non-integral")
                continue
            f = gauss_fail(a)
            if f:
                fails += 1
                print(f"  alpha={alpha} H={coeffs[:5]} -> FAILS at {f}")
    print(f"\n  random H with H(0)=1: {trials - fails}/{trials} HOLD")

    print()
    print("=" * 78)
    print("PART 3 - control: H(0) != 1 should break it (matches Bala's hypothesis)")
    print("=" * 78)
    for h0 in (0, 2, 3, -1):
        coeffs = [h0] + [random.randint(-4, 4) for _ in range(6)]
        H = as_series(coeffs, N)
        a = diag_seq(H, 0, None, N)
        if a is None:
            print(f"  H(0)={h0} -> non-integral")
            continue
        f = gauss_fail(a)
        print(f"  H(0)={h0:3d} H={coeffs[:5]} -> {'HOLDS' if not f else f'fails at {f}'}")

    print()
    print("=" * 78)
    print("PART 4 - extra generality: fixed integral prefactor F(x) as well")
    print("=" * 78)
    for t in range(8):
        Hc = [1] + [random.randint(-5, 5) for _ in range(6)]
        Fc = [random.randint(-5, 5) for _ in range(6)]
        H = as_series(Hc, N)
        F = as_series(Fc, N)
        a = diag_seq(H, random.choice([0, 1]), F, N)
        if a is None:
            print(f"  F={Fc[:4]} H={Hc[:4]} -> non-integral")
            continue
        f = gauss_fail(a)
        print(f"  F={Fc[:4]} H={Hc[:4]} -> {'HOLDS' if not f else f'FAILS at {f}'}")


if __name__ == "__main__":
    main()
