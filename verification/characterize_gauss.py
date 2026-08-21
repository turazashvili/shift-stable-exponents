#!/usr/bin/env python3
"""
Characterise EXACTLY which coefficient sequences (c_k) make

    a(n) = n! * [x^n] exp( sum_{k>=1} c_k x^k )

satisfy the Gauss congruence   a(n+k) == a(n)  (mod k)  for all n,k >= 1.

Motivation: seven OPEN OEIS conjectures (A000262, A082579, A255807, A255819,
A294361, A294362, A294363) are all this statement for particular (c_k), and all
seven verify numerically. But random integer (c_k) FAILS, so there is a real
condition to find. If it is clean, one theorem kills all seven at once.

Note on the combinatorics: exp(sum c_k x^k) has no 1/k!, so by the exponential
formula a(n) = sum over set partitions pi of [n] of prod_{B in pi} (|B|! * c_{|B|}),
i.e. a block of size m carries weight m! * c_m. For c_k=1 that is m! = the number
of linear orders on the block, hence A000262 "sets of LISTS".
"""

from fractions import Fraction
from math import comb, factorial
import itertools

N = 42


def a_from_c(c, n=N):
    """a(m) = m! [x^m] exp(sum_{k>=1} c_k x^k), via (m+1)A_{m+1} = sum k c_k A_{m+1-k}."""
    A = [Fraction(0)] * (n + 1)
    A[0] = Fraction(1)
    for m in range(n):
        acc = Fraction(0)
        for k in range(1, m + 2):
            if k < len(c) and c[k]:
                acc += Fraction(k) * Fraction(c[k]) * A[m + 1 - k]
        A[m + 1] = acc / Fraction(m + 1)
    out, fact = [], 1
    for m in range(n + 1):
        if m:
            fact *= m
        v = A[m] * fact
        if v.denominator != 1:
            return None
        out.append(int(v))
    return out


def a_from_partitions(c, n=N):
    """Cross-check: a(m) = sum_j C(m-1,j-1) * (j! * c_j) * a(m-j)."""
    a = [0] * (n + 1)
    a[0] = 1
    for m in range(1, n + 1):
        s = 0
        for j in range(1, m + 1):
            if j < len(c):
                s += comb(m - 1, j - 1) * factorial(j) * c[j] * a[m - j]
        a[m] = s
    return a


def gauss_fails(a, maxk=None):
    """First violation of a(n+k) == a(n) mod k, or None."""
    L = len(a) - 1
    maxk = maxk or L // 2
    for k in range(1, maxk + 1):
        for n in range(0, L - k + 1):
            if (a[n + k] - a[n]) % k != 0:
                return (n, k)
    return None


def const(v):
    return [0] + [v] * N


def main():
    print("=" * 76)
    print("STEP 0 - fix verified: the two computation methods must now agree")
    print("=" * 76)
    for name, c in [("c_k=1", const(1)), ("c_k=k", [0] + list(range(1, N + 1))),
                    ("c_k=k^2", [0] + [k * k for k in range(1, N + 1)])]:
        a1, a2 = a_from_c(c), a_from_partitions(c)
        print(f"  {name:10s} egf={a1[:7]}  partitions={a2[:7]}  agree={a1 == a2}")

    print()
    print("=" * 76)
    print("STEP 1 - constant c_k = v.  Which v satisfy the congruence?")
    print("=" * 76)
    for v in range(-6, 9):
        a = a_from_c(const(v))
        f = gauss_fails(a)
        print(f"  c_k={v:3d}  ->  {'HOLDS' if not f else f'fails at (n,k)={f}'}"
              f"    a(0..5)={a[:6]}")

    print()
    print("=" * 76)
    print("STEP 2 - c_k = k^j and other divisor-type functions")
    print("=" * 76)

    def sigma(k, p):
        s = 0
        d = 1
        while d * d <= k:
            if k % d == 0:
                s += d ** p
                e = k // d
                if e != d:
                    s += e ** p
            d += 1
        return s

    cands = {
        "k^0 = 1": lambda k: 1,
        "k^1": lambda k: k,
        "k^2": lambda k: k * k,
        "k^3": lambda k: k ** 3,
        "k^4": lambda k: k ** 4,
        "d(k)=sigma_0": lambda k: sigma(k, 0),
        "sigma_1(k)": lambda k: sigma(k, 1),
        "sigma_2(k)": lambda k: sigma(k, 2),
        "sigma_3(k)": lambda k: sigma(k, 3),
        "2k": lambda k: 2 * k,
        "k+1": lambda k: k + 1,
        "k^2+k": lambda k: k * k + k,
        "phi(k)": lambda k: sum(1 for i in range(1, k + 1)
                                if __import__("math").gcd(i, k) == 1),
        "mu-like [k==1]": lambda k: 1 if k == 1 else 0,
        "2^k": lambda k: 2 ** k,
        "k!": lambda k: factorial(k),
    }
    holds = []
    for name, f in cands.items():
        c = [0] + [f(k) for k in range(1, N + 1)]
        a = a_from_c(c)
        fail = gauss_fails(a)
        if not fail:
            holds.append(name)
        print(f"  c_k={name:16s} -> {'HOLDS' if not fail else f'fails at {fail}'}")

    print()
    print("=" * 76)
    print("STEP 3 - closure: is the HOLDS set closed under addition? (c + c')")
    print("=" * 76)
    base = {
        "1": lambda k: 1,
        "k": lambda k: k,
        "k^2": lambda k: k * k,
        "d(k)": lambda k: sigma(k, 0),
        "sigma(k)": lambda k: sigma(k, 1),
    }
    names = list(base)
    for i in range(len(names)):
        for j in range(i, len(names)):
            f, g = base[names[i]], base[names[j]]
            c = [0] + [f(k) + g(k) for k in range(1, N + 1)]
            fail = gauss_fails(a_from_c(c))
            print(f"  ({names[i]}) + ({names[j]}):{'':4s} "
                  f"{'HOLDS' if not fail else f'fails at {fail}'}")

    print()
    print("=" * 76)
    print("STEP 4 - THE KEY PROBE. Every holding case above has the form")
    print("         c_k = sum_{d|k} g(d) for some integer g (Dirichlet conv with 1).")
    print("         1=[d==1]*1, k=sum phi(d), k^2=sum J_2(d), sigma_j = 1*Id_j ...")
    print("         So test: c = 1 * g  (i.e. c_k = sum_{d|k} g(d)) for random g.")
    print("=" * 76)
    import random
    random.seed(7)
    ok = bad = 0
    for t in range(14):
        g = [0] + [random.randint(-9, 9) for _ in range(N)]
        c = [0] + [sum(g[d] for d in range(1, k + 1) if k % d == 0)
                   for k in range(1, N + 1)]
        a = a_from_c(c)
        fail = gauss_fails(a) if a else "non-integral"
        if fail:
            bad += 1
        else:
            ok += 1
        print(f"  trial {t:2d} g_1..g_5={g[1:6]}  c_1..c_5={c[1:6]}  "
              f"-> {'HOLDS' if not fail else f'fails at {fail}'}")
    print(f"\n  divisor-sum form:  HOLDS {ok}/14,  fails {bad}/14")

    print()
    print("=" * 76)
    print("STEP 5 - control: random c NOT of divisor-sum form")
    print("=" * 76)
    ok2 = bad2 = 0
    for t in range(8):
        c = [0] + [random.randint(-9, 9) for _ in range(N)]
        a = a_from_c(c)
        fail = gauss_fails(a) if a else "non-integral"
        if fail:
            bad2 += 1
        else:
            ok2 += 1
        print(f"  trial {t:2d} c_1..c_5={c[1:6]} -> "
              f"{'HOLDS' if not fail else f'fails at {fail}'}")
    print(f"\n  arbitrary c:  HOLDS {ok2}/8,  fails {bad2}/8")


if __name__ == "__main__":
    main()
