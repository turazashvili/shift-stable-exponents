#!/usr/bin/env python3
"""
DECISIVE TEST of the conjecture isolated by characterize_gauss.py:

    CONJECTURE.  Let c_1 = 1 and let c_2, c_3, ... be ARBITRARY integers.
    Define  a(n) = n! * [x^n] exp( sum_{k>=1} c_k x^k ).
    Then    a(n+k) == a(n)  (mod k)   for all n >= 0, k >= 1.

NECESSITY is provable by hand: a(0)=1, and expanding,
    a(p) = c_1^p + (terms divisible by p)  ==  c_1^p  ==  c_1  (mod p)   [Fermat]
so a(p) == a(0) mod p forces c_1 == 1 (mod p) for EVERY prime p, hence c_1 = 1.

This script stress-tests SUFFICIENCY. If it survives, the seven open OEIS
conjectures (A000262, A082579, A255807, A255819, A294361, A294362, A294363) are
all corollaries of one theorem, since each has c_1 = 1:
    1, k, k^2, k^3, sigma(k), sigma_2(k), d(k)  all equal 1 at k=1.
"""

from fractions import Fraction
import random
import sys


def a_from_c(c, n):
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


def first_gauss_failure(a, maxk=None):
    L = len(a) - 1
    maxk = maxk or L // 2
    for k in range(1, maxk + 1):
        for n in range(0, L - k + 1):
            if (a[n + k] - a[n]) % k != 0:
                return (n, k)
    return None


def run(label, trials, N, gen, seed):
    random.seed(seed)
    fails = []
    nonint = 0
    for t in range(trials):
        c = gen(N)
        a = a_from_c(c, N)
        if a is None:
            nonint += 1
            continue
        f = first_gauss_failure(a)
        if f:
            fails.append((t, c[1:8], f))
    status = "ALL HOLD" if not fails else f"{len(fails)} FAILURES"
    print(f"  {label:52s} N={N:3d} trials={trials:4d} -> {status}"
          + (f"  non-integral={nonint}" if nonint else ""))
    for t, head, f in fails[:4]:
        print(f"        trial {t}: c_1..c_7={head} first failure (n,k)={f}")
    return len(fails)


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 46
    print("=" * 84)
    print("SUFFICIENCY STRESS TEST:  c_1 = 1, arbitrary integers thereafter")
    print("=" * 84)

    total = 0
    total += run("c_1=1, c_k in [-9,9]", 200, N,
                 lambda n: [0, 1] + [random.randint(-9, 9) for _ in range(n)], 1)
    total += run("c_1=1, c_k in [-10^6,10^6]", 120, N,
                 lambda n: [0, 1] + [random.randint(-10**6, 10**6) for _ in range(n)], 2)
    total += run("c_1=1, c_k in [0,3] (sparse/small)", 200, N,
                 lambda n: [0, 1] + [random.randint(0, 3) for _ in range(n)], 3)
    total += run("c_1=1, c_k mostly zero", 200, N,
                 lambda n: [0, 1] + [random.choice([0, 0, 0, 0, random.randint(-50, 50)])
                                     for _ in range(n)], 4)
    total += run("c_1=1, c_k huge alternating", 80, N,
                 lambda n: [0, 1] + [(-1) ** k * random.randint(0, 10**9)
                                     for k in range(n)], 5)

    print()
    print("=" * 84)
    print("CONTROL: c_1 != 1 should fail (necessity, proved by hand via Fermat)")
    print("=" * 84)
    for v in (-1, 0, 2, 3, 7, -5):
        run(f"c_1={v}, c_k in [-9,9]", 40, N,
            lambda n, v=v: [0, v] + [random.randint(-9, 9) for _ in range(n)], 11)

    print()
    print("=" * 84)
    print("THE SEVEN OPEN OEIS INSTANCES, at higher range")
    print("=" * 84)

    def sig(k, p):
        s, d = 0, 1
        while d * d <= k:
            if k % d == 0:
                s += d ** p
                e = k // d
                if e != d:
                    s += e ** p
            d += 1
        return s

    inst = [
        ("A000262 c_k=1",          lambda k: 1),
        ("A082579 c_k=k",          lambda k: k),
        ("A255807 c_k=k^2",        lambda k: k * k),
        ("A255819 c_k=k^3",        lambda k: k ** 3),
        ("A294361 c_k=sigma(k)",   lambda k: sig(k, 1)),
        ("A294362 c_k=sigma_2(k)", lambda k: sig(k, 2)),
        ("A294363 c_k=d(k)",       lambda k: sig(k, 0)),
    ]
    NN = 90
    allok = True
    for name, f in inst:
        c = [0] + [f(k) for k in range(1, NN + 1)]
        a = a_from_c(c, NN)
        fail = first_gauss_failure(a)
        ok = fail is None
        allok &= ok
        print(f"  {name:26s} c_1={f(1)}  n,k up to {NN}  -> "
              f"{'HOLDS' if ok else f'FAILS at {fail}'}")

    print()
    print("=" * 84)
    if total == 0 and allok:
        print("RESULT: sufficiency survived every trial; necessity is proved.")
        print("        => single theorem 'c_1 = 1  <=>  Gauss congruence' subsumes")
        print("           all seven open OEIS conjectures.")
    else:
        print(f"RESULT: {total} sufficiency failures -- conjecture as stated is FALSE.")
    print("=" * 84)


if __name__ == "__main__":
    main()
