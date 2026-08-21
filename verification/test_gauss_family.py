#!/usr/bin/env python3
"""
Test a UNIFIED conjecture covering a whole family of open OEIS conjectures.

Observation from mining OEIS: the "Gauss congruence" conjecture
    a(n+k) == a(n)  (mod k)    for all n, k >= 1
is posted as OPEN on many sequences, and a large subfamily all have the same shape

    a(n) = n! * [x^n] exp( sum_{k>=1} c_k x^k )        (c_k integers)

which by the exponential formula equals

    a(n) = sum over set partitions pi of [n] of  prod_{B in pi} c_{|B|}

i.e. the number of set partitions of [n] where a block of size m carries one of
c_m colours. Open instances found:

    A000262  c_k = 1          exp(x/(1-x))          "sets of lists"   (CORE seq)
    A082579  c_k = k          exp(x/(1-x)^2)
    A255807  c_k = k^2        exp(sum k^2 x^k)
    A255819  c_k = k^3        exp(sum k^3 x^k)
    A294361  c_k = sigma(k)   exp(sum sigma(k) x^k)
    A294362  c_k = sigma_2(k) exp(sum sigma_2(k) x^k)
    A294363  c_k = d(k)       exp(sum d(k) x^k)

DeepMind's agent proved the SAME congruence for A278070 as a one-off. If the
congruence instead holds for ARBITRARY integer (c_k), then all of these are
corollaries of a single theorem -- a much stronger and more publishable result
than seven separate proofs.

This script:
  (1) computes each sequence exactly and checks it against OEIS's own terms,
  (2) tests the congruence for each,
  (3) tests the congruence for RANDOM integer (c_k), which is the real test of
      whether a general theorem exists,
  (4) probes whether integrality of c_k is actually needed.
"""

from fractions import Fraction
from functools import lru_cache
import random
import sys

N = 60  # number of terms to compute


# ------------------------------------------------------------------ arithmetic

def divisors_sigma(k, power):
    s = 0
    d = 1
    while d * d <= k:
        if k % d == 0:
            s += d ** power
            e = k // d
            if e != d:
                s += e ** power
        d += 1
    return s


def egf_exp_coeffs(c, n):
    """Given c[1..n] integers, return a[0..n] with a(m) = m! [x^m] exp(sum c_k x^k).

    Uses A' = f' A on the ordinary series, then multiplies by m!.
    A(x) = sum A_m x^m, f(x) = sum_{k>=1} c_k x^k.
    (m+1) A_{m+1} = sum_{k=1}^{m+1} k c_k A_{m+1-k}
    """
    A = [Fraction(0)] * (n + 1)
    A[0] = Fraction(1)
    for m in range(0, n):
        acc = Fraction(0)
        for k in range(1, m + 2):
            if k < len(c) and c[k] != 0:
                acc += Fraction(k) * Fraction(c[k]) * A[m + 1 - k]
        A[m + 1] = acc / Fraction(m + 1)
    # multiply by m!
    out = []
    fact = 1
    for m in range(n + 1):
        if m > 0:
            fact *= m
        v = A[m] * fact
        assert v.denominator == 1, f"non-integer term at m={m}: {v}"
        out.append(int(v))
    return out


def set_partition_weighted(c, n):
    """Independent check via the recurrence a(n) = sum_{j=1}^{n} C(n-1,j-1) c_j a(n-j)."""
    from math import comb
    a = [0] * (n + 1)
    a[0] = 1
    for m in range(1, n + 1):
        s = 0
        for j in range(1, m + 1):
            if j < len(c):
                s += comb(m - 1, j - 1) * c[j] * a[m - j]
        a[m] = s
    return a


# ------------------------------------------------------------------ the test

def check_gauss(a, maxk=None, maxn=None):
    """Check a(n+k) == a(n) mod k. Returns list of counterexamples."""
    L = len(a) - 1
    maxk = maxk or L // 2
    bad = []
    for k in range(1, maxk + 1):
        for n in range(0, L - k + 1):
            if maxn and n > maxn:
                break
            if (a[n + k] - a[n]) % k != 0:
                bad.append((n, k, a[n], a[n + k]))
    return bad


FAMILY = {
    "A000262 c_k=1        exp(x/(1-x))":        lambda k: 1,
    "A082579 c_k=k        exp(x/(1-x)^2)":      lambda k: k,
    "A255807 c_k=k^2":                          lambda k: k * k,
    "A255819 c_k=k^3":                          lambda k: k ** 3,
    "A294361 c_k=sigma(k)":                     lambda k: divisors_sigma(k, 1),
    "A294362 c_k=sigma_2(k)":                   lambda k: divisors_sigma(k, 2),
    "A294363 c_k=d(k)":                         lambda k: divisors_sigma(k, 0),
}

# Validate our definitions against OEIS's own stored terms, read from the dump.
def oeis_terms(anum, root="oeisdata"):
    import os
    import re
    p = os.path.join(root, "seq", anum[:4], anum + ".seq")
    if not os.path.exists(p):
        return None
    raw = ""
    with open(p, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            m = re.match(r"^%([STU])\s+A\d{6}\s?(.*)$", line.rstrip("\n"))
            if m:
                raw += m.group(2)
    out = []
    for tok in raw.split(","):
        tok = tok.strip()
        if tok:
            try:
                out.append(int(tok))
            except ValueError:
                pass
    return out


def main():
    print("=" * 74)
    print("PART 1 - each known open instance, computed two independent ways")
    print("=" * 74)
    seqs = {}
    for label, f in FAMILY.items():
        c = [0] + [f(k) for k in range(1, N + 1)]
        a1 = egf_exp_coeffs(c, N)
        a2 = set_partition_weighted(c, N)
        agree = a1 == a2
        seqs[label] = a1
        anum = label.split()[0]
        oe = oeis_terms(anum)
        if oe:
            # OEIS offset may be 0 or 1; accept a match as a contiguous prefix.
            m = min(len(oe), 10)
            match = (a1[:m] == oe[:m]) or (a1[1:m + 1] == oe[:m])
            oestat = f"matches OEIS stored terms: {match}"
        else:
            oestat = "OEIS terms not found"
        print(f"\n{label}")
        print(f"    first terms : {a1[:9]}")
        print(f"    two methods agree: {agree}   |   {oestat}")
        bad = check_gauss(a1)
        if bad:
            print(f"    GAUSS CONGRUENCE: *** FAILS *** e.g. {bad[:3]}")
        else:
            print(f"    GAUSS CONGRUENCE: holds for all 1<=k<={len(a1)//2}, "
                  f"0<=n<={len(a1)-1}-k  ({sum(1 for _ in range(1, len(a1)//2+1))} moduli)")

    print()
    print("=" * 74)
    print("PART 2 - THE REAL TEST: random integer (c_k). If the congruence holds")
    print("         for arbitrary integers, one theorem implies every instance.")
    print("=" * 74)
    random.seed(20260820)
    fails = 0
    for trial in range(12):
        c = [0] + [random.randint(-40, 40) for _ in range(N)]
        a = egf_exp_coeffs(c, N)
        bad = check_gauss(a)
        tag = "OK  " if not bad else "FAIL"
        if bad:
            fails += 1
        print(f"  trial {trial:2d}  c_1..c_6={c[1:7]}  -> {tag}"
              + ("" if not bad else f"  counterexample {bad[0]}"))
    print(f"\n  random-integer trials failing: {fails}/12")

    print()
    print("=" * 74)
    print("PART 3 - is integrality of c_k necessary? (try a half-integer c_1)")
    print("=" * 74)
    c = [0] + [Fraction(1, 2)] + [1] * (N - 1)
    try:
        a = egf_exp_coeffs(c, N)
        bad = check_gauss(a)
        print(f"  c_1=1/2: terms integral, congruence {'holds' if not bad else 'FAILS'}")
    except AssertionError as e:
        print(f"  c_1=1/2 -> sequence is not integral ({e}); integrality of c_k matters")

    print()
    print("=" * 74)
    print("PART 4 - stronger form: does the period divide k exactly, i.e. is")
    print("         a(n) mod k a function of n mod k?  (equivalent to Part 1)")
    print("=" * 74)
    a = seqs["A000262 c_k=1        exp(x/(1-x))"]
    for k in (2, 3, 4, 5, 6, 7, 8, 9, 10, 12):
        residues = {}
        ok = True
        for n in range(0, len(a)):
            r = n % k
            v = a[n] % k
            if r in residues and residues[r] != v:
                ok = False
                break
            residues[r] = v
        print(f"  k={k:3d}  a(n) mod k depends only on n mod k: {ok}   "
              f"residues={[residues.get(i) for i in range(min(k, 8))]}")


if __name__ == "__main__":
    main()
