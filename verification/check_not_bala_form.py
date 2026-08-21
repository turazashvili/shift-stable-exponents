#!/usr/bin/env python3
"""
Certifies Proposition "A293013 is not of Bala's 2017 form" (Section 7.3 of the paper).

Obstruction (Lemma in the paper). If b(0) = 1 and

    B(x) = sum_n b(n) x^n / n!  =  Fhat(x) * exp(x * Ghat(x))

for some Fhat, Ghat in Z[[x]], then Fhat(0) = B(0) = 1, so Fhat is a unit in Z[[x]],
and

    B'/B  =  Fhat'/Fhat + Ghat + x*Ghat'   in   Z[[x]].

So exhibiting a single non-integer coefficient of B'/B proves that B is NOT of Bala's
form. The obstruction is one-way: integrality of B'/B is necessary, not sufficient.

This script
  (1) computes A293013 exactly and checks it against the terms stored in the OEIS,
  (2) exhibits the first non-integer coefficient of B'/B,
  (3) sanity-checks that a genuine Bala-form EGF passes the test (so the test is not
      vacuously failing everything).

Usage:
    python3 verification/check_not_bala_form.py
"""

from fractions import Fraction as Fr
from math import factorial

N = 14

# OEIS A293013, a(n) = n! * [x^n] exp(x/(1-x)^n)
A293013 = [1, 1, 5, 55, 961, 24101, 818821, 36053515, 1984670465, 132825475081]


def mul(a, b, M):
    r = [Fr(0)] * (M + 1)
    for i, x in enumerate(a):
        if x == 0 or i > M:
            continue
        for j, y in enumerate(b[: M - i + 1]):
            if y:
                r[i + j] += x * y
    return r


def power(a, e, M):
    r = [Fr(1)] + [Fr(0)] * M
    base = a[: M + 1] + [Fr(0)] * max(0, M + 1 - len(a))
    while e:
        if e & 1:
            r = mul(r, base, M)
        e >>= 1
        if e:
            base = mul(base, base, M)
    return r


def inv(a, M):
    assert a[0] != 0
    r = [Fr(0)] * (M + 1)
    r[0] = 1 / a[0]
    for m in range(1, M + 1):
        s = sum(a[i] * r[m - i] for i in range(1, m + 1))
        r[m] = -s / a[0]
    return r


def deriv(a, M):
    return [(i + 1) * a[i + 1] for i in range(M)] + [Fr(0)]


def ff(n, i):
    p = 1
    for t in range(i):
        p *= n - t
    return p


def b_closed(W, F, G, A, M, NM):
    """b(n) = sum_i (n)_i [x^i](W F^{A(n)} G^{M(n)(n-i)}), exact."""
    out = []
    for n in range(NM + 1):
        K = n
        base = mul(W[: K + 1] + [Fr(0)] * (K + 1), power(F, A(n), K), K)
        H = power(G, M(n), K)
        Hj = [Fr(1)] + [Fr(0)] * K
        tot = Fr(0)
        for j in range(n + 1):
            tot += ff(n, n - j) * mul(base, Hj, K)[n - j]
            if j < n:
                Hj = mul(Hj, H, K)
        out.append(tot)
    return out


def log_deriv_of_egf(b, M):
    """B = sum b(n)x^n/n!  ->  B'/B"""
    B = [Fr(b[n], factorial(n)) for n in range(M + 1)]
    return mul(deriv(B, M), inv(B, M), M)


def main():
    one = [Fr(1)] + [Fr(0)] * N
    geo = [Fr(1)] * (N + 1)  # 1/(1-x)

    print("=" * 78)
    print("A293013 is not of Bala's 2017 form  (paper, Section 7.3)")
    print("=" * 78)

    b = b_closed(one, one, geo, lambda n: 0, lambda n: n, N)
    bi = [int(x) for x in b]
    print(f"  computed b(0..9) : {bi[:10]}")
    print(f"  OEIS   A293013   : {A293013}")
    ok_terms = bi[: len(A293013)] == A293013
    print(f"  MATCH: {ok_terms}")
    assert ok_terms, "computed sequence does not match OEIS A293013"

    Q = log_deriv_of_egf(b, N)
    print()
    print("  B'/B coefficients:")
    first_bad = None
    for m in range(11):
        c = Q[m]
        isint = c.denominator == 1
        mark = "" if isint else "   <-- NOT an integer"
        print(f"    [x^{m:>2}] = {str(c):>20}{mark}")
        if not isint and first_bad is None:
            first_bad = (m, c)

    print()
    assert first_bad is not None, "no obstruction found -- proposition NOT certified"
    m, c = first_bad
    print(f"  first non-integer: [x^{m}](B'/B) = {c}")
    print("  => B admits no representation Fhat*exp(x*Ghat) with Fhat,Ghat in Z[[x]].")

    print()
    print("=" * 78)
    print("sanity: a genuine Bala-form EGF must PASS the integrality test")
    print("=" * 78)
    # B = 1/(1-x) * exp(x(1+x))
    Fh = geo
    xG = [Fr(0), Fr(1), Fr(1)] + [Fr(0)] * (N - 2)
    E = [Fr(0)] * (N + 1)
    E[0] = Fr(1)
    term = [Fr(0)] * (N + 1)
    term[0] = Fr(1)
    for j in range(1, N + 1):
        term = mul(term, xG, N)
        for i in range(N + 1):
            E[i] += term[i] / factorial(j)
    B2 = mul(Fh, E, N)
    Q2 = mul(deriv(B2, N), inv(B2, N), N)
    allint = all(Q2[m].denominator == 1 for m in range(11))
    print(f"  F=1/(1-x), G=1+x:  B'/B integral on [x^0..x^10]? {allint}")
    print(f"  first coefficients: {[str(Q2[m]) for m in range(6)]}")
    assert allint, "sanity check failed -- the test rejects a genuine Bala-form series"

    print()
    print("CERTIFIED: the obstruction holds for A293013 and does not fire spuriously.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
