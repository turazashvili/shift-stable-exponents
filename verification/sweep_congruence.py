#!/usr/bin/env python3
"""
Hostile sweep of the shift-congruence property

    b(n+k) == b(n)  (mod k)

for b(n) = n! [x^n]( W F^{A(n)} exp(x G^{M(n)}) ), over structured and randomised
choices of (W, F, G, A, M), using exact integer arithmetic only (never floating
point).

This script exists so that every (n,k)-pair count quoted in README.md and in
paper/paper.tex is reproducible: it prints the exact number of pairs tested and
the exact number of violations. Do not quote a figure this script has not printed.

Method. From the closed form (Proposition 3 of the paper)

    b(n) = sum_{i=0..n} (n)_i [x^i]( W F^{A(n)} G^{M(n)(n-i)} ),

substitute j = n - i:

    b(n) = sum_{j=0..n} (n)_{n-j} [x^{n-j}]( W F^{A(n)} H^j ),   H = G^{M(n)}.

The powers H^j are then built incrementally (one truncated multiplication each)
instead of by repeated binary exponentiation, which is what makes a bound of
n+k <= 60 feasible in exact arithmetic.

Usage:
    python3 verification/sweep_congruence.py [BOUND] [CONFIGS]
"""

import random
import sys
from math import factorial, gcd

# --------------------------------------------------------------------------
# truncated integer power series, as coefficient lists of length N+1
# --------------------------------------------------------------------------


def mul(a, b, N):
    """(a*b) truncated to degree N."""
    r = [0] * (N + 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        if i > N:
            break
        # only j with i+j <= N contribute
        for j, y in enumerate(b[: N - i + 1]):
            if y:
                r[i + j] += x * y
    return r


def power(a, e, N):
    """a**e truncated to degree N, by binary exponentiation."""
    r = [1] + [0] * N
    base = a[: N + 1] + [0] * max(0, N + 1 - len(a))
    while e:
        if e & 1:
            r = mul(r, base, N)
        e >>= 1
        if e:
            base = mul(base, base, N)
    return r


def ff(n, i):
    """falling factorial (n)_i = n(n-1)...(n-i+1)."""
    p = 1
    for t in range(i):
        p *= n - t
    return p


def b_seq(W, F, G, A, M, NMAX):
    """b(0..NMAX) via the closed form, exact integers, incremental powers of H."""
    out = []
    for n in range(NMAX + 1):
        N = n
        base = mul(W[: N + 1] + [0] * (N + 1), power(F, A(n), N), N)
        H = power(G, M(n), N)
        Hj = [1] + [0] * N          # H^0
        tot = 0
        for j in range(n + 1):
            term = mul(base, Hj, N)
            tot += ff(n, n - j) * term[n - j]
            if j < n:
                Hj = mul(Hj, H, N)
        out.append(tot)
    return out


# --------------------------------------------------------------------------
# configurations
# --------------------------------------------------------------------------

EXPONENTS = [
    ("A=n,    M=n", lambda n: n, lambda n: n),
    ("A=n,    M=1", lambda n: n, lambda n: 1),
    ("A=0,    M=n", lambda n: 0, lambda n: n),
    ("A=1,    M=n", lambda n: 1, lambda n: n),
    ("A=n^2,  M=n", lambda n: n * n, lambda n: n),
    ("A=n,    M=n^2", lambda n: n, lambda n: n * n),
    ("A=3,    M=7", lambda n: 3, lambda n: 7),
    ("A=2n+4, M=n+1", lambda n: 2 * n + 4, lambda n: n + 1),
]


def pad(c, N):
    return list(c) + [0] * (N + 1)


def structured(N):
    """Structured (W,F,G) triples. F(0)=G(0)=1; W unconstrained."""
    return [
        ("W=1,      F=1+x,        G=1+x", [1], [1, 1], [1, 1]),
        ("W=1,      F=1/(1-x),    G=1+x", [1], [1] * (N + 1), [1, 1]),
        ("W=1,      F=1+x,        G=1/(1-x)", [1], [1, 1], [1] * (N + 1)),
        ("W=1,      F=1,          G=1/(1-x)", [1], [1], [1] * (N + 1)),
        ("W=1+2x,   F=1+x+x^2,    G=1+3x", [1, 2], [1, 1, 1], [1, 3]),
        ("W=-5+x^3, F=1-2x,       G=1+x+x^4", [-5, 0, 0, 1], [1, -2], [1, 1, 0, 0, 1]),
        ("W=7,      F=1+9x^2,     G=1-x", [7], [1, 0, 9], [1, -1]),
        ("W=1-x,    F=1-x-x^2,    G=1+2x-x^3", [1, -1], [1, -1, -1], [1, 2, 0, -1]),
    ]


def randomised(rng, N, count):
    out = []
    for t in range(count):
        wl = rng.randint(1, 4)
        W = [rng.randint(-9, 9) for _ in range(wl)]
        if all(c == 0 for c in W):
            W = [1]
        F = [1] + [rng.randint(-6, 6) for _ in range(rng.randint(1, 3))]
        G = [1] + [rng.randint(-6, 6) for _ in range(rng.randint(1, 3))]
        out.append((f"random #{t + 1}", W, F, G))
    return out


# --------------------------------------------------------------------------


def main():
    BOUND = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    NRAND = int(sys.argv[2]) if len(sys.argv) > 2 else 8

    rng = random.Random(20260821)
    N = BOUND

    configs = [(d, W, F, G) for d, W, F, G in structured(N)]
    configs += randomised(rng, N, NRAND)

    print("=" * 78)
    print(f"HOSTILE SWEEP of  b(n+k) == b(n) (mod k)   for  n+k <= {BOUND}")
    print("exact integer arithmetic; no floating point")
    print("=" * 78)
    print(f"  series triples : {len(configs)}")
    print(f"  exponent pairs : {len(EXPONENTS)}")
    print(f"  combinations   : {len(configs) * len(EXPONENTS)}")
    print()

    total_pairs = 0
    total_viol = 0
    violations = []

    for desc, W, F, G in configs:
        Wp, Fp, Gp = pad(W, N), pad(F, N), pad(G, N)
        row = []
        for ename, A, M in EXPONENTS:
            b = b_seq(Wp, Fp, Gp, A, M, BOUND)
            pairs = viol = 0
            for n in range(BOUND + 1):
                for k in range(1, BOUND + 1 - n):
                    pairs += 1
                    if (b[n + k] - b[n]) % k != 0:
                        viol += 1
                        if len(violations) < 20:
                            violations.append((desc, ename, n, k))
            total_pairs += pairs
            total_viol += viol
            row.append(viol)
        flag = "OK" if sum(row) == 0 else f"** {sum(row)} VIOLATIONS **"
        print(f"  {desc:<34} {flag}")

    print()
    print("=" * 78)
    print(f"  (n,k) pairs tested : {total_pairs:,}")
    print(f"  violations         : {total_viol:,}")
    print("=" * 78)
    if total_viol:
        print("VIOLATIONS FOUND — the congruence as stated is FALSE:")
        for v in violations:
            print("   ", v)
        return 1
    print(f"NO VIOLATIONS over {total_pairs:,} pairs (n+k <= {BOUND}).")
    print()
    print("Quote this figure and this bound, and nothing larger:")
    print(f"    {total_pairs:,} (n,k) pairs with n+k <= {BOUND}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
