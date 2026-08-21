#!/usr/bin/env python3
"""
Checks every numeric example quoted in paper/paper.tex.

The point of this script is that no figure in the paper should rest on a
computation nobody re-ran. Each assertion below names the section of the paper
it certifies. If the paper is edited and a number changes, this fails.

Usage:
    python3 verification/check_paper_claims.py
"""

from fractions import Fraction as Fr
from math import factorial

N = 14


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
    r = [Fr(0)] * (M + 1)
    r[0] = 1 / a[0]
    for m in range(1, M + 1):
        r[m] = -sum(a[i] * r[m - i] for i in range(1, m + 1)) / a[0]
    return r


def ff(n, i):
    p = 1
    for t in range(i):
        p *= n - t
    return p


def b_closed(W, F, G, A, M, NM):
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


def pad(c, M=N):
    return [Fr(x) for x in c] + [Fr(0)] * (M + 1)


def log_deriv_of_egf(b, M):
    """B = sum b(n) x^n / n!  ->  B'/B, exactly."""
    B = [Fr(b[n], factorial(n)) for n in range(M + 1)]
    Bp = [(i + 1) * B[i + 1] for i in range(M)] + [Fr(0)]
    return mul(Bp, inv(B, M), M)


CHECKS = []


def check(section, desc, got, want):
    ok = got == want
    CHECKS.append((ok, section, desc, got, want))
    return ok


def main():
    one, geo = pad([1]), pad([1] * (N + 1))

    # ---- Section 5, Example: A361036 with F = G = 1+x -------------------
    b = b_closed(one, pad([1, 1]), pad([1, 1]), lambda n: n, lambda n: n, 9)
    bi = [int(x) for x in b]
    check("Sec 5 Example", "A361036 first nine terms", bi[:9],
          [1, 2, 11, 124, 2225, 56546, 1928707, 85029596, 4687436609])
    check("Sec 5 Example", "A361036 mod 7, nine terms", [x % 7 for x in bi[:9]],
          [1, 2, 4, 5, 6, 0, 4, 1, 2])

    # ---- Section 6.1: shift-stability cannot be dropped -----------------
    b = b_closed(one, pad([1, 1]), one, lambda n: 2 ** n, lambda n: 1, 6)
    bi = [int(x) for x in b]
    check("Sec 6.1", "A(n)=2^n sequence", bi[:6],
          [1, 3, 21, 529, 58625, 28788001])
    check("Sec 6.1", "b(4)-b(1) = 58622", bi[4] - bi[1], 58622)
    check("Sec 6.1", "58622 mod 3 = 2", (bi[4] - bi[1]) % 3, 2)

    # not necessary instance-by-instance: F = 1 lets any A through
    for name, A in (("2^n", lambda n: 2 ** n), ("n!", lambda n: factorial(n))):
        bb = [int(x) for x in b_closed(one, one, pad([1, 1]), A, lambda n: 1, 11)]
        viol = [(n, k) for n in range(12) for k in range(1, 12 - n)
                if (bb[n + k] - bb[n]) % k != 0]
        check("Sec 6.1", f"F=1 with A(n)={name}: no violations", len(viol), 0)

    # ---- Section 6.2: F0*G0 = 1 necessary, not sufficient ---------------
    b = b_closed(one, pad([-1, 1]), pad([-1]), lambda n: n, lambda n: n, 6)
    bi = [int(x) for x in b]
    check("Sec 6.2", "F=-1+x, G=-1 sequence", bi[:6], [1, 2, -1, 34, -15, 1546])
    check("Sec 6.2", "b(4)-b(1) = -17", bi[4] - bi[1], -17)
    check("Sec 6.2", "-17 not divisible by 3", (bi[4] - bi[1]) % 3 != 0, True)

    # outside product-one it fails: F = 2, G = 1  ->  b(n) = 2^n
    b = b_closed(one, pad([2]), one, lambda n: n, lambda n: 1, 4)
    bi = [int(x) for x in b]
    check("Sec 6.2", "F=2,G=1 gives 2^n", bi[:4], [1, 2, 4, 8])
    check("Sec 6.2", "b(3)-b(0) = 7", bi[3] - bi[0], 7)

    # the even (-1,-1) branch really does survive, and equals the positive one
    Fn, Gn = pad([-1, 0, -3]), pad([-1, 0, 5])
    Fp, Gp = pad([1, 0, 3]), pad([1, 0, -5])
    bn = b_closed(one, Fn, Gn, lambda n: n, lambda n: n, 10)
    bp = b_closed(one, Fp, Gp, lambda n: n, lambda n: n, 10)
    check("Sec 6.2", "even branch: b_{F,G} = b_{Ftilde,Gtilde}", bn, bp)
    viol = [(n, k) for n in range(11) for k in range(1, 11 - n)
            if (bn[n + k] - bn[n]) % k != 0]
    check("Sec 6.2", "even branch: no violations", len(viol), 0)

    # A=0 slice: constraint is G0=1, F unconstrained (NOT W(0)G0=1)
    surviving = []
    for F0 in range(-2, 3):
        for G0 in range(-2, 3):
            bb = b_closed(pad([2]), pad([F0, 1]), pad([G0, 1]),
                          lambda n: 0, lambda n: n, 9)
            if all((bb[n + k] - bb[n]) % k == 0
                   for n in range(10) for k in range(1, 10 - n)):
                surviving.append((F0, G0))
    check("Sec 6.2", "A=0 slice: G0 always 1",
          sorted({g for _, g in surviving}), [1])
    check("Sec 6.2", "A=0 slice: F0 unconstrained",
          sorted({f for f, _ in surviving}), [-2, -1, 0, 1, 2])

    # ---- Section 7.3: A293013 outside Bala's 2017 form ------------------
    b = b_closed(one, one, geo, lambda n: 0, lambda n: n, N)
    bi = [int(x) for x in b]
    check("Sec 7.3", "A293013 first seven terms", bi[:7],
          [1, 1, 5, 55, 961, 24101, 818821])
    B = [Fr(bi[n], factorial(n)) for n in range(N + 1)]
    Bp = [(i + 1) * B[i + 1] for i in range(N)] + [Fr(0)]
    Q = mul(Bp, inv(B, N), N)
    check("Sec 7.3", "B'/B low coefficients", [str(Q[m]) for m in range(6)],
          ["1", "4", "21", "120", "755", "5215"])
    check("Sec 7.3", "[x^6](B'/B) = 117271/3", Q[6], Fr(117271, 3))
    check("Sec 7.3", "[x^6](B'/B) not an integer", Q[6].denominator != 1, True)

    # ---- Section 8: A000085 and the localization question ---------------
    G2 = [Fr(1), Fr(1, 2)] + [Fr(0)] * (N + 1)
    a = b_closed(one, one, G2, lambda n: 1, lambda n: 1, 9)
    check("Sec 8", "A000085 terms", [str(x) for x in a[:9]],
          ["1", "1", "2", "4", "10", "26", "76", "232", "764"])
    check("Sec 8", "A000085 integral", all(x.denominator == 1 for x in a), True)
    check("Sec 8", "a(2)-a(0) not divisible by 2", int(a[2] - a[0]) % 2 != 0, True)

    G3 = [Fr(1), Fr(1, 3)] + [Fr(0)] * (N + 1)
    c = b_closed(one, one, G3, lambda n: 1, lambda n: 1, 9)
    check("Sec 8", "G=1+x/3 gives b(2) = 5/3", c[2], Fr(5, 3))
    check("Sec 8", "b(2)-b(0) = 2/3", c[2] - c[0], Fr(2, 3))
    check("Sec 8", "(b(2)-b(0))/2 = 1/3", (c[2] - c[0]) / 2, Fr(1, 3))
    q = (c[2] - c[0]) / 2
    t = q.denominator
    while t % 3 == 0:
        t //= 3
    check("Sec 8", "1/3 lies in Z[1/3]", t == 1, True)

    # ---- Section 7.4: Bala base case ------------------------------------
    # b(k) = b(0) = W(0) mod k.  NOT necessarily 1 unless W(0) = 1.
    for W0 in (1, 7, -3):
        bb = b_closed(pad([W0]), pad([1, 1]), pad([1, 1]),
                      lambda n: 3, lambda n: 5, 9)
        bi = [int(x) for x in bb]
        check("Sec 7.4", f"W(0)={W0}: b(0)=W(0)", bi[0], W0)
        check("Sec 7.4", f"W(0)={W0}: b(k)=b(0) mod k for k=2..7",
              all((bi[k] - bi[0]) % k == 0 for k in range(2, 8)), True)
    # and the point of the correction: b(k) is NOT 1 mod k when W(0) != 1
    bb = [int(x) for x in b_closed(pad([7]), pad([1, 1]), pad([1, 1]),
                                   lambda n: 3, lambda n: 5, 9)]
    check("Sec 7.4", "W(0)=7: b(4) mod 4 = 3, not 1", bb[4] % 4, 3)

    # ---- Section 7.3: obstruction fires for A361036, not for A278070 -----
    b361036 = b_closed(one, pad([1, 1]), pad([1, 1]), lambda n: n, lambda n: n, N)
    Q1 = log_deriv_of_egf([int(x) for x in b361036], N)
    check("Sec 7.3", "A361036: [x^4](B'/B) = 2777/2", Q1[4], Fr(2777, 2))
    b278070 = b_closed(one, geo, one, lambda n: n, lambda n: 1, N)
    check("Sec 7.3", "A278070 terms", [int(x) for x in b278070[:8]],
          [1, 2, 11, 106, 1457, 25946, 566827, 14665106])
    Q2 = log_deriv_of_egf([int(x) for x in b278070], N)
    check("Sec 7.3", "A278070: B'/B integral on [x^0..x^10] (obstruction does NOT fire)",
          all(Q2[m].denominator == 1 for m in range(11)), True)

    # ---- Section 8: localization holds for EVERY k ------------------------
    def divisible_in_ZD(d, k, D):
        q = d / k
        t = q.denominator
        for pr in (2, 3, 5, 7, 11, 13):
            if D % pr == 0:
                while t % pr == 0:
                    t //= pr
        return t == 1

    # A000085 via G = 1 + x/2 : odd k holds, even k fails
    G2 = [Fr(1), Fr(1, 2)] + [Fr(0)] * (N + 1)
    a85 = b_closed(one, one, G2, lambda n: 1, lambda n: 1, 11)
    check("Sec 8", "A000085: odd-k congruence holds",
          [(n, k) for n in range(12) for k in range(1, 12 - n)
           if k % 2 == 1 and int(a85[n + k] - a85[n]) % k != 0], [])
    check("Sec 8", "A000085: coprimality is necessary (a(2)-a(0) not div by 2)",
          int(a85[2] - a85[0]) % 2 != 0, True)
    # G = 1 + x/3 : holds in Z[1/3] for EVERY k, including k=2
    G3 = [Fr(1), Fr(1, 3)] + [Fr(0)] * (N + 1)
    a3 = b_closed(one, one, G3, lambda n: 1, lambda n: 1, 11)
    check("Sec 8", "G=1+x/3: holds in Z[1/3] for every k (no coprimality)",
          [(n, k) for n in range(12) for k in range(1, 12 - n)
           if not divisible_in_ZD(a3[n + k] - a3[n], k, 3)], [])

    # ---- report ---------------------------------------------------------
    print("=" * 78)
    print("NUMERIC CLAIMS IN paper/paper.tex")
    print("=" * 78)
    width = max(len(d) for _, _, d, _, _ in CHECKS)
    bad = 0
    for ok, sec, desc, got, want in CHECKS:
        if ok:
            print(f"  [ok]   {sec:<14} {desc}")
        else:
            bad += 1
            print(f"  [FAIL] {sec:<14} {desc}")
            print(f"         got  = {got}")
            print(f"         want = {want}")
    print("=" * 78)
    print(f"  {len(CHECKS) - bad}/{len(CHECKS)} claims verified")
    print("=" * 78)
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
