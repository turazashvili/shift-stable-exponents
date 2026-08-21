#!/usr/bin/env python3
"""
FAITHFULNESS CHECK — does the Lean development talk about the right objects?

This is the guard against misformalization, and it is the step a reviewer should care
about most, because everything else in the repository is machine-checked *given* the
definitions. Here we check the definitions themselves, from outside Lean.

The four Lean declarations transcribed below, verbatim from
`ShiftStableExponents/Basic.lean` (including `Nat.descFactorial` and ℕ *truncated* subtraction):

    def bala (W F G : ℚ⟦X⟧) (A M : ℕ → ℕ) (n : ℕ) : ℚ :=
      (Nat.factorial n : ℚ) * coeff n (W * F ^ A n * subst (X * G ^ M n) (exp ℚ))

    def Bint (W F G : ℤ⟦X⟧) (A M : ℕ → ℕ) (n : ℕ) : ℤ :=
      ∑ i ∈ range (n + 1),
        (n.descFactorial i : ℤ) * coeff i (W * F ^ A n * G ^ (M n * (n - i)))

    def Tint (W F G : ℤ⟦X⟧) (A M : ℕ → ℕ) (m i : ℕ) : ℤ :=
      (m.descFactorial i : ℤ) * coeff i (W * F ^ A m * G ^ (M m * (m - i)))

    def ShiftStable (A : ℕ → ℕ) : Prop :=
      ∀ m k : ℕ, (k : ℤ) ∣ ((A (m + k) : ℤ) - (A m : ℤ))

What is checked here:
  (1) `bala` = `Bint`  numerically — i.e. the Lean theorem `bala_eq_Bint` is not vacuous
      and the closed form really is the exponential-generating-function definition;
  (2) `Bint`, at the instances used by the four named corollaries, reproduces the terms
      OEIS actually stores for A278070, A293013, A361281, A361036;
  (3) `ShiftStable` holds for exactly the exponent functions the corollaries instantiate;
  (4) the proved congruence holds on those sequences.

Needs the OEIS dump at ./oeisdata (see mining/README.md). Exact arithmetic throughout.
"""

from fractions import Fraction
from math import factorial
import os
import re
import sys

DEG = 26


# ---------------------------------------------------------------- power series over Q/Z

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


def ser(c, deg):
    c = list(c[:deg + 1])
    return c + [0] * (deg + 1 - len(c))


# ---------------------------------------------------------------- Lean transcriptions

def descFactorial(m, i):
    """Nat.descFactorial m i — zero as soon as a factor hits 0, as in Lean/ℕ."""
    r = 1
    for t in range(i):
        r *= (m - t) if m - t > 0 else 0
    return r


def natsub(a, b):
    """ℕ truncated subtraction, exactly as Lean's `a - b` on ℕ."""
    return a - b if a >= b else 0


def bala(W, F, G, A, M, n):
    """n! * [x^n]( W * F^A(n) * exp(x * G^M(n)) ), from the definition (via exp series)."""
    deg = n
    GM = powr(G, M(n), deg)
    xGM = [0] + GM[:deg]
    E = [Fraction(0)] * (deg + 1)
    E[0] = Fraction(1)
    for m in range(deg):
        acc = Fraction(0)
        for k in range(1, m + 2):
            if k <= deg and xGM[k]:
                acc += Fraction(k) * Fraction(xGM[k]) * E[m + 1 - k]
        E[m + 1] = acc / Fraction(m + 1)
    pre = mul(W, powr(F, A(n), deg), deg)
    tot = Fraction(0)
    for j in range(deg + 1):
        if pre[j]:
            tot += Fraction(pre[j]) * E[deg - j]
    v = tot * factorial(n)
    return v


def Tint(W, F, G, A, M, m, i):
    d = descFactorial(m, i)
    if d == 0:
        return 0
    S = mul(mul(W, powr(F, A(m), i), i), powr(G, M(m) * natsub(m, i), i), i)
    return d * S[i]


def Bint(W, F, G, A, M, n):
    return sum(Tint(W, F, G, A, M, n, i) for i in range(n + 1))


def shift_stable(A, mmax=40, kmax=25):
    """Check ShiftStable A on a range; returns list of counterexamples."""
    return [(m, k) for m in range(mmax) for k in range(1, kmax)
            if (A(m + k) - A(m)) % k != 0]


# ---------------------------------------------------------------- OEIS terms

def oeis_terms(anum, root="oeisdata"):
    p = os.path.join(root, "seq", anum[:4], anum + ".seq")
    if not os.path.exists(p):
        return None
    raw = ""
    with open(p, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            m = re.match(r"^%([STU])\s+A\d{6}\s?(.*)$", line.rstrip("\n"))
            if m:
                raw += m.group(2)
    return [int(t) for t in raw.split(",") if t.strip()]


# ---------------------------------------------------------------- the four corollaries

one = ser([1], DEG)
onep = ser([1, 1], DEG)          # 1 + x
inv = ser([1] * (DEG + 1), DEG)  # 1/(1 - x)

ID = lambda n: n
ZERO = lambda n: 0
ONE = lambda n: 1

CASES = [
    # (OEIS id, Lean corollary, W, F, G, A, M)
    ("A278070", "bala_congruence_A278070", one, inv, one, ID, ONE),
    ("A293013", "bala_congruence_A293013", one, one, inv, ZERO, ID),
    ("A361281", "bala_congruence_A361281", one, one, onep, ZERO, ID),
    ("A361036", "bala_congruence_A361036", one, onep, onep, ID, ID),
]


def main():
    if not os.path.isdir("oeisdata"):
        print("oeisdata/ not found. From the repository root:\n"
              "    git clone --depth 1 https://github.com/oeis/oeisdata.git\n"
              "See mining/README.md.", file=sys.stderr)
        return 1

    ok = True

    print("=" * 78)
    print("(1) `bala` == `Bint`  (the Lean theorem bala_eq_Bint, checked numerically)")
    print("=" * 78)
    for anum, cor, W, F, G, A, M in CASES:
        lhs = [bala(W, F, G, A, M, n) for n in range(15)]
        rhs = [Bint(W, F, G, A, M, n) for n in range(15)]
        integral = all(v.denominator == 1 for v in lhs)
        same = [int(v) for v in lhs] == rhs
        ok &= integral and same
        print(f"  {anum}: bala integral: {integral}   bala == Bint: {same}")

    print()
    print("=" * 78)
    print("(2) `Bint` reproduces the terms OEIS actually stores")
    print("=" * 78)
    for anum, cor, W, F, G, A, M in CASES:
        mine = [Bint(W, F, G, A, M, n) for n in range(9)]
        oe = (oeis_terms(anum) or [])[:9]
        match = mine == oe
        ok &= match
        print(f"  {anum}  (Lean: {cor})")
        print(f"      Bint = {mine}")
        print(f"      OEIS = {oe}")
        print(f"      match: {match}")

    print()
    print("=" * 78)
    print("(3) `ShiftStable` holds for exactly the exponents the corollaries use")
    print("=" * 78)
    for label, fn in [("fun n => n            (ShiftStable.id)", ID),
                      ("fun _ => 0            (ShiftStable.const)", ZERO),
                      ("fun _ => 1            (ShiftStable.const)", ONE),
                      ("fun n => n * n        (ShiftStable.mul)", lambda n: n * n)]:
        bad = shift_stable(fn)
        ok &= not bad
        print(f"  {label}  counterexamples: {len(bad)}")
    print("  controls (should FAIL, and the theorem correctly excludes them):")
    for label, fn in [("fun n => 2 ^ n", lambda n: 2 ** n),
                      ("fun n => n !  ", lambda n: factorial(min(n, 8)))]:
        bad = shift_stable(fn, mmax=12, kmax=10)
        print(f"    {label}  counterexamples: {len(bad)}  "
              f"{'(good - not shift-stable)' if bad else '*** UNEXPECTED ***'}")
        ok &= bool(bad)

    print()
    print("=" * 78)
    print("(4) the proved congruence, on the real sequences")
    print("=" * 78)
    tested = viol = 0
    for anum, cor, W, F, G, A, M in CASES:
        a = [Bint(W, F, G, A, M, n) for n in range(19)]
        bad = 0
        for k in range(1, 10):
            for n in range(0, 19 - k):
                tested += 1
                if (a[n + k] - a[n]) % k != 0:
                    bad += 1
                    viol += 1
        print(f"  {anum}: violations {bad}")
    ok &= viol == 0
    print(f"\n  total: {tested} (n,k) pairs, {viol} violations")

    print()
    print("=" * 78)
    print("FAITHFUL — the Lean definitions compute Bala's b(n) and match OEIS."
          if ok else
          "PROBLEM — a check failed; the Lean statement may not mean what is claimed.")
    print("=" * 78)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
