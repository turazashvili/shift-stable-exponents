# Shift-stable exponents and congruences for exponential generating functions

A machine-checked proof, in **Lean 4 + Mathlib**, of a family of congruences for
sequences defined by exponential generating functions of the form

$$b(n) \;=\; n!\,[x^n]\Big(F(x)^{A(n)}\exp\big(x\,G(x)^{M(n)}\big)\Big).$$

The main theorem resolves four conjectures of **Peter Bala** recorded in the
[OEIS](https://oeis.org) in March 2023, on two independent axes, and subsumes his 2017
theorem as the case of constant exponents.

---

## The result

> **Theorem.** Let $F,G\in\mathbb{Z}[[x]]$ with $F(0)=G(0)=1$, and let
> $A,M:\mathbb{N}\to\mathbb{N}$ be *shift-stable*, meaning
> $A(m+k)\equiv A(m) \pmod{k}$ for all $m,k$ (every polynomial with
> natural-number coefficients qualifies). Put
> $$b(n)=n!\,[x^n]\big(F(x)^{A(n)}\exp(x\,G(x)^{M(n)})\big).$$
> Then $b(n)\in\mathbb{Z}$ and $b(n+k)\equiv b(n)\pmod{k}$ for all $n,k\ge 1$.

Equivalently: for every $k$, the sequence $b \bmod k$ is purely periodic with period
dividing $k$.

### Cases covered

| $A(n)$ | $M(n)$ | statement | status before this work |
|---|---|---|---|
| const | const | Bala's 2017 theorem | proved by Bala (2017) |
| $n$ | $n$ | conjecture on [A361036](https://oeis.org/A361036) | **open since Mar 2023** |
| $0$ | $n$ | conjectures on [A293013](https://oeis.org/A293013), [A361281](https://oeis.org/A361281) | **open since Mar 2023** |
| $n$ | $1$ | general conjecture on [A278070](https://oeis.org/A278070) | **open** (only the single-sequence case was known) |
| $n^2$ | $n$ | quadratic exponents | not previously posed |

The A361036 and A278070 axes are genuinely different — one puts $n$ inside the
exponential, the other only in the prefactor — and neither is a special case of the
other. They unify because the proof only ever needs the two exponents to be
shift-stable.

---

## Proof sketch

Expanding $\exp(xG^M)=\sum_j x^jG^{Mj}/j!$ and reindexing $i=n-j$ gives the finite
closed form

$$b(n)=\sum_{i\ge 0}(n)_i\,[x^i]\Big(F^{A(n)}G^{M(n)(n-i)}\Big),\qquad (n)_i=\frac{n!}{(n-i)!}.$$

Writing $F=1+P$, $G=1+Q$ with $P(0)=Q(0)=0$, the Newton expansion
$[x^i]\big((1+P)^{A}Z\big)=\sum_{r\le i}[x^i](P^rZ)\binom{A}{r}$ turns each block into
an integer combination of binomial coefficients in the exponents. Then telescoping
$X'Y'Z'-XYZ=(X'-X)Y'Z'+X(Y'-Y)Z'+XY(Z'-Z)$ reduces everything to two facts:

1. a falling factorial is an integer polynomial, so it maps congruent arguments to
   congruent values;
2. $r!\mid (n)_i$ whenever $r\le i$, and $r!\big(\binom{A'}{r}-\binom{A}{r}\big)=(A')_r-(A)_r$,
   so the spare divisibility in $(n)_i$ absorbs the denominators exactly.

The two uses of $r\le i$ and $s\le i$ are independent; one never needs $r!\,s!\mid i!$.

---

## Repository layout

```
ShiftStableExponents.lean          root module
ShiftStableExponents/Basic.lean    the full development (no `sorry`, no `sorryAx`)
test/Axioms.lean              prints axiom dependencies of every main theorem
paper/paper.tex               LaTeX source of the accompanying paper
verification/                 independent numerical checks (exact integer arithmetic)
mining/                       the OEIS scanning pipeline that found the conjecture
docs/                         research log, instance triage
```

### Lean development

| declaration | content |
|---|---|
| `bala` | $b(n)$, defined directly from `PowerSeries.exp` and `PowerSeries.subst` |
| `bala_eq_Bint` | the generating-function bridge: `bala = Bint`, an explicit integer sum |
| `coeff_one_add_pow_mul` | Newton expansion of $[x^i]((1+P)^A Z)$ |
| `ShiftStable` | the hypothesis on exponents, with closure under `+` and `*` |
| `Bint_shift` | the congruence for the explicit sum |
| `bala_congruence` | **main theorem**, end to end |
| `bala_congruence_A361036`, `bala_congruence_A278070`, `bala_congruence_sq` | named corollaries |

Nothing is assumed: `bala` is defined from Mathlib's `exp` and `subst`, and every step
from that definition to the congruence is machine-checked.

---

## Reviewing this work

If you are checking the claims rather than using them, start with
**[`REVIEWING.md`](REVIEWING.md)**. It is a levelled guide: two minutes to read the one
definition that human judgement cannot be removed from, five minutes for the numerics,
under an hour for the full machine check, then how to try to break it and how to check the
result is not already known. It also lists the known weak points and what would falsify
each claim.

## Building

Requires [`elan`](https://github.com/leanprover/elan). The toolchain is pinned in
`lean-toolchain` and Mathlib in `lakefile.toml`.

```bash
lake exe cache get     # download prebuilt Mathlib oleans (a few GB)
lake build             # build the library
lake env lean test/Axioms.lean
```

To build the paper:

```bash
cd paper && pdflatex paper.tex && pdflatex paper.tex
```

`test/Axioms.lean` should print, for each of the six main theorems, exactly

```
[propext, Classical.choice, Quot.sound]
```

i.e. Mathlib's three standard axioms and **no `sorryAx`**.

---

## Numerical verification

The `verification/` scripts are independent of the Lean development and use exact
integer/rational arithmetic throughout (never floating point).

```bash
python3 verification/verify_proof.py        # each proof step, incl. 46,200 termwise cases
python3 verification/check_faithful.py      # Lean's definitions vs. the real OEIS terms
python3 verification/test_unified.py        # the unified statement across 8 exponent pairs
python3 verification/check_sharpness.py     # the necessary condition on F(0), G(0)
```

Summary of what they establish:

* the closed form agrees with the definition of $b$ on all tested $(F,G,A,M)$;
* the Lean definitions reproduce the stored OEIS terms of A278070, A293013, A361281 and
  A361036 to nine terms each;
* the congruence holds in 200/200 randomized trials and in a hostile search over
  460,812 $(n,k)$ pairs up to $n+k\le 140$;
* shift-stability of the exponents is **necessary**: non-polynomial exponents such as
  $2^n$ and $n!$ fail in 6/6 trials;
* the hypothesis $F(0)=G(0)=1$ can be weakened to $F(0)G(0)=1$ (see
  `docs/FINDINGS.md`), and beyond that the congruence fails.

---

## Provenance and credit

The conjectures are **Peter Bala's**, posted as OEIS comments in March 2023; the
constant-exponent case is his 2017 theorem,
*[Integer sequences that become periodic on reduction modulo k for all k](https://oeis.org/A047974/a047974_1.pdf)*,
whose closing question this work answers. This repository contributes the proof and its
formalization, not the statements.

The property $\,(a-b)\mid f(a)-f(b)\,$ studied here is known in the literature as having
**integral difference ratios**, and is completely characterized by Cégielski,
Grigorieff and Guessarian (*Int. J. Number Theory* **11** (2015),
[arXiv:1310.1507](https://arxiv.org/abs/1310.1507)) in terms of Newton coefficients.
That literature and the OEIS one appear to have been disconnected; see the paper's
discussion of why their criterion does not directly settle the present case.

The conjecture was located by an automated scan of all 398,442 OEIS sequences
(`mining/`), which was in turn motivated by the reported hit rates in
Tsoukalas et al., *Advancing Mathematics Research with AI-Driven Formal Proof Search*
([arXiv:2605.22763](https://arxiv.org/abs/2605.22763)).

## License

Apache License 2.0 — see [`LICENSE`](LICENSE). Consistent with Mathlib's license.
