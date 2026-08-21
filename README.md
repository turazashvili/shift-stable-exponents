# Shift-stable exponents and congruences for exponential generating functions

A machine-checked proof, in **Lean 4 + Mathlib**, of a family of congruences for
sequences defined by exponential generating functions of the form

$$b(n) \;=\; n!\,[x^n]\Big(W(x)\,F(x)^{A(n)}\exp\big(x\,G(x)^{M(n)}\big)\Big).$$

The main theorem resolves four conjectures of **Peter Bala** recorded in the
[OEIS](https://oeis.org) in March 2023, on two independent axes, and subsumes his 2017
theorem as the case of constant exponents.

---

## The result

> **Theorem.** Let $W,F,G\in\mathbb{Z}[[x]]$ with $F(0)=G(0)=1$ (*no condition on*
> $W$), and let $A,M:\mathbb{N}\to\mathbb{N}$ be *shift-stable*, meaning
> $A(m+k)\equiv A(m) \pmod{k}$ for all $m,k$ (every polynomial with
> natural-number coefficients qualifies). Put
> $$b(n)=n!\,[x^n]\big(W(x)\,F(x)^{A(n)}\exp(x\,G(x)^{M(n)})\big).$$
> Then $b(n)\in\mathbb{Z}$ and $b(n+k)\equiv b(n)\pmod{k}$ for all $n\ge 0$, $k\ge 1$.

Equivalently: for every $k$, the sequence $b \bmod k$ is purely periodic with period
dividing $k$.

The unconstrained prefactor $W$ is what makes the A361281 axis and Bala's 2017 theorem
instances of a single statement; it is present in the Lean theorem
(`bala_congruence`).

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

$$b(n)=\sum_{i\ge 0}(n)_i\,[x^i]\Big(W\,F^{A(n)}G^{M(n)(n-i)}\Big),\qquad (n)_i=\frac{n!}{(n-i)!}.$$

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
| `bala_congruence_A361036` | $A(n)=M(n)=n$ — A361036, general form |
| `bala_congruence_A278070` | $A(n)=n$, $M(n)=1$ — A278070, general form |
| `bala_congruence_A361281` | $A(n)=0$, $M(n)=n$, $W$ unconstrained — A361281, general form |
| `bala_congruence_A293013` | as above with $G=1/(1-x)$ — A293013 |
| `bala_congruence_sq` | $A(n)=n^2$, $M(n)=n$ — not previously posed |

These nine declarations are exactly the ones audited by `test/Axioms.lean`; CI enforces
that each depends on precisely `[propext, Classical.choice, Quot.sound]` and fails if any
declaration is dropped or any other axiom appears.

Nothing is assumed: `bala` is defined from Mathlib's `exp` and `subst`, and every step
from that definition to the congruence is machine-checked.

---

## The paper

The LaTeX source is [`paper/paper.tex`](paper/paper.tex). A built PDF is attached to the
[latest release](https://github.com/turazashvili/shift-stable-exponents/releases/latest),
and CI rebuilds it on every push (see the `paper` job) so the source is known to compile.

To build it yourself:

```bash
cd paper && pdflatex paper.tex && pdflatex paper.tex
```

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

`test/Axioms.lean` should print, for each of the nine theorems it audits, exactly

```
[propext, Classical.choice, Quot.sound]
```

i.e. Mathlib's three standard axioms and **no `sorryAx`**.

---

## Numerical verification

The `verification/` scripts are independent of the Lean development and use exact
integer/rational arithmetic throughout (never floating point).

```bash
python3 verification/verify_proof.py         # each proof step, incl. 46,200 termwise cases
python3 verification/check_faithful.py       # Lean's definitions vs. the real OEIS terms
python3 verification/test_unified.py         # the unified statement across 8 exponent pairs
python3 verification/sweep_congruence.py 100 8   # hostile (n,k) sweep -> the 646,400 figure
python3 verification/check_sharpness.py      # what the constant terms must satisfy
python3 verification/check_paper_claims.py   # every numeric example quoted in the paper
python3 verification/check_not_bala_form.py  # A293013 is outside Bala's 2017 form
python3 verification/probe_localization.py   # the Z[1/D] localization (Section 8)
```

Summary of what they establish:

* the closed form agrees with the definition of $b$ on all tested $(W,F,G,A,M)$;
* the Lean definitions reproduce the stored OEIS terms of A278070, A293013, A361281 and
  A361036 to nine terms each;
* the congruence holds in 200/200 randomized trials (`test_unified.py`), on 46,200
  termwise cases of the central identity (`verify_proof.py`), and over **646,400**
  $(n,k)$ pairs with $n+k\le 100$ across 128 combinations of $(W,F,G,A,M)$
  (`sweep_congruence.py`), with no exception;
* shift-stability of the exponents **cannot be dropped** from a uniform theorem:
  with $F=1+x$, exponents such as $A(n)=2^n$ and $A(n)=n!$ produce violations. It is
  not *necessary* in every instance — if $F=1$ the factor $F^{A(n)}$ is trivial and
  any $A$ whatsoever works;
* the constant terms cannot be relaxed freely. In the diagonal slice $W=1$,
  $A=M=\mathrm{id}$, the condition $F(0)G(0)=1$ is **necessary but not sufficient**:
  it also holds for $F(0)=G(0)=-1$, where the congruence survives when $-F$ and $-G$
  are *even* series. Evenness is a real constraint, not a convenience: in every case with
  an odd term that we tested (625 scanned) the congruence failed, e.g. $F=-1+x$, $G=-1$
  gives $b(4)-b(1)=-17\not\equiv0\bmod 3$. We have not proved that *every* odd term
  forces failure. `check_sharpness.py`
  exhibits both the surviving family and the failures;
* the family really does contain sequences outside Bala's 2017 form: for A293013 the
  logarithmic derivative $B'/B$ has $[x^6]=117271/3\notin\mathbb{Z}$, which is impossible
  for $\widehat F\exp(x\widehat G)$ with $\widehat F,\widehat G\in\mathbb{Z}[[x]]$
  (`check_not_bala_form.py`). The same test fires for A361036 at $[x^4]=2777/2$; it does
  *not* fire for A278070, which may itself be of Bala's form;
* the hypothesis $G\in\mathbb{Z}[[x]]$ can be dropped: the same proof runs over any
  commutative ring, so for $G\in\mathbb{Z}[1/D][[x]]$ one gets
  $b(n+k)-b(n)\in k\,\mathbb{Z}[1/D]$ for *every* $k$, and hence the ordinary congruence
  for every $k$ coprime to $D$ when $b$ is integral. This recovers the odd-$k$ congruence
  recorded on A000085 (`probe_localization.py`). These supplementary results are proved by
  hand, not in Lean;

Every figure quoted above is printed by the script named next to it. No number in this
README or in the paper is quoted unless a script in `verification/` produces it.

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
