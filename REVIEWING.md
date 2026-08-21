# How to review this repository

A guide for someone who wants to check the claims rather than take them on trust,
organized by how much effort each level costs. **Level 3 is the one that matters** — it is
where a machine, not a human, checks the mathematics.

If you only do one thing: do Level 0 (two minutes), because it is the only place where
human judgement is irreducible. The main theorem and its four OEIS corollaries downstream of
it are verified by Lean's kernel. The sharpness analysis (§6 of the paper), the non-Bala-form
proposition (§7.3) and the localization results (§8) are human proofs supported by the
Python checks in `verification/`; they are not in the Lean development.

---

## The claim being checked

> **Theorem.** Let $W,F,G\in\mathbb{Z}[[x]]$ with $F(0)=G(0)=1$ (no condition on $W$), and
> let $A,M:\mathbb{N}\to\mathbb{N}$ be *shift-stable* — meaning $k \mid A(m+k)-A(m)$ for
> all $m,k$. Then
> $$b(n) = n!\,[x^n]\big(W(x)\,F(x)^{A(n)}\exp(x\,G(x)^{M(n)})\big)$$
> is an integer and $b(n+k)\equiv b(n) \pmod k$ for all $n\ge0$, $k\ge1$.

This resolves conjectures of Peter Bala on OEIS A361036, A361281, A293013 and the general
conjecture on A278070. The statements are his; this repository contributes the proof.

---

## Level 0 — Read the definition (2 minutes, nothing to install)

**Why this matters most.** A formalization can only be as good as its statement. If the
Lean definition of $b(n)$ does not match what Bala wrote, then everything below verifies
the wrong theorem, and no amount of machine checking will catch it. So check the
definition by eye. It is two lines.

Open `ShiftStableExponents/Basic.lean` and find, near line 39:

```lean
def bala (W F G : ℚ⟦X⟧) (A M : ℕ → ℕ) (n : ℕ) : ℚ :=
  (Nat.factorial n : ℚ) * coeff n (W * F ^ A n * subst (X * G ^ M n) (exp ℚ))
```

Read it against Bala's own words, which you can see at
<https://oeis.org/A361036> (comment of 13 Mar 2023):

> *"let F(x) and G(x) denote power series with integer coefficients with F(0) = G(0) = 1.
> Define b(n) = n! \* [x^n] exp(x\*G(x)^n)\*F(x)^n."*

Three things to satisfy yourself about:

1. `exp ℚ` is Mathlib's genuine exponential power series
   ([`Mathlib/RingTheory/PowerSeries/Exp.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/RingTheory/PowerSeries/Exp.lean)),
   with `coeff n (exp A) = 1/n!`. It is not a bespoke definition.
2. `subst (X * G ^ M n) (exp ℚ)` is Mathlib's substitution, i.e. literally
   $\exp(x\,G(x)^{M(n)})$ — not a reformulation of it.
3. `coeff n` extracts the coefficient of $x^n$, and the whole thing is multiplied by $n!$.

Also glance at line 289:

```lean
def ShiftStable (A : ℕ → ℕ) : Prop :=
  ∀ m k : ℕ, (k : ℤ) ∣ ((A (m + k) : ℤ) - (A m : ℤ))
```

That is the hypothesis on the exponents, stated with no escape hatches.

**If both of those read correctly to you, the rest is mechanical.**

---

## Level 1 — Run the numerics (5 minutes, Python 3 only, no dependencies)

These are independent of Lean and use exact integer/rational arithmetic — never floating
point. An agreement is therefore exact over the range tested: not an approximation, but
not a proof of an identity beyond that range either. Each script exits non-zero if a
required check fails, so a green run means something.

```bash
python3 verification/verify_proof.py
python3 verification/check_sharpness.py
```

`verify_proof.py` checks each step of the argument separately. Expected, among other lines:

```
STEP 5 - TERMWISE shift-stability of eq (*) (the heart of the proof)
  termwise X'Y'Z' == XYZ mod k    tested 46200   violations: 0
```

`check_sharpness.py` establishes the *correct* condition on constant terms. In the
diagonal slice $W=1$, $A=M=\mathrm{id}$ it should report that $F=G=-1$ satisfies the
congruence, that a scan of $(F_0,G_0)\in[-3,3]^2$ finds it holding at exactly the two
points with $F_0G_0=1$, and — importantly — that $F_0G_0=1$ is **not sufficient**: its
`E1(c)` control block exhibits product-one pairs with an *odd* term that fail.

> **Note on two errors we made.** An earlier version of this repository claimed
> $F(0)=G(0)=1$ was *necessary*. That was false, found by adversarial review; $F_0G_0=1$
> is the necessary condition in that slice, and the $(-1,-1)$ branch is a nonempty
> infinite family. A later version then over-corrected, claiming $F(0)G(0)=1$ could simply
> *replace* $F(0)=G(0)=1$ — i.e. that it was sufficient. That is also false: sufficiency
> on the $(-1,-1)$ branch needs $-F$ and $-G$ to be **even**. Evenness is a real
> constraint, not a convenience — in every case with an odd term that we tested (625
> scanned) the congruence failed, e.g. $F=-1+x$, $G=-1$ gives
> $b(4)-b(1)=-17\not\equiv0 \bmod 3$ — though we have not proved that *every* odd term
> forces failure. The flawed
> test block inside `verify_proof.py` has been left in place and clearly labelled as
> flawed rather than deleted, so you can see what it actually measured. See
> `docs/RESEARCH-LOG.md` and Section 6.2 of the paper.

---

## Level 2 — Check we are talking about the right sequences (15 minutes, ~3 GB download)

The risk this addresses: the theorem could be true and formalized correctly, yet be about
different sequences than the OEIS entries we claim to resolve.

```bash
git clone --depth 1 https://github.com/oeis/oeisdata.git      # ~3 GB, 398k sequences
python3 verification/check_faithful.py
```

This transcribes the Lean definitions verbatim — *including* `Nat.descFactorial` and ℕ
truncated subtraction, which are easy to get wrong — and checks four things. It should end
with:

```
FAITHFUL — the Lean definitions compute Bala's b(n) and match OEIS.
```

and, in the body, that `Bint` reproduces the stored OEIS terms:

| sequence | first terms |
|---|---|
| A278070 | 1, 2, 11, 106, 1457, 25946, 566827, 14665106, 438351041 |
| A293013 | 1, 1, 5, 55, 961, 24101, 818821, 36053515, 1984670465 |
| A361281 | 1, 1, 5, 37, 481, 10001, 288901, 10820965, 511186817 |
| A361036 | 1, 2, 11, 124, 2225, 56546, 1928707, 85029596, 4687436609 |

Compare a couple of those against the sequence pages yourself, e.g.
<https://oeis.org/A361036>.

Then, for the unified statement across many exponent pairs:

```bash
python3 verification/test_unified.py
```

Expected: the closed form agrees with the definition on all eight `(A, M)` pairs, the
congruence holds 200/200 on random `(F,G)`, and non-polynomial exponents such as $2^n$ and
$n!$ **fail** 6/6 — confirming shift-stability is doing real work rather than being a
decoration.

---

## Level 3 — Verify the proof (30–60 minutes, mostly download)

This is the decisive step. Lean's kernel checks every inference; if it compiles and no
theorem depends on `sorryAx`, the mathematics is correct *given* the definitions you read
at Level 0.

```bash
# install elan (the Lean toolchain manager) if you don't have it
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o elan-init.sh
sh elan-init.sh -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"

lake exe cache get     # downloads prebuilt Mathlib (several GB) — the slow part
lake build             # should end: Build completed successfully
lake env lean test/Axioms.lean
```

The toolchain version is pinned in `lean-toolchain` and Mathlib is pinned in
`lake-manifest.json`, so you get the exact environment this was checked against.

`test/Axioms.lean` must print exactly this, nine times:

```
'ShiftStableExponents.bala_eq_Bint' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShiftStableExponents.coeff_one_add_pow_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShiftStableExponents.Bint_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShiftStableExponents.bala_congruence' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShiftStableExponents.bala_congruence_A361036' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShiftStableExponents.bala_congruence_A278070' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShiftStableExponents.bala_congruence_A361281' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShiftStableExponents.bala_congruence_A293013' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShiftStableExponents.bala_congruence_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**What to look for:** `propext`, `Classical.choice` and `Quot.sound` are Mathlib's three
standard axioms; essentially every Mathlib theorem depends on them. The thing that must
**not** appear is `sorryAx`, which is what a gap in a proof looks like. There is no
`sorryAx` anywhere.

Both this and Level 1 run automatically in CI (`.github/workflows/ci.yml`), and the CI
step fails the build if `sorryAx` ever appears.

---

## Level 4 — Try to break it

A good reviewer attacks rather than confirms. Concrete things to try:

**4a. Look for escape hatches in the source.**

```bash
grep -nE "sorry|axiom |native_decide|unsafe|implemented_by|partial def|@\[extern" \
     ShiftStableExponents/Basic.lean
```

Expected: one hit only, the words "No `sorry`." in the header comment. In particular
`native_decide` — which would delegate a proof to unverified compiled code — does not
appear.

**4b. Check the hypotheses are load-bearing, not decorative.** Weaken one and confirm the
proof breaks. For example, in `term_shift`/`dvd_Tint_sub` the constraint `r ≤ i` is
essential: without it there is no guarantee that `r!` divides `(n)_i`, so the binomial
denominators are not absorbed. `verify_proof.py` checks this directly — STEP 5 confirms
the termwise claim holds on 46,200 cases with `r ≤ i`, and STEP 5b re-runs the same
statement over the same `(k, i, n)` ranges with the constraint removed and reports
**11,509 violations out of 117,600 cases**. Both figures are printed by the script, so you
can confirm them rather than take them on trust.

**4c. Hunt for a counterexample to the theorem itself.** Use exact integers, never floats.
`python3 verification/sweep_congruence.py 100 8` searches 646,400 pairs $(n,k)$ with
$n+k\le100$ across
128 combinations of structured and random $(W,F,G,A,M)$ and finds none; it prints the exact
count, so you can confirm the figure rather than take it on trust. Beating that search is
the cleanest possible refutation.

**4d. Check the corollaries really instantiate the OEIS statements.** Read
`bala_congruence_A361281` in the source and confirm that the unconstrained prefactor `W`
is what plays the role of the OEIS comment's `F` — the OEIS statement there places *no*
condition on `F(0)`, which is why the main theorem carries a separate `W`. If that mapping
were wrong, the corollary would prove something weaker than advertised.

**4e. Evaluate the definitions inside Lean.** Rather than trusting the Python
transcription, you can make Lean compute `Bint` on concrete inputs with `#eval` and check
the output against OEIS bytes directly. This is the strongest form of the faithfulness
check, because it removes the transcription step entirely. The reproducible equivalent
shipped in this repository is `verification/check_faithful.py`, which transcribes the Lean
definitions verbatim — including `Nat` truncated subtraction — and compares against the
stored OEIS terms for all four sequences.

---

## Level 5 — Check it is not already known

The result is elementary, which makes prior art the main risk. What was done, and what you
can redo:

- **Full-text web search** for the construction `"exp(x*G(x)^n)"` returns nothing relevant.
- **OEIS full-text search** for the same string returns exactly two sequences, A361281 and
  A361036, both still reading "we conjecture".
- The three target sequences are **absent** from `google-deepmind/formal-conjectures`,
  while the related A278070 is present — so they were not in the formalization corpus.
- **The property itself is not new**, and the paper says so: it is what
  Cégielski–Grigorieff–Guessarian (*Int. J. Number Theory* **11** (2015),
  [arXiv:1310.1507](https://arxiv.org/abs/1310.1507)) call having *integral difference
  ratios*, and they characterize it completely. §7 of the paper explains why their
  criterion does not directly settle these families. If you think it does, that is the
  most valuable objection you could raise.
- Check the entries are still unresolved at the time you read this — Bala is an active
  contributor: <https://oeis.org/history?seq=A361036> and likewise for the others.

---

## Known weak points, stated plainly

1. **The definition is a human reading.** Level 0 cannot be automated away. It is two
   lines, but it is the hinge.
2. **`import Mathlib`** pulls in the whole library rather than named modules. Convenient,
   slow, and it makes the dependency footprint large. It does not affect soundness.
3. **The result is elementary.** A three-lemma proof of a three-year-old conjecture is the
   shape of a rediscovery. Two independent searches found no prior proof, but neither could
   search every venue; see Level 5.
4. **We have made errors in this repository and corrected them in place.** The false
   sharpness claim (Level 1) is the documented example; `docs/RESEARCH-LOG.md` also records
   an earlier line of work that turned out to rediscover Bala's own 2017 theorem, caught
   before any Lean was written. Treat the log as part of the evidence, not as decoration.
5. **`docs/instances-triage.md` deliberately does not overclaim.** An automated scan flagged
   14 further sequences; hand-checking reduced that to 3 genuinely settled by this theorem,
   ~6 already implied by Bala's own 2017 result, and 1 outright false positive.

---

## What would falsify the claims

| claim | how to falsify |
|---|---|
| the theorem is true | exhibit $(W,F,G,A,M,n,k)$ satisfying the hypotheses with $b(n+k)\not\equiv b(n)\pmod k$ |
| the proof is correct | `lake build` fails, or `test/Axioms.lean` prints `sorryAx` |
| the formalization is faithful | show `bala` does not equal $n![x^n](WF^{A(n)}\exp(xG^{M(n)}))$, or that `Bint` does not reproduce the OEIS terms |
| the corollaries match the OEIS conjectures | show an instantiation is weaker than the OEIS wording |
| the result is new | produce a prior proof, or show CGG's Theorem 2.5 settles it directly |

Reports of any of these are more useful than confirmation. The research log is kept so
that mistakes are auditable rather than invisible.
