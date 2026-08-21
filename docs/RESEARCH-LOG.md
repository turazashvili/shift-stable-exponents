# OEIS conjecture-mining pipeline — state and findings

Working dir: `/home/niko/sandbox/math_problems`

## Why OEIS (the strategic premise)

DeepMind's AlphaProof Nexus paper (arXiv:2605.22763) reports, with the same agent
and tooling, in the same run:

| corpus | attempted | solved | hit rate |
|---|---|---|---|
| open Erdős problems | 353 | 9 | **2.5%** |
| open OEIS conjectures | 492 | 44 | **8.9%** |

OEIS is 3.5x the hit rate on a far larger and much less contested corpus. Their
appendix B.2 also states they harvested **2,649** open OEIS conjectures and only
ever attempted 492 — ~2,150 of their own corpus untouched.

Two further facts that make this feasible rather than aspirational:
- *"A basic agent alternating LLM-based generation with Lean-based verification
  replicated the Erdős successes."* The evolutionary/AlphaProof machinery is not
  the moat.
- *"Codex (GPT-5.5) ... solved 7/9 problems."* A commercial coding agent + Lean
  reproduces most of their Erdős result. No TPUs required.

## Infrastructure (working)

- Lean 4.27.0 via elan; mathlib cache warm (6.9G).
- `formal-conjectures/` — DeepMind's Lean formalization repo (Erdős statements).
- `alphaproof-nexus-results/` — their published proofs, incl. **38 OEIS files**.
- **Validated end-to-end**: `lake build APNOutputs.OEIS.oeis_278070_conjecture_0`
  succeeded (7991 jobs). Their proofs compile here.
- `oeisdata/` — official full OEIS dump, **398,442 sequences**, 3.1G.

## Mining results

`mine_oeis.py` over all 398,442 sequences (~30s):

- **43,949** sequences contain a conjecture marker (vs their 2,649 corpus — 16x)
- **5,522** pass the tractability filter (vs their 492 *attempted* — 11x)
- 2,186 correctly excluded as already-settled; 1,957 dead

### Calibration against ground truth

`diagnose_recall.py` uses DeepMind's 37 published OEIS solves as a labelled
recall set. Shape-detector recall (settled-filter bypassed): **21/37 = 57%**,
after fixing the regexes against real OEIS phrasing (was 10/37). The two studied
archetypes rank #1 (A278070, 21.75) and high (A248802, 12.75).

**29 of their 37 solves are now annotated "proved" in OEIS** — the database is
being updated with AI-agent resolutions, so the settled filter auto-avoids taken
problems. This is why sequence-level (not line-level) settled detection matters.

### The bug that mattered

The settled detector originally missed the idiom **"The above conjecture is true
- see the Bala link."** Fixing it moved settled-detections 828 → 2,186 and
removed **300 already-solved candidates (5.2%)** from the list. This is exactly
the literature-retrieval trap that burned the Erdős community (Barreto on #333,
solved by Erdős himself in 1977; 9 of DeepMind's 13 January "solves" were
rediscoveries).

## Finding: the Gauss-congruence family

The conjecture `a(n+k) == a(n) (mod k)` recurs across many sequences. DeepMind
proved the A278070 instance as a one-off. Mining found 11 open instances, 7 of
which share the shape `a(n) = n![x^n] exp(sum c_k x^k)`.

Derived a unified statement:
- **Necessity, proved by hand:** `a(p) == c_1^p == c_1 (mod p)` by Fermat and
  `a(0)=1`, so `c_1 == 1 mod p` for every prime `p`, forcing `c_1 = 1`.
- **Sufficiency:** 800 random trials, all hold; 240 controls with `c_1 != 1`, all fail.

### This is Bala (2017). Rediscovery.

Peter Bala, *"Integer sequences that become periodic on reduction modulo k for
all k"* (Dec 2017), linked from OEIS A047974:

> **Theorem 1.** If `A(x) = sum a(n)x^n/n! = F(x) exp(x G(x))` with
> `F, G in Z[[x]]` and **`G(0) = 1`**, then `a(n+k) == a(n) (mod k)`.

Since `x·G(x) = sum c_k x^k` gives `c_1 = G(0)`, his `G(0)=1` **is** my `c_1=1`,
with extra generality from the prefactor `F`. Fully subsumed, 8 years stale.
Caught before any Lean was written — cost ~15 minutes.

## RESULT (UPGRADED): a single theorem covering BOTH open axes, verified end to end

The technique generalized further than the original target. Instead of one conjecture,
`BalaEndToEnd.lean` now proves a **unified theorem with arbitrary shift-stable exponents**:

> **Theorem.** Let `F, G ∈ ℤ[[x]]` with `F(0) = G(0) = 1`, and let `A, M : ℕ → ℕ` be
> *shift-stable* (`A(m+k) ≡ A(m) mod k`; every polynomial with ℕ coefficients qualifies).
> Then `b n = n! · [xⁿ]( F^{A n} · exp(x · G^{M n}) )` is integer valued and
> `b(n+k) ≡ b(n) (mod k)`.

Named cases, all now formally verified corollaries:

| `A n` | `M n` | which conjecture | prior status |
|---|---|---|---|
| const | const | Bala's 2017 Theorem 1 | proved 2017 (Bala) |
| `n` | `n` | **Bala A361036 general** | **open since Mar 2023** |
| `0` | `n` | A293013 / A361281 | **open since Mar 2023** |
| `n` | `1` | **A278070 general** | **open** (only the single-sequence case had been proved, by an AI agent, May 2026) |
| `n²` | `n` | quadratic exponents | never posed |

The two open axes are genuinely different — A361036 puts `n` inside the exponential,
A278070 puts it only in the prefactor — and neither is a special case of the other.
The unification is that the proof only ever needs the two exponents to be *shift-stable*,
which is strictly weaker than "polynomial".

Sharpness of that hypothesis, verified: non-polynomial exponents (`2ⁿ`, `n!`) **fail
6/6**. Expansion identity verified for 8 exponent pairs; congruence 200/200 on random
`F, G`. Lean's `Bint F G A M n` reproduces the OEIS stored terms for **all four** named
sequences to 9 terms (`A278070 1,2,11,106,1457,25946,566827,14665106,438351041`).

Theorems: `bala_congruence`, `bala_congruence_A361036`, `bala_congruence_A278070`,
`bala_congruence_sq`, plus `bala_eq_Bint` and `Bint_shift`. `#print axioms` on all six:
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

### (superseded, kept for the record) Bala's 2023 conjecture alone, end to end

**Status: COMPLETE.** `BalaEndToEnd.lean` compiles with no `sorry` and no `sorryAx`.
The final theorem is stated about

    bala F G n = n ! * [xⁿ]( Fⁿ * exp(x * Gⁿ) )

defined **directly** from mathlib's `PowerSeries.exp` and `PowerSeries.subst`, with
hypotheses `constantCoeff F = 1`, `constantCoeff G = 1`. Nothing is assumed.

| theorem | content |
|---|---|
| `bala_eq_Bint` | the bridge: `bala (toQ F) (toQ G) n = (Bint F G n : ℚ)` — **the former gap** |
| `coeff_one_add_pow_mul` | Newton expansion `[xⁱ]((1+P)^A·Z) = Σ_{r≤i} [xⁱ](Pʳ·Z)·C(A,r)` |
| `Bint_shift` | `k ∣ Bint F G (n+k) − Bint F G n` |
| `bala_congruence` | **end-to-end**: `bala` is integer valued and `b(n+k) ≡ b(n) (mod k)` |

`#print axioms` on all four: `[propext, Classical.choice, Quot.sound]` only.

How the bridge was done: `exp(x·Gⁿ)` is `subst (X * G^n) (exp ℚ)`; `coeff_subst'` gives a
`finsum` which collapses to `Σ_{d≤e}` because `xᵈ ∣ (x·H)ᵈ`; truncating at degree `n`
changes no coefficient `≤ n`, so multiplying by `Fⁿ` is safe; then `coeff_X_pow_mul`
and the reindexing `d ↦ n−i` with `n!/(n−i)! = descFactorial n i` produce `Bint`.

Faithfulness (test-lemma guard): Lean's `Bint`, transcribed verbatim, reproduces the
OEIS stored terms for all three sequences to 9 terms:
`A293013 1,1,5,55,961,24101,818821,36053515,1984670465`;
`A361281 1,1,5,37,481,10001,288901,10820965,511186817`;
`A361036 1,2,11,124,2225,56546,1928707,85029596,4687436609`.

**Remaining soft spot (irreducible):** whether the one-line `bala` definition is
faithful to Bala's prose is a human reading, as in any formalization. It is short
enough to check by eye.

## Superseded status note (kept for the record)

**Status.** The *arithmetic core* is proved and machine-checked in Lean 4 + mathlib
(`BalaCongruence.lean`), no `sorry`, no `sorryAx`. The conjecture itself is **not yet
formally verified**, and the gap is sharper than "routine bookkeeping":

> `BalaCongruence.lean` contains **zero** hypotheses mentioning `F`, `G`, power series,
> `exp`, or `F(0)=G(0)=1`.

Every hypothesis of Bala's conjecture, and every use of integrality of `d`, lives
entirely in the unformalized bridge `b n = B d n N`. What Lean proves is a
hypothesis-free arithmetic fact about `descFactorial` and `choose`. Two further side
conditions also live outside Lean: `N > n` is load-bearing (`B d n n ≠ b n`: it drops
the `i = n` block), and `d` must be *the same function for every* `n` (true, since
`d i r s = [xⁱ]PʳQˢ`, but it is a quantifier ordering Lean never sees).
Closing this bridge is the next task, not a formality.

### What the conjecture is, and whose it is

Not mine. Peter Bala stated it on **OEIS A361036, comment of 13 Mar 2023**:

> "let F(x) and G(x) denote power series with integer coefficients with
> F(0) = G(0) = 1. Define b(n) = n! * [x^n] exp(x*G(x)^n)*F(x)^n. Then we
> conjecture that b(n+k) == b(n) (mod k) for all n and k."

His 2017 note proves only the case of a **fixed** `G`; it ends with exactly the
open question this answers. A literature subagent found **no proof anywhere**, and
confirmed A293013 / A361281 / A361036 were **never formalized** (0 hits in
`google-deepmind/formal-conjectures`) and were **not** in the 492-conjecture
benchmark. The nearest prior art is A278070 (n-dependent *prefactor*, constant
exponential), proved by an AI agent in May 2026 for $5.

### The proof

Expand `exp(x·Gⁿ) = Σⱼ xʲGⁿʲ/j!` and `F^A G^B = Σ C(A,r)C(B,s)PʳQˢ` with
`F = 1+P`, `G = 1+Q`. Since `[xⁱ]PʳQˢ = 0` unless `r+s ≤ i`, this gives a finite
closed form

    b(n) = Σᵢ Σ_{r+s≤i} d(i,r,s) · (n)ᵢ · C(n,r) · C(n(n−i),s)          (★)

with `(n)ᵢ = descFactorial`, `d(i,r,s) = [xⁱ]PʳQˢ ∈ ℤ` independent of `n`. The
conjecture then reduces to: **every term of (★) is shift-stable mod k.** Telescope
`X'Y'Z' − XYZ = (X'−X)(Y'Z') + X(Y'−Y)Z' + XY(Z'−Z)` and kill each piece:

- `k ∣ X'−X` — the falling factorial is an integer polynomial.
- `k ∣ X(Y'−Y)` — `r! ∣ X` (from `r ≤ i`, via `r! ∣ i! ∣ (n)ᵢ`), and
  `r!(Y'−Y) = (n+k)_r − (n)_r ≡ 0 mod k`.
- `k ∣ X(Z'−Z)` — same with `s ≤ i`, using `N(n+k) − N(n) = k(n + (n−i) + k)`.

The uses of `r ≤ i` and `s ≤ i` are **independent**; one never needs `r!s! ∣ i!`.
That is what makes it elementary. (An earlier gcd-based route,
`(k/gcd(k,m!)) ∣ C(N',m)−C(N,m)`, works but is strictly worse to formalize.)

### What is machine-checked vs. not

| statement | status |
|---|---|
| `term_shift` — each term of (★) shift-stable mod k | **Lean, proved** |
| `edge_term` — `k ∣ (n+k)ᵢ` for `i > n` | **Lean, proved** |
| `B_shift` / `B_modEq` — the full sum (★) satisfies the congruence, ∀ d, ∀ N | **Lean, proved** |
| `b(n) = B(d,n,N)` for `N > n` (the generating-function identity, Steps 1–2) | **numeric only** |

The one gap is routine power-series bookkeeping, not mathematical content. It is
verified *exactly* (integer arithmetic, not floating point) in `verify_proof.py`
and `check_faithful.py`.

### Evidence the formalization is not vacuous (test-lemma guard)

`check_faithful.py` transcribes Lean's `T`/`B` **verbatim**, including ℕ-truncated
subtraction, and finds:

- Lean's `B` reproduces `b` for all three OEIS targets and 8/8 random `(F,G)`
- terms match OEIS's stored terms
- `B` is independent of the truncation `N`, as the `∀ N` in `B_shift` requires
- the formally proved congruence holds on the real sequences (324 cases, 0 violations)

Plus, from `verify_proof.py`: the heart of the proof, termwise shift-stability,
tested on **46,200** cases with 0 violations. Independent hostile review reports
**460,812** `(n,k)` pairs with 0 violations (to `n+k ≤ 140`), confirms the hypotheses
are load-bearing (dropping `r ≤ i` produces 2637 counterexamples to `term_shift`),
and — a stronger faithfulness check than mine — made **Lean itself `#eval` its own
`T`/`B`**, matching the OEIS `%S/%T/%U` bytes verbatim for all three sequences.

### CORRECTION: my sharpness claim was wrong

An earlier version of this file asserted "sharpness confirmed (dropping `F(0)=1` or
`G(0)=1` breaks the congruence)". **That is false**, found by hostile review and
independently reconfirmed here in `check_sharpness.py`. The true necessary condition is

    F(0) * G(0) = 1

which over `ℤ` also admits `(F(0), G(0)) = (-1, -1)`. Necessity: at `n = 0`, `k = p`
prime, `(p)ᵢ ≡ 0 mod p` for `i ≥ 1`, so `b(p) ≡ F₀^p G₀^{p²} ≡ F₀G₀ (mod p)` by Fermat,
while `b(0) = 1`; so `F₀G₀ ≡ 1` mod every prime, hence `F₀G₀ = 1`.

The `(-1,-1)` branch is non-empty and infinite: if `F = -F̃`, `G = -G̃` with `F̃, G̃`
**even** series (functions of `x²`) and `F̃(0) = G̃(0) = 1`, then `b_{F,G} = b_{F̃,G̃}`
*identically* — because for odd `n`, `x ↦ -x` fixes `F̃, G̃` and turns `exp(-xG̃ⁿ)` into
`exp(xG̃ⁿ)`. Verified exactly on three such pairs; controls with a single odd term fail
(45 and 67 violations). A scan of `(F₀,G₀) ∈ [-3,3]²` finds the congruence holding at
**exactly** the two points with `F₀G₀ = 1`.

Why the original check missed it: `verify_proof.py`'s sharpness block randomised only
the constant term, which lands in the generic failing region and never samples the
even-series family. This does not affect the proof — Bala's conjecture assumes
`F(0)=G(0)=1` — but the stated *sharpness* was wrong, and the theorem is in fact true
on a strictly larger domain than advertised.

### Honest read on difficulty

An elementary 3-lemma proof of a conjecture open since 2023 is suspicious, so:
Bala's own 2017 note poses the question and does not answer it; the strictly
easier A278070 variant went unproved until May 2026; and the subagent's search
turned up nothing. The plausible explanation is the thesis of this whole project —
these are *computations nobody bothered to do*, not deep problems. The
non-obvious step is the expansion (★); once you have it, the rest is bookkeeping.

### Prior art we must cite: the property is already classified

A second, deeper search found a **complete published characterization of exactly this
property**, predating Bala's note:

> **Cégielski, Grigorieff, Guessarian**, *Newton representation of functions over
> natural integers having integral difference ratios*, Int. J. Number Theory **11**
> (2015), arXiv:1310.1507. **Thm 2.5:** for `f(x) = Σₖ aₖ C(x,k)`, the condition
> `(a-b) ∣ f(a)-f(b)` for all `a ≠ b` holds **iff** `lcm(1,…,k) ∣ aₖ` for all `k`.
> **Cor 2.6:** `k! ∣ aₖ` suffices. **Prop 3.3/3.7:** the class is a ring, closed under
> composition.

Setting `a = n+k, b = n`, "integral difference ratios" *is* Bala's property. So this is
not a mysterious new phenomenon — it is a **membership question in a fully classified
class**, and our expansion (★) is precisely a Newton-type expansion, i.e. the attack
CGG's framework prescribes. Any write-up must cite CGG and Pin–Silva (2011) and
pre-empt the obvious referee question, "why not just apply Theorem 2.5?" (Answer: the
number of summands grows with `n`, the exponent `n(n-i)` is quadratic in `n`, and
`[xⁱ]H^N` is only integer-*valued* in `n`, not integer-coefficient; CGG's closure
properties are for finitely many fixed operations.)

Bounding the folklore risk: the two literatures are **provably disconnected**. OEIS
full-text has zero hits for "integral difference ratio"; CGG's paper has zero
occurrences of `OEIS`, `Bala`, `exp(x`, `G(x)`, or "exponential generating"; and all 15
of CGG's citations are theoretical CS / universal algebra, none applying it to a
generating-function-defined sequence. CGG's theorem also already answers the open
Question at the end of Bala's 2017 note — nobody noticed.

### Web search (BrowserOS neo, 21 Aug 2026) — the check both subagents were blocked from

The previous searches could not reach any general web search engine; this closes that gap.

| query | result |
|---|---|
| verbatim `"exp(x*G(x)^n)"` | **Nothing relevant.** One 2003 French numerical-analysis thesis with an unrelated lookalike `exp(X·g(X/n))`. No paper on the indexed web contains this construction. |
| `"A361036" OR "A361281" OR "A293013" conjecture proof` | Only A278070 (whose *different* conjecture was AI-proved) + an irrelevant A342357. **No proof of ours.** |
| `"integral difference ratios" "generating function"` | Confirms CGG 2015 (Int. J. Number Theory 11:07; arXiv Oct 2013). Citing items are Academia.edu mirrors, "Affine completeness of free binary algebras", generic binomial-coefficient pages. **Nothing applying it to a generating-function-defined sequence.** |
| `"become periodic on reduction modulo"` | The phrase occurs essentially only as the title of Bala's note, cited from OEIS entries (A047974, A000262, A255819, A064571, A293527/8, A296618, A080833). **No journal paper on this property under this name.** |
| `Bala conjecture OEIS "mod k" proof arxiv 2026` | Only Kallat's A028342 paper (different sequence, multiplicative axis). |

Caveat: Google's AI-overview panels asserted various things about generating functions and
this property; those are model-generated, not sources, and were ignored.

Net effect: novelty confidence rises from ~90% to **~95%**. The two literatures
(OEIS/Bala vs. CGG "integral difference ratios") are confirmed disconnected.

### No race after all

Checked directly against OEIS revision histories: **A361036 is unchanged since
revision #13 (28 Mar 2023); A361281 since #21 (13 Mar 2023); A293013's only 2026 edit
(11 Jul) was cosmetic.** Bala's 30 Jul / 1 Aug / 16 Aug 2026 activity was on A057693,
A000009 and A000262 — not these. Contemporaneous evidence from A361281's revision
history, Bala on 12 Mar 2023: *"I have a feeling that this periodicity property modulo
k might hold more generally for sequences of the form a(n) = n!·[x^n] exp(x·G(x)^n) …
I need to do some experimentation next week."*

Also worth recording: `B_shift` is **strictly more general** than the A361036
statement — it additionally covers the A361281 variant (fixed prefactor `F`, only
`G(0)=1`) via `d i r s = 0` for `r ≥ 1`.

## Superseded: generalizing Bala past his hypothesis

Three sequences carry the same conjecture but have **no resolution annotation**,
because Bala's theorem does not apply — their inner series depends on `n`:

| seq | form | status |
|---|---|---|
| A293013 | `n![x^n] exp(x/(1-x)^n)` | verified true, unannotated |
| A361281 | `n! sum_k C(nk,n-k)/k! = n![x^n] exp(x(1+x)^n)` | verified true, unannotated |
| A361036 | `n![x^n] (1+x)^n exp(x(1+x)^n)` | verified true, unannotated |

All three are the diagonal `a(n) = n![x^n] F(x) H(x)^(alpha*n) exp(x H(x)^n)`
with `H in Z[[x]]`, `H(0)=1`.

**CONJECTURE (generalized Bala).** For `H in Z[[x]]` with `H(0)=1`, integer
`alpha >= 0`, and fixed `F in Z[[x]]`, the diagonal above satisfies
`a(n+k) == a(n) (mod k)`.

Evidence (`test_bala_generalization.py`):
- all 3 targets reproduce OEIS terms and satisfy the congruence
- **42/42** random integral `H` with `H(0)=1`, `alpha in {0,1,2}`
- controls `H(0) != 1`: all fail (hypothesis is sharp)
- 8/8 with arbitrary fixed integral prefactor `F`

Caveat: the unrestricted `n`-dependent version is **false** — with `G_n = 1` and
adversarial `F_n`, `a(n)` is essentially arbitrary. The `H(x)^n` structure is
load-bearing, which is what makes this a real theorem rather than a slogan.
