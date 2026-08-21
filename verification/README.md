# Numerical verification

These scripts are **independent of the Lean development**. They use exact integer and
rational arithmetic (`fractions.Fraction`, Python big integers) throughout — never
floating point. So a reported agreement is exact over the range tested: it is not an
approximation, but neither is it a proof of an identity beyond that range. The proof is
the Lean development and the paper; these scripts are the guard against
misformalization and mis-stated numbers.

Every figure quoted in the paper or the top-level README is printed by one of the scripts
below, and `check_figures.py` enforces that mechanically in CI rather than leaving it to
discipline. Three figures were quoted here before that check existed and turned out to be
produced by nothing — "460,812 (n,k) pairs", "2637 counterexamples" and "625 odd-term
cases", each caught by outside review. That is what the check exists to prevent.

No dependencies beyond the Python standard library.

## Scripts that run standalone

| script | what it checks | exits non-zero on regression |
|---|---|---|
| `verify_proof.py` | every step of the proof separately: the two expansions against the definition, the three divisibility lemmas over exhaustive ranges, the edge terms, and **termwise shift-stability over 46,200 cases**. Also drops the `r ≤ i` constraint to confirm the arithmetic claim then becomes false | yes |
| `check_sharpness.py` | what the constant terms must satisfy. In the diagonal slice `W=1`, `A=M=id`: shows `F(0)=G(0)=1` is *not* necessary, that `F(0)·G(0)=1` *is* necessary, that it is **not sufficient** (odd-term controls must fail), and that the `(-1,-1)` branch with *even* `-F`, `-G` is a nonempty infinite family | yes |
| `check_paper_claims.py` | **every numeric example quoted in the paper**, asserted section by section — 40 claims | yes |
| `check_not_bala_form.py` | the A293013 obstruction: `[x^6](B'/B) = 117271/3`, so its e.g.f. does not factor as `F·exp(xG)` over `ℤ`. Includes a control confirming a genuine Bala-form series *passes*, so the test cannot fire spuriously | yes |
| `probe_localization.py` | the `ℤ[1/D]` congruence of §8 over 7128 `(n,k)` pairs including `gcd(k,D) > 1`, plus the withdrawn `G = 1+x/3` "counterexample" and the A000085 odd-`k` recovery | yes |
| `sweep_congruence.py` | the hostile `(n,k)` sweep. **Run it as `sweep_congruence.py 100 8`** to reproduce the 646,400-pair figure quoted in the paper; the bare invocation uses a smaller, faster bound and prints which one it used | yes |

## Scripts that need the OEIS dump

These compare against OEIS's own stored terms, so they need the sequence data. See
`../mining/README.md` for how to fetch it, then run from the repository root. Both fail
loudly if the dump is absent rather than skipping the comparison.

| script | what it checks | exits non-zero on regression |
|---|---|---|
| `check_faithful.py` | transcribes the Lean definitions *verbatim* (including `Nat` truncated subtraction) and confirms they reproduce the stored OEIS terms — the anti-misformalization guard | yes |
| `test_unified.py` | the unified statement across eight exponent pairs `(A, M)`, its A278070 term comparison against the dump, plus controls that non-shift-stable exponents must fail | yes |
| `check_figures.py` | **the traceability rule itself.** Runs the scripts above and checks, in both directions, that every figure quoted in `README.md`, `REVIEWING.md` and `paper/paper.tex` is printed by one of them: a manifest figure that stops being printed fails, and a new figure a document quotes but no script produces fails. Numbers that are not measurements (years, arXiv ids, the size of the external OEIS dump) sit in an explicit ignore-list with a stated reason. The `.tex` scanner strips comments, the bibliography and reference macros, and reads math mode — an earlier hand audit using a regex that skipped `$`-adjacent digits missed `$7128$` entirely | yes |

## Historical scripts

Kept for the record; they document a path that turned out to rediscover a known result.

| script | what it was for |
|---|---|
| `test_gauss_family.py` | the seven-sequence family with a fixed inner series |
| `characterize_gauss.py` | isolating the condition `c₁ = 1` empirically |
| `test_c1_conjecture.py` | stress-testing that condition (800 trials) |
| `test_bala_generalization.py` | first test of the `H(x)^n` diagonal generalization |

The `c₁ = 1` condition these converge on is exactly the hypothesis `G(0) = 1` of Bala's
2017 theorem. That branch of the work was a rediscovery, caught before any Lean was
written; see `../docs/RESEARCH-LOG.md`.
