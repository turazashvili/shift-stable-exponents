# Numerical verification

These scripts are **independent of the Lean development**. They use exact integer and
rational arithmetic (`fractions.Fraction`, Python big integers) throughout — never
floating point — so a reported agreement is an identity, not an approximation.

No dependencies beyond the Python standard library.

## Scripts that run standalone

| script | what it checks |
|---|---|
| `verify_proof.py` | every step of the proof separately: the two expansions against the definition, the three divisibility lemmas over exhaustive ranges, the edge terms, and **termwise shift-stability over 46,200 cases** |
| `check_sharpness.py` | what the constant terms must satisfy. In the diagonal slice `W=1`, `A=M=id`: shows `F(0)=G(0)=1` is *not* necessary, that `F(0)·G(0)=1` *is* necessary, that it is **not sufficient** (odd-term controls fail), and that the `(-1,-1)` branch with *even* `-F`, `-G` is a nonempty infinite family |

## Scripts that need the OEIS dump

These compare against OEIS's own stored terms, so they need the sequence data. See
`../mining/README.md` for how to fetch it, then run from the repository root.

| script | what it checks |
|---|---|
| `check_faithful.py` | transcribes the Lean definitions *verbatim* (including `Nat` truncated subtraction) and confirms they reproduce the stored OEIS terms — the anti-misformalization guard |
| `test_unified.py` | the unified statement across eight exponent pairs `(A, M)`, plus controls showing non-polynomial exponents fail |

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
