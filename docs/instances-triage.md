# Triage: which OEIS shift-congruence conjectures does the theorem settle?

Produced by `mining/find_instances.py`, then checked **by hand and by computation** —
the script's classifier is a heuristic first pass and over-reports. This file records the
honest verdicts.

Scan of the August 2026 OEIS dump (398,442 sequences):

| | count |
|---|---|
| carrying the shift-congruence conjecture `a(n+k) ≡ a(n) (mod k)` | 25 |
| already annotated as settled in OEIS | 4 |
| open | 21 |

## A. Settled by the theorem in this repository (n-dependent exponent)

These lie outside Bala (2017) because the inner series moves with `n`.

| sequence | form | instance |
|---|---|---|
| [A293013](https://oeis.org/A293013) | `n![xⁿ] exp(x/(1-x)ⁿ)` | `W=F=1`, `A=0`, `M=id`, `G=1/(1-x)` |
| [A361281](https://oeis.org/A361281) | `n![xⁿ] exp(x(1+x)ⁿ)` | `W=F=1`, `A=0`, `M=id`, `G=1+x` |
| [A361036](https://oeis.org/A361036) | `n![xⁿ] (1+x)ⁿ exp(x(1+x)ⁿ)` | `W=1`, `A=M=id`, `F=G=1+x` |

Plus the three *general* statements in those entries' comments and in
[A278070](https://oeis.org/A278070) (`A=id`, `M≡1`), which are the substance of the paper.

## B. Open in OEIS, but already implied by Bala's own 2017 theorem

Each has a **fixed** integral inner series `G` with `G(0)=1`, so
`Σ b(n)xⁿ/n! = W(x)·exp(x·G(x))` and Bala's Theorem 1 applies directly. Verified
computationally: 0 violations for `k ≤ 12`, and `G` confirmed integral with `G(0)=1`.

| sequence | e.g.f. | `G` |
|---|---|---|
| [A080833](https://oeis.org/A080833) | `exp(x/(1-x-x²))` | `1/(1-x-x²)` |
| [A088009](https://oeis.org/A088009) | `exp(x/(1-x²))` | `1/(1-x²)` |
| [A111884](https://oeis.org/A111884) | `exp(x/(1+x))` | `1/(1+x)` |
| [A112243](https://oeis.org/A112243) | `exp(x(1+x)/(1-2x))` | `(1+x)/(1-2x)` |
| [A115329](https://oeis.org/A115329) | `exp(x + 2x²)` | `1+2x` |
| [A294213](https://oeis.org/A294213) | `exp(1/((1-x)(1-x²)) - 1)` | integral, `G(0)=1` |

**This is a free contribution, and not ours:** these conjectures need only an OEIS
annotation pointing at
[Bala's 2017 note](https://oeis.org/A047974/a047974_1.pdf). No new mathematics. Worth
submitting as a courtesy, credited entirely to Bala. Do **not** present these as results
of this work.

Also in this group, with `W` a nontrivial prefactor and `G` constant
(`Σ b(n)xⁿ/n! = W(x)e^x`), and already listed as examples in Bala's own note:
[A000522](https://oeis.org/A000522), [A064570](https://oeis.org/A064570),
[A064571](https://oeis.org/A064571), [A229464](https://oeis.org/A229464).

## C. False positive — out of scope

[A000085](https://oeis.org/A000085) (involutions, `exp(x + x²/2)`). The scan matched it,
but its statement is restricted:

> `a(n+k) == a(n) (mod k) for all n >= 0 and all positive **odd** integers k.`

The unrestricted property genuinely **fails** (27 violations for even `k ≤ 14`), so this
is a different, weaker claim. The reason is visible in the shape:
`x + x²/2 = x(1 + x/2)`, so `G = 1 + x/2 ∉ ℤ[[x]]`, and the hypothesis of the theorem is
violated by the denominator 2 — precisely the `k` for which the property fails.

### A generalization that looked natural and is false

The obvious guess — that `G ∈ ℤ[1/D][[x]]` gives the congruence for all `k` coprime to
`D` — is **wrong**. Tested:

| `G` | `k` coprime to the denominator | `k` sharing a factor |
|---|---|---|
| `1 + x/2` | 0 violations | 27 violations |
| `1 + x/3` | **172 violations** | 78 violations |

So `1 + x/2` working for odd `k` is not an instance of a general denominator principle.
A000085 instead belongs to the *multiplicative* family `a(n+k) ≡ a(n)a(k) (mod k)`, the
subject of a separate Bala note (July 2026, linked from
[A057693](https://oeis.org/A057693)). Out of scope here; recorded so that nobody repeats
the guess.

*(Groups A and B are stated for the record. Group A is the contribution of this
repository; group B follows from Bala's own 2017 note and is credited entirely to him.)*
