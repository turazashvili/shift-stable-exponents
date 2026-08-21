#!/usr/bin/env python3
"""
Harvest and rank open conjectures from the OEIS full-database dump (oeis/oeisdata).

Goal: find conjectures matching the *empirically demonstrated tractable profile* for
LLM+Lean formal proof agents, as established by DeepMind's AlphaProof Nexus results
(arXiv:2605.22763), which proved 44/492 autoformalized OEIS conjectures.

Their 44 published solves (alphaproof-nexus-results/APNOutputs/OEIS) cluster hard on:
  - modular congruences / divisibility / integrality
  - exact constant value on an arithmetic progression   e.g. A248802: a(10n+2) = 67
  - structural predicates: is-square, is-prime, odd/even, positivity
  - closed forms, recurrences, periodicity, palindromic symmetry
and NOT on asymptotics, densities, limits, or infinitude statements.

Input format (OEIS internal): one file per sequence, lines of form `%X Annnnnn text`
  %N name   %C comment   %F formula   %K keywords   %O offset
  %S/%T/%U terms   %t/%o/%p programs   %H links   %D refs   %e examples
"""

import os
import re
import sys
import json
import argparse
from collections import defaultdict, Counter

# ---------------------------------------------------------------- parsing

FIELD_RE = re.compile(r"^%([A-Za-z])\s+(A\d{6})\s?(.*)$")

# Fields where a conjecture may be stated.
CONJ_FIELDS = ("C", "F", "N", "e")


def parse_seq_file(path):
    """Parse one .seq file into {field_letter: [lines]}. Returns (anum, fields)."""
    fields = defaultdict(list)
    anum = None
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                line = line.rstrip("\n")
                m = FIELD_RE.match(line)
                if not m:
                    continue
                f, a, text = m.group(1), m.group(2), m.group(3)
                anum = anum or a
                fields[f].append(text)
    except OSError:
        return None, None
    return anum, fields


def terms_of(fields):
    """Reassemble the term list from %S/%T/%U."""
    raw = "".join(fields.get("S", []) + fields.get("T", []) + fields.get("U", []))
    out = []
    for tok in raw.split(","):
        tok = tok.strip()
        if not tok:
            continue
        try:
            out.append(int(tok))
        except ValueError:
            pass
    return out


# ---------------------------------------------------------------- conjecture detection

# A line is a conjecture candidate if it announces itself as one.
CONJ_MARK = re.compile(
    r"\b(conjectur\w*|it appears that|appears to be|apparently|seems to|"
    r"empirical\w*|probably|presumably|is believed|we believe|"
    r"no proof is known|unproved|unproven)\b",
    re.I,
)

# Signals that the statement has ALREADY been settled -> exclude.
# NOTE: this is applied at SEQUENCE level, not line level. A conjecture line itself
# rarely says "proved"; the resolution is typically added as a *separate* comment
# later. Checking per-line re-admits solved problems -- exactly the failure that
# burned the Erdos-problem community (Barreto on #333, solved by Erdos in 1977).
SETTLED = re.compile(
    r"\b(this (was |has been )?(now )?(been )?prov(ed|en)|"
    r"proof (is given|was given|appears|follows|can be found|is in|is due|below|above)|"
    r"prov(ed|en) (by|in|above|below|using|via)|"
    r"now a theorem|is a theorem|"
    r"conjecture (is|was) (now )?(prov(ed|en)|settled|resolved|false|disproved)|"
    r"the conjecture (was|is) (prov|settl|resolv|verifi)|"
    r"disprov(ed|en)|counterexample (was |is )?(found|given)|"
    r"no longer a conjecture|confirmed by|"
    # --- idioms that OEIS actually uses to record a resolution. The absence of
    # these cost us a full investigation: A000262 et al. carry
    #   "The above conjecture is true - see the Bala link."
    # and were settled by Bala (2018), yet passed the earlier filter.
    r"(above|preceding|foregoing|first|second|last) conjectures? (is|are) true|"
    r"conjectures? (is|are) (now )?true|"
    r"the conjectures? (has|have) been (prov|establish|verifi|settl)|"
    r"(is|are) (now )?(known to be|established) (true|correct)|"
    r"see the .{0,30}link|"
    r"(follows|follow) (immediately |easily |directly )?from (the|a) (theorem|result|work|paper)|"
    r"this (is|follows) (a )?(known|classical|standard) (result|theorem)|"
    r"answered (in the )?affirmative|"
    r"resolved (by|in)|settled (by|in)|"
    # AI-agent resolutions now being annotated into OEIS
    r"autonomous AI agent|Tsoukalas|AlphaProof|Lean proof|formally verified)\b",
    re.I,
)

# ---- tractable-shape patterns (positive weights) -------------------------------
# Phrasings taken from actual OEIS comment text, validated against the 37 published
# DeepMind solves used as a labelled recall set (see diagnose_recall.py).

POS = [
    # ---- the "Gauss congruence" family: a(n+k) = a(n) mod k.
    # DeepMind proved this for A278070; the identical statement is open on many
    # other sequences (Peter Bala posted it widely). Highest-value single family.
    (r"a\(\s*n\s*\+\s*k\s*\)\s*[=≡]=?\s*a\(\s*n\s*\)\s*\(?\s*mod\s*k",
     8.0, "GAUSS_CONGRUENCE"),
    (r"a\(\s*n\s*\+\s*\w+\s*\)\s*-\s*a\(\s*n\s*\)\s*is divisible by", 7.0, "GAUSS_CONGRUENCE"),
    # exact constant value on an arithmetic progression: the A248802 archetype
    (r"a\(\s*\d*\s*\*?\s*n\s*[+-]\s*\d+\s*\)\s*[=≡]\s*-?\d+\b", 6.0, "EXACT_VAL_ON_AP"),
    (r"a\(\s*\d+\s*\*?\s*n\s*\)\s*[=≡]\s*-?\d+\b", 5.0, "EXACT_VAL_ON_AP"),
    # closed form (anchor relaxed: OEIS embeds these mid-sentence)
    (r"a\(\s*n\s*\)\s*=\s*(floor|ceiling|round|\d|[a-zA-Z]\w*\(|\()", 2.5, "CLOSED_FORM"),
    (r"\b(closed form|explicit formula|has the formula)\b", 1.5, "CLOSED_FORM"),
    # congruence / divisibility / integrality
    (r"\b(congruen\w*|\bmod\b|modulo)\b", 3.0, "CONGRUENCE"),
    (r"(\bdivisible by\b|\bdivides\b|\bdivisor of\b|is an integer\b|"
     r"is not an integer\b|integrality|never an integer)", 3.0, "DIVISIBILITY"),
    # structural predicates -- real OEIS phrasings
    (r"\b(is (always )?a (perfect )?square|perfect square|is a cube|"
     r"are (all )?squares?|square for all)\b", 4.0, "SQUARE"),
    (r"\b(is (always )?prime|is 1 or (a )?prime|are (all )?primes?|"
     r"contains only .{0,30}\bprimes?\b|only 1'?s and (the )?primes?|"
     r"consists? of .{0,20}primes?|all (the )?primes? appear)\b", 3.5, "PRIME"),
    (r"\b((is|are) (always )?(odd|even)|parity|"
     r"(odd|even) terms (occur|appear)|"
     r"a\(n\) is (odd|even))\b", 3.0, "PARITY"),
    (r"(\b(is (always )?positive|is never (zero|0)|nonzero|never vanishes)\b|"
     r"a\(\s*n\s*\)\s*>\s*0|>\s*0 for (all|n))", 3.0, "POSITIVITY"),
    (r"\b(occurs? only at|appears? only at|only at positions|"
     r"occurs? (exactly )?(once|twice)|appears? (exactly )?(once|twice))\b",
     3.5, "POSITION_CHARACTERIZATION"),
    (r"\b(never|no term)\b.{0,40}\b(equals?|is|divisible)\b", 2.0, "NEGATIVE_PREDICATE"),
    # membership in a named family (A103311: "all elements are Fibonacci numbers")
    (r"\ball (elements|terms|members)\b.{0,40}\bare\b", 3.0, "MEMBERSHIP"),
    # periodicity / symmetry / recurrence
    (r"\b(period\w*|eventually periodic|cycle length)\b", 3.5, "PERIODICITY"),
    (r"\b(palindrom\w*|symmetr\w*)\b", 3.5, "SYMMETRY"),
    (r"\b(recurrence|satisfies the recurrence|linear recurrence|D-finite)\b",
     3.0, "RECURRENCE"),
    # explicit finite/bounded claims
    (r"\b(the only|the largest|the last|only finitely many|"
     r"there are no (other|more)|except for)\b", 3.0, "FINITE_CLAIM"),
    (r"\b(bijection|injective|surjective|exactly one|unique\w*|"
     r"is a permutation of)\b", 2.0, "UNIQUENESS"),
    # digit / base statements (finite case analysis)
    (r"\b(digits?|base \d+|decimal expansion|ternary|binary representation)\b",
     1.5, "DIGITS"),
]

# ---- harder-shape patterns (mild penalties, NOT bans) -------------------------
# DeepMind demonstrably proved several asymptotic/limit conjectures
# (A340737 Tendsto e, A258667 IsEquivalent, A194806 bounded ratio, A051293
# asymptotic expansion), so these are down-ranked rather than excluded.

NEG = [
    (r"\b(asymptotic\w*|asymptotically)\b|~\s*[a-zA-Z0-9]", -1.5, "ASYMPTOTIC"),
    (r"\b(density|densities)\b", -2.0, "DENSITY"),
    (r"\b(limit|tends to|converges to|lim[ _]|approaches)\b", -1.0, "LIMIT"),
    (r"\b(infinitely many|infinitude|there exist infinitely)\b", -4.5, "INFINITUDE"),
    (r"\b(irrational|transcendental|normal number)\b", -6.0, "IRRATIONALITY"),
    (r"\bO\(|Omega\(|\blog log\b|\bBig-?O\b", -1.5, "GROWTH_ORDER"),
    (r"\b(Riemann Hypothesis|\bRH\b|Collatz|Goldbach|twin prime|"
     r"Hardy-?Littlewood|Schinzel|Bunyakovsky|Cramer|abc conjecture|"
     r"Legendre'?s conjecture)\b", -7.0, "FAMOUS_OPEN"),
    (r"\b(for (all )?sufficiently large|for large enough)\b", -1.0, "EVENTUAL"),
    (r"\b(heuristic\w*|numerical evidence suggests|random model)\b", -1.0, "HEURISTIC"),
]

POS_C = [(re.compile(p, re.I), w, t) for p, w, t in POS]
NEG_C = [(re.compile(p, re.I), w, t) for p, w, t in NEG]

# quantifier presence: a provable statement usually ranges over all n
QUANT = re.compile(r"\b(for all n|for every n|for any n|all n *>=|for n *>=|"
                   r"for all k|every term|all terms)\b", re.I)

# keyword-based signals
KW_GOOD = {"easy", "nonn", "core", "nice"}
KW_BAD = {"dead", "unkn", "obsc", "probation", "fini", "full", "dumb"}


MIN_SHAPE = 3.0  # a candidate must have real mathematical shape, not just good metadata


def score_conjecture(text, kws, n_terms, has_prog, has_formula):
    """Return (total, shape, tags).

    `shape` comes ONLY from the mathematical form of the statement (POS/NEG patterns).
    Infrastructure bonuses (program present, keywords, crispness) are added afterwards
    and deliberately cannot rescue a statement with no tractable shape -- otherwise
    every well-documented sequence scores highly regardless of its conjecture.
    """
    tags = []
    shape = 0.0
    n_pos = 0

    for rx, w, tag in POS_C:
        if rx.search(text):
            shape += w
            tags.append(tag)
            n_pos += 1
    for rx, w, tag in NEG_C:
        if rx.search(text):
            shape += w
            tags.append(tag)

    # Hard gate: need at least one tractable-shape signal and net positive shape.
    if n_pos == 0 or shape < MIN_SHAPE:
        return -1.0, shape, tags

    bonus = 0.0

    # must be a general statement, not a one-off remark
    if QUANT.search(text):
        bonus += 1.5
        tags.append("QUANTIFIED")

    # computability: a program means we can define it in Lean and test it
    if has_prog:
        bonus += 1.0
        tags.append("HAS_PROGRAM")
    if has_formula:
        bonus += 0.75
        tags.append("HAS_FORMULA")

    # empirical support: more known terms = conjecture more likely true
    if n_terms >= 40:
        bonus += 1.0
    elif n_terms >= 20:
        bonus += 0.5
    elif n_terms < 8:
        bonus -= 1.5
        tags.append("FEW_TERMS")

    # keywords (capped: a sequence with many tags shouldn't dominate on metadata alone)
    kl = set(kws)
    if kl & KW_GOOD:
        bonus += min(1.5, 0.5 * len(kl & KW_GOOD))
        tags.append("KW+" + ",".join(sorted(kl & KW_GOOD)))
    if kl & KW_BAD:
        bonus -= 4.0
        tags.append("KW-" + ",".join(sorted(kl & KW_BAD)))

    # length sanity: very long comments are usually discursive, not crisp statements
    L = len(text)
    if L > 600:
        bonus -= 2.0
        tags.append("VERBOSE")
    elif 40 <= L <= 260:
        bonus += 1.0
        tags.append("CRISP")

    return shape + bonus, shape, tags


# ---------------------------------------------------------------- main scan


def iter_seq_files(root):
    seqdir = os.path.join(root, "seq")
    for sub in sorted(os.listdir(seqdir)):
        d = os.path.join(seqdir, sub)
        if not os.path.isdir(d):
            continue
        for fn in sorted(os.listdir(d)):
            if fn.endswith(".seq"):
                yield os.path.join(d, fn)


def gather_conjectures(fields):
    """Extract conjecture candidates, joining continuation lines.

    OEIS stores each comment as its own %C line, but a conjecture is often split:
      %C A224515 Conjectures:
      %C A224515 (1) every odd square appears ...
      %C A224515 (2) ...
    A line that announces a conjecture but carries no content (ends in ':' or is
    very short) therefore absorbs the following lines.
    """
    out = []
    for f in CONJ_FIELDS:
        lines = fields.get(f, [])
        for i, text in enumerate(lines):
            if not CONJ_MARK.search(text):
                continue
            merged = text
            if text.rstrip().endswith(":") or len(text) < 45:
                for j in range(i + 1, min(i + 4, len(lines))):
                    merged += " " + lines[j]
                    if len(merged) > 400:
                        break
            out.append((f, merged))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="oeisdata")
    ap.add_argument("--out", default="candidates.jsonl")
    ap.add_argument("--min-score", type=float, default=6.0)
    ap.add_argument("--exclude", default="", help="file of A-numbers to skip (already attempted)")
    ap.add_argument("--limit-files", type=int, default=0)
    args = ap.parse_args()

    excluded = set()
    if args.exclude and os.path.exists(args.exclude):
        with open(args.exclude) as fh:
            for line in fh:
                m = re.search(r"A?(\d{6})", line.strip())
                if m:
                    excluded.add("A" + m.group(1))

    stats = Counter()
    tagstats = Counter()
    kept = []

    for i, path in enumerate(iter_seq_files(args.root)):
        if args.limit_files and i >= args.limit_files:
            break
        stats["files"] += 1
        anum, fields = parse_seq_file(path)
        if not anum:
            stats["unparsed"] += 1
            continue

        kws = []
        for kline in fields.get("K", []):
            kws.extend(k.strip() for k in kline.split(","))
        if "dead" in kws:
            stats["dead"] += 1
            continue

        name = " ".join(fields.get("N", []))[:400]
        tms = terms_of(fields)
        has_prog = any(f in fields for f in ("t", "o", "p"))
        has_formula = "F" in fields

        cand_lines = gather_conjectures(fields)
        if not cand_lines:
            continue
        stats["seqs_with_conjecture"] += 1

        # SEQUENCE-level settled check: scan every comment/formula/link/example,
        # because a resolution is normally recorded as a separate later comment.
        seq_blob = " ".join(
            fields.get("C", []) + fields.get("F", []) + fields.get("e", [])
            + fields.get("H", []) + fields.get("D", [])
        )
        if SETTLED.search(seq_blob):
            stats["settled_seq_skipped"] += 1
            continue

        if anum in excluded:
            stats["excluded_already_attempted"] += 1
            continue

        for f, text in cand_lines:
            sc, shape, tags = score_conjecture(text, kws, len(tms), has_prog, has_formula)
            stats["conjecture_lines"] += 1
            if sc >= args.min_score:
                stats["kept"] += 1
                for t in tags:
                    tagstats[t] += 1
                kept.append({
                    "anum": anum,
                    "field": f,
                    "score": round(sc, 2),
                    "shape": round(shape, 2),
                    "tags": tags,
                    "name": name,
                    "conjecture": text,
                    "keywords": kws,
                    "n_terms": len(tms),
                    "terms_head": tms[:12],
                    "has_program": has_prog,
                })

    kept.sort(key=lambda r: -r["score"])
    with open(args.out, "w") as fh:
        for r in kept:
            fh.write(json.dumps(r) + "\n")

    print("=== scan stats ===", file=sys.stderr)
    for k, v in stats.most_common():
        print(f"{k:34s} {v}", file=sys.stderr)
    print("\n=== top tags among kept ===", file=sys.stderr)
    for k, v in tagstats.most_common(24):
        print(f"{k:26s} {v}", file=sys.stderr)
    print(f"\nwrote {len(kept)} candidates -> {args.out}", file=sys.stderr)


if __name__ == "__main__":
    main()
