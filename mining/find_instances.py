#!/usr/bin/env python3
"""
Find every OEIS sequence carrying the shift-congruence conjecture

    a(n+k) == a(n) (mod k)     for all n and k
    ("a(n) mod k is purely periodic with period dividing k")

and classify each by whether the main theorem of this repository settles it.

The theorem covers exactly the sequences of the form

    b(n) = n! * [x^n]( W(x) * F(x)^A(n) * exp(x * G(x)^M(n)) )

with W, F, G in Z[[x]], F(0) = G(0) = 1 (no condition on W), and A, M shift-stable.
Since Bala's 2017 theorem is the constant-exponent case, anything already covered by
that is not new; what we look for is the n-dependent exponents.

Usage (from the repository root, with the OEIS dump present -- see README):
    python3 mining/find_instances.py --root oeisdata
"""

import argparse
import os
import re
import sys
from collections import Counter

FIELD_RE = re.compile(r"^%([A-Za-z])\s+(A\d{6})\s?(.*)$")

# The conjecture, in the phrasings OEIS actually uses.
CONJ_RE = re.compile(
    r"a\(\s*n\s*\+\s*k\s*\)\s*==?\s*a\(\s*n\s*\)\s*\(?\s*mod\s*k"
    r"|b\(\s*n\s*\+\s*k\s*\)\s*==?\s*b\(\s*n\s*\)\s*\(?\s*mod\s*k"
    r"|period\s+divides\s+k"
    r"|periodic\s+on\s+reduction\s+modulo",
    re.I,
)

# Already-settled markers, at SEQUENCE level (see mining/README.md).
SETTLED_RE = re.compile(
    r"(above|preceding|foregoing|first|second|last)?\s*conjectures?\s+(is|are)\s+true"
    r"|this (was|has been)?\s*(now )?(been )?prov(ed|en)"
    r"|prov(ed|en) (by|in|above|below|using|via)"
    r"|see the .{0,30}link"
    r"|autonomous AI agent|Tsoukalas|AlphaProof|Lean proof"
    r"|is a theorem|now a theorem",
    re.I,
)

# ---- shape detection on the %N / %F lines -----------------------------------

# n! * [x^n] ...  or  E.g.f. ...
EGF_RE = re.compile(r"n\s*!\s*\*?\s*\[\s*x\s*\^\s*n\s*\]|E\.?g\.?f\.?", re.I)
# an exp(...) whose argument mentions n  -> n-dependent inner series (our M(n))
EXP_N_RE = re.compile(r"exp\s*\([^)]*\^\s*(?:\(?\s*)?n", re.I)
# a prefactor raised to an n-dependent power -> our A(n)
PREFACTOR_N_RE = re.compile(r"\)\s*\^\s*(?:\(?\s*)?n|\^\s*n\s*\*\s*exp|\^\s*\(\s*-?\s*n", re.I)
# any exp at all
EXP_RE = re.compile(r"\bexp\s*\(", re.I)


def parse(path):
    fields = {}
    anum = None
    try:
        with open(path, encoding="utf-8", errors="replace") as fh:
            for line in fh:
                m = FIELD_RE.match(line.rstrip("\n"))
                if not m:
                    continue
                f, a, text = m.group(1), m.group(2), m.group(3)
                anum = anum or a
                fields.setdefault(f, []).append(text)
    except OSError:
        return None, None
    return anum, fields


def iter_files(root):
    seqdir = os.path.join(root, "seq")
    for sub in sorted(os.listdir(seqdir)):
        d = os.path.join(seqdir, sub)
        if os.path.isdir(d):
            for fn in sorted(os.listdir(d)):
                if fn.endswith(".seq"):
                    yield os.path.join(d, fn)


def classify(name, formulas):
    """Return (verdict, reason) for whether the theorem plausibly applies."""
    blob = " ".join([name] + formulas)
    if not EGF_RE.search(blob) and not EXP_RE.search(blob):
        return "OTHER", "no e.g.f./exp form found in %N or %F"
    has_exp = bool(EXP_RE.search(blob))
    exp_has_n = bool(EXP_N_RE.search(blob))
    pref_has_n = bool(PREFACTOR_N_RE.search(blob))
    if not has_exp:
        return "OTHER", "no exp(...) factor"
    if exp_has_n and pref_has_n:
        return "COVERED", "n in both the exponential and a prefactor power (A,M both id-like)"
    if exp_has_n:
        return "COVERED", "n inside the exponential (M(n) nonconstant)"
    if pref_has_n:
        return "COVERED", "n in a prefactor power (A(n) nonconstant, M constant)"
    return "BALA2017", "exp with fixed inner series -- already Bala's 2017 theorem"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="oeisdata")
    ap.add_argument("--out", default="instances_report.md")
    args = ap.parse_args()

    stats = Counter()
    buckets = {"COVERED": [], "BALA2017": [], "OTHER": []}
    settled = []

    for path in iter_files(args.root):
        stats["files"] += 1
        anum, fields = parse(path)
        if not anum:
            continue
        kws = []
        for kl in fields.get("K", []):
            kws += [x.strip() for x in kl.split(",")]
        if "dead" in kws:
            continue

        cf = fields.get("C", []) + fields.get("F", [])
        if not any(CONJ_RE.search(t) for t in cf):
            continue
        stats["with_conjecture"] += 1

        blob = " ".join(cf + fields.get("H", []) + fields.get("e", []))
        name = " ".join(fields.get("N", []))
        formulas = fields.get("F", [])

        if SETTLED_RE.search(blob):
            stats["already_settled"] += 1
            settled.append((anum, name[:100]))
            continue
        stats["open"] += 1

        verdict, reason = classify(name, formulas)
        stats["verdict_" + verdict] += 1
        conj = next(t for t in cf if CONJ_RE.search(t))
        buckets[verdict].append((anum, name[:120], reason, conj[:220]))

    lines = []
    lines.append("# OEIS sequences carrying the shift-congruence conjecture\n")
    lines.append("Generated by `mining/find_instances.py`.\n")
    lines.append("| | count |")
    lines.append("|---|---|")
    for k in ("files", "with_conjecture", "already_settled", "open",
              "verdict_COVERED", "verdict_BALA2017", "verdict_OTHER"):
        lines.append(f"| {k} | {stats[k]} |")
    lines.append("")

    lines.append("## Open, and apparently SETTLED by the main theorem\n")
    lines.append("These have an n-dependent exponent, so they fall outside Bala (2017) "
                 "but inside the theorem proved here. Each needs the e.g.f. checked by "
                 "hand before claiming it.\n")
    for anum, name, reason, conj in sorted(buckets["COVERED"]):
        lines.append(f"### [{anum}](https://oeis.org/{anum})")
        lines.append(f"- **name:** {name}")
        lines.append(f"- **why covered:** {reason}")
        lines.append(f"- **conjecture:** {conj}")
        lines.append("")

    lines.append("## Open, but already the constant-exponent case (Bala 2017)\n")
    for anum, name, reason, conj in sorted(buckets["BALA2017"]):
        lines.append(f"- [{anum}](https://oeis.org/{anum}) — {name}")
    lines.append("")

    lines.append("## Open, shape not recognized (manual triage needed)\n")
    for anum, name, reason, conj in sorted(buckets["OTHER"]):
        lines.append(f"- [{anum}](https://oeis.org/{anum}) — {name}")
    lines.append("")

    lines.append("## Already settled in OEIS (excluded)\n")
    for anum, name in sorted(settled):
        lines.append(f"- [{anum}](https://oeis.org/{anum}) — {name}")
    lines.append("")

    with open(args.out, "w") as fh:
        fh.write("\n".join(lines))

    for k, v in stats.most_common():
        print(f"{k:24s} {v}", file=sys.stderr)
    print(f"\nwrote {args.out}", file=sys.stderr)
    print(f"\nCOVERED (candidate new results): "
          f"{', '.join(a for a, *_ in sorted(buckets['COVERED']))}", file=sys.stderr)


if __name__ == "__main__":
    main()
