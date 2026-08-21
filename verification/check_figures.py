#!/usr/bin/env python3
"""
Enforce the traceability rule: every figure quoted in the documentation must be
printed by a checked-in script.

README.md and verification/README.md both promise this. Three times it turned out
not to hold -- "460,812 (n,k) pairs", "2637 counterexamples" and "625 odd-term
cases" were all quoted in the docs while no script produced them, and all three
were caught by outside review rather than by us. This script makes the promise
enforceable instead of aspirational.

It does two things:

  FORWARD  every entry in MANIFEST below must appear in the stdout of the script
           it names. A figure that stops being produced fails here.

  REVERSE  every figure-shaped number in the docs must be accounted for: either it
           is in MANIFEST, or it is in IGNORE with a stated reason. A new
           unbacked figure fails here.

Adding a figure to the docs therefore requires either pointing at the script that
prints it, or saying explicitly why it is not a measurement.

Needs the OEIS dump, because some figures come from check_faithful.py.

Usage:
    python3 verification/check_figures.py
"""

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DOCS = ["README.md", "REVIEWING.md", "paper/paper.tex"]

# --------------------------------------------------------------------------
# Figures that are measurements. figure -> (script, argv tail)
# --------------------------------------------------------------------------
MANIFEST = {
    # verify_proof.py
    "46200": ("verify_proof.py", []),
    "11509": ("verify_proof.py", []),
    "117600": ("verify_proof.py", []),
    # sweep_congruence.py, at the bound the docs quote
    "646400": ("sweep_congruence.py", ["100", "8"]),
    "128": ("sweep_congruence.py", ["100", "8"]),
    "100": ("sweep_congruence.py", ["100", "8"]),
    # test_unified.py
    "200": ("test_unified.py", []),
    # check_sharpness.py
    "600": ("check_sharpness.py", []),
    # check_not_bala_form.py  ([x^6](B'/B) = 117271/3)
    "117271": ("check_not_bala_form.py", []),
    # check_paper_claims.py  ([x^4](B'/B) = 2777/2 for A361036)
    "2777": ("check_paper_claims.py", []),
    # check_faithful.py -- the stored OEIS terms quoted in REVIEWING.md
    "106": ("check_faithful.py", []),
    "1457": ("check_faithful.py", []),
    "25946": ("check_faithful.py", []),
    "566827": ("check_faithful.py", []),
    "14665106": ("check_faithful.py", []),
    "438351041": ("check_faithful.py", []),
    "961": ("check_faithful.py", []),
    "24101": ("check_faithful.py", []),
    "818821": ("check_faithful.py", []),
    "36053515": ("check_faithful.py", []),
    "1984670465": ("check_faithful.py", []),
    "481": ("check_faithful.py", []),
    "10001": ("check_faithful.py", []),
    "288901": ("check_faithful.py", []),
    "10820965": ("check_faithful.py", []),
    "511186817": ("check_faithful.py", []),
    "124": ("check_faithful.py", []),
    "2225": ("check_faithful.py", []),
    "56546": ("check_faithful.py", []),
    "1928707": ("check_faithful.py", []),
    "85029596": ("check_faithful.py", []),
    "4687436609": ("check_faithful.py", []),

    # ---- figures quoted in paper/paper.tex ----------------------------------
    # sequence terms and worked examples, all asserted by check_paper_claims.py
    "58625": ("check_paper_claims.py", []),
    "529": ("check_paper_claims.py", []),
    "28788001": ("check_paper_claims.py", []),
    "58622": ("check_paper_claims.py", []),
    "1546": ("check_paper_claims.py", []),
    "2777": ("check_paper_claims.py", []),
    # the localization sweep of Section 8
    "7128": ("probe_localization.py", []),
}

# --------------------------------------------------------------------------
# Numbers that are not measurements. figure -> why
# --------------------------------------------------------------------------
IGNORE = {
    "2015": "publication year (Cegielski-Grigorieff-Guessarian)",
    "2017": "publication year (Bala's note)",
    "2023": "year Bala posted the OEIS conjectures",
    "2014": "publication year (Pin-Silva)",
    "2026": "current year",
    "1310": "arXiv identifier 1310.1507",
    "2605": "arXiv identifier 2605.22763",
    "2608": "arXiv identifier 2608.11941",
    "2607": "arXiv identifier 2607.18313",
    "289": "a line number in Basic.lean, not a quantity",
    "2020": "the year of the Mathematics Subject Classification scheme",
    "398442": (
        "number of sequences in the external August 2026 OEIS dump; provenance of "
        "the search, not a claim about our results, and verifiable by counting the "
        "dump's .seq files"
    ),
}


def strip_latex(t):
    """Remove the parts of a .tex file that carry no quoted quantities.

    This has to be done carefully. An earlier hand audit of paper.tex used a regex that
    excluded digits adjacent to `$` and therefore missed `$7128$` entirely, reporting a
    clean result while a figure went unchecked. So: strip comments, drop the
    bibliography wholesale (page ranges and years are not measurements), remove the
    arguments of reference-like macros, and remove sub/superscripts -- then scan the
    remainder, math mode included.
    """
    t = re.sub(r"(?<!\\)%.*", "", t)
    t = re.sub(r"\\begin\{thebibliography\}.*?\\end\{thebibliography\}", "", t, flags=re.S)
    for cmd in ("label", "ref", "Cref", "cref", "eqref", "cite", "url", "oeis",
                "texorpdfstring", "bibitem"):
        t = re.sub(r"\\" + cmd + r"\{[^{}]*\}", "", t)
    t = re.sub(r"\\href\{[^{}]*\}\{[^{}]*\}", "", t)
    t = re.sub(r"\^\{?\d+\}?", "", t)      # exponents, e.g. x^{2}
    t = re.sub(r"_\{?\d+\}?", "", t)        # subscripts
    return t


def figures_in(text, is_tex=False):
    """Numbers in a document that look like a quoted quantity."""
    if is_tex:
        text = strip_latex(text)
        # In LaTeX the thousands separator is {,} -- a bare comma is a list separator.
        # Normalise the former, then do NOT apply the comma-grouped pattern, or a term
        # list such as "1, 5, 55, 961, 24101" is misread as the single figure 55,961.
        text = text.replace("{,}", "")
        pat = re.compile(r"(?<![\w.])\d{3,}(?![\w])")
    else:
        pat = re.compile(
            r"(?<![\w.])\d{1,3}(?:,\d{3})+(?![\w])"     # comma-grouped: 646,400
            r"|(?<![\w.])\d{3,}(?![\w])"                 # three or more digits
        )
    out = {}
    for m in pat.finditer(text):
        raw = m.group(0)
        out.setdefault(raw.replace(",", ""), set()).add(raw)
    return out


def run(script, args):
    p = ROOT / "verification" / script
    r = subprocess.run(
        [sys.executable, str(p), *args],
        cwd=ROOT, capture_output=True, text=True, timeout=3600,
    )
    return r.returncode, r.stdout + r.stderr


def main():
    print("=" * 78)
    print("FIGURE TRACEABILITY")
    print("=" * 78)

    # ---- run each distinct script once -----------------------------------
    needed = sorted({(sc, tuple(ar)) for sc, ar in MANIFEST.values()})
    outputs = {}
    for script, args in needed:
        args = list(args)
        label = " ".join([script, *args])
        print(f"  running {label} ...", flush=True)
        code, out = run(script, args)
        if code != 0:
            print(f"    !! exited {code}")
        outputs[(script, tuple(args))] = out

    problems = []

    # ---- FORWARD: every manifest figure must be printed ------------------
    print()
    print("FORWARD: manifest figure -> script output")
    for fig, (script, args) in sorted(MANIFEST.items(), key=lambda kv: (kv[1][0], kv[0])):
        out = outputs[(script, tuple(args))]
        flat = out.replace(",", "")
        ok = fig in flat
        if not ok:
            problems.append(f"{fig} is quoted in the docs but {script} does not print it")
        print(f"  [{'ok' if ok else 'FAIL'}]  {fig:<12} {script}")

    # ---- REVERSE: every doc figure must be accounted for -----------------
    print()
    print("REVERSE: doc figure -> manifest or ignore-list")
    for doc in DOCS:
        text = (ROOT / doc).read_text(encoding="utf-8")
        found = figures_in(text, is_tex=doc.endswith(".tex"))
        unknown = [f for f in found if f not in MANIFEST and f not in IGNORE]
        print(f"  {doc}: {len(found)} figures, {len(unknown)} unaccounted")
        for f in sorted(unknown):
            forms = "/".join(sorted(found[f]))
            problems.append(
                f"{forms} appears in {doc} but is in neither MANIFEST nor IGNORE"
            )

    # ---- manifest rot ----------------------------------------------------
    all_flat = ""
    for d in DOCS:
        txt = (ROOT / d).read_text(encoding="utf-8")
        if d.endswith(".tex"):
            txt = strip_latex(txt).replace("{,}", "")
        all_flat += txt.replace(",", "") + "\n"
    stale = [f for f in MANIFEST if f not in all_flat]
    if stale:
        print()
        print("NOTE: manifest entries no longer quoted in the docs (harmless, but prune):")
        for f in sorted(stale):
            print(f"  {f}  ({MANIFEST[f][0]})")

    # ---- report ----------------------------------------------------------
    print()
    print("=" * 78)
    if problems:
        print(f"UNTRACEABLE FIGURES: {len(problems)}")
        for p in problems:
            print(f"  - {p}")
        print("=" * 78)
        print("Either point the figure at the script that prints it (MANIFEST),")
        print("or record why it is not a measurement (IGNORE).")
        return 1
    print("All quoted figures are produced by a checked-in script.")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
