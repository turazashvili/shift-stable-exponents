#!/usr/bin/env python3
"""Diagnose why DeepMind's known-solved OEIS conjectures were missed by the miner.

For each A-number they solved, walk the same pipeline stages and report the stage
at which it dropped out. This turns the 37 published solves into a labelled
recall test set for tuning the filter.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mine_oeis as M


def find_seq(root, anum):
    p = os.path.join(root, "seq", anum[:4], anum + ".seq")
    return p if os.path.exists(p) else None


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "oeisdata"
    listfile = sys.argv[2] if len(sys.argv) > 2 else "dm_solved_oeis.txt"
    threshold = float(sys.argv[3]) if len(sys.argv) > 3 else 7.0

    anums = []
    with open(listfile) as fh:
        for line in fh:
            m = re.search(r"A\d{6}", line)
            if m:
                anums.append(m.group(0))

    buckets = {}
    for anum in anums:
        path = find_seq(root, anum)
        if not path:
            buckets.setdefault("NO_FILE", []).append((anum, ""))
            continue
        _, fields = M.parse_seq_file(path)
        kws = []
        for k in fields.get("K", []):
            kws.extend(x.strip() for x in k.split(","))
        tms = M.terms_of(fields)
        has_prog = any(f in fields for f in ("t", "o", "p"))
        has_formula = "F" in fields

        # stage 1: any line that announces itself as a conjecture?
        marked = M.gather_conjectures(fields)
        if not marked:
            # is there anything conjecture-ish at all in C/F?
            allCF = " ".join(fields.get("C", []) + fields.get("F", []))
            buckets.setdefault("NO_CONJ_MARKER", []).append(
                (anum, "C/F chars=%d" % len(allCF)))
            continue

        # stage 2: settled filter (sequence level, same as miner)
        seq_blob = " ".join(fields.get("C", []) + fields.get("F", [])
                            + fields.get("e", []) + fields.get("H", [])
                            + fields.get("D", []))
        m2 = M.SETTLED.search(seq_blob)
        if m2 and not os.environ.get("NO_SETTLED"):
            buckets.setdefault("SETTLED_FILTER", []).append((anum, m2.group(0)))
            continue
        unsettled = marked

        # stage 3 / 4: shape gate and threshold
        best = (-99, None, None)
        for f, t in unsettled:
            sc, shape, tags = M.score_conjecture(t, kws, len(tms), has_prog, has_formula)
            if sc > best[0]:
                best = (sc, shape, tags, t)
        sc, shape, tags = best[0], best[1], best[2]
        if sc < 0:
            npos = sum(1 for rx, w, tag in M.POS_C if any(
                rx.search(t) for f, t in unsettled))
            buckets.setdefault("SHAPE_GATE", []).append(
                (anum, "shape=%.1f pos_tags=%d tags=%s" % (shape or 0, npos,
                 ",".join(tags or []))))
        elif sc < threshold:
            buckets.setdefault("BELOW_THRESHOLD", []).append(
                (anum, "score=%.2f tags=%s" % (sc, ",".join(tags))))
        else:
            buckets.setdefault("KEPT", []).append(
                (anum, "score=%.2f" % sc))

    order = ["KEPT", "BELOW_THRESHOLD", "SHAPE_GATE", "SETTLED_FILTER",
             "NO_CONJ_MARKER", "NO_FILE"]
    print("=" * 78)
    print("RECALL DIAGNOSIS on %d published DeepMind OEIS solves (threshold %.1f)"
          % (len(anums), threshold))
    print("=" * 78)
    for b in order:
        rows = buckets.get(b, [])
        if not rows:
            continue
        print("\n%-16s  %d" % (b, len(rows)))
        for anum, why in sorted(rows):
            print("    %-9s %s" % (anum, why[:150]))
    print()


if __name__ == "__main__":
    main()
