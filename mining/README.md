# The OEIS conjecture-mining pipeline

How the conjecture proved in this repository was located: an automated scan of the
entire OEIS for open conjectures whose *shape* suggests they are tractable to a
formal-proof agent.

## Getting the data

The official full-database mirror (~3 GB, ~398k sequences, one file per sequence in the
classic OEIS internal format):

```bash
git clone --depth 1 https://github.com/oeis/oeisdata.git
```

## Running the scan

```bash
python3 mining/mine_oeis.py --root oeisdata --out candidates.jsonl \
        --min-score 7 --exclude mining/dm_solved_oeis.txt
```

Roughly 30 seconds over the full database. Output is one JSON object per candidate with
a score, matched shape tags, the conjecture text and the sequence metadata.

Observed on the August 2026 dump:

| | count |
|---|---|
| sequences scanned | 398,442 |
| sequences containing a conjecture marker | 43,949 |
| excluded as already settled | 2,186 |
| candidates passing the tractability filter | 5,522 |

## Calibration

The filter is validated against ground truth rather than intuition. `diagnose_recall.py`
uses the 37 OEIS conjectures published as solved in
[arXiv:2605.22763](https://arxiv.org/abs/2605.22763) as a labelled recall set, and
reports, for each miss, the pipeline stage that dropped it.

```bash
python3 mining/diagnose_recall.py oeisdata mining/dm_solved_oeis.txt 7.0

# shape-detector recall with the settled-filter bypassed:
NO_SETTLED=1 python3 mining/diagnose_recall.py oeisdata mining/dm_solved_oeis.txt 7.0
```

Shape-detector recall is 21/37 (57%). With the settled filter active, 29 of those 37 are
correctly excluded — OEIS has since been annotated with their resolutions, so the
pipeline automatically avoids problems that are already taken.

## The lesson worth carrying forward

The single most important component is **not** the shape scorer but the
already-settled detector, and it must operate at *sequence* level rather than line
level: a conjecture line almost never says "proved", because the resolution is added
later as a separate comment. An early version missed the idiom

> "The above conjecture is true - see the Bala link."

which was concealing 300 already-solved problems (5.2% of the candidate list). This is
the same failure mode that has repeatedly embarrassed automated attacks on the Erdős
problem list. See `../docs/RESEARCH-LOG.md`.
