"""Which definitions a paper's readings show by their bodies (Unfolding.tsv).

Each row is one decision for one paper and one constant: `unfold` (the readings show the
definition's body, unfolded once) or `keep` (the readings show its label). The decisions are
presentation only. Whatever they say, each reading is parsed back and the kernel checks it
against the declaration's full type, so a decision can make a reading longer or shorter,
never wrong.

The rule the decisions follow: keep the paper's own terms; unfold what only Lean names,
when its body is short; keep long bodies. A row may cite the paper: a verbatim TeX quote and
its page, checked against the downloaded paper like the quotes on the web pages. A `keep`
that rests on "this is the paper's term" must cite it.
"""
import csv
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]  # the IRStatement folder
TABLE = BASE / "Tables" / "Unfolding.tsv"
EVIDENCE = "evidence (TeX, verbatim from the paper)"


def rows():
    with TABLE.open() as source:
        out = list(csv.DictReader(source, delimiter="\t", quoting=csv.QUOTE_NONE))
    seen = set()
    for r in out:
        if r["decision"] not in ("unfold", "keep") or (r["paper"], r["constant"]) in seen:
            raise ValueError(f"Unfolding.tsv: bad or repeated row for {r['paper']} {r['constant']}")
        if bool(r[EVIDENCE]) != bool(r["page"]):
            raise ValueError(f"Unfolding.tsv: evidence and page go together ({r['constant']})")
        seen.add((r["paper"], r["constant"]))
    return out


def unfolded(key):
    """The constants the readings of paper `key` show by their bodies."""
    return [r["constant"] for r in rows() if r["paper"] == key and r["decision"] == "unfold"]


def check(key):
    """Problems with the paper evidence of one paper's decisions, or None when the paper is not downloaded."""
    import quotes
    cited = [r for r in rows() if r["paper"] == key and r[EVIDENCE]]
    if not cited:
        return []
    paper = quotes.load(key)
    if not paper or paper.get("unavailable") or not (quotes.CACHE / f"P{key}" / "paper.pdf").exists():
        return None
    files = quotes.Paper(key, paper, quotes.CACHE)
    return [f"{r['constant']}: {p}" for r in cited
            for p in quotes.check_quote(files, {"page": int(r["page"]), "tex": r[EVIDENCE]})]
