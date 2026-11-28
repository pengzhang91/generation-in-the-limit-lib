"""Write and verify the glossary: an IR reading of the definition behind each label.

For each paper, the library constants named in its readings (the page's label table) are
looked up in Lean. For a plain definition `c`, `#ir_glossary c` (Glossary.lean) adds the
theorem `IRGlossary.c : ∀ x…, c x… ↔ body` (or `= body`), proved by `Iff.rfl` or `rfl`,
so the kernel confirms that `body` is the definition of `c` unfolded once. That theorem is then
read like any declaration: the saved body must have one parse, equal to the tree selected
from the theorem's export, and the kernel compares the parse's Lean rendering with the
theorem's type. A label keeps the wording it has on the paper's page; labels that occur only
inside definitions get labels by the same rule, avoiding the page's labels.

`--write` regenerates the glossary pages (Readings/Glossary/Pxx.md) before verifying them.
By default every paper with a reading page is processed, and the run writes the check log
Readings/Glossary/RUN-LOG.md and the rule cards; `--papers 03 05` checks only those and writes no log.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile

sys.dont_write_bytecode = True
BASE = Path(__file__).resolve().parents[1]  # the IRStatement folder
sys.path.insert(0, str(Path(__file__).resolve().parent))
import cards
import reader
from reader import (KEYS, LATER, LAKE, LEAN, READINGS, EXPORTER, VOCABULARY, compile_grammar, complete, display, inventory,
                   lean_file, lean_text, messages, page_path, parse, roundtrip, run, stage)
from selector import label_words, paper_names, select

GLOSSARY = READINGS / "Glossary"
MODULE = "IRStatement.Glossary"
OWN = "GenLimit."  # only the library's own definitions; Mathlib's are notation the reader knows
SAMPLE = (("Prop", 3, 20), ("Term", 3, 10), ("Doc", 4, 20))


def page_labels(key):
    """{constant: label} from the label table of the paper's saved readings."""
    text = page_path(key).read_text()
    return {c: l for l, c in re.findall(r"^\| \*([^*]+)\* \| `([^`]+)` \|$", text, re.M)}


def more_labels(fixed, extra):
    """Labels for constants that occur only inside definitions: the same rule as for readings,
    with namespace components added until no label repeats one of the page's or another's."""
    depth = {c: 1 for c in extra}

    def make(c):
        return " ".join(label_words(p) for p in c.split(".")[-depth[c]:])
    taken = set(fixed.values())
    while True:
        seen = {}
        for c in extra:
            seen.setdefault(make(c), []).append(c)
        clashes = [cs for label, cs in seen.items() if len(cs) > 1 or label in taken]
        if not clashes:
            return {**fixed, **{c: make(c) for c in extra}}
        for cs in clashes:
            for c in cs:
                if depth[c] >= len(c.split(".")):
                    raise ValueError(f"No distinct label for {c}")
                depth[c] += 1


def export(work, key, consts, modules):
    """Add each definition statement and export it. Returns {c: (kind, module, line, tree)} and
    {c: why} for the constants that have no definition statement."""
    lines = []
    for c in consts:
        lines += [f"#ir_glossary {c}", f"#ir_export IRGlossary.{c} unfolding"]
    imports = [EXPORTER, MODULE, *modules]
    msgs = messages(lean_file(work, f"Glossary{key}.lean", lines, imports))
    first = len(imports) + 1
    found, why = {}, {}
    for m in msgs:
        k = (m["pos"]["line"] - first) // 2
        c = consts[k]
        if m["severity"] == "error":
            why.setdefault(c, m["data"].splitlines()[0][:160])
        elif m["severity"] == "information":
            data = json.loads(m["data"])
            if data[0] == "definition":
                found.setdefault(c, {}).update(kind=data[2], module=data[3], line=data[4])
            else:
                found.setdefault(c, {})["tree"] = data[1]
    good = {c: v for c, v in found.items() if c not in why and "tree" in v and "kind" in v}
    return good, {c: why.get(c, "not exported") for c in consts if c not in good}


def source_path(module):
    return LEAN / (module.replace(".", "/") + ".lean")


def heading(label):
    return f"*{label}*"


def write_page(key, entries, names, missing):
    reg = json.loads((LEAN.parent / "registry" / "papers" / f"P{key}.json").read_text())
    parts = [f"# P{key} glossary · {reg['paper']['title']}\n\n"
             f"Definitions of the labels in [the P{key} readings](../{page_path(key).name}), "
             "read from Lean. Each body is checked like a reading against "
             "`IRGlossary.c`, a theorem that states the definition of `c` and is proved by `Iff.rfl` or `rfl`. "
             "[Glossary log](RUN-LOG.md)"]
    for e in entries:
        link = os.path.relpath(source_path(e["module"]), GLOSSARY)
        parts.append(f"## {heading(names[e['const']])}\n\n{e['body']}\n\n"
                     f"[Lean definition]({link}#L{e['line']}) · `{e['const']}`")
    if missing:
        parts.append("## Labels without a checked definition\n\n" +
                     "\n".join(f"- *{names[c]}* `{c}`: {why}" for c, why in sorted(missing.items(),
                                                                         key=lambda x: names[x[0]])))
    used = sorted({c for c in names if any(f"*{names[c]}*" in e["body"] for e in entries)}, key=lambda c: names[c])
    if used:
        parts.append("## Labels\n\n| Label | Lean constant |\n|---|---|\n" +
                     "\n".join(f"| *{names[c]}* | `{c}` |" for c in used))
    return "\n\n".join(parts) + "\n"


def saved(path):
    """[(constant, body)] from a saved glossary page."""
    text = path.read_text().split("\n## Labels without a checked definition\n")[0].split("\n## Labels\n")[0]
    out = []
    for section in re.split(r"^## .+$", text, flags=re.M)[1:]:
        body, ref = section.strip("\n").rsplit("\n\n", 1)
        m = re.fullmatch(r"\[Lean definition\]\([^)]+\) · `([^`]+)`", ref)
        if not m:
            raise ValueError(f"Missing definition reference: {ref!r}")
        out.append((m[1], body))
    return out


def verify(work, key, path, readings, modules):
    """Parse each saved body, compare trees, render P′ and ask the kernel. Returns {c: status}."""
    sections = saved(path)
    if [c for c, _ in sections] != list(readings):
        raise ValueError(f"{path.name} must contain the readable definitions in order")
    status, checks = {}, []
    for c, body in sections:
        r = readings[c]
        trees = complete(parse(r["g"], r["gname"], body))
        unique = len(trees) == 1
        same = unique and trees[0] == r["tree"]
        canonical = unique and display(r["g"].render(trees, r["gname"], r["gname"] + "Eng")[0]) == body
        status[c] = {"parses": len(trees), "same": same, "canonical": canonical, "lean": "not run"}
        if unique:
            checks.append((c, lean_text(r["g"].render(trees, r["gname"], r["gname"] + "Lean")[0])))
    if checks:
        imports = ["IRStatement.Check", VOCABULARY, MODULE, *modules]
        lines = [f"#ir_glossary {c}" for c, _ in checks] + \
                [f"#check_statement IRGlossary.{c} against ({p})" for c, p in checks]
        result = lean_file(work, f"GlossaryChecked{key}.lean", lines, imports)
        errors = [[] for _ in lines]
        for m in messages(result):
            if m["severity"] == "error":
                errors[m["pos"]["line"] - len(imports) - 1].append(m["data"])
        for k, (c, term) in enumerate(checks):
            errs = errors[k] + errors[len(checks) + k]
            status[c].update(lean=stage(f"IRGlossary.{c}", errs), errors=errs, term=term)
    return status


def one_paper(work, key, write, log):
    fixed = page_labels(key)
    consts = sorted((c for c in fixed if c.startswith(OWN)), key=lambda c: (fixed[c].lower(), c))
    modules = sorted({e.module for e in inventory(key)})
    found, missing = export(work, key, consts, modules)
    avoid = paper_names([v["tree"] for v in found.values()])
    chosen = []
    for c in consts:
        if c not in found:
            continue
        try:
            tree, sel = select(found[c]["tree"], avoid, defines=(c, found[c]["kind"]))
        except Exception as error:
            missing[c] = f"no reading yet ({type(error).__name__}: {str(error)[:120]})"
            continue
        chosen.append((c, tree, sel))
    from selector import label_constant   # a key c#h (a hidden proof argument) has the label of c
    extra = sorted({label_constant(k)[0] for _, _, s in chosen for k in s.consts} - set(fixed))
    names = more_labels(fixed, extra)
    folder = work / f"G{key}"
    folder.mkdir()
    readings = {}
    for k, (c, tree, sel) in enumerate(chosen):
        gname = f"G{key}x{k}"
        readings[c] = {"tree": tree, "gname": gname, "g": compile_grammar(folder, gname, [sel], names)}
    path = GLOSSARY / f"P{key}.md"
    if write:
        entries = [{"const": c, "body": display(r["g"].render([r["tree"]], r["gname"], r["gname"] + "Eng")[0]),
                    **found[c]} for c, r in readings.items()]
        path = folder / f"P{key}.md"
        path.write_text(write_page(key, entries, names, missing))
    if write:
        # A definition Lean rejects is listed with the reason, and the page is published with the rest.
        trial = verify(work, key, path, readings, modules)
        rejected = [c for c, st in trial.items() if st["lean"] != "accepted"]
        for c in rejected:
            missing[c] = (f"no checked reading yet (Lean: {trial[c]['lean']}: "
                          f"{(trial[c].get('errors') or [''])[0].splitlines()[0][:100]})")
            del readings[c]
        if rejected:
            entries = [e for e in entries if e["const"] not in rejected]
            path.write_text(write_page(key, entries, names, missing))
    log.append(f"## P{key}\n\nSHA-256 of the checked page: `{hashlib.sha256(path.read_bytes()).hexdigest()}`\n")
    status = verify(work, key, path, readings, modules)
    recovered = total = 0
    for c, r in readings.items():
        count, failures = roundtrip(r["g"], folder, r["gname"], sizes=SAMPLE)
        total += count
        recovered += count - len(failures)
    for c, s in status.items():
        log.append(f"### *{names[c]}* · `{c}`\n\n- GF parses of the saved body: {s['parses']} complete\n"
                   f"- Parsed tree equals the tree selected from the definition statement: {s['same']}\n"
                   f"- Saved body is the canonical rendering of the parsed tree: {s['canonical']}\n"
                   f"- Lean: {s['lean']}" + (": " + " | ".join(x[:300] for x in s.get("errors", []))
                                              if s.get("errors") else "") + "\n" +
                   (f"\nRecovered proposition P′:\n\n```lean\n{s['term']}\n```\n" if "term" in s else ""))
    good = [c for c, s in status.items() if s["parses"] == 1 and s["same"] and s["canonical"] and s["lean"] == "accepted"]
    for c, s in status.items():
        if c not in good:
            print(f"P{key} {c}: parses {s['parses']}, same {s['same']}, canonical {s['canonical']}, "
                  f"Lean {s['lean']} {(s.get('errors') or [''])[0][:300]}", flush=True)
    line = (f"P{key}: {len(good)}/{len(consts)} library labels have a checked definition; "
            f"{len(missing)} without; {recovered}/{total} random trees recovered")
    print(line, flush=True)
    ok = len(good) == len(status) and recovered == total
    if write and ok:
        GLOSSARY.mkdir(parents=True, exist_ok=True)
        (GLOSSARY / f"P{key}.md").write_text(path.read_text())
    # For the rule cards: the trees of the checked definitions, keyed like the readings in reader.py.
    usage = {(key, f"glossary *{names[c]}*", c): readings[c]["tree"] for c in good}
    sources = {(key, f"glossary *{names[c]}*", c): (readings[c]["g"], readings[c]["gname"], folder) for c in good}
    return line, ok, {c: why for c, why in missing.items()}, usage, sources


def main():
    cli = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    cli.add_argument("--write", action="store_true", help="regenerate the glossary pages, verify them, then publish")
    cli.add_argument("--papers", nargs="+", choices=KEYS + LATER, help="papers to check (default: all; writes the log)")
    args = cli.parse_args()
    full = args.papers is None
    if full:
        args.papers = [k for k in list(KEYS) + list(LATER) if page_path(k).exists()]
    log = ["# Glossary check log\n\nWritten by `glossary.py` from the saved glossary pages; do not edit.\n"]
    summary, ok, reasons, usage, sources = [], True, {}, {}, {}
    with tempfile.TemporaryDirectory(prefix="ir-glossary-") as temp:
        work = Path(temp)
        run([*LAKE, "build", EXPORTER, VOCABULARY, MODULE], cwd=LEAN)
        for key in args.papers:
            line, good, missing, used, where = one_paper(work, key, args.write, log)
            usage.update(used)
            sources.update(where)
            summary.append(line)
            ok &= good
            for why in missing.values():
                kind = ("not a definition (a structure, class or inductive type)" if "is not a definition" in why else
                        "a structure projection" if "structure projection" in why else
                        "defined by recursion or pattern matching" if "recursion or pattern" in why else
                        "rejected by Lean" if "no checked reading" in why else
                        "no selector construction" if "no reading yet" in why else why[:60])
                reasons[kind] = reasons.get(kind, 0) + 1
        if full:
            cards.save_usage("glossary", usage, sources, "glossary")
            total, used_rules = cards.write_cards(work)
            print(f"Rule cards: {used_rules} of {total} rules used by the checked texts; see RULE-CARDS.md", flush=True)
    log.insert(1, "\n".join(f"- {s}" for s in summary) + "\n")
    if full:
        GLOSSARY.mkdir(parents=True, exist_ok=True)
        (GLOSSARY / "RUN-LOG.md").write_text("\n".join(log))
    print("Reasons without a definition:", json.dumps(reasons, indent=1, ensure_ascii=False))
    if not ok:
        raise SystemExit("Glossary verification failed; see the messages above.")


if __name__ == "__main__":
    main()
