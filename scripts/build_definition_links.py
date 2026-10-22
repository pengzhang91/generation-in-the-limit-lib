#!/usr/bin/env python3
"""Generate GitHub definition links for a Lean file from the declaration index."""

from __future__ import annotations

import argparse
from collections import Counter
import json
import os
from pathlib import Path
import sys
from urllib.parse import quote


ROOT = Path(__file__).resolve().parents[1]
CARDS = ROOT / "registry/generated/declarations.jsonl"
DEFAULT_SOURCE = Path(
    "GenLimitLean/GenLimit/"
    "Paper04_ExploringFacetsOfLanguageGeneration/Results/Overview.lean"
)
DEFAULT_OUTPUT = ROOT / "registry/generated/definition-links/P04_Overview.md"
DEFINITION_KINDS = {
    "abbrev", "constructor", "definition", "inductive", "opaque",
    "projection", "structure",
}


def load_cards():
    cards = {}
    for line in CARDS.read_text(encoding="utf-8").splitlines():
        card = json.loads(line)
        if card["name"] in cards:
            raise ValueError("duplicate declaration: " + card["name"])
        cards[card["name"]] = card
    return cards


def definition_dependencies(names, cards):
    """Follow definition types and bodies, stopping at theorem proof bodies."""
    found = set()
    pending = list(names)
    while pending:
        name = pending.pop()
        if name in found:
            continue
        card = cards[name]
        if card["kind"] not in DEFINITION_KINDS:
            continue
        found.add(name)
        pending.extend(card["type_dependencies"] + card["body_dependencies"])
    return sorted(found)


def source_link(card, output):
    source = ROOT / card["source_path"]
    if not source.is_file():
        raise ValueError("missing source file: " + card["source_path"])
    line = card["source_line"]
    if line is not None and not 1 <= line <= len(
        source.read_text(encoding="utf-8").splitlines()
    ):
        raise ValueError("source position is out of date: " + card["name"])
    relative = Path(os.path.relpath(source, output.parent)).as_posix()
    return quote(relative, safe="/") + ("#L{}".format(line) if line else "")


def render(source, output, cards):
    declarations = sorted(
        (c for c in cards.values() if c["source_path"] == source.as_posix()),
        key=lambda c: (c["source_line"] or sys.maxsize, c["name"]),
    )
    if not declarations:
        raise ValueError("no indexed declarations in " + source.as_posix())
    title = (
        "P04 overview definition links" if source == DEFAULT_SOURCE
        else "Definition links for " + source.name
    )
    lines = [
        "# " + title, "",
        "Click a symbol to open the source file at its definition on GitHub.", "",
        "Source: [`{}`]({}).".format(source.as_posix(), source_link(dict(declarations[0], source_line=None), output)), "",
        "Each section lists project symbols used in that declaration's type. "
        "The lookup at the end also follows definitions used inside those symbols. "
        "Lean and Mathlib symbols are outside this project index.", "",
    ]

    def table(names):
        rows = ["| Symbol | Defined in |", "|---|---|"]
        for name in names:
            card = cards[name]
            location = Path(card["source_path"]).name
            if card["source_line"]:
                location += ":{}".format(card["source_line"])
            rows.append("| [`{}`]({}) | `{}` |".format(name, source_link(card, output), location))
        return rows

    short_names = Counter(c["name"].rsplit(".", 1)[-1] for c in declarations)
    roots = set()
    for card in declarations:
        short = card["name"].rsplit(".", 1)[-1]
        lines += ["## " + (short if short_names[short] == 1 else card["name"]), "",
                  "[View source]({})".format(source_link(card, output)), ""]
        names = sorted(set(card["type_dependencies"]))
        roots.update(names)
        lines += table(names) if names else ["No project symbols occur in this declaration's type."]
        lines.append("")

    definitions = definition_dependencies(roots, cards)
    lines += ["## Definition lookup", "",
              "Use your browser's Find command to locate a name while following definitions.", "",
              "<details>", "<summary>All {} reachable project definitions</summary>".format(len(definitions)), ""]
    lines += table(definitions)
    lines += ["", "</details>", "",
              "Generated from the [declaration index]({}). ".format(
                  quote(Path(os.path.relpath(CARDS, output.parent)).as_posix(), safe="/"))
              + "See the [generator instructions]({}) to refresh this page "
              "or generate links for another Lean file.".format(
                  quote(Path(os.path.relpath(ROOT / "registry/README.md", output.parent)).as_posix(), safe="/")), ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?", type=Path, default=DEFAULT_SOURCE,
                        help="repository-relative Lean file (default: P04 Results/Overview.lean)")
    parser.add_argument("--output", type=Path, help="Markdown output; required for other Lean files")
    parser.add_argument("--check", action="store_true", help="check without writing files")
    args = parser.parse_args()
    source = (ROOT / args.source).resolve().relative_to(ROOT)
    if not (ROOT / source).is_file() or source.suffix != ".lean":
        raise ValueError("not a Lean source file: " + source.as_posix())
    if source != DEFAULT_SOURCE and args.output is None:
        raise ValueError("--output is required when selecting another Lean file")
    output = (ROOT / args.output).resolve() if args.output else DEFAULT_OUTPUT
    output_relative = output.relative_to(ROOT)
    if output.suffix != ".md":
        raise ValueError("--output must name a Markdown (.md) file")
    payload = render(source, output, load_cards())
    if args.check:
        if not output.is_file() or output.read_text(encoding="utf-8") != payload:
            raise ValueError("stale definition links: " + str(output))
        print("definition links valid: " + str(output_relative))
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(payload, encoding="utf-8")
        print("wrote " + str(output_relative))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError) as error:
        print("definition links error: " + str(error), file=sys.stderr)
        sys.exit(2)
