#!/usr/bin/env python3
"""Generate a declaration-level retrieval index from the compiled Lean library."""

from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path
from typing import Any


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = REPOSITORY_ROOT / "GenLimitLean"
EXPORTER = LEAN_ROOT / "DeclarationIndexExport.lean"
CLAIM_INDEX = REPOSITORY_ROOT / "registry" / "generated" / "index.json"
CARDS_OUTPUT = (
    REPOSITORY_ROOT / "registry" / "generated" / "declarations.jsonl"
)
INDEX_OUTPUT = (
    REPOSITORY_ROOT / "registry" / "generated" / "declaration-index.json"
)
SCHEMA_VERSION = "1.0.0"
PREFIX = "DECLARATION_INDEX "
PAPER_MODULE_PATTERN = re.compile(r"^GenLimit\.Paper([0-9]{2}A?)_")
VALID_KINDS = {
    "abbrev",
    "constructor",
    "definition",
    "inductive",
    "instance",
    "opaque",
    "postulate",
    "projection",
    "structure",
    "theorem",
}


class DeclarationIndexError(Exception):
    """A malformed export or stale dependency prevents index generation."""


def reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise DeclarationIndexError(f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


def load_json(path: Path) -> dict[str, Any]:
    try:
        with path.open(encoding="utf-8") as handle:
            value = json.load(handle, object_pairs_hook=reject_duplicate_keys)
    except (OSError, json.JSONDecodeError) as error:
        raise DeclarationIndexError(f"cannot read {relative(path)}: {error}")
    if not isinstance(value, dict):
        raise DeclarationIndexError(f"{relative(path)} must contain a JSON object")
    return value


def relative(path: Path) -> str:
    try:
        return path.resolve().relative_to(REPOSITORY_ROOT).as_posix()
    except ValueError:
        return str(path)


def run_exporter() -> list[dict[str, Any]]:
    process = subprocess.run(
        ["lake", "env", "lean", EXPORTER.name],
        cwd=LEAN_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    if process.returncode != 0:
        print(process.stdout, file=sys.stderr, end="")
        print(process.stderr, file=sys.stderr, end="")
        raise DeclarationIndexError("Lean declaration export failed")

    records: list[dict[str, Any]] = []
    for line in process.stdout.splitlines():
        if not line.startswith(PREFIX):
            continue
        try:
            record = json.loads(
                line[len(PREFIX) :], object_pairs_hook=reject_duplicate_keys
            )
        except json.JSONDecodeError as error:
            raise DeclarationIndexError(f"invalid Lean export record: {error}")
        if not isinstance(record, dict):
            raise DeclarationIndexError("Lean export record must be an object")
        records.append(record)

    if not records:
        raise DeclarationIndexError("Lean exporter produced no declarations")
    return records


def require_string(record: dict[str, Any], field: str, context: str) -> str:
    value = record.get(field)
    if not isinstance(value, str) or not value:
        raise DeclarationIndexError(f"{context}.{field} must be a nonempty string")
    return value


def require_string_list(
    record: dict[str, Any], field: str, context: str
) -> list[str]:
    value = record.get(field)
    if not isinstance(value, list) or not all(
        isinstance(item, str) and item for item in value
    ):
        raise DeclarationIndexError(f"{context}.{field} must be a string array")
    if len(value) != len(set(value)):
        raise DeclarationIndexError(
            f"{context}.{field} must be duplicate-free"
        )
    return value


def source_path_for_module(module: str) -> Path:
    components = module.split(".")
    if components == ["GenLimit"]:
        return LEAN_ROOT / "GenLimit.lean"
    return LEAN_ROOT.joinpath(*components).with_suffix(".lean")


def classify_module(module: str) -> tuple[str, str | None]:
    match = PAPER_MODULE_PATTERN.match(module)
    if match:
        return "paper", "P" + match.group(1)
    if module == "GenLimit.Core" or module.startswith("GenLimit.Core."):
        return "core", None
    if module == "GenLimit.Support" or module.startswith("GenLimit.Support."):
        return "support", None
    if module == "GenLimit.Bridges" or module.startswith("GenLimit.Bridges."):
        return "bridge", None
    return "library", None


def validate_exported_records(
    records: list[dict[str, Any]],
) -> dict[str, dict[str, Any]]:
    expected_fields = {
        "body_dependencies",
        "direct_abbreviation_target",
        "docstring",
        "kind",
        "module",
        "name",
        "safety",
        "source_line",
        "type",
        "type_dependencies",
    }
    by_name: dict[str, dict[str, Any]] = {}
    for record in records:
        name = require_string(record, "name", "export")
        context = f"export[{name}]"
        if set(record) != expected_fields:
            missing = sorted(expected_fields - set(record))
            extra = sorted(set(record) - expected_fields)
            raise DeclarationIndexError(
                f"{context} has wrong fields; missing={missing}, extra={extra}"
            )
        if name in by_name:
            raise DeclarationIndexError(f"duplicate exported declaration: {name}")
        if not name.startswith("GenLimit."):
            raise DeclarationIndexError(f"{context} is outside the GenLimit namespace")
        kind = require_string(record, "kind", context)
        if kind not in VALID_KINDS:
            raise DeclarationIndexError(f"{context}.kind is invalid: {kind!r}")
        module = require_string(record, "module", context)
        if module != "GenLimit" and not module.startswith("GenLimit."):
            raise DeclarationIndexError(
                f"{context}.module is outside the GenLimit library: {module!r}"
            )
        source_path = source_path_for_module(module)
        if not source_path.is_file():
            raise DeclarationIndexError(
                f"{context}.module has no source file at {relative(source_path)}"
            )
        require_string(record, "type", context)
        record["type_dependencies"] = sorted(
            require_string_list(record, "type_dependencies", context)
        )
        record["body_dependencies"] = sorted(
            require_string_list(record, "body_dependencies", context)
        )
        if record["safety"] not in {"safe", "unsafe", "partial"}:
            raise DeclarationIndexError(f"{context}.safety is invalid")
        if record["source_line"] is not None and (
            not isinstance(record["source_line"], int)
            or isinstance(record["source_line"], bool)
            or record["source_line"] < 1
        ):
            raise DeclarationIndexError(
                f"{context}.source_line must be null or a positive integer"
            )
        if record["docstring"] is not None and not isinstance(
            record["docstring"], str
        ):
            raise DeclarationIndexError(
                f"{context}.docstring must be null or a string"
            )
        target = record["direct_abbreviation_target"]
        if target is not None and (not isinstance(target, str) or not target):
            raise DeclarationIndexError(
                f"{context}.direct_abbreviation_target must be null or a name"
            )
        by_name[name] = record

    names = set(by_name)
    for name, record in by_name.items():
        for field in ("type_dependencies", "body_dependencies"):
            missing_dependencies = sorted(set(record[field]) - names)
            if missing_dependencies:
                raise DeclarationIndexError(
                    f"export[{name}].{field} references unindexed declarations: "
                    + ", ".join(missing_dependencies)
                )
        target = record["direct_abbreviation_target"]
        if target is not None and target not in names:
            raise DeclarationIndexError(
                f"export[{name}] abbreviation target is not indexed: {target}"
            )
    return by_name


def resolve_canonical_names(
    records: dict[str, dict[str, Any]],
) -> dict[str, str]:
    resolved: dict[str, str] = {}

    def resolve(name: str, visiting: set[str]) -> str:
        if name in resolved:
            return resolved[name]
        if name in visiting:
            cycle = " -> ".join(sorted(visiting | {name}))
            raise DeclarationIndexError(f"abbreviation cycle: {cycle}")
        target = records[name]["direct_abbreviation_target"]
        canonical = name if target is None else resolve(target, visiting | {name})
        resolved[name] = canonical
        return canonical

    for name in sorted(records):
        resolve(name, set())
    return resolved


def load_claim_links() -> dict[str, list[str]]:
    claim_index = load_json(CLAIM_INDEX)
    mapping = claim_index.get("by_lean_declaration")
    if not isinstance(mapping, dict):
        raise DeclarationIndexError(
            f"{relative(CLAIM_INDEX)} lacks by_lean_declaration"
        )
    result: dict[str, list[str]] = {}
    for declaration, claim_ids in mapping.items():
        if not isinstance(declaration, str) or not isinstance(claim_ids, list):
            raise DeclarationIndexError("malformed by_lean_declaration facet")
        if not all(isinstance(claim_id, str) for claim_id in claim_ids):
            raise DeclarationIndexError(
                f"malformed claim IDs for declaration {declaration}"
            )
        result[declaration] = sorted(set(claim_ids))
    return result


def build_cards(
    exported: dict[str, dict[str, Any]], claim_links: dict[str, list[str]]
) -> list[dict[str, Any]]:
    missing_registered = sorted(set(claim_links) - set(exported))
    if missing_registered:
        raise DeclarationIndexError(
            "claim registry declarations missing from Lean export: "
            + ", ".join(missing_registered)
        )

    canonical_names = resolve_canonical_names(exported)
    aliases_by_canonical: dict[str, list[str]] = defaultdict(list)
    for name, canonical in canonical_names.items():
        if name != canonical:
            aliases_by_canonical[canonical].append(name)

    cards = []
    for name in sorted(exported):
        record = exported[name]
        module = record["module"]
        area, paper_label = classify_module(module)
        source_path = source_path_for_module(module)
        card = {
            "schema_version": SCHEMA_VERSION,
            "name": name,
            "canonical_name": canonical_names[name],
            "aliases": sorted(aliases_by_canonical.get(canonical_names[name], [])),
            "direct_abbreviation_target": record["direct_abbreviation_target"],
            "kind": record["kind"],
            "safety": record["safety"],
            "module": module,
            "source_path": relative(source_path),
            "source_line": record["source_line"],
            "area": area,
            "paper_label": paper_label,
            "type": record["type"],
            "docstring": record["docstring"],
            "type_dependencies": record["type_dependencies"],
            "body_dependencies": record["body_dependencies"],
            "registered_claim_ids": claim_links.get(name, []),
        }
        cards.append(card)
    return cards


def sorted_mapping(mapping: dict[str, list[str]]) -> dict[str, list[str]]:
    return {key: sorted(set(mapping[key])) for key in sorted(mapping)}


def build_index(cards: list[dict[str, Any]]) -> dict[str, Any]:
    by_area: dict[str, list[str]] = defaultdict(list)
    by_kind: dict[str, list[str]] = defaultdict(list)
    by_module: dict[str, list[str]] = defaultdict(list)
    by_paper: dict[str, list[str]] = defaultdict(list)
    by_claim: dict[str, list[str]] = defaultdict(list)
    by_name: dict[str, dict[str, Any]] = {}
    aliases: dict[str, str] = {}

    for line_number, card in enumerate(cards, start=1):
        name = card["name"]
        by_area[card["area"]].append(name)
        by_kind[card["kind"]].append(name)
        by_module[card["module"]].append(name)
        if card["paper_label"] is not None:
            by_paper[card["paper_label"]].append(name)
        for claim_id in card["registered_claim_ids"]:
            by_claim[claim_id].append(name)
        if card["canonical_name"] != name:
            aliases[name] = card["canonical_name"]
        by_name[name] = {
            "jsonl_line": line_number,
            "kind": card["kind"],
            "module": card["module"],
            "canonical_name": card["canonical_name"],
            "registered_claim_ids": card["registered_claim_ids"],
        }

    counts_by_kind = {
        kind: len(names) for kind, names in sorted(by_kind.items())
    }
    counts_by_area = {
        area: len(names) for area, names in sorted(by_area.items())
    }
    return {
        "schema_version": SCHEMA_VERSION,
        "generated_from": "GenLimitLean/DeclarationIndexExport.lean",
        "declarations_file": relative(CARDS_OUTPUT),
        "counts": {
            "declarations": len(cards),
            "claim_linked_declarations": sum(
                bool(card["registered_claim_ids"]) for card in cards
            ),
            "direct_abbreviations": len(aliases),
            "by_area": counts_by_area,
            "by_kind": counts_by_kind,
        },
        "by_name": dict(sorted(by_name.items())),
        "by_area": sorted_mapping(by_area),
        "by_kind": sorted_mapping(by_kind),
        "by_module": sorted_mapping(by_module),
        "by_paper": sorted_mapping(by_paper),
        "by_registered_claim": sorted_mapping(by_claim),
        "alias_to_canonical": dict(sorted(aliases.items())),
    }


def render_cards(cards: list[dict[str, Any]]) -> str:
    return "".join(
        json.dumps(
            card, ensure_ascii=False, sort_keys=True, separators=(",", ":")
        )
        + "\n"
        for card in cards
    )


def render_index(index: dict[str, Any]) -> str:
    return json.dumps(index, ensure_ascii=False, sort_keys=True, indent=2) + "\n"


def atomic_write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix="." + path.name + ".", dir=str(path.parent)
    )
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as handle:
            handle.write(content)
        os.chmod(temporary_name, 0o644)
        os.replace(temporary_name, path)
    except Exception:
        try:
            os.unlink(temporary_name)
        except OSError:
            pass
        raise


def check_output(path: Path, expected: str) -> bool:
    if not path.exists():
        print(f"missing generated file: {relative(path)}")
        return False
    actual_bytes = path.read_bytes()
    expected_bytes = expected.encode("utf-8")
    if actual_bytes == expected_bytes:
        return True
    print(f"stale generated file: {relative(path)}")
    try:
        actual = actual_bytes.decode("utf-8")
    except UnicodeDecodeError:
        print("generated file is not valid UTF-8")
        return False
    difference = difflib.unified_diff(
        actual.splitlines(),
        expected.splitlines(),
        fromfile=relative(path),
        tofile=relative(path) + " (expected)",
        lineterm="",
    )
    for index, line in enumerate(difference):
        if index >= 80:
            print(
                "... diff truncated; regenerate with "
                "python3 scripts/build_declaration_index.py"
            )
            break
        print(line)
    return False


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="compare generated files without writing them",
    )
    return parser.parse_args()


def main() -> int:
    arguments = parse_arguments()
    try:
        exported = validate_exported_records(run_exporter())
        claim_links = load_claim_links()
        cards = build_cards(exported, claim_links)
        index = build_index(cards)
        payloads = {
            CARDS_OUTPUT: render_cards(cards),
            INDEX_OUTPUT: render_index(index),
        }
        if arguments.check:
            results = [
                check_output(path, content) for path, content in payloads.items()
            ]
            clean = all(results)
            if not clean:
                print(
                    "regenerate with: python3 scripts/build_declaration_index.py"
                )
                return 1
        else:
            for path, content in payloads.items():
                atomic_write(path, content)
                print(f"wrote {relative(path)}")
        print(
            "declaration index valid: "
            f"{len(cards)} declaration(s), "
            f"{index['counts']['claim_linked_declarations']} claim-linked, "
            f"{index['counts']['direct_abbreviations']} direct abbreviation(s)"
        )
        return 0
    except (DeclarationIndexError, OSError, TypeError, KeyError) as error:
        print(f"declaration index error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
