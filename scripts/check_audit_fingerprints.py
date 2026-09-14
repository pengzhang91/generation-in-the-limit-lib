#!/usr/bin/env python3
"""Check human-audit applicability fingerprints against current Lean declarations."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = REPOSITORY_ROOT / "GenLimitLean"
EXPORTER = LEAN_ROOT / "AuditFingerprintExport.lean"
DEFAULT_MANIFEST_DIRECTORY = (
    LEAN_ROOT / "AuditRecords" / "Human" / "Fingerprints"
)
PREFIX = "AUDIT_FINGERPRINT "
VALID_STATUSES = {"current", "needs-review"}
SHA256_PATTERN = re.compile(r"[0-9a-f]{64}")


def anchor_key(anchor: dict[str, Any]) -> tuple[str, str, str]:
    return (
        anchor["audit_id"],
        anchor["aspect"],
        anchor["declaration"],
    )


def export_current_anchors() -> dict[tuple[str, str, str], dict[str, str]]:
    process = subprocess.run(
        ["lake", "env", "lean", EXPORTER.name],
        cwd=LEAN_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    combined_output = process.stdout + process.stderr
    if process.returncode != 0:
        print(combined_output, file=sys.stderr, end="")
        raise RuntimeError("Lean audit-fingerprint export failed")

    anchors: dict[tuple[str, str, str], dict[str, str]] = {}
    for line in combined_output.splitlines():
        position = line.find(PREFIX)
        if position < 0:
            continue
        payload = json.loads(line[position + len(PREFIX) :])
        expression = payload.pop("expression")
        payload["sha256"] = hashlib.sha256(expression.encode("utf-8")).hexdigest()
        key = anchor_key(payload)
        if key in anchors:
            raise RuntimeError(f"duplicate exported audit anchor: {key}")
        anchors[key] = payload

    if not anchors:
        raise RuntimeError("Lean exporter produced no audit fingerprints")
    return anchors


def load_manifests(directory: Path) -> list[dict[str, Any]]:
    manifests = []
    for path in sorted(directory.glob("*.json")):
        with path.open(encoding="utf-8") as handle:
            manifest = json.load(handle)
        manifest["_path"] = path
        manifests.append(manifest)
    if not manifests:
        raise RuntimeError(f"no audit fingerprint manifests found under {directory}")
    return manifests


def validate_manifest(manifest: dict[str, Any]) -> None:
    path = manifest["_path"]
    if manifest.get("schema_version") != 1:
        raise RuntimeError(f"{path}: expected schema_version 1")
    status = manifest.get("status")
    if status not in VALID_STATUSES:
        raise RuntimeError(f"{path}: invalid status {status!r}")
    candidate_baseline = manifest.get("candidate_baseline", False)
    if not isinstance(candidate_baseline, bool):
        raise RuntimeError(f"{path}: candidate_baseline must be Boolean")
    if candidate_baseline and status != "needs-review":
        raise RuntimeError(
            f"{path}: a candidate baseline must remain needs-review"
        )
    if candidate_baseline and not manifest.get("candidate_captured_at"):
        raise RuntimeError(
            f"{path}: a candidate baseline requires candidate_captured_at"
        )
    if status == "needs-review" and not manifest.get("review_note"):
        raise RuntimeError(f"{path}: needs-review requires a review_note")
    audit_id = manifest.get("audit_id")
    if not audit_id:
        raise RuntimeError(f"{path}: audit_id is required")
    anchors = manifest.get("anchors")
    if not isinstance(anchors, list) or not anchors:
        raise RuntimeError(f"{path}: a nonempty anchors list is required")
    seen: set[tuple[str, str]] = set()
    for anchor in anchors:
        key = (anchor.get("aspect"), anchor.get("declaration"))
        if key in seen:
            raise RuntimeError(f"{path}: duplicate anchor {key}")
        seen.add(key)
        if key[0] not in {"type", "value"} or not key[1]:
            raise RuntimeError(f"{path}: malformed anchor {key}")
        fingerprint = anchor.get("sha256", "")
        if not SHA256_PATTERN.fullmatch(fingerprint):
            raise RuntimeError(f"{path}: malformed SHA-256 for {key}")


def expected_anchor_map(manifest: dict[str, Any]) -> dict[tuple[str, str, str], str]:
    audit_id = manifest["audit_id"]
    return {
        (audit_id, anchor["aspect"], anchor["declaration"]): anchor["sha256"]
        for anchor in manifest["anchors"]
    }


def describe_key(key: tuple[str, str, str]) -> str:
    _audit_id, aspect, declaration = key
    return f"{declaration} ({aspect})"


def check_manifests(
    manifests: list[dict[str, Any]],
    current: dict[tuple[str, str, str], dict[str, str]],
) -> int:
    for manifest in manifests:
        validate_manifest(manifest)
    audit_ids = [manifest.get("audit_id") for manifest in manifests]
    duplicate_ids = sorted(
        audit_id for audit_id in set(audit_ids)
        if audit_ids.count(audit_id) > 1
    )
    if duplicate_ids:
        print(
            "Duplicate audit IDs: " + ", ".join(duplicate_ids),
            file=sys.stderr,
        )
        return 1
    known_audit_ids = {manifest["audit_id"] for manifest in manifests}
    unexpected_ids = sorted(
        {key[0] for key in current}.difference(known_audit_ids)
    )
    if unexpected_ids:
        print(
            "Unregistered exported audit IDs: " + ", ".join(unexpected_ids),
            file=sys.stderr,
        )
        return 1

    failed = False
    for manifest in manifests:
        audit_id = manifest["audit_id"]
        expected = expected_anchor_map(manifest)
        actual = {
            key: value for key, value in current.items()
            if key[0] == audit_id
        }
        differences: list[str] = []

        for key in sorted(expected):
            if key not in actual:
                differences.append(f"missing current anchor: {describe_key(key)}")
            elif expected[key] != actual[key]["sha256"]:
                differences.append(
                    f"changed: {describe_key(key)}\n"
                    f"    reviewed {expected[key]}\n"
                    f"    current  {actual[key]['sha256']}"
                )
        for key in sorted(set(actual).difference(expected)):
            differences.append(f"new unreviewed anchor: {describe_key(key)}")

        status = manifest["status"]
        if status == "current" and differences:
            failed = True
            print(f"NEEDS-REVIEW [{audit_id}]", file=sys.stderr)
            for difference in differences:
                print(f"  - {difference}", file=sys.stderr)
            print(
                "  Mark this manifest needs-review with a review_note, or "
                "refresh it only after the affected audit scope is reviewed.",
                file=sys.stderr,
            )
        elif status == "needs-review":
            label = "candidate baseline; " if manifest.get("candidate_baseline") else ""
            print(f"WARNING [{audit_id}] {label}remains needs-review")
            print(f"  review note: {manifest['review_note']}")
            for difference in differences:
                print(f"  - {difference}")
        else:
            print(f"CURRENT [{audit_id}] ({len(expected)} anchors)")

    return 1 if failed else 0


def dump_current(
    audit_id: str,
    current: dict[tuple[str, str, str], dict[str, str]],
) -> int:
    anchors = [
        {
            "aspect": key[1],
            "declaration": key[2],
            "sha256": value["sha256"],
        }
        for key, value in sorted(current.items())
        if key[0] == audit_id
    ]
    if not anchors:
        print(f"unknown exported audit ID: {audit_id}", file=sys.stderr)
        return 1
    print(json.dumps({"audit_id": audit_id, "anchors": anchors}, indent=2))
    return 0


def parse_arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest-directory",
        type=Path,
        default=DEFAULT_MANIFEST_DIRECTORY,
        help="directory containing tracked audit-fingerprint manifests",
    )
    parser.add_argument(
        "--dump",
        metavar="AUDIT_ID",
        help="print current hashes for review without modifying a baseline",
    )
    return parser.parse_args()


def main() -> int:
    arguments = parse_arguments()
    try:
        current = export_current_anchors()
        if arguments.dump:
            return dump_current(arguments.dump, current)
        manifests = load_manifests(arguments.manifest_directory)
        return check_manifests(manifests, current)
    except (
        OSError,
        RuntimeError,
        TypeError,
        KeyError,
        json.JSONDecodeError,
    ) as error:
        print(f"audit fingerprint check failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
