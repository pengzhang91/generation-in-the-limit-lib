#!/usr/bin/env python3
"""Build the main-result human-audit planning inventory from existing evidence."""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import date
import hashlib
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "GenLimitLean/AuditRecords/Human"
SCOPE = DIRECTORY / "MainTheoremScope.json"
JSON_OUTPUT = DIRECTORY / "MainTheoremAudit.json"
MARKDOWN_OUTPUT = DIRECTORY / "MainTheoremAudit.md"
LABELS = {
    "current": "已有现行人审",
    "partial-review": "仅部分规格有人审",
    "needs-review": "需续审",
    "not-reviewed": "待首次人审",
    "no-formalization": "原陈述无形式化",
}


def read(path):
    return json.loads(path.read_text(encoding="utf-8"))


def relative(path):
    return path.relative_to(ROOT).as_posix()


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def cell(value):
    return str(value).replace("|", "\\|").replace("\n", " ")


def local_link(label, path, line=None):
    suffix = "#L{}".format(line) if line else ""
    return "[{}](../../../{}{})".format(cell(label), path, suffix)


def load_inventory(as_of, snapshot_head=None):
    snapshot_head = snapshot_head or git("rev-parse", "HEAD")
    policy = read(SCOPE)
    manifest = read(ROOT / "registry/registry.json")
    entries = {p: read(ROOT / p) for p in manifest["paper_entries"]}
    if {p["entry"] for p in policy["papers"]} != set(entries):
        raise ValueError("planning scope must cover every registered paper exactly once")
    if len(policy["papers"]) != len(entries):
        raise ValueError("duplicate paper in planning scope")
    umbrellas = {
        line[len("import "):]
        for line in (ROOT / "GenLimitLean/GenLimit.lean").read_text().splitlines()
        if line.startswith("import GenLimit.Paper")
    }
    if umbrellas != {e["paper"]["umbrella_module"] for e in entries.values()}:
        raise ValueError("planning scope does not match the library umbrellas")
    declarations = {}
    for line in (ROOT / "registry/generated/declarations.jsonl").read_text().splitlines():
        declaration = json.loads(line)
        declarations[declaration["name"]] = declaration
    fingerprints = []
    anchor_map = {}
    for path in sorted((DIRECTORY / "Fingerprints").glob("*.json")):
        record = read(path)
        fingerprints.append(path)
        for anchor in record["anchors"]:
            if anchor["aspect"] == "type":
                anchor_map.setdefault(anchor["declaration"], []).append({
                    "audit_id": record["audit_id"],
                    "path": relative(path),
                    "status": record["status"],
                    "human_reviewed_checkpoint": record["human_reviewed_checkpoint"],
                    "applicability_scope": record["applicability_scope"],
                })
    papers = []
    all_selected = set()
    for selection in policy["papers"]:
        entry = entries[selection["entry"]]
        claims = {c["id"]: c for c in entry["claims"]}
        if len(selection["claim_ids"]) != len(set(selection["claim_ids"])):
            raise ValueError("duplicate selected claim")
        rows = []
        for claim_id in selection["claim_ids"]:
            claim = claims[claim_id]
            if claim_id in all_selected:
                raise ValueError("claim counted in multiple papers")
            all_selected.add(claim_id)
            candidates = [(link["declaration"], link["role"]) for link in claim["lean_links"]]
            for name in policy.get("audit_declaration_aliases", {}).get(claim_id, []):
                if not any(a["kind"] == "human-correspondence" for a in claim["audit_refs"]):
                    raise ValueError("reviewed facade requires a claim-scoped human record")
                candidates.append((name, "reviewed-facade"))
            evidence = []
            for name, role in candidates:
                if name not in declarations:
                    raise ValueError("declaration missing from compiled index: " + name)
                for record in anchor_map.get(name, []):
                    evidence.append(dict(record, declaration=name, role=role))
            direct = [e for e in evidence if e["role"].startswith("formalizes") or e["role"] == "reviewed-facade"]
            active = [e for e in direct if e["status"] == "current"]
            core = [e for e in evidence if e["role"] == "provides-core" and e["status"] == "current"]
            coverage = claim["formalization"]["coverage"]
            if coverage == "none":
                status = "no-formalization"
            elif active:
                status = "current"
            elif core:
                status = "partial-review"
            elif any(e["status"] == "needs-review" for e in direct):
                status = "needs-review"
            else:
                status = "not-reviewed"
            links = []
            for link in claim["lean_links"]:
                declaration = declarations[link["declaration"]]
                if not (ROOT / declaration["source_path"]).is_file():
                    raise ValueError("missing declaration source")
                links.append(dict(link, source_path=declaration["source_path"], source_line=declaration["source_line"]))
            rows.append({
                "claim_id": claim_id,
                "title": claim["title"],
                "kind": claim["kind"],
                "source_refs": claim["source_refs"],
                "source_assessment": claim["source_assessment"],
                "formalization": claim["formalization"],
                "lean_links": links,
                "audit_facades": [
                    dict(declarations[name], role="reviewed-facade", declaration=name)
                    for name in policy.get("audit_declaration_aliases", {}).get(claim_id, [])
                ],
                "human_status": status,
                "human_evidence": evidence,
                "claim_audit_refs": claim["audit_refs"],
                "review_note": policy.get("review_notes", {}).get(claim_id, ""),
                "related_claim_ids": policy.get("related_claims", {}).get(claim_id, []),
            })
        papers.append({
            "entry": selection["entry"],
            "paper_id": entry["paper"]["id"],
            "label": Path(selection["entry"]).stem,
            "title": entry["paper"]["title"],
            "paper_map": entry["paper"]["paper_map"],
            "source_editions": entry["source_editions"],
            "scope_basis": selection["scope_basis"],
            "scope_kind": selection["scope_kind"],
            "results": rows,
            "outside_scope_claim_ids": sorted(set(claims) - set(selection["claim_ids"])),
        })
    rows = [row for paper in papers for row in paper["results"]]
    inputs = [Path(__file__).resolve(), SCOPE, ROOT / "registry/registry.json", DIRECTORY / "README.md",
              ROOT / "registry/generated/declarations.jsonl", ROOT / "GenLimitLean/GenLimit.lean"]
    inputs += [ROOT / path for path in entries] + fingerprints
    mathematical_paths = git("ls-files", "--", "GenLimitLean/GenLimit").splitlines()
    inputs += [ROOT / path for path in mathematical_paths if path.endswith(".lean")]
    inputs += [p for p in [ROOT / "GenLimitLean/lean-toolchain", ROOT / "GenLimitLean/lake-manifest.json"] if p.is_file()]
    hashes = {relative(p): digest(p) for p in sorted(set(inputs))}
    return {
        "schema_version": 1,
        "as_of": as_of,
        "target": policy["target"],
        "selection_policy": policy["selection_policy"],
        "snapshot": {
            "kind": "working-tree-planning-inventory",
            "git_head": snapshot_head,
            "mathematical_code_matches_git_head": not bool(git("diff", snapshot_head, "--", "GenLimitLean/GenLimit")),
            "input_sha256": hashes,
            "note": "Includes local audit metadata. This inventory does not create a frozen release or a new human audit.",
        },
        "counts": {
            "papers": len(papers),
            "main_result_groups": len(rows),
            "human_status": dict(sorted(Counter(r["human_status"] for r in rows).items())),
            "formalization_coverage": dict(sorted(Counter(r["formalization"]["coverage"] for r in rows).items())),
            "by_formalization_and_human_status": {
                coverage: dict(sorted(Counter(r["human_status"] for r in rows if r["formalization"]["coverage"] == coverage).items()))
                for coverage in ["full", "partial", "none"]
            },
            "outside_scope_claims": sum(len(p["outside_scope_claim_ids"]) for p in papers),
        },
        "papers": papers,
    }


def render(report):
    counts = report["counts"]
    lines = [
        "# Main theorem human audit inventory", "",
        "截至 {}，覆盖当前库的 **{} 篇论文、{} 个主结果候选组**。目标是 Level 1：定理规格和决定其含义的定义与原文的对应关系。".format(report["as_of"], counts["papers"], counts["main_result_groups"]), "",
        "计数单位是 registry 的 claim group，不一定等于一个定理编号。多个版本、同一定理的分项和 overview/detailed 重述按下列范围处理。每篇的范围依据都列出；`main-text-candidates` 是保守候选范围，可在开始该篇审核时收窄。", "",
        "人审状态只适用于证据明确覆盖的声明、定义和来源版本。当前记录不自动覆盖其他实现、其他版本、构造或证明。AI 检查和 Lean kernel 检查均不算 human audit。", "",
        "有些已完成人审的 Lean 规格带有明确的来源限定，其形式化覆盖仍为 partial。这两件事分别记录；不会因为原论文其他分项尚未形式化，就撤销已有规格的人审。", "",
        "## 版本与使用方法", "",
        "数学代码基于 `{}`；当前数学代码与该提交{}。本表包含本地审核记录更新，尚未建立 rebuttal 冻结版本。完整输入文件哈希见 [JSON](MainTheoremAudit.json)。".format(report["snapshot"]["git_head"], "一致" if report["snapshot"]["mathematical_code_matches_git_head"] else "存在差异"), "",
        "主结果范围由 [MainTheoremScope.json](MainTheoremScope.json) 明确列出。表格由 registry、声明索引及现有人审指纹生成，不新增任何审核结论。刷新命令：", "",
        "```bash", "python3 scripts/build_main_theorem_audit.py --as-of {}".format(report["as_of"]),
        "python3 scripts/build_main_theorem_audit.py --check", "```", "",
        "先看已有完整形式化且待首次人审的项；有旧人审的项仅续审受影响范围。部分形式化应先明确实际 Lean 规格和缺口，再审核已有部分。无原陈述形式化的项单列为 gap；反例、修正和条件性结论不能代替原陈述。", "",
        "## 总数", "", "| 人审状态 | 主结果组数 |", "|---|---:|",
    ]
    lines += ["| {} | {} |".format(label, counts["human_status"].get(status, 0)) for status, label in LABELS.items()]
    lines += ["", "形式化覆盖按现有注册范围统计：完整 {} 组，部分 {} 组，无原陈述形式化 {} 组。它与上表是同一批结果的不同维度，不能相加。".format(*(counts["formalization_coverage"].get(k, 0) for k in ["full", "partial", "none"])), "",
              "待首次人审的 {} 组中，{} 组已有完整注册规格，{} 组只有部分形式化。".format(counts["human_status"].get("not-reviewed", 0), counts["by_formalization_and_human_status"]["full"].get("not-reviewed", 0), counts["by_formalization_and_human_status"]["partial"].get("not-reviewed", 0)), "",
              "已有现行人审不等于整篇 paper 已审完。仅部分规格有人审仍有未覆盖范围；无原陈述形式化包括明确不计划按字面证明的错误原陈述。", "",
              "## 按论文汇总", "", "| Paper | 候选组 | 现行人审 | 部分人审 | 续审 | 首次人审 | 无原陈述形式化 |", "|---|---:|---:|---:|---:|---:|---:|"]
    for paper in report["papers"]:
        counter = Counter(r["human_status"] for r in paper["results"])
        lines.append("| [{}](#{}) | {} | {} | {} | {} | {} | {} |".format(paper["label"], paper["label"].lower(), len(paper["results"]), *(counter.get(s, 0) for s in LABELS)))
    for paper in report["papers"]:
        lines += ["", "## " + paper["label"], "", paper["title"], "",
                  "范围：{} (`{}`)".format(paper["scope_basis"], paper["scope_kind"]), "",
                  "依据：{}；{}。".format(local_link("registry", paper["entry"]), local_link("PaperMap", paper["paper_map"])), "",
                  "| 论文结果 | Lean 声明 | 形式化 | 人审状态与证据 |", "|---|---|---|---|"]
        for row in paper["results"]:
            refs = [r for r in row["source_refs"] if not r["locator"].startswith(("Definition", "Proof", "Algorithm"))]
            ref = (refs or row["source_refs"])[0]
            editions = {e["id"]: e for e in paper["source_editions"]}
            edition = editions[ref["edition"]]
            locator = cell(ref["locator"])
            source = "[{}]({})".format(locator, edition["url"]) if edition.get("url") else locator
            source += " — " + cell(edition.get("label", ref["edition"]))
            if ref.get("pages"):
                source += "; p. " + cell(ref["pages"])
            formal = [l for l in row["lean_links"] if l["role"].startswith("formalizes")]
            display = row["audit_facades"] + (formal or row["lean_links"])
            shown = display[:2]
            names = [local_link("`" + l["declaration"].split(".")[-1] + "`", l["source_path"], l["source_line"]) + (" ({})".format(l["role"]) if not formal else "") for l in shown]
            if len(display) > 2:
                names.append("其余见 JSON")
            coverage = row["formalization"]["coverage"]
            coverage_text = {"full": "完整（注册范围）", "partial": "部分", "none": "无原陈述形式化"}[coverage]
            reasons = row["formalization"].get("reason_codes", [])
            if reasons:
                coverage_text += "; " + cell(", ".join(reasons))
            notes = [LABELS[row["human_status"]]]
            evidence = {}
            for item in row["human_evidence"]:
                direct = item["role"].startswith("formalizes") or item["role"] == "reviewed-facade"
                relevant = (
                    row["human_status"] == "current" and direct and item["status"] == "current"
                    or row["human_status"] == "partial-review" and item["status"] == "current"
                    or row["human_status"] == "needs-review" and direct and item["status"] == "needs-review"
                )
                if relevant:
                    evidence[item["path"]] = item
            for path, item in sorted(evidence.items()):
                notes.append(local_link(item["audit_id"], path) + " ({})".format(item["status"]))
            if row["review_note"]:
                notes.append(cell(row["review_note"]))
            if row["source_assessment"]["status"] != "no-known-issue":
                notes.append("source: " + row["source_assessment"]["status"])
            lines.append("| {} | {} | {} | {} |".format(source, "; ".join(names) or "—", coverage_text, "; ".join(notes)))
        lines += ["", "表外的 {} 个 registry claim 属于定义、支撑结果、其他版本或重复陈述等；完整 ID 保留在 JSON 的 `outside_scope_claim_ids`，不视为已审核。".format(len(paper["outside_scope_claim_ids"]))]
    lines += ["", "## 形式化缺口索引", "",
              "下列结果无原陈述形式化。部分项有修正、反例或语义核心；是否需要补齐应按 source assessment、disposition 和缺失组件判断，不自动成为证明任务。", "",
              "| Paper | 来源结果 | 处理性质 | Claim ID |", "|---|---|---|---|"]
    for paper in report["papers"]:
        for row in paper["results"]:
            if row["formalization"]["coverage"] == "none":
                disposition = row["formalization"]["disposition"] + "; source: " + row["source_assessment"]["status"]
                lines.append("| [{}](#{}) | {} | {} | `{}` |".format(paper["label"], paper["label"].lower(), cell(row["source_refs"][0]["locator"]), disposition, row["claim_id"]))
    lines.append("")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--as-of", help="inventory date, YYYY-MM-DD")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    as_of = args.as_of or (read(JSON_OUTPUT)["as_of"] if JSON_OUTPUT.exists() else date.today().isoformat())
    date.fromisoformat(as_of)
    # Keep the recorded revision when checking: committing the inventory must
    # not invalidate it. All current input contents are still hashed below.
    snapshot_head = read(JSON_OUTPUT)["snapshot"]["git_head"] if args.check and JSON_OUTPUT.exists() else None
    report = load_inventory(as_of, snapshot_head=snapshot_head)
    payloads = {
        JSON_OUTPUT: json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        MARKDOWN_OUTPUT: render(report),
    }
    for path, payload in payloads.items():
        if args.check:
            if not path.exists() or path.read_text(encoding="utf-8") != payload:
                raise ValueError("stale generated inventory: " + relative(path))
        else:
            path.write_text(payload, encoding="utf-8")
    print(json.dumps(report["counts"], ensure_ascii=False, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (KeyError, ValueError) as exc:
        print("audit inventory error: " + str(exc), file=sys.stderr)
        sys.exit(1)
