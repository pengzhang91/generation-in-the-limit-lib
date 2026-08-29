#!/usr/bin/env python3
"""Validate the claim registry and render deterministic LLM projections."""

import argparse
import copy
import difflib
import json
import os
from pathlib import Path, PurePosixPath
import re
import tempfile


REPOSITORY_ROOT = Path(__file__).resolve().parent.parent
REGISTRY_ROOT = REPOSITORY_ROOT / "registry"
MANIFEST_PATH = REGISTRY_ROOT / "registry.json"

SCHEMA_VERSION = "0.1.0"

PAPER_ID_RE = re.compile(r"^paper:[a-z0-9][a-z0-9-]*$")
CLAIM_ID_RE = re.compile(r"^claim:[a-z0-9][a-z0-9:-]*$")
CARD_ID_RE = re.compile(r"^(?:paper|claim):[a-z0-9][a-z0-9:-]*$")
SLUG_RE = re.compile(r"^[a-z0-9][a-z0-9-]*$")
LEAN_NAME_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
)
LEAN_NAMESPACE_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
)
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
DATE_RE = re.compile(r"^[0-9]{4}-[0-9]{2}-[0-9]{2}$")
INVENTORY_LABEL_RE = re.compile(r"^#[0-9]+[A-Z]?$")

FORMALIZING_ROLES = {
    "formalizes",
    "formalizes-direction",
    "formalizes-special-case",
    "formalizes-stronger-result",
    "formalizes-weaker-result",
}
WHOLE_CLAIM_ROLES = {
    "formalizes",
    "formalizes-stronger-result",
}
COMPONENT_CAPABLE_ROLES = FORMALIZING_ROLES | {
    "corrects",
    "provides-core",
    "implements-construction",
}
ROLE_RELATIONSHIPS = {
    "formalizes": {"exact", "faithful-equivalent", "faithful-specialization"},
    "formalizes-stronger-result": {"faithful-generalization", "strengthened"},
    "formalizes-direction": {"weakened-special-case"},
    "formalizes-special-case": {"weakened-special-case"},
    "formalizes-weaker-result": {
        "weakened-special-case",
        "related-materially-different",
    },
    "corrects": {
        "exact",
        "faithful-equivalent",
        "faithful-specialization",
        "faithful-generalization",
        "strengthened",
        "corrected",
    },
    "provides-core": {
        "weakened-special-case",
        "related-materially-different",
        "faithful-specialization",
    },
    "implements-construction": {
        "exact",
        "faithful-equivalent",
        "faithful-specialization",
        "corrected",
        "related-materially-different",
    },
    "mirrors-construction": {"related-materially-different"},
    "refutes": {"refutation"},
}

EXPECTED_GENERATED_OUTPUTS = {
    "cards": "registry/generated/cards.jsonl",
    "index": "registry/generated/index.json",
    "lean_audit": "GenLimitLean/RegistryAudit.lean",
}


class RegistryError(Exception):
    pass


def reject_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise RegistryError("duplicate JSON key: {!r}".format(key))
        result[key] = value
    return result


def reject_nonfinite_number(value):
    raise RegistryError("non-finite JSON number is not permitted: {}".format(value))


def load_json(path):
    try:
        with path.open("r", encoding="utf-8") as handle:
            return json.load(
                handle,
                object_pairs_hook=reject_duplicate_keys,
                parse_constant=reject_nonfinite_number,
            )
    except RegistryError:
        raise
    except (OSError, json.JSONDecodeError) as exc:
        raise RegistryError("cannot read {}: {}".format(relative(path), exc))


def relative(path):
    try:
        return path.resolve().relative_to(REPOSITORY_ROOT).as_posix()
    except ValueError:
        return str(path)


def require_object(value, context):
    if not isinstance(value, dict):
        raise RegistryError("{} must be an object".format(context))


def require_array(value, context, nonempty=False):
    if not isinstance(value, list):
        raise RegistryError("{} must be an array".format(context))
    if nonempty and not value:
        raise RegistryError("{} must not be empty".format(context))


def require_string(value, context, nonempty=True):
    if not isinstance(value, str):
        raise RegistryError("{} must be a string".format(context))
    if nonempty and not value:
        raise RegistryError("{} must not be empty".format(context))


def require_keys(value, required, optional, context):
    require_object(value, context)
    required = set(required)
    optional = set(optional)
    missing = sorted(required - set(value))
    extra = sorted(set(value) - required - optional)
    if missing:
        raise RegistryError("{} is missing keys: {}".format(context, ", ".join(missing)))
    if extra:
        raise RegistryError("{} has unknown keys: {}".format(context, ", ".join(extra)))


def require_enum(value, choices, context):
    if value not in choices:
        raise RegistryError(
            "{} must be one of {}; found {!r}".format(
                context, ", ".join(sorted(choices)), value
            )
        )


def require_pattern(value, pattern, context):
    require_string(value, context)
    if not pattern.fullmatch(value):
        raise RegistryError("{} has invalid form: {!r}".format(context, value))


def require_unique_strings(values, context, pattern=None, nonempty=False):
    require_array(values, context, nonempty=nonempty)
    seen = set()
    for index, value in enumerate(values):
        item_context = "{}[{}]".format(context, index)
        require_string(value, item_context)
        if pattern is not None and not pattern.fullmatch(value):
            raise RegistryError("{} has invalid form: {!r}".format(item_context, value))
        if value in seen:
            raise RegistryError("{} repeats {!r}".format(context, value))
        seen.add(value)


def validate_repository_path(value, context, must_exist=True):
    require_string(value, context)
    if "\\" in value:
        raise RegistryError("{} must use forward slashes".format(context))
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts:
        raise RegistryError("{} must be a safe repository-relative path".format(context))
    resolved = REPOSITORY_ROOT.joinpath(*path.parts)
    if must_exist and not resolved.exists():
        raise RegistryError("{} does not exist: {}".format(context, value))
    return resolved


def validate_module(module, context):
    require_pattern(module, LEAN_NAME_RE, context)
    module_path = REPOSITORY_ROOT / "GenLimitLean"
    for segment in module.split("."):
        module_path = module_path / segment
    module_path = module_path.with_suffix(".lean")
    if not module_path.is_file():
        raise RegistryError(
            "{} does not map to a Lean source file: {}".format(context, relative(module_path))
        )


def enum_from(schema, definition, property_name=None):
    node = schema["$defs"][definition]
    if property_name is not None:
        node = node["properties"][property_name]
    return set(node["enum"])


class Contract:
    def __init__(self, schema):
        self.coverages = enum_from(schema, "coverage")
        self.source_kinds = enum_from(schema, "sourceEdition", "kind")
        self.source_relation_types = enum_from(schema, "sourceRelation", "type")
        self.inventory_scopes = enum_from(schema, "claimInventory", "scope")
        self.inventory_completeness = enum_from(
            schema, "claimInventory", "completeness"
        )
        self.claim_kinds = enum_from(schema, "claim", "kind")
        self.novelties = enum_from(schema, "claim", "novelty")
        self.source_item_kinds = enum_from(schema, "sourceRef", "item_kind")
        self.source_assessments = enum_from(schema, "sourceAssessment", "status")
        self.dispositions = enum_from(schema, "formalization", "disposition")
        self.lean_roles = enum_from(schema, "leanLink", "role")
        self.source_relationships = enum_from(
            schema, "leanLink", "source_relationship"
        )
        self.claim_relation_types = enum_from(schema, "claimRelation", "type")
        self.audit_kinds = enum_from(schema, "auditRef", "kind")


def validate_manifest(manifest):
    context = "registry/registry.json"
    require_keys(
        manifest,
        {
            "schema_version",
            "registry_status",
            "coverage_policy",
            "entry_schema",
            "paper_entries",
            "generated_outputs",
        },
        set(),
        context,
    )
    if manifest["schema_version"] != SCHEMA_VERSION:
        raise RegistryError(
            "{} schema_version must be {}".format(context, SCHEMA_VERSION)
        )
    require_enum(manifest["registry_status"], {"pilot", "active"}, context + ".registry_status")
    require_enum(
        manifest["coverage_policy"],
        {"listed-entries-only", "umbrella-complete"},
        context + ".coverage_policy",
    )
    schema_path = validate_repository_path(
        manifest["entry_schema"], context + ".entry_schema"
    )
    require_unique_strings(
        manifest["paper_entries"], context + ".paper_entries", nonempty=True
    )
    for index, entry_path in enumerate(manifest["paper_entries"]):
        validate_repository_path(
            entry_path, "{}.paper_entries[{}]".format(context, index)
        )
        if not entry_path.startswith("registry/papers/") or not entry_path.endswith(".json"):
            raise RegistryError(
                "{}.paper_entries[{}] must name registry/papers/*.json".format(
                    context, index
                )
            )

    discovered = sorted(
        relative(path) for path in (REGISTRY_ROOT / "papers").glob("*.json")
    )
    if sorted(manifest["paper_entries"]) != discovered:
        raise RegistryError(
            "registry/registry.json paper_entries must list every registry/papers/*.json; "
            "manifest={}, discovered={}".format(
                sorted(manifest["paper_entries"]), discovered
            )
        )

    outputs = manifest["generated_outputs"]
    require_keys(outputs, {"cards", "index", "lean_audit"}, set(), context + ".generated_outputs")
    if outputs != EXPECTED_GENERATED_OUTPUTS:
        raise RegistryError(
            "{}.generated_outputs must equal the protected v0 mapping: {}".format(
                context, EXPECTED_GENERATED_OUTPUTS
            )
        )
    for name, output_path in EXPECTED_GENERATED_OUTPUTS.items():
        validate_repository_path(
            output_path,
            "{}.generated_outputs.{}".format(context, name),
            must_exist=False,
        )
    return schema_path


def validate_source_edition(source, context, contract, source_ids):
    require_keys(
        source,
        {"id", "kind", "label", "relations"},
        {"identifier", "url", "version_date", "pdf_sha256"},
        context,
    )
    require_pattern(source["id"], SLUG_RE, context + ".id")
    if source["id"] in source_ids:
        raise RegistryError("{} repeats source edition {!r}".format(context, source["id"]))
    source_ids.add(source["id"])
    require_enum(source["kind"], contract.source_kinds, context + ".kind")
    require_string(source["label"], context + ".label")
    if "identifier" in source:
        require_string(source["identifier"], context + ".identifier")
    if "url" in source:
        require_string(source["url"], context + ".url")
        if not re.match(r"^https?://", source["url"]):
            raise RegistryError("{}.url must use http or https".format(context))
    if "version_date" in source:
        require_pattern(source["version_date"], DATE_RE, context + ".version_date")
    if "pdf_sha256" in source:
        require_pattern(source["pdf_sha256"], SHA256_RE, context + ".pdf_sha256")
    require_array(source["relations"], context + ".relations")
    for index, relation in enumerate(source["relations"]):
        relation_context = "{}.relations[{}]".format(context, index)
        require_keys(relation, {"type", "target"}, {"notes"}, relation_context)
        require_enum(
            relation["type"], contract.source_relation_types, relation_context + ".type"
        )
        require_pattern(relation["target"], SLUG_RE, relation_context + ".target")
        if "notes" in relation:
            require_string(relation["notes"], relation_context + ".notes")


def validate_paper(paper, context, contract):
    require_keys(
        paper,
        {
            "id",
            "inventory_label",
            "aliases",
            "title",
            "authors",
            "year",
            "citation_key",
            "summary",
            "topics",
            "paper_map",
            "umbrella_module",
            "declaration_namespaces",
            "formalization_scope",
            "audit_refs",
        },
        set(),
        context,
    )
    require_pattern(paper["id"], PAPER_ID_RE, context + ".id")
    require_pattern(
        paper["inventory_label"], INVENTORY_LABEL_RE, context + ".inventory_label"
    )
    require_unique_strings(paper["aliases"], context + ".aliases")
    require_string(paper["title"], context + ".title")
    require_unique_strings(paper["authors"], context + ".authors", nonempty=True)
    if type(paper["year"]) is not int or paper["year"] < 1900:
        raise RegistryError("{}.year must be an integer at least 1900".format(context))
    require_string(paper["citation_key"], context + ".citation_key")
    require_string(paper["summary"], context + ".summary")
    require_unique_strings(paper["topics"], context + ".topics", SLUG_RE)
    validate_repository_path(paper["paper_map"], context + ".paper_map")
    validate_module(paper["umbrella_module"], context + ".umbrella_module")
    require_unique_strings(
        paper["declaration_namespaces"],
        context + ".declaration_namespaces",
        LEAN_NAMESPACE_RE,
        nonempty=True,
    )
    scope = paper["formalization_scope"]
    scope_context = context + ".formalization_scope"
    require_keys(scope, {"coverage", "summary", "specializations", "gaps"}, set(), scope_context)
    require_enum(scope["coverage"], contract.coverages, scope_context + ".coverage")
    require_string(scope["summary"], scope_context + ".summary")
    require_unique_strings(scope["specializations"], scope_context + ".specializations")
    require_unique_strings(scope["gaps"], scope_context + ".gaps")
    require_array(paper["audit_refs"], context + ".audit_refs")
    for index, audit_ref in enumerate(paper["audit_refs"]):
        validate_audit_ref(
            audit_ref, "{}.audit_refs[{}]".format(context, index), contract
        )


def validate_inventory(inventory, context, contract, source_ids):
    require_keys(
        inventory,
        {
            "source_edition",
            "scope",
            "scope_description",
            "completeness",
            "exclusions",
            "notes",
        },
        set(),
        context,
    )
    if inventory["source_edition"] not in source_ids:
        raise RegistryError(
            "{}.source_edition does not resolve: {!r}".format(
                context, inventory["source_edition"]
            )
        )
    require_enum(inventory["scope"], contract.inventory_scopes, context + ".scope")
    require_string(inventory["scope_description"], context + ".scope_description")
    require_enum(
        inventory["completeness"],
        contract.inventory_completeness,
        context + ".completeness",
    )
    require_unique_strings(inventory["exclusions"], context + ".exclusions")
    require_string(inventory["notes"], context + ".notes", nonempty=False)


def validate_source_ref(source_ref, context, contract, source_ids):
    require_keys(
        source_ref,
        {"edition", "locator", "item_kind"},
        {"pages", "section", "notes"},
        context,
    )
    if source_ref["edition"] not in source_ids:
        raise RegistryError(
            "{}.edition does not resolve: {!r}".format(context, source_ref["edition"])
        )
    require_string(source_ref["locator"], context + ".locator")
    require_enum(
        source_ref["item_kind"], contract.source_item_kinds, context + ".item_kind"
    )
    for key in ("pages", "section", "notes"):
        if key in source_ref:
            require_string(source_ref[key], context + "." + key)


def validate_component(component, context, contract):
    require_keys(
        component,
        {"id", "summary", "coverage", "disposition", "reason_codes"},
        set(),
        context,
    )
    require_pattern(component["id"], SLUG_RE, context + ".id")
    require_string(component["summary"], context + ".summary")
    require_enum(component["coverage"], contract.coverages, context + ".coverage")
    require_enum(
        component["disposition"], contract.dispositions, context + ".disposition"
    )
    require_unique_strings(component["reason_codes"], context + ".reason_codes", SLUG_RE)
    if component["coverage"] != "full" and not component["reason_codes"]:
        raise RegistryError("{} incomplete coverage requires a reason code".format(context))


def validate_interface(interface, context):
    require_keys(
        interface,
        set(),
        {"universe", "presentation", "access", "computability", "output"},
        context,
    )
    if not interface:
        raise RegistryError("{} must not be empty".format(context))
    for key, value in interface.items():
        require_string(value, context + "." + key)


def validate_lean_link(
    link,
    context,
    contract,
    claim_source_editions,
    component_ids,
    declaration_modules,
):
    require_keys(
        link,
        {
            "declaration",
            "module",
            "role",
            "source_editions",
            "source_relationship",
            "covers_components",
            "notes",
        },
        {"interface"},
        context,
    )
    require_pattern(link["declaration"], LEAN_NAME_RE, context + ".declaration")
    validate_module(link["module"], context + ".module")
    require_enum(link["role"], contract.lean_roles, context + ".role")
    require_unique_strings(
        link["source_editions"], context + ".source_editions", SLUG_RE, nonempty=True
    )
    unknown_editions = sorted(set(link["source_editions"]) - claim_source_editions)
    if unknown_editions:
        raise RegistryError(
            "{}.source_editions are not referenced by this claim: {}".format(
                context, ", ".join(unknown_editions)
            )
        )
    require_enum(
        link["source_relationship"],
        contract.source_relationships,
        context + ".source_relationship",
    )
    role = link["role"]
    relationship = link["source_relationship"]
    allowed_relationships = ROLE_RELATIONSHIPS.get(role)
    if allowed_relationships is None or relationship not in allowed_relationships:
        raise RegistryError(
            "{} role {!r} is incompatible with source_relationship {!r}".format(
                context, role, relationship
            )
        )
    require_unique_strings(
        link["covers_components"], context + ".covers_components", SLUG_RE
    )
    unknown_components = sorted(set(link["covers_components"]) - component_ids)
    if unknown_components:
        raise RegistryError(
            "{}.covers_components do not resolve: {}".format(
                context, ", ".join(unknown_components)
            )
        )
    if role in {"mirrors-construction", "refutes"} and link["covers_components"]:
        raise RegistryError("{} role {!r} cannot cover components".format(context, role))
    if (
        component_ids
        and set(link["covers_components"]) == component_ids
        and role
        in {
            "formalizes-direction",
            "formalizes-special-case",
            "formalizes-weaker-result",
            "provides-core",
            "implements-construction",
        }
    ):
        raise RegistryError(
            "{} non-whole-claim role {!r} cannot cover every component".format(
                context, role
            )
        )
    require_string(link["notes"], context + ".notes", nonempty=False)
    if "interface" in link:
        validate_interface(link["interface"], context + ".interface")

    declaration = link["declaration"]
    previous_module = declaration_modules.get(declaration)
    if previous_module is not None and previous_module != link["module"]:
        raise RegistryError(
            "{} is assigned conflicting modules: {} and {}".format(
                declaration, previous_module, link["module"]
            )
        )
    declaration_modules[declaration] = link["module"]


def validate_audit_ref(audit_ref, context, contract):
    require_keys(audit_ref, {"kind", "path", "scope"}, {"locator"}, context)
    require_enum(audit_ref["kind"], contract.audit_kinds, context + ".kind")
    validate_repository_path(audit_ref["path"], context + ".path")
    require_string(audit_ref["scope"], context + ".scope")
    if "locator" in audit_ref:
        require_string(audit_ref["locator"], context + ".locator")


def validate_claim(
    claim,
    context,
    contract,
    source_ids,
    claim_ids,
    declaration_modules,
    pending_relations,
):
    require_keys(
        claim,
        {
            "id",
            "kind",
            "title",
            "statement_summary",
            "source_refs",
            "source_assessment",
            "result_kinds",
            "assumptions",
            "tags",
            "novelty",
            "formalization",
            "lean_links",
            "relations",
            "audit_refs",
        },
        set(),
        context,
    )
    require_pattern(claim["id"], CLAIM_ID_RE, context + ".id")
    if claim["id"] in claim_ids:
        raise RegistryError("duplicate claim id: {}".format(claim["id"]))
    claim_ids.add(claim["id"])
    require_enum(claim["kind"], contract.claim_kinds, context + ".kind")
    require_string(claim["title"], context + ".title")
    require_string(claim["statement_summary"], context + ".statement_summary")
    require_array(claim["source_refs"], context + ".source_refs", nonempty=True)
    seen_source_refs = set()
    for index, source_ref in enumerate(claim["source_refs"]):
        source_context = "{}.source_refs[{}]".format(context, index)
        validate_source_ref(source_ref, source_context, contract, source_ids)
        key = (source_ref["edition"], source_ref["locator"])
        if key in seen_source_refs:
            raise RegistryError("{} duplicates edition and locator".format(source_context))
        seen_source_refs.add(key)
    claim_source_editions = {source_ref["edition"] for source_ref in claim["source_refs"]}

    assessment = claim["source_assessment"]
    assessment_context = context + ".source_assessment"
    require_keys(assessment, {"status", "notes"}, set(), assessment_context)
    require_enum(
        assessment["status"], contract.source_assessments, assessment_context + ".status"
    )
    require_string(assessment["notes"], assessment_context + ".notes", nonempty=False)
    if assessment["status"] in {
        "accepted-with-qualification",
        "corrected",
        "refuted",
        "disputed",
        "not-assessed",
    } and not assessment["notes"]:
        raise RegistryError("{} requires explanatory notes".format(assessment_context))

    require_unique_strings(
        claim["result_kinds"], context + ".result_kinds", SLUG_RE, nonempty=True
    )
    require_unique_strings(claim["assumptions"], context + ".assumptions", SLUG_RE)
    require_unique_strings(claim["tags"], context + ".tags", SLUG_RE)
    require_enum(claim["novelty"], contract.novelties, context + ".novelty")
    if claim["novelty"] == "open-problem" and claim["kind"] not in {
        "conjecture",
        "open-problem",
    }:
        raise RegistryError(
            "{} open-problem novelty requires conjecture or open-problem kind".format(
                context
            )
        )
    if claim["kind"] == "open-problem" and claim["novelty"] != "open-problem":
        raise RegistryError("{} open-problem kind requires open-problem novelty".format(context))

    formalization = claim["formalization"]
    formalization_context = context + ".formalization"
    require_keys(
        formalization,
        {"coverage", "disposition", "reason_codes", "notes", "components"},
        set(),
        formalization_context,
    )
    require_enum(
        formalization["coverage"], contract.coverages, formalization_context + ".coverage"
    )
    require_enum(
        formalization["disposition"],
        contract.dispositions,
        formalization_context + ".disposition",
    )
    require_unique_strings(
        formalization["reason_codes"],
        formalization_context + ".reason_codes",
        SLUG_RE,
    )
    require_string(formalization["notes"], formalization_context + ".notes", nonempty=False)
    if formalization["coverage"] != "full" and not formalization["reason_codes"]:
        raise RegistryError(
            "{} incomplete coverage requires a reason code".format(
                formalization_context
            )
        )

    require_array(formalization["components"], formalization_context + ".components")
    component_ids = set()
    component_coverages = set()
    for index, component in enumerate(formalization["components"]):
        component_context = "{}.components[{}]".format(formalization_context, index)
        validate_component(component, component_context, contract)
        if component["id"] in component_ids:
            raise RegistryError("{} repeats component id {!r}".format(context, component["id"]))
        component_ids.add(component["id"])
        component_coverages.add(component["coverage"])
    require_array(claim["lean_links"], context + ".lean_links")
    seen_link_editions = {}
    formalizing_links = []
    whole_support_editions = set()
    component_support_editions = {component_id: set() for component_id in component_ids}
    for index, link in enumerate(claim["lean_links"]):
        link_context = "{}.lean_links[{}]".format(context, index)
        validate_lean_link(
            link,
            link_context,
            contract,
            claim_source_editions,
            component_ids,
            declaration_modules,
        )
        link_key = (link["declaration"], link["role"])
        previous_editions = seen_link_editions.setdefault(link_key, set())
        overlapping_editions = sorted(previous_editions & set(link["source_editions"]))
        if overlapping_editions:
            raise RegistryError(
                "{} duplicates a declaration and role for source edition(s): {}".format(
                    link_context, ", ".join(overlapping_editions)
                )
            )
        previous_editions.update(link["source_editions"])
        if link["role"] in FORMALIZING_ROLES:
            if assessment["status"] == "not-assessed":
                raise RegistryError(
                    "{} formalizing role is incompatible with not-assessed source status".format(
                        link_context
                    )
                )
            formalizing_links.append(link)
        correction_supports_retained_claim = (
            link["role"] == "corrects"
            and link["source_relationship"] != "corrected"
            and assessment["status"] in {"accepted-with-qualification", "corrected"}
        )
        if link["role"] == "corrects":
            if assessment["status"] not in {
                "accepted-with-qualification",
                "corrected",
                "refuted",
                "disputed",
            }:
                raise RegistryError(
                    "{} corrects role requires a recorded source qualification, correction, dispute, or refutation".format(
                        link_context
                    )
                )
            if (
                link["source_relationship"] != "corrected"
                and not correction_supports_retained_claim
            ):
                raise RegistryError(
                    "{} retained-claim correction requires accepted-with-qualification or corrected source assessment".format(
                        link_context
                    )
                )
        if link["role"] == "refutes" and assessment["status"] not in {
            "refuted",
            "disputed",
        }:
            raise RegistryError(
                "{} refutes role requires refuted or disputed source assessment".format(
                    link_context
                )
            )

        supports_components = (
            link["role"] in COMPONENT_CAPABLE_ROLES
            and (link["role"] != "corrects" or correction_supports_retained_claim)
        )
        if link["covers_components"] and not supports_components:
            raise RegistryError(
                "{} role/assessment cannot contribute component coverage".format(link_context)
            )
        if supports_components:
            for component_id in link["covers_components"]:
                component_support_editions[component_id].update(link["source_editions"])

        supports_whole_claim = (
            link["role"] in WHOLE_CLAIM_ROLES or correction_supports_retained_claim
        )
        if supports_whole_claim and component_ids and not link["covers_components"]:
            raise RegistryError(
                "{} whole-claim support must explicitly cover the exhaustive components".format(
                    link_context
                )
            )
        if supports_whole_claim and not link["covers_components"]:
            whole_support_editions.update(link["source_editions"])

    components_by_id = {
        component["id"]: component for component in formalization["components"]
    }
    coverage = formalization["coverage"]
    if assessment["status"] == "refuted" and coverage != "none":
        raise RegistryError("{} refuted source claim must have none coverage".format(context))
    if component_ids:
        for component_id, component in components_by_id.items():
            supported_editions = component_support_editions[component_id]
            component_coverage = component["coverage"]
            if component_coverage == "full" and supported_editions != claim_source_editions:
                raise RegistryError(
                    "{} component {!r} full coverage requires every claim source edition; supported={}, required={}".format(
                        context,
                        component_id,
                        sorted(supported_editions),
                        sorted(claim_source_editions),
                    )
                )
            if component_coverage == "partial" and not (
                supported_editions and supported_editions < claim_source_editions
            ):
                raise RegistryError(
                    "{} component {!r} partial coverage requires a nonempty proper subset of source editions".format(
                        context, component_id
                    )
                )
            if component_coverage in {"none", "unknown"} and supported_editions:
                raise RegistryError(
                    "{} component {!r} {} coverage cannot have component-supporting links".format(
                        context, component_id, component_coverage
                    )
                )

        if "unknown" in component_coverages:
            derived_coverage = "unknown"
        elif component_coverages == {"full"}:
            derived_coverage = "full"
        elif component_coverages == {"none"}:
            derived_coverage = "none"
        else:
            derived_coverage = "partial"
        if coverage != derived_coverage:
            raise RegistryError(
                "{} claim coverage {!r} disagrees with exhaustive component coverage {!r}".format(
                    context, coverage, derived_coverage
                )
            )
        if derived_coverage in {"none", "unknown"} and formalizing_links:
            raise RegistryError(
                "{} {} component coverage cannot coexist with formalizing links".format(
                    context, derived_coverage
                )
            )
    else:
        if coverage == "partial":
            raise RegistryError("{} partial coverage requires explicit exhaustive components".format(context))
        if coverage == "full" and whole_support_editions != claim_source_editions:
            raise RegistryError(
                "{} full coverage requires whole-claim support for every source edition; supported={}, required={}".format(
                    context,
                    sorted(whole_support_editions),
                    sorted(claim_source_editions),
                )
            )
        if coverage in {"none", "unknown"} and (
            whole_support_editions or formalizing_links
        ):
            raise RegistryError(
                "{} {} coverage cannot have unmodeled formalizing support".format(
                    context, coverage
                )
            )

    require_array(claim["relations"], context + ".relations")
    for index, relation in enumerate(claim["relations"]):
        relation_context = "{}.relations[{}]".format(context, index)
        require_keys(relation, {"type", "target"}, {"notes"}, relation_context)
        require_enum(
            relation["type"], contract.claim_relation_types, relation_context + ".type"
        )
        require_pattern(relation["target"], CARD_ID_RE, relation_context + ".target")
        if "notes" in relation:
            require_string(relation["notes"], relation_context + ".notes")
        pending_relations.append((relation_context, relation["target"]))

    require_array(claim["audit_refs"], context + ".audit_refs")
    for index, audit_ref in enumerate(claim["audit_refs"]):
        validate_audit_ref(
            audit_ref, "{}.audit_refs[{}]".format(context, index), contract
        )


def validate_entry(
    entry,
    entry_path,
    contract,
    paper_ids,
    claim_ids,
    declaration_modules,
    pending_relations,
):
    context = relative(entry_path)
    require_keys(
        entry,
        {"schema_version", "paper", "source_editions", "claim_inventory", "claims"},
        set(),
        context,
    )
    if entry["schema_version"] != SCHEMA_VERSION:
        raise RegistryError("{} schema_version must be {}".format(context, SCHEMA_VERSION))
    validate_paper(entry["paper"], context + ".paper", contract)
    paper_id = entry["paper"]["id"]
    if paper_id in paper_ids:
        raise RegistryError("duplicate paper id: {}".format(paper_id))
    paper_ids.add(paper_id)

    require_array(entry["source_editions"], context + ".source_editions", nonempty=True)
    source_ids = set()
    for index, source in enumerate(entry["source_editions"]):
        validate_source_edition(
            source,
            "{}.source_editions[{}]".format(context, index),
            contract,
            source_ids,
        )
    for index, source in enumerate(entry["source_editions"]):
        for relation_index, relation in enumerate(source["relations"]):
            if relation["target"] not in source_ids:
                raise RegistryError(
                    "{}.source_editions[{}].relations[{}].target does not resolve: {!r}".format(
                        context, index, relation_index, relation["target"]
                    )
                )

    require_array(entry["claim_inventory"], context + ".claim_inventory", nonempty=True)
    inventoried_sources = set()
    for index, inventory in enumerate(entry["claim_inventory"]):
        inventory_context = "{}.claim_inventory[{}]".format(context, index)
        validate_inventory(inventory, inventory_context, contract, source_ids)
        edition = inventory["source_edition"]
        if edition in inventoried_sources:
            raise RegistryError("{} repeats source edition {!r}".format(inventory_context, edition))
        inventoried_sources.add(edition)
    if inventoried_sources != source_ids:
        raise RegistryError(
            "{} must declare one claim_inventory entry per source edition; missing={}, extra={}".format(
                context,
                sorted(source_ids - inventoried_sources),
                sorted(inventoried_sources - source_ids),
            )
        )

    require_array(entry["claims"], context + ".claims")
    if not entry["claims"] and any(
        inventory["completeness"] != "not-started"
        for inventory in entry["claim_inventory"]
    ):
        raise RegistryError(
            "{} empty claims require every claim_inventory entry to be not-started".format(
                context
            )
        )
    for index, claim in enumerate(entry["claims"]):
        validate_claim(
            claim,
            "{}.claims[{}]".format(context, index),
            contract,
            source_ids,
            claim_ids,
            declaration_modules,
            pending_relations,
        )

    referenced_editions = {
        source_ref["edition"]
        for claim in entry["claims"]
        for source_ref in claim["source_refs"]
    }
    for index, inventory in enumerate(entry["claim_inventory"]):
        if (
            inventory["completeness"] == "not-started"
            and inventory["source_edition"] in referenced_editions
        ):
            raise RegistryError(
                "{}.claim_inventory[{}] is not-started but claims reference source edition {!r}".format(
                    context, index, inventory["source_edition"]
                )
            )

    claim_coverages = {
        claim["formalization"]["coverage"] for claim in entry["claims"]
    }
    if not claim_coverages or "unknown" in claim_coverages:
        derived_paper_coverage = "unknown"
    elif claim_coverages == {"full"}:
        derived_paper_coverage = "full"
    elif claim_coverages == {"none"}:
        derived_paper_coverage = "none"
    else:
        derived_paper_coverage = "partial"
    declared_paper_coverage = entry["paper"]["formalization_scope"]["coverage"]
    if declared_paper_coverage != derived_paper_coverage:
        raise RegistryError(
            "{}.paper.formalization_scope.coverage {!r} disagrees with claim aggregate {!r}".format(
                context, declared_paper_coverage, derived_paper_coverage
            )
        )


def imported_paper_umbrellas():
    umbrella = REPOSITORY_ROOT / "GenLimitLean" / "GenLimit.lean"
    modules = set()
    pattern = re.compile(r"^import (GenLimit\.Paper[^\s]+)\s*$")
    for line in umbrella.read_text(encoding="utf-8").splitlines():
        match = pattern.match(line)
        if match:
            modules.add(match.group(1))
    return modules


def load_and_validate(require_umbrella_complete=False):
    manifest = load_json(MANIFEST_PATH)
    schema_path = validate_manifest(manifest)
    schema = load_json(schema_path)
    if schema.get("$id") != "urn:genlimit:registry:paper-entry:" + SCHEMA_VERSION:
        raise RegistryError("registry schema $id does not match schema version")
    contract = Contract(schema)

    entries = []
    paper_ids = set()
    paper_lookup = {}
    umbrella_modules = set()
    claim_ids = set()
    declaration_modules = {}
    pending_relations = []
    for entry_name in sorted(manifest["paper_entries"]):
        entry_path = REPOSITORY_ROOT / PurePosixPath(entry_name)
        entry = load_json(entry_path)
        validate_entry(
            entry,
            entry_path,
            contract,
            paper_ids,
            claim_ids,
            declaration_modules,
            pending_relations,
        )
        paper = entry["paper"]
        for token in set(
            [paper["inventory_label"], paper["citation_key"]] + paper["aliases"]
        ):
            previous_paper = paper_lookup.get(token)
            if previous_paper is not None and previous_paper != paper["id"]:
                raise RegistryError(
                    "paper lookup token {!r} is shared by {} and {}".format(
                        token, previous_paper, paper["id"]
                    )
                )
            paper_lookup[token] = paper["id"]
        if paper["umbrella_module"] in umbrella_modules:
            raise RegistryError(
                "duplicate paper umbrella module: {}".format(paper["umbrella_module"])
            )
        umbrella_modules.add(paper["umbrella_module"])
        entries.append((entry_name, entry))

    all_card_ids = paper_ids | claim_ids
    for context, target in pending_relations:
        if target not in all_card_ids:
            raise RegistryError("{}.target does not resolve: {!r}".format(context, target))

    require_complete = (
        require_umbrella_complete
        or manifest["coverage_policy"] == "umbrella-complete"
    )
    if require_complete:
        imported = imported_paper_umbrellas()
        registered = {entry["paper"]["umbrella_module"] for _, entry in entries}
        missing = sorted(imported - registered)
        extra = sorted(registered - imported)
        if missing or extra:
            raise RegistryError(
                "paper umbrella coverage mismatch; missing={}, extra={}".format(missing, extra)
            )

    return manifest, entries, declaration_modules


def resolved_source_ref(source_ref, sources):
    result = copy.deepcopy(source_ref)
    source = sources[source_ref["edition"]]
    result["source"] = {
        key: source[key]
        for key in (
            "id",
            "kind",
            "label",
            "identifier",
            "url",
            "version_date",
            "pdf_sha256",
        )
        if key in source
    }
    return result


def build_cards(entries):
    cards = []
    for entry_name, entry in sorted(entries, key=lambda pair: pair[1]["paper"]["id"]):
        paper = entry["paper"]
        paper_card = copy.deepcopy(paper)
        paper_card.update(
            {
                "card_type": "paper",
                "schema_version": SCHEMA_VERSION,
                "source_editions": copy.deepcopy(entry["source_editions"]),
                "claim_inventory": copy.deepcopy(entry["claim_inventory"]),
                "claim_ids": sorted(claim["id"] for claim in entry["claims"]),
                "source_entry": entry_name,
            }
        )
        cards.append(paper_card)

        sources = {source["id"]: source for source in entry["source_editions"]}
        paper_context = {
            "id": paper["id"],
            "inventory_label": paper["inventory_label"],
            "title": paper["title"],
            "citation_key": paper["citation_key"],
            "year": paper["year"],
        }
        for claim in sorted(entry["claims"], key=lambda item: item["id"]):
            claim_card = copy.deepcopy(claim)
            claim_card.update(
                {
                    "card_type": "claim",
                    "schema_version": SCHEMA_VERSION,
                    "paper": paper_context,
                    "source_entry": entry_name,
                    "source_refs": [
                        resolved_source_ref(source_ref, sources)
                        for source_ref in claim["source_refs"]
                    ],
                }
            )
            cards.append(claim_card)
    return cards


def append_index(mapping, key, value):
    mapping.setdefault(key, set()).add(value)


def sorted_mapping_of_sets(mapping):
    return {key: sorted(values) for key, values in sorted(mapping.items())}


def build_index(manifest, entries, cards):
    by_assumption = {}
    by_claim_kind = {}
    by_coverage = {}
    by_disposition = {}
    by_declaration = {}
    by_result_kind = {}
    by_novelty = {}
    by_paper_topic = {}
    by_source_edition = {}
    by_source_assessment = {}
    by_tag = {}
    frontier = []
    frontier_details = []
    unknown_formalization = []
    open_problems = []
    paper_id_by_alias = {}
    paper_summaries = []

    for entry_name, entry in sorted(entries, key=lambda pair: pair[1]["paper"]["id"]):
        paper = entry["paper"]
        for alias in set(
            [paper["inventory_label"], paper["citation_key"]] + paper["aliases"]
        ):
            paper_id_by_alias[alias] = paper["id"]
        for topic in paper["topics"]:
            append_index(by_paper_topic, topic, paper["id"])
        coverages = {}
        for claim in entry["claims"]:
            coverage = claim["formalization"]["coverage"]
            disposition = claim["formalization"]["disposition"]
            assessment = claim["source_assessment"]["status"]
            coverages[coverage] = coverages.get(coverage, 0) + 1
            append_index(by_coverage, coverage, claim["id"])
            append_index(by_claim_kind, claim["kind"], claim["id"])
            append_index(by_disposition, disposition, claim["id"])
            append_index(by_novelty, claim["novelty"], claim["id"])
            append_index(by_source_assessment, assessment, claim["id"])
            for result_kind in claim["result_kinds"]:
                append_index(by_result_kind, result_kind, claim["id"])
            for assumption in claim["assumptions"]:
                append_index(by_assumption, assumption, claim["id"])
            for tag in claim["tags"]:
                append_index(by_tag, tag, claim["id"])
            for source_ref in claim["source_refs"]:
                append_index(by_source_edition, source_ref["edition"], claim["id"])
            for lean_link in claim["lean_links"]:
                append_index(by_declaration, lean_link["declaration"], claim["id"])
            if coverage in {"none", "partial"} and claim["novelty"] in {
                "published-result-claim",
                "published-informal-claim",
            } and assessment not in {"refuted", "disputed"}:
                frontier.append(claim["id"])
                frontier_details.append(
                    {
                        "claim_id": claim["id"],
                        "coverage": coverage,
                        "disposition": disposition,
                        "source_assessment": assessment,
                        "gap_scope": (
                            "components"
                            if claim["formalization"]["components"]
                            else "whole-claim"
                        ),
                        "missing_component_ids": sorted(
                            component["id"]
                            for component in claim["formalization"]["components"]
                            if component["coverage"] != "full"
                        ),
                        "reason_codes": claim["formalization"]["reason_codes"],
                    }
                )
            if coverage == "unknown":
                unknown_formalization.append(claim["id"])
            if claim["novelty"] == "open-problem":
                open_problems.append(claim["id"])
        paper_summaries.append(
            {
                "id": paper["id"],
                "inventory_label": paper["inventory_label"],
                "title": paper["title"],
                "source_entry": entry_name,
                "claim_count": len(entry["claims"]),
                "claims_by_formalization_coverage": dict(sorted(coverages.items())),
            }
        )

    cards_by_id = {}
    for line_number, card in enumerate(cards, start=1):
        cards_by_id[card["id"]] = {
            "card_type": card["card_type"],
            "jsonl_line": line_number,
        }

    return {
        "schema_version": SCHEMA_VERSION,
        "registry_status": manifest["registry_status"],
        "coverage_policy": manifest["coverage_policy"],
        "cards_file": manifest["generated_outputs"]["cards"],
        "counts": {
            "cards": len(cards),
            "claims": sum(len(entry["claims"]) for _, entry in entries),
            "papers": len(entries),
            "registered_lean_declarations": len(by_declaration),
        },
        "papers": paper_summaries,
        "paper_id_by_alias": dict(sorted(paper_id_by_alias.items())),
        "cards_by_id": dict(sorted(cards_by_id.items())),
        "by_assumption": sorted_mapping_of_sets(by_assumption),
        "by_claim_kind": sorted_mapping_of_sets(by_claim_kind),
        "by_formalization_coverage": sorted_mapping_of_sets(by_coverage),
        "by_formalization_disposition": sorted_mapping_of_sets(by_disposition),
        "by_lean_declaration": sorted_mapping_of_sets(by_declaration),
        "by_novelty": sorted_mapping_of_sets(by_novelty),
        "by_paper_topic": sorted_mapping_of_sets(by_paper_topic),
        "by_result_kind": sorted_mapping_of_sets(by_result_kind),
        "by_source_edition": sorted_mapping_of_sets(by_source_edition),
        "by_source_assessment": sorted_mapping_of_sets(by_source_assessment),
        "by_tag": sorted_mapping_of_sets(by_tag),
        "formalization_frontier": sorted(
            frontier_details, key=lambda item: item["claim_id"]
        ),
        "formalization_frontier_claim_ids": sorted(frontier),
        "unknown_formalization_claim_ids": sorted(unknown_formalization),
        "open_problem_claim_ids": sorted(open_problems),
    }


def render_cards(cards):
    lines = [
        json.dumps(card, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        for card in cards
    ]
    return "\n".join(lines) + "\n"


def render_index(index):
    return json.dumps(index, ensure_ascii=False, sort_keys=True, indent=2) + "\n"


def render_lean_audit(declaration_modules):
    imports = sorted(set(declaration_modules.values()))
    lines = [
        "/- This file is generated by scripts/build_registry.py. Do not edit. -/",
    ]
    lines.extend("import " + module for module in imports)
    lines.extend(
        [
            "import Lean.Util.CollectAxioms",
            "import Lean.Elab.Command",
            "",
            "open Lean Elab Command",
            "",
            "private def registryAllowedAxioms : Array Name :=",
            "  #[``propext, ``Classical.choice, ``Quot.sound].qsort Name.lt",
            "",
            "/-- Resolve a registered declaration, verify its defining module, and enforce",
            "the project's logical-dependency allowlist. -/",
            "elab \"assert_registered_decl \" n:ident \" in \" expectedModule:ident : command => do",
            "  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo n",
            "  let expected := expectedModule.getId",
            "  let env ← getEnv",
            "  let some moduleIdx := env.getModuleIdxFor? name",
            "    | throwError m!\"cannot determine defining module for {name}\"",
            "  let actual := env.header.moduleNames[moduleIdx.toNat]!",
            "  unless actual == expected do",
            "    throwError m!\"wrong defining module for {name}: {actual}; expected {expected}\"",
            "  let actualAxioms := (← Lean.collectAxioms name).qsort Name.lt",
            "  unless actualAxioms.all fun ax => registryAllowedAxioms.contains ax do",
            "    throwError m!\"unexpected axioms for {name}: {actualAxioms.toList}\"",
            "  logInfo m!\"{name}: module {actual}, logical dependencies {actualAxioms.toList}\"",
            "",
        ]
    )
    for declaration, module in sorted(declaration_modules.items()):
        lines.append("assert_registered_decl {} in {}".format(declaration, module))
    lines.append("")
    return "\n".join(lines)


def atomic_write(path, content):
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix="." + path.name + ".", dir=str(path.parent)
    )
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as handle:
            handle.write(content)
        os.chmod(temporary_name, 0o644)
        os.replace(temporary_name, str(path))
    except Exception:
        try:
            os.unlink(temporary_name)
        except OSError:
            pass
        raise


def check_output(path, expected):
    if not path.exists():
        print("missing generated file: {}".format(relative(path)))
        return False
    actual_bytes = path.read_bytes()
    expected_bytes = expected.encode("utf-8")
    if actual_bytes == expected_bytes:
        return True
    print("stale generated file: {}".format(relative(path)))
    try:
        actual = actual_bytes.decode("utf-8")
    except UnicodeDecodeError:
        print("generated file is not valid UTF-8")
        return False
    diff = difflib.unified_diff(
        actual.splitlines(),
        expected.splitlines(),
        fromfile=relative(path),
        tofile=relative(path) + " (expected)",
        lineterm="",
    )
    for index, line in enumerate(diff):
        if index >= 80:
            print("... diff truncated; regenerate with python3 scripts/build_registry.py")
            break
        print(line)
    return False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="validate and compare generated files without writing",
    )
    parser.add_argument(
        "--require-umbrella-complete",
        action="store_true",
        help="require a paper entry for every paper umbrella imported by GenLimit.lean",
    )
    args = parser.parse_args()

    try:
        manifest, entries, declaration_modules = load_and_validate(
            require_umbrella_complete=args.require_umbrella_complete
        )
        cards = build_cards(entries)
        index = build_index(manifest, entries, cards)
        payloads = {
            REPOSITORY_ROOT / PurePosixPath(manifest["generated_outputs"]["cards"]): render_cards(cards),
            REPOSITORY_ROOT / PurePosixPath(manifest["generated_outputs"]["index"]): render_index(index),
            REPOSITORY_ROOT / PurePosixPath(manifest["generated_outputs"]["lean_audit"]): render_lean_audit(declaration_modules),
        }
        if args.check:
            results = [
                check_output(path, payload) for path, payload in payloads.items()
            ]
            clean = all(results)
            if not clean:
                print("regenerate with: python3 scripts/build_registry.py")
                return 1
        else:
            for path, payload in payloads.items():
                atomic_write(path, payload)
                print("wrote {}".format(relative(path)))
        print(
            "registry valid: {} paper(s), {} claim(s), {} Lean declaration(s)".format(
                len(entries),
                sum(len(entry["claims"]) for _, entry in entries),
                len(declaration_modules),
            )
        )
        return 0
    except RegistryError as exc:
        print("registry error: {}".format(exc))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
