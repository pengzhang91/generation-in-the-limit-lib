# Claim-centered LLM registry

This directory is the machine-readable research index for the Lean library.
Its primary entity is a mathematical claim from a pinned source edition, not
a Lean declaration.  A claim may have several Lean realizations, a partial
realization, a counterexample, a correction, or no Lean counterpart at all.

The current `0.1.0` registry is deliberately a **P01-only pilot**.  It must not
be interpreted as a complete inventory of every paper imported by
`GenLimit.lean`.  The machine-readable scope is declared in
[`registry.json`](registry.json) as `listed-entries-only`.  Once every imported
paper has at least an identity card, this can be changed to
`umbrella-complete` and enforced in CI.

## Authority boundaries

- Lean owns declaration types, proof terms, imports, and logical dependencies.
- Source editions own the published mathematical statements.
- `AuditRecords` own snapshot-specific correspondence evidence.
- Registry entries own stable IDs, source-to-Lean mappings, curated
  classifications, and declared inventory scope.
- Files under `generated/` and `GenLimitLean/RegistryAudit.lean` are generated
  projections and must not be edited by hand.

The registry therefore does not copy Lean theorem signatures.  It records a
declaration name and defining module; the generated Lean audit resolves that
name, checks module ownership, and enforces the project's axiom allowlist.
Fields under `lean_links.interface` are curated comparison metadata, not values
extracted from Lean theorem types; their evidence comes from the card's scoped
audit references.

## Card semantics

Each file in `papers/` contains one paper card and its source claims.  In
particular:

- `formalization.coverage: "none"` means the source claim has no formalizing
  Lean link.  It may still have a Lean refutation or correction.
- `novelty: "published-result-claim"` records provenance, not truth.  Read it
  together with `source_assessment`; a published-but-unformalized claim must
  never be presented as a new conjecture.
- `source_assessment: "no-known-issue"` means only that this registry records no
  source issue.  It is not a correctness proof or a human-audit certification.
- If `formalization.components` is nonempty, it is an exhaustive decomposition:
  claim-level coverage is derived from component coverage.  In particular, a
  Nat-only realization of an arbitrary-countable-universe claim is `partial`
  until the transport obligation is discharged.
- In v0, component-level `partial` means that the whole component is covered
  for a nonempty proper subset of the claim's source editions.  Partial work
  within one edition must be split into smaller full/none components.
- Coverage and disposition are independent: `partial` + `maintained` means the
  registered formalized component is maintained while other source obligations
  remain open.
- Lean links may cross paper boundaries.  Their role and
  `source_relationship` distinguish a direct formalization from a weaker core,
  correction, refutation, or materially different related construction.
- `claim_inventory` states which part of each source edition has been
  inventoried.  Absence from a `complete` custom inventory is meaningful only
  inside its stated custom scope.
- A paper identity card may temporarily use `claims: []` only when every source
  inventory is marked `not-started` and paper coverage is `unknown`.  An
  edition marked `not-started` cannot already be cited by a claim.
- Paper-level coverage is the aggregate of the inventoried claim cards, so it
  cannot disagree with their claim-level coverage.
- `audit_refs` always state their scope.  Referring to a human ledger does not
  silently promote an entire paper to human-audited status.

The generated `cards.jsonl` contains one independently retrievable paper or
claim card per line.  It is the preferred input for LLM retrieval.  The
generated `index.json` supplies deterministic facets for declaration lookup,
formalization-frontier queries, and result-kind filtering.

## Commands

From the repository root:

```bash
python3 scripts/build_registry.py
python3 scripts/build_registry.py --check
```

The first command validates entries and regenerates all projections.  The
second is read-only and fails if validation fails or any generated file is
stale.  After Lake dependencies are available, check the registered Lean
references with:

```bash
cd GenLimitLean
lake env lean RegistryAudit.lean
```

`--require-umbrella-complete` is intentionally not enabled during the pilot.
It is available to test the eventual invariant that every paper umbrella
imported by `GenLimit.lean` has a registry entry.
