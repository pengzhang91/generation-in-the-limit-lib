# Claim-centered LLM registry

This directory is the machine-readable research index for the Lean library.
Its primary entity is a mathematical claim from a pinned source edition, not
a Lean declaration.  A claim may have several Lean realizations, a partial
realization, a counterexample, a correction, or no Lean counterpart at all.

The current `0.2.0` registry has an identity card for every paper umbrella
imported by `GenLimit.lean`; [`registry.json`](registry.json) therefore declares
`umbrella-complete`, and CI enforces exact agreement with those imports.  This
is paper-identity completeness, not theorem-inventory completeness.  P00, P00A,
P01, P02, P03, P04, P05, P06, P08, P09, P10, P28, and P39 have detailed claim cards.  Every other entry
deliberately has no claims and marks both its source-claim and Lean-declaration
inventories as `not-started`.

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
- Source-edition IDs are registry-global, not merely paper-local, so the
  `by_source_edition` facet cannot silently merge unrelated editions.
- `lean_declaration_inventory` separately states how much of the Lean side has
  been mapped to the declared claims.  `complete` is always relative to its
  explicit scope; it never means that every helper declaration below an
  umbrella import has a card.
- `paper_map` names the best existing paper-facing local metadata or mapping
  document.  Detailed entries normally point into `PaperMaps/`; an
  identity-only entry may temporarily point to its documented Lean umbrella
  when no dedicated PaperMap exists, and must disclose that boundary in its
  scope summary.
- A paper identity card may temporarily use `claims: []` only when every source
  inventory and its Lean-declaration inventory are marked `not-started`, and
  paper coverage is `unknown`.  Such a card records identity only; it does not
  assert that the source has no results or that Lean has no declarations.  An
  edition marked `not-started` cannot already be cited by a claim.
- Paper-level coverage is the aggregate of the inventoried claim cards, so it
  cannot disagree with their claim-level coverage.
- `audit_refs` always state their scope.  Referring to a human ledger does not
  silently promote an entire paper to human-audited status.

The generated `cards.jsonl` contains one independently retrievable paper or
claim card per line.  It is the preferred input for LLM retrieval.  The
generated `index.json` supplies deterministic facets for declaration lookup,
formalization-frontier queries, result-kind filtering, identity-versus-claim
entry status, and both source-claim and Lean-declaration inventory progress.
Each component-scoped frontier entry carries the missing components' own
summary, disposition, and reason codes; consumers must not infer a proof target
from a missing component whose disposition is `not-planned` or whose summary
records a false literal reading.
The JSON Schema describes each entry's local structure; the Python builder is
the canonical validator because it also enforces semantic, cross-card, source
ID, umbrella-coverage, and generated-output invariants.

## Commands

From the repository root:

```bash
python3 scripts/build_registry.py
python3 scripts/build_registry.py --check --require-umbrella-complete
```

The first command validates entries and regenerates all projections.  The
second is read-only and fails if validation fails, any generated file is stale,
or the registered umbrella set differs from the paper imports in
`GenLimit.lean`.  Because the manifest itself declares `umbrella-complete`, a
plain `--check` enforces the same coverage invariant; the explicit flag makes
the CI contract visible.  After Lake dependencies are available, check the
registered Lean references with:

```bash
cd GenLimitLean
lake env lean RegistryAudit.lean
```

The umbrella check is deliberately syntactic and narrow: it guarantees exactly
one paper entry for every `GenLimit.Paper*` import.  Claim and declaration
inventory status remains explicit inside each entry and is never inferred from
the presence of an umbrella card.
