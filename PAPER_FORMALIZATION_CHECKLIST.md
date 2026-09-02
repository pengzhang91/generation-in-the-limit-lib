# Paper Formalization Checklist

Use this checklist when adding or substantially extending a paper
formalization. Its purpose is to give every paper a consistent public shape
and to make the scope and remaining gaps auditable.

Not every item applies to every paper. Mark genuinely inapplicable items as
such in the PaperMap rather than creating empty placeholder modules.

## 1. Source and scope

- [ ] Pin the formalized source edition: title, authors, venue or arXiv
  identifier, version, and date where available.
- [ ] Record whether the Lean development follows the arXiv or published
  version when their theorem numbering or statements differ.
- [ ] State the intended scope: semantic mathematics, executable algorithm,
  complexity result, or a clearly identified subset of these.
- [ ] Record every material change of interface, strengthened assumption,
  specialization, repaired source statement, and unresolved source gap.

## 2. Lean structure and theorem coverage

- [ ] Add a paper umbrella at `GenLimit/PaperNN_Name.lean` which imports the
  public modules of the development.
- [ ] Put paper-specific definitions and proofs under
  `GenLimit/PaperNN_Name/`.
- [ ] Reuse paper-independent definitions and lemmas from `Core`; put reusable
  proof infrastructure that is not foundational vocabulary in `Support`.
- [ ] Check for overlap with existing paper developments before introducing a
  second definition. Prefer a bridge theorem or compatibility `abbrev` when
  two source-facing interfaces must coexist.
- [ ] Record cross-paper reuse exposed by formalization in
  `GenLimitLean/PaperMaps/THEOREM_EQUIVALENCES.md`, especially an exact
  equivalence, representation bridge, or shared semantic obligation that the
  source papers do not state explicitly. Distinguish proved reuse from a
  merely similar or prospective reuse candidate.
- [ ] Give source-facing declarations stable names that expose the paper's
  numbering where practical, such as `theorem_2_7` or `lemma_4_1`.
- [ ] Keep assumptions and quantifier order faithful to the pinned source.
  Document any deliberate packaging difference, such as an explicitly
  indexed family in place of an abstract countable collection.
- [ ] Do not leave `sorry`, `admit`, undeclared proof holes, or paper-local
  axioms. Any reliance on existing library axioms or classical choice should
  be disclosed when it materially affects the claim.

## 3. Main-results facade

- [ ] Add `GenLimit/PaperNN_Name/Results/Overview.lean` for a substantial
  multi-result development.
- [ ] Make `Overview.lean` a compilable public facade, not a comments-only
  inventory: import the canonical proof modules and expose thin theorem
  wrappers or aliases for the paper's main results.
- [ ] Do not duplicate proofs in `Overview.lean`; delegate to the canonical
  theorem declarations.
- [ ] Summarize full, partial, specialized, repaired, and open results in the
  module documentation, including the exact qualifications.
- [ ] Import the results facade from the paper umbrella when it is intended to
  be part of the public API.

## 4. PaperMap

- [ ] Add `GenLimitLean/PaperMaps/PaperNN_Name.md`.
- [ ] Include the pinned source edition, Lean umbrella, main-results entry
  point, overall coverage status, and semantic/executable scope.
- [ ] Include a claim-to-Lean table with at least these fields:

  | Paper item | Lean declaration / file | Coverage | Qualification |
  |---|---|---|---|

- [ ] Use explicit coverage labels such as `Full`, `Full specialization`,
  `Partial`, `Infrastructure only`, `Source repair`, or `Open`.
- [ ] Explain every gap rather than letting absence imply completion.
- [ ] Identify shared `Core`/`Support` infrastructure and dependencies on
  other numbered paper developments.
- [ ] Do not add a PaperMap link to `THEOREM_EQUIVALENCES.md` while that file
  remains local and untracked; the central record can be linked publicly only
  after it is deliberately added to the repository.

## 5. Repository integration

- [ ] Import the paper umbrella from `GenLimitLean/GenLimit.lean`.
- [ ] Add or update the paper row in the repository-root `README.md`.
- [ ] Add or update the paper entry in `GenLimitLean/README.md`.
- [ ] Add the bibliographic entry to `CITATION.bib`, using the pinned source
  edition and a stable citation key.
- [ ] Add `registry/papers/PNN.json`, validate it against the registry schema,
  and regenerate tracked registry outputs using the repository's registry
  workflow.
- [ ] Check that displayed theorem counts, coverage labels, paths, and source
  versions agree across the Overview, PaperMap, READMEs, citation, and
  registry metadata.

## 6. Verification

- [ ] During development, build the narrowest changed module first with
  `lake build GenLimit.Module.Name` from `GenLimitLean/`.
- [ ] After changing `Core` or shared `Support`, build that module and only the
  directly affected paper umbrellas before broader verification.
- [ ] Build the paper umbrella: `lake build GenLimit.PaperNN_Name`.
- [ ] Search the new development for proof holes and unintended axioms.
- [ ] Check warnings separately from failures and resolve new warnings where
  practical.
- [ ] Before declaring a substantial Lean change ready to commit or push, run
  one repository-wide incremental `lake build`.
- [ ] Documentation-only edits need no Lean rebuild unless they change
  imports, module paths, generated inputs, or executable examples.

## 7. Commit review

- [ ] Review `git status` and the exact diff; exclude unrelated, private, and
  explicitly untracked research files.
- [ ] Confirm that renamed or moved modules leave no stale imports or public
  paths.
- [ ] Confirm that the commit contains source, documentation, citation, and
  registry changes intended for this paper—and nothing else.
- [ ] In the handoff, report targeted builds, the final full build, warnings,
  known gaps, and whether anything remains uncommitted or unpushed.
