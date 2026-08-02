# Human audit records

These are human semantic audits, separate from Lean's kernel checks in
[AUDIT.md](AUDIT.md). Each record is complete only at its stated level.

| Development | Audit level | Auditor | Recorded | Release |
|---|---|---|---|---|
| KM semantic | Level 3: theorem, construction, and proof correspondence | Peng Zhang | 17 July 2026; narrow re-audit 20 July 2026 | `v0.3.0`; current revision `unreleased` |
| DenseGeneration exact presentation | Black-box input/output specification | Peng Zhang | 16 July 2026 | `v0.3.0` |
| DenseGeneration patient-scope machine | State-machine construction and manuscript correspondence | Peng Zhang | 19 July 2026 | `unreleased` |
| DenseGeneration criticality and focus | Definition-level manuscript correspondence | Peng Zhang | 19 July 2026 | `unreleased` |
| DenseGeneration exact-presentation main result | End-to-end algorithm-to-main-theorem correspondence | Peng Zhang | 19 July 2026 | checkpoint `374e24f` |
| DenseGeneration partial enumeration, Lemma 3.16 and Theorem 3.17 | Level 2: transformation and main-theorem correspondence | Peng Zhang | 19 July 2026 | `unreleased` |
| Gold arbitrary-text semantic theory | Level 2: shared Core prerequisites and Gold Text | Peng Zhang | 2 August 2026 | `unreleased` |

## KM semantic construction and proof correspondence

For a fixed family `O`, `KM.Semantic.generator O stream` does not receive the
hidden target index `z`. If `stream` exactly presents `O.language z`, the main
theorem says that every sufficiently late output belongs to the target and is
absent from `sample stream t`.

| Checked item | Audited meaning |
|---|---|
| Model | `OracleFamily` is an indexed family of infinite languages, and `Presents` means exact positive-data presentation. |
| Criticality | `Critical` is KM criticality; critical languages form the required inclusion chain and the target is eventually critical. |
| Construction | At round `t`, `focus` selects the greatest critical index below `t`, and `fresh` selects the least focused-language element outside `sample stream t`. |
| Uniformity | The generator depends on `O`, `stream`, and `t`, not on `z`. |
| Conclusion | Eventual target membership and freshness from the first `t` stream observations; generator outputs need not be mutually distinct. |
| Access model | Round `t` uses the current observation prefix, but whole-language inclusion makes this semantic construction noncomputable from the membership oracle. |

This Level 3 audit covers the round-dependent Section 4 construction,
especially (4.2)--(4.6), with `t` explicit. It does not certify a literal
finite-set-only realization of the interface stated in (4.1).

On 20 July 2026, Peng Zhang performed a narrow human re-audit against the KM
NeurIPS 2024 proceedings version after the semantic-file cleanup. The
paper-facing definitions, main theorem statement, and proof steps were
unchanged: the existing proof body was moved directly into
`kleinbergMullainathan_main`, the duplicate `eventual_correctness` alias was
removed, and the Section 4 boundary was documented.

The current audited code anchors are:

| Code anchor | SHA-256 |
|---|---|
| `GenLimit/KM/Critical.lean` | `61b1c01977eaa69adaa63e56ccf8a0dac9c3554035a99d6d325ea2affeeb2e60` |
| `GenLimit/KM/Semantic.lean` | `3f603dff375c9f3cc5ee0bca80271e8dd36b775f3f661d2fa56cf8e5923aefaa` |

The shared model is in [`GenLimit/Core/Basic.lean`](GenLimit/Core/Basic.lean).
This audit does not require a literal tactic-by-tactic or line-by-line identity
between the Lean proof and the prose. It does cover the theorem statement,
semantic construction, intermediate mathematical steps, and proof
correspondence at Level 3. It does not cover the observed-set interface or
either finite-query development (the NeurIPS proceedings endpoint machine and
the arXiv-v1 whole-prefix machine).

## DenseGeneration exact-presentation black-box specification

For a fixed family `O`, `PatientMachine.output O stream` does not receive the
hidden target index `z`. For every stream exactly presenting `O.language z`,
the joint theorem gives eventual target validity, novelty, and target-relative
lower density at least `1 / 2`.

| Checked item | Audited meaning |
|---|---|
| Inputs | `OracleFamily` is an indexed family of infinite languages; `Presents stream (O.language z)` means that the stream presents exactly the target. |
| Uniformity | The generator depends on `O` and the observed stream, not on `z`. |
| Validity | Every sufficiently late output belongs to `O.language z`. |
| Novelty | Every sufficiently late output differs from all stream values through that round and from all earlier generator outputs. |
| Density | The numerator counts target elements below `n` first announced by the generator; the denominator is `|O.language z ∩ Finset.range n|`, not `n`. |
| Strength | The result proves achievability of target-relative lower density at least `1 / 2`. |

Code anchors are
[`GenLimit/DenseGeneration/Patient/Machine.lean`](GenLimit/DenseGeneration/Patient/Machine.lean)
and [`GenLimit/DenseGeneration/Patient/Main.lean`](GenLimit/DenseGeneration/Patient/Main.lean),
with `Presents` and `OracleFamily` in `GenLimit.Core`. This audit does not
certify manuscript-algorithm correspondence, paper-to-Lean proof
correspondence, finite-query executability, computational complexity, or the
separate upper bound needed for optimality. The current machine is semantic
and noncomputable because recursive criticality compares whole infinite
languages. The separate construction audit below now covers the machine's
manuscript correspondence, and the definition audit below covers recursive
criticality and focus, at their respective stated levels.

## DenseGeneration patient-scope machine construction

The construction in `GenLimit/DenseGeneration/Patient/Machine.lean` was
checked directly against the Dense Generation manuscript. The result is
**PASS** at the state-machine construction and manuscript-correspondence
level.

| Checked item | Audited correspondence |
|---|---|
| Indexing and time | Positive paper values and one-based language indices are translated to `ℕ`; paper round `T ≥ 1` is Lean output round `T - 1`, while the post-round state is `run O stream T`. |
| State and initialization | The exclusive scope bound, focus-change count, consecutive-focus age, focus index, output history, last output, and move label have the intended roles; the initial scope and `tau` are `1`, while the initial focus and age are `0`. |
| Stable branch | The machine tests the previous `2 ^ tau` completed focus rounds, expands the scope by one, recomputes the highest critical focus after the current observation, and increments `tau` exactly when the focus changes. |
| Backtracking | The three manuscript cases are represented by the highest surviving critical index, the lowest consistent index in the old scope, and the globally lowest consistent index when the old scope is empty of consistent candidates. The exclusive Lean scope `i + 1` matches the one-based paper scope ending at the selected language. |
| Output and history | Each round receives `stream t`, decides using the sample through that announcement, selects the least focused-language value absent from both parties' prior announcements, updates `age` and `used`, and records the output in the post-round state. |
| Totalization and access model | Extra fallbacks make the Lean definitions total on arbitrary histories but are unreachable on an exact presentation. The construction is semantic and noncomputable because it uses whole-language consistency, criticality, and inclusion. |

The audited code anchor has SHA-256
`ca4ad447ccaeeb9ce9304c555b525a32d8a2f491c0372d3b5b9f32f0898f6b73`.
This record does not yet cover `MachineInvariant.lean`, downstream validity or
charging arguments, the rest of the `Patient` directory, or a line-by-line
audit of every helper-theorem proof in `Machine.lean`.

## DenseGeneration recursive criticality and focus definitions

The definitions `RecursiveCritical` and `IsFocus` in
`GenLimit/DenseGeneration/Critical.lean` were checked directly against
Definitions 3.2, 3.5, and 3.6 of the Dense Generation manuscript. The result
is **PASS** at the definition and manuscript-correspondence level.

| Checked item | Audited correspondence |
|---|---|
| Recursive criticality | Index zero is critical exactly when it is consistent. An index `n + 1` is critical exactly when it is consistent and its language is contained in every earlier recursively critical language. |
| Focus | `IsFocus C stream t s f` says that `f < s`, that `f` is recursively critical, and that every recursively critical `j < s` satisfies `j ≤ f`; hence `f` is the highest-indexed critical language in scope. |
| Indexing | The manuscript's one-based language indices are translated to zero-based Lean indices, and a Lean scope bound `s` contains exactly the indices `< s`. |
| Audit boundary | Only the two paper-facing definitions were audited. The lemmas and proofs in `Critical.lean`, including eventual target criticality and focus containment, are verified by Lean but were not checked against the manuscript proof steps. |

The audited `Critical.lean` code anchor has SHA-256
`a4ca152c7dccca987999b5fc68dc04541be79bd209fdbaabaaf7bf4f87e77d9f`.

## DenseGeneration exact-presentation end-to-end conclusion

Taken together, the exact-presentation input/output audit, the recursive
criticality and focus definition audit, and the patient-scope machine audit
constitute an **end-to-end algorithm-to-main-theorem correspondence audit**
for Theorem 3.14. Human review identifies the manuscript algorithm with the
Lean state machine and the manuscript claim with the Lean theorem statement;
Lean's kernel verifies that this machine satisfies that statement.

This establishes the main exact-presentation algorithmic claim without
certifying the manuscript's intermediate lemmas, its proof steps, or a
line-by-line correspondence between the manuscript proof and the Lean proof.
It also does not add finite-query, complexity, optimality, randomized, or
partial-enumeration claims. The audited `Patient/Main.lean` code anchor at
checkpoint `374e24f` has SHA-256
`d2998e711536b5cea618b32fb7e09c22dceab244e3ce7355e2d9e90906ffb2d3`.

The later shared-density and API cleanup changed the paper-facing density
wrapper, made an internal certificate bridge private, and removed a redundant
derived theorem. The file's current hash is
`cd4b763251a6f77e36522cbc7203b0abbfdbea12cc9e9f4fa8bc9a689ba7a91a`;
a narrow human re-audit of the exact-presentation wrapper remains pending. The
machine and criticality anchors above are unchanged.

## DenseGeneration partial enumeration: Lemma 3.16 and Theorem 3.17

The finite-intersection transformation, the paper-facing statements of Lemma
3.16 and Theorem 3.17, and their operational density definitions were checked
directly against Section 3.3 of the Dense Generation manuscript. The result is
**PASS at Level 2** for these two results.

| Checked item | Audited correspondence |
|---|---|
| Inputs | The stream exactly presents an infinite language `E`, with `E ⊆ O.language z`; `O.language z` is the unknown true target `K`. |
| Closure transformation | The definitions in `Partial/Closure.lean` encode nonempty finite intersections by positive binary codes, retain exactly the infinite intersections, order retained codes increasingly, and expose the resulting indexed family as `closure O`. |
| Reused algorithm | The formal construction is the already-audited patient-scope machine run as `PatientMachine.output (closure O) stream`; the machine itself is unchanged. |
| Uniformity | The generator receives `O` and the observed stream, but not `E` or the hidden target index `z`. |
| Lemma 3.16 | `lemma_3_16_generation` gives eventual membership in `O.language z`, freshness from the observed stream through the current round, and non-repetition of generator outputs. |
| Density metric | `relativeLowerDensity A K` is the liminf of ambient-prefix counts `|A ∩ [0,n)| / |K ∩ [0,n)|`. The output metric explicitly counts generator-first elements that belong to `K`. |
| Theorem 3.17 | If `E` has relative lower density `α` in `K`, the concrete transformed run has target-relative lower density at least `α / 2`. |
| Access model | Retaining only infinite intersections and reindexing them is semantic and noncomputable; the audited result does not claim a finite-query implementation. |

Human review identifies the manuscript's transformed algorithm with the Lean
construction and its claims with the Lean theorem statements. Lean's kernel
verifies that this construction satisfies those statements. The audit reuses
the existing patient-machine record whose SHA-256 is
`ca4ad447ccaeeb9ce9304c555b525a32d8a2f491c0372d3b5b9f32f0898f6b73`.
The audited Lean code checkpoint is `22f04f7`.

The new audited code anchors have SHA-256 values:

| Code anchor | SHA-256 |
|---|---|
| `Partial/Closure.lean` | `6cc7c705b49d03d8966ad64902305c93528d102ce4e5dd0b281708312737e671` |
| `Abstract/TargetDensity.lean` | `fcad41b14bad213f8014da6d99fdba04ed28df27fe37bf1b0873594700f37358` |
| `Partial/Validity.lean` | `45709d6ec5cb32c42a1faad66a52154143164a6fa1f18af25d4351113c1f8e4c` |
| `Partial/Main.lean` | `9754880a47f8e18c248bf28e27bec16b050ee78e9399625bbee9cc6781e5c868` |

After the original audit checkpoint, the internal certificate bridge in
`Partial/Main.lean` was made private and its explanatory comment was
clarified. The audited paper-facing definitions and theorem statements were
unchanged.

The audited manuscript copy has SHA-256
`1a9a81a7aa02719f5cfe852746f3db853d47d42f699e8f62cc78f451ef7cb23e`.

This record does not cover Example 3.15, intermediate proof-step
correspondence, the proof bodies in `Partial/Critical`, `Partial/Certificate`,
`Partial/Trace`, or the counting and liminf modules. It also does not cover
finite-query executability, complexity, the Kleinberg--Wei algorithm, or the
optimality upper bound.

## Gold arbitrary-text semantic theory

On 2 August 2026, Peng Zhang reported completion of a human audit at Level 2
for the Gold arbitrary-text semantic path. The new shared Core files had
also been read as the prerequisite layer. The audited scope is the concrete
semantic theory of identification from arbitrary exact positive text.

| Checked file or layer | Audited role |
|---|---|
| `GenLimit/Core/Text.lean` | Ordered finite prefixes of a stream and their finite-set view. |
| `GenLimit/Core/Identification.lean` | Generic learners, eventual syntactic stabilization, and identification in the limit. |
| `GenLimit/Gold/Text/Model.lean` | Gold text naming relations and the target-, class-, and semantic-identification interfaces. |
| `GenLimit/Gold/Text/Consistency.lean` | Equivalence between positive compatibility of a finite history and consistency of the corresponding stream prefix. |
| `GenLimit/Gold/Text/Finite.lean` | The observed-elements learner and the semantic convergence content of Theorem I.6 for all finite languages. |
| `GenLimit/Gold/Text/Locking.lean` | The semantic locking-sequence lemma used as supporting machinery; it is not presented as a numbered theorem in Gold's paper. |
| `GenLimit/Gold/Text/Superfinite.lean` | Gold's Section 8 arbitrary-text semantic obstruction: all finite languages are identifiable, but no proper superclass is. |

The audit therefore covers the definitions and proof chain leading from the
finite-language learner through locking and finite tell-tales to
`superfinite_not_semanticallyIdentifiable` and
`finiteLanguages_maximal_semanticallyIdentifiable`.  It verifies the intended
semantic reading: even a possibly noncomputable learner cannot identify, from
every arbitrary positive text, a class containing every finite language and
at least one infinite language.

This record does not cover `Gold/Abstract`, Theorem 7.1,
`Abstract/TextSpecialization.lean`, `Text/Enumeration.lean`, `Gold/Informant`,
or the bridge files.  It also does not certify effective tester or generator
indices, recursive or primitive-recursive counterexample texts, or Gold's
Theorems I.8 and I.9.  Under the current `ℕ → ℕ` stream model, the empty
language has no exact text, so its identification condition is vacuous.

The audited code anchors have SHA-256 values:

| Code anchor | SHA-256 |
|---|---|
| `GenLimit/Core/Text.lean` | `0d09cf30062fc02b8b77214e987009eebc4ebf6aa77fc5e3df5bdaa9ff993a21` |
| `GenLimit/Core/Identification.lean` | `b4629c10265a70a52c5955b50b723c33d186c0ea66500c7f91ffa3b7f6bd96e8` |
| `GenLimit/Gold/Text/Model.lean` | `2e05362eea4ec3d44de34f89dd6e183f0b3ba76f75a0294c5282bf9d7b52274f` |
| `GenLimit/Gold/Text/Consistency.lean` | `f00718c664cd1b1bd1f00164c96625c36965325caa1ec74915db52fb5e608626` |
| `GenLimit/Gold/Text/Finite.lean` | `97427cb75441a51ec9b74f9d47398dc1ddcb3294d06d829ffa3145691bad4619` |
| `GenLimit/Gold/Text/Locking.lean` | `972eb4e2719228190e59262fb6ce974912584a56c3c219ab4edc33875c827010` |
| `GenLimit/Gold/Text/Superfinite.lean` | `b8cc3d36129cb62d2b3ed6916f5926081bcf7345a3f6c3e6a73b427a99b7f842` |

## Paper 28: human correspondence review pending

Li--Han--Jiang--Gao's *Contrastive Identification and Generation in the
Limit* has a completed checksum-pinned AI-assisted statement reconstruction
and source comparison, but **no named human audit level has been assigned**.
It is therefore intentionally absent from the completed-audit table above.
The evidence and exact source versions are preserved in
[`AuditRecords/ContrastiveGeneration/`](AuditRecords/ContrastiveGeneration/),
and the current scope is summarized in the
[Paper 28 map](PaperMaps/ContrastiveGeneration.md).

The external audit inspected the pre-repair baseline. Its finding that
`theorem_6_6` did not expose the advertised named absence-count witness was
then addressed in a separately tracked public change by
`absenceCountIdentifier_finitely_identifies`. That repair is kernel checked
and closes the statement-interface gap, but it is not itself a human
paper-to-Lean correspondence audit. In particular, no human record currently
certifies unordered-edge transport, the full clean hierarchy, the
fixed-enumeration tie-breaking rule, computability, runtime, or the broader
robustness and probabilistic claims left outside the Lean scope.

## Paper 31: human correspondence review pending

Kleinberg--Mehrotra--Saberi--Velegkas's *On Language Generation in the Limit
with Bounded Memory* has a completed checksum-pinned AI-assisted statement
reconstruction and source comparison, but **no named human audit level has
been assigned**. It is therefore intentionally absent from the
completed-audit table above. The evidence and exact source version are
preserved in [`AuditRecords/BoundedMemory/`](AuditRecords/BoundedMemory/), and
the current scope is summarized in the
[Paper 31 map](PaperMaps/BoundedMemory.md).

The external audit inspected a baseline in which the four substantive coding-
cell properties for Appendix Lemma A.3 were present but no single existential
wrapper packaged them. The separately tracked public `lemma_A_3` repair is
kernel checked and closes that statement-interface gap, but it is not itself a
human paper-to-Lean correspondence audit. In particular, no human record
currently certifies transport from `ℕ` to arbitrary countable universes, the
paper's fixed-global-order density game, an intrinsically infinite set-output
codomain, transport of Theorem 5.2 back to the input indexing, computability,
runtime, bounded-bit memory, or the omitted countable and temporal-density
extensions.

## Re-audit condition

The two `v0.3.0` records apply to that release. The KM semantic record also
applies to descendants in which the re-audited code anchors above remain
unchanged. The patient-scope machine-construction record and criticality/focus
record apply to the exact source hashes recorded above. Each end-to-end
conclusion requires all of its component audit anchors to remain unchanged.
The partial-enumeration Level 2 record also depends on the inherited
patient-machine anchor. The Gold Text Level 2 record applies while all
seven Gold and shared-Core anchors above remain unchanged. Re-audit is required
if an anchor changes or a stronger correspondence claim is made.
