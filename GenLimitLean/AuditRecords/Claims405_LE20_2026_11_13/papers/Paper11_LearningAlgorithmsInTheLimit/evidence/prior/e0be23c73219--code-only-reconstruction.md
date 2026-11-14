# Stage 1: code-only statement reconstruction

This report reconstructs exactly the 16 declarations in `stage1/targets.txt`, in their supplied order. Its mathematical evidence is restricted to the supplied target types, definition values and constructors, with the declared standard Lean/Mathlib boundary. Identifiers and source anchors locate evidence; they do not supply intended meanings. No paper, source-paper URL, developer interpretation, registry, PaperMap, other package, other stage, theorem proof body, raw project source, or external mathematical source was consulted. This is a statement reconstruction, not a proof audit, source-correspondence finding, fresh compilation, or human certification.

## Input census and provenance

The initial directory listing already contained `explicit-target-types/README.md`, `types.jsonl`, and its manifest. The main manifest covers the README and explicit type data. All 13 main-manifest entries and both supplemental-manifest entries matched their recorded SHA-256 values before interpretation. The two manifest files themselves were also hashed. There were 15 distinct input files, 144 exported declarations, 16 target theorem types, and 16 matching explicit type records. Every target theorem value is absent; the additional encoding-law theorem also has no proof value. The dependency-reference census has no undeclared names beyond the supplied external boundary.

The snapshot declares capture time `2026-11-10T14:23:54.375653+00:00`, Git head `60620581aa210daec6fa7d3aa65d7f9fdb565b8c`, branch `work/non-p38`, and a dirty working tree. These are supplied provenance assertions; underlying source files and Git state were not opened or independently checked. The toolchain metadata specifies Lean 4.24.0 and Mathlib v4.24.0, with Mathlib revision `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. Metadata URLs were encountered as literal strings only; none was opened.

Configuration supplied for this isolated run: model `gpt-6.1-sol`, reasoning `xhigh`, context fork `none`. Backend identity and independent configuration telemetry are unavailable. The access ledger in `stage1-run.json` distinguishes byte reads, model-visible excerpts, truncation, and subsequent focused rereads. There was no Lean or Lake invocation, repository edit, Git operation, network request, or subagent delegation by this reviewer.

| Input relative to stage1/ | Bytes | Actual SHA-256 |
| --- | ---: | --- |
| `START_HERE.md` | 190 | `1725bd4c80588e11a0e2ac348db0760993060736fac1f9a2d28b6990b2e41638` |
| `PROMPT.md` | 1827 | `d79a9f3221e3fdc6cdb3835026d91ba49ca51b6fade5f30a27d10c5aba9eed4e` |
| `SHA256SUMS` | 1126 | `96bca54e9d4792d93d04c5fa45140e778802330352690ec4c0b4f3b2b899939b` |
| `explicit-target-types/README.md` | 515 | `32eaa6c83ca84b5d6901931d03ec27518572a50f3f7f6d3a45b49246bd489358` |
| `explicit-target-types/SHA256SUMS` | 154 | `ced503408c93a76d4dfb1e7c74eeef092d844e2fea57302967ba214f765953a6` |
| `snapshot.json` | 7809 | `65176ff1072e6cba5a11a855e59c195255eb3e5062f3997f2ba4fd4da79e8ffb` |
| `targets.txt` | 1236 | `6a8e766e39093eee6d25b7d8a214037e353b5d3954264f13f692929f69cf4a70` |
| `01-target-statements.md` | 18753 | `d443c86b3fd6c9503ad81c6b4b9049aec330b642c7ed7a826504db2bfc16eea9` |
| `external-constant-boundary.txt` | 1690 | `e0e2845fa4e27c2fdaaed6b13c5e3c240842d0bf06b0ab0ce2b80ac2cd431650` |
| `lakefile.toml` | 379 | `0fef48c5e314b7476f09da4caa5615d58a50937752aea1b192c0921a05b6e3d0` |
| `lean-toolchain` | 25 | `42779d67b81608af8a12aa4328d2ab47ca201925b3b2bd68369587b5340bb434` |
| `lake-manifest.json` | 3100 | `994d8b6a379cea0e626d27fe8fa2fc74a2d966197a6998ecde6bd419634991aa` |
| `02-definition-dependencies.md` | 81867 | `136c040b6c5e783df9dfc1ae3a03750e08dc3f8f1d3bf044db51358aca77d397` |
| `declarations.jsonl` | 149579 | `d990582d4a861b9185ebaa8e9314c3fe58d6467e7eabedc830d2a7b9e02d681d` |
| `explicit-target-types/types.jsonl` | 25134 | `74c63636873d55bde3dd0b8826704653ed5de0c5c3708e892e860d7be07b9346` |

## Definition glossary and interpretation rules

A stream is a total function from natural numbers. `Covers stream source` means **range(stream) = source**, so every streamed input belongs to the source and every source input appears at least once. Repetitions are allowed, with no frequency or delay bound. A covering stream makes its source nonempty, even when the source is finite; an empty source has no such stream. No probability law, full-support distribution, fairness rate, or independent sampling assumption occurs in these targets.

`GenLimit.Learner Info Name` is a function from a finite **list** of observations to a name. At time t it receives exactly observations at indices 0 through t−1, via `textPrefix`; time zero gives the empty list. `LearnsByCriterion learner information correct` expands to `∃ r, correct r ∧ ∃ T, ∀ t ≥ T, learner(prefix information t) = r`. This is eventual exact stabilization of a single representation. `LearnsInLimit` uses the criterion `CorrectOn`, namely equality of the represented and target `Option` values on every source input. `none` is an observable semantic value in this equality, not an omitted label. No convergence rate, bound on T, early correctness, or externally recognizable stopping time is included.

The common enumeration learner tests indices 0 through the history length, retaining those fitting **every** observation in the list. It returns the least retained index when the filtered finite set is nonempty, and 0 otherwise. `labeledFits` compares a candidate's `Option` output with the stored optional label. `labeledStream` supplies the input and the target's exact optional value at that input. Decidable equality makes these finite comparisons decidable relative to the supplied functions. The signatures impose no coding or ordinary-computability certificate on arbitrary input types, semantics, simulators, or observation functions; operational language in this report is relative to those interfaces.

For set-based claims, `exampleSet observe m inputs` is the graph `{(x, observe m x) | x ∈ inputs}`. `IsCharacteristicSet learner observe modelSemantics representationSemantics source m core` means both `core ⊆ source` and: for **every set** S with `core ⊆ S ⊆ source`, the representation returned from that graph is correct on the **whole source** for model m. Neither core nor S is required finite. This learner consumes a set, so order and multiplicity are absent. Model semantics and representation semantics are independent supplied functions; observations need not be semantic outputs. `AgreeOn` is equality of semantic `Option` values throughout the source.

A `BoundedEnumeration` consists only of `decode : Nat → Nat × Nat` and `runWithin : Nat → Nat → Input → Option Output`. Its candidate semantics applies `runWithin` to the two decoded components and the input. The exported structure includes no coverage, resource-bound correctness, or effectiveness law. A `TimeBoundObservation` has input, output value, and natural-number timeBound fields; unlike labeled observations, its value is not optional. `TimeObservedCorrectOn` requires one candidate to return `some value` at each input's exact supplied budget.

A `Mealy State A B` contains a start state and total step function `State → A → State × B`. Running a finite word recursively emits one B per A and returns its final state and complete output list. There is **no Fintype State assumption** in the relevant types. A `PolicyMachine State Tape` similarly contains a start state and a total step returning a next state and `TapeAction`, where an action records a written symbol and one of left/right/stay. `toFST` simply packages these same fields as a Mealy machine. The supplied run consumes a prescribed scanned-symbol list; it does not maintain and revisit an actual tape according to those action labels. `rationalSemantics` is always `some` of the complete output list.

For the Turing-specific interface, a program is a finite list of `(nextState, writtenSymbol, headMove)` instructions. Lookup uses a natural pairing of the current state and encoded scanned symbol. Missing instructions default to state 0, the same scanned symbol, and stay. Configurations start in state 1; state 0 halts. A tape has a left list, scanned symbol, and right list, with a supplied blank used beyond stored lists. `runWithin` performs the natural-number budget of steps, retains halted configurations, and reads an optional output only at state 0. `TuringIO` supplies blank, input-to-tape initialization, and partial tape-to-output reading; their effectiveness is not an assumption. A candidate natural number unpairs into scale and program code, and invalid program codes decode to the empty list.

All implicit types were checked against explicit applications and predicate signatures. In particular, the rational-enumeration input domain is `List A`, its semantic output domain is **List B**, its representation domain is Nat, and the final merge witness domain is Config. Universes and Sort-polymorphism do not add finiteness, decidability, encoding, or algorithmic assumptions beyond the displayed binders.

## Target dossiers

### 1. `GenLimit.LearningAlgorithmsLimit.Results.lemma_9_distinguishability`

Source anchor supplied by the interface: `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:27`. Original target type, quoted verbatim:

```lean
∀ {Input : Type u_1} {Obs : Type u_2} {Rep : Sort u_3} {Model : Sort u_4} {Output : Type u_5}
  {learner : Set.{max u_2 u_1} (Prod.{u_1, u_2} Input Obs) → Rep} {observe : Model → Input → Obs}
  {modelSemantics : Model → Input → Option.{u_5} Output} {representationSemantics : Rep → Input → Option.{u_5} Output}
  {source coreM coreN : Set.{u_1} Input} {m n : Model},
  GenLimit.LearningAlgorithmsLimit.IsCharacteristicSet.{u_1, u_2, u_3, u_4, u_5} learner observe modelSemantics
      representationSemantics source m coreM →
    GenLimit.LearningAlgorithmsLimit.IsCharacteristicSet.{u_1, u_2, u_3, u_4, u_5} learner observe modelSemantics
        representationSemantics source n coreN →
      Not (GenLimit.LearningAlgorithmsLimit.AgreeOn.{u_4, u_1, u_5} modelSemantics source m n) →
        ∃ x,
          And (Membership.mem.{u_1, u_1} (Union.union.{u_1} coreM coreN) x) (Ne.{u_2 + 1} (observe m x) (observe n x))
```

**Reconstruction and quantifiers.** Fix arbitrary Input, Obs and Output types and arbitrary Rep and Model sorts, a single set learner, observation function, both semantic functions, a common source, two models m and n, and two cores. If coreM is characteristic for m and coreN characteristic for n under these same interfaces, and m and n do not agree semantically on the source, then there is an input x in `coreM ∪ coreN` whose observations differ: `observe m x ≠ observe n x`. Skeleton: `∀ interfaces, source, m, n, cores; char(m,coreM) → char(n,coreN) → ¬∀x∈source, sem(m,x)=sem(n,x) → ∃x∈coreM∪coreN, obs(m,x)≠obs(n,x)`.

**Information and dependencies.** Each characteristic premise quantifies all intermediate input sets and guarantees correctness of the learner's representation on the entire source. The learner sees a graph of observations, not m or n, their semantics, or a source-membership oracle as a separate argument. Rep need not coincide with Model. The distinguishing x may depend on every fixed interface and both given characteristic cores. The conclusion supplies a semantic existence witness, with no method or timing bound for finding it.

**Limits and edge cases.** The statement does not construct either characteristic core, impose finite size, or assert that every observational difference is a semantic difference. Semantic disagreement includes differing defined values or `none` versus `some`. An empty source makes the disagreement hypothesis impossible. Empty union cores cannot satisfy all three premises together. The same-model case also makes the disagreement hypothesis impossible; no distinctness assumption was silently added.

### 2. `GenLimit.LearningAlgorithmsLimit.Results.theorem_12_timeRestrictedIOO_core`

Source anchor supplied by the interface: `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:45`. Original target type, quoted verbatim:

```lean
∀ {Output : Type u_1} {Input : Type u_2} [inst : DecidableEq.{u_1 + 1} Output]
  (enumeration : GenLimit.LearningAlgorithmsLimit.BoundedEnumeration.{u_2, u_1} Input Output)
  (target : Input → Option.{u_1} Output) (stream : Nat → Input) (source : Set.{u_2} Input),
  GenLimit.LearningAlgorithmsLimit.Covers.{u_2} stream source →
    (∃ candidate,
        GenLimit.LearningAlgorithmsLimit.CorrectOn.{1, u_2, u_1}
          (GenLimit.LearningAlgorithmsLimit.BoundedEnumeration.semantics.{u_2, u_1} enumeration) target source
          candidate) →
      GenLimit.LearningAlgorithmsLimit.LearnsInLimit.{max u_2 u_1, 0, u_2, u_1}
        (GenLimit.LearningAlgorithmsLimit.labeledEnumerationLearner.{u_1, u_2}
          (GenLimit.LearningAlgorithmsLimit.BoundedEnumeration.semantics.{u_2, u_1} enumeration))
        (GenLimit.LearningAlgorithmsLimit.labeledStream.{u_2, u_1} target stream)
        (GenLimit.LearningAlgorithmsLimit.BoundedEnumeration.semantics.{u_2, u_1} enumeration) target source
```

**Reconstruction and quantifiers.** For arbitrary Output with decidable equality, arbitrary Input, an enumeration E, optional target function f, stream s, and source S, assume `range s = S` and `∃ c : Nat, ∀ x∈S, E.semantics c x = f x`. Then the specific labeled enumeration learner for `E.semantics`, receiving records `(s n, f(s n))`, stabilizes to one natural-number representation r correct on S. Expanded conclusion: `∃ r : Nat, (∀ x∈S, E.semantics r x=f x) ∧ ∃ T : Nat, ∀ t≥T, learner(prefix t)=r`. The premise's c precedes the conclusion witnesses; neither r nor T is supplied to the learner.

**Information and dependencies.** E is fixed in the learner. The data contain exact optional labels, including `none`. At history length t the search includes precisely indices at most t, so an existing correct candidate eventually enters the search and is consistent with every record. The source and the existence certificate are proof assumptions, not additional history fields. The chosen r and convergence threshold may depend on E, f, s and S. The theorem states an unspecified correct stabilized index, not equality with the supplied witness or an explicit minimum-index conclusion.

**Limits and edge cases.** The structure does not certify that its two decoded naturals encode actual clocks or Turing programs. An ordinary effective learner requires effective supplied operations; decidable output equality alone does not establish them. There is no sample or runtime bound. Repeated inputs and duplicate candidate semantics are allowed. Finite sources work through repetitions; empty-source coverage is impossible. No correctness outside S, totality of f, or restriction excluding `none` is assumed.

### 3. `GenLimit.LearningAlgorithmsLimit.Results.theorem_12_minIndex_claim_not_justified`

Source anchor supplied by the interface: `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:62`. Original target type, quoted verbatim:

```lean
And
  (∃ budget,
    Eq.{1} (GenLimit.LearningAlgorithmsLimit.minIndexDiagnosticRun budget 0 Unit.unit) (Option.some.{0} Bool.false))
  (And
    (∃ budget,
      Eq.{1} (GenLimit.LearningAlgorithmsLimit.minIndexDiagnosticRun budget 1 Unit.unit) (Option.some.{0} Bool.false))
    (And (Eq.{1} (GenLimit.LearningAlgorithmsLimit.minIndexDiagnosticRun 2 0 Unit.unit) Option.none.{0})
      (Eq.{1} (GenLimit.LearningAlgorithmsLimit.minIndexDiagnosticRun 2 1 Unit.unit) (Option.some.{0} Bool.false))))
```

**Reconstruction and quantifiers.** This closed proposition has four conjuncts: (1) there exists a natural budget at which representation 0 on the sole Unit input returns `some false`; (2) there exists a natural budget at which representation 1 returns `some false`; (3) at budget exactly 2, representation 0 returns `none`; and (4) at budget exactly 2, representation 1 returns `some false`. Skeleton: `(∃ b0, run b0 0 ()=some false) ∧ (∃ b1, run b1 1 ()=some false) ∧ run 2 0 ()=none ∧ run 2 1 ()=some false`. The two existential budgets are separate witnesses, without an asserted equality between them.

**Definition and dependencies.** The supplied diagnostic function ignores its Unit argument. For representation 0 it returns `some false` iff budget ≥10; for representation 1 iff budget ≥2; for every other representation it returns `none`. Thus 10 and 2 respectively are concrete compatible witnesses from the definition. The theorem's named identifier contributes no additional logical content. There is no learner, source, observation history, general enumeration, or minimum-selection function in the type.

**Limits and edge cases.** This establishes the displayed diagnostic behavior only. It does not itself negate a universally quantified minimum-index theorem, prove failure of every learning procedure, or characterize all time-restricted representations. At small budgets both values may be absent; at budget at least 10 both named representations return the same value. Those definitional facts explain the example's scope without importing a claim from a named source theorem.

### 4. `GenLimit.LearningAlgorithmsLimit.Results.corollary_13_parametrizedTMClass_core`

Source anchor supplied by the interface: `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:70`. Original target type, quoted verbatim:

```lean
∀ {Output : Type u_1} {Input : Type u_2} [inst : DecidableEq.{u_1 + 1} Output]
  (enumeration : GenLimit.LearningAlgorithmsLimit.BoundedEnumeration.{u_2, u_1} Input Output)
  (target : Input → Option.{u_1} Output) (stream : Nat → Input) (source : Set.{u_2} Input),
  GenLimit.LearningAlgorithmsLimit.Covers.{u_2} stream source →
    (∃ candidate,
        GenLimit.LearningAlgorithmsLimit.CorrectOn.{1, u_2, u_1}
          (GenLimit.LearningAlgorithmsLimit.BoundedEnumeration.semantics.{u_2, u_1} enumeration) target source
          candidate) →
      GenLimit.LearningAlgorithmsLimit.LearnsInLimit.{max u_2 u_1, 0, u_2, u_1}
        (GenLimit.LearningAlgorithmsLimit.labeledEnumerationLearner.{u_1, u_2}
          (GenLimit.LearningAlgorithmsLimit.BoundedEnumeration.semantics.{u_2, u_1} enumeration))
        (GenLimit.LearningAlgorithmsLimit.labeledStream.{u_2, u_1} target stream)
        (GenLimit.LearningAlgorithmsLimit.BoundedEnumeration.semantics.{u_2, u_1} enumeration) target source
```

**Reconstruction and quantifiers.** This target has exactly the same supplied kernel type as dossier 2. For every optional-output enumeration E over arbitrary Input and decidable-equality Output, target f, stream s, and source S, exact stream coverage and the existence of one source-correct natural index imply eventual stabilization of the specified labeled enumeration learner to a source-correct natural index. In full witness order: `∀ E,f,s,S; Covers s S → (∃ c:Nat, CorrectOn E.semantics f S c) → ∃ r:Nat, CorrectOn E.semantics f S r ∧ ∃ T:Nat, ∀ t≥T, guess(t)=r`.

**Information and dependencies.** The learner uses the semantics supplied by E and only the finite list of labeled stream records. At length t it checks candidates 0 through t and returns the least history-consistent one, or 0 if none is available. Neither the correct witness, target function, source set, nor any convergence certificate is a direct learner input. Stabilization is of the index itself, even if many indices denote the same source behavior.

**Limits and edge cases.** There is no extra family parameter, Turing-machine type, encoded parametrization, clock law, or effective-enumeration certificate in this target's binders. Those cannot be supplied by its name. The conclusion has no rate or prescribed final index. It covers finite or infinite presented sources, permits repetitions and `none` labels, and says nothing outside the source. A covering stream cannot present the empty set. Thus this dossier preserves the identical claim independently rather than treating the target label as evidence of a stronger specialization.

### 5. `GenLimit.LearningAlgorithmsLimit.Results.theorem_14_universalTBO_core`

Source anchor supplied by the interface: `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:86`. Original target type, quoted verbatim:

```lean
∀ {Output : Type u_1} {Input : Type u_2} [inst : DecidableEq.{u_1 + 1} Output]
  (simulate : Nat → Input → Nat → Option.{u_1} Output)
  (observation : Input → GenLimit.LearningAlgorithmsLimit.TimeBoundObservation.{u_2, u_1} Input Output)
  (stream : Nat → Input) (source : Set.{u_2} Input),
  GenLimit.LearningAlgorithmsLimit.Covers.{u_2} stream source →
    (∀ (input : Input),
        Membership.mem.{u_2, u_2} source input →
          Eq.{u_2 + 1} (GenLimit.LearningAlgorithmsLimit.TimeBoundObservation.input.{u_2, u_1} (observation input))
            input) →
      (∃ candidate,
          GenLimit.LearningAlgorithmsLimit.TimeObservedCorrectOn.{u_2, u_1} simulate observation source candidate) →
        GenLimit.LearningAlgorithmsLimit.LearnsByCriterion.{max u_2 u_1, 0}
          (GenLimit.LearningAlgorithmsLimit.timeObservedLearner.{u_1, u_2} simulate) (fun n => observation (stream n))
          (GenLimit.LearningAlgorithmsLimit.TimeObservedCorrectOn.{u_2, u_1} simulate observation source)
```

**Reconstruction and quantifiers.** Fix arbitrary Input and decidable-equality Output, `simulate : Nat → Input → Nat → Option Output`, an observation assignment o, stream s, and source S. Assume exact coverage; assume the input field of o(x) equals x for every x∈S; and assume one natural candidate c satisfies `simulate c x (o(x).timeBound) = some(o(x).value)` for every x∈S. Then the named time-observed learner on the sequence o(s n) stabilizes to a natural r satisfying that same whole-source criterion. Skeleton: `∀ simulate,o,s,S; coverage → input-coherence → (∃ c, ∀x∈S, fits(c,x)) → ∃ r, (∀x∈S, fits(r,x)) ∧ ∃T, ∀t≥T, guess(t)=r`.

**Information and dependencies.** Each record exposes its input, output, and natural budget. The learner tests the supplied simulator at that exact budget, uses the common finite minimum-consistent-index search, and has no target program as an input. The coherence premise connects the record's field to the domain input used by the correctness criterion. One candidate must fit all source records, rather than each input having an unrelated candidate.

**Limits and edge cases.** The simulator is arbitrary; no monotonicity in budget, universal-machine property, or ordinary computability certificate is required. There is no multiplicative slack parameter in this theorem. Zero budgets are allowed, subject to the fitting-candidate premise. The observation assignment must give the same record at repeated occurrences of an input. No finite convergence bound follows from the type; records off S are unconstrained. Coverage excludes an empty source and allows repetitions and finite sources.

### 6. `GenLimit.LearningAlgorithmsLimit.Results.corollary_15_turingTBO`

Source anchor supplied by the interface: `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:103`. Original target type, quoted verbatim:

```lean
∀ {Symbol : Type u_1} {Output : Type u_2} {Input : Type u_3} [Fintype.{u_1} Symbol] [DecidableEq.{u_1 + 1} Symbol]
  [inst : Encodable.{u_1} Symbol] [inst_1 : DecidableEq.{u_2 + 1} Output]
  (io : GenLimit.LearningAlgorithmsLimit.TuringIO.{u_1, u_3, u_2} Symbol Input Output),
  GenLimit.LearningAlgorithmsLimit.SolvesTuringTBO.{u_1, u_3, u_2} io
    (GenLimit.LearningAlgorithmsLimit.turingTBOLearner.{u_1, u_2, u_3} io)
```

**Reconstruction and quantifiers.** For every finite Symbol type with decidable equality and an Encodable instance, every Output type with decidable equality, arbitrary Input, and a supplied TuringIO io, the specific `turingTBOLearner io` solves the expanded task. For **every** target finite program P, source S, stream s and observation assignment o, if s covers S and o is a Turing time-bound observation for P on S, then there exist a natural candidate r and threshold T such that all guesses from T onward equal r and its decoded program computes the observed output on every x∈S. Computation in the conclusion is `∀ x∈S, ∃ budget, runWithin budget io (program r) x = some(o(x).value)`.

**Certificates and information.** The observation hypothesis includes input-field coherence and `∃ scale : Nat, ∀ x∈S, runWithin (scale * o(x).timeBound) io P x = some(o(x).value)`. This is one source-wide scale, allowed to depend on P, io, S and o. It is not a separately chosen scale per input. Candidate naturals encode scale and program code. The learner tests each candidate using its scale times the observed bound; it receives records and fixed io, not P, the witnessing scale, S, or a stopping certificate. The same named learner works for all P, S, s and o at that io.

**Limits and edge cases.** The displayed learned-program criterion has pointwise budget witnesses, not an explicit uniform-scale guarantee for the final r. Input and Output need no encoding; io initialization and output reading are arbitrary functions. Consequently the statement does not certify an ordinary effective pipeline for arbitrary io. Symbol finiteness does not make the set of programs finite. Scales and bounds are natural numbers including zero, although impossible observation cases are excluded by their premise. No correctness off S, exact recovery of P, runtime rate, or finite stopping test is asserted. Empty-source coverage is impossible.

### 7. `GenLimit.LearningAlgorithmsLimit.Results.theorem_16_recursiveToRational_behavior`

Source anchor supplied by the interface: `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:113`. Original target type, quoted verbatim:

```lean
∀ {State : Type u_1} {Tape : Type u_2} (M : GenLimit.LearningAlgorithmsLimit.PolicyMachine.{u_1, u_2} State Tape)
  (scanned : List.{u_2} Tape),
  Eq.{u_2 + 1} (GenLimit.LearningAlgorithmsLimit.PolicyMachine.tapeBehavior.{u_1, u_2} M scanned)
    (GenLimit.LearningAlgorithmsLimit.Mealy.run.{u_1, u_2, u_2}
        (GenLimit.LearningAlgorithmsLimit.PolicyMachine.toFST.{u_1, u_2} M) scanned).2
```

**Reconstruction and quantifiers.** For any State and Tape types, any supplied policy machine M, and any finite prescribed list of scanned Tape symbols, M's `tapeBehavior` equals the second component of the run of `M.toFST` on that list. The equality domain, exposed explicitly, is `List (TapeAction Tape)`. Skeleton: `∀ State,Tape,M,scanned; tapeBehavior M scanned = (Mealy.run (toFST M) scanned).2`. There are no hypotheses and no existential conversion witness.

**Definition and available data.** A policy machine has a start state and total transition function returning the next state and a written-symbol/head-move action. The conversion retains this start and transition function. `tapeBehavior` is itself defined by the same second-component expression. Each symbol in the prescribed list therefore contributes one recorded action; the recursive Mealy run threads state through the list. This is a behavioral equality of the supplied formal objects, independently of the target's descriptive name.

**Limits and edge cases.** The type has no finite-state premise, Turing-program argument, recursiveness certificate, or existence theorem converting all recursive functions into rational transductions. It does not assert that actual tape movement would generate the supplied scanned sequence. No learner, representation index, stream, source restriction, or time budget occurs. The empty list yields the empty action list on both sides; the final state is not part of the displayed equality. State need not be finite or encodable; the supplied M already includes a start state.

### 8. `GenLimit.LearningAlgorithmsLimit.Results.theorem_16_rationalEnumeration_core`

Source anchor supplied by the interface: `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:120`. Original target type, quoted verbatim:

```lean
∀ {B : Type u_1} {State : Type u_2} {A : Type u_3} [inst : DecidableEq.{u_1 + 1} B]
  (machines : Nat → GenLimit.LearningAlgorithmsLimit.Mealy.{u_2, u_3, u_1} State A B) (targetIndex : Nat)
  (stream : Nat → List.{u_3} A) (source : Set.{u_3} (List.{u_3} A)),
  GenLimit.LearningAlgorithmsLimit.Covers.{u_3} stream source →
    GenLimit.LearningAlgorithmsLimit.LearnsInLimit.{max u_3 u_1, 0, u_3, u_1}
      (GenLimit.LearningAlgorithmsLimit.labeledEnumerationLearner.{u_1, u_3} fun j =>
        GenLimit.LearningAlgorithmsLimit.rationalSemantics.{u_2, u_3, u_1} (machines j))
      (GenLimit.LearningAlgorithmsLimit.labeledStream.{u_3, u_1}
        (GenLimit.LearningAlgorithmsLimit.rationalSemantics.{u_2, u_3, u_1} (machines targetIndex)) stream)
      (fun j => GenLimit.LearningAlgorithmsLimit.rationalSemantics.{u_2, u_3, u_1} (machines j))
      (GenLimit.LearningAlgorithmsLimit.rationalSemantics.{u_2, u_3, u_1} (machines targetIndex)) source
```

**Reconstruction and quantifiers.** For arbitrary A, B and State, with decidable equality on B, fix a sequence `machines : Nat → Mealy State A B`, any targetIndex k, a stream of finite A-words, and a source of finite A-words. If the stream covers the source, the labeled enumeration learner for this machine family stabilizes to a natural r whose complete output word equals that of `machines k` on every source word. Skeleton: `∀ machines,k,s,S; Covers s S → ∃ r:Nat, (∀w∈S, rationalSemantics(machines r) w = rationalSemantics(machines k) w) ∧ ∃T, ∀t≥T, guess(t)=r`.

**Information and hidden domains.** Explicit application fixes Input to `List A`, semantic Output to **List B**, Info to labeled word/optional-output-word records, and representation to Nat. Thus the equality concerns entire output lists, not a selected symbol, support, language membership, or single-output loss. `rationalSemantics` always returns `some` of the run's output list. The data are generated using k; the learner is parametrized only by the machine family and the history, not by k. Family membership of the target supplies a correct candidate without an additional existence premise.

**Limits and edge cases.** No exhaustive enumeration of all machines is required, and State, A and B need not be finite. The family and its transition functions have no ordinary-computability certificates. Repeated machines or behaviorally identical indices are allowed; final r need not equal k. Words may be empty, giving `some []`; sources may be finite or infinite, with no convergence rate. Coverage rules out an empty source. Correctness concerns the source only and does not identify internal states or behavior elsewhere.

### 9. `GenLimit.LearningAlgorithmsLimit.Results.theorem_17_lateSplit_characteristic_obstruction`

Source anchor supplied by the interface: `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:140`. Original target type, quoted verbatim:

```lean
∀ (learner : Set.{0} (Prod.{0, 0} Nat Bool) → Bool) (splitAt : Nat) (coreFalse coreTrue : Set.{0} Nat),
  GenLimit.LearningAlgorithmsLimit.IsCharacteristicSet.{0, 0, 1, 1, 0} learner
      (GenLimit.LearningAlgorithmsLimit.lateSplitObservation splitAt)
      (GenLimit.LearningAlgorithmsLimit.lateSplitSemantics splitAt)
      (GenLimit.LearningAlgorithmsLimit.lateSplitSemantics splitAt) Set.univ.{0} Bool.false coreFalse →
    GenLimit.LearningAlgorithmsLimit.IsCharacteristicSet.{0, 0, 1, 1, 0} learner
        (GenLimit.LearningAlgorithmsLimit.lateSplitObservation splitAt)
        (GenLimit.LearningAlgorithmsLimit.lateSplitSemantics splitAt)
        (GenLimit.LearningAlgorithmsLimit.lateSplitSemantics splitAt) Set.univ.{0} Bool.true coreTrue →
      ∃ n, And (Membership.mem.{0, 0} (Union.union.{0} coreFalse coreTrue) n) (LE.le.{0} splitAt n)
```

**Reconstruction and quantifiers.** Fix any set learner `Set (Nat × Bool) → Bool`, any splitAt k, and any two sets of naturals CF and CT. If CF is characteristic for model false and CT characteristic for model true under the displayed observations and semantics over all naturals, then `∃ n : Nat, n∈CF∪CT ∧ k≤n`. Skeleton: `∀ learner,k,CF,CT; char(false,CF) → char(true,CT) → ∃n∈CF∪CT, n≥k`.

**Meaning of the concrete interfaces.** At input n, an observation is false before k and the model's branch Boolean at or after k. Its semantics is `some` of that observation. Model and representation domains are both Bool, with the same semantic map; the learner's Boolean output is interpreted as one of these two behaviors. The false model returns false everywhere, while the true model first differs at k. Each characteristic premise still demands source-wide correctness for every input set between the core and all naturals. The information is an unordered set of input/Boolean pairs.

**Limits and edge cases.** Neither core is assumed finite; no stream or delay rate is involved. The witness must lie in the union, so the result does not require each core separately to contain a late input or to contain k itself. It supplies no bound on cardinality, mass, runtime, or a procedure to find n. At k=0 the conclusion requires a union member with the automatically true inequality n≥0. Two empty cores cannot simultaneously meet the premises; the theorem does not construct characteristic cores for an arbitrary learner.

### 10. `GenLimit.LearningAlgorithmsLimit.Results.theorem_17_mass_lower_bound_core`

Source anchor supplied by the interface: `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:158`. Original target type, quoted verbatim:

```lean
∀ (learner : Set.{0} (Prod.{0, 0} Nat Bool) → Bool) (splitAt : Nat) (coreFalse coreTrue : Finset.{0} Nat),
  GenLimit.LearningAlgorithmsLimit.IsCharacteristicSet.{0, 0, 1, 1, 0} learner
      (GenLimit.LearningAlgorithmsLimit.lateSplitObservation splitAt)
      (GenLimit.LearningAlgorithmsLimit.lateSplitSemantics splitAt)
      (GenLimit.LearningAlgorithmsLimit.lateSplitSemantics splitAt) Set.univ.{0} Bool.false ↑coreFalse →
    GenLimit.LearningAlgorithmsLimit.IsCharacteristicSet.{0, 0, 1, 1, 0} learner
        (GenLimit.LearningAlgorithmsLimit.lateSplitObservation splitAt)
        (GenLimit.LearningAlgorithmsLimit.lateSplitSemantics splitAt)
        (GenLimit.LearningAlgorithmsLimit.lateSplitSemantics splitAt) Set.univ.{0} Bool.true ↑coreTrue →
      LE.le.{0} (HAdd.hAdd.{0, 0, 0} splitAt 1)
        (HAdd.hAdd.{0, 0, 0} (GenLimit.LearningAlgorithmsLimit.inputMass coreFalse)
          (GenLimit.LearningAlgorithmsLimit.inputMass coreTrue))
```

**Reconstruction and quantifiers.** For every set learner, natural splitAt k, and finite sets CF and CT, assume their underlying sets are characteristic for the same false and true models over all naturals. Then `k+1 ≤ inputMass CF + inputMass CT`. Expanding the supplied measure gives `k+1 ≤ (Σ n∈CF, n+1) + (Σ n∈CT, n+1)`. Skeleton: `∀ learner,k,CF:Finset Nat,CT:Finset Nat; char(false,↑CF) → char(true,↑CT) → k+1≤mass(CF)+mass(CT)`.

**Dependencies and information.** The finite sets are supplied witnesses, not generated by the theorem. The learner still consumes sets of labeled inputs; coercing a Finset to a Set does not change the characteristic requirement to finite intermediate sets. Each core's finite mass is the sum of strictly positive input weights. This is a combined bound, depending explicitly on the chosen split threshold and the two given characteristic cores. It keeps both masses, the additive 1 on the left, and the additive 1 in every weight.

**Limits and edge cases.** Mass is neither cardinality nor a probability. Large individual indices can create large mass with few members, so this is not a sample-count lower bound. Overlap contributes separately to both terms; the conclusion is not the mass of the union. There is no rate in stream time or computational cost. With k=0 the lower bound is 1, so two empty cores are excluded by the hypotheses. For arbitrary k the theorem remains conditional on both finite characteristic cores existing; it does not prove that every learner has such cores.

### 11. `GenLimit.LearningAlgorithmsLimit.Results.corollary_18_forgetting_preserves_indistinguishability`

Source anchor supplied by the interface: `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:178`. Original target type, quoted verbatim:

```lean
∀ {Model : Sort u_1} {Input : Type u_2} {Rich : Sort u_3} {Poor : Sort u_4} (rich : Model → Input → Rich)
  (forget : Rich → Poor) {m n : Model} {inputs : Set.{u_2} Input},
  (∀ (x : Input), Membership.mem.{u_2, u_2} inputs x → Eq.{u_3} (rich m x) (rich n x)) →
    ∀ (x : Input), Membership.mem.{u_2, u_2} inputs x → Eq.{u_4} (forget (rich m x)) (forget (rich n x))
```

**Reconstruction and quantifiers.** For arbitrary Model, Rich and Poor sorts, arbitrary Input, an observation function rich, and one fixed map `forget : Rich → Poor`, fix models m,n and an input set I. If `rich m x = rich n x` for every x∈I, then `forget(rich m x) = forget(rich n x)` for every x∈I. Skeleton: `∀ rich,forget,m,n,I; (∀x∈I, rich m x=rich n x) → ∀x∈I, forget(rich m x)=forget(rich n x)`.

**Dependencies and information.** The same forgetting map is applied on both sides, with no additional dependence on model or input. The type expresses preservation of equality under an arbitrary function at each allowed input. It does not mention model semantics, learners, representations, examples, characteristic cores, or an inference procedure. Sort-polymorphism permits observations and models beyond ordinary data types without requiring any enumeration or decidability instances.

**Limits and edge cases.** No injectivity, surjectivity, effectiveness, or nontriviality of forget is assumed. A constant forgetting map is permitted, so equality after forgetting gives no reverse equality guarantee. The statement does not assert that every observational relation is a forgetting map or compare probabilities of observations. Empty I makes both universal statements vacuous; infinite I is allowed. Repeated models, empty types, and already equal observations need no special side conditions. There are no witnesses, rates, numerical constants, or hidden source-coverage assumptions in this target.

### 12. `GenLimit.LearningAlgorithmsLimit.Results.corollary_18_characteristic_bound_lifts_to_richer_observations`

Source anchor supplied by the interface: `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:188`. Original target type, quoted verbatim:

```lean
∀ {Input : Type u_1} {Poor : Type u_2} {Rep : Sort u_3} {Model : Sort u_4} {Rich : Type u_5} {Output : Type u_6}
  (learner : Set.{max u_2 u_1} (Prod.{u_1, u_2} Input Poor) → Rep) (rich : Model → Input → Rich) (forget : Rich → Poor)
  (modelSemantics : Model → Input → Option.{u_6} Output) (representationSemantics : Rep → Input → Option.{u_6} Output)
  (source : Set.{u_1} Input) (mass : Set.{u_1} Input → Nat) (bound : Model → Nat),
  (∀ (m : Model),
      ∃ core,
        And
          (GenLimit.LearningAlgorithmsLimit.IsCharacteristicSet.{u_1, u_2, u_3, u_4, u_6} learner
            (fun model input => forget (rich model input)) modelSemantics representationSemantics source m core)
          (LE.le.{0} (mass core) (bound m))) →
    ∀ (m : Model),
      ∃ core,
        And
          (GenLimit.LearningAlgorithmsLimit.IsCharacteristicSet.{u_1, u_5, u_3, u_4, u_6}
            (GenLimit.LearningAlgorithmsLimit.liftLearnerAlongForget.{u_1, u_2, u_3, u_5} learner forget) rich
            modelSemantics representationSemantics source m core)
          (LE.le.{0} (mass core) (bound m))
```

**Reconstruction and quantifiers.** Fix Input, Poor, Rich and Output types, arbitrary Rep and Model sorts, a poor-observation set learner L, rich observations R, a map f forgetting Rich to Poor, the two semantic functions, a source S, arbitrary `mass : Set Input → Nat`, and `bound : Model → Nat`. Assume `∀ m, ∃ C, characteristic(L, f∘R, S,m,C) ∧ mass C ≤ bound m`. Then `∀ m, ∃ C, characteristic(liftLearnerAlongForget L f, R, S,m,C) ∧ mass C ≤ bound m`. All interfaces, S, mass and bound are fixed before either model-wise quantifier.

**Information and dependencies.** The lifted learner maps a rich example set to the poor set consisting of `(x,f(observation))` for every `(x,observation)` in it, then invokes L. The rich observation graph therefore supplies exactly the poor graph on the same inputs. A premise core can be reused unchanged; the displayed conclusion records existence and its same numerical bound rather than an equality between named witnesses. C can depend on m and all the fixed interfaces. The lifted learner is one fixed function for all models, while core existence is model-wise.

**Limits and edge cases.** Neither C nor intermediate example sets must be finite. The arbitrary mass function need not be cardinality, monotone, additive, or related to input length; the bound need not satisfy a growth law. No algorithm for finding cores or computing set images is certified. An empty source is allowed here because there is no stream; the only possible core and intermediate input set are empty, and source correctness is vacuous. No injectivity of f is needed, and no converse bound transfer is asserted.

### 13. `GenLimit.LearningAlgorithmsLimit.Results.theorem_21_tagged_two_step`

Source anchor supplied by the interface: `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:213`. Original target type, quoted verbatim:

```lean
∀ {State : Type u_1} {Tape : Type u_2} [inst : DecidableEq.{u_1 + 1} State] [inst_1 : DecidableEq.{u_2 + 1} Tape]
  (M : GenLimit.LearningAlgorithmsLimit.PolicyMachine.{u_1, u_2} State Tape) (q : State) (a : Tape),
  Eq.{max (u_2 + 1) (u_1 + 1)}
    (GenLimit.LearningAlgorithmsLimit.Mealy.runFrom.{max u_2 u_1, max u_2 u_1, max u_2 u_1}
      (GenLimit.LearningAlgorithmsLimit.PolicyMachine.toFST.{max u_2 u_1, max u_2 u_1}
        (GenLimit.LearningAlgorithmsLimit.taggedMachine.{u_1, u_2} M))
      (Sum.inl.{u_1, max u_2 u_1} q)
      (List.cons.{max u_2 u_1} (Sum.inl.{u_2, max u_2 u_1} a)
        (List.cons.{max u_2 u_1} (Sum.inr.{u_2, max u_2 u_1} (Prod.mk.{u_1, u_2} q a)) List.nil.{max u_2 u_1})))
    (Prod.mk.{max u_2 u_1, max u_2 u_1}
      (Sum.inl.{u_1, max u_2 u_1} (GenLimit.LearningAlgorithmsLimit.PolicyMachine.step.{u_1, u_2} M q a).1)
      (List.cons.{max u_2 u_1} (GenLimit.LearningAlgorithmsLimit.markerAction.{u_1, u_2} (Prod.mk.{u_1, u_2} q a))
        (List.cons.{max u_2 u_1}
          (GenLimit.LearningAlgorithmsLimit.liftAction.{u_2, u_1}
            (GenLimit.LearningAlgorithmsLimit.PolicyMachine.step.{u_1, u_2} M q a).2)
          List.nil.{max u_2 u_1})))
```

**Reconstruction and quantifiers.** For arbitrary State and Tape with decidable equality, a policy machine M, any state q and scanned symbol a, let `(q',action) = M.step q a`. Running the converted tagged machine from normal state `inl q` on the two-symbol word `[inl a, inr(q,a)]` yields exactly the pair `(inl q', [markerAction(q,a), liftAction(action)])`. Skeleton: `∀ M,q,a; runFrom(toFST(taggedMachine M), inl q, [inl a,inr(q,a)]) = (inl(M.step q a).1, [marker(q,a),lift((M.step q a).2)])`.

**Definitions and data.** Tagged states are `State ⊕ (State × Tape)` and tagged symbols are `Tape ⊕ (State × Tape)`. The first step enters pending state `inr(q,a)` and writes that tag with stay. The matching tag then triggers the original step, returns to a normal state, writes the original action's symbol as an `inl`, and retains its head move. Equality tests on State and Tape allow checking the matching pair. The final-state and the two-action-list components are both essential parts of the equality.

**Limits and edge cases.** q need not be M's start state, and State need not be finite. The particular tag is exactly the prescribed matching tag; this theorem does not state the same simulation for arbitrary or mismatched tags. It is an equality of Mealy runs on supplied scanned symbols, not an assertion that a physical tape automatically presents those two symbols. There is no learner, source, characteristic set, minimality result, or runtime complexity claim beyond the explicit two-symbol expansion.

### 14. `GenLimit.LearningAlgorithmsLimit.Results.taggedMachine_runFrom`

Source anchor supplied by the interface: `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:223`. Original target type, quoted verbatim:

```lean
∀ {State : Type u_1} {Tape : Type u_2} [inst : DecidableEq.{u_1 + 1} State] [inst_1 : DecidableEq.{u_2 + 1} Tape]
  (M : GenLimit.LearningAlgorithmsLimit.PolicyMachine.{u_1, u_2} State Tape) (q : State) (w : List.{u_2} Tape),
  Eq.{max (u_2 + 1) (u_1 + 1)}
    (GenLimit.LearningAlgorithmsLimit.Mealy.runFrom.{max u_2 u_1, max u_2 u_1, max u_2 u_1}
      (GenLimit.LearningAlgorithmsLimit.PolicyMachine.toFST.{max u_2 u_1, max u_2 u_1}
        (GenLimit.LearningAlgorithmsLimit.taggedMachine.{u_1, u_2} M))
      (Sum.inl.{u_1, max u_2 u_1} q) (GenLimit.LearningAlgorithmsLimit.taggedScannedFrom.{u_1, u_2} M q w))
    (Prod.mk.{max u_2 u_1, max u_2 u_1}
      (Sum.inl.{u_1, max u_2 u_1}
        (GenLimit.LearningAlgorithmsLimit.Mealy.runFrom.{u_1, u_2, u_2}
            (GenLimit.LearningAlgorithmsLimit.PolicyMachine.toFST.{u_1, u_2} M) q w).1)
      (GenLimit.LearningAlgorithmsLimit.taggedActionsFrom.{u_1, u_2} M q w))
```

**Reconstruction and quantifiers.** For arbitrary State and Tape with decidable equality, a policy machine M, any q, and any finite scanned word w, run the tagged conversion from `inl q` on `taggedScannedFrom M q w`. The result equals `(inl qFinal, taggedActionsFrom M q w)`, where qFinal is the final state of the original converted policy machine run from q on w. Skeleton: `∀ M,q,w; runTagged(inl q, taggedScannedFrom M q w) = (inl(runOriginal(q,w).1), taggedActionsFrom M q w)`.

**State-dependent encoding.** For an empty word, both generated lists are empty. For head a at state q, the scanned encoding prepends `[inl a, inr(q,a)]` and recurses on the tail at `(M.step q a).1`. The output encoding prepends the marker action and lifted original action, with the same recursive state. Thus encoding the word depends on M and the evolving state, rather than being a fixed symbolwise map independent of the model. Each original symbol contributes two tagged inputs and two recorded actions; the theorem preserves the exact final normal state and entire generated action sequence.

**Limits and edge cases.** Arbitrary finite w, including empty words, are covered, but arbitrary tagged input words are not. The output equality includes tags; it is not literal equality of tagged and untagged action lists. The assertion is uniform as a mathematical identity for supplied M,q,w, without an ordinary-computability certificate for M's abstract transition function. No finiteness of State, real-tape reachability hypothesis, learning algorithm, rate, or program-identification guarantee appears.

### 15. `GenLimit.LearningAlgorithmsLimit.Results.theorem_21_transition_cover_core`

Source anchor supplied by the interface: `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:233`. Original target type, quoted verbatim:

```lean
∀ {Transition : Type u_1} {Sample : Type u_2} [DecidableEq.{u_1 + 1} Transition] [inst : DecidableEq.{u_2 + 1} Sample]
  (used : Finset.{u_1} Transition) (exercises : Sample → Set.{u_1} Transition) (witness : Transition → Sample),
  (∀ (e : Transition), Membership.mem.{u_1, u_1} used e → Membership.mem.{u_1, u_1} (exercises (witness e)) e) →
    ∀ (stream : Nat → Sample) (source : Set.{u_2} Sample),
      GenLimit.LearningAlgorithmsLimit.Covers.{u_2} stream source →
        (∀ (e : Transition), Membership.mem.{u_1, u_1} used e → Membership.mem.{u_2, u_2} source (witness e)) →
          And
            (LE.le.{0} (Finset.card.{u_2} (GenLimit.LearningAlgorithmsLimit.transitionCover.{u_2, u_1} used witness))
              (Finset.card.{u_1} used))
            (And
              (∀ (e : Transition),
                Membership.mem.{u_1, u_1} used e →
                  ∃ sample,
                    And
                      (Membership.mem.{u_2, u_2}
                        (GenLimit.LearningAlgorithmsLimit.transitionCover.{u_2, u_1} used witness) sample)
                      (Membership.mem.{u_1, u_1} (exercises sample) e))
              (∃ t,
                ∀ (sample : Sample),
                  Membership.mem.{u_2, u_2} (GenLimit.LearningAlgorithmsLimit.transitionCover.{u_2, u_1} used witness)
                      sample →
                    ∃ n, And (LT.lt.{0} n t) (Eq.{u_2 + 1} (stream n) sample)))
```

**Reconstruction and quantifiers.** Fix arbitrary Transition and Sample types with decidable equality, a finite set U of used transitions, `exercises : Sample → Set Transition`, and a total witness function W. Assume `∀ e∈U, e∈exercises(W e)`. For every stream s and source S, if s covers S and every W e for e∈U belongs to S, then for `Q = transitionCover U W = U.image W` all three conclusions hold: `|Q|≤|U|`; every e∈U is exercised by some sample in Q; and `∃ t:Nat, ∀ sample∈Q, ∃ n:Nat, n<t ∧ s n=sample`. These conclusions form one conjunction.

**Dependencies and information.** U, exercises and W are fixed before the stream and source quantifiers. The finite image Q may identify several transitions' witnesses. The appearance-time t is shared across the whole finite cover and can depend on s and S as well as U and W. The occurrence index n is chosen after sample, so different samples may appear at different indices below that one bound. The witness function is supplied, with its exercise and source-membership certificates; the theorem does not find that function from unlabeled samples.

**Limits and edge cases.** There is no upper bound on t in terms of |U| or |Q|: coverage allows arbitrarily late first occurrences. Repeated stream inputs and duplicate witness values are allowed. If U is empty, Q is empty and t=0 satisfies the last conjunct vacuously. Infinite source sets and exercise sets are allowed; only U and Q must be finite. The words transition and exercises name abstract types and a relation here, with no particular machine semantics, learner convergence, or state-recovery theorem included.

### 16. `GenLimit.LearningAlgorithmsLimit.Results.theorem_21_msm_merge_order_core`

Source anchor supplied by the interface: `GenLimitLean/GenLimit/Paper11_LearningAlgorithmsInTheLimit/Results/Overview.lean:251`. Original target type, quoted verbatim:

```lean
∀ {Candidate : Type u_1} {Config : Type u_2} [inst : DecidableEq.{u_1 + 1} Candidate]
  (candidates : Config → Finset.{u_1} Candidate) (score : Config → Candidate → Nat)
  (merge : Config → Candidate → Config) (remaining : Config → Nat) (intended : Config → Candidate → Prop)
  (Sound Complete : Config → Prop) (initial : Config),
  Sound initial →
    (∀ (config : Config),
        Sound config →
          Not (Complete config) →
            ∃ good,
              And (Membership.mem.{u_1, u_1} (candidates config) good)
                (And (intended config good) (LE.le.{0} 2 (score config good)))) →
      (∀ (config : Config),
          Sound config →
            Not (Complete config) →
              ∀ (bad : Candidate),
                Membership.mem.{u_1, u_1} (candidates config) bad →
                  Not (intended config bad) → LE.le.{0} (score config bad) 1) →
        (∀ (config : Config) (choice : Candidate),
            Sound config → intended config choice → Sound (merge config choice)) →
          (∀ (config : Config),
              Sound config →
                Complete config → GenLimit.LearningAlgorithmsLimit.IsMSMTerminal.{u_1, u_2} candidates score config) →
            (∀ (config : Config) (choice : Candidate),
                GenLimit.LearningAlgorithmsLimit.IsMSMChoice.{u_1, u_2} candidates score config choice →
                  LT.lt.{0} (remaining (merge config choice)) (remaining config)) →
              ∃ final,
                And
                  (Relation.ReflTransGen.{u_2}
                    (GenLimit.LearningAlgorithmsLimit.MSMStep.{u_1, u_2} candidates score merge) initial final)
                  (And (Sound final)
                    (And (Complete final)
                      (GenLimit.LearningAlgorithmsLimit.IsMSMTerminal.{u_1, u_2} candidates score final)))
```

**Reconstruction and exact hypotheses.** Fix arbitrary Candidate and Config types with decidable equality on Candidate; configuration-dependent finite candidates and natural scores; merge, natural remaining measure, intended relation, Sound and Complete predicates; and an initial configuration. Six assumptions are required: (1) Sound initial; (2) at every sound incomplete configuration, some candidate is intended and has score at least **2**; (3) at every sound incomplete configuration, every candidate that is not intended has score at most **1**; (4) every intended merge from any sound configuration preserves Sound, without requiring that the choice belongs to its candidate set; (5) every sound complete configuration is MSM-terminal; and (6) at every configuration and every MSM choice, remaining strictly decreases after merging, without a Sound restriction on this last premise.

**Conclusion and quantifier skeleton.** An MSM choice belongs to the candidate set, has strictly positive score, and maximizes score over that whole finite set. An MSMStep is a merge using some such choice. The conclusion is `∃ final:Config, ReflTransGen MSMStep initial final ∧ Sound final ∧ Complete final ∧ IsMSMTerminal candidates score final`. ReflTransGen means reachability by a finite sequence of zero or more steps. Terminal means no MSM choice exists. All functions and predicates precede all assumptions and the final existential; intermediate good candidates may depend on their configurations. No theorem from a named source is implicit in these premises.

**Limits and edge cases.** The score gap separates any maximum in a sound incomplete configuration from unintended candidates; tied maximum scores are allowed. The relation does not prescribe a tie-breaking order. The target concludes existence of a reachable sound complete terminal configuration, not uniqueness, a particular run, or a universally quantified policy outcome. An initially complete sound configuration can be its own final witness with zero steps. Empty candidate sets or all-zero scores are terminal; the good-candidate hypothesis prevents these at sound incomplete configurations. A zero remaining measure cannot admit an MSM choice under strict descent. No concrete merging system, sample relation, or executable procedure for the arbitrary predicates is supplied. There is no explicit numerical path-length, learning-time, or computational-cost bound in the displayed conclusion.

## Exhaustive coverage table

“Complete” here means that the statement, its supplied dependencies, witness order, information interface, and principal edge cases are reconstructed. It is not a proof or paper-correspondence verdict. Dossier numbering follows `targets.txt` and is exhaustive, including the diagnostic and both transition identities.

| # | Target suffix | Claim and retained scope | Coverage |
| ---: | --- | --- | --- |
| 1 | lemma_9_distinguishability | Two given characteristic sets; semantic disagreement; observation witness in their union; arbitrary sets | Complete |
| 2 | theorem_12_timeRestrictedIOO_core | Abstract bounded enumeration; exact optional labels; coverage and correct-index premise; stable correct Nat | Complete |
| 3 | theorem_12_minIndex_claim_not_justified | Four diagnostic conjuncts; two independent budget witnesses; exact budget-2 outcomes | Complete |
| 4 | corollary_13_parametrizedTMClass_core | Same kernel claim as #2; no additional Turing parametrization premise or conclusion | Complete |
| 5 | theorem_14_universalTBO_core | Source-coherent observation inputs; exact budgets; one whole-source fitting candidate; stable criterion | Complete |
| 6 | corollary_15_turingTBO | One learner per io across programs and sources; common-scale premise; pointwise computation conclusion | Complete |
| 7 | theorem_16_recursiveToRational_behavior | Policy behavior equals converted Mealy output list; no finite-state or recursive-computation premise | Complete |
| 8 | theorem_16_rationalEnumeration_core | Given machine family; List A inputs; whole List B labels; eventual correct Nat index | Complete |
| 9 | theorem_17_lateSplit_characteristic_obstruction | Conditional on two characteristic Sets; union contains an input ≥ splitAt | Complete |
| 10 | theorem_17_mass_lower_bound_core | Two finite cores; sum of n+1 weights separately; combined lower bound splitAt+1 | Complete |
| 11 | corollary_18_forgetting_preserves_indistinguishability | Equality preserved by one arbitrary forgetting function; Sort-polymorphic; forward only | Complete |
| 12 | corollary_18_characteristic_bound_lifts_to_richer_observations | Fixed lifted set learner; model-wise cores; same arbitrary mass and model bound | Complete |
| 13 | theorem_21_tagged_two_step | Exact matching two-symbol tag; final state and both actions; arbitrary starting state | Complete |
| 14 | taggedMachine_runFrom | Model/state-dependent tagged finite word; exact final state and complete encoded actions | Complete |
| 15 | theorem_21_transition_cover_core | Finite image cardinality; exercise coverage; one finite prefix containing all selected samples | Complete |
| 16 | theorem_21_msm_merge_order_core | All six assumptions; thresholds 2/1; positive maxima; finite reachable sound complete terminal witness | Complete |

## Boundary and unresolved-context statement

No decisive project type or definition body is missing from the supplied reconstruction boundary, so no additional mathematical-context request was needed. Exported dependency references close against the 144 declarations and declared external constants. Generated matchers, projections, constructors, recursors and encoding helpers were treated by their supplied definitions and standard Lean meanings; their names were not mined for extra mathematical claims. Truncated bulk displays were supplemented with focused declaration and explicit-type reads for every statement-relevant domain and operation.

All 16 original target strings above were mechanically compared against the original target markdown and the declaration export; all matched exactly. The explicit supplement was used to disambiguate domains and implicit instances, not to introduce assumptions. No theorem body was available or examined. No fresh elaboration, build, axiom audit, or claim about proof correctness has been substituted for this reconstruction. Every existence statement remains at its displayed dependency level; no unprovided algorithm, rate, distribution, source theorem, or stronger unconditional conclusion has been inferred from a label.
