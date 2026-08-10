# 01 — Paper01_LanguageGenerationInTheLimit — Language Generation in the Limit — Lean Faithfulness Audit

**Stage 2:** author-paper/Lean statement-faithfulness comparison  
**PAPER INDEX:** 01 of 36  
**PAPER CODE:** `Paper01_LanguageGenerationInTheLimit`  
**PAPER NAME:** *Language Generation in the Limit*  
**AUTHORS:** Jon Kleinberg and Sendhil Mullainathan  
**LEAN SNAPSHOT:** `fifalsp/generation-in-the-limit-lib`, branch `main`, commit `dfcd13534f9d51642a9f88904268e95454c88f7f`

---

## 1. Snapshot verification and evidence boundary

### 1.1 Author-source verification

Both newly supplied PDFs are readable, unencrypted, and text-extractable; each also rendered successfully page-by-page.

| File | Supplied bytes | Verified SHA-256 | Pages | Readability check |
|---|---:|---|---:|---|
| `01-kleinberg-mullainathan-neurips2024.pdf` | 318166 | `4b29159d3d11506fa8f92f38e4dfe234f209a730f786de7ef6c577f7e34b0745` | 22 | `pdfinfo`, text extraction, and raster rendering succeeded |
| `01-kleinberg-mullainathan-arxiv-v1.pdf` | 531856 | `db2648f7768c455015d22d1785e19747796ada40763322ec181bad780ab9a54f` | 24 | `pdfinfo`, text extraction, and raster rendering succeeded |

The hashes exactly match the values supplied in the request. No web source or substitute version was consulted.

The 18 Lean files from Stage 1 and the Stage-1 artifact `01-paper01-language-generation-in-the-limit-lean-statement-reconstruction.md` were also readable at their existing local paths and were left unchanged. The Stage-1 artifact was treated only as an index and fallible intermediary; all decisive formal comparisons below were rechecked against the attached Lean source declarations and statement-relevant definition bodies.

### 1.2 Evidence rule

For the papers, the evidence is the authors' definitions, numbered statements, assumptions, and theorem/proof text in the two supplied PDFs. Every paper citation below has the form **filename, statement number, printed page, section**. The proceedings and arXiv-v1 versions are kept separate whenever their statements or algorithms differ.

For Lean, the evidence is:

* public declaration signatures;
* right-hand sides of statement-relevant `def`, `abbrev`, and `structure` declarations, recursively unfolded as needed;
* explicit binder order, implicit arguments, typeclass assumptions, and `noncomputable` markers.

Lean comments, docstrings, theorem names as semantic evidence, theorem proof bodies, tactics, and repository CI were excluded. In particular, this audit does **not** assert that the source elaborates, compiles, proves its declarations, or is axiom-free.

### 1.3 Verdict vocabulary

Every comparison unit below receives exactly one correspondence verdict and exactly one difficulty verdict from the requested lists. “Source correction” and “repaired theorem” are additional descriptive labels, not alternative verdicts.

For local definitions and lemmas, `Exact / formally equivalent` means exact after fixing the formal development's ambient universe `ℕ` and applying the harmless zero-based reindexing. Results whose advertised scope itself quantifies over an arbitrary countable universe are still classified globally as `Faithful specialization`, because no transport theorem is supplied.

## 2. Executive findings

1. **The central unprompted countable-family theorem is represented faithfully at statement level.** The endpoint machine matches the NeurIPS proceedings stopping rule; the separate first-fresh-eligible machine matches arXiv v1. Both give a target-independent generator over `ℕ`, relative to an exact uniform membership oracle, with a presentation-dependent eventual threshold. The fixed universe `ℕ` is a genuine specialization of the papers' arbitrary explicitly enumerable countable universe.

2. **The formalized main theorem is not trivialized.** The generator does not receive the target index, a convergence time, correctness feedback, or a target-membership oracle. The hypotheses `Presents` and `OracleFamily` encode exactly an exact positive presentation, infinitude of every candidate, and a uniform candidate-membership oracle. The helper conditions used by the machines are internal finite consistency/criticality/termination facts; none assumes the final target-membership conclusion.

3. **The papers' finite-set function statement (4.1) and construction (4.5) do not literally fit together when repetitions are allowed.** Both PDFs state that `f_C` is a function of the finite set `S_t` alone, but then define it by scanning the first `t` candidate languages. The same finite set can occur at different times under repeated presentations. Lean contains two distinct responses:
   * a round-dependent semantic rule, which faithfully mirrors the `C_t` construction but has the stronger input interface `(stream,t)` and therefore is not a literal formalization of `f_C : Finset U → U`;
   * a finite-set-only cardinality-scope rule, which is a genuine repair and establishes the literal (4.1) conclusion even with repetitions.

4. **The formalization is materially incomplete as a formalization of either full paper.** Neither version's finite-family uniform theorem (2.2) is present. Prompted generation is absent entirely: the robust-prompt theorem (7.1) is missing from both-version coverage, and arXiv v1's stronger regular-subset-query theorem (7.5)/(7.6), context-free corollary, and finite-family prompted impossibility are also missing.

5. **No probability, rate, efficiency, or output-output distinctness is silently added.** The formal conclusions are eventual and deterministic, with no convergence rate or query bound. They require freshness only relative to the adversary's observed sample. This matches theorem (2.1), but it does not formalize the papers' informal “modify the algorithm to avoid repeated generated outputs” remark, nor theorem (2.2)'s infinite sequence of pairwise distinct outputs.

6. **The formal source contains useful statement-level repairs.** Most notably, the proceedings' printed (5.6) omits the condition that a consistent candidate exists and omits freshness, despite the surrounding algorithm and the proof of (5.7) needing those facts. The Lean round invariant includes the consistent-candidate hypothesis and freshness. The arXiv-v1 invariant is also strengthened to state least-fresh-output minimality.

## 3. Mathematical model in the two author versions

The common model is as follows. A countable indexed list `C={L_1,L_2,…}` consists of infinite subsets of a countable universe `U`; repetitions in the list are permitted. A black box answers `w∈L_i`. The adversary chooses a target `K=L_z` and presents a sequence whose set of values is exactly `K`, with repetitions allowed. `S_t` is the set of values shown through step `t`. A generator sees positive data only, receives no correctness feedback, and generates from `K` in the limit if, after some target-presentation-dependent time, every output lies in `K−S_t`. See `01-kleinberg-mullainathan-neurips2024.pdf`, pp. 3–4, §2, and `01-kleinberg-mullainathan-arxiv-v1.pdf`, pp. 4–6, §§2–3.

The two versions agree on this model and on the central theorems. They differ materially in the concrete finite-query stopping rule and in the prompted-generation results retained in the paper.

## 4. Complete inventory of author-paper results

### 4.1 NeurIPS 2024 proceedings version

#### Primary results

| ID | Author statement | Exact mathematical force | Citation |
|---|---|---|---|
| N1 | Countable-family generation in the limit | One membership-query algorithm works for every indexed countable family of infinite languages and every exact adversarial enumeration of any target in that family; after an enumeration-dependent threshold, every output is in `K−S_t`. | `01-kleinberg-mullainathan-neurips2024.pdf`, (2.1), p. 4, §2; realized as (5.7), p. 8, §5 |
| N2 | Uniform finite-family generation | One algorithm has the property that for every finite family `C` there is a bound `t(C)` such that, from any set/sequence of at least `t(C)` distinct target elements, it can output an infinite sequence of pairwise distinct elements of `K−S`. The bound depends on `C`, not on `K` or `S`. | `01-kleinberg-mullainathan-neurips2024.pdf`, (2.2), p. 4, §2; proof pp. 13–14, Appendix A.4 |
| N3 | Finite-set semantic function | For every countable family there is a function from finite subsets of `U` to `U` that is eventually fresh-and-correct along every exact target presentation. No effectiveness is required. | `01-kleinberg-mullainathan-neurips2024.pdf`, (4.1), p. 5, §4; correctness (4.6), p. 6 |
| N4 | Robust-prompt generation | For any countable family and any exact target presentation accompanied by prompts robust for every candidate language, a membership-query algorithm eventually outputs a fresh target string extending the current prompt. | `01-kleinberg-mullainathan-neurips2024.pdf`, (7.1), p. 10, §7; supporting (A.1)–(A.2), pp. 14–15, Appendix A.5 |

#### Numbered internal results supporting N1 and N3

| Statement | Content | Citation |
|---|---|---|
| (4.2) | Criticality: `L_n` is sample-consistent and is contained in every sample-consistent `L_i` with `i≤n`. | `01-kleinberg-mullainathan-neurips2024.pdf`, p. 6, §4 |
| (4.3) | The chosen target copy `L_z` is eventually critical forever. | `01-kleinberg-mullainathan-neurips2024.pdf`, p. 6, §4 |
| (4.4) | Later critical indices form a descending inclusion chain: if `i<j` are critical, then `L_j⊆L_i`. | `01-kleinberg-mullainathan-neurips2024.pdf`, p. 6, §4 |
| (4.5) | Round-dependent construction: among critical languages in `C_t`, choose the highest index and then the least unseen element. | `01-kleinberg-mullainathan-neurips2024.pdf`, p. 6, §4 |
| (4.6) | Eventual correctness of that semantic construction. | `01-kleinberg-mullainathan-neurips2024.pdf`, p. 6, §4 |
| (5.1) | `(t,m)`-criticality uses consistency plus inclusion only on the finite universe prefix. | `01-kleinberg-mullainathan-neurips2024.pdf`, p. 7, §5 |
| (5.2) | The target is eventually `(t,m)`-critical uniformly for all `m≥1`. | `01-kleinberg-mullainathan-neurips2024.pdf`, p. 7, §5 |
| (5.3) | If `i<j` are both `(t,m)`-critical, then `L_j[m]⊆L_i[m]`. | `01-kleinberg-mullainathan-neurips2024.pdf`, p. 7, §5 |
| (5.4) | Criticality is monotone toward smaller cutoffs. | `01-kleinberg-mullainathan-neurips2024.pdf`, p. 7, §5 |
| (5.5) | Each round's endpoint search terminates after finitely many operations. | `01-kleinberg-mullainathan-neurips2024.pdf`, p. 8, §5 |
| (5.6) | Printed statement: the round output belongs to the prefix of a maximal `(t,m_t)`-critical language. As printed, it omits an explicit consistent-candidate hypothesis and omits freshness. | `01-kleinberg-mullainathan-neurips2024.pdf`, p. 8, §5 |
| (5.7) | Eventual fresh target-membership of the algorithm's outputs. | `01-kleinberg-mullainathan-neurips2024.pdf`, p. 8, §5 |
| (A.1) | Prompted-round termination/invariant under a consistent candidate and a robust prompt. | `01-kleinberg-mullainathan-neurips2024.pdf`, p. 14, Appendix A.5 |
| (A.2) | Eventual prompted correctness. | `01-kleinberg-mullainathan-neurips2024.pdf`, pp. 14–15, Appendix A.5 |

#### Additional mathematical claims and examples

* A self-contained impossibility construction for identification in the limit on a countable family of one-way and bidirectional arithmetic progressions appears in `01-kleinberg-mullainathan-neurips2024.pdf`, pp. 12–13, Appendix A.1. It is background rather than a new generation theorem.
* The finite-family proof uses closure: after `t(C)` distinct samples, the intersection of all consistent languages is infinite and can be enumerated through membership queries; `01-kleinberg-mullainathan-neurips2024.pdf`, pp. 8–9, §6 and pp. 13–14, Appendix A.4.
* An infinite-family example has closure equal to the observed set at every finite stage, yet still admits generation in the limit; `01-kleinberg-mullainathan-neurips2024.pdf`, p. 15, Appendix A.6.
* The authors state informally that the semantic and finite-query generators can be modified so generated outputs do not repeat; `01-kleinberg-mullainathan-neurips2024.pdf`, pp. 6 and 8, §§4–5. This strengthening is not given a numbered theorem.

### 4.2 arXiv version 1

#### Primary results

| ID | Author statement | Exact mathematical force | Citation |
|---|---|---|---|
| A1 | Countable-family generation in the limit | Same high-level theorem as N1, but the Section 5 algorithm stops at the first cutoff whose selected prefix contains any fresh element and returns the least such element. | `01-kleinberg-mullainathan-arxiv-v1.pdf`, (2.1), p. 4, §2; (5.7), p. 16, §5 |
| A2 | Uniform finite-family generation | Same theorem as N2. | `01-kleinberg-mullainathan-arxiv-v1.pdf`, (2.2), p. 5, §2; proof p. 17, §6 |
| A3 | Finite-set semantic function | Same literal finite-set theorem as N3. | `01-kleinberg-mullainathan-arxiv-v1.pdf`, (4.1), p. 9, §4; (4.6), p. 11 |
| A4 | Robust-prompt generation | Same robust-prompt theorem as N4. | `01-kleinberg-mullainathan-arxiv-v1.pdf`, (7.1), p. 18, §7; (7.2)–(7.3), p. 20, §7.1 |
| A5 | Non-trivial prompts with regular subset queries | With membership queries plus queries of the form `L_i⊆R` for regular `R`, an algorithm eventually handles every prompt that currently has at least one continuation in `K−S_t`. | `01-kleinberg-mullainathan-arxiv-v1.pdf`, assumptions/result (7.4)–(7.5), p. 21, §7.2; correctness (7.6), p. 22 |
| A6 | Context-free corollary | For the family of context-free languages, A5 needs no added oracle because inclusion in a regular language is decidable through standard closure/emptiness facts. | `01-kleinberg-mullainathan-arxiv-v1.pdf`, pp. 20–21, §7.2, prose surrounding footnotes 4–5 |
| A7 | No finite uniform bound for prompted generation | Even for a two-language finite family, no fixed `t(C)` guarantees correct prompted generation after that many distinct samples. | `01-kleinberg-mullainathan-arxiv-v1.pdf`, pp. 22–23, §7.3 |

The internal statements (4.2)–(4.6), (5.1)–(5.7), and (7.2)–(7.3) have the same mathematical roles as in the proceedings version, except for the changed Section 5 stopping/output rule. The additional statements (7.4)–(7.6) occur only in arXiv v1.

### 4.3 Version differences that matter to the audit

| Topic | NeurIPS proceedings | arXiv v1 | Lean consequence |
|---|---|---|---|
| Section 5 stopping rule | At each increased cutoff, test only the newly reached endpoint and output that endpoint when it belongs to the selected language. | At each cutoff, inspect the whole selected prefix, stop when any fresh element exists, and return the least such element. | The source has two separate machines with exactly these two semantic rules. |
| Statement (5.6) | Omits an explicit consistent-candidate condition and does not state freshness. | Includes the consistent-candidate condition; still states only prefix membership, while the algorithm text supplies freshness and leastness. | The endpoint invariant is a repaired/incomparable strengthening of the printed proceedings statement; the arXiv invariant is a faithful strengthening. |
| Prompted extensions | Robust prompts only; stronger results are deferred to the full version. | Robust prompts, non-trivial prompts with regular subset queries, context-free corollary, and finite-family impossibility. | No prompted result is formalized. |
| Identification and closure example | Moved to appendices. | Included in main Sections 3.1–3.2. | Neither is formalized. |
| Finite-set function versus time | (4.1) says `f_C` takes only a finite set, while (4.5) scans `C_t`; repetitions are allowed. | Same mismatch. | Lean has both a round-dependent mirror and a separate finite-set-only repair. |
| Preliminary “minimal language” prose | Defines the discarded preliminary notion as a consistent language contained in every consistent language (a least element). | Defines it as inclusion-minimal: there is no distinct consistent sublanguage contained in it. | Lean does not define this preliminary notion; it formalizes only numbered criticality (4.2), which agrees across versions. |
| Inclusion prose before (4.2) | The sentence explaining why a smaller consistent language is safer reverses the element implication; the numbered definition and subsequent chain use the correct inclusion direction. | The corresponding prose has the correct direction. | Lean uses the correct direction. This is a prose correction, not a theorem mismatch. |

## 5. Complete inventory of substantive Lean target-scope results

The target-specific source contains four mathematical layers. The six `Core` files are shared infrastructure rather than Paper01-specific result modules. Their primitive declarations needed to interpret the target results (`Language`, `LanguageFamily`, `Presents`, `sample`, `Consistent`, and `OracleFamily`) are audited in §§6 and 11. Other generic-countable, partial-presentation, target-stability, and umbrella declarations are not counted as Paper01 target-scope results; they are recorded as shared/extra infrastructure in §13 rather than silently attributed to the paper.

1. **Whole-language criticality:** `GenLimit.Critical` and the eventual-critical/nesting declarations.
2. **Semantic generators:** a round-indexed noncomputable generator and a finite-observed-set noncomputable generator.
3. **Shared finite-query infrastructure:** finite-prefix criticality, exact Boolean realizations of consistency and criticality, maximal candidate selection, and stabilization.
4. **Two stateful finite-query machines:** an endpoint machine and a first-fresh-eligible machine, each with a terminal eventual-correctness theorem.

The seven terminal declarations from Stage 1 are:

```lean
variable (O : OracleFamily)
theorem GenLimit.OracleFamily.eventual_correctness
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    O.GeneratesInLimit stream z

theorem GenLimit.OracleFamily.kleinbergMullainathan_main
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    O.GeneratesInLimit stream z

variable (O : OracleFamily)
theorem GenLimit.OracleFamily.ArxivV1.eventual_correctness
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    GenLimit.OracleFamily.ArxivV1.GeneratesInLimit O stream z

theorem GenLimit.OracleFamily.ArxivV1.kleinbergMullainathan_main
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    GenLimit.OracleFamily.ArxivV1.GeneratesInLimit O stream z

theorem GenLimit.KM.Semantic.kleinbergMullainathan_main
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    GenLimit.KM.Semantic.GeneratesInLimit O stream z

theorem GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z))
    (hinjective : Function.Injective stream) :
    GenLimit.KM.SetInterface.GeneratesFromObservedSet O stream z

theorem GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface_with_repetitions
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    GenLimit.KM.SetInterface.GeneratesFromObservedSet O stream z
```

The two `eventual_correctness`/`kleinbergMullainathan_main` pairs are propositionally duplicate at the signature level. They are counted separately because they are separate public declarations, but they do not add distinct mathematical claims.

Section 14 classifies all 69 target-specific theorem declarations, including auxiliary bridge and invariant statements, and assigns every substantive one a paper correspondence and difficulty verdict. Section 16 records their exact whitespace-normalized signatures. Decidability instances are listed separately because they assert availability of decision procedures but are not independent paper theorems.

## 6. Primitive formal model and access audit

### 6.1 Exact signatures

```lean
abbrev GenLimit.Language := Set ℕ

abbrev GenLimit.LanguageFamily := ℕ → GenLimit.Language

def GenLimit.Presents (stream : ℕ → ℕ) (L : GenLimit.Language) : Prop :=
  Set.range stream = L

def GenLimit.sample (stream : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range t).image stream

def GenLimit.Consistent
    (C : GenLimit.LanguageFamily) (stream : ℕ → ℕ) (t i : ℕ) : Prop :=
  ↑(GenLimit.sample stream t) ⊆ C i

structure GenLimit.OracleFamily where
  language : GenLimit.LanguageFamily
  infinite' : ∀ i, (language i).Infinite
  query : ℕ → ℕ → Bool
  query_spec : ∀ i u, query i u = true ↔ u ∈ language i
```

### 6.2 Literal interpretation

Let `C_i=O.language i`, `x_t=stream t`, and

`S_t={x_s : s<t}`.

Then `Presents stream (C_z)` is exactly `range(stream)=C_z`: every observation is positive, every target element eventually occurs, and repetitions/order are unrestricted. `Consistent C stream t i` is exactly `S_t⊆C_i`.

The generator is fixed after `O` is fixed and before `z` is quantified. The target index appears only in the correctness proposition. The threshold occurs after `O,stream,z,hP`, so it may depend on all of them. It is not supplied to the generator.

### 6.3 Access comparison

| Access feature | Papers | Lean | Audit |
|---|---|---|---|
| Candidate membership | Uniform black box `w∈L_i` | `query i u : Bool` with exact `query_spec` | Preserved |
| Target membership | Not available because `z` is hidden | `kmGenerator` has no `z` argument | Preserved |
| Positive examples | Current/past enumerated values | Concrete definitions inspect `sample stream t` and recursive states built from earlier values | Preserved by recursive definition, although the type accepts the whole stream function |
| Correctness feedback | None | No feedback parameter | Preserved |
| Whole-language inclusion | Used only in the noncomputable semantic construction | `Critical`/`CriticalOn` use actual subset relations | Preserved for the semantic theorem, not used by finite-query output definitions |
| Infinitude | Every candidate language is infinite | `infinite' : ∀i, Infinite(C_i)` | Preserved |
| Time/query complexity | Only finite termination, no efficiency bound | Unbounded least-search definitions plus existence/specification theorems; no numerical query bound | Preserved at the theorem's stated granularity; no efficiency certification |

Extensionally, the concrete finite tests reduce to `query`, finite ranges/filters/maxima, natural arithmetic, and a least successful cutoff. No finite test asks a whole-language subset question. There is, however, an important source-only limitation: each `roundCounter` is defined with `Nat.find` applied to the separately stated existence theorem (`stop_exists` or `hasFreshEligible_exists`). The resulting cutoff is specified as the least cutoff satisfying the decidable membership-based predicate, but the attached source does not include the imported operational definition of `Nat.find`, and the proof term supplying existence is excluded by instruction. Therefore this audit can certify the extensional membership-query rule, but not a compiled/extracted execution path that erases all proof witnesses.

No source signature formalizes a Turing machine, a complexity class, or a `Computable` predicate. Thus the paper's broad “algorithm using standard computation plus membership queries” is represented at statement/definition level by oracle-relative functions and finite decidable tests, while actual compilation/extraction remains indeterminate and outside the evidence boundary.

## 7. Recursive expansion of every main Lean rule

### 7.1 Shared semantic criticality

```lean
def GenLimit.Critical
    (C : LanguageFamily) (stream : ℕ → ℕ) (t n : ℕ) : Prop :=
  Consistent C stream t n ∧
    ∀ i, i ≤ n → Consistent C stream t i → C n ⊆ C i
```

Fully expanded:

`Critical(C,x,t,n)` iff

1. for every `u`, if `u=x_s` for some `s<t`, then `u∈C_n`; and
2. for every `i≤n`, if every observed `u=x_s` with `s<t` lies in `C_i`, then every element of `C_n` lies in `C_i`.

This is a genuine compatibility/minimality condition. It does not mention the generator's output or the target index. Its inclusion clause may be vacuous when `n` is the least consistent index, but consistency itself is required. It is not circular.

The two key separately stated declarations are:

```lean
theorem GenLimit.critical_subset_of_le
    {C : LanguageFamily} {stream : ℕ → ℕ} {t i j : ℕ}
    (hij : i ≤ j) (hi : Critical C stream t i)
    (hj : Critical C stream t j) : C j ⊆ C i

theorem GenLimit.target_eventually_critical
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    ∃ T, ∀ t, T ≤ t → Critical C stream t z
```

Their signatures express the paper's chain and eventual-target facts; this audit does not use their proof bodies to claim they are established.

### 7.2 Round-indexed semantic rule

```lean
noncomputable def GenLimit.KM.Semantic.criticalIndices
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range t).filter (Critical C stream t)

noncomputable def GenLimit.KM.Semantic.focus
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  if h : (criticalIndices C stream t).Nonempty
  then (criticalIndices C stream t).max' h
  else 0

noncomputable def GenLimit.KM.Semantic.fresh
    (O : OracleFamily) (stream : ℕ → ℕ) (t i : ℕ) : ℕ :=
  Nat.find ((O.infinite' i).exists_notMem_finset (sample stream t))

noncomputable def GenLimit.KM.Semantic.generator
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  fresh O stream t (focus O.language stream t)
```

Thus, at time `t`, the rule scans indices `<t`, takes the greatest whole-language-critical index (or `0` if none), and takes the least natural in that language outside `S_t`.

The final predicate is

```lean
def GenLimit.KM.Semantic.GeneratesInLimit
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    generator O stream t ∈ O.language z ∧
    generator O stream t ∉ sample stream t
```

**Compatibility/difficulty finding.** `fresh` directly contains only the easy subgoal “fresh element of the selected infinite language,” which is justified by the paper's infinitude assumption. It does not contain target correctness. The nontrivial part remains showing that the selected critical language is eventually contained in the target. However, the rule receives `t` separately, so it has information not recoverable from the set `S_t` when observations repeat. This is not merely a type-theoretic possibility: take `C_0=ℕ`, let `C_1` be the even naturals, and let the observed set remain `{0}` for two rounds. At scope `t=1`, the focus is `0` and the least fresh output is `1`; at scope `t=2`, index `1` is also critical, becomes the greatest focus, and the least fresh output is `2`. Thus the same observed finset can produce different outputs. Relative to literal (4.1), this changes and weakens the interface.

### 7.3 Finite-observed-set semantic repair

```lean
def GenLimit.KM.SetInterface.ConsistentOn
    (C : LanguageFamily) (S : Finset ℕ) (n : ℕ) : Prop :=
  (↑S : Set ℕ) ⊆ C n

def GenLimit.KM.SetInterface.CriticalOn
    (C : LanguageFamily) (S : Finset ℕ) (n : ℕ) : Prop :=
  ConsistentOn C S n ∧
    ∀ i, i ≤ n → ConsistentOn C S i → C n ⊆ C i

noncomputable def GenLimit.KM.SetInterface.criticalIndices
    (C : LanguageFamily) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range S.card).filter (CriticalOn C S)

noncomputable def GenLimit.KM.SetInterface.focus
    (C : LanguageFamily) (S : Finset ℕ) : ℕ :=
  if h : (criticalIndices C S).Nonempty
  then (criticalIndices C S).max' h
  else 0

noncomputable def GenLimit.KM.SetInterface.fresh
    (O : OracleFamily) (S : Finset ℕ) (i : ℕ) : ℕ :=
  Nat.find ((O.infinite' i).exists_notMem_finset S)

noncomputable def GenLimit.KM.SetInterface.generator
    (O : OracleFamily) (S : Finset ℕ) : ℕ :=
  fresh O S (focus O.language S)
```

The literal finite-set conclusion is:

```lean
def GenLimit.KM.SetInterface.GeneratesFromObservedSet
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    generator O (sample stream t) ∈ O.language z ∧
      generator O (sample stream t) ∉ sample stream t
```

Here the output function itself is fixed from `O` and a `Finset ℕ`; neither the raw round, the stream, the target index, nor the eventual threshold is an argument of `generator`.

The candidate scope is `S.card`, not elapsed time. The output therefore depends literally only on `O` and `S`. Along an exact presentation of an infinite target, `|S_t|` is nondecreasing and unbounded, so every fixed target index eventually enters the scope. The separate signature asserting the needed scope fact is:

```lean
theorem GenLimit.KM.SetInterface.eventually_target_below_sample_card
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    ∃ T, ∀ t, T ≤ t → z < (sample stream t).card
```

This helper does not contain target correctness. It is a genuine cardinality fact. The final repetition-tolerant theorem is a repaired realization of the literal finite-set interface.

### 7.4 Shared finite-prefix predicates

```lean
def GenLimit.FinitelyCritical
    (C : LanguageFamily) (stream : ℕ → ℕ) (t m n : ℕ) : Prop :=
  Consistent C stream t n ∧
    ∀ i, i ≤ n → Consistent C stream t i →
      ∀ u, u < m → u ∈ C n → u ∈ C i
```

Fully expanded, this is whole-sample consistency of `n` plus containment of `C_n∩[0,m)` in every earlier-or-equal consistent candidate's cutoff prefix.

```lean
def GenLimit.OracleFamily.finitePrefix (O : OracleFamily) (i m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun u => O.query i u = true)

def GenLimit.OracleFamily.inconsistentSamples
    (O : OracleFamily) (stream : ℕ → ℕ) (t i : ℕ) : Finset ℕ :=
  (sample stream t).filter (fun u => O.query i u = false)

def GenLimit.OracleFamily.ConsistentAt
    (O : OracleFamily) (stream : ℕ → ℕ) (t i : ℕ) : Prop :=
  O.inconsistentSamples stream t i = ∅

def GenLimit.OracleFamily.criticalFailures
    (O : OracleFamily) (stream : ℕ → ℕ) (t m n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun i =>
    O.ConsistentAt stream t i ∧
      ¬ O.finitePrefix n m ⊆ O.finitePrefix i m)

def GenLimit.OracleFamily.FinitelyCriticalAt
    (O : OracleFamily) (stream : ℕ → ℕ) (t m n : ℕ) : Prop :=
  O.ConsistentAt stream t n ∧ O.criticalFailures stream t m n = ∅
```

The bridge signatures are genuine equivalences:

```lean
theorem GenLimit.OracleFamily.mem_finitePrefix
    {i m u : ℕ} :
    u ∈ O.finitePrefix i m ↔ u < m ∧ u ∈ O.language i

theorem GenLimit.OracleFamily.consistentAt_iff
    {stream : ℕ → ℕ} {t i : ℕ} :
    O.ConsistentAt stream t i ↔
      Consistent O.language stream t i

theorem GenLimit.OracleFamily.finitelyCriticalAt_iff
    {stream : ℕ → ℕ} {t m n : ℕ} :
    O.FinitelyCriticalAt stream t m n ↔
      FinitelyCritical O.language stream t m n
```

These conditions do not assume a target or output. They assert that the finite Boolean tests have the intended semantic meaning. No subset oracle is present.

At `m=0`, the prefix-containment clause is vacuous, but consistency remains. The papers quantify `m≥1`; extending the definitions/theorems to `m=0` does not drive the eventual correctness result because successful machine cutoffs are positive and grow above observed values.

### 7.5 Candidate selection

```lean
def GenLimit.OracleFamily.consistentCandidates
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun i => O.ConsistentAt stream t i)

def GenLimit.OracleFamily.HasConsistent
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) : Prop :=
  (O.consistentCandidates stream t).Nonempty

def GenLimit.OracleFamily.criticalCandidates
    (O : OracleFamily) (stream : ℕ → ℕ) (t m : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun n => O.FinitelyCriticalAt stream t m n)

def GenLimit.OracleFamily.selected
    (O : OracleFamily) (stream : ℕ → ℕ) (t m : ℕ)
    (h : O.HasConsistent stream t) : ℕ :=
  (O.criticalCandidates stream t m).max'
    (O.criticalCandidates_nonempty h m)
```

`HasConsistent` merely says that some index `<t` contains all current observations. It can fail early, and then the machines output an arbitrary default. Once `z<t`, an exact presentation makes the target itself a witness. This hypothesis therefore does not encode the final conclusion.

The stabilization condition needed for both searches is separately stated as:

```lean
theorem GenLimit.OracleFamily.selected_eventually_constant
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) :
    ∃ M, ∀ m, M ≤ m →
      O.selected stream t m h = O.selected stream t M h
```

This is a genuine finite-index stabilization fact. It does not identify the target and does not assert output correctness.

### 7.6 Proceedings endpoint machine

```lean
def GenLimit.OracleFamily.Stop
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ)
    (h : O.HasConsistent stream t) (q : ℕ) : Prop :=
  O.query (O.selected stream t q h) (q - 1) = true

def GenLimit.OracleFamily.roundCounter
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ)
    (h : O.HasConsistent stream t) (b : ℕ) : ℕ :=
  Nat.find (O.stop_exists h b)

structure GenLimit.OracleFamily.MachineState where
  counter : ℕ
  output : ℕ

def GenLimit.OracleFamily.processRound
    (O : OracleFamily) (stream : ℕ → ℕ) (t b : ℕ) : MachineState :=
  if h : O.HasConsistent stream t then
    let q := O.roundCounter stream t h b
    ⟨q, q - 1⟩
  else
    ⟨b, 0⟩

def GenLimit.OracleFamily.run
    (O : OracleFamily) (stream : ℕ → ℕ) : ℕ → MachineState
  | 0 => ⟨0, 0⟩
  | t + 1 =>
      let previous := run O stream t
      let start := max previous.counter (stream t + 1)
      O.processRound stream (t + 1) start

def GenLimit.OracleFamily.kmGenerator
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  (O.run stream t).output
```

The corresponding terminal proposition is:

```lean
def GenLimit.OracleFamily.GeneratesInLimit
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    O.kmGenerator stream t ∈ O.language z ∧
      O.kmGenerator stream t ∉ sample stream t
```

After unfolding `kmGenerator`, this says exactly that there is a threshold `T` such that every later stored machine output belongs to the target candidate `O.language z` and is outside the observations strictly before that round.

At a successful round, `q` is the least cutoff above `b` satisfying the endpoint membership test; the output is `q−1`. The start is raised above every newly observed natural, so the endpoint is fresh. Under the natural reindexing `u_1↔0,u_2↔1,…`, this is the proceedings rule of testing the newly reached `u_m`.

The termination condition is not an external assumption. It is a separate theorem signature:

```lean
theorem GenLimit.OracleFamily.stop_exists
    {stream : ℕ → ℕ} {t : ℕ}
    (h : O.HasConsistent stream t) (b : ℕ) :
    ∃ q, b < q ∧ O.Stop stream t h q
```

The full successful-round invariant is:

```lean
theorem GenLimit.OracleFamily.run_round_spec
    {stream : ℕ → ℕ} {t : ℕ} (ht : 0 < t)
    (h : O.HasConsistent stream t) :
    ∃ n,
      n < t ∧
      FinitelyCritical O.language stream t (O.run stream t).counter n ∧
      (∀ j, j < t →
        FinitelyCritical O.language stream t (O.run stream t).counter j →
        j ≤ n) ∧
      (O.run stream t).output ∈
        O.finitePrefix n (O.run stream t).counter ∧
      (O.run stream t).output ∉ sample stream t
```

No target appears in this invariant. It is not a disguised correctness assumption.

### 7.7 arXiv-v1 first-fresh-eligible machine

```lean
def GenLimit.OracleFamily.ArxivV1.eligible
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ)
    (h : O.HasConsistent stream t) (q : ℕ) : Finset ℕ :=
  (O.finitePrefix (O.selected stream t q h) q).filter
    (fun u => u ∉ sample stream t)

def GenLimit.OracleFamily.ArxivV1.HasFreshEligible
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ)
    (h : O.HasConsistent stream t) (q : ℕ) : Prop :=
  (eligible O stream t h q).Nonempty

def GenLimit.OracleFamily.ArxivV1.roundCounter
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ)
    (h : O.HasConsistent stream t) (b : ℕ) : ℕ :=
  Nat.find (hasFreshEligible_exists O h b)

def GenLimit.OracleFamily.ArxivV1.roundOutput
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ)
    (h : O.HasConsistent stream t) (b : ℕ) : ℕ :=
  (eligible O stream t h (roundCounter O stream t h b)).min'
    (roundCounter_spec O h b).2
```

Its state recursion has the same start update as the proceedings machine, but stores this independently chosen least output:

```lean
def GenLimit.OracleFamily.ArxivV1.kmGenerator
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  (GenLimit.OracleFamily.ArxivV1.run O stream t).output

def GenLimit.OracleFamily.ArxivV1.GeneratesInLimit
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    GenLimit.OracleFamily.ArxivV1.kmGenerator O stream t ∈ O.language z ∧
      GenLimit.OracleFamily.ArxivV1.kmGenerator O stream t ∉ sample stream t
```

Thus the terminal conclusion has the same target/freshness quantifier structure as the proceedings predicate; only the concrete output rule differs.

Its state recursion is the same as the endpoint machine except that counter and output are stored separately and the output is the least fresh member of the selected prefix at the first successful cutoff.

The termination signature is:

```lean
theorem GenLimit.OracleFamily.ArxivV1.hasFreshEligible_exists
    {stream : ℕ → ℕ} {t : ℕ}
    (h : O.HasConsistent stream t) (b : ℕ) :
    ∃ q, b < q ∧
      GenLimit.OracleFamily.ArxivV1.HasFreshEligible O stream t h q
```

The round invariant explicitly includes prefix membership, freshness, maximal finite-criticality, and leastness among fresh elements of that prefix. None of these hypotheses supplies target correctness.

### 7.8 Definition/helper correspondence and difficulty matrix

This matrix gives the requested single verdict pair for every substantive public definition used in the Paper01 target modules. Closely coupled implementation definitions are grouped only when they form one paper algorithm clause; every public target-specific definition is named either here or in the exact inventory of §16.1.

| Lean definition(s) | Paper comparison unit | Correspondence verdict | Difficulty verdict | Finding |
|---|---|---|---|---|
| `GenLimit.Critical` | Both PDFs, (4.2): whole-language criticality | Exact / formally equivalent | Preserved | Same consistency and earlier-index inclusion condition, modulo zero-based indexing. |
| `GenLimit.FinitelyCritical` | Both PDFs, (5.1): finite-prefix criticality | Faithful generalization | Preserved | Same condition for positive cutoffs; Lean also permits cutoff zero. |
| `GenLimit.KM.Semantic.criticalIndices`; `GenLimit.KM.Semantic.focus` | Both PDFs, (4.5): greatest critical index among the first-round scope | Faithful specialization | Preserved | Exact round-indexed construction over `ℕ`; arbitrary fallback `0` when the set is empty. |
| `GenLimit.KM.Semantic.fresh`; `GenLimit.KM.Semantic.generator` | Both PDFs, (4.5): least unseen element of the selected language | Faithful specialization | Preserved | Infinitude supplies a fresh selected-language element; no target correctness is embedded. |
| `GenLimit.KM.Semantic.GeneratesInLimit` | Both PDFs, (4.6), for the round-indexed rule | Faithful specialization | Preserved | Exact eventual target-membership/freshness predicate for that rule; the theorem/interface mismatch with literal (4.1) is assessed separately. |
| `GenLimit.KM.SetInterface.ConsistentOn`; `GenLimit.KM.SetInterface.CriticalOn` | Finite-set rewriting of both PDFs' consistency and (4.2) | Exact / formally equivalent | Preserved | No elapsed-time input is present. |
| `GenLimit.KM.SetInterface.criticalIndices`; `GenLimit.KM.SetInterface.focus` | Cardinality-scope repair of the finite-set-only claim (4.1) | Extra Lean result not claimed by the paper | Indeterminate | The papers do not propose `card(S)` as the candidate scope. This is a new repair mechanism. |
| `GenLimit.KM.SetInterface.fresh`; `GenLimit.KM.SetInterface.generator` | Repaired finite-set construction realizing (4.1) | Faithful specialization | Preserved | The resulting function is genuinely of the observed finset alone; the chosen repair is extra, but the advertised task is unchanged. |
| `GenLimit.KM.SetInterface.GeneratesFromObservedSet` | Both PDFs, literal conclusion of (4.1) | Faithful specialization | Preserved | Same quantifier pattern over `ℕ`, with arbitrary repeated presentations allowed by the repetition-tolerant theorem. |
| `GenLimit.OracleFamily.finitePrefix`; `GenLimit.OracleFamily.inconsistentSamples`; `GenLimit.OracleFamily.ConsistentAt` | Both PDFs, `L_i[m]` and finite membership-query consistency tests in §5 | Exact / formally equivalent | Preserved | Exact Boolean-oracle realizations of finite prefixes and sample consistency. |
| `GenLimit.OracleFamily.criticalFailures`; `GenLimit.OracleFamily.FinitelyCriticalAt` | Both PDFs, finite membership-query test for (5.1) | Exact / formally equivalent | Preserved | Failure witnesses are precisely earlier consistent indices violating finite-prefix containment. |
| `GenLimit.OracleFamily.consistentCandidates`; `GenLimit.OracleFamily.HasConsistent`; `GenLimit.OracleFamily.criticalCandidates`; `GenLimit.OracleFamily.selected` | Both PDFs, candidate scope and `n_t(m)` in §5 | Exact / formally equivalent | Preserved | `selected` is the greatest in-scope finite-critical index; no target index is an input. |
| `GenLimit.OracleFamily.Stop`; `GenLimit.OracleFamily.roundCounter` | Proceedings §5 endpoint stopping rule and (5.5) | Faithful specialization | Preserved | Strict natural prefix and `q-1` encode the one-based endpoint rule over `ℕ`. |
| `GenLimit.OracleFamily.MachineState`; `GenLimit.OracleFamily.processRound`; `GenLimit.OracleFamily.run`; `GenLimit.OracleFamily.kmGenerator` | Proceedings §5 state update and per-round output | Faithful specialization | Preserved | The recursive state processes exactly the observations with index below the output round; early failure uses the paper's arbitrary-output branch. |
| `GenLimit.OracleFamily.GeneratesInLimit` | Proceedings (2.1)/(5.7) correctness predicate | Faithful specialization | Preserved | Eventual target membership and freshness, with no rate or target argument to the generator. |
| `GenLimit.OracleFamily.ArxivV1.eligible`; `GenLimit.OracleFamily.ArxivV1.HasFreshEligible`; `GenLimit.OracleFamily.ArxivV1.roundCounter`; `GenLimit.OracleFamily.ArxivV1.roundOutput` | arXiv-v1 §5 first-fresh-eligible stopping/output rule | Faithful specialization | Preserved | The first successful cutoff and least fresh selected-prefix member are represented explicitly. |
| `GenLimit.OracleFamily.ArxivV1.MachineState`; `GenLimit.OracleFamily.ArxivV1.processRound`; `GenLimit.OracleFamily.ArxivV1.run`; `GenLimit.OracleFamily.ArxivV1.kmGenerator` | arXiv-v1 §5 state update | Faithful specialization | Preserved | Same recursive access boundary as the paper; output and cutoff are stored separately. |
| `GenLimit.OracleFamily.ArxivV1.GeneratesInLimit` | arXiv-v1 (2.1)/(5.7) correctness predicate | Faithful specialization | Preserved | Same eventual target-membership/freshness predicate over the fixed universe `ℕ`. |

## 8. Bidirectional correspondence: paper results to Lean

### 8.1 Proceedings version

| Paper comparison unit | Lean counterpart(s) | Correspondence verdict | Difficulty verdict | Audit finding |
|---|---|---|---|---|
| N1: (2.1)/(5.7), unprompted countable-family algorithm | `GenLimit.OracleFamily.eventual_correctness`; `GenLimit.OracleFamily.kleinbergMullainathan_main` | Faithful specialization | Preserved | Exact positive presentation, infinitude, repetitions, hidden target, membership-only finite tests, and eventual freshness are preserved. Specializations: universe `ℕ`, zero-based indexing, no transport theorem. |
| N2: (2.2), finite-family uniform bound and infinite distinct output sequence | none | Not represented in Lean | Indeterminate | No finite-family/closure object, no `t(C)`, and no theorem producing an infinite pairwise-distinct sequence from a fixed sample. |
| N3: literal (4.1), finite-set-only function, repetitions allowed | `GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface_with_repetitions` | Faithful specialization | Preserved | The formal generator is literally a function of the observed finset; cardinality replaces elapsed-time scope. This is a repaired construction proving the same claim over `ℕ`. |
| N3 restricted to injective presentations | `GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface` | Faithful specialization | Weakened / easier | Adds global injectivity, so `card(S_t)=t`; the paper permits repetitions. A stronger repetition-tolerant formal theorem also exists. |
| Printed (4.5)/(4.6) round-dependent construction treated as if it were `f_C(S_t)` | `GenLimit.KM.Semantic.kleinbergMullainathan_main` | Related but materially different | Weakened / easier | The Lean rule receives `t` and scans indices `<t`; same finite set at two repeated rounds can lead to different outputs. It mirrors the construction but not the finite-set-only interface. |
| (4.2) criticality | `GenLimit.Critical` | Exact / formally equivalent | Preserved | Zero-based reindexing only. |
| (4.3) target eventually critical | `GenLimit.target_eventually_critical` | Faithful specialization | Preserved | Same quantifier order and presentation-dependent threshold; formal universe fixed to `ℕ`. |
| (4.4) critical chain for `i<j` | `GenLimit.critical_subset_of_le` | Faithful generalization | Preserved | Lean permits `i=j`, adding only the trivial reflexive case. |
| (5.1) finite criticality | `GenLimit.FinitelyCritical` | Faithful generalization | Preserved | Same content on `m≥1`; Lean also defines the harmless `m=0` case. |
| (5.2) eventual finite criticality uniformly in `m` | `GenLimit.target_eventually_finitelyCritical` | Faithful generalization | Preserved | Lean quantifies all natural cutoffs, including zero. |
| (5.3) finite-prefix nesting | `GenLimit.finitelyCritical_prefix_subset` | Faithful generalization | Preserved | Uses `i≤j` rather than `i<j`; equality is trivial. |
| (5.4) cutoff monotonicity | `GenLimit.finitelyCritical_cutoff_mono` | Faithful generalization | Preserved | Uses non-strict cutoff comparison. |
| (5.5) endpoint-round termination | `GenLimit.OracleFamily.stop_exists` plus `roundCounter_spec` | Faithful specialization | Preserved | The existential cutoff depends on current family/oracle, finite history, round, consistency witness, and start; it does not depend on target `z`. |
| Printed proceedings (5.6) | `GenLimit.OracleFamily.run_round_spec` | Related but materially different | Indeterminate | Repaired statement: Lean adds the needed `HasConsistent` and `t>0` hypotheses, but also strengthens the conclusion with freshness and explicit maximality. Added hypotheses and stronger conclusion make direct difficulty ordering incomparable. |
| N4: (7.1)/(A.2), robust prompted generation | none | Not represented in Lean | Indeterminate | No string alphabet, concatenation, prefix relation, prompt sequence, robustness predicate, or prompted generator. |
| Identification impossibility construction | none | Not represented in Lean | Indeterminate | No identifier/learner outputting candidate indices and no arithmetic-progression counterexample. |
| Closure counterexample and finite-family closure proof | none | Not represented in Lean | Indeterminate | No closure definition or intersection-enumeration theorem. |
| Informal no-repeat modification | none | Not represented in Lean | Indeterminate | Formal freshness is only relative to `S_t`, not earlier generated outputs. |

### 8.2 arXiv v1

| Paper comparison unit | Lean counterpart(s) | Correspondence verdict | Difficulty verdict | Audit finding |
|---|---|---|---|---|
| A1: (2.1)/(5.7), first-fresh-eligible algorithm | `GenLimit.OracleFamily.ArxivV1.eventual_correctness`; `GenLimit.OracleFamily.ArxivV1.kleinbergMullainathan_main` | Faithful specialization | Preserved | The stopping cutoff and least fresh prefix output match arXiv v1, including arbitrary repetitions. Universe is specialized to `ℕ`. |
| A2: (2.2), finite-family theorem | none | Not represented in Lean | Indeterminate | Same omission as N2. |
| A3: (4.1), finite-set function | `GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface_with_repetitions` | Faithful specialization | Preserved | Same repaired cardinality-scope realization. |
| A3's printed `C_t` construction | `GenLimit.KM.Semantic.kleinbergMullainathan_main` | Related but materially different | Weakened / easier | Same elapsed-time/interface mismatch as in the proceedings version. |
| arXiv (5.5) termination | `GenLimit.OracleFamily.ArxivV1.hasFreshEligible_exists` | Faithful specialization | Preserved | Exactly the existence condition needed by first-fresh-eligible search. |
| arXiv (5.6) successful-round invariant | `GenLimit.OracleFamily.ArxivV1.run_round_spec` | Faithful generalization | Strengthened / harder | Paper states selected-prefix membership under a consistent candidate; Lean additionally states freshness, maximality, and leastness among fresh prefix members. |
| A4: (7.1)/(7.3), robust prompts | none | Not represented in Lean | Indeterminate | No prompting formalism. |
| A5: (7.4)–(7.6), non-trivial prompts with regular subset queries | none | Not represented in Lean | Indeterminate | No regular-language type, subset-query oracle, `t`-validity, or prompt continuation. |
| A6: context-free corollary | none | Not represented in Lean | Indeterminate | No context-free/regular language representation or decidability theorem. |
| A7: no finite uniform bound for prompted generation | none | Not represented in Lean | Indeterminate | No two-language parity/prefix counterexample or negative theorem. |
| Identification impossibility, closure example, no-repeat remark | none | Not represented in Lean | Indeterminate | Same omissions as for the proceedings version. |

## 9. Lean-to-paper correspondence for every terminal formal theorem

| Lean declaration | Paper counterpart | Correspondence verdict | Difficulty verdict | Classification |
|---|---|---|---|---|
| `GenLimit.OracleFamily.eventual_correctness` | NeurIPS (2.1)/(5.7) | Faithful specialization | Preserved | Faithful translation of the proceedings algorithm over `ℕ` |
| `GenLimit.OracleFamily.kleinbergMullainathan_main` | NeurIPS (2.1)/(5.7) | Faithful specialization | Preserved | Signature-duplicate terminal theorem |
| `GenLimit.OracleFamily.ArxivV1.eventual_correctness` | arXiv-v1 (2.1)/(5.7) | Faithful specialization | Preserved | Faithful version-specific translation over `ℕ` |
| `GenLimit.OracleFamily.ArxivV1.kleinbergMullainathan_main` | arXiv-v1 (2.1)/(5.7) | Faithful specialization | Preserved | Signature-duplicate terminal theorem |
| `GenLimit.KM.Semantic.kleinbergMullainathan_main` | Printed construction (4.5)/(4.6), but not literal finite-set interface (4.1) | Related but materially different | Weakened / easier | Valid round-dependent theorem; not by itself the advertised finite-set theorem |
| `GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface` | (4.1) under an added repetition-free hypothesis | Faithful specialization | Weakened / easier | Valid stronger-assumption specialization |
| `GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface_with_repetitions` | Literal (4.1)/(4.6) | Faithful specialization | Preserved | Source correction/repaired construction; same claimed theorem over `ℕ` |

No terminal theorem is classified as “Collapsed / trivialized.”

## 10. Quantifier and dependence audit

### 10.1 Countable-family algorithmic theorem

Paper-level quantifier content, in the standard oracle-parameterized reading:

`family/oracle fixed → one generator fixed → target and exact presentation arbitrary → threshold exists → all later times correct`.

Lean's exact order is:

`∀ O : OracleFamily, ∀ stream, ∀ z, Presents(stream,C_z) → ∃ T, ∀ t, T≤t → output_O(stream,t)∈C_z\S_t`.

| Object | May depend on | May not depend on |
|---|---|---|
| `O` | supplied indexed family, infinitude witnesses, uniform query | target presentation chosen later |
| concrete generator definition | `O`; at time `t`, the recursive finite prefix of `stream` and `t` | `z`, correctness feedback, convergence threshold |
| target index `z` | chosen after `O` | cannot affect generator's code/value except through the input stream's past data |
| threshold `T` | `O,stream,z,hP` | later time `t` |
| output at `t` | `O`, `t`, and past/currently processed observations | future observations by recursive unfolding; target index; output correctness feedback |

This is the essential uniformity claimed by (2.1). The threshold is not uniform over targets or presentations, and neither paper asks it to be. Because repeated candidate languages are permitted, the same target set may equal `C_z` at several indices; the formal threshold may depend on the chosen occurrence `z`, while the generator remains unchanged. This matches the papers' use of a chosen target occurrence in the indexed list.

### 10.2 Finite-set theorem

Lean's repetition-tolerant set theorem has order

`∀O, ∀stream,z, Presents(stream,C_z) → ∃T∀t≥T, f_O(S_t)∈C_z\S_t`,

where `f_O` is defined before `stream,z,T` and accepts only `S`. This matches the literal order of (4.1), modulo the fixed-universe specialization.

The injective theorem inserts `Function.Injective stream` before the existential threshold. That additional premise can affect `T` and strictly narrows the allowed presentations.

### 10.3 Supporting uniformities

* `GenLimit.target_eventually_critical`: one `T` works for all later `t` for a fixed `C,stream,z`.
* `GenLimit.target_eventually_finitelyCritical`: one `T` works for every later `t` and **all** cutoffs `m`; `m` is quantified after `t` and after the threshold.
* `GenLimit.OracleFamily.selected_eventually_constant`: for a fixed round and consistency witness, one cutoff `M` works for all larger cutoffs.
* `GenLimit.OracleFamily.stop_exists` and its arXiv counterpart: the successful cutoff may depend on the current round, observed stream, start bound, oracle, and consistency proof; there is no uniform numerical bound.
* `run_round_spec`: its selected index `n` may depend on the entire current machine state and round data, but not on a target index because none is in the signature.

### 10.4 Paper results missing with distinctive quantifier content

The missing finite-family theorem has a different uniformity:

`one algorithm → for each finite C, choose t(C) → for every K∈C and every sufficiently large distinct sample S → infinite pairwise-distinct output sequence`.

Nothing in the formal source has an existential `t(C)` before `K,S`, or an infinite output sequence from a fixed finite sample.

The missing prompted theorems quantify a prompt sequence after the target presentation and impose either robustness for every candidate language or non-triviality relative to the hidden target at each time. No formal declaration has these objects.

## 11. Difficulty, circularity, and witness-smuggling audit

| Condition/helper | Fully expanded role | Independently stated establishment | Circular, vacuous, or conclusion-encoding? |
|---|---|---|---|
| `Presents stream (C z)` | `range(stream)=C_z` | Definition, not a theorem | Genuine data assumption. It says nothing about generator outputs. |
| `OracleFamily.infinite'` | every candidate has infinitely many naturals | Structure field | Matches the paper's standing assumption. It supplies candidate freshness, not target identification. |
| `OracleFamily.query_spec` | query truth is exactly candidate membership | Structure field | Matches black-box access; no target index is supplied. |
| `Critical` | current consistency plus full inclusion into every earlier consistent candidate | Definition; nesting/eventuality stated by `critical_subset_of_le`, `target_eventually_critical` | Genuine structural condition. It does not mention the output. Inclusion can be vacuous for the least consistent candidate, as in the paper, but target correctness is not. |
| `FinitelyCritical` | same condition restricted to `u<m` | Definition; bridges and eventuality stated separately | Genuine finite approximation. At `m=0`, only the comparison clause is vacuous; successful rounds use positive growing cutoffs. |
| `HasConsistent` | some candidate index `<t` contains the sample | Definition; `criticalCandidates_nonempty` states finite-critical candidate existence | Can fail early; not assumed in final theorem. Once target index enters scope, target consistency supplies it. No conclusion encoded. |
| `selected` | maximum finite-critical index in scope | Definition; membership/maximality/stabilization signatures | Does not know `z`; not circular. |
| `stop_exists` | an endpoint successful cutoff exists beyond any start | Separate theorem signature | This is exactly termination, not an external witness hypothesis of the main theorem. Proof correctness remains unassessed. |
| `hasFreshEligible_exists` | a cutoff with a fresh selected-prefix member exists beyond any start | Separate theorem signature | Same finding for arXiv v1. |
| `run_round_spec` | target-free per-round maximality/output/freshness invariant | Separate theorem signature | Strong helper theorem, but not a hypothesis supplied to final correctness. It does not contain target membership. |
| `target_eventually_finitelyCritical` | target becomes finite-critical uniformly in cutoff | Separate theorem signature | This is the central mathematical reduction from exact presentation to criticality, not a compatibility premise assumed from outside. |
| `finitelyCritical_prefix_subset` | later critical prefix contained in earlier critical prefix | Separate theorem signature | Genuine bridge converting maximal index into target containment. |
| `eventually_target_below_sample_card` | distinct-sample count eventually exceeds fixed target index | Separate theorem signature | Genuine repair lemma; no generated output appears. |
| `GeneratesInLimit` | existential eventual correctness | Definition used only as theorem conclusion | It directly *is* the advertised conclusion, but it is never a premise of a main theorem. |

**Difficulty conclusion.** The endpoint and arXiv-v1 main theorems preserve the mathematical difficulty of the papers' countable unprompted result. Their only external assumptions are the paper's model assumptions. No helper hypothesis gives a correct output, a target subset certificate, a target index to the generator, or a convergence time. The semantic round-dependent theorem is easier than literal (4.1) only because it receives elapsed time separately. The set-interface repetition theorem restores the original finite-set difficulty without conclusion smuggling.

## 12. Edge cases, rates, and representation limits

### 12.1 Finite, infinite, empty, and zero cases

* `OracleFamily` requires every indexed language to be infinite, exactly as both papers do for generation forever.
* `Presents` is a total stream with range equality, so it cannot present an empty target; this is immaterial under infinitude.
* Candidate and universe indices begin at `0`, while the papers begin at `1`. The finite prefix `{u<m}` corresponds to `{u_1,…,u_m}` under the obvious reindexing.
* `sample stream 0=∅`; both machines begin in state `(0,0)` and may output the arbitrary default `0` before a consistent candidate enters scope. All final statements are eventual.
* `FinitelyCritical` is defined at `m=0`; the paper states it for positive `m`. The comparison clause is then vacuous, but consistency remains.
* Endpoint `q−1` uses truncated natural subtraction. `roundCounter_spec` separately states `b<q`; in actual positive rounds the start is raised above `stream t`, so the successful `q` is positive.
* The formal main theorem does not cover finite target languages, partial presentations, noise, or omitted target elements. Those models appear only in shared infrastructure or other papers.

### 12.2 Freshness and distinctness

All final Lean predicates require

`output(t) ∉ S_t`.

They do **not** require `output(t)≠output(s)` for earlier generated outputs. This is exact for the formal definition of generation in the limit in both PDFs, but does not capture the authors' informal no-repeat modification. It also does not approach theorem (2.2), which explicitly asks for an infinite sequence of distinct strings from a fixed complement.

### 12.3 Rates and probabilities

Neither paper theorem (2.1) nor the Lean theorem has a probability parameter, error probability, convergence rate, mistake bound, or query-complexity bound. Thresholds are existential and presentation-dependent. The formalization does not strengthen or weaken a rate because none is claimed.

### 12.4 Representation specialization

The papers allow an arbitrary explicitly enumerable countable universe `U`. The concrete formal algorithms are tied to `ℕ` and to its order, finite prefixes, and least elements. The imported generic core has type-polymorphic sample lemmas, but no main theorem transports either machine across an encoding/bijection. Therefore full arbitrary-countable-universe generality is **not** formally represented; this is why the positive correspondence verdicts are “Faithful specialization,” not “Exact / formally equivalent.”

## 13. Source corrections, missing results, extra results, and indeterminacies

### 13.1 Source corrections/repaired statements

1. **Finite-set interface repair.** Both papers' (4.1) require a function of `S` alone, while (4.5) uses `t`. `GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface_with_repetitions` repairs the construction by using `|S|` as an unbounded scope. This is a faithful theorem-level repair, not a formalization of the literal construction.
2. **Proceedings (5.6) repair.** The printed statement lacks the condition that `C_t` has a consistent language, even though the algorithm outputs arbitrarily otherwise. `GenLimit.OracleFamily.run_round_spec` adds that condition and also records freshness/maximality.
3. **arXiv (5.6) strengthening.** The arXiv statement has the consistent-candidate condition, but the formal invariant additionally states freshness and leastness, both present in the algorithm text.
4. **Proceedings inclusion prose.** Lean's `Critical` and chain theorem use the correct direction `later critical ⊆ earlier critical`, agreeing with the numbered results rather than the reversed explanatory sentence.
5. **Potential empty-maximum proof edge case in (4.3).** Both author proofs define a maximum over the set of earlier indices that fail to contain the target without separately treating the possibility that this set is empty; see proceedings p. 12, Appendix A.2, and arXiv-v1 p. 10, proof of (4.3). The Lean theorem signature is unconditional and covers `z=0`/empty bad-index cases, but proof bodies are excluded, so this audit does not claim that the formal source successfully repairs the proof.

### 13.2 Author-paper results missing from Lean

* finite-family uniform theorem (2.2), including closure and infinite distinct enumeration;
* robust prompted generation (7.1) in both versions;
* prompted round invariants (A.1)/(A.2) or (7.2)/(7.3);
* arXiv-v1 regular subset-query assumption and theorem (7.4)–(7.6);
* arXiv-v1 context-free corollary;
* arXiv-v1 finite-family prompted impossibility;
* identification-in-the-limit impossibility construction;
* closure-insufficiency example;
* formal pairwise-nonrepetition strengthening.

### 13.3 Extra Lean results not separately claimed by either paper

* a fully finite-set-only repetition-tolerant cardinality-scope construction (a repair of, rather than a separately claimed strengthening beyond, (4.1));
* the injective finite-set specialization;
* generic natural-antitone eventual constancy as a reusable theorem;
* executable/semantic equivalence theorems for finite tests;
* numerous machine counter, range, minimum, and maximum invariants;
* shared generic sample-cardinality and presentation-stability theorems, including statements over arbitrary types without a countability assumption;
* partial-presentation infrastructure not used in the authors' exact-presentation model.

### 13.4 Indeterminate items and precise missing evidence

1. **Lean acceptance/proof correctness:** no elaboration, compiler output, or kernel check is in evidence; theorem bodies are excluded by instruction.
2. **Axiom/classical-choice status:** imported declarations and proof bodies were not audited. `noncomputable` marks the semantic/set rules, but the exact axiom footprint is unknown.
3. **Extracted algorithm status:** the finite-query definitions are explicit and their success predicates are decidable finite membership tests, but the cutoffs use `Nat.find` applied to proof terms of existence. Without the imported operational definition, those proof bodies, a compilation artifact, or a separate `Computable` theorem, executable extraction is indeterminate.
4. **Exact query count:** no formal cost model or bound is stated.
5. **Transport to arbitrary countable `U`:** no encoding/bijection theorem is present.
6. **Generated structure declarations:** constructors/projections/recursors produced by elaboration are not independently inventoried; source-visible structure fields were audited.

## 14. Declaration-by-declaration target-scope audit

This appendix covers every theorem declaration in the Paper01-specific modules. Pure decidability instances are listed after the theorem matrix. Definitions are covered recursively in §7. A row marked “paper-internal” corresponds to an explicit definition, algorithm clause, or proof-level fact even when the paper did not assign it a separate theorem number.

### 14.1 Whole-language criticality

| Lean declaration and compact statement key (exact signature in §16) | Paper counterpart | Correspondence verdict | Difficulty verdict | Finding |
|---|---|---|---|---|
| `GenLimit.critical_subset_of_le {C} {stream} {t i j} (hij : i ≤ j) (hi : Critical C stream t i) (hj : Critical C stream t j) : C j ⊆ C i` | both versions (4.4) | Faithful generalization | Preserved | Adds only `i=j`. |
| `GenLimit.least_consistent_critical {C} {stream} {t n} (hn : Consistent C stream t n) (hleast : ∀ i, i < n → ¬ Consistent C stream t i) : Critical C stream t n` | prose after (4.2) | Exact / formally equivalent | Preserved | Genuine existence of a critical candidate. |
| `GenLimit.bad_earlier_eventually_inconsistent {C} {stream} {z} (hP : Presents stream (C z)) : ∃ T, ∀ t, T ≤ t → ∀ i, i < z → ¬ C z ⊆ C i → ¬ Consistent C stream t i` | proof-level content for (4.3) | Faithful specialization | Preserved | Uniform over the finite earlier-index scope. |
| `GenLimit.target_eventually_critical {C} {stream} {z} (hP : Presents stream (C z)) : ∃ T, ∀ t, T ≤ t → Critical C stream t z` | both versions (4.3) | Faithful specialization | Preserved | Same eventuality; `ℕ` universe/indexing. |

### 14.2 Finite criticality

| Lean declaration and compact statement key (exact signature in §16) | Paper counterpart | Correspondence verdict | Difficulty verdict | Finding |
|---|---|---|---|---|
| `GenLimit.critical_finitelyCritical {C} {stream} {t n} (h : Critical C stream t n) (m : ℕ) : FinitelyCritical C stream t m n` | implication preceding (5.2) | Exact / formally equivalent | Preserved | Whole inclusion implies every finite-prefix inclusion. |
| `GenLimit.finitelyCritical_cutoff_mono {C} {stream} {t m m' n} (hmm' : m' ≤ m) (h : FinitelyCritical C stream t m n) : FinitelyCritical C stream t m' n` | (5.4) | Faithful generalization | Preserved | Non-strict comparison and zero cutoff included. |
| `GenLimit.finitelyCritical_prefix_subset {C} {stream} {t m i j} (hij : i ≤ j) (hi : FinitelyCritical C stream t m i) (hj : FinitelyCritical C stream t m j) : ∀ u, u < m → u ∈ C j → u ∈ C i` | (5.3) | Faithful generalization | Preserved | Equality case added. |
| `GenLimit.least_consistent_finitelyCritical {C} {stream} {t n} (hn : Consistent C stream t n) (hleast : ∀ i, i < n → ¬ Consistent C stream t i) (m : ℕ) : FinitelyCritical C stream t m n` | paper-internal existence fact | Exact / formally equivalent | Preserved | Supplies nonemptiness of finite-critical candidates. |
| `GenLimit.target_eventually_finitelyCritical {C} {stream} {z} (hP : Presents stream (C z)) : ∃ T, ∀ t, T ≤ t → ∀ m, FinitelyCritical C stream t m z` | (5.2) | Faithful generalization | Preserved | Uniform all-natural cutoff statement. |

### 14.3 Finite-oracle bridges and candidate selection

| Lean declaration and compact statement key (exact signature in §16) | Paper counterpart | Correspondence verdict | Difficulty verdict | Finding |
|---|---|---|---|---|
| `GenLimit.OracleFamily.mem_finitePrefix {i m u} : u ∈ O.finitePrefix i m ↔ u < m ∧ u ∈ O.language i` | definition of `L_i[m]` | Exact / formally equivalent | Preserved | Exact finite-query realization. |
| `GenLimit.OracleFamily.consistentAt_iff {stream} {t i} : O.ConsistentAt stream t i ↔ Consistent O.language stream t i` | finite membership-query consistency test | Exact / formally equivalent | Preserved | Genuine executable/semantic bridge. |
| `GenLimit.OracleFamily.finitelyCriticalAt_iff {stream} {t m n} : O.FinitelyCriticalAt stream t m n ↔ FinitelyCritical O.language stream t m n` | finite membership-query criticality test | Exact / formally equivalent | Preserved | No subset oracle. |
| `GenLimit.OracleFamily.mem_consistentCandidates {stream} {t i} : i ∈ O.consistentCandidates stream t ↔ i < t ∧ O.ConsistentAt stream t i` | definition of candidates in `C_t` | Exact / formally equivalent | Preserved | Mechanical but exact. |
| `GenLimit.OracleFamily.mem_criticalCandidates {stream} {t m n} : n ∈ O.criticalCandidates stream t m ↔ n < t ∧ O.FinitelyCriticalAt stream t m n` | definition of `(t,m)`-critical candidates in `C_t` | Exact / formally equivalent | Preserved | Mechanical but exact. |
| `GenLimit.OracleFamily.criticalCandidates_nonempty {stream} {t} (h : O.HasConsistent stream t) (m : ℕ) : (O.criticalCandidates stream t m).Nonempty` | first consistent language is finite-critical | Exact / formally equivalent | Preserved | Does not assume target correctness. |
| `GenLimit.OracleFamily.selected_mem {stream} {t m} (h : O.HasConsistent stream t) : O.selected stream t m h ∈ O.criticalCandidates stream t m` | definition of `n_t(m)` | Exact / formally equivalent | Preserved | Max is a candidate. |
| `GenLimit.OracleFamily.selected_lt {stream} {t m} (h : O.HasConsistent stream t) : O.selected stream t m h < t` | `n_t(m)∈C_t` | Exact / formally equivalent | Preserved | Scope property. |
| `GenLimit.OracleFamily.selected_finitelyCriticalAt {stream} {t m} (h : O.HasConsistent stream t) : O.FinitelyCriticalAt stream t m (O.selected stream t m h)` | selected finite criticality | Exact / formally equivalent | Preserved | Oracle-level version. |
| `GenLimit.OracleFamily.selected_finitelyCritical {stream} {t m} (h : O.HasConsistent stream t) : FinitelyCritical O.language stream t m (O.selected stream t m h)` | selected finite criticality | Exact / formally equivalent | Preserved | Semantic version. |
| `GenLimit.OracleFamily.selected_max {stream} {t m n} (h : O.HasConsistent stream t) (hnt : n < t) (hn : O.FinitelyCriticalAt stream t m n) : n ≤ O.selected stream t m h` | maximality of `n_t(m)` | Exact / formally equivalent | Preserved | Needed for target-index comparison. |
| `GenLimit.OracleFamily.selected_antitone {stream} {t m m'} (h : O.HasConsistent stream t) (hmm' : m ≤ m') : O.selected stream t m' h ≤ O.selected stream t m h` | disruptive-iteration monotonicity in proof of (5.5) | Faithful generalization | Preserved | States all cutoff pairs. |
| `GenLimit.OracleFamily.antitone_nat_eventually_constant (f : ℕ → ℕ) (hf : Antitone f) : ∃ M, ∀ m, M ≤ m → f m = f M` | no separate paper result | Extra Lean result not claimed by the paper | Indeterminate | Reusable general lemma. |
| `GenLimit.OracleFamily.selected_eventually_constant {stream} {t} (h : O.HasConsistent stream t) : ∃ M, ∀ m, M ≤ m → O.selected stream t m h = O.selected stream t M h` | last-disruptive-iteration fact in (5.5) | Exact / formally equivalent | Preserved | Genuine termination ingredient. |

### 14.4 Proceedings endpoint machine

| Lean declaration and compact statement key (exact signature in §16) | Paper counterpart | Correspondence verdict | Difficulty verdict | Finding |
|---|---|---|---|---|
| `GenLimit.OracleFamily.stop_exists {stream} {t} (h : O.HasConsistent stream t) (b : ℕ) : ∃ q, b < q ∧ O.Stop stream t h q` | proceedings (5.5) successful branch | Faithful specialization | Preserved | Finite termination certificate; no target. |
| `GenLimit.OracleFamily.roundCounter_spec {stream} {t} (h : O.HasConsistent stream t) (b : ℕ) : b < O.roundCounter stream t h b ∧ O.Stop stream t h (O.roundCounter stream t h b)` | first successful endpoint cutoff | Exact / formally equivalent | Preserved | Definition/specification fact. |
| `GenLimit.OracleFamily.roundCounter_gt {stream} {t} (h : O.HasConsistent stream t) (b : ℕ) : b < O.roundCounter stream t h b` | counter increment | Exact / formally equivalent | Preserved | Freshness infrastructure. |
| `GenLimit.OracleFamily.roundCounter_output_mem_selectedPrefix {stream} {t} (h : O.HasConsistent stream t) (b : ℕ) : O.roundCounter stream t h b - 1 ∈ O.finitePrefix (O.selected stream t (O.roundCounter stream t h b) h) (O.roundCounter stream t h b)` | endpoint belongs to selected prefix | Exact / formally equivalent | Preserved | Matches proceedings stopping rule. |
| `GenLimit.OracleFamily.processRound_counter_ge_start (stream) (t b) : b ≤ (O.processRound stream t b).counter` | paper-internal counter monotonicity | Exact / formally equivalent | Preserved | No correctness content. |
| `GenLimit.OracleFamily.processRound_of_hasConsistent {stream} {t b} (h : O.HasConsistent stream t) : O.processRound stream t b = ⟨O.roundCounter stream t h b, O.roundCounter stream t h b - 1⟩` | successful round assignment | Exact / formally equivalent | Preserved | Endpoint output. |
| `GenLimit.OracleFamily.run_succ_counter_ge_start (stream) (t) : max (O.run stream t).counter (stream t + 1) ≤ (O.run stream (t + 1)).counter` | initialization/update rule | Exact / formally equivalent | Preserved | Zero-based shift. |
| `GenLimit.OracleFamily.run_counter_bounds {stream} : ∀ {t k}, k < t → stream k < (O.run stream t).counter` | all prior observations below cutoff | Exact / formally equivalent | Preserved | Causality/freshness invariant. |
| `GenLimit.OracleFamily.sample_lt_roundStart {stream} {t u} (hu : u ∈ sample stream (t + 1)) : u < max (O.run stream t).counter (stream t + 1)` | paper-internal freshness fact | Exact / formally equivalent | Preserved | Every observed value below next search start. |
| `GenLimit.OracleFamily.run_round_spec {stream} {t} (ht : 0 < t) (h : O.HasConsistent stream t) : ∃ n, n < t ∧ FinitelyCritical ... ∧ maximality ∧ output-prefix-membership ∧ output-freshness` | printed proceedings (5.6) | Related but materially different | Indeterminate | Repaired hypotheses plus strengthened conclusion. |
| `GenLimit.OracleFamily.eventual_correctness {stream} {z} (hP : Presents stream (O.language z)) : O.GeneratesInLimit stream z` | proceedings (5.7)/(2.1) | Faithful specialization | Preserved | Main result. |
| `GenLimit.OracleFamily.kleinbergMullainathan_main {stream} {z} (hP : Presents stream (O.language z)) : O.GeneratesInLimit stream z` | proceedings (2.1) | Faithful specialization | Preserved | Duplicate proposition. |

### 14.5 arXiv-v1 machine

| Lean declaration and compact statement key (exact signature in §16) | Paper counterpart | Correspondence verdict | Difficulty verdict | Finding |
|---|---|---|---|---|
| `GenLimit.OracleFamily.ArxivV1.mem_eligible {stream} {t q u} (h : O.HasConsistent stream t) : u ∈ eligible O stream t h q ↔ u ∈ O.finitePrefix (O.selected stream t q h) q ∧ u ∉ sample stream t` | arXiv step (iv) | Exact / formally equivalent | Preserved | Fresh selected-prefix membership. |
| `GenLimit.OracleFamily.ArxivV1.hasFreshEligible_exists {stream} {t} (h : O.HasConsistent stream t) (b : ℕ) : ∃ q, b < q ∧ HasFreshEligible O stream t h q` | arXiv (5.5) | Faithful specialization | Preserved | Termination condition. |
| `GenLimit.OracleFamily.ArxivV1.roundCounter_spec {stream} {t} (h : O.HasConsistent stream t) (b : ℕ) : b < roundCounter O stream t h b ∧ HasFreshEligible O stream t h (roundCounter O stream t h b)` | first successful cutoff | Exact / formally equivalent | Preserved | Definition/specification. |
| `GenLimit.OracleFamily.ArxivV1.roundCounter_gt ... : b < roundCounter O stream t h b` | counter increment | Exact / formally equivalent | Preserved | Direct projection. |
| `GenLimit.OracleFamily.ArxivV1.roundCounter_le_of_freshEligible ... (hbq : b < q) (hq : HasFreshEligible O stream t h q) : roundCounter O stream t h b ≤ q` | “first successful cutoff” implicit in algorithm | Exact / formally equivalent | Preserved | Least-cutoff property. |
| `GenLimit.OracleFamily.ArxivV1.roundOutput_mem_eligible ... : roundOutput O stream t h b ∈ eligible O stream t h (roundCounter O stream t h b)` | arXiv minimum-output rule | Exact / formally equivalent | Preserved | Output eligible. |
| `GenLimit.OracleFamily.ArxivV1.roundOutput_le_of_mem ... (hu : u ∈ eligible ...) : roundOutput O stream t h b ≤ u` | arXiv minimum-output rule | Exact / formally equivalent | Preserved | Leastness. |
| `GenLimit.OracleFamily.ArxivV1.roundOutput_spec ... : prefix-membership ∧ freshness ∧ leastness` | arXiv step (iv) | Exact / formally equivalent | Preserved | Packages the exact output rule. |
| `GenLimit.OracleFamily.ArxivV1.processRound_counter_ge_start ...` | paper-internal counter invariant | Exact / formally equivalent | Preserved | Same as endpoint machine. |
| `GenLimit.OracleFamily.ArxivV1.processRound_of_hasConsistent ... : processRound ... = ⟨roundCounter..., roundOutput...⟩` | successful round assignment | Exact / formally equivalent | Preserved | Counter/output separated. |
| `GenLimit.OracleFamily.ArxivV1.run_succ_counter_ge_start ...` | arXiv state update | Exact / formally equivalent | Preserved | Same update rule. |
| `GenLimit.OracleFamily.ArxivV1.run_counter_bounds ...` | prior observations below cutoff | Exact / formally equivalent | Preserved | Finite-access/freshness invariant. |
| `GenLimit.OracleFamily.ArxivV1.sample_lt_runCounter ...` | observed values below stored cutoff | Exact / formally equivalent | Preserved | Paper-internal consequence. |
| `GenLimit.OracleFamily.ArxivV1.run_round_spec ... : ∃n, maximal finite-criticality ∧ prefix-membership ∧ freshness ∧ leastness` | arXiv (5.6) and step (iv) | Faithful generalization | Strengthened / harder | Adds explicit maximality/freshness/leastness. |
| `GenLimit.OracleFamily.ArxivV1.eventual_correctness ... : GeneratesInLimit O stream z` | arXiv (5.7)/(2.1) | Faithful specialization | Preserved | Main result. |
| `GenLimit.OracleFamily.ArxivV1.kleinbergMullainathan_main ... : GeneratesInLimit O stream z` | arXiv (2.1) | Faithful specialization | Preserved | Duplicate proposition. |

### 14.6 Round-indexed semantic declarations

| Lean declaration and compact statement key (exact signature in §16) | Paper counterpart | Correspondence verdict | Difficulty verdict | Finding |
|---|---|---|---|---|
| `GenLimit.KM.Semantic.mem_criticalIndices {C} {stream} {t n} : n ∈ criticalIndices C stream t ↔ n < t ∧ Critical C stream t n` | (4.5) candidate scope | Exact / formally equivalent | Preserved | Mechanical characterization. |
| `GenLimit.KM.Semantic.focus_spec {C} {stream} {t z} (hzt : z < t) (hz : Critical C stream t z) : focus C stream t < t ∧ Critical C stream t (focus C stream t) ∧ z ≤ focus C stream t` | maximal critical index in (4.5) | Exact / formally equivalent | Preserved | Target-free max property except arbitrary comparison index `z`. |
| `GenLimit.KM.Semantic.fresh_spec (O) (stream) (t i) : fresh O stream t i ∈ O.language i ∧ fresh O stream t i ∉ sample stream t` | lowest unseen member in (4.5) | Exact / formally equivalent | Preserved | Uses infinitude only. |
| `GenLimit.KM.Semantic.fresh_le_of_mem_of_not_mem_sample ... : fresh O stream t i ≤ x` | “lowest-indexed element” in (4.5) | Exact / formally equivalent | Preserved | Leastness. |
| `GenLimit.KM.Semantic.generator_spec ... : generator O stream t ∈ O.language (focus ...) ∧ generator O stream t ∉ sample stream t` | construction property | Exact / formally equivalent | Preserved | Not target correctness. |
| `GenLimit.KM.Semantic.generator_le_of_mem_focus_of_not_mem_sample ... : generator O stream t ≤ x` | leastness of construction | Exact / formally equivalent | Preserved | Paper-internal. |
| `GenLimit.KM.Semantic.kleinbergMullainathan_main ... : GeneratesInLimit O stream z` | literal (4.6) after round-dependent (4.5) | Related but materially different | Weakened / easier | Extra elapsed-time input; valid theorem but not literal finite-set function. |

### 14.7 Finite-observed-set declarations

| Lean declaration and compact statement key (exact signature in §16) | Paper counterpart | Correspondence verdict | Difficulty verdict | Finding |
|---|---|---|---|---|
| `GenLimit.KM.SetInterface.consistentOn_sample_iff ... : ConsistentOn C (sample stream t) n ↔ Consistent C stream t n` | consistency rewritten as a finite-set predicate | Exact / formally equivalent | Preserved | Definitional bridge. |
| `GenLimit.KM.SetInterface.criticalOn_sample_iff ... : CriticalOn C (sample stream t) n ↔ Critical C stream t n` | criticality rewritten as a finite-set predicate | Exact / formally equivalent | Preserved | Definitional bridge. |
| `GenLimit.KM.SetInterface.criticalOn_subset_of_le ... : C j ⊆ C i` | (4.4) in set interface | Faithful generalization | Preserved | Equality case added. |
| `GenLimit.KM.SetInterface.mem_criticalIndices ... : n ∈ criticalIndices C S ↔ n < S.card ∧ CriticalOn C S n` | no literal paper construction; repair scope | Extra Lean result not claimed by the paper | Indeterminate | New cardinality-scope design. |
| `GenLimit.KM.SetInterface.focus_spec ... : focus C S < S.card ∧ CriticalOn ... ∧ z ≤ focus C S` | repair scope maximality | Extra Lean result not claimed by the paper | Indeterminate | Supports repaired theorem. |
| `GenLimit.KM.SetInterface.fresh_spec ... : fresh O S i ∈ O.language i ∧ fresh O S i ∉ S` | lowest unseen element in (4.5) | Exact / formally equivalent | Preserved | Finite-set form. |
| `GenLimit.KM.SetInterface.generator_spec ... : generator O S ∈ O.language (focus O.language S) ∧ generator O S ∉ S` | repaired construction property | Extra Lean result not claimed by the paper | Indeterminate | No target conclusion. |
| `GenLimit.KM.SetInterface.sample_card_of_injective ... : (sample stream t).card = t` | no separate paper theorem | Extra Lean result not claimed by the paper | Indeterminate | Explains injective specialization. |
| `GenLimit.KM.SetInterface.eventually_target_below_sample_card ... : ∃T∀t≥T, z < (sample stream t).card` | no separate paper theorem | Extra Lean result not claimed by the paper | Indeterminate | Genuine repetition-tolerant scope lemma. |
| `GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface ... (hinjective) : GeneratesFromObservedSet O stream z` | (4.1) under injective presentation | Faithful specialization | Weakened / easier | Added hypothesis. |
| `GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface_with_repetitions ... : GeneratesFromObservedSet O stream z` | literal (4.1)/(4.6) | Faithful specialization | Preserved | Repaired construction; same theorem over `ℕ`. |

### 14.8 Decidability instances and source-visible structures

The following public instances assert decision procedures for finite predicates; they are faithful implementation infrastructure rather than independent paper results:

```lean
GenLimit.OracleFamily.consistentAtDecidable
GenLimit.OracleFamily.finitelyCriticalAtDecidable
GenLimit.OracleFamily.hasConsistentDecidable
GenLimit.OracleFamily.stopDecidable
GenLimit.OracleFamily.ArxivV1.hasFreshEligibleDecidable
```

Each has **correspondence verdict:** `Exact / formally equivalent` and **difficulty verdict:** `Preserved` relative to the paper's claim that the corresponding finite tests can be carried out with finitely many membership queries.

The source-visible machine structures are:

```lean
structure GenLimit.OracleFamily.MachineState where
  counter : ℕ
  output : ℕ

structure GenLimit.OracleFamily.ArxivV1.MachineState where
  counter : ℕ
  output : ℕ
```

They are data interfaces, not mathematical result claims. The exact set of elaborator-generated constructors/projections/recursors is outside this source-only audit.

## 15. Author-statement citation register

All shorthand such as “proceedings (5.6),” “arXiv (5.5),” or “both versions (4.4)” in the comparison matrices resolves to the full filename/page citations below. Page numbers are the printed PDF page numbers visible in the supplied files.

### 15.1 NeurIPS 2024 proceedings

| Statement or claim | Full supplied-source citation |
|---|---|
| Model, exact positive enumeration, membership-query access, repetitions, infinitude | `01-kleinberg-mullainathan-neurips2024.pdf`, pp. 3–4, §2 |
| (2.1), countable-family generation | `01-kleinberg-mullainathan-neurips2024.pdf`, (2.1), p. 4, §2; concrete correctness (5.7), p. 8, §5 |
| (2.2), finite-family uniform generation | `01-kleinberg-mullainathan-neurips2024.pdf`, (2.2), p. 4, §2; proof pp. 13–14, Appendix A.4 |
| (4.1), finite-set semantic function | `01-kleinberg-mullainathan-neurips2024.pdf`, (4.1), p. 5, §4 |
| (4.2)–(4.6), criticality, nesting, construction, semantic correctness | `01-kleinberg-mullainathan-neurips2024.pdf`, (4.2)–(4.6), p. 6, §4; proof of (4.3)/(4.6), pp. 12–13, Appendix A.2 |
| (5.1)–(5.4), finite-prefix criticality facts | `01-kleinberg-mullainathan-neurips2024.pdf`, (5.1)–(5.4), p. 7, §5; proof of (5.4), p. 13, Appendix A.3 |
| (5.5)–(5.7), termination, round invariant, correctness | `01-kleinberg-mullainathan-neurips2024.pdf`, (5.5)–(5.7), p. 8, §5; proofs pp. 13–14, Appendix A.3 |
| (7.1), robust-prompt generation | `01-kleinberg-mullainathan-neurips2024.pdf`, (7.1), p. 10, §7 |
| (A.1)–(A.2), prompted round invariant/correctness | `01-kleinberg-mullainathan-neurips2024.pdf`, (A.1)–(A.2), pp. 14–15, Appendix A.5 |
| Identification impossibility construction | `01-kleinberg-mullainathan-neurips2024.pdf`, pp. 12–13, Appendix A.1 |
| Closure proof for the finite family | `01-kleinberg-mullainathan-neurips2024.pdf`, pp. 8–9, §6; pp. 13–14, Appendix A.4 |
| Infinite-family closure counterexample | `01-kleinberg-mullainathan-neurips2024.pdf`, p. 15, Appendix A.6 |
| Informal no-repeat modifications | `01-kleinberg-mullainathan-neurips2024.pdf`, pp. 6 and 8, §§4–5 |
| Preliminary “minimal language” definition | `01-kleinberg-mullainathan-neurips2024.pdf`, p. 5, §4, prose preceding (4.2) |
| Reversed inclusion sentence preceding criticality | `01-kleinberg-mullainathan-neurips2024.pdf`, p. 5, §4, prose immediately before (4.2) |

### 15.2 arXiv version 1

| Statement or claim | Full supplied-source citation |
|---|---|
| Model, exact positive enumeration, membership-query access, repetitions, infinitude | `01-kleinberg-mullainathan-arxiv-v1.pdf`, pp. 4–6, §§2–3 |
| (2.1), countable-family generation | `01-kleinberg-mullainathan-arxiv-v1.pdf`, (2.1), p. 4, §2; concrete correctness (5.7), p. 16, §5 |
| (2.2), finite-family uniform generation | `01-kleinberg-mullainathan-arxiv-v1.pdf`, (2.2), p. 5, §2; proof pp. 16–17, §6 |
| (4.1), finite-set semantic function | `01-kleinberg-mullainathan-arxiv-v1.pdf`, (4.1), p. 9, §4 |
| (4.2)–(4.4), criticality and nesting | `01-kleinberg-mullainathan-arxiv-v1.pdf`, (4.2)–(4.4), p. 10, §4 |
| (4.5)–(4.6), semantic construction/correctness | `01-kleinberg-mullainathan-arxiv-v1.pdf`, (4.5)–(4.6), p. 11, §4 |
| (5.1)–(5.4), finite-prefix criticality facts | `01-kleinberg-mullainathan-arxiv-v1.pdf`, (5.1)–(5.4), p. 12, §5 |
| (5.5), first-fresh-eligible round termination | `01-kleinberg-mullainathan-arxiv-v1.pdf`, (5.5), p. 13, §5 |
| (5.6)–(5.7), round invariant and correctness | `01-kleinberg-mullainathan-arxiv-v1.pdf`, (5.6)–(5.7), p. 16, §5 |
| (7.1), robust-prompt generation | `01-kleinberg-mullainathan-arxiv-v1.pdf`, (7.1), p. 18, §7 |
| (7.2)–(7.3), robust-prompt round invariant/correctness | `01-kleinberg-mullainathan-arxiv-v1.pdf`, (7.2)–(7.3), p. 20, §7.1 |
| (7.4)–(7.6), regular-subset-query model and non-trivial-prompt theorem | `01-kleinberg-mullainathan-arxiv-v1.pdf`, (7.4)–(7.5), p. 21, §7.2; (7.6), p. 22, §7.2 |
| Context-free-language corollary | `01-kleinberg-mullainathan-arxiv-v1.pdf`, pp. 20–21, §7.2, prose and footnotes 4–5 |
| No finite uniform bound for prompted generation | `01-kleinberg-mullainathan-arxiv-v1.pdf`, pp. 22–23, §7.3 |
| Identification impossibility construction | `01-kleinberg-mullainathan-arxiv-v1.pdf`, pp. 6–7, §3.1 |
| Closure definition/counterexample | `01-kleinberg-mullainathan-arxiv-v1.pdf`, pp. 7–8, §3.2 |
| Informal no-repeat modifications | `01-kleinberg-mullainathan-arxiv-v1.pdf`, pp. 11 and 16, §§4–5 |
| Preliminary inclusion-minimal-language definition | `01-kleinberg-mullainathan-arxiv-v1.pdf`, p. 9, §4, prose preceding (4.2) |

## 16. Exact normalized Lean signatures

This appendix supplies the exact or whitespace-normalized source signatures behind the compact keys in §14. Proof bodies are omitted. Each heading gives the fully qualified declaration name. Signatures that contain a free `O` occur under an enclosing source declaration `variable (O : GenLimit.OracleFamily)`; therefore `O` is an explicit earlier parameter of the resulting public declaration even where the local theorem line does not repeat its type.

### 16.1 All 37 public target-specific definition declarations

These are the exact or whitespace-normalized definitions, including their statement-relevant right-hand sides. The same free-`O` convention described above applies.

#### `GenLimit.Critical`

```lean
def GenLimit.Critical (C : LanguageFamily) (stream : ℕ → ℕ) (t n : ℕ) : Prop :=
  Consistent C stream t n ∧
    ∀ i, i ≤ n → Consistent C stream t i → C n ⊆ C i
```

#### `GenLimit.FinitelyCritical`

```lean
def GenLimit.FinitelyCritical
    (C : LanguageFamily) (stream : ℕ → ℕ) (t m n : ℕ) : Prop :=
  Consistent C stream t n ∧
    ∀ i, i ≤ n → Consistent C stream t i →
      ∀ u, u < m → u ∈ C n → u ∈ C i
```

#### `GenLimit.OracleFamily.finitePrefix`

```lean
def GenLimit.OracleFamily.finitePrefix (i m : ℕ) : Finset ℕ :=
  (Finset.range m).filter (fun u => O.query i u = true)
```

#### `GenLimit.OracleFamily.inconsistentSamples`

```lean
def GenLimit.OracleFamily.inconsistentSamples (stream : ℕ → ℕ) (t i : ℕ) : Finset ℕ :=
  (sample stream t).filter (fun u => O.query i u = false)
```

#### `GenLimit.OracleFamily.ConsistentAt`

```lean
def GenLimit.OracleFamily.ConsistentAt (stream : ℕ → ℕ) (t i : ℕ) : Prop :=
  O.inconsistentSamples stream t i = ∅
```

#### `GenLimit.OracleFamily.criticalFailures`

```lean
def GenLimit.OracleFamily.criticalFailures (stream : ℕ → ℕ) (t m n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun i =>
    O.ConsistentAt stream t i ∧
      ¬ O.finitePrefix n m ⊆ O.finitePrefix i m)
```

#### `GenLimit.OracleFamily.FinitelyCriticalAt`

```lean
def GenLimit.OracleFamily.FinitelyCriticalAt (stream : ℕ → ℕ) (t m n : ℕ) : Prop :=
  O.ConsistentAt stream t n ∧ O.criticalFailures stream t m n = ∅
```

#### `GenLimit.OracleFamily.consistentCandidates`

```lean
def GenLimit.OracleFamily.consistentCandidates (stream : ℕ → ℕ) (t : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun i => O.ConsistentAt stream t i)
```

#### `GenLimit.OracleFamily.HasConsistent`

```lean
def GenLimit.OracleFamily.HasConsistent (stream : ℕ → ℕ) (t : ℕ) : Prop :=
  (O.consistentCandidates stream t).Nonempty
```

#### `GenLimit.OracleFamily.criticalCandidates`

```lean
def GenLimit.OracleFamily.criticalCandidates (stream : ℕ → ℕ) (t m : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun n => O.FinitelyCriticalAt stream t m n)
```

#### `GenLimit.OracleFamily.selected`

```lean
def GenLimit.OracleFamily.selected
    (stream : ℕ → ℕ) (t m : ℕ) (h : O.HasConsistent stream t) : ℕ :=
  (O.criticalCandidates stream t m).max'
    (O.criticalCandidates_nonempty h m)
```

#### `GenLimit.OracleFamily.Stop`

```lean
def GenLimit.OracleFamily.Stop
    (stream : ℕ → ℕ) (t : ℕ) (h : O.HasConsistent stream t) (q : ℕ) : Prop :=
  O.query (O.selected stream t q h) (q - 1) = true
```

#### `GenLimit.OracleFamily.roundCounter`

```lean
def GenLimit.OracleFamily.roundCounter
    (stream : ℕ → ℕ) (t : ℕ) (h : O.HasConsistent stream t) (b : ℕ) : ℕ :=
  Nat.find (O.stop_exists h b)
```

#### `GenLimit.OracleFamily.processRound`

```lean
def GenLimit.OracleFamily.processRound
    (stream : ℕ → ℕ) (t b : ℕ) : MachineState :=
  if h : O.HasConsistent stream t then
    let q := O.roundCounter stream t h b
    ⟨q, q - 1⟩
  else
    ⟨b, 0⟩
```

#### `GenLimit.OracleFamily.run`

```lean
def GenLimit.OracleFamily.run (O : OracleFamily) (stream : ℕ → ℕ) : ℕ → MachineState
  | 0 => ⟨0, 0⟩
  | t + 1 =>
      let previous := run O stream t
      let start := max previous.counter (stream t + 1)
      O.processRound stream (t + 1) start
```

#### `GenLimit.OracleFamily.kmGenerator`

```lean
def GenLimit.OracleFamily.kmGenerator (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  (O.run stream t).output
```

#### `GenLimit.OracleFamily.GeneratesInLimit`

```lean
def GenLimit.OracleFamily.GeneratesInLimit (stream : ℕ → ℕ) (z : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    O.kmGenerator stream t ∈ O.language z ∧
      O.kmGenerator stream t ∉ sample stream t
```

#### `GenLimit.OracleFamily.ArxivV1.eligible`

```lean
def GenLimit.OracleFamily.ArxivV1.eligible
    (stream : ℕ → ℕ) (t : ℕ) (h : O.HasConsistent stream t)
    (q : ℕ) : Finset ℕ :=
  (O.finitePrefix (O.selected stream t q h) q).filter
    (fun u => u ∉ sample stream t)
```

#### `GenLimit.OracleFamily.ArxivV1.HasFreshEligible`

```lean
def GenLimit.OracleFamily.ArxivV1.HasFreshEligible
    (stream : ℕ → ℕ) (t : ℕ) (h : O.HasConsistent stream t)
    (q : ℕ) : Prop :=
  (eligible O stream t h q).Nonempty
```

#### `GenLimit.OracleFamily.ArxivV1.roundCounter`

```lean
def GenLimit.OracleFamily.ArxivV1.roundCounter
    (stream : ℕ → ℕ) (t : ℕ) (h : O.HasConsistent stream t)
    (b : ℕ) : ℕ :=
  Nat.find (hasFreshEligible_exists O h b)
```

#### `GenLimit.OracleFamily.ArxivV1.roundOutput`

```lean
def GenLimit.OracleFamily.ArxivV1.roundOutput
    (stream : ℕ → ℕ) (t : ℕ) (h : O.HasConsistent stream t)
    (b : ℕ) : ℕ :=
  (eligible O stream t h (roundCounter O stream t h b)).min'
    (roundCounter_spec O h b).2
```

#### `GenLimit.OracleFamily.ArxivV1.processRound`

```lean
def GenLimit.OracleFamily.ArxivV1.processRound
    (stream : ℕ → ℕ) (t b : ℕ) : MachineState :=
  if h : O.HasConsistent stream t then
    ⟨roundCounter O stream t h b, roundOutput O stream t h b⟩
  else
    ⟨b, 0⟩
```

#### `GenLimit.OracleFamily.ArxivV1.run`

```lean
def GenLimit.OracleFamily.ArxivV1.run (O : OracleFamily) (stream : ℕ → ℕ) : ℕ → MachineState
  | 0 => ⟨0, 0⟩
  | t + 1 =>
      let previous := run O stream t
      let start := max previous.counter (stream t + 1)
      processRound O stream (t + 1) start
```

#### `GenLimit.OracleFamily.ArxivV1.kmGenerator`

```lean
def GenLimit.OracleFamily.ArxivV1.kmGenerator (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  (run O stream t).output
```

#### `GenLimit.OracleFamily.ArxivV1.GeneratesInLimit`

```lean
def GenLimit.OracleFamily.ArxivV1.GeneratesInLimit (stream : ℕ → ℕ) (z : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    kmGenerator O stream t ∈ O.language z ∧
      kmGenerator O stream t ∉ sample stream t
```

#### `GenLimit.KM.Semantic.criticalIndices`

```lean
noncomputable def GenLimit.KM.Semantic.criticalIndices
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range t).filter (Critical C stream t)
```

#### `GenLimit.KM.Semantic.focus`

```lean
noncomputable def GenLimit.KM.Semantic.focus
    (C : LanguageFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ := by
  classical
  let candidates := criticalIndices C stream t
  exact if h : candidates.Nonempty then candidates.max' h else 0
```

#### `GenLimit.KM.Semantic.fresh`

```lean
noncomputable def GenLimit.KM.Semantic.fresh
    (O : OracleFamily) (stream : ℕ → ℕ) (t i : ℕ) : ℕ := by
  classical
  exact Nat.find ((O.infinite' i).exists_notMem_finset (sample stream t))
```

#### `GenLimit.KM.Semantic.generator`

```lean
noncomputable def GenLimit.KM.Semantic.generator
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  fresh O stream t (focus O.language stream t)
```

#### `GenLimit.KM.Semantic.GeneratesInLimit`

```lean
def GenLimit.KM.Semantic.GeneratesInLimit
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    generator O stream t ∈ O.language z ∧
      generator O stream t ∉ sample stream t
```

#### `GenLimit.KM.SetInterface.ConsistentOn`

```lean
def GenLimit.KM.SetInterface.ConsistentOn
    (C : LanguageFamily) (S : Finset ℕ) (n : ℕ) : Prop :=
  (↑S : Set ℕ) ⊆ C n
```

#### `GenLimit.KM.SetInterface.CriticalOn`

```lean
def GenLimit.KM.SetInterface.CriticalOn
    (C : LanguageFamily) (S : Finset ℕ) (n : ℕ) : Prop :=
  ConsistentOn C S n ∧
    ∀ i, i ≤ n → ConsistentOn C S i → C n ⊆ C i
```

#### `GenLimit.KM.SetInterface.criticalIndices`

```lean
noncomputable def GenLimit.KM.SetInterface.criticalIndices
    (C : LanguageFamily) (S : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.range S.card).filter (CriticalOn C S)
```

#### `GenLimit.KM.SetInterface.focus`

```lean
noncomputable def GenLimit.KM.SetInterface.focus
    (C : LanguageFamily) (S : Finset ℕ) : ℕ := by
  classical
  let candidates := criticalIndices C S
  exact if h : candidates.Nonempty then candidates.max' h else 0
```

#### `GenLimit.KM.SetInterface.fresh`

```lean
noncomputable def GenLimit.KM.SetInterface.fresh
    (O : OracleFamily) (S : Finset ℕ) (i : ℕ) : ℕ := by
  classical
  exact Nat.find ((O.infinite' i).exists_notMem_finset S)
```

#### `GenLimit.KM.SetInterface.generator`

```lean
noncomputable def GenLimit.KM.SetInterface.generator
    (O : OracleFamily) (S : Finset ℕ) : ℕ :=
  fresh O S (focus O.language S)
```

#### `GenLimit.KM.SetInterface.GeneratesFromObservedSet`

```lean
def GenLimit.KM.SetInterface.GeneratesFromObservedSet
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    generator O (sample stream t) ∈ O.language z ∧
      generator O (sample stream t) ∉ sample stream t
```

### 16.2 All 69 target-specific theorem declarations

#### `GenLimit.critical_subset_of_le`

```lean
theorem GenLimit.critical_subset_of_le
    {C : LanguageFamily} {stream : ℕ → ℕ} {t i j : ℕ}
    (hij : i ≤ j) (hi : Critical C stream t i)
    (hj : Critical C stream t j) : C j ⊆ C i
```

#### `GenLimit.least_consistent_critical`

```lean
theorem GenLimit.least_consistent_critical
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ}
    (hn : Consistent C stream t n)
    (hleast : ∀ i, i < n → ¬ Consistent C stream t i) :
    Critical C stream t n
```

#### `GenLimit.bad_earlier_eventually_inconsistent`

```lean
theorem GenLimit.bad_earlier_eventually_inconsistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i < z →
      ¬ C z ⊆ C i → ¬ Consistent C stream t i
```

#### `GenLimit.target_eventually_critical`

```lean
theorem GenLimit.target_eventually_critical
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    ∃ T, ∀ t, T ≤ t → Critical C stream t z
```

#### `GenLimit.OracleFamily.ArxivV1.mem_eligible`

```lean
@[simp] theorem GenLimit.OracleFamily.ArxivV1.mem_eligible
    {stream : ℕ → ℕ} {t q u : ℕ} (h : O.HasConsistent stream t) :
    u ∈ eligible O stream t h q ↔
      u ∈ O.finitePrefix (O.selected stream t q h) q ∧
        u ∉ sample stream t
```

#### `GenLimit.OracleFamily.ArxivV1.hasFreshEligible_exists`

```lean
theorem GenLimit.OracleFamily.ArxivV1.hasFreshEligible_exists
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    ∃ q, b < q ∧ HasFreshEligible O stream t h q
```

#### `GenLimit.OracleFamily.ArxivV1.roundCounter_spec`

```lean
theorem GenLimit.OracleFamily.ArxivV1.roundCounter_spec
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    b < roundCounter O stream t h b ∧
      HasFreshEligible O stream t h (roundCounter O stream t h b)
```

#### `GenLimit.OracleFamily.ArxivV1.roundCounter_gt`

```lean
theorem GenLimit.OracleFamily.ArxivV1.roundCounter_gt
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    b < roundCounter O stream t h b
```

#### `GenLimit.OracleFamily.ArxivV1.roundCounter_le_of_freshEligible`

```lean
theorem GenLimit.OracleFamily.ArxivV1.roundCounter_le_of_freshEligible
    {stream : ℕ → ℕ} {t q : ℕ} (h : O.HasConsistent stream t) (b : ℕ)
    (hbq : b < q) (hq : HasFreshEligible O stream t h q) :
    roundCounter O stream t h b ≤ q
```

#### `GenLimit.OracleFamily.ArxivV1.roundOutput_mem_eligible`

```lean
theorem GenLimit.OracleFamily.ArxivV1.roundOutput_mem_eligible
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    roundOutput O stream t h b ∈
      eligible O stream t h (roundCounter O stream t h b)
```

#### `GenLimit.OracleFamily.ArxivV1.roundOutput_le_of_mem`

```lean
theorem GenLimit.OracleFamily.ArxivV1.roundOutput_le_of_mem
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b u : ℕ)
    (hu : u ∈ eligible O stream t h (roundCounter O stream t h b)) :
    roundOutput O stream t h b ≤ u
```

#### `GenLimit.OracleFamily.ArxivV1.roundOutput_spec`

```lean
theorem GenLimit.OracleFamily.ArxivV1.roundOutput_spec
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    roundOutput O stream t h b ∈
        O.finitePrefix
          (O.selected stream t (roundCounter O stream t h b) h)
          (roundCounter O stream t h b) ∧
      roundOutput O stream t h b ∉ sample stream t ∧
      ∀ u, u ∈
          O.finitePrefix
            (O.selected stream t (roundCounter O stream t h b) h)
            (roundCounter O stream t h b) →
        u ∉ sample stream t →
          roundOutput O stream t h b ≤ u
```

#### `GenLimit.OracleFamily.ArxivV1.processRound_counter_ge_start`

```lean
theorem GenLimit.OracleFamily.ArxivV1.processRound_counter_ge_start
    (stream : ℕ → ℕ) (t b : ℕ) :
    b ≤ (processRound O stream t b).counter
```

#### `GenLimit.OracleFamily.ArxivV1.processRound_of_hasConsistent`

```lean
theorem GenLimit.OracleFamily.ArxivV1.processRound_of_hasConsistent
    {stream : ℕ → ℕ} {t b : ℕ} (h : O.HasConsistent stream t) :
    processRound O stream t b =
      ⟨roundCounter O stream t h b, roundOutput O stream t h b⟩
```

#### `GenLimit.OracleFamily.ArxivV1.run_succ_counter_ge_start`

```lean
theorem GenLimit.OracleFamily.ArxivV1.run_succ_counter_ge_start
    (stream : ℕ → ℕ) (t : ℕ) :
    max (run O stream t).counter (stream t + 1) ≤
      (run O stream (t + 1)).counter
```

#### `GenLimit.OracleFamily.ArxivV1.run_counter_bounds`

```lean
theorem GenLimit.OracleFamily.ArxivV1.run_counter_bounds
    {stream : ℕ → ℕ} :
    ∀ {t k}, k < t → stream k < (run O stream t).counter
```

#### `GenLimit.OracleFamily.ArxivV1.sample_lt_runCounter`

```lean
theorem GenLimit.OracleFamily.ArxivV1.sample_lt_runCounter
    {stream : ℕ → ℕ} {t u : ℕ} (hu : u ∈ sample stream t) :
    u < (run O stream t).counter
```

#### `GenLimit.OracleFamily.ArxivV1.run_round_spec`

```lean
theorem GenLimit.OracleFamily.ArxivV1.run_round_spec
    {stream : ℕ → ℕ} {t : ℕ} (ht : 0 < t)
    (h : O.HasConsistent stream t) :
    ∃ n,
      n < t ∧
      FinitelyCritical O.language stream t (run O stream t).counter n ∧
      (∀ j, j < t →
        FinitelyCritical O.language stream t (run O stream t).counter j →
        j ≤ n) ∧
      (run O stream t).output ∈
        O.finitePrefix n (run O stream t).counter ∧
      (run O stream t).output ∉ sample stream t ∧
      (∀ u, u ∈ O.finitePrefix n (run O stream t).counter →
        u ∉ sample stream t →
          (run O stream t).output ≤ u)
```

#### `GenLimit.OracleFamily.ArxivV1.eventual_correctness`

```lean
theorem GenLimit.OracleFamily.ArxivV1.eventual_correctness
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    GeneratesInLimit O stream z
```

#### `GenLimit.OracleFamily.ArxivV1.kleinbergMullainathan_main`

```lean
theorem GenLimit.OracleFamily.ArxivV1.kleinbergMullainathan_main
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    GeneratesInLimit O stream z
```

#### `GenLimit.critical_finitelyCritical`

```lean
theorem GenLimit.critical_finitelyCritical
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ}
    (h : Critical C stream t n) (m : ℕ) :
    FinitelyCritical C stream t m n
```

#### `GenLimit.finitelyCritical_cutoff_mono`

```lean
theorem GenLimit.finitelyCritical_cutoff_mono
    {C : LanguageFamily} {stream : ℕ → ℕ} {t m m' n : ℕ}
    (hmm' : m' ≤ m) (h : FinitelyCritical C stream t m n) :
    FinitelyCritical C stream t m' n
```

#### `GenLimit.finitelyCritical_prefix_subset`

```lean
theorem GenLimit.finitelyCritical_prefix_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {t m i j : ℕ}
    (hij : i ≤ j)
    (hi : FinitelyCritical C stream t m i)
    (hj : FinitelyCritical C stream t m j) :
    ∀ u, u < m → u ∈ C j → u ∈ C i
```

#### `GenLimit.least_consistent_finitelyCritical`

```lean
theorem GenLimit.least_consistent_finitelyCritical
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ}
    (hn : Consistent C stream t n)
    (hleast : ∀ i, i < n → ¬ Consistent C stream t i) (m : ℕ) :
    FinitelyCritical C stream t m n
```

#### `GenLimit.target_eventually_finitelyCritical`

```lean
theorem GenLimit.target_eventually_finitelyCritical
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z)) :
    ∃ T, ∀ t, T ≤ t → ∀ m, FinitelyCritical C stream t m z
```

#### `GenLimit.OracleFamily.processRound_counter_ge_start`

```lean
theorem GenLimit.OracleFamily.processRound_counter_ge_start
    (stream : ℕ → ℕ) (t b : ℕ) :
    b ≤ (O.processRound stream t b).counter
```

#### `GenLimit.OracleFamily.processRound_of_hasConsistent`

```lean
theorem GenLimit.OracleFamily.processRound_of_hasConsistent
    {stream : ℕ → ℕ} {t b : ℕ} (h : O.HasConsistent stream t) :
    O.processRound stream t b =
      ⟨O.roundCounter stream t h b,
        O.roundCounter stream t h b - 1⟩
```

#### `GenLimit.OracleFamily.run_succ_counter_ge_start`

```lean
theorem GenLimit.OracleFamily.run_succ_counter_ge_start
    (stream : ℕ → ℕ) (t : ℕ) :
    max (O.run stream t).counter (stream t + 1) ≤
      (O.run stream (t + 1)).counter
```

#### `GenLimit.OracleFamily.run_counter_bounds`

```lean
theorem GenLimit.OracleFamily.run_counter_bounds
    {stream : ℕ → ℕ} :
    ∀ {t k}, k < t → stream k < (O.run stream t).counter
```

#### `GenLimit.OracleFamily.sample_lt_roundStart`

```lean
theorem GenLimit.OracleFamily.sample_lt_roundStart
    {stream : ℕ → ℕ} {t u : ℕ} (hu : u ∈ sample stream (t + 1)) :
    u < max (O.run stream t).counter (stream t + 1)
```

#### `GenLimit.OracleFamily.run_round_spec`

```lean
theorem GenLimit.OracleFamily.run_round_spec
    {stream : ℕ → ℕ} {t : ℕ} (ht : 0 < t)
    (h : O.HasConsistent stream t) :
    ∃ n,
      n < t ∧
      FinitelyCritical O.language stream t (O.run stream t).counter n ∧
      (∀ j, j < t →
        FinitelyCritical O.language stream t (O.run stream t).counter j →
        j ≤ n) ∧
      (O.run stream t).output ∈
        O.finitePrefix n (O.run stream t).counter ∧
      (O.run stream t).output ∉ sample stream t
```

#### `GenLimit.OracleFamily.eventual_correctness`

```lean
theorem GenLimit.OracleFamily.eventual_correctness
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    O.GeneratesInLimit stream z
```

#### `GenLimit.OracleFamily.kleinbergMullainathan_main`

```lean
theorem GenLimit.OracleFamily.kleinbergMullainathan_main
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    O.GeneratesInLimit stream z
```

#### `GenLimit.OracleFamily.mem_finitePrefix`

```lean
@[simp] theorem GenLimit.OracleFamily.mem_finitePrefix {i m u : ℕ} :
    u ∈ O.finitePrefix i m ↔ u < m ∧ u ∈ O.language i
```

#### `GenLimit.OracleFamily.consistentAt_iff`

```lean
theorem GenLimit.OracleFamily.consistentAt_iff {stream : ℕ → ℕ} {t i : ℕ} :
    O.ConsistentAt stream t i ↔
      Consistent O.language stream t i
```

#### `GenLimit.OracleFamily.finitelyCriticalAt_iff`

```lean
theorem GenLimit.OracleFamily.finitelyCriticalAt_iff
    {stream : ℕ → ℕ} {t m n : ℕ} :
    O.FinitelyCriticalAt stream t m n ↔
      FinitelyCritical O.language stream t m n
```

#### `GenLimit.OracleFamily.stop_exists`

```lean
theorem GenLimit.OracleFamily.stop_exists
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    ∃ q, b < q ∧ O.Stop stream t h q
```

#### `GenLimit.OracleFamily.roundCounter_spec`

```lean
theorem GenLimit.OracleFamily.roundCounter_spec
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    b < O.roundCounter stream t h b ∧
      O.Stop stream t h (O.roundCounter stream t h b)
```

#### `GenLimit.OracleFamily.roundCounter_gt`

```lean
theorem GenLimit.OracleFamily.roundCounter_gt
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    b < O.roundCounter stream t h b
```

#### `GenLimit.OracleFamily.roundCounter_output_mem_selectedPrefix`

```lean
theorem GenLimit.OracleFamily.roundCounter_output_mem_selectedPrefix
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) (b : ℕ) :
    O.roundCounter stream t h b - 1 ∈
      O.finitePrefix
        (O.selected stream t (O.roundCounter stream t h b) h)
        (O.roundCounter stream t h b)
```

#### `GenLimit.OracleFamily.mem_consistentCandidates`

```lean
@[simp] theorem GenLimit.OracleFamily.mem_consistentCandidates
    {stream : ℕ → ℕ} {t i : ℕ} :
    i ∈ O.consistentCandidates stream t ↔
      i < t ∧ O.ConsistentAt stream t i
```

#### `GenLimit.OracleFamily.mem_criticalCandidates`

```lean
@[simp] theorem GenLimit.OracleFamily.mem_criticalCandidates
    {stream : ℕ → ℕ} {t m n : ℕ} :
    n ∈ O.criticalCandidates stream t m ↔
      n < t ∧ O.FinitelyCriticalAt stream t m n
```

#### `GenLimit.OracleFamily.criticalCandidates_nonempty`

```lean
theorem GenLimit.OracleFamily.criticalCandidates_nonempty
    {stream : ℕ → ℕ} {t : ℕ}
    (h : O.HasConsistent stream t) (m : ℕ) :
    (O.criticalCandidates stream t m).Nonempty
```

#### `GenLimit.OracleFamily.selected_mem`

```lean
theorem GenLimit.OracleFamily.selected_mem
    {stream : ℕ → ℕ} {t m : ℕ} (h : O.HasConsistent stream t) :
    O.selected stream t m h ∈ O.criticalCandidates stream t m
```

#### `GenLimit.OracleFamily.selected_lt`

```lean
theorem GenLimit.OracleFamily.selected_lt
    {stream : ℕ → ℕ} {t m : ℕ} (h : O.HasConsistent stream t) :
    O.selected stream t m h < t
```

#### `GenLimit.OracleFamily.selected_finitelyCriticalAt`

```lean
theorem GenLimit.OracleFamily.selected_finitelyCriticalAt
    {stream : ℕ → ℕ} {t m : ℕ} (h : O.HasConsistent stream t) :
    O.FinitelyCriticalAt stream t m (O.selected stream t m h)
```

#### `GenLimit.OracleFamily.selected_finitelyCritical`

```lean
theorem GenLimit.OracleFamily.selected_finitelyCritical
    {stream : ℕ → ℕ} {t m : ℕ} (h : O.HasConsistent stream t) :
    FinitelyCritical O.language stream t m (O.selected stream t m h)
```

#### `GenLimit.OracleFamily.selected_max`

```lean
theorem GenLimit.OracleFamily.selected_max
    {stream : ℕ → ℕ} {t m n : ℕ} (h : O.HasConsistent stream t)
    (hnt : n < t) (hn : O.FinitelyCriticalAt stream t m n) :
    n ≤ O.selected stream t m h
```

#### `GenLimit.OracleFamily.selected_antitone`

```lean
theorem GenLimit.OracleFamily.selected_antitone
    {stream : ℕ → ℕ} {t m m' : ℕ} (h : O.HasConsistent stream t)
    (hmm' : m ≤ m') :
    O.selected stream t m' h ≤ O.selected stream t m h
```

#### `GenLimit.OracleFamily.antitone_nat_eventually_constant`

```lean
theorem GenLimit.OracleFamily.antitone_nat_eventually_constant
    (f : ℕ → ℕ) (hf : Antitone f) :
    ∃ M, ∀ m, M ≤ m → f m = f M
```

#### `GenLimit.OracleFamily.selected_eventually_constant`

```lean
theorem GenLimit.OracleFamily.selected_eventually_constant
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t) :
    ∃ M, ∀ m, M ≤ m →
      O.selected stream t m h = O.selected stream t M h
```

#### `GenLimit.KM.Semantic.mem_criticalIndices`

```lean
@[simp] theorem GenLimit.KM.Semantic.mem_criticalIndices
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ} :
    n ∈ criticalIndices C stream t ↔ n < t ∧ Critical C stream t n
```

#### `GenLimit.KM.Semantic.focus_spec`

```lean
theorem GenLimit.KM.Semantic.focus_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {t z : ℕ}
    (hzt : z < t) (hz : Critical C stream t z) :
    focus C stream t < t ∧
      Critical C stream t (focus C stream t) ∧
      z ≤ focus C stream t
```

#### `GenLimit.KM.Semantic.fresh_spec`

```lean
theorem GenLimit.KM.Semantic.fresh_spec
    (O : OracleFamily) (stream : ℕ → ℕ) (t i : ℕ) :
    fresh O stream t i ∈ O.language i ∧
      fresh O stream t i ∉ sample stream t
```

#### `GenLimit.KM.Semantic.fresh_le_of_mem_of_not_mem_sample`

```lean
theorem GenLimit.KM.Semantic.fresh_le_of_mem_of_not_mem_sample
    (O : OracleFamily) (stream : ℕ → ℕ) (t i x : ℕ)
    (hxLanguage : x ∈ O.language i)
    (hxFresh : x ∉ sample stream t) :
    fresh O stream t i ≤ x
```

#### `GenLimit.KM.Semantic.generator_spec`

```lean
theorem GenLimit.KM.Semantic.generator_spec
    (O : OracleFamily) (stream : ℕ → ℕ) (t : ℕ) :
    generator O stream t ∈ O.language (focus O.language stream t) ∧
      generator O stream t ∉ sample stream t
```

#### `GenLimit.KM.Semantic.generator_le_of_mem_focus_of_not_mem_sample`

```lean
theorem GenLimit.KM.Semantic.generator_le_of_mem_focus_of_not_mem_sample
    (O : OracleFamily) (stream : ℕ → ℕ) (t x : ℕ)
    (hxFocus : x ∈ O.language (focus O.language stream t))
    (hxFresh : x ∉ sample stream t) :
    generator O stream t ≤ x
```

#### `GenLimit.KM.Semantic.kleinbergMullainathan_main`

```lean
theorem GenLimit.KM.Semantic.kleinbergMullainathan_main
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    GeneratesInLimit O stream z
```

#### `GenLimit.KM.SetInterface.consistentOn_sample_iff`

```lean
@[simp] theorem GenLimit.KM.SetInterface.consistentOn_sample_iff
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ} :
    ConsistentOn C (sample stream t) n ↔ Consistent C stream t n
```

#### `GenLimit.KM.SetInterface.criticalOn_sample_iff`

```lean
@[simp] theorem GenLimit.KM.SetInterface.criticalOn_sample_iff
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ} :
    CriticalOn C (sample stream t) n ↔ Critical C stream t n
```

#### `GenLimit.KM.SetInterface.criticalOn_subset_of_le`

```lean
theorem GenLimit.KM.SetInterface.criticalOn_subset_of_le
    {C : LanguageFamily} {S : Finset ℕ} {i j : ℕ}
    (hij : i ≤ j) (hi : CriticalOn C S i)
    (hj : CriticalOn C S j) :
    C j ⊆ C i
```

#### `GenLimit.KM.SetInterface.mem_criticalIndices`

```lean
@[simp] theorem GenLimit.KM.SetInterface.mem_criticalIndices
    {C : LanguageFamily} {S : Finset ℕ} {n : ℕ} :
    n ∈ criticalIndices C S ↔ n < S.card ∧ CriticalOn C S n
```

#### `GenLimit.KM.SetInterface.focus_spec`

```lean
theorem GenLimit.KM.SetInterface.focus_spec
    {C : LanguageFamily} {S : Finset ℕ} {z : ℕ}
    (hzScope : z < S.card) (hz : CriticalOn C S z) :
    focus C S < S.card ∧
      CriticalOn C S (focus C S) ∧
      z ≤ focus C S
```

#### `GenLimit.KM.SetInterface.fresh_spec`

```lean
theorem GenLimit.KM.SetInterface.fresh_spec
    (O : OracleFamily) (S : Finset ℕ) (i : ℕ) :
    fresh O S i ∈ O.language i ∧ fresh O S i ∉ S
```

#### `GenLimit.KM.SetInterface.generator_spec`

```lean
theorem GenLimit.KM.SetInterface.generator_spec
    (O : OracleFamily) (S : Finset ℕ) :
    generator O S ∈ O.language (focus O.language S) ∧
      generator O S ∉ S
```

#### `GenLimit.KM.SetInterface.sample_card_of_injective`

```lean
theorem GenLimit.KM.SetInterface.sample_card_of_injective
    (stream : ℕ → ℕ) (hinjective : Function.Injective stream) (t : ℕ) :
    (sample stream t).card = t
```

#### `GenLimit.KM.SetInterface.eventually_target_below_sample_card`

```lean
theorem GenLimit.KM.SetInterface.eventually_target_below_sample_card
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    ∃ T, ∀ t, T ≤ t → z < (sample stream t).card
```

#### `GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface`

```lean
theorem GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z))
    (hinjective : Function.Injective stream) :
    GeneratesFromObservedSet O stream z
```

#### `GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface_with_repetitions`

```lean
theorem GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface_with_repetitions
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    GeneratesFromObservedSet O stream z
```

### 16.3 Public decidability-instance signatures

```lean
variable (O : GenLimit.OracleFamily)

instance GenLimit.OracleFamily.consistentAtDecidable
    (stream : ℕ → ℕ) (t i : ℕ) :
    Decidable (O.ConsistentAt stream t i)

instance GenLimit.OracleFamily.finitelyCriticalAtDecidable
    (stream : ℕ → ℕ) (t m n : ℕ) :
    Decidable (O.FinitelyCriticalAt stream t m n)

instance GenLimit.OracleFamily.hasConsistentDecidable
    (stream : ℕ → ℕ) (t : ℕ) :
    Decidable (O.HasConsistent stream t)

instance GenLimit.OracleFamily.stopDecidable
    (stream : ℕ → ℕ) (t : ℕ)
    (h : O.HasConsistent stream t) (q : ℕ) :
    Decidable (O.Stop stream t h q)

instance GenLimit.OracleFamily.ArxivV1.hasFreshEligibleDecidable
    (stream : ℕ → ℕ) (t : ℕ)
    (h : O.HasConsistent stream t) (q : ℕ) :
    Decidable (GenLimit.OracleFamily.ArxivV1.HasFreshEligible O stream t h q)
```

### 16.4 Source-visible structure signatures

```lean
structure GenLimit.OracleFamily.MachineState where
  counter : ℕ
  output : ℕ

structure GenLimit.OracleFamily.ArxivV1.MachineState where
  counter : ℕ
  output : ℕ
```

These structures are data interfaces. This source-only audit does not inventory elaborator-generated recursors, projections beyond the displayed fields, or proof-body dependencies.

## 17. Compact verdict table

| Version/result | Correspondence verdict | Difficulty verdict | Bottom line |
|---|---|---|---|
| NeurIPS (2.1)/(5.7) | Faithful specialization | Preserved | Faithful endpoint-algorithm formalization over `ℕ`; no target access or conclusion-smuggling. |
| arXiv-v1 (2.1)/(5.7) | Faithful specialization | Preserved | Faithful first-fresh-eligible formalization over `ℕ`; version-specific stopping rule preserved. |
| Literal finite-set theorem (4.1), both versions | Faithful specialization | Preserved | Faithfully realized by the repetition-tolerant set-interface repair. |
| Round-dependent semantic construction as a formalization of literal (4.1) | Related but materially different | Weakened / easier | Mirrors (4.5) but receives elapsed time separately. |
| Finite-family theorem (2.2), both versions | Not represented in Lean | Indeterminate | Major omission. |
| Robust prompted theorem (7.1), both versions | Not represented in Lean | Indeterminate | Major omission. |
| arXiv-v1 non-trivial prompt theorem (7.5)/(7.6) | Not represented in Lean | Indeterminate | Major arXiv-specific omission. |
| arXiv-v1 finite-family prompted impossibility | Not represented in Lean | Indeterminate | Omitted negative result. |
| Proceedings printed (5.6) versus formal round invariant | Related but materially different | Indeterminate | Formal statement repairs hypotheses and strengthens the conclusion. |
| arXiv-v1 (5.6) versus formal round invariant | Faithful generalization | Strengthened / harder | Adds explicit freshness, maximality, and leastness. |

### Overall verdict for the NeurIPS proceedings version

**Faithful for the central countable unprompted theorem and its criticality/finite-query mechanism, but materially incomplete for the proceedings paper as a whole.** The main represented theorem preserves the model, access restrictions, quantifier order, and mathematical difficulty, subject to the fixed-`ℕ` specialization. The literal finite-set theorem is recovered by a genuine repair. However, the second main theorem (2.2) and the robust-prompt theorem (7.1) are not formalized.

### Overall verdict for arXiv v1

**Faithful and version-correct for the central unprompted Sections 4–5 result, but even more materially incomplete for the full arXiv-v1 paper.** The separate first-fresh-eligible machine matches arXiv v1 rather than the proceedings algorithm, and its difficulty is preserved. The formalization omits (2.2), robust prompts, regular-subset-query/non-trivial prompts, the context-free corollary, and the finite-family prompted impossibility.

### Executive summary for the consolidated 36-paper audit

Paper 01's Lean source faithfully captures the core theorem that every membership-oracle-indexed countable family of infinite languages over `ℕ` admits eventual fresh generation from any exact positive presentation, and it separately tracks the distinct NeurIPS and arXiv-v1 finite-query stopping rules. The main formal theorem is not trivialized: the generator has no target index, target oracle, feedback, or supplied convergence witness. Lean also repairs the papers' mismatch between a finite-set-only function statement and a time-dependent construction by providing a cardinality-scope finite-set generator. Coverage is nevertheless incomplete: the finite-family uniform theorem and all prompted-generation results are absent, including arXiv v1's stronger regular-subset-query theorem and prompted impossibility result.
