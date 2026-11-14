# P27 — independent Stage 2 statement comparison

**Result.** The main feedback characterizations and their two explicit union and zero-example corollaries agree at the level of semantic guarantees. Several native generators use different constructions. No-feedback coverage is partial: the equivalence retains a substantive self-locking assumption, a separate target contradicts source Lemma A.8, and two of the five inner-cover boundary assertions have no matching inspected native endpoint.

**Identity and isolation.** The source is *Language Generation with Feedback: Queries and Mistakes*, Hanneke–Karbasi–Mehrotra–Velegkas, pinned ICML 2026 OpenReview jvfXyIcQ8a. Original PDF SHA-256: `e3467ab76be2eae001490a43e461865d2c704633e2656bd05ff2eb477b4b1319`; PDF creation metadata is 2026-06-05. No edition was substituted. Printed/PDF page numbers agree on the reviewed pages. The annotation-free viewing derivative has its own hash in the run record.

The independent [source inventory](source-inventory.md) was completed at 07:45:56 UTC and frozen at 07:46:34 UTC, before this comparison first consulted Stage 1 at approximately 07:46:57 UTC. Its JSON hash is `dd9da8cf5c8c6c09ff1df7e28e34b235cb2d0b17672e44d62a6cea872309b87f`. Stage 1 was already frozen at 07:37:25 UTC. Both freezes were checked and preserved. The interface snapshot identifies hash `e56b617a39899cb9acfd94b61e19680934bf78aa1f40d8d07d8e7f1d10bee1fc`; no Git state was inspected.

The [ten-row comparison JSON](stage2-claims.json) preserves every source component, assumption, classification and declaration anchor. Exact types and definition values were rechecked directly; all 134 recursive record types match their native census counterparts. All 1,457 census records were searched for relevant supporting interfaces, without claiming individual interpretation of every helper. Theorem proof bodies, raw Lean comments, owner explanations and later-stage context remained excluded.

## Common mathematical boundary

The source's languages are infinite subsets of a countable ordered universe. An ordinary presentation contains exactly the target's elements, exhaustively, with repetitions permitted. Lean's `Presents` is range equality. Lists and finite tuples preserve the full sample order; finite sets retain only the seen values.

One strategy precedes every target and permitted run; a finite eventual correctness time may depend on the run. Freshness excludes seen samples, and generally does not exclude prior generated outputs. Infinite-set outputs remain infinite before stabilization. Nat-indexed infinite cover members need not belong to the target class; repeated members are allowed. Finite cover size zero forces an empty class.

The universal feedback endpoints explicitly assume `Countable α`, `Infinite α` and that all target languages are infinite. The last condition matches the source convention. Ambient infinitude follows from any nonempty source collection; the explicit `Infinite α` excludes only the literal finite-universe/empty-collection edge of the source's phrase “arbitrary countable universe.” The matrix labels that boundary as faithful specialization; the substantive assertions agree on the intended infinite universe.

These are deterministic functions and arbitrary sets. Classical choices, rank selection, membership-bit equations and existential strategies supply no effective program, decidable target or cover representation, executable infinite output, uniform convergence rate, loss bound or probability guarantee.

**Timing checked directly.** Ordinary mistake output on a nonempty history of length n sees n−1 earlier feedback bits; the current bit arrives afterward and tests membership in K minus the current seen set. Set mistake feedback tests only the canonical first point, while success tests the whole set. Queries receive one membership answer before the current output; zero-based round t sees t+1 samples and t+1 answers at output. Extra empty-history values and the n versus t+1 indexing do not change eventual correctness. Zero-example games have no sample stream. Noisy games use the observed interaction, with an unknown eventual-feedback cutoff distinct from the success cutoff.

## Comparison matrix

“R” refers to [stage1/declarations.jsonl](../stage1/declarations.jsonl); “N” refers to [the native census](../stage1/native-declaration-census.jsonl). Numbers are one-based record/line numbers.

| Slot | Source location, printed = PDF | Registered target records | Correspondence and material scope |
|---|---|---|---|
| C01 | Thm. 3.1 p.6; A.1 pp.11–12 | R29 | Faithful specialization at the ambient boundary above; matching element-mistake characterization, locking-existence lemma and cover algorithm. |
| C02 | Thm. 3.2 p.6; A.1 pp.11–12 | R33 | Same boundary specialization; matching first-element feedback and element/set existence equivalence. |
| C03 | Thm. 3.3 p.6; A.2.2 pp.14–15 | R34 | Equivalent separation with a named all-infinite native three-point witness. Concrete fresh-block rule differs; source query nonrepetition is not preserved. |
| C04 | Thm. 3.4 p.6; A.2.1 pp.13–14 | R35 | Same boundary specialization; equivalent characterization with a different scheduled-query construction. |
| C05 | Cor. 3.6 p.7; A.2–A.3 pp.15–16 | R26 | Same boundary specialization; both countable-union implications covered. Adjacent product remark has no located native endpoint. |
| C06 | Cor. 3.7 p.7; A.4–A.5 pp.16–18 | R27 | Partial full-context coverage: both main implications match, concrete algorithms differ, and the adjacent zero-example set-mistake extension lacks a corresponding interface. |
| C07 | Cor. 3.8 p.8; A.6–A.7 pp.18–22 | R28 | Faithful generalization of the inherited formal presentation model to arbitrary sample streams, matching the broader prose. Both characterizations covered; finite expansion is replaced. |
| C08 | Thm. 3.9 p.8; A.6.1 pp.22–23 | R37–38 | Partial: unconditional set-to-element implication and conditional iff. The extra self-locking premise cannot be dropped. |
| C09 | Lemma A.8 p.23 | R36 | Substantively different: a same-witness counterexample to the positive source lemma; source-correction evidence, not a positive formalization. |
| C10 | Thm. 3.10 p.8; A.9–A.13 pp.24–25 | R30–32 | Partial: A.9, A.12 and A.13 covered; unconditional A.10 and nongenerable countably covered A.11 not located. |

## Component and algorithm comparison

**C01.** R29 has the same strategy/target/presentation/threshold quantifier order and countable-cover containment. N209 matches Lemma A.1: some nonempty target-valued history locks every finite target-valued tail. It does not require that history to prefix every enumeration. N392/397/400 implement forced-positive self-simulation. N370 enumerates all finite sample/bit-list pairs, including malformed pairs, and replaces finite ranges by the universe rather than filtering them out; extra cover candidates are harmless. N239 selects the minimum-rank unseen point of the cover member indexed by the number of prior negative bits. Zero-based cover indexing and the classically chosen finite-predecessor rank preserve the source construction.

**C02.** N249 outputs that same cover member minus all seen sample values. N423 takes a set strategy's canonical first point. N251–255 tie representative strategy, feedback and output statements to these exact named strategies. Thus neither matching a representative bit nor changing output mode is mistaken for an oracle certifying an entire infinite set.

**C03.** The existential facade does not itself say its class is all-infinite. N485–490 define the three-point class and give infinitude and both separating properties for that same class; N276 says it has no countable inner cover. N469/473/474 supply distinct-block diagonal witnesses belonging to each cover candidate and excluded from the diagonal language. This recovers the source's intended infinite-language witness without identifying an existential witness through a proof body.

The block encoding uses Nat ≃ Nat × Fin 3, equivalent to the source's positive-integer blocks after reindexing. N480 queries position 0 and outputs position 1 or 2 according to the current bit. N479's output equation, N465's all-round freshness and the language definition support the source's first-round validity by same-witness interface assembly. However, N484 chooses a block above the maximum sampled block; source instead tracks its last used block and chooses a later unseen block. Repeated samples can therefore cause repeated native queries. This loses the source implementation's auxiliary nonrepetition property while preserving its separation theorem.

**C04.** N165 indexes output sets by the round, sample tuple and well-formed answer list, matching countable-range necessity. The sufficient strategy N248 differs from the displayed source algorithm: N233 queries a fixed fair enumeration of cover-row/point pairs via Nat.unpair, and N211 chooses the least passing row among those currently eligible. It then deletes current sample values. Source queries the least unseen point in the active phase, counts negative answers, and branches on the current answer between C_i and C_(i+1). These are different semantic constructions for the same one-query theorem; literal algorithm correspondence is not claimed.

**C05.** R26's two conjuncts match Corollary 3.6 and both Corollaries A.2–A.3. N797 constructs the union cover by pairing the collection and within-cover indices; N223 states its covering property. The corresponding set-mistake union result can be assembled from R26 and the set/element equivalence R33 on those same classes. The learner is not given a hidden collection index, and no effective family of generators is assumed. No matching product-cover endpoint was located for the neighboring Section 3.4.1 Cartesian-product remark; that ancillary gap is separate from coverage of the named union corollaries.

**C06.** R27 and N156–157 match the two explicit zero-example implications. The predicates receive only feedback and require eventual membership or infinite-set containment in K. They impose no cross-round novelty, consistently with S_n being empty.

The native element strategy N256 repeatedly uses enumeration point 0 of the cover member indexed by negative replies; it may settle at one positive representative without that whole cover member being contained in K. Source A.4 excludes all prior outputs and traverses candidates. N259 instead uses the fixed query schedule and emits the least passing whole cover row; source A.5 tracks queries within its active phase and deletes them from positive outputs. These changes preserve the theorem goals but not the displayed algorithms.

The A.4 context also says the zero-example set-mistake conclusion follows by equivalence. The census has no corresponding zero-example set-mistake predicate/endpoint. Ordinary presentation-based R33 is insufficient evidence for that separately modified zero-example game. A source question also remains: A.4's global prior-output memory can already contain a later candidate's least negative point, so its claimed stabilization at the least fully contained candidate is stronger than the eventual-validity goal.

**C07.** R28 contains both equivalences. R6/R10 universally quantify arbitrary sample streams and observed feedback streams, with no presentation assumption. That strengthens the literal inherited source Definitions 6–7 and matches the surrounding arbitrary-contamination motivation. Correctness after an unknown cutoff is an implication premise about the actual strategy driven by observed earlier bits. Mistake output precedes its current bit; query-set output sees it. No noise distribution or bound on the cutoff is added.

The native constructions replace source finite expansion and repaired targets. N810 repeats each original cover member at infinitely many paired indices. N325 certifies the ordinary cover element strategy on that repeated cover under eventual feedback; it does not exclude its own earlier outputs. N197/326 use scheduled queries on repeated rows and delete every queried point through the current round, together with samples, from the chosen passing row. Queries can repeat. The source's finite-perturbation sets, nonrepeating interaction and exact repaired-target reduction are not literal native constructions. This is an alternative robust construction, not a mismatch in the oracle guarantee.

**C08.** R38 unconditionally supplies set-to-element generation, even over arbitrary types, faithfully generalizing the source domain. R37 assumes that **every successful element generator on the class has its freshened generator self-lock along every presentation**, then concludes the iff. This substantive premise is absent from source Theorem 3.9.

Native freshening R80 keeps a fresh output or chooses an arbitrary unseen universe point; source chooses the canonical least. N334/346/351 define the same recursive own-output set construction. N337 asserts its infinitude from everywhere-freshness, and N335–336 assert correctness under a locking hypothesis. The conditional theorem also permits arbitrary infinite types with decidable equality, beyond countable types; that universe generalization and its stronger locking premise are opposing changes. Neither erasing the premise nor imposing a total stronger/weaker ordering is justified. Failure of the source's locking proof does not establish that unconditional Theorem 3.9 itself is false.

**C09.** R36 states four facts together for one named generator: success on its singleton target class, everywhere freshness, a valid base presentation, and no self-locking prefix of that presentation. R25 gives infinitude of that same target. The universe is Nat + Nat; the target is all left-summand points; the presentation enumerates them in order. The generator emits a right-summand point exactly on full ordered spike histories [inl 0,…,inl(n−1),inl(n+1)] and otherwise chooses a fresh target point.

This is counterevidence to the source's universal actual-prefix lemma. Everywhere freshness means the source's preceding freshening operation preserves this generator's values. It does not contradict Lemma A.1's weaker existence of some locking history. The independent source inventory already flagged p.23's unjustified nesting step: an actual prefix of a fixed ordered enumeration need not extend an arbitrary error-forcing continuation appended earlier. Stage 3 should adjudicate the source formulation; no theorem proof or human certification is offered here.

**C10.** All five parts are distinguished:

- **A.9:** R31 states finite inner cover ⇒ ordinary element generability. Countable and nonempty ambient type are explicit; target infinitude follows from cover containment. A zero-sized finite cover handles the empty class. Source's finite-union proof machinery is outside this statement audit.
- **A.10:** No unconditional native interface states ordinary generability ⇒ countable inner cover. Generic cover machinery and C08's conditional conversion do not supply that missing unconditional assembly.
- **A.11:** No native class was found combining a countable inner cover with failure of ordinary generation. C09 is a successful generator without self-locking, so it cannot replace this nongenerable example.
- **A.12:** R30 has all-infinite, generable and countably covered together. N158 additionally matches the source proof's general fact for any countable all-infinite class.
- **A.13:** R32 has all-infinite, generable and no finite cover together. N504–508 supply those properties for the same named vertical-row class over Nat × Nat. N502 reads the first sample's row and selects an arbitrary unseen row point; source uses the canonical minimum. The source's row witness is recovered independently of the existential facade.

Absence judgments used searches across all census theorem types and relevant nonproof definition aliases, not facade names alone. The source's A.10 proof relies on Theorem 3.9, but its questioned route does not independently establish falsity of A.10 or A.11.

## Thirteen registered target dossiers

All names below have prefix `GenLimit.FeedbackQueries.Results.`. Exact types are at the indicated R record; source and full hypotheses are given above and in the JSON.

| Target suffix | R | Retained statement |
|---|---:|---|
| theorem_3_1 | 29 | Element mistake iff countable inner cover, with explicit domain/all-infinite premises. |
| theorem_3_2 | 33 | First-element-feedback set mistake iff element mistake. |
| theorem_3_3 | 34 | Some Nat class has element query success and no set query success; native same-class support supplies infinitude. |
| theorem_3_4 | 35 | Set query iff countable inner cover. |
| corollary_3_6 | 26 | Both countable-union implications, with one resulting class-wide learner in each model. |
| corollary_3_7 | 27 | Both explicit zero-example implications, with separate conclusion witnesses. |
| corollary_3_8 | 28 | Both arbitrary-stream eventual-feedback characterizations. |
| theorem_3_9_of_selfLocking | 37 | Iff conditional on the universal freshened-generator self-locking premise. |
| theorem_3_9_set_to_element | 38 | Unconditional set-to-element direction; no typeclass premises. |
| theorem_3_9_appendix_A_8_gap | 36 | Four same-witness counterexample properties, including successful generation and no actual-prefix lock. |
| theorem_3_10_finiteInnerCover_sufficient | 31 | Finite cover suffices; Nonempty and Countable premises retained. |
| theorem_3_10_countableInnerCover_example | 30 | One class has UUS, generation and a countable cover. |
| theorem_3_10_noFiniteInnerCover_example | 32 | One product-domain class has UUS, generation and no finite cover. |

## Stage 1 updates, coverage and unresolved questions

No semantic error was found in Stage 1's reconstructed target types or feedback definitions. Its refusal to name unnamed existential witnesses remains correct. Native same-class results now add the three-point witness's infinitude, the general countable-class fact, and the vertical-row witness's combined properties; these are supporting interface assemblies, not witnesses extracted from proofs.

All ten slots, thirteen targets, grouped A.2–A.7 and A.9–A.13 assertions, A.1/A.8 locking meanings, and displayed generator components are accounted for. Source visuals from pp.4–8 and 11–25 were retained; pp.17 and 23 were re-inspected during comparison. Ordinary versus zero-example versus arbitrary-stream models, feedback timing, quantifier dependencies, and semantic computation boundaries were checked separately.

Stage 3 questions are the source's actual-prefix A.8 assertion, unconditional recovery of Theorem 3.9, missing native A.10/A.11 assertions, the auxiliary zero-example set-mistake extension, and A.4's stronger phase-stabilization assertion. The noisy model's formal inherited assumptions versus broader prose should remain explicit. No genuine oracle/timing translation mismatch was found. No claim is made about proof correctness, compilation, effective extraction or human certification.

STOP: comparison complete pending coordinator verification and freeze; developer explanations remain unopened.
