# P27 — informed adjudication

**Disposition.** The existing counterexample justifies correcting source Lemma A.8, including its application to the source's specific freshening. It does **not** refute or complete unrestricted Theorem 3.9. Its reverse direction and Theorem 3.10 components A.10/A.11 remain formalization gaps. The principal feedback statements match on their disclosed semantic domains; algorithm variants, same-witness assemblies and ancillary zero-example/product gaps remain qualified. No genuine oracle/timing translation mismatch was found.

This is the **same source-informed Stage 2 reviewer continuing after freeze**, not a third independent blind review. Parent steering requested the A.8 premise check and preservation of conditional/gap qualifications; it supplied no new proof or counterexample construction. [Stage 2](source-comparison.md), [the source inventory](source-inventory.md) and their frozen JSON evidence remain unchanged. The ten-row [adjudication JSON](adjudicated-claims.json) accounts for all 38 component comparisons and all 13 targets without duplicating the large Stage 2 rows.

## Pinned evidence and explanations

The only source edition remains ICML 2026 OpenReview jvfXyIcQ8a, original PDF SHA-256 `e3467ab76be2eae001490a43e461865d2c704633e2656bd05ff2eb477b4b1319` (creation metadata 2026-06-05). Printed and PDF pages agree. The exported interface snapshot remains `e56b617a39899cb9acfd94b61e19680934bf78aa1f40d8d07d8e7f1d10bee1fc`.

| Explanation opened after Stage 2 freeze | Actual SHA-256 | What it discloses; what it cannot establish |
|---|---|---|
| [PaperMap](../stage3-context/PaperMap.md), lines 15–23, 37–47, 95–104 | `0a3e7c65c2d1d0ff05872f046aa1dfb659de7f8442b1d3b31bbe046e5ba6b7dc` | Semantic/infinite-domain scope, alternative noise construction, conditional 3.9 and deferred A.10/A.11. Disclosure is consistent with inspected interfaces but is not proof. |
| [Owner registry](../owner/registry.json), /paper/formalization_scope and /claims/0–9 | `17939fff9e31af5f17e3a533161ba7b2faea6a8d4817e276325f8958c36a5774` | Same scope, source-error explanation for A.8, five separate 3.10 components. Its full-coverage labels do not cover every adjacent remark or literal construction automatically. |
| Stage 3 instructions | `6c633fea6c1a5c76bfcde08b1d11d230708bd063fae5b8665eccd65bb7114d67` | Authorizes informed adjudication, not alteration of frozen evidence or proof certification. |

Embedded claims about earlier human/kernel audits were not used as mathematical evidence; linked audit ledgers and proof bodies were not opened. All three freezes and nine frozen outputs were verified. All 134 recursive types still match the native census. Below, **R** means the one-based line in [recursive interfaces](../stage1/declarations.jsonl), **N** the line in [native census](../stage1/native-declaration-census.jsonl).

**Source numbering qualification.** In this pinned PDF, the no-feedback discussion is Section **3.4.4**, p.8, and Appendix A.6, pp.22–25. Registry/claim-index references to Section 3.5 are locator metadata, not a different source edition. Theorem 3.10 has five components A.9–A.13, even though the introductory informal list omits the no-finite-cover example.

## Final target coverage

All target suffixes have prefix `GenLimit.FeedbackQueries.Results.`. Each source claim's complete assumptions and exact types remain in Stage 2.

| Slot | Target suffix / R | Final target assessment |
|---|---|---|
| C01 | theorem_3_1 / 29 | Matches the semantic characterization, qualified by explicit ambient infinitude and cover/rank representation. |
| C02 | theorem_3_2 / 33 | Matches representative-feedback equivalence; the representative bit never certifies the entire set. |
| C03 | theorem_3_3 / 34 | Matches through the same native all-infinite three-point witness; concrete fresh-block algorithm is a variant. |
| C04 | theorem_3_4 / 35 | Matches the one-query characterization; fixed fair scheduling differs from the displayed adaptive generator. |
| C05 | corollary_3_6 / 26 | Both named union branches match; set-mistake closure is assemblable. Adjacent product remark remains unrepresented. |
| C06 | corollary_3_7 / 27 | Both explicit zero-example implications match. Different algorithms and the auxiliary set-mistake zero-example gap remain. |
| C07 | corollary_3_8 / 28 | Both characterizations match the broader arbitrary-stream prose; formal inherited definitions are generalized. Alternative robustification is disclosed. |
| C08 | theorem_3_9_of_selfLocking / 37 | Faithful conditional construction, not unrestricted theorem coverage. The extra universal self-locking premise stays visible. |
| C08 | theorem_3_9_set_to_element / 38 | Unconditional source direction, faithfully generalized beyond countable types. |
| C09 | theorem_3_9_appendix_A_8_gap / 36 | Justified source correction: opposite to positive A.8, not positive coverage of that lemma. |
| C10 | theorem_3_10_finiteInnerCover_sufficient / 31 | A.9 matches; cover containment entails target infinitude. |
| C10 | theorem_3_10_countableInnerCover_example / 30 | A.12 matches; N158 additionally supplies the reusable countable-class result. |
| C10 | theorem_3_10_noFiniteInnerCover_example / 32 | A.13 matches using the same native vertical-row class and separate same-class properties. |

## A.8: hypothesis-complete mathematical check

**Informal mathematical check — not Lean-checked in this audit.** Source p.23 claims that every successful generator, after freshening, has a locking **actual prefix of every fixed presentation**, correct after every finite target-valued continuation. R36 instead asserts success, everywhere freshness, a valid presentation and absence of any such prefix for the same named objects.

Write a_i = inl(i), b_i = inr(i). Let X = Nat + Nat, K = {a_i : i ≥ 0}, and H = {K}. Let

- h_n = [a_0,…,a_(n−1),a_(n+1)];
- G(h) = b_0 when h equals some h_n;
- otherwise G(h) is a point of K outside the finite seen set;
- p(i) = a_i.

These are exactly the defining expressions R19–24. The following checks validate the explanation independently of its coverage labels:

1. **Domain and family.** X is countably infinite; K is infinite; the singleton class is permitted. No actual source premise requires a nonidentifiable or uncountable class. R25 supplies the same target's infinitude interface.
2. **History/access model.** G uses the full finite ordered history, as permitted by Section 2, p.4. It has no feedback or target-membership oracle. Its arbitrary fresh selection stays within the source's semantic function model; no effective implementation is inferred.
3. **Success on every presentation.** If n < m, h_n and h_m disagree at position n: the former has a_(n+1), the latter a_n. Thus two distinct spike histories cannot both prefix one stream. There is at most one spike error on any stream; every other output belongs to K and is sample-fresh. Hence every target presentation has a finite eventual correctness time. N846/848/849/852 state the corresponding facts; no uniform time bound is needed.
4. **Freshness on every input.** A spike contains only left-summand points, so b_0 is unseen. At nonspikes the output explicitly avoids all seen points. This covers malformed/off-target histories too, matching EverywhereFresh (R12, N847).
5. **The source's specific freshening.** Source G-circle preserves G(h) whenever G(h) is unseen. Since that holds on every history here, G-circle = G everywhere. Source's canonical-minimum fallback and Lean's arbitrary-fresh fallback are both dormant. R80 and N220 expose precisely this branch condition; the selection difference cannot save A.8.
6. **Actual prefix and allowed continuation.** p genuinely presents K. After its prefix of length n, append the single target point a_(n+1). The resulting ordered list is h_n and G-circle returns b_0 outside K. This works for every n, including all positive lengths relevant to the source. The continuation need not remain a prefix of p; A.8 quantifies all finite K-valued continuations. N843/844 assert the same prefix/continuation relationship.
7. **Scope of the correction.** The source proof's attempt to nest actual prefixes after arbitrary witnessing continuations fails: these spike continuations are incompatible. This invalidates the universal actual-prefix locking inference. It does not invalidate mere existence of some locking history, such as the different statement used for C01.

The same singleton class has an immediate successful set generator h ↦ K minus seen(h), an infinite subset at every round. Thus this example itself satisfies both sides of Theorem 3.9; it cannot refute the headline equivalence.

**Smallest safe repaired conversion.** Keep the fresh self-simulation argument conditional on actual-prefix self-locking instead of deriving that property from success alone. N333 implements the sufficient condition for one everywhere-fresh self-locking generator. Public R37 assumes the stronger class-wide condition for every successful generator's freshening. Neither interface provides the omitted unrestricted implication. A weaker “some locking history exists” replacement would not justify the source's actual-prefix argument automatically.

Owner /claims/8 correctly records a refutation with no positive coverage; /claims/7 and PaperMap line 42 correctly keep unrestricted 3.9 partial. Their documented deferral is accepted as scope disclosure, not proof of either truth or falsity.

## Remaining discrepancies and local checks

**C01–C02: model and representation.** The source allows arbitrary countable X and only infinite target languages; Lean explicitly requires Infinite α. It follows automatically for a nonempty source collection, but the literal finite-universe/empty-class edge remains excluded. This harmless intended-domain specialization stays recorded. Nat-indexed infinite covers with repetitions and a classically selected finite-predecessor rank preserve semantic meaning. They provide no effective enumeration or uniform selector. Native locking/simulation and representative-feedback equalities match the already checked source components.

**C03: resolved witness assembly, changed algorithm.** Native N485–490 give the three-point class and its infinitude/separation facts for that same class; N276 gives no countable cover. N479 and N465 support validity from the first round for the same strategy. Owner disclosure agrees. However, the native block above the sampled maximum can repeat when samples repeat, whereas source A.2.2 tracks a strictly increasing used-block index. The theorem matches; global query nonrepetition from the particular source algorithm does not transfer.

**C04–C05: constructions and ancillary coverage.** Fair cover-point scheduling still uses one membership query per round, with its current answer available before output. In the truthful model every bad lower cover row has a point eventually tested, so only finitely many rows below a contained row need be eliminated; this explains the alternative strategy without claiming a Lean proof audit. Countable union cover pairing and the two named union branches match. Set-mistake union closure is a same-class assembly through C02. The neighboring Cartesian-product remark has no located endpoint and remains ancillary unrepresented context.

**C06: headline match, local source proof repair, auxiliary gap.** Source zero-example success has S_n empty and therefore imposes membership/containment, not cross-round novelty. Native constant-representative element output and fair-scheduled query sets can meet those goals while differing from the source traversal algorithms. The owner’s full label applies to the two explicit interfaces, not automatically to A.4's additional set-mistake zero-example sentence. There is no corresponding zero-example set-mistake predicate/endpoint in the frozen census; ordinary R33 requires presentations and cannot simply be instantiated with an empty seen set for an infinite target.

**Informal check A4 — not Lean-checked.** Let K be the positive evens, C1 = K ∪ {1}, C2 = (K minus {2}) ∪ {1}, and C3 = K, in natural order. All members are infinite and C3 is the least wholly contained candidate. Source A.4 first emits 1 and advances to C2. Global prior-output memory now excludes 1, so it emits 4,6,8,… and stays at C2 forever. The p.17 assertion that it reaches C3 is false, while eventual validity holds. A finite family is countable; additional distinct infinite members may be appended after C3 if desired.

The smallest repair preserves the algorithm and replaces the unnecessary phase claim: its phase cannot pass the least fully contained cover member, where every output is valid. Hence the negative-bit count is bounded and there are only finitely many invalid outputs. This is a local correction of proof prose, not a refutation of Corollary A.4 or a new Lean proof.

**C07: qualified model and robustification.** R6/R10 admit arbitrary sample streams and observed bits eventually correct for the actual interaction. This is stronger than literal inherited Definitions 6–7 and consistent with the source's arbitrary-contamination prose. PaperMap line 41 and registry /claims/6 explicitly disclose repeated cover members and queried-point removal instead of finite expansion. Repetition preserves unpoisoned copies despite finitely many false negatives; removing queried points prevents early false positives from persisting in set outputs. This explains the mechanisms, without certifying the full infinite-run proof. Source nonrepetition and finite-expanded-target construction are not native construction coverage. Both named A.6/A.7 characterization interfaces are present; no stochastic noise law, known cutoff or complexity guarantee is added.

**C08/C10: disclosed gaps remain gaps.** R37's extra premise is substantive. The opposing changes—more general ambient types but stronger locking hypotheses—cannot be collapsed into an unconditional equivalence. Source A.10's route uses unrestricted 3.9; A.11 then uses A.10. PaperMap lines 44–45 and registry /claims/9 accurately defer those two of five components, matching the frozen census searches. No claim that their statements are false follows. A.9/A.12/A.13 remain accepted independently. N158 verifies the countable-class fact; the owner's assertion about a hidden singleton wrapper proof is not used to identify its existential witness. N504–508 tie the vertical-row properties to the same class, with arbitrary semantic fresh-point selection rather than a canonical minimum.

## Validation limits and follow-up

All mathematical arguments above are expressly informal and not Lean-checked in this audit. Exported theorem statements and defining expressions were inspected; theorem proofs, compilation, axiom audits, human certification and effective extraction were not. No distribution, loss/rate, machine-level or query-complexity claim is certified. The source's permitted query oracle and after-output mistake signal remain distinct; no extra target oracle was found.

Keep the A.8 correction, conditional/unproved 3.9 status, and A.10/A.11 deferrals visible. Qualify zero-example and ancillary product coverage; label literal algorithm variants, including the lost query-nonrepetition addendum. If source proof prose is revisited, use the local A.4 bounded-negative-count repair. Correct Section 3.5 locator metadata only in a separately authorized update. No source, registry, proof, Git or frozen output was changed, and no further unrestricted-theorem proof search was undertaken.

Adjudication is complete for all 10 slots, 13 targets and 38 prior components. STOP pending the coordinator's final freeze.
