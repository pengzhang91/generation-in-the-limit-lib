# P27 source-only inventory

Pinned edition: Hanneke, Karbasi, Mehrotra and Velegkas, *Language Generation with Feedback: Queries and Mistakes*, ICML 2026, OpenReview jvfXyIcQ8a. The original PDF's locally computed SHA-256 is `e3467ab76be2eae001490a43e461865d2c704633e2656bd05ff2eb477b4b1319`, matching the package's expected hash. Text comes from the packaged page-marked extraction; visual checks use the annotation-removed derivative, whose distinct SHA-256 is recorded in the run record. Printed and PDF page numbers agree on every visually checked page.

This inventory covers all ten claim-index slots and their grouped appendix results. It records source meaning only; no implementation, earlier reconstruction, or source-to-implementation assessment was accessed. The JSON contains the same ten slots with fully stated per-slot assumptions and qualifications.

**Common source model (Sections 2–3.1, pp. 4–6).** X is a countable universe with a fixed enumerating order; the proofs use that each element has finitely many predecessors. Languages are infinite subsets of X and a collection may be uncountable. In the ordinary model, a presentation enumerates every element of its target K, permits repetitions, and contains only elements of K. H_n is the ordered length-n prefix and S_n is its finite support. A generator is a sequence of functions on finite ordered interaction histories. An element generator outputs one point; a set generator outputs an infinite set on every input. Success means that one generator works for every target and every permitted presentation, with a finite eventual correctness time that can depend on that interaction; subsequent outputs lie in K minus S_n. The functions and sets are semantic objects. No decidability, effective presentation, time bound, random seed, probability law, or probabilistic success criterion is imposed. A countable inner cover is a countable family of infinite subsets C_i of X such that every K in the collection contains some C_i. A cover member need not itself belong to the collection. A finite inner cover has the same property with finitely many infinite members.

**Feedback and access.** A query answer is received before that round's output and gives membership in K; the model permits one query per round indefinitely. Mistake feedback is received after the output and gives membership in K minus S_n; for an infinite set output it tests only the canonical first point. Cover-based constructions assume fixed semantic access to their arbitrary cover sets; no effective enumeration, membership decision procedure, finite encoding of an infinite output, or runtime bound is provided. The maps are deterministic and no probability measure or randomized success criterion is introduced.

**Reading and visuals.** The complete 26-page author text was read. The decisive definitions, statements, constructions and formulas were visually checked on PDF/printed pp. 4–8 and 11–25, in `visual-checks/page_N.png`. External papers cited as prerequisites were not opened; their results are recorded as dependencies stated by this pinned paper.

## C01 — claim:hkmv26:element-mistake-characterization

Element-valued generation in the limit with mistake feedback is possible exactly for collections with a countable inner cover.

**Source locations:** Theorem 3.1, PDF/printed pp. 6; Definitions 1, 3 and 4; Section 2 and Section 3.1, PDF/printed pp. 4, 5, 6; Appendix A.1.1; Lemma A.1 and three-part proof, PDF/printed pp. 11, 12.

**Parts and proof context:**

- **Necessity: Lemma A.1:** For each target and successful element mistake generator, some finite target history with its induced feedback locks correctness for every finite target continuation, including the empty continuation. This is an existence of a locking history, without requiring it to prefix every enumeration.
- **Necessity: self-simulation:** For each finite history sigma and finite past-bit string beta, repeatedly append the generator's output to the history and append answer 1. Keep infinite output ranges; there are countably many such finite input pairs. A locking pair supplies an infinite subset of each target.
- **Sufficiency: cover generator:** Use i_n = 1 plus the number of earlier zero feedback bits; output the least point of C_(i_n) outside S_n. Each incorrect lower-index candidate is eventually exposed by its least point outside K, after the finite predecessor points have appeared. The least contained cover candidate is never abandoned.

**Qualifications:** The source calls these objects algorithms, but its mathematical definition imposes no computability condition. A single membership-correct point is insufficient: correctness also excludes the current seen set.

**Visual record:** [p. 4](visual-checks/page_4.png), [p. 5](visual-checks/page_5.png), [p. 6](visual-checks/page_6.png), [p. 11](visual-checks/page_11.png), [p. 12](visual-checks/page_12.png).

## C02 — claim:hkmv26:set-element-mistake-equivalence

For each collection, the existence of a successful set-valued mistake-feedback generator is equivalent to the existence of a successful element-valued one.

**Source locations:** Theorem 3.2, PDF/printed pp. 6; Definition 3, PDF/printed pp. 5; Appendix A.1.1 joint proof with Theorem 3.1, PDF/printed pp. 11, 12.

**Parts and proof context:**

- **Set to element:** Output the canonical first element of the original set. Its observed bit exactly equals the bit supplied to the set generator, so the same feedback history can be simulated.
- **Element to set, through a cover:** Use Theorem 3.1's extracted countable inner cover. With i_n counting earlier negative bits, output C_(i_n) minus S_n; the feedback still checks only its first point. The cover proof makes the entire infinite output eventually correct.

**Qualifications:** The equivalence concerns existence for a collection. It does not change the source's first-element-only set feedback into a test of all output points.

**Visual record:** [p. 5](visual-checks/page_5.png), [p. 6](visual-checks/page_6.png), [p. 11](visual-checks/page_11.png), [p. 12](visual-checks/page_12.png).

## C03 — claim:hkmv26:query-separation

There is a collection that an element generator can generate with one membership query per round, but no set generator can generate with this feedback.

**Source locations:** Theorem 3.3, PDF/printed pp. 6; Definition 2, PDF/printed pp. 4, 5; Appendix A.2.2 witness and diagonalization, PDF/printed pp. 14, 15.

**Parts and proof context:**

- **Element generator:** Select a block disjoint from S_n with index larger than all previously used block indices. Query 3j-2, then output 3j-1 on answer 1 and 3j on answer 0. The output differs from the queried point, is unseen, and belongs to K from round 1; queries never repeat.
- **No countable inner cover:** An infinite candidate cover set intersects infinitely many finite blocks. For each countably indexed candidate choose a distinct intersected block and a point in the candidate; choose that block's bit so the selected point is excluded. The resulting target contains no candidate in the cover.
- **Set impossibility:** Apply Theorem 3.4 to the absence of a countable inner cover.

**Additional scope:** For the exhibited witness the universe is the positive integers, split into consecutive three-point blocks B_j = {3j-2,3j-1,3j}, j >= 1.

**Qualifications:** The positive result does not need to output the queried point, although the general query model allows such output when it is fresh. The diagonal bit choice is a mathematical existence argument; it does not assert an effective construction from an arbitrary cover representation.

**Visual record:** [p. 5](visual-checks/page_5.png), [p. 6](visual-checks/page_6.png), [p. 13](visual-checks/page_13.png), [p. 14](visual-checks/page_14.png), [p. 15](visual-checks/page_15.png).

## C04 — claim:hkmv26:set-query-characterization

Set-valued generation in the limit with query feedback is possible exactly when the collection has a countable inner cover.

**Source locations:** Theorem 3.4, PDF/printed pp. 6; Definition 2 and Definition 4, PDF/printed pp. 5, 6; Appendix A.2.1 two directions, PDF/printed pp. 13, 14.

**Parts and proof context:**

- **Necessity: all possible output ranges:** For each n there are countably many ordered histories and finitely many n-bit transcripts. The union over n of all set outputs is countable; all its members are infinite, and eventual success contributes a contained set for each target.
- **Sufficiency: query rule:** Let i_n be 1 plus earlier negative answers and query the least member of C_(i_n) outside S_n.
- **Sufficiency: current-answer output rule:** If the current answer is 1, output C_(i_n) minus S_n; if 0, output C_(i_n+1) minus S_n. Each is infinite. Finite predecessor exposure drives the index to the least cover member contained in K.

**Qualifications:** This is the indefinite one-query-per-round model, not a fixed finite total query budget. Counting possible outputs proves countability; it does not supply an effective enumeration or encoding of arbitrary infinite outputs.

**Visual record:** [p. 5](visual-checks/page_5.png), [p. 6](visual-checks/page_6.png), [p. 13](visual-checks/page_13.png), [p. 14](visual-checks/page_14.png).

## C05 — claim:hkmv26:countable-union-closure

For countably many collections on the same domain, if every collection is generable with element mistake feedback, their union is too; if every collection is set-generable with query feedback, their union is too. Mistake set generation follows by the source's element/set equivalence.

**Source locations:** Corollary 3.6 and Section 3.4.1, PDF/printed pp. 7; Corollary A.2, PDF/printed pp. 15, 16; Corollary A.3, PDF/printed pp. 16.

**Parts and proof context:**

- **Corollary 3.6:** States the two corresponding union closure conclusions together.
- **Corollary A.2:** Element mistake-feedback union closure by Theorem 3.1, the union of the countable covers, and Theorem 3.1 again.
- **Corollary A.3:** Set query-feedback union closure by the same argument with Theorem 3.4.
- **Adjacent Cartesian-product remark:** Section 3.4.1 also observes that covers C_1 and C_2 yield the countable product cover C_1 tensor C_2 for the collection of product languages L_1 times L_2 over X_1 times X_2. This is a remark beside the named union corollaries.

**Additional scope:** All collections in a union use a common countable universe X and the corresponding feedback model.

**Qualifications:** Corollary 3.6 abbreviates the mistake output mode; A.2 states the element version explicitly, and Theorem 3.2 supplies the set version. The paragraph attributing a finite set-query union result to Bai et al. is background, not an additional premise.

**Visual record:** [p. 7](visual-checks/page_7.png), [p. 15](visual-checks/page_15.png), [p. 16](visual-checks/page_16.png).

## C06 — claim:hkmv26:zero-example-generation

Ordinary mistake-feedback generability implies zero-example mistake generability; ordinary set-query generability implies zero-example set-query generability. Here S_n is empty at every round and only feedback remains.

**Source locations:** Corollary 3.7 and Section 3.4.2, PDF/printed pp. 7; Corollaries A.4 and A.5, PDF/printed pp. 16; Appendix A.4.1 and A.4.2 constructions, PDF/printed pp. 16, 17, 18.

**Parts and proof context:**

- **Corollary 3.7:** Groups the mistake and set-query zero-example implications.
- **Corollary A.4 and its construction:** Let T_n be all prior output points; let i_n count earlier zero bits. Output the least member of C_(i_n) outside T_n. The source says the set-mistake conclusion follows from Theorem 3.2.
- **Corollary A.5 and its construction:** Let T_n be the prior query points used at the current index i_n; query the least point of C_(i_n) outside T_n. On answer 1 output C_(i_n) minus T_n; on answer 0 output C_(i_n+1). Every output set is infinite.
- **Progress proof:** The source seeks the least contained candidate: while a lower candidate is active, progressing through its finite predecessor points eventually exposes a negative point; after reaching a contained candidate, all subsequent feedback is positive.

**Additional scope:** The conclusion replaces a target enumeration by a special zero-example interaction with no positive samples and S_n = empty for every n. Feedback is still received every round.

**Access/timing:** Mistake output uses past bits and gets its new bit afterward. Query output can use the current query answer. No positive-sample channel is used in the zero-example conclusion.

**Qualifications:** The zero-example interaction is a deliberately modified setting, not an enumeration of an infinite target under Definition 1. A.4's prose mentions unseen input S_n while its displayed output rule excludes own prior outputs T_n; the displayed formula is the operative construction. For A.4, the proof's statement that it reaches the least fully contained candidate is stronger than eventual correctness: globally excluded prior outputs can include a bad point of a later candidate. The inventory retains the source's conclusion and records its actual T_n rule. A.5 excludes prior queries at the current phase from its set output, but its success criterion is still K because S_n is empty; it does not impose global cross-round set disjointness.

**Visual record:** [p. 7](visual-checks/page_7.png), [p. 16](visual-checks/page_16.png), [p. 17](visual-checks/page_17.png), [p. 18](visual-checks/page_18.png).

## C07 — claim:hkmv26:eventually-correct-feedback

With arbitrary finitely corrupted feedback followed by correct bits forever, element mistake generability and set-query generability are each equivalent to existence of a countable inner cover.

**Source locations:** Definition 5; Corollary 3.8 and discussion, PDF/printed pp. 7, 8; Theorems A.6 and A.7; Definitions 6 and 7, PDF/printed pp. 18; Proof of A.6, PDF/printed pp. 18, 19, 20; Proof of A.7, PDF/printed pp. 20, 21, 22.

**Parts and proof context:**

- **Corollary 3.8:** Groups the element-mistake and set-query characterizations.
- **Theorem A.6: finite expansion:** Expand the collection and cover by finite perturbations; choose a fixed enumeration of the expanded cover.
- **Theorem A.6: generator:** Let T_n be all prior outputs and i_n be 1 plus prior observed zero bits. Output the least point of the current expanded candidate outside S_n union T_n, so outputs never repeat.
- **Theorem A.6: target repair and conclusion:** Change membership of finitely many early output points to match their observed labels. Nonrepetition makes every label consistent with one repaired target. The source applies cover-based generation to that target; eventually avoiding its finite symmetric difference gives true-target generation. The reverse direction uses feedback correct from the start.
- **Theorem A.7: generator:** Let Q_n be all earlier query points. Choose the least expanded-cover index having no previously queried member with observed label 0; query its least point outside Q_n. On observed answer 1 output that candidate, and on 0 output its next indexed candidate, in either case deleting S_n union Q_(n+1). Queries never repeat.
- **Theorem A.7: target repair and conclusion:** Repair membership of finitely many early queried points to obtain K'. Negative observations permanently invalidate bad candidates and the least candidate contained in K' survives. Delete all queried points from outputs to exclude the finite false positives introduced in K'. Necessity again uses the clean-feedback special case.

**Additional scope:** For every permitted interaction the observed feedback can differ from its correct round-specific value during a finite prefix; there is some n_0 after which every bit is correct. The error count and n_0 have no fixed bound and need not be supplied to the generator. The correct bits are evaluated on the actual interaction generated using the observed earlier bits, not on a separate clean run.

**Access/timing:** In A.6 the observed mistake bit follows the output; in A.7 the observed query bit precedes the output. Feedback eventually has the exact membership/freshness meaning prescribed by Definitions 2 or 3. No stochastic noise assumption appears.

**Qualifications:** The named results here cover element mistake feedback and set query feedback. They do not explicitly state the eventual-correct set-mistake analogue. Definitions 6 and 7 inherit the underlying interaction models, including the ordinary target-enumeration premise. Surrounding prose and constructions additionally advertise arbitrary contamination or absence of informative examples; they still delete the finite seen set S_n. No separate fully specified arbitrary-stream model is introduced. The displayed finite-expansion formulas omit parentheses around union and difference, but the accompanying explanation and repaired-target formulas specify finite symmetric-difference variants, namely (D union A) minus B. A.7's negative-answer set uses index i_n+1 rather than recomputing the next surviving index inside that round; its index is selected afresh at the following round.

**Visual record:** [p. 7](visual-checks/page_7.png), [p. 8](visual-checks/page_8.png), [p. 18](visual-checks/page_18.png), [p. 19](visual-checks/page_19.png), [p. 20](visual-checks/page_20.png), [p. 21](visual-checks/page_21.png), [p. 22](visual-checks/page_22.png).

## C08 — claim:hkmv26:no-feedback-set-element-equivalence

In the ordinary no-feedback model, a collection has a successful set generator if and only if it has a successful element generator.

**Source locations:** Theorem 3.9 and Section 3.4.4, PDF/printed pp. 8; Definition 1, PDF/printed pp. 4; Appendix A.6.1, PDF/printed pp. 22, 23.

**Parts and proof context:**

- **Set to element:** Select the canonical least member of the infinite output set. Eventual set containment implies eventual validity and freshness of this point.
- **Freshening:** Replace an element generator by G-circle, using G's output when it is outside the current history and the canonical least unseen universe point otherwise. It stays eventually successful and is fresh on every finite input history.
- **Lemma A.8 dependency:** The proof invokes actual-prefix self-locking of G-circle for each target enumeration; see C09 for the exact quantifiers.
- **Element to set self-simulation:** Starting from h of length n, iteratively append s_t = G-circle_(n+t-1)(h^(t-1)) and output the set of all s_t. Freshening ensures this set is infinite on every input; the cited self-locking property is used for eventual target containment.

**Access/timing:** Only H_n is observed before output. Freshness is against its support S_n.

**Qualifications:** The source works with ordered histories. Its proof needs the actual-prefix assertion of Lemma A.8, not just existence of some target locking history. The validity argument inherits the source-internal ordered-prefix construction concern recorded for C09.

**Visual record:** [p. 4](visual-checks/page_4.png), [p. 8](visual-checks/page_8.png), [p. 22](visual-checks/page_22.png), [p. 23](visual-checks/page_23.png).

## C09 — claim:hkmv26:appendix-a8-self-locking

For a fixed target K, any fixed enumeration of K, and the freshened successful generator G-circle from the preceding proof, some actual enumeration prefix H_(n_0) locks correctness: for every finite continuation rho in K^r and every r >= 0, G-circle_(n_0+r)(H_(n_0) concatenated with rho) lies in K minus the support of that concatenated history.

**Source locations:** Freshening and Lemma A.8; proof, PDF/printed pp. 23; Definition 1 and ordered-history model, PDF/printed pp. 4.

**Parts and proof context:**

- **Displayed lemma formula:** There exists n_0 such that every r >= 0 and every rho in K^r has a correct fresh output at the end of H_(n_0) concatenated with rho.
- **Source proof paragraph:** Argues by contradiction, claiming to choose nested sufficiently long actual prefixes of the fixed enumeration that extend all previously committed samples, then append error-forcing continuations while ensuring the enumeration remains exhaustive.
- **Use in Theorem 3.9:** Once such a prefix occurs, every later actual history extends it; recursively appended own outputs are claimed to stay in K, yielding a correct infinite set output.

**Additional scope:** G is an element generator successful on every enumeration of each target in the collection. G-circle is the preceding freshening of G, so it outputs a point outside its input support on every finite history. The target and the whole enumeration are fixed before the existential choice of n_0; n_0 may depend on them.

**Access/timing:** No feedback. The guarantee is over all finite K-valued continuations of an actual prefix of each fixed presentation.

**Qualifications:** This is stronger than Lemma A.1's existence of some finite locking history. Substituting the latter changes the assertion. The proof says a later actual prefix extends the previously appended witnessing continuation. With ordered histories, arbitrary appended continuations need not be prefixes of the fixed enumeration; the paragraph does not justify that nesting step. This source-internal proof issue is recorded without weakening the displayed lemma. The source does not separately state an arbitrary fresh generator as the lemma's variable: it uses the specific freshening G-circle supplied by the proof context.

**Visual record:** [p. 4](visual-checks/page_4.png), [p. 23](visual-checks/page_23.png).

## C10 — claim:hkmv26:no-feedback-inner-cover-boundary

The no-feedback model satisfies all five assertions grouped in Theorem 3.10: finite inner cover implies generability; generability implies a countable inner cover; some countably inner-covered collection is nongenerable; some generable collection has a countable inner cover; and some generable collection has no finite inner cover.

**Source locations:** Theorem 3.10, PDF/printed pp. 8; Appendix A.6 restatement, PDF/printed pp. 22; Theorems A.9 through A.11 and proofs, PDF/printed pp. 24; Theorems A.12 and A.13 proofs, PDF/printed pp. 25.

**Parts and proof context:**

- **Theorem A.9: finite-cover sufficiency:** For each finite cover member C_i, consider targets containing it; output C_i minus S_n on that subcollection, correct from round 1. Invoke Li et al. (2025), Theorem 3.10, that a finite union of uniformly generable collections is generable in the limit.
- **Theorem A.10: countable-cover necessity:** Convert an element generator to a set generator with Theorem 3.9. The countable union of all output ranges on finite ordered histories yields a countable family of infinite sets containing a subset of every target.
- **Theorem A.11: countable cover is insufficient:** Use the cited Hanneke et al. (2025)/Bai et al. (2026) example of two individually generable collections with a nongenerable union. A.10 gives each a countable inner cover; their union cover supplies the nongenerable union's countable inner cover. The statement is phrased as noncharacterization, and its proof supplies this direction.
- **Theorem A.12: generable and countably covered example:** Any countable collection works, using the cited countable-collection generability theorem of Kleinberg and Mullainathan (2024) and taking the collection itself as its inner cover.
- **Theorem A.13: generable without a finite cover:** Over X = positive integers squared, let L_i = {(i,j): j >= 1}. The first sample identifies its row i; output the canonical least unseen point in that row, valid from round 1. Each infinite cover set can be contained in at most one of the pairwise disjoint rows, so finitely many cannot cover them all.

**Qualifications:** Theorem 3.10 has five parts, although the introductory informal list gives only four; A.13 is the additional generable-without-finite-cover component. A.10 invokes Theorem 3.9, whose proof depends on the stronger actual-prefix Lemma A.8; see C09's source-internal qualification. The external prerequisites used in A.9, A.11 and A.12 are cited by the pinned source, rather than reproved there. The A.11 proof does not spell out the cited counterexample's languages. No unsupported explicit witness is inferred.

**Visual record:** [p. 4](visual-checks/page_4.png), [p. 8](visual-checks/page_8.png), [p. 22](visual-checks/page_22.png), [p. 23](visual-checks/page_23.png), [p. 24](visual-checks/page_24.png), [p. 25](visual-checks/page_25.png).

Source-only review is complete. Stop here pending the coordinator's freeze and explicit authorization for the comparison phase.
