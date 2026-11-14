# Stage 3 adjudication

## Executive disposition and provenance

Both selected targets remain **matches source context, with qualified model/representation choices**. The newly opened explanations corroborate the deterministic scope and alternative necessity construction; they do not certify proof equivalence. The canonical examples remain missing formal specializations, and the entire statistical/IID/rate model remains a substantive coverage gap. Several source descriptions admit small informal repairs; none supplies a counterexample to either selected Lean proposition.

This is the **same continuing Stage 2 reviewer**, not a third independent blind review. Requested invocation remains gpt-6.1-sol/xhigh with initial fork_turns=none; backend revision and sampling identity are unavailable. The parent supplied the Stage 3 instructions and a checklist of issues, but no mathematical argument or proof; it reported that its full report review was pending. All mathematical arguments newly given below are informal and not Lean-checked. No source or Lean proof certification is claimed.

Frozen Stage 2 hashes remain unchanged: `source-comparison.md` = `60891cbbae3a5290aa60f4af5180c518784ed9745fbb949d3f18f89128a3c3fa`; `stage2-run.json` = `bf9f730b3d656412517eab600e878223c9b07f0340e34eb36ca49d2b3b73aa6d`. Stage 1 and the complete source/native evidence remain those pinned in that run. In particular the official arXiv:2511.04103v1 PDF has hash `fdc00078c5ca6f2794005d608ebae5c46a7b5f012e5a200891e10cfd1f4a32d4`, 30 pages; printed/PDF page numbers agree on the decisive renders.

## Existing explanations tested

| Context and hash | Relevant anchors | Adjudication |
|---|---|---|
| `stage3-context/PaperMap.md`, `9e10dadac4d49c724cc207341b6c59800116c983e98c6d9cfba5b3cbbc74f4e9` | Lines14–32 scope/presentability/k=0/semantic model;42–46 algorithm, necessity, targets;47,67–78 missing statistics | Accurate substantive disclosure, supported by exact interfaces. “Proof-equivalent route” describes intent, not a proof certification by this audit. |
| `stage3-context/registry.json`, `2ddda937f4b2194fde6d684f0c9301093ed6dbcf35cdf52080b2dc9beadc2822` | Lines36–49 partial scope;104–105 source locator;146–152 model;184–186 relative layers;249–285 statistics | Target interpretations agree with canonical definitions. Some source locators/inventory labels are stale; statistical summary needs the nontriviality proviso. |
| `stage3-context/provenance.json`, `d5c4215ec0c4d8cda20af08421eee529ae39511b9d45d40867e6a8ffd08cf356` | Capture timestamp 2026-11-10T14:23:54.916517+00:00 and frozen-context hashes | All three entries in the context manifest verified; read only after Stage 2 freeze. No additional correction record or raw developer comments were supplied/read. |

The pinned source ends its numbered sections at 8.3. Documentation references to “Sections 8–10” are incorrect. Registry Theorem 1 locators “pp3,23–24; Sections1.1 and10” should point to p3 and its detailed bounds pp14–17, Sections5–6. Statistical details extend through p27, not merely p24. The registry exclusion list's Claim9.1 and Algorithms1–3 do not match this edition's Claim5.1, Algorithms1–2, and Procedure2. These are documentation issues, not evidence of wrong Lean mathematics. No documentation was edited.

## Both scoped targets

Let H(F) mean ∀i ∃s:Nat→α, range(s)=F_i. Both exact types quantify arbitrary α with DecidableEq α and F:Nat→Set α, assume H(F), and then quantify every natural k. The common learner property is

∃A:(t:Nat)→(Fin t→α)→(Fin k→Nat), ∀z,s, range(s)=F_z → ∃N ∀t≥N ∃r:Fin k, F_(A(t,s below t)(r))=F_z.

| Full short Lean target | Exact remaining claim and source | Final disposition |
|---|---|---|
| `GenLimit.ListIdentification.Results.theorem_1` | Under the common binders/premise, ∀k, the displayed learner property iff ∀i Ψ(F,i,k). Ψ0=False; Ψ(i,k+1) means ∃finite T⊆F_i ∀j, T⊆F_j→F_j⊊F_i→Ψ(j,k), in the same full F. Source Theorem1 p3 and (4)–(6) p11, detailed Theorems6–7. | **Matches source context; qualified ambient generalization and k=0 extension.** Both implications and witness order retained. |
| `GenLimit.ListIdentification.Results.theorem_2` | Same learner property iff ∃layers:List(Set Nat), length=k ∧ every index belongs to a listed layer ∧ every i in every layer has a finite T⊆F_i excluding that layer's proper sublanguages containing T. Source Theorem2 pp3,17–18. | **Matches source context through native assembly; qualified index-layer representation.** All three conjuncts retained. Literal separately indexed learner-valued wrapper is not the definition. |

H(F) is stronger than bare nonemptiness on an arbitrary uncountable ambient type, but the source also assumes a countable universe. `exactPresentation_presents` supplies presentations from nonemptiness on countable α; the native Nat specialization also exposes the nonempty-language formulation. Conversely H(F) permits unused uncountable ambient points. No language is silently lost: all target sources remain universally quantified after H(F), not restricted to its existential witnesses.

The successful output index may vary forever while denoting the correct language, matching the source's BC convention. A Core identifier elsewhere requires a fixed final name; that different definition does not replace P14's target predicate. Claim5.1 stabilizes a particular construction's least index, a stronger local fact, not a strengthened success requirement on every learner.

For k=0, an exact presentation of F_0 prevents success because Fin0 has no slot; Ψ0 is false and the length-zero layer list cannot cover index0. Empty languages violate H(F), rather than receiving a purported learner guarantee. Finite nonempty languages use repetitions; partial streams that omit target elements are outside range equality. Duplicate names satisfy extensional correctness and never count as strict sublanguages. Positive-Nat/zero-based indexing and at-most-k/exact-k outputs translate by renaming and padding; native padding preserves all existing guesses when length≤k.

Theorem2's index layers may overlap, repeat, or be empty, just as a union claim need not be a partition. `relativeIdentifier_identifies_member` (Stratification:199) provides a single scalar learner on each layer, and `stratifiedIdentifier` (:242) concatenates outputs. Nonempty layers admit countable reindexing; empty layers may be replaced by singleton or repeated identifiable layers while retaining k positions. This is small semantic assembly, not missing decomposition mathematics. A pairwise-disjointness claim is not a conjunct of the target.

Footnote4 p10 explicitly imposes no computational restriction. Learners see only their ordered finite input histories; A is chosen per F,k, not separately per target or source. Their thresholds are source-dependent. Classical tell-tale selection, semantic language tests, and relative layer membership in constructed functions are source-permitted. DecidableEq α does not give decidable membership or language equality; arbitrary functions are not ordinary programs, finite-query oracle procedures, uniform decider programs, or ordinary samplers. No effective uniformity across F or k is asserted or required here.

## Local mathematical checks of source discrepancies

### Canonical families and Remark 2

Stage 2 preserved a reversed removed-set cardinality and wrong base-depth explanation on p12. For C_m={Z\F: F finite, |F|≤m}, the corrected depth relation is

Ψ(Z\F,r) iff r>m−|F|.

Informally, induct on r. At r=0 both sides are false. If r>m−|F|, every proper sublanguage removes a strict superset G of F, so the predecessor depth holds there; even T=∅ works. If 1≤r≤m−|F|, any finite T⊆Z\F leaves a fresh x outside F∪T. The language Z\(F∪{x}) contains T and fails predecessor depth by induction. This checks countability, infinitude/nonemptiness, the fixed full collection, and every finite tell-tale, including empty T.

Thus C_m fails global depth m but satisfies m+1, and the deepest base languages in the m+1 construction remove m elements, not one unless m=1. The same fresh-element induction shows all finite depths fail in the all-cofinite collection C_infty. Examples4–5 and the hierarchy conclusions survive; the literal explanation needs |G|>|F| and the corrected base level. These are **justified informal source corrections**, while Lean has no corresponding canonical-family formalizations. The generation contrast still relies on an external attributed theorem not independently reviewed here.

### Algorithm 2 exhaustion versus necessity

The literal line4 on p15 can be undefined under the full source assumptions. Take k=1, U=Nat, and C consisting of Nat and all nonempty finite subsets. This is countable, every language is nonempty and presentable, and Ψ(Nat,1) fails: every finite tell-tale fits inside a proper finite member. Let A always guess Nat. After the first string x, the routine may extend its chain from Nat to {x}, which contains the enumerated data and fails Ψ(_,0). At that leaf no unseen string exists. This is a counterexample to the printed routine's totality, not to Theorem7: A indeed fails on the constant presentation of {x}.

A minimal repair repeats a fixed member whenever the current language is exhausted, otherwise taking the first unseen member. Nonemptiness ensures a fallback; finite targets are already completely covered, and infinite targets keep making unseen progress. The proof must accordingly replace its universal “new distinct string” assertion by a completeness argument. Empty targets remain excluded, not handled by invented observations.

The native `listIdentify` is Algorithm1, with explicit empty-I/zero-depth branches and bounded output; it is not Algorithm2. Native necessity instead exposes target-lock existence, strict-language-cone reduction and deletion of a recognized target slot (Necessity:71,82,141; GeneralNecessity:48–199,247). Its exact necessity statement is the contrapositive of the source lower bound under H(F). Disclosed use of another route is **matches source context**; the literal state machine/invariants remain unformalized. No proof-body equivalence is certified.

### Theorem 10: causal simulations and coupling

Stage 2 questioned whether p23's infinite-input descriptions respect Definition5's t inputs and t random bits. They can be made causal without adding an oracle, as follows; this is an informal construction repair, not a native theorem.

From an IID learner to a randomized presentation learner, use disjoint fair-bit blocks to draw geometric positions J with P(J=j)=2^(-j). The jth source value at that position is available once the observed presentation prefix reaches J. At physical time t use only the first t bits and t source items; suspend pending draws rather than accessing the future, and hold the last completed simulated prediction. Every finite number of draws finishes at finite physical time almost surely. Their values are IID under D_sigma, which has exact target support even with repeated source values. The completed simulated length tends to infinity, so eventual success transfers with probability at least p. Initial empty simulation uses a fixed k-list.

In the reverse direction select the first two distinct values a,b from the **even subsequence only**, and use subsequent disjoint even pairs, accepting (a,b) or (b,a), to obtain independent fair bits. Conditional on the finite selection history, each accepted orientation is equally likely because D(a)D(b)=D(b)D(a)>0. Even data are independent of the odd IID sequence fed to the randomized learner. At physical time t simulate only as many logical steps as both observed odd examples and extracted bits allow; that number tends to infinity almost surely on nonsingleton targets. If the target is a singleton, the semantic singleton-index selector is eventually correct before any distinct pair is found. All decisions use finite observed prefixes and fixed F, not the target index or D as learner input.

This explicitly supplies delayed timing and an independent selection convention. It supports the theorem's existence claim, not rate preservation or the printed timing sentence literally. The original whole-stream a,b choice might also be justified by a conditional stopping-time argument; no full-premise theorem counterexample was found. **Qualified source construction repair; original proof details not certified.** All these probability constructions remain absent from Lean.

### Theorem 11: pointwise gap, rounding and sample-size boundaries

The theorem says ∀A ∃L,D with limsup error≥a=1/(k+1). Its negation gives one A with limsup<a separately for every L,D, not one uniform ε across them as equation(16) suggests. A pointwise gap suffices: choose ε(L,D)>0 and its eventual batch-size threshold separately. The booster itself uses only sample size and A: choose batch length b(t)=max(1,floor(log t)), number M(t)=floor(t/b(t)), discard leftovers, canonicalize denotations, and return k distinct most frequent representatives with fixed tie-breaking.

For each fixed L,D, sufficiently large batches have hit probability above k/(k+1) by a positive pointwise gap. The source's concentration/capacity argument then bounds boosted error by exp(−c(L,D)t/log t) for some positive c. This is summable; Borel–Cantelli gives eventual success almost surely for every L,D using the **same** booster. That contradicts Corollary8.1 if the condition fails. No uniform gap is needed in the learner's definition. **Justified informal quantifier/rounding repair; no counterexample to the theorem established.** The probability ingredients and Corollary8.1 are not Lean-certified here.

Using max(1,…) avoids log0/division-by-zero and defines all small sample sizes; arbitrary default predictions cover the initial finite range. For positive exponential rates finite initial exceptions can be absorbed into c1, while c2 and thresholds may depend on L,D as Definition4 permits. This cannot be assumed for an arbitrary rate having zeros. Definition4's R:Nat→[0,1] evaluated at real c2t is literally ill-typed mathematics; specify a real-domain extension or a rounding convention. For exponential R, floor/ceiling changes are absorbed by constants. For a pathological arbitrary nonmonotone R, different conventions need not be equivalent. None of these statistical repairs has a Lean implementation in this package.

### Nontriviality and randomized lower bounds

Theorem3's unqualified “best possible” reading fails for the fully admissible family consisting of repeated names for {0}: a constant correct learner has zero error for every valid distribution and positive sample size. This does not refute Theorem13, whose additional premise is k+1 **distinct extensional languages** sharing a string. The smallest headline repair adds that premise only to the optimal-lower-rate clause. The PaperMap roadmap acknowledges nontrivial collections, but the registry's statistical statement summary should carry the qualification.

Footnote9 does support the randomized extension after a small additional step. Choose full-support D_j on each of the k+1 languages with mass≥1/2 on the shared x; countability and nonemptiness permit such laws, including singleton cases. On the fixed prefix x^t the sum of randomized miss probabilities is at least one. Some j has conditional miss probability≥1/(k+1), and one fixed j does so infinitely often. Its unconditional error is at least 2^(-t)/(k+1). For all sufficiently large t this exceeds exp(−2t), since 2−log2>0. The infinite subsequence is unbounded, so the same target and law satisfy the stated infinitely-often lower bound. A lost factor at finite times therefore does **not** refute that theorem. This is an informal completion, not a claim that the printed indicator proof already covers random outputs.

## Coverage and remaining work

The verified full supplement still has all 491 declarations and all 29 expected modules (28 nonempty plus import-only umbrella), manifest `865b323d3ee3b6f36c1c1e067a3ee3e159ded9eba09b604c7113551865ad8a44`. This credits Algorithm1, Claim5.1, Theorems6–7, recursive Ψ, peeling, relative learners and decomposition, alongside shared deterministic/scalar support. The missing Section8 model and results cannot be repaired by adding a theorem_3 facade; canonical-family claims need their own combinatorics. Same-witness reuse and literal learner-valued decomposition are smaller native assemblies. Theorem9's strict probability threshold, computation-tree events, Top-k bridge, and full-support IID semantics also remain unformalized, with no stronger endpoint or effective guarantee inferred.

Minimal follow-up: correct pinned-edition locators and statistical nontriviality wording; document the local source construction repairs; separately scope formalization of canonical examples and the probability/rate branch. No source, Lean, PaperMap, registry, or frozen report was changed. Completion of this adjudication means all requested discrepancies were assessed, not that the entire paper is formalized or all proof questions have been certified. Standard external meanings are assumed; no new compilation, library-body review, theorem-proof audit, or human approval occurred.
