# P00 independent source inventory (Stage 2, before Stage 1 access)

## Identity, ordering and scope

E Mark Gold, *Language Identification in the Limit*, Information and Control 10 (1967), printed pp. 447-474; DOI 10.1016/S0019-9958(67)91165-5. Received February 20, 1967 (printed p.466/PDF20). Pinned PDF SHA256: `a15cdcfe84d79ceb6b5a01bdd040948a04adb533c9afc8670ff191f474097693`. One edition only; all 17 original claim slots inventoried individually. PDF page numbers below are one-based; PDF p = printed p - 446.

Source-only phase began 2026-11-13 23:42:14 UTC (first clock reading, after opening the Stage 2 prompt). Scope index, source README/manifest, identity extraction and complete 28-page marked source text were read before this inventory. The full source text includes the introductory conventions, all definitions, remarks and interpretive proof text, both appendices and references. Formula/layout checks used base-page raster images extracted losslessly from PDF CCITT page images, converted by macOS sips: PDF3,4,12,16,17,18,19,25,26,27 (printed449,450,458,462,463,464,465,471,472,473). Poppler and PyMuPDF unavailable; a Swift/PDFKit attempt stalled and was terminated, without producing evidence. No annotations were used. The manifest reports zero annotation objects.

**Ordering attestation:** This inventory is being written and hashed before any Stage 1 output, code-only Lean evidence, developer explanation, PaperMap, registry assessment, prior audit, owner material or Stage 3 context is opened. Only source metadata is treated as provenance, never mathematical evidence. Inventory save time is appended programmatically below. The initial wrong-path attempt `P00/claim-index.json` returned file-not-found; the actual scope input is `P00/stage2/claim-index.json`.

## Standing source assumptions and semantic model

- Printed pp.448-451/PDF2-5: one fixed finite nonempty alphabet A; language means a subset of all finite strings over A. Time starts at 1. A guessing rule takes the finite information prefix through t and returns a language name. A class is effectively identifiable iff there is ONE effective guessing algorithm such that FOR EVERY target in the class and EVERY allowed presentation, there exist a fixed correct name and a finite stabilization time after which ALL outputs are that same name. Name/time can depend on target and presentation; the learner cannot depend on them. No bound on stabilization time, error count or computation time is asserted.
- Printed pp.450-451/PDF4-5: a text is a total sequence of actual target strings whose range is exactly the target, with arbitrary repetitions. Variants require the sequence function to be arbitrary, recursive or primitive recursive. There is no explicit pause/blank symbol. Thus an empty language has no text as literally defined; any universal presentation condition on it is vacuous unless a convention repairs this.
- An arbitrary informant supplies truthful (string,membership) observations, covering every string at least once; a methodical informant uses a fixed a priori enumeration; a request informant answers learner-selected strings chosen from preceding observations. A request strategy need not enumerate every string unless the strategy chooses to. Equivalence of presentation methods means equality of identifiable classes for EVERY naming relation (p.451/PDF5), not equality of sequences or a fixed time bound.
- Tester names are Turing machines computing the total characteristic function (1 in target, 0 outside). Generator names are machine indices whose computed sequence/function has target range; the wording varies between total-sequence language on pp.451,474 and partial number-theoretic functions in Section11. Effective index translations, not arbitrary extensional maps, matter. Primitive recursive languages have primitive recursive characteristic functions; recursive languages have total effective decision procedures; r.e. languages have effective generators (AppendixII p.474/PDF28).
- Printed pp.456-458/PDF10-12 abstract model: objects O, observations I, names N with interpretation f:N->O, allowed sets I-infinity(o) of infinite information sequences. Finite-prefix compatibility means there exists an allowed continuation for the candidate object. Distinguishability says no one sequence is allowed for distinct objects. Collapsing uncertainty says every distinct rival is excluded by some finite observed prefix (and hence by all later prefixes); the exclusion time may depend on rival and observed sequence.
- Printed p.457/PDF11: ineffective identification drops ONLY algorithmic effectivity of the guessing function. Every object must have a name for naming-independence. Printed p.458/PDF12 explicitly assumes henceforth I and O countable and every object named. No nonempty-presentation condition is explicit. Enumeration is a surjection from positive integers onto objects, possibly with repetitions, with a chosen name for each enumerated object.
- Identification by enumeration (p.458/PDF12) guesses the first enumerated object compatible with all information so far. It is effective only when compatibility is uniformly effectively testable on (prefix,index), and a name is uniformly effectively obtainable from the index. Pointwise decidability or an arbitrary choice function is insufficient.
- Superfinite (p.452/PDF6) means a class contains ALL finite languages and AT LEAST ONE infinite language. It does not mean every class containing some finite languages, nor every class containing an infinite language.
- Section11 (pp.463-465/PDF17-19) recodes strings by a recursive bijection with positive integers; AppendixI (p.467/PDF21) explicitly requires a primitive recursive bijection in both directions where primitive recursion matters. Section11 names are positive integer machine indices. Translation is a partial function defined correctly on every valid source name in its domain class. Limiting recursive means a single TOTAL RECURSIVE approximation g(n,t) eventually constant to f(n) wherever f is defined; outside the domain no required stabilization. 2-recursive means its graph/representing predicate is 2-r.e. in the Kleene hierarchy, cited as equivalent to limiting recursion. Domain generator means halting domain is L, anti-domain generator means halting domain is complement L.
- All scoped claims are deterministic and universal over presentations. There is no sampling distribution, probabilistic loss, statistical risk or quantitative convergence rate. The p.461/PDF15 probabilistic suggestion is speculative and does not modify any scoped theorem.

## Individually scoped source assertions

### C01 — Theorem 7.1, printed458-459/PDF12-13

Under countable I and O and a name for each object: (a) ineffective identification implies distinguishability; (b) collapsing uncertainty implies ineffective identification, specifically the first-compatible guessing rule works for EVERY surjective object enumeration (including repetitions); (c) if each allowed-presentation set I-infinity(o) is countable, distinguishability implies ineffective identification. The last clause can first identify the countable presentation sequence class and then translate to its unique object and a name. It is not a claim that distinguishability alone implies identification without the countable-presentation hypothesis, nor that collapsing uncertainty is necessary. It is not an effective characterization. Quantifiers: existence of one semantic learner precedes all target/presentation quantifiers; in (b), each chosen enumeration yields a successful learner.

### C02 — Section8 Language Identifiability, second paragraph, printed460/PDF14

Every countable class of named languages is INEFFECTIVELY identifiable from recursive text, and separately from primitive recursive text. Countably many allowed texts can first be identified by enumeration; text range uniquely determines the language. No effective learner or effective text/name translation is promised, and no computable uniform enumeration of all total recursive texts is asserted. Languages with no allowed text (in particular literally empty target) impose no obligations.

### C03 — Section8 Language Identifiability, first paragraph, printed460/PDF14

Every countable class of languages, each with at least one name, is INEFFECTIVELY identifiable from arbitrary informants, using identification by enumeration, because truthful exhaustive informants collapse uncertainty. Countability belongs to the class, not to its generally uncountable set of arbitrary presentations. No effective enumeration/name map or learner is promised.

### C04 — learning-time Theorem10.1, printed461-462/PDF15-16

Fix an abstract identification situation satisfying collapsing uncertainty, an enumeration (duplication allowed), and its enumeration learner G0. No guessing rule G, even ineffective, uniformly improves G0's stabilization time: it is impossible that for ALL valid target/presentation pairs tau(G)<=tau(G0) and for SOME pair tau(G)<tau(G0). tau is the first time t>=1 from which all guesses are the same correct NAME; tau=infinity if there is none. Thus if G is strictly earlier on one pair, there is another valid pair where G0 is strictly earlier. Source remark says the proof still holds without global identification by G0, provided each allowable finite prefix has an enumerated compatible object. This is Pareto minimality in learning time, not pointwise fastest performance or a computational-runtime guarantee. The remark refers to Theorem9.1 although the displayed result is10.1; preserve as a numbering question.

### C05 — TheoremI.6, printed469/PDF23; Section7 restatement printed459/PDF13

The class of ALL finite languages is EFFECTIVELY tester-identifiable from arbitrary positive text. The specific learner guesses exactly the finite set of examples observed so far, using an effective procedure to obtain a tester for that set; it eventually uses one fixed correct tester after all elements have appeared. The same learner must handle every finite target and arbitrary presentation. The semantic set output alone is weaker than this code-index guarantee; order-dependent choices of infinitely changing tester indices would not suffice. Empty-target text is absent in the literal source model.

### C06 — Section8 third paragraph, printed460/PDF14; surrounding Section9 printed460-461/PDF14-15

For arbitrary text, ineffective identification has the same dividing line as effective identification: all finite languages are identifiable; EVERY PROPER SUPERCLASS of the class of all finite languages is not. Equivalently the finite class is maximal under inclusion among learnable classes containing it, not a greatest learnable class containing every learnable family. Both the positive finite-class component and the semantic superfinite impossibility are in scope. Names must exist where a positive identification claim is made; negative result is semantic (no arbitrary learner), not merely failure of effective learners.

### C07 — CorollaryI.2, printed466-467/PDF20-21

For ANY method of information presentation and any language class, failure of EFFECTIVE generator identification implies failure of EFFECTIVE tester identification. This contraposes the effective tester-to-generator index translation theorem, including stable-name convergence and all allowed presentations. It is not a theorem that arbitrary chosen generator/tester naming interpretations are intertranslatable.

### C08 — TheoremI.3, printed467/PDF21; definitions450-451/PDF4-5

Arbitrary, methodical and request informants are equivalent presentation methods in the sense that EVERY naming relation gives the same identifiable classes. Three effective simulations are described: arbitrary->methodical is restriction; methodical->request asks the fixed enumeration; request->arbitrary waits until the currently desired observation appears, repeating intermediate guesses as necessary, then advances the simulated interactive learner. Exhaustive arbitrary informants ensure each wait finishes. The claim preserves existence of effective learners and eventual fixed correct names, without a time bound. Any semantic analog is a separate weakening of the effectivity guarantee.

### C09 — naming-translation Theorem10.1, printed463-464/PDF17-18

For the same class and information presentation, EFFECTIVE N1-identification plus a LIMITING RECURSIVE partial translation from every valid N1-name to a correct N2-name implies EFFECTIVE N2-identification. With a single total recursive approximation g(n,t) and source learner G1, the constructed output at time t is g(G1(prefix_t),t). It eventually stabilizes because G1 becomes one correct fixed name and that name's translation approximation becomes fixed. Source numbering repeats10.1 from Section10; location distinguishes them. Mere eventual correctness of a noncomputable array would establish a semantic variant only.

### C10 — Corollary10.1, printed464/PDF18

**Literal printed claim:** for every class C containing all finite languages and at least one infinite recursive language, there is no LIMITING RECURSIVE translation from TESTERS for C to GENERATORS. This direction has been visually verified on PDF18. It conflicts with the explicit effective tester->generator translation on p.451/PDF5 and AppendixI TheoremI.1 p.466/PDF20, and with the preceding use of differing learnability powers. Do not silently reverse it. A likely intended generator->tester statement is a Stage3 source-correction question, not the literal inventory. Class C need not consist wholly of recursive languages; only the witness infinite recursive language is explicitly demanded. Translation domain is all valid tester indices naming members of C.

### C11 — Theorem10.2, printed465/PDF19; definitions463-465/PDF17-19

For every class C containing all finite languages and at least one infinite RECURSIVE language, no 2-recursive partial translation takes every domain-generator name for a member of C to an anti-domain-generator name of the SAME target (a domain generator of its complement). This is uniform index complementation, not complementing a set abstractly. 2-recursive is the graph hierarchy notion, identified in the text with limiting-recursive functions. A cited upper bound is a 3-recursive translation for the class of recursive sets (Section11 introduction), but it is contextual and not a separate claim slot here. Proof invokes the suspect Corollary10.1 and a 'given both domain and anti-domain generators, find a generator' statement that warrants Stage3 scrutiny: their stated generator-versus-tester direction should not be repaired silently.

### C12 — TheoremI.4, printed467-468/PDF21-22; Section7 restatement459/PDF13

The ENTIRE class of primitive recursive languages is EFFECTIVELY tester-identifiable from a methodical informant. A fixed uniformly total recursive enumeration of unary primitive recursive functions is thresholded to enumerate characteristic functions; candidate agreement on every observed bit is uniformly decidable; a total recursive compiler maps candidate index to a tester. The first compatible index learner is effective and converges to one fixed correct tester. Requires one uniform enumeration/compiler, not pointwise computability alone.

### C13 — TheoremI.5, printed468-469/PDF22-23

The ENTIRE class of recursive languages is NOT EFFECTIVELY generator-identifiable from methodical informants. Proof context begins with any effective rule successful on all finite and cofinite targets, builds a recursive methodical membership-bit sequence, and forces infinitely many name changes. This does not claim semantic nonidentifiability (the recursive class is countable and C03 applies). Target/presentation can depend on the proposed effective learner.

### C14 — TheoremI.7, printed469-470/PDF23-24; Section7 restatement459-460/PDF13-14

The ENTIRE class of r.e. languages is EFFECTIVELY generator-identifiable from primitive recursive text. Identify the text function via first-compatible enumeration of primitive recursive functions, then effectively compile its index to a generator with the same range. Quantifiers are one effective learner for every r.e. target and every primitive recursive presentation; fixed correct generator name may depend on the presentation, including different primitive recursive enumerators for the same language. It does not identify r.e. languages from all recursive texts. Empty-target total text caveat applies.

### C15 — TheoremI.9, printed471-473/PDF25-27

ANY superfinite class is NOT EFFECTIVELY tester-identifiable from primitive recursive text. The source allows any infinite witness L and says if it is nonrecursive it has no tester, otherwise use a primitive recursive range enumeration f of L. The diagonal construction is scoped: after replacing a computable guessing functional by a primitive recursive approximation with the same limiting behavior (cited Gold1965), maintain X_t and output i_t; P_t means f(X_t) has already appeared, Q_t means a bounded computation witness y<=t shows current tester guess rejects f(X_t). Start X_1=1 and i_1=f(1). Advance X when P; produce f(X) when not P and Q; otherwise repeat the preceding output. Both the primitive recursiveness of this generated text and its eventual failure of stable correct testing matter. Cases can yield a finite target or the infinite L; no semantic impossibility is claimed. Proof text pp.472-473 case II visually reads an x OUTSIDE the finite produced range with Z_a(x)!=0; OCR corrupts its membership signs. This is not a reason to change the theorem statement.

### C16 — TheoremI.8, printed470-471/PDF24-25

ANY superfinite class is NOT EFFECTIVELY generator-identifiable from recursive text. Source proof reduces the infinite witness L to r.e. (otherwise no generator), chooses a recursive injective enumeration a_1,a_2,... of L, then effectively constructs a repetition-rich recursive text forcing different correct guesses for growing finite initial target sets at arbitrarily late stages. One learner is refuted by a recursive presentation chosen from its behavior. This is not primitive-recursive-text generator impossibility, and not a noncomputable-learner impossibility. The source's assertion that an unnameable/nonpresentable infinite target makes the result immediate needs attention under the literal total-text convention; no resolution imposed here.

### C17 — TheoremI.1, printed466/PDF20; naming discussion451/PDF5

For ANY presentation method and language class, EFFECTIVE tester-identification implies EFFECTIVE generator-identification. A single recursive translation of correct tester indices to generator indices is composed with the learner; fixed-name convergence is preserved. This covers the actual machine-based naming relations uniformly, not just an arbitrary semantic transfer supplied as a hypothesis. The all-finite/empty-language conventions and partial-versus-total generator convention may affect the literal implementation of a uniform translation, so these remain visible boundary questions.

## Source questions reserved for Stage 3

1. Corollary10.1 p.464/PDF18 literally has tester->generator, conflicting with p.451 and I.1; likely direction error, but no correction is adopted.
2. Section11 theorem/corollary numbering reuses10.1 despite Section11; learning-time remark references9.1. Identity must include printed/PDF pages.
3. Literal texts have no blank, so empty targets have no text; generator total/partial conventions vary. Some negative-result 'otherwise immediate' reductions deserve explicit convention checking.
4. C06 asserts maximality over proper superclasses, not that every arbitrary-text learnable class consists only of finite languages.
5. TheoremI.9 relies on an external primitive-recursive guessing-functional replacement theorem. Its proof is not independently certified here.

## Input hashes and save record

Inventory saved at UTC: 2026-11-13T23:47:14.223533+00:00

- `P00/stage2/PROMPT.md`: SHA256 `c19584fc8895ad9208a686614365c7244ae3dee42df9b28b98c68ddad1fa28dc`
- `P00/stage2/claim-index.json`: SHA256 `ea2eb94b9fef3570e4db71eecd8012bbabd3214bbb151f1321e81e0c17ffa5c6`
- `sources/P00/README.md`: SHA256 `5f093147c0d583b4f58bebda7cb9ba013edc673526e61913eab1faf44b19cde2`
- `sources/P00/SOURCE_MANIFEST.json`: SHA256 `c5a645d6c49b6d49a4550679caf1bdadc630f594aaa37ab8b9dd887f2fbc6480`
- `sources/P00/information-and-control-1967/first-page-identity.txt`: SHA256 `94bbbdf1dcaaa9aab1cf630387557a15512823f0f7dc9bb932ffae58fb0a9678`
- `sources/P00/information-and-control-1967/page-marked-text.txt`: SHA256 `d4795365a53e00490f859b405338d5e032bad33068d3acfaad24cb72b31cda52`
- `sources/P00/information-and-control-1967/source.pdf`: SHA256 `a15cdcfe84d79ceb6b5a01bdd040948a04adb533c9afc8670ff191f474097693`
