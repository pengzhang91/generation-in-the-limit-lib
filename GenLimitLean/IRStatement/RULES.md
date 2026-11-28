# Rules of the IR statement reader

The reader turns the full elaborated type of a Lean declaration into short controlled-English sentences. It then checks the English by parsing it back and comparing the result with Lean.

Each English construction is a rule of a [GF](https://www.grammaticalframework.org/) grammar (Grammatical Framework; [references](README.md#references)) with two renderings: an English one and a Lean one with the same slots. A reviewer checks rules, never individual readings. If every rule a reading uses is faithful, the reading is faithful, because the reading parses to exactly one tree and the kernel accepts that tree's Lean rendering.

[Readings](Readings/README.md) · [Rule cards](RULE-CARDS.md) · [File structure](STRUCTURE.md)

## Reproduce

Run these from the repository root. They need Lean, Lake, the repository dependencies and the GF binary (`GF_BIN`, `gf` on the path, or `local/tools/gf`).

```sh
python3 GenLimitLean/IRStatement/Scripts/reader.py         # P01 and its negative controls; writes no log
python3 GenLimitLean/IRStatement/Scripts/reader.py --all   # every paper, P00–P39 → Readings/RUN-LOG.md
python3 GenLimitLean/IRStatement/Scripts/glossary.py       # definitions of the labels → Readings/Glossary/
python3 GenLimitLean/IRStatement/Scripts/cards.py          # RULE-CARDS.md from the saved rule usage
python3 GenLimitLean/IRStatement/Scripts/pairs.py          # minimal pairs → MINIMAL-PAIRS.md
python3 GenLimitLean/IRStatement/Scripts/web.py --fetch    # web pages → Web/index.html, Web/Pxx.html
```

`web.py` shows each statement in three forms: the paper's statement, the IR statement and the Lean statement with its docstring. It builds a page only if a check log records a pass for the saved readings' exact bytes, and only if every quotation in [PaperStatements/](PaperStatements/) passes [quotes.py](Scripts/quotes.py): LaTeX quotations must occur in the arXiv source and their prose on the stated page of the PDF; plain-text quotations must occur on the stated page. A statement that is only a formula is placed by its number, printed within one page. `--fetch` downloads the arXiv and PMLR papers into `local/papers/`. P00, P00A, P26 and P27 are marked `supplied`: their PDFs are never downloaded and are copied by hand to `local/papers/Pxx/paper.pdf`. P00 and P00A are scans with no source: their quotations are transcribed from the scan, their words are checked against the scan's text layer (with listed OCR corrections), and their formulas are not checked; the page says so.

The two full runs, `reader.py --all` and `glossary.py`, also save which rules their checked texts use (`RULE-USAGE.json` next to each log) and rewrite [RULE-CARDS.md](RULE-CARDS.md) from both, so the cards count every reading and every glossary definition. The P01 command takes under a minute, `--all` about 10 minutes.

- `--write` regenerates the selected pages. It verifies the staged copies and publishes a page only if all of its readings pass. For every paper, a reading that Lean rejects is moved to the page's list of declarations without a checked reading, with the reason, and the rest is published.
- `--papers 03 05` processes only the papers listed and writes no log.
- `--page FILE` checks an edited copy of `Readings/P01.md` and writes no log.

## Current results

- 321 declarations in the `Results/Overview.lean` files of 35 papers (P00–P39). 320 have a checked reading; Lean rejects the reading of P21 `example_4_11`, which its page lists without one.
- 536 glossary definitions are checked the same way. A label that unfolding removes from a page leaves its glossary too.
- Every random tree comes back as the only parse of its own English (34,570 trees for the readings, 26,702 for the glossary).
- 153 of the 158 rules are used. 319 of the 320 statements on the web pages have a quotation checked against the paper; the other is a Lean-only helper.

## What is checked for every reading

1. The page is read from disk. Each section is split into its visible body and its declaration line, and the link is checked against the declaring line in `Overview.lean`. A body that begins with the mark *Setting A.* gets the text of Setting A in place of the mark (see "Throughout" below); everything after this step sees the full text.
2. The body is tokenized:
   - Adjacent tokens get `GLUE`, as in `o(t)`, `L_z` and `number,`.
   - A blank line becomes `PARA`, and bullets become `INMARK`/`NEXTMARK`/`OUTMARK`.
   - Any other spacing is rejected.
3. GF parses the tokens. The grammar is the shared rules plus a lexicon of names from this reading's Lean statement: its variables, oracle families, numerals and the labels of its constants. The lexicon contains names only, no wording.
4. Exactly one complete parse is required. It must equal the tree selected from the Lean export, and its rendering must equal the saved body.
5. GF renders the parsed tree as a Lean proposition P′, and `#check_statement <declaration> against (P′)` asks the kernel for definitional equality with the declaration's entire type.
6. Two kinds of control check the checker itself:
   - **Grammar regression.** About 100 random trees per reading (about 3,000 for P01) must each come back as the only parse of their own English.
   - **Negative controls.** For P01 Theorem 2.2, a copy of the reading is edited so that the threshold may depend on the sample.

## What a reviewer checks, and what needs no review

| Part | Review |
| --- | --- |
| The GF rules, shown as generated cards in [RULE-CARDS.md](RULE-CARDS.md), each with up to two real examples from the checked readings | **Yes, once per rule.** 153 of the 158 rules are used by the 856 checked texts: the 320 readings of P00–P39 and 536 glossary definitions. They are grouped into seven tiers by how much care they need. Sign a rule in [RuleTiers.tsv](Tables/RuleTiers.tsv). |
| The sentence frames in [Frames.tsv](Tables/Frames.tsv) | **Yes, once per row.** Read the label's glossary entry, which states the definition in the same sentence (see "Sentence frames" below). |
| The label algorithm (`label_words`, `labels`, `plural` and `VERBS`) | **Yes, once.** It makes the label of every constant mechanically, so its 422 constants need no review of their own. |
| The three formal devices in [Vocabulary.lean](Vocabulary.lean) | **Yes, once.** |
| `#ir_glossary` in [Glossary.lean](Glossary.lean) | **Yes, once.** It states the definition of a constant as a theorem proved by `Iff.rfl` or `rfl`; the glossary readings are checked against that theorem. |
| The Throughout substitution ([throughout.py](Scripts/throughout.py)) | **Yes, once.** It replaces a leading mark *Setting A.* by the text of Setting A. Nothing else. |
| The selector ([selector.py](Scripts/selector.py)), renaming ([Renaming.tsv](Tables/Renaming.tsv)), unfolding ([Unfold.tsv](Tables/Unfold.tsv), [Unfolding.tsv](Tables/Unfolding.tsv)), the choice of settings and layout | No. Whatever they produce is parsed back and checked by the kernel. A bad choice can make a reading fail or read badly, never wrong. |
| The pipeline: tokenizer, GF, `#check_statement` ([Check.lean](Check.lean)), the kernel | Trusted base, the same for every reading. |
| The quotations from the papers | No. [quotes.py](Scripts/quotes.py) checks that they are verbatim against the PDF and the LaTeX source. The formulas of P00 and P00A are transcribed from a scan and not checked. |
| Whether the IR statement says what the paper says | **Yes, per statement**, on the web page: the paper's words next to the IR statement. This checks the Lean formalization itself; the kernel has already tied the IR statement to Lean. |
## How to review

Once, for the tools. After this, every reading says what its Lean declaration says.

1. **Rule cards** ([RULE-CARDS.md](RULE-CARDS.md)). Each card shows the English and the Lean side of a rule; check that they mean the same. Sign the rule in the `reviewed by` column of [RuleTiers.tsv](Tables/RuleTiers.tsv). Start with the tiers *structure* (quantifiers, assumptions, lists) and *hidden* (omitted proof arguments and the like); *plumbing* only joins sentences. The five unused rules need no review.
2. **Frames** ([Frames.tsv](Tables/Frames.tsv)). For each row, read the start of the label's glossary entry and check that the added words name the right roles. Start with the twelve that add a verb or a math word (see "Sentence frames").
3. **[Vocabulary.lean](Vocabulary.lean).** Check that `increasingEnumeration`, `FirstTerms` and `depends_only%` say what their English says: “list the elements of A in increasing order”, {x(n) : n < t} and “depending only on …”.
4. **`#check_statement`** ([Check.lean](Check.lean), 38 lines). Check that it compares the declaration's entire type, and that it rejects a statement with holes or `sorry`.
5. **The label algorithm**, once, not label by label. The grammar fixes which constant a label names. But a label is only a name and can mislead; its glossary entry gives the definition.
6. **`#ir_glossary`** ([Glossary.lean](Glossary.lean)) and **the Throughout substitution** ([throughout.py](Scripts/throughout.py)).

Per statement, on the web pages. This reviews the Lean formalization itself, because the kernel has already tied the IR statement to Lean.

- Compare the paper's statement ("In the paper") with the IR statement.
- For an italic label, open its definition under "Definitions of the labels" (a label with a dotted underline links there) and compare it with the paper's definition under "Terms from the paper".
- The formulas of P00 and P00A are transcribed by hand; compare them with the scan.
- A short paper is a good start, for example P08 (2 statements) or P13 (7).

## Wording that still needs mathematical review

1. **Label conventions.**
   - "X is *label*" assumes that a one-argument predicate reads as an adjective. A label that begins with a word in `VERBS` drops "is".
   - A label can be awkward, for example "C is *no identification rate*". It cannot mislead about the arguments, because their order is Lean's or a frame's, and the kernel checks both.
   - The label of a constant says no more than its Lean name. Its meaning is the Lean definition, read in the glossary.
2. **Domain wording (P01).**
   - "the membership-query generator for O" and "the prompted membership-query generator for O with coding e" name the algorithms but do not describe them.
   - "at step t" should match the paper's indexing. The library's output at step t comes after the first t observations.
   - "O has a membership oracle" covers `query` and its correctness.
   - "the oracle confirms x ∈ L_i" means `O.query i x = true`. The equivalence with x ∈ L_i is not definitional and is not stated.
   - "*arbitrarily long extensions* in every L_i" stands for: for all i and n, some c with length at least n has p · c ∈ L_i.
3. **Types and universes.**
   - "a type" leaves its universe to Lean. Consecutive type binders share a sentence; Lean still gives each its own universe.
   - "a sort" means `Sort u`.
   - "a type in the lowest universe" means `Type`.
4. **Casts and arithmetic.** "↑X" is a cast to whatever type its context needs. "−" on ℕ is truncated subtraction.
5. **Agreement with the papers.** This is beyond the IR. For example, in P01 Theorem 2.2 the sample is any finite S ⊆ L_z with at least t_C elements, and in P01 Theorem 7.1 T may depend on the prompts.

## Limitations

- The rules were first written for P00–P15; P16–P39 needed ten more (see "How the rules carried over to P16–P39" below). A new paper may still need new rules. Until then the selector names what it cannot read, and the declaration is listed on its page without a reading.
- Readings lose instance arguments that the statement passes explicitly (`@dist _ inst`). Lean then rejects the reading; it is never accepted with the wrong instance.
- The dependency check (`depends_only%`) runs at elaboration, not in the kernel. Its trust is the same as the elaborator's.
- When a reading's structure is wrong, Lean sometimes reports the rejection while inferring a universe level rather than as a kernel mismatch. This happens in minimal pair 3. It is still a rejection.
- Random trees are a sample: they show no ambiguity was found, not that there is none.

## How the rules carried over to P16–P39

P16–P32 and P39, eighteen papers, were first read only after the rules for P00–P15 were fixed. This tested whether the rules carry over to new papers.

- **First run, rules unchanged.** 164 of 187 declarations passed (88%), and 12 of the 18 papers passed in full. Of the 23 failures:
  - 14 were declarations the selector could not build: an instance with two arguments (`FiniteDimensional ℝ E`), the type `L i`, a type constant applied to a number (`Fin 2`, `Lattice 1`, `Lattice (d+2)`) and a constraint on an element of a set (`↥S`).
  - 7 were elaboration errors: a missing cast (a `Finset` as the set argument of a label), `x ∈ K ∧ x ∉ l` written as K ∖ l when l is a list, a constant function whose argument type Lean could not infer, and `LetGe`.
  - 1 was a kernel mismatch and 1 an ambiguous parse.
- **No wrong reading was accepted.** Two weaknesses showed. First, “Let k ≥ 2.” left the type of k to Lean, and a later `1 / ↑k` made k a real number; this caused the kernel mismatch and one elaboration error. `LetGe`, `ForallAtLeast` and `ExistsGe` now bind k : ℕ explicitly. Second, a named term could be both a variable and a language family; the new rule `DefineFam` reads “Let F = …, with languages M_0, M_1, M_2, ….”
- **After the fixes,** all but one passed. Ten rules were added: `DefineFam`, `AssumeClassOver`, `TVarApp`, `TFin`, `TFinUpTo`, `TLblApp`, `TLblAppPlus`, `TMember`, `LamTy` and `FinsetSet`. The one left is P21 `example_4_11`, which passes an instance explicitly (see "Limitations"). The `Overview.lean` files have changed since; "Current results" has today's numbers.
- **The test has ended.** These papers now have unfolding decisions and paper names like the others, and every paper follows the same publication rule.

## Glossary: definitions of the labels

A label says no more than its Lean name. The glossary says what it means. For each library definition `c` named in a paper's readings, `#ir_glossary c` adds the theorem
`IRGlossary.c : ∀ x…, c x… ↔ body` (for a proposition), `c x… = body` (for data or a type), proved by `Iff.rfl` or `rfl`. Its type is read and checked exactly like a declaration's, so the reading of the right-hand side is definitionally the definition of `c`, unfolded once. The reading begins "By definition, …".

- Each glossary page is `Readings/Glossary/Pxx.md`; its check log is `Readings/Glossary/RUN-LOG.md`.
- A label keeps the wording it has on the paper's page. Constants that occur only inside definitions get labels by the same rule, with namespace components added until they differ from the page's labels.
- Only plain definitions qualify. Structures, classes, inductive types, structure projections and definitions by recursion or pattern matching are listed without a reading, with the reason. So is a definition whose reading Lean rejects.
- Mathlib constants (`Set.Infinite`, `Set.range`, …) are not in the glossary; they are standard notation.

## Throughout: shared settings

Several readings on one page often begin with the same sentences, for example "Let α be a type. Assume that α is *countable*. …". A page states such a run once, under "## Throughout", as "### Setting A". Each reading that shares it begins with the mark *Setting A.* instead.

- The mark is text substitution. The checker puts the text of Setting A in place of the mark, then parses and checks the full text. The kernel still compares the whole statement with the declaration's whole type.
- The mark may only open a reading. It is followed by a space when the reading goes on in the same paragraph, or by a blank line when it goes on in a new one.
- A setting covers whole leading sentences that begin with "Let", "Assume" or "Suppose", in plain paragraphs. It never covers a conclusion.
- `throughout.choose` picks the settings greedily by the text they save. A setting has at least 3 sentences, is shared by at least 2 readings and saves at least 200 characters; a page has at most 4. A reading uses at most one. These numbers are presentation only.
- The glossary pages have no settings. Readers jump to one definition at a time, so each definition stays self-contained.

## Labels of Lean constants

A constant appears in English as a label in italics, made from its Lean name by one fixed rule:
- Take the last name component and split it at capitals, underscores and digits. Lower-case each word except acronyms.
- `GenLimit.Generic.GeneratableInLimit` becomes *generatable in limit*, and `GenLimit.LiRamanTewari.UUS` becomes *UUS*.
- When two constants in one paper get the same label, both are prefixed with their namespace components until the labels differ. For example, *abstract identifiable* and *effective identifiable*.

Each page ends with a table mapping its labels to Lean constants. Arguments are shown in Lean's order, and implicit arguments are left to Lean:

| Use | English | Lean |
| --- | --- | --- |
| predicate with one argument | X is *label*, or X *label* when the label begins with a verb such as *has* | `c X` |
| predicate with several arguments | *label*(X, Y) | `c X Y` |
| predicate with a frame in `Frames.tsv` | a short sentence, e.g. X *achieves time vector* Z on Y | `c X Y Z` |
| function | *label*(X, Y), or *label* with no explicit argument | `c X Y`, `c` |
| type | a *label* over A and B | `c A B` |
| class instance | Assume that α is *label*. | `[c α]` |

A proof argument is not shown when it is an assumption in scope: *scheduler entry time*(f, i) stands for `schedulerEntryTime f (hf := by assumption) i`, and the assumption needs no name ("call this assumption hf" disappears). Another proof argument is not shown either when Lean proves it from the context: the exporter tries the tactic `first | assumption | linarith | positivity | simp_all +zetaDelta` on the argument's type, and only a proof it finds is hidden; the label then stands for `c (h := by …)` with that tactic. P17's *theorem six four orders*(1 − c) had a 400-word proof term before. Proofs do not change what a statement says (proof irrelevance), and the kernel checks the result. The label algorithm writes such a constant as `c#h` (`c#h!` for the tactic) internally; the page's label table shows `c`.

Negations of the commonest claims are written without “it is not the case that”: *label*(X, Y) does not hold (`¬ c X Y`), P(X) does not hold for a predicate variable, and A ⊈ B (`¬ A ⊆ B`). A claim ending in “does not hold” joins “and” and “or” like an atom, but no quantifier follows it, because “P does not hold for every x” could deny the quantifier.

**Sentence frames.** A predicate with several arguments can instead read as a short sentence, without unfolding its definition. `Frames.tsv` gives the sentence: `{label}` is the label in italics, `{1}`, `{2}`, … are the shown arguments in Lean's order, and the other words are plain lower-case words. For example, the frame `{1} {label} {3} on {2}` of `GenLimit.ParetoGeneration.AchievesTimeVector` turns *achieves time vector*(𝒢, 𝒞, t) into “𝒢 *achieves time vector* t on 𝒞”, and `{2} is {label} in {1}` turns *pareto optimal*(N, t⋆) into “t⋆ is *pareto optimal* in N”. Each frame becomes one lexicon entry: English puts the arguments in the slots, and Lean applies `c` to them in its own order. The kernel check therefore covers which argument goes where. What it cannot check is whether the added words suit the roles: “on 𝒞” must name the collection, not the generator. To check that, read the label's glossary entry, which states the definition in the same sentence with the definition's parameter names (“By definition, G *achieves time vector* time on F if and only if …”). A frame applies only when the number of shown arguments matches. The frame's own words are plain lower-case words; the grammar's connectives and quantifier words (and, or, not, if, every, some, holds, the, …) are not allowed, so a frame cannot look like logic. A negated frame with a copula before the label reads “X is not *label* for Y” (“are not”, “does not have” for “has”): the same lexicon entry with `¬` in Lean. Like “does not hold”, it joins “and” and “or” but takes no trailing quantifier. Other negated frames read “it is not the case that …”.

`Frames.tsv` has 174 frames for P00–P39. One model per four to six papers proposed them from a shared brief, reading the paper (the TeX source or PDF) or the Lean docstrings; a script checked each row's form and showed the glossary heading and every use rewritten. Most frames add only role words (for, is, has, with, under, of, on, a, at, from, in, given, to, using, relative, by, against, than). 53 also add a word that names an argument's role (rate, threshold, list size, noise level, radius, slack, …). Twelve add a verb or a math word and deserve the closest look: *approximate breadth in limit* and *sample allowing infinite coverage* (“generates with”), *exponential breadth* (“achieves”), *valid index* and the two “on injective” labels (“gives”), *QECTT*, *k angluin condition* and *vanishing noise dense set condition* (“satisfies”), P14's *exponential* (“identifies … at *exponential* rate”), *difference represented* (“minus”) and *distance dominated by* (“times”).

Labels carry no meaning that the Lean name does not. A label can be awkward, for example "C is *no identification rate*", but it cannot be unfaithful, because it is just the constant's name. A frame adds a few words, mostly role words such as “on”, “in” or “at”. These words are what a reader checks against the label's glossary entry, one row per label.

## Scope and layout conventions

These conventions are part of the structure rules. Their cards say what to check.

- A sentence that introduces something ("Let x ∈ ℕ.", "Suppose that P.", "Let G = …") is in force for the rest of the text, or for the rest of its bullet.
- "There is T ∈ ℕ, depending only on O, x and z, with the following property." chooses T, and the rest of the text is the property. Lean checks the dependency list against the variables in scope. When the property is a list, the choice reads "… with the following properties:" and the bullets follow.
- The dependency list is shown only when the property opens with a variable of its own: a "Let" sentence or a leading "for every", possibly after local definitions and assumptions. A variable introduced inside a bullet or a later clause is plainly introduced after the choice. Then the reader sees that T does not depend on it. Otherwise T may depend on everything above, and the sentence is "There is T ∈ ℕ with the following property.", or, when the property is one simple claim, "There is T ∈ ℕ such that …".
- "All of the following hold:" is followed by a bullet for each conjunct. "The following are equivalent:", "At least one of the following holds:" and "Exactly one of the following holds:" are followed by two bullets.
- "for every x ∈ S" after an atomic claim covers only that claim. Before a claim, it covers all of it.
- "Let t ≥ T." and "for every t ≥ T" bind a natural number t, and so do "for every i < n" and "there is i < n such that".
- Notation: (x, y) is a pair, [x, y] a list, () the element of the one-point type, {0, …, k − 1} is Fin k, ⟨x⟩ is x as an element of a subtype, "a member of S" is an element of the set S as a type (↥S), "the set F" is a finite set F as a set, and (x ∈ T ↦ Y) is a function whose argument Y does not use (or uses only under a coercion), so its type is shown.
- "Let F = …, with languages M_0, M_1, M_2, …." names a family of languages given by a formula; M_i is its i-th language.
- Brackets mark compound operands and compound left conjuncts, and "and" and "or" never mix without brackets.
- Introductions share a paragraph. Each choice and each run of assumptions starts a new one.

## Formal vocabulary

- `IRStatement.increasingEnumeration A h` is the least element of `A`, then repeatedly the least element above the previous one. The kernel identifies it with `GenLimit.KM.FiniteFamily.enumerateAccepted O C S h`. The elaborator's `rfl` does not prove that equation.
- `IRStatement.FirstTerms.firstTerms s t` stands for {s(n) : n < t}. It is `GenLimit.sample` for ℕ-valued streams and `GenLimit.Generic.sample` otherwise.
- `depends_only% [x, …] P` checks at elaboration that the listed names are exactly the variables in scope. Hypotheses, instance arguments and local definitions are not counted. The check leaves nothing in the term.

## Choices that are presentation only

- **Renaming** ([Renaming.tsv](Tables/Renaming.tsv)): stream → x, members → C, tC → t_C, prompts → p, time → t (with its fresh copies time_1 → t_1). A renaming is skipped in a statement where the new name is taken. This is α-equivalence.
- **Names as in the paper** (rows of [Renaming.tsv](Tables/Renaming.tsv) with a `paper`; P01–P39 have them, 175 rows): for one paper, a variable gets the paper's name (P13: F → 𝒞, G → 𝒢; P09: α → 𝒳, H → ℋ), and a named term headed by a given constant gets the paper's symbol instead of its first letter (P13: t⋆, m⋆). This only helps reading the IR next to the paper; it does not claim that the objects are the paper's, and the reading still says what each name stands for. A name that is not a plain identifier (t⋆, 𝒞, and Σ or 𝒫, which are Mathlib notation) is written «…» in Lean, which is the same identifier.
- **Unfolding** ([Unfold.tsv](Tables/Unfold.tsv)): 10 definitions are shown by their bodies in every paper, and the kernel checks each unfolding. The local word *robust* names one of them.
- **Unfolding by paper** ([Unfolding.tsv](Tables/Unfolding.tsv), [unfolding.py](Scripts/unfolding.py)): one decision per paper and constant, `unfold` or `keep`. The rule: keep the paper's own terms; unfold what only Lean names when its body is short; keep long bodies. A row may cite the paper with a verbatim TeX quote and its page; `reader.py` checks each citation against the downloaded PDF and source and stops if one fails. A `keep` that rests on "this is the paper's term" must cite it. P02–P39 have decisions: 603 rows, 155 `unfold` and 448 `keep`; 403 rows cite the paper. P13 was the first trial: each of its 19 candidates was unfolded alone and checked, then decided from the paper (9 `unfold`, 10 `keep`). Its seven readings grew from 538 to 717 words but used 23 distinct labels instead of 29. The rows for the other papers were proposed by one model per few papers from the paper itself, given the rule, the word change of each unfolding and the P13 example; every citation passed the check, and a decision whose reading Lean could not elaborate again was changed to `keep`. P09 and P11 were decided before their PDFs were here, and P26 and P27 have no LaTeX source, so their rows cite nothing. The web page lists the decisions under "Definitions shown by their bodies".
- **Placement:** a definition such as a generator G, a set A or a sequence o(t) appears as soon as its ingredients are in scope. This shows that it does not use what comes later.
- **Grouping:** consecutive binders of one type share a sentence, consecutive choices share a sentence, and consecutive assumptions share a paragraph. Consecutive type binders share a sentence too ("Let A and B be types."). Lean gives each binder of `∀ (A B : Type _)` its own universe, so the grouping does not merge universes.
- **Named terms, extended:** an unfolded application is named like a label application ("Let S = (i ↦ *max*(…)).", Lean `let S := fun i => …`), and once K names c(x), an application c(x, i) reads K(i) (Lean `K i`, reduced by the kernel).
- **Universal bullets:** a bullet that is one universal claim over a simple claim reads "P for every x ∈ T", not "Let x ∈ T. Then P."
- **Named terms:** a label application used several times gets a one-letter name, "Let K = *carrier*(O(z)).", introduced as soon as its variables are in scope. The Lean side is `let K := …`, which the kernel unfolds (ζ-reduction), so the check covers it. A term is named when it occurs at least twice and naming saves about 20 characters, and only if each of its variables is bound once in the statement. The letter avoids every name used in the paper's other readings.
- **Hidden proofs:** when a proof is passed to a term, its hypothesis is named: "Suppose that P, and call this assumption h." The P01 rules omit the name when the rule reconstructs the proof itself.

## Origins

This reader was written after earlier GF readers of this project, which are not in this repository. Three pieces come from them: `#check_statement` ([Check.lean](Check.lean), with only its namespace renamed), and the GF runner and the inventory of each paper's results ([runner.py](Scripts/runner.py), cut down to what this reader uses). The exporter, the grammar, the selector and the label algorithm are new; they replace the earlier per-statement vocabulary tables.

An earlier reader's P01 Theorem 2.2 says “There exists a natural number tC with the following property.”, so that the threshold does not depend on the sample follows only from the sentence order. Here the sentence says “depending only on O and C”, and Lean checks it. The phrase “in increasing order” may come from that earlier grammar.
