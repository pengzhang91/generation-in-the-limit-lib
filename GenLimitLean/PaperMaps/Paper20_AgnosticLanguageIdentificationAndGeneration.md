# Paper 20 · Agnostic Language Identification and Generation

Høgsgaard and Pabbaraju's November 7, 2026 edition has nine main theorems and one corollary in Sections 2 and 3. Each has an explicit statement and a proof in the public Lean module. Section 1 presents five informal summaries of these results. [Paper, arXiv v4](https://arxiv.org/html/2601.23258v4) · [Results/Overview.lean](../GenLimit/Paper20_AgnosticLanguageIdentificationAndGeneration/Results/Overview.lean)

## Main results

| Paper | Lean endpoint | What the proof establishes |
|---|---|---|
| Theorem 2.1 | `theorem_2_1` | When some language attains optimal risk, Algorithm 1's probability of returning a suboptimal language and its expected excess risk are eventually at most $2f(n)\exp(-n/(2f(n)^2))$, for every diverging window $f$. |
| Theorem 2.2 | `theorem_2_2` | Two languages with private strings force expected excess risk at least $\exp(-5n)$ infinitely often for one distribution with an attained optimum, even for randomized identifiers. |
| Theorem 2.3 | `theorem_2_3` | For a fixed countable family of infinite languages, every randomized identifier and every rate $R\to0$ admit a distribution with unattained infimum and excess risk at least $R(n)/8$ infinitely often. |
| Theorem 2.4 | `theorem_2_4` | A supported tell-tale for an optimal language gives Algorithm 2 an eventual minimal-identification failure bound $cf(n)\exp(-dn/f(n)^2)$, with $c,d>0$. |
| Theorem 2.5 | `theorem_2_5` | A fixed family has tell-tales for every language. For each deterministic identifier, a distribution has an optimum, has no optimal supported tell-tale, and gives liminf probability of minimal identification at most $1/2$. |
| Theorem 3.1 | `theorem_3_1` | For every randomized generator and positive $\varepsilon$, a fixed infinite-support law has generation error at least $1-\varepsilon$ infinitely often. |
| Theorem 3.2 | `theorem_3_2` | Algorithm 3 achieves error at most $c\exp(-dn)$ when the support contains a candidate and the candidate family has finite witness index. |
| Corollary 3.3 | `corollary_3_3` | A finite family of infinite languages has finite witness index. The exponential guarantee follows for the same Algorithm 3. |
| Theorem 3.4 | `theorem_3_4` | For a fixed family and ambient enumeration, every deterministic generator has a distribution whose support contains a candidate, whose witness index is infinite, and whose limsup error is at least $1/2$. |
| Theorem 3.5 | `theorem_3_5` | If two languages have finite intersection and omit a common outside string, every randomized generator has one distribution containing a candidate in its support and giving error at least $\exp(-2n)/4$ infinitely often. |

## Reading the statements

The model uses Core's indexed language families and finite-history learners, the shared finite tell-tale predicate, and ordered IID samples from a discrete probability mass function. Repeated observations contribute to empirical error. Randomized algorithms are kernels from the observed list to a probability mass function. Weak identification measures expected excess risk. Minimal identification measures the probability of failing to output an inclusion-minimal optimum. Generation requires a word in the distribution's support that is absent from the training list. [Model.lean](../GenLimit/Paper20_AgnosticLanguageIdentificationAndGeneration/Model.lean)

Families use zero-based indices and may repeat languages. Algorithm 3 inherits each language's word order from one enumeration of the whole universe. Equation (9) is represented by existence of a common finite prefix length that reveals an outside-support word in every unsupported language. Its negation expresses an infinite witness index. Algorithms 1–3 are classical functions with the paper's selection rules. The statistical theorems use semantic access to language membership and tell-tales. The source's query implementations and runtime discussion are outside this inventory. [IdentificationUpper.lean](../GenLimit/Paper20_AgnosticLanguageIdentificationAndGeneration/IdentificationUpper.lean) · [GenerationUpper.lean](../GenLimit/Paper20_AgnosticLanguageIdentificationAndGeneration/GenerationUpper.lean)

Informal Theorems 1.1 and 1.3 use the phrase “for any $g(n)=o(n)$.” The declaration `identification_sublinear_exponents` constructs a single window from $g$ that gives both upper bounds uniformly in the language family and sampling law. The lower bounds retain the precise family hypotheses and exponential constants of Sections 2–3. Informal Theorems 1.2, 1.4, and 1.5 correspond to 2.3, 3.1, and the finite-family generation bounds 3.3 and 3.5. [SublinearRates.lean](../GenLimit/Paper20_AgnosticLanguageIdentificationAndGeneration/SublinearRates.lean)

## Proof choices

- **2.3.** A finite-block argument flips labels unseen by the training sample. Baire's theorem selects a single infinite labeling that witnesses infinitely many hard sample sizes. The Lean conclusion allows every real-valued rate tending to zero, including the paper's rates in $(0,1)$. [UnseenLabels.lean](../GenLimit/Paper20_AgnosticLanguageIdentificationAndGeneration/UnseenLabels.lean) · [SlowIdentification.lean](../GenLimit/Paper20_AgnosticLanguageIdentificationAndGeneration/SlowIdentification.lean)
- **2.5.** Equation (4) requires an attained optimum. Lean takes a descending chain in which all risks are zero and no optimum is inclusion-minimal. Every language has a singleton tell-tale outside the common support. This proves the stated existential obstruction with failure probability one. The appendix uses a different family and proves failure in an instance with a minimal optimum. [MinimalLower.lean](../GenLimit/Paper20_AgnosticLanguageIdentificationAndGeneration/MinimalLower.lean)
- **3.1 and 3.4.** Finite-sample event probabilities vary continuously along geometrically weighted streams. Preserving a bad event while extending a finite prefix yields one limiting distribution. In 3.4, an infinite walk includes an entire row or all row starts. Auxiliary languages make the witness index infinite in the same distribution. The underlying 3.4 proof also works for randomized generators. [GenerationDiagonal.lean](../GenLimit/Paper20_AgnosticLanguageIdentificationAndGeneration/GenerationDiagonal.lean) · [InfiniteIndex.lean](../GenLimit/Paper20_AgnosticLanguageIdentificationAndGeneration/InfiniteIndex.lean)

The registry records kernel checks for these ten statements. Independent human correspondence review is pending.
