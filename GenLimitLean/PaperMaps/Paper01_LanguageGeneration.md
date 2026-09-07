# #01 Language Generation map

Lean module: `GenLimit.Paper01_LanguageGeneration`.
Declaration namespaces retained for API compatibility include `GenLimit.KM`
and `GenLimit.OracleFamily`.

Main declarations:

- semantic: `GenLimit.KM.Semantic.kleinbergMullainathan_main`;
- NeurIPS proceedings finite-query:
  `GenLimit.OracleFamily.kleinbergMullainathan_main`;
- arbitrary-universe transport:
  `GenLimit.KM.Transport.kleinbergMullainathan_main_of_equiv` and
  `GenLimit.KM.Transport.kleinbergMullainathan_main_countable`;
- finite-set interface for arbitrary exact presentations:
  `GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface_with_repetitions`.

Canonical source edition: the NeurIPS 2024 proceedings. The audited
proceedings PDF has SHA-256
`4b29159d3d11506fa8f92f38e4dfe234f209a730f786de7ef6c577f7e34b0745`.
An earlier arXiv-v1 algorithm was once formalized as a separate variant, but
it is no longer part of the active library or claim inventory. Its immutable
audit evidence remains as a historical snapshot.

Audit records: the semantic path's Level 3 human review and the observed-set
path's ChatGPT Pro check are indexed in the
[authoritative human-audit ledger](../AuditRecords/Human/README.md). Detailed
ChatGPT Pro provenance and immutable historical evidence, including the
retired arXiv-v1 variant, live in the
[#01 audit record](../AuditRecords/Paper01_LanguageGeneration/).

The #01 Language Generation development depends on `GenLimit.Core` and does
not import the #39 Dense Generation development or any cross-paper bridge.
There is no separate `Results/Overview.lean`: the active formalized paper
surface is one headline theorem exposed through several implementation
interfaces, so the paper umbrella itself is the public facade. This should be
revisited if Theorem 2.2 or Theorem 7.1 is added.

## Formalization boundary

The three `ℕ`-based paths below cover the countable-family
generation-in-the-limit result (Theorem 2.1), its Section 4 semantic
construction, and the NeurIPS Section 5 algorithm. The finite-query theorem is
also transported along an explicit equivalence `α ≃ ℕ`; a convenience wrapper
chooses such an equivalence for every countable ambient type, using infinitude
of the indexed languages. Thus Theorem 2.1 now covers the paper's arbitrary
explicitly enumerable countable universe. The development does not formalize
the proceedings paper in full. In particular, the following remain outside
its scope:

- finite-family uniform Theorem 2.2;
- robust-prompt Theorem 7.1;
- the informal strengthening that generated outputs can themselves be made
  pairwise distinct.

The semantic and finite-set-only constructions remain stated over `ℕ`; only
the source-facing finite-query Theorem 2.1 currently has the general transport.
The explicit-equivalence theorem preserves the membership-query interface.
The convenience `[Countable α]` wrapper chooses its equivalence classically
and therefore does not assert an executable encoding by itself.

## NeurIPS Section 4 boundary

The `GenLimit.Paper01_LanguageGeneration.Semantic` module formalizes the noncomputable construction in
Section 4 of the NeurIPS paper, especially (4.2)--(4.6). It follows the
round-dependent rule in (4.5), making `t` an explicit input to the generator.

Statement (4.1) describes `f_C` as a function of the observed finite set alone,
but (4.5) selects among the first `t` candidate languages. Because the paper
permits repeated observations, the same observed set can occur at different
times and does not determine `t`.
`GenLimit.Paper01_LanguageGeneration.SetInterface` instead scans the
first `|S_t|` candidates. Exact presentations of the paper's infinite targets
have unboundedly many distinct observations, so this set-only scope eventually
contains the target index even with arbitrary repetitions. The literal (4.1)
interface is therefore checked on the paper's full presentation boundary; the
injective theorem remains as the special case where `|S_t| = t`.

## Dependency path

```text
Core.Basic / Core.TargetStability / Core.OracleFamily
                         |
          Paper01_LanguageGeneration.Critical
              /          |          \
  .Semantic  .SetInterface  .FiniteQuery.Critical
                                      |
                             .FiniteQuery.Oracle
                                      |
                           .FiniteQuery.Selection
                                      |
                             .FiniteQuery.Round
                                      |
                            .FiniteQuery.Machine
                                      |
                              .FiniteQuery.Main
                                      |
                    .Transport  <---  Support.Renaming
```

## Indexing conventions

The paper uses one-based language and universe indices.  Lean is zero-based:

- `sample stream t` contains observations at positions `k < t`;
- candidate indices satisfy `n < t`;
- the semantic focus is the greatest #01-critical candidate below `t`;
- in the finite-query development, a cutoff `m` denotes the strict prefix
  `{u | u < m}`; and
- at cutoff `m`, the finite-query Proceedings endpoint is `m - 1`.

The implementation's indexed family is a function `ℕ → Set ℕ`, rather than a
set of sets. The transport layer generalizes this to `ℕ → Set α`. Both forms
preserve enumeration order and permit repeated languages.

## Paper correspondence

| Paper item | Lean declaration | Module | Ownership |
|---|---|---|---|
| Exact presentation | `Presents` | `GenLimit.Core.Basic` | Core |
| Observed set `S_t` | `sample` | `GenLimit.Core.Basic` | Core |
| Semantic consistency | `Consistent` | `GenLimit.Core.Basic` | Core |
| Full criticality, (4.2) | `Critical` | `GenLimit.Paper01_LanguageGeneration.Critical` | #01 |
| Target eventually critical, (4.3) | `target_eventually_critical` | `GenLimit.Paper01_LanguageGeneration.Critical` | #01, using Core stability |
| Critical-language chain, (4.4) | `critical_subset_of_le` | `GenLimit.Paper01_LanguageGeneration.Critical` | #01 |
| Semantic focus | `KM.Semantic.focus` | `GenLimit.Paper01_LanguageGeneration.Semantic` | #01 semantic |
| Round-dependent semantic construction, (4.5) | `KM.Semantic.generator` | `GenLimit.Paper01_LanguageGeneration.Semantic` | #01 semantic |
| Round-indexed semantic guarantee, (4.6), underlying Theorem (2.1) | `KM.Semantic.kleinbergMullainathan_main` | `GenLimit.Paper01_LanguageGeneration.Semantic` | #01 semantic |
| Finite-set consistency and criticality | `KM.SetInterface.ConsistentOn`, `KM.SetInterface.CriticalOn` | `GenLimit.Paper01_LanguageGeneration.SetInterface` | #01 observed-set interface |
| Literal observed-set generator from (4.1), arbitrary exact presentations | `KM.SetInterface.generator`, `KM.SetInterface.eventually_target_below_sample_card`, `KM.SetInterface.kleinbergMullainathan_set_interface_with_repetitions` | `GenLimit.Paper01_LanguageGeneration.SetInterface` | Complete, including repeated observations |
| Injective-presentation specialization | `KM.SetInterface.sample_card_of_injective`, `KM.SetInterface.kleinbergMullainathan_set_interface` | `GenLimit.Paper01_LanguageGeneration.SetInterface` | Compatibility theorem |
| Finite consistency test | `OracleFamily.ConsistentAt` | `GenLimit.Paper01_LanguageGeneration.FiniteQuery.Oracle` | #01 finite-query |
| Finite criticality | `FinitelyCritical` / `FinitelyCriticalAt` | `GenLimit.Paper01_LanguageGeneration.FiniteQuery.Critical`, `GenLimit.Paper01_LanguageGeneration.FiniteQuery.Oracle` | #01 finite-query |
| (5.2) | `target_eventually_finitelyCritical` | `GenLimit.Paper01_LanguageGeneration.FiniteQuery.Critical` | #01 finite-query, using semantic criticality |
| (5.3) | `finitelyCritical_prefix_subset` | `GenLimit.Paper01_LanguageGeneration.FiniteQuery.Critical` | #01 finite-query |
| (5.4) | `finitelyCritical_cutoff_mono` | `GenLimit.Paper01_LanguageGeneration.FiniteQuery.Critical` | #01 finite-query |
| `n_t(m)` | `OracleFamily.selected` | `GenLimit.Paper01_LanguageGeneration.FiniteQuery.Selection` | #01 finite-query |
| Eventual constancy of `n_t(m)` | `selected_eventually_constant` | `GenLimit.Paper01_LanguageGeneration.FiniteQuery.Selection` | #01 finite-query |
| (5.5) | `stop_exists` | `GenLimit.Paper01_LanguageGeneration.FiniteQuery.Round` | #01 finite-query |
| Corrected (5.6) | `run_round_spec` | `GenLimit.Paper01_LanguageGeneration.FiniteQuery.Machine` | #01 finite-query |
| (5.7) | `OracleFamily.eventual_correctness` | `GenLimit.Paper01_LanguageGeneration.FiniteQuery.Main` | #01 finite-query |
| Finite-query Theorem (2.1) | `OracleFamily.kleinbergMullainathan_main` | `GenLimit.Paper01_LanguageGeneration.FiniteQuery.Main` | #01 finite-query |
| Explicitly enumerable countable-universe Theorem (2.1) | `KM.Transport.kleinbergMullainathan_main_of_equiv` | `GenLimit.Paper01_LanguageGeneration.Transport` | Complete transport along `α ≃ ℕ` |
| Abstract countable-universe wrapper | `KM.Transport.kleinbergMullainathan_main_countable` | `GenLimit.Paper01_LanguageGeneration.Transport` | Classical choice of a coding; semantic convenience API |

## What the three formalizations prove in common

The semantic, finite-set, and proceedings finite-query generators are
different definitions, but all three main theorems establish
the same input/output condition on their respective presentation boundaries:
after a presentation-dependent threshold, the output lies in the target and
does not belong to `sample stream t`. This is freshness from the first `t`
adversary observations; none of the #01 theorems currently requires
non-repetition among the generator's own outputs. The finite-set theorem
covers arbitrary exact presentations; its candidate scope is the number of
distinct observations, not the raw round. The finite-query machine uses the
raw round as the finite candidate scope and supports arbitrary repetitions.
Transport along an equivalence preserves the same target-membership and
sample-freshness conclusion without changing the underlying machine proof.

## Finite-query proof details made explicit

1. The maximum over bad earlier indices is handled through shared uniform
   finite-scope stabilization, including the empty case.  This also supplies
   the eventual criticality lemma used by the semantic proof.
2. Per-round output and freshness require a consistent candidate.  The final
   proof establishes this once the target index lies below `t`.
3. The state is a strict cutoff.  Before round `t + 1`, it is raised to at
   least `stream t + 1`; this proves that the stopping endpoint is fresh.
4. Eventual constancy is proved through a minimum of the range of an antitone
   natural-number sequence, so the no-change case needs no special convention.
5. The concrete machine runs over `ℕ`; the general theorem either receives an
   explicit equivalence with `ℕ` or marks its classical choice of one.

## What each construction assumes about access and computability

The semantic generator directly tests `Critical`, which compares inclusion
between whole infinite languages, and classically chooses a fresh element of
the focused language. Its round-`t` output depends only on the observed prefix
through round `t`, but it is deliberately noncomputable from the pointwise
membership oracle. It uses #01's original criticality definition, not #39's
recursive criticality.

By contrast, every finite-query #01 test at a fixed time and cutoff is a finite
Boolean computation:

- consistency checks the finite sample;
- criticality checks candidate indices at most `n` and universe values below
  the cutoff; and
- selection takes a maximum over indices below `t`.

The finite-query counter uses `Nat.find` with a proved stopping witness. Its
predicate is decidable from `OracleFamily.query`; infinitude is used to prove
termination. The proceedings algorithm tests only the newly reached endpoint.
The `SetInterface` theorem remains a separate semantic, noncomputable
construction.

`KM.Transport.encodeFamily` maps each language and stream through the supplied
equivalence and answers every encoded membership query by decoding the natural
number and calling the original oracle. Consequently,
`kleinbergMullainathan_main_of_equiv` preserves the paper's finite-query access
model. `kleinbergMullainathan_main_countable` is intentionally weaker as an
implementation claim: its equivalence is selected by classical choice.

## Port provenance

The observed-set path was adapted from
`fifalsp/generation-in-the-limit-lib` snapshot
`722cad8bd935292a66b731c7aae8b8337697e864`:

- observed-set interface source commit
  `f1142da7d9226e5d72a10bcf32cba508341f3174`.

The public port retains Peng's `GenLimit.KM` declaration namespace while the
physical module follows `GenLimit.Paper01_LanguageGeneration`. The observed-set
cardinality argument was rewritten against the existing `GenLimit.Core.Basic`
API, so the destination commit is intentionally not claimed to be a literal
cherry-pick. The original source history remains canonical at the pinned
snapshot above.
