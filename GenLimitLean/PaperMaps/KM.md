# Paper 01 — Kleinberg--Mullainathan paper map

Lean umbrella: `GenLimit.KM`

Main declarations:

- semantic: `GenLimit.KM.Semantic.kleinbergMullainathan_main`;
- NeurIPS proceedings finite-query:
  `GenLimit.OracleFamily.kleinbergMullainathan_main`;
- arXiv-v1 finite-query:
  `GenLimit.OracleFamily.ArxivV1.kleinbergMullainathan_main`;
- finite-set interface for arbitrary exact presentations:
  `GenLimit.KM.SetInterface.kleinbergMullainathan_set_interface_with_repetitions`.

Source versions:

- the semantic and endpoint-test finite-query paths correspond to the NeurIPS
  2024 proceedings;
- the parallel first-fresh-eligible path corresponds to
  arXiv:2404.06757v1 (10 April 2024), pinned PDF SHA-256
  `db2648f7768c455015d22d1785e19747796ada40763322ec181bad780ab9a54f`;
- the NeurIPS 2024 proceedings PDF used for correspondence checking has
  SHA-256 `4b29159d3d11506fa8f92f38e4dfe234f209a730f786de7ef6c577f7e34b0745`.

The two finite-query stopping rules are a source-version difference, not a
paper error.  Both are finite-membership-query algorithms and both prove the
same generation-in-the-limit guarantee.

Human audit status: the semantic development has a Level 3 audit covering the
theorem statement, semantic construction, intermediate mathematical steps,
and proof correspondence. This does not require literal tactic-by-tactic
identity. The finite-query and finite-set-interface developments are outside
that audit. See the
[human audit record](../HUMAN_AUDIT.md).

The KM development depends on `GenLimit.Core` and does not import the DenseGeneration
development or any cross-paper bridge.

## ChatGPT Pro statement-faithfulness check

At the maintainer's direction, ChatGPT Pro ran a two-stage check against Lean
snapshot `dfcd13534f9d51642a9f88904268e95454c88f7f`: a code-only natural-language
reconstruction, followed by a comparison with the two pinned author PDFs. The
artifacts are mirrored in this public repository with checksums:

- [code-only reconstruction](../AuditRecords/KM/evidence/code-only-reconstruction.md), SHA-256 `45d8246b3d9cfc51a7afe22c5e315a757d7a817059ee48bc93b822c3173fdf80`;
- [paper comparison](../AuditRecords/KM/evidence/source-comparison.md), SHA-256 `21e840362f424c2327d8d74c864bf2e3495ef059fcbcaf576684332945be8631`.

The machine-readable provenance and review-status record is
[`AuditRecords/KM/record.json`](../AuditRecords/KM/record.json). The reports
are mirrored byte-for-byte from the pinned private source snapshot so that the
public review does not depend on ChatGPT access or private repository access.

This evidence is review input, not a human audit and not a kernel certificate.
The existing Level 3 record applies only to the semantic path stated above;
independent human correspondence review of both finite-query paths and the
finite-set interface remains pending.

## Formalization boundary

The four paths below cover the countable-family generation-in-the-limit result
(Theorem 2.1), its Section 4 semantic construction, and both published Section
5 algorithms. They do not formalize the papers in full. In particular, the
following remain outside this development:

- finite-family uniform Theorem 2.2;
- robust-prompt Theorem 7.1;
- arXiv-v1's stronger regular-subset-query result (7.5)--(7.6), its
  context-free corollary, and its finite-family prompted impossibility; and
- the informal strengthening that generated outputs can themselves be made
  pairwise distinct.

The universe is fixed to `ℕ`. This is a faithful specialization of the papers'
arbitrary explicitly enumerable countable universe; no general transport
theorem is claimed here.

## NeurIPS Section 4 boundary

The `GenLimit.KM.Semantic` path formalizes the noncomputable construction in
Section 4 of the NeurIPS paper, especially (4.2)--(4.6). It follows the
round-dependent rule in (4.5), making `t` an explicit input to the generator.

Statement (4.1) describes `f_C` as a function of the observed finite set alone,
but (4.5) selects among the first `t` candidate languages. Because the paper
permits repeated observations, the same observed set can occur at different
times and does not determine `t`. `GenLimit.KM.SetInterface` instead scans the
first `|S_t|` candidates. Exact presentations of the paper's infinite targets
have unboundedly many distinct observations, so this set-only scope eventually
contains the target index even with arbitrary repetitions. The literal (4.1)
interface is therefore checked on the paper's full presentation boundary; the
injective theorem remains as the special case where `|S_t| = t`.

## Dependency path

```text
Core.Basic / Core.TargetStability / Core.OracleFamily
                         |
                    KM.Critical
              /          |          \
     KM.Semantic  KM.SetInterface  KM.FiniteQuery.Critical
                                      |
                             KM.FiniteQuery.Oracle
                                      |
                           KM.FiniteQuery.Selection
                              /               \
              KM.FiniteQuery.Round      KM.FiniteQuery.ArxivV1
                         |
                KM.FiniteQuery.Machine
                         |
                  KM.FiniteQuery.Main
```

## Indexing conventions

The paper uses one-based language and universe indices.  Lean is zero-based:

- `sample stream t` contains observations at positions `k < t`;
- candidate indices satisfy `n < t`;
- the semantic focus is the greatest KM-critical candidate below `t`;
- in the finite-query development, a cutoff `m` denotes the strict prefix
  `{u | u < m}`; and
- at cutoff `m`, the finite-query Proceedings endpoint is `m - 1`, while
  arXiv v1 chooses the least fresh eligible value anywhere below `m`.

The indexed family is a function `ℕ → Set ℕ`, rather than a set of sets.
This preserves enumeration order and permits repeated languages.

## Paper correspondence

| Paper item | Lean declaration | Module | Ownership |
|---|---|---|---|
| Exact presentation | `Presents` | `GenLimit.Core.Basic` | Core |
| Observed set `S_t` | `sample` | `GenLimit.Core.Basic` | Core |
| Semantic consistency | `Consistent` | `GenLimit.Core.Basic` | Core |
| Full criticality, (4.2) | `Critical` | `GenLimit.KM.Critical` | KM |
| Target eventually critical, (4.3) | `target_eventually_critical` | `GenLimit.KM.Critical` | KM, using Core stability |
| Critical-language chain, (4.4) | `critical_subset_of_le` | `GenLimit.KM.Critical` | KM |
| Semantic focus | `KM.Semantic.focus` | `GenLimit.KM.Semantic` | KM semantic |
| Round-dependent semantic construction, (4.5) | `KM.Semantic.generator` | `GenLimit.KM.Semantic` | KM semantic |
| Round-indexed semantic guarantee, (4.6), underlying Theorem (2.1) | `KM.Semantic.kleinbergMullainathan_main` | `GenLimit.KM.Semantic` | KM semantic |
| Finite-set consistency and criticality | `KM.SetInterface.ConsistentOn`, `KM.SetInterface.CriticalOn` | `GenLimit.KM.SetInterface` | KM finite-set interface |
| Literal observed-set generator from (4.1), arbitrary exact presentations | `KM.SetInterface.generator`, `KM.SetInterface.eventually_target_below_sample_card`, `KM.SetInterface.kleinbergMullainathan_set_interface_with_repetitions` | `GenLimit.KM.SetInterface` | Complete, including repeated observations |
| Injective-presentation specialization | `KM.SetInterface.sample_card_of_injective`, `KM.SetInterface.kleinbergMullainathan_set_interface` | `GenLimit.KM.SetInterface` | Compatibility theorem |
| Finite consistency test | `OracleFamily.ConsistentAt` | `GenLimit.KM.FiniteQuery.Oracle` | KM finite-query |
| Finite criticality | `FinitelyCritical` / `FinitelyCriticalAt` | `GenLimit.KM.FiniteQuery.Critical`, `GenLimit.KM.FiniteQuery.Oracle` | KM finite-query |
| (5.2) | `target_eventually_finitelyCritical` | `GenLimit.KM.FiniteQuery.Critical` | KM finite-query, using semantic criticality |
| (5.3) | `finitelyCritical_prefix_subset` | `GenLimit.KM.FiniteQuery.Critical` | KM finite-query |
| (5.4) | `finitelyCritical_cutoff_mono` | `GenLimit.KM.FiniteQuery.Critical` | KM finite-query |
| `n_t(m)` | `OracleFamily.selected` | `GenLimit.KM.FiniteQuery.Selection` | KM finite-query |
| Eventual constancy of `n_t(m)` | `selected_eventually_constant` | `GenLimit.KM.FiniteQuery.Selection` | KM finite-query |
| (5.5) | `stop_exists` | `GenLimit.KM.FiniteQuery.Round` | KM finite-query |
| Corrected (5.6) | `run_round_spec` | `GenLimit.KM.FiniteQuery.Machine` | KM finite-query |
| (5.7) | `OracleFamily.eventual_correctness` | `GenLimit.KM.FiniteQuery.Main` | KM finite-query |
| Finite-query Theorem (2.1) | `OracleFamily.kleinbergMullainathan_main` | `GenLimit.KM.FiniteQuery.Main` | KM finite-query |
| arXiv-v1 fresh eligible prefix | `OracleFamily.ArxivV1.eligible`, `OracleFamily.ArxivV1.mem_eligible` | `GenLimit.KM.FiniteQuery.ArxivV1` | Literal whole-prefix search set |
| arXiv-v1 finite termination | `OracleFamily.ArxivV1.hasFreshEligible_exists`, `OracleFamily.ArxivV1.roundCounter_spec`, `OracleFamily.ArxivV1.roundCounter_le_of_freshEligible` | `GenLimit.KM.FiniteQuery.ArxivV1` | First successful cutoff, proved in Lean |
| arXiv-v1 least eligible choice | `OracleFamily.ArxivV1.roundOutput_spec` | `GenLimit.KM.FiniteQuery.ArxivV1` | Exact minimum and freshness |
| arXiv-v1 repeated-observation access invariant | `OracleFamily.ArxivV1.run_counter_bounds`, `OracleFamily.ArxivV1.sample_lt_runCounter` | `GenLimit.KM.FiniteQuery.ArxivV1` | Every observed value lies below the queried cutoff |
| arXiv-v1 successful round | `OracleFamily.ArxivV1.run_round_spec` | `GenLimit.KM.FiniteQuery.ArxivV1` | Least fresh element of the maximal finite-critical prefix |
| arXiv-v1 Theorem (2.1) | `OracleFamily.ArxivV1.eventual_correctness`, `OracleFamily.ArxivV1.kleinbergMullainathan_main` | `GenLimit.KM.FiniteQuery.ArxivV1` | Complete for arbitrary exact presentations, including repetitions |

## What the four formalizations prove in common

The semantic, finite-set, proceedings finite-query, and arXiv-v1 finite-query
generators are different definitions, but all four main theorems establish
the same input/output condition on their respective presentation boundaries:
after a presentation-dependent threshold, the output lies in the target and
does not belong to `sample stream t`. This is freshness from the first `t`
adversary observations; none of the KM theorems currently requires
non-repetition among the generator's own outputs. The finite-set theorem
covers arbitrary exact presentations; its candidate scope is the number of
distinct observations, not the raw round. Both finite-query machines use the
raw round as the finite candidate scope and support arbitrary repetitions.

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
5. The countable universe is fixed as `ℕ`; no hidden enumeration oracle is
   used.

The arXiv-v1 path shares the same finite-critical selector, but uses the
earlier source's whole-prefix stopping rule.  At each increasing cutoff it
forms the finite set of elements in the selected language that have not
appeared in the observed sample, stops at the first nonempty such set, and
returns its minimum.  Stabilization of the selected index and infinitude of
its language prove termination.  The state keeps the queried cutoff separate
from the output because the minimum may be smaller than the new endpoint.
The cutoff still grows above every observation, including under repeated
presentations.

## What each construction assumes about access and computability

The semantic generator directly tests `Critical`, which compares inclusion
between whole infinite languages, and classically chooses a fresh element of
the focused language. Its round-`t` output depends only on the observed prefix
through round `t`, but it is deliberately noncomputable from the pointwise
membership oracle. It uses KM's original criticality definition, not
DenseGeneration's recursive criticality.

By contrast, every finite-query KM test at a fixed time and cutoff is a finite
Boolean computation:

- consistency checks the finite sample;
- criticality checks candidate indices at most `n` and universe values below
  the cutoff; and
- selection takes a maximum over indices below `t`.

Both finite-query counters use `Nat.find` with proved stopping witnesses.
Their predicates are decidable from `OracleFamily.query`; infinitude is used
to prove termination.  The proceedings path tests only the newly reached
endpoint.  The arXiv-v1 path tests the whole queried prefix and chooses its
least fresh eligible element.  This is a change between source versions, not
a correction of a false claim.  The `SetInterface` theorem remains a separate
semantic, noncomputable construction.

## Port provenance

The two added paths were adapted from
`fifalsp/generation-in-the-limit-lib` snapshot
`722cad8bd935292a66b731c7aae8b8337697e864`:

- observed-set interface source commit
  `f1142da7d9226e5d72a10bcf32cba508341f3174`;
- arXiv-v1 finite-query source commit
  `db73228c5b926daafd08d3244d11d2420c4e93ba`.

The public port keeps Peng's `GenLimit.KM` module naming. The observed-set
cardinality argument was rewritten against the existing `GenLimit.Core.Basic`
API, so the destination commit is intentionally not claimed to be a literal
cherry-pick. The original source history remains canonical at the pinned
snapshot above.
