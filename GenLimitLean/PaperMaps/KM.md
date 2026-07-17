# Kleinberg--Mullainathan paper map

Lean umbrella: `GenLimit.KM`

Main declarations:

- semantic: `GenLimit.KM.Semantic.kleinbergMullainathan_main`;
- finite-query: `GenLimit.OracleFamily.kleinbergMullainathan_main`.

Human audit status: the semantic theorem statement and construction
correspondence are complete; line-by-line proof correspondence and the
finite-query development are outside that audit. See the
[human audit record](../HUMAN_AUDIT.md).

The KM development depends on `GenLimit.Core` and does not import the DenseGeneration
development or any cross-paper bridge.

## Dependency path

```text
Core.Basic / Core.TargetStability / Core.OracleFamily
                         |
                    KM.Critical
                    /          \
           KM.Semantic       KM.FiniteQuery.Critical
                                      |
                             KM.FiniteQuery.Oracle
                                      |
                           KM.FiniteQuery.Selection
                                      |
                             KM.FiniteQuery.Round
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
- at cutoff `m`, the finite-query Proceedings endpoint is `m - 1`.

The indexed family is a function `ℕ → Set ℕ`, rather than a set of sets.
This preserves enumeration order and permits repeated languages.

## Paper correspondence

| Paper item | Lean declaration | Module | Ownership |
|---|---|---|---|
| Exact presentation | `Presents` | `GenLimit.Core.Basic` | Core |
| Observed set `S_t` | `sample` | `GenLimit.Core.Basic` | Core |
| Semantic consistency | `Consistent` | `GenLimit.Core.Basic` | Core |
| Full criticality | `Critical` | `GenLimit.KM.Critical` | KM |
| Critical-language chain | `critical_subset_of_le` | `GenLimit.KM.Critical` | KM |
| Target eventually critical | `target_eventually_critical` | `GenLimit.KM.Critical` | KM, using Core stability |
| Semantic focus | `KM.Semantic.focus` | `GenLimit.KM.Semantic` | KM semantic |
| Semantic generator | `KM.Semantic.generator` | `GenLimit.KM.Semantic` | KM semantic |
| Semantic Theorem (2.1) | `KM.Semantic.kleinbergMullainathan_main` | `GenLimit.KM.Semantic` | KM semantic |
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

## Common theorem boundary

The semantic and finite-query generators are different definitions, but both
main theorems establish the same input/output condition: after a
presentation-dependent threshold, the output lies in the target and does not
belong to `sample stream t`.  This is freshness from the first `t` adversary
observations; neither KM theorem currently requires non-repetition among the
generator's own outputs.

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

## Access-model boundary

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

`roundCounter` uses `Nat.find` with the proved stopping witness.  Its predicate
is decidable by `OracleFamily.query`; infinitude is used to prove termination.

The `FiniteQuery` round is the endpoint-test algorithm in the NeurIPS
proceedings.  The later first-fresh-eligible variant is not yet formalized.
