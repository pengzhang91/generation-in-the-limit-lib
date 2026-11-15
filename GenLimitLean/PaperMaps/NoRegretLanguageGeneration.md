# No-Regret Language Generation

Jiaxun Li, Vinod Raman, and Ambuj Tewari. [arXiv:2610.23641v1](https://arxiv.org/abs/2610.23641v1).

The authors' standalone Lean 4.22 distribution reports checks of 65 proof modules and 1,310 theorem declarations. The status column below records that source audit. The GenLimitLib port retains the declaration namespaces and translates the module imports. Paper numbering and machine-readable registry integration are pending.

From GenLimitLean, build and audit this development with

```sh
lake build GenLimit.NoRegretLanguageGeneration
lake env lean GenLimit/NoRegretLanguageGeneration/Audit.lean
```

Most declarations use the PredictionToGeneration namespace. Module names in the table are relative to GenLimit.NoRegretLanguageGeneration.

| Manuscript label | Status | Proof entry points |
| --- | --- | --- |
| Section 2: protocol, trajectories, losses, UUS | checked | Basic, Plays; `uus_iff_infinite_support` in Support; real success criteria in AsymptoticBridge and AnytimeAgnosticReal |
| `thm:mf-finite-characterization` | checked | FiniteMinimax: `mf_spec`, `mf_generator_attained`, `mf_generator_lower_bound`, `strategy_iff_generator` |
| `thm:smf-characterization` | checked | FiniteMinimax: `smf_spec`, `smf_generator_attained`, `smf_generator_lower_bound` |
| `lem:app-realizable-profile-regularity` | checked | FiniteMinimax: `mf_mono_succ`, `mf_succ_le`, `finite_profile_regularity` |
| `lem:app-agnostic-profile-regularity` | checked | FiniteMinimax: `smf_mono_succ`, `smf_succ_le`, `finite_profile_regularity` |
| `thm:mf-infinite-characterization` | checked | Uniform: `realizable_uniform_characterization`, `uniform_iff_infinite`, `wellFounded_infinite_lower_bound` |
| `thm:horizon-anytime-main` | checked | `realizable_no_regret_iff_isLittleO`, `horizon_to_anytime_real` |
| `thm:agnostic-horizon-anytime-main` | checked | `agnostic_no_regret_iff_isLittleO`, `agnostic_horizon_to_anytime_real`; virtual copy-response simulation in AnytimeAgnostic |
| `thm:compactness-gap` | checked, corrected endpoint | Blocks namespace: `compactness_gap_finite`, `compactness_gap_infinite`, `compactness_zero` |
| `thm:slow-growth` | checked | AnytimeRealizable: `slow_growth_anytime`, one generator for all positive horizons and the prescribed natural-valued rate |
| `thm:arbitrary-profile` | checked | ArbitraryProfiles: `arbitrary_profile`, exact quarter/eight rescaling and explicit countable UUS class |
| `cor:common-profiles` | checked, regularized | CommonProfiles/NamedProfiles/NearLinearProfile: all four families, full parameter ranges, Mathlib Theta and no-regret |
| `prop:mf-le-smf` | checked | `mf_le_smf` |
| `prop:necessary` | checked | `mf_le_smf`; NoRegretImplication also proves the same agnostic generator is realizably no-regret |
| `thm:pair-separation` | checked | PairedPoints uniform generator bound; PairedLowerBound: `paired_separation`, signed lower witnesses |
| `lem:sparse-graph-cover` | checked | CaroWei: `weighted_independent`, `caro_wei`, `sparse_vertex_cover` |
| `thm:arbitrary-agnostic-profile` | checked | ArbitraryAgnosticProfiles: `arbitrary_agnostic_profile`, `agnostic_theta_of_rescaling` |
| `cor:arbitrary-anytime-agnostic-rates` | checked | CommonAnytimeProfiles: `HasQuantitativeAgnosticProfile`, four `quantitative_agnostic_*_profile` theorems; one generator with uniform eventual rate and matching minimax Theta |
| `thm:comparison-realizable-criteria` | checked | ComparisonDiagram: `comparison_diagram_complete`, `criterion_counterexample_of_no_path`, `comparison_path_strict`; all six criteria and every missing arrow |
| `prop:agnostic-contamination-transfer` | checked | `contamination_transfer_real`, `contamination_transfer_littleO` |
| `thm:finite-class-bounds` | checked | FiniteClass: `finite_class_uniform_bound`, `finite_class_agnostic_bound`, `finite_class_agnostic_isLittleO`; literal real floor in ManuscriptBounds |
| `prop:cofinite-linear-profile` | checked | Cofinite: countability, UUS, nonuniform generator and exact linear MF/SMF; Comparisons: `cofinite_comparison_witness` |
| `lem:app-dynamic-sauer` | checked | `sequential_sauer`, `sauer_eq_truncated_choose`, `capacity_sauer`; CapacityTrees: exact query-tree supremum and unit-weight leaf count |
| `lem:app-realizable-capacity` | checked | `capacity_maximizer`, `capacity_realizable_update` |
| `lem:app-agnostic-capacity` | checked | `capacity_agnostic_update`, including the four-way split and signed multiplicative factors |
| `thm:finite-ldim-realizable` | checked | `finite_ldim_realizable_floor`, `finite_ldim_realizable_rate`, `finite_ldim_realizable_anytime`, `finite_ldim_realizable_littleO` |
| `thm:finite-ldim-agnostic` | checked | `finite_ldim_agnostic_bound`, `finite_ldim_agnostic_rate`, `finite_ldim_agnostic_anytime`, `finite_ldim_agnostic_littleO` |
| `lem:app-single-component-forcing` | checked | SharpnessComponent: exact dimension one, `component_forces`, `single_component` |
| `lem:app-product-construction` | checked | SharpnessProduct: `exact_dimension`, `product_forces`, `product_lower` |
| `thm:sharp-ldim-generation` | checked | Sharpness: `sharpness`, `sharpness_theta`; ManuscriptBounds: `sharpness_base_two`, universal constants for every dimension at least two and horizon at least three |
| `prop:finite-vc-linear-regret` | checked | VCCounterexample: `vc_one`, `uus`, `countable_class`, `dimensions_eq_horizon`, `every_generator_linear` |

## Exact scope and corrections

1. **Compactness endpoint.** The finite parameter must be positive if the
   natural numbers include zero. The zero-reserve class has MF zero, not one;
   `compactness_zero` proves that case. The positive finite and infinite cases
   have the manuscript's claimed finite and uniform forcing values.
2. **Real profile regularization.** The named real-valued functions need not
   be natural-valued, admissible, or monotone at early horizons. CommonProfiles
   proves that rounding and changing a finite prefix preserves the claimed
   asymptotics; both realizable and agnostic examples use this bridge.
3. **Minimax notation.** Finite numeric MF/SMF are maxima of forceable
   thresholds, with matching attained history-generator upper bounds and
   adversarial lower witnesses. Uniform minimax is stated at every natural
   threshold using genuinely well-founded trees, including the unbounded case.
   These express the exact minimax content; no separate literal extended-natural
   infimum/supremum expression is introduced.
4. **VC representation.** The VC-one proof uses singleton and pair shattering.
   Representation proves equivalence with ordinary finite-set shattering;
   ClassicalDimensions also proves the numeric dimension equals one. Explicit
   mistake-index sets, cardinal identities, and same-comparator pattern
   characterizations are supplied by Representation.
5. **Capacity.** ENNReal gives a conservative extension of nonnegative bounded
   weights. The recursion is proved equal to the supremum over adaptive query
   trees; unit weights give ordinary nonempty leaf counts. Constructed weights
   have finite range, which guarantees an attained legal-output maximizer.
6. **Anytime rates.** Explicit Littlestone bounds include a constant additive
   term to cover every early positive horizon. The rate functions diverge, so
   this term does not change the manuscript's asymptotic statement.
7. **Generic cited result.** The general countable-UUS nonuniform-generation
   theorem from the prose is also proved directly:
   `countable_uus_nonuniform` in CountableGeneration. Its generator receives
   no membership feedback and has a target-specific uniform last-mistake bound.
