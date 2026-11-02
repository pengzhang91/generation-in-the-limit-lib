import GenLimit.Paper21_GenerationInMetricSpaces.CoveringGeometry
import GenLimit.Support.HistoryChain
import GenLimit.Support.StreamPrefix
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Push

/-!
# The general row-array diagonal

Appendix Lemma C.2 of arXiv:2602.07710v2. Fixed observations and all selected
row prefixes are explicitly required to belong to each witnessing target.
The construction is semantic and uses classical choices of successful phases.
-/

set_option maxHeartbeats 10000

namespace GenLimit.MetricSpaces

/-- Closed neighborhoods distribute over a finite union, including when
neither distance infimum is attained. -/
theorem closedNeighborhood_union (ρ : Distance α) (A B : Set α) (r : ℝ) :
    closedNeighborhood ρ (A ∪ B) r =
      closedNeighborhood ρ A r ∪ closedNeighborhood ρ B r := by
  ext y
  constructor
  · intro hy
    by_cases hA : y ∈ closedNeighborhood ρ A r
    · exact Or.inl hA
    · apply Or.inr
      by_contra hB
      change ¬ (∀ η, r < η → ∃ x ∈ A, ρ x y < η) at hA
      change ¬ (∀ η, r < η → ∃ x ∈ B, ρ x y < η) at hB
      push_neg at hA hB
      obtain ⟨a, hra, ha⟩ := hA
      obtain ⟨b, hrb, hb⟩ := hB
      obtain ⟨x, hx | hx, hxy⟩ := hy (min a b) (lt_min hra hrb)
      · exact (not_lt_of_ge (ha x hx)) (hxy.trans_le (min_le_left _ _))
      · exact (not_lt_of_ge (hb x hx)) (hxy.trans_le (min_le_right _ _))
  · rintro (hy | hy)
    · exact inClosedNeighborhood_mono_centers Set.subset_union_left hy
    · exact inClosedNeighborhood_mono_centers Set.subset_union_right hy

namespace RowDiagonal

open GenLimit.Generic GenLimit.Support

variable {α : Type*}

noncomputable section

def prefixList (stream : Stream α) (n : ℕ) : List α :=
  List.ofFn (fun i : Fin n => stream i)

@[simp] theorem prefixList_length (stream : Stream α) (n : ℕ) :
    (prefixList stream n).length = n := by simp [prefixList]

@[simp] theorem prefixList_get (stream : Stream α) (n : ℕ) (i : Fin n) :
    (prefixList stream n).get ⟨i, by simp⟩ = stream i := by simp [prefixList]

theorem mem_prefixList {stream : Stream α} {n : ℕ} {x : α} :
    x ∈ prefixList stream n ↔ ∃ j, j < n ∧ stream j = x := by
  simp only [prefixList, List.mem_ofFn]
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j, j.isLt, hj⟩
  · rintro ⟨j, hj, heq⟩; exact ⟨⟨j, hj⟩, heq⟩

theorem prefixList_prepend (xs : List α) (tail : Stream α) (k : ℕ) :
    prefixList (prependStream xs tail) (xs.length + k) = xs ++ prefixList tail k := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    by_cases hx : i < xs.length
    · simp [prefixList, List.getElem_append_left hx,
        prependStream_apply_of_lt xs tail hx]
    · have hge : xs.length ≤ i := Nat.le_of_not_gt hx
      simp [prefixList, List.getElem_append_right hge,
        prependStream_apply_of_not_lt xs tail hx]

def historyOutput (G : Generator α) (xs : List α) : α := G xs.length xs.get

/-- Values of the prescribed finite prefixes of rows `0,...,n-1`. -/
def prior (row : ℕ → Stream α) {n : ℕ} (cut : Fin n → ℕ) : Set α :=
  {x | ∃ i : Fin n, ∃ j, j < cut i ∧ row i j = x}

/-- Values of all stopped positive-row prefixes. -/
def stopped (row : ℕ → Stream α) (cut : ℕ → ℕ) : Set α :=
  {x | ∃ i j, j < cut i ∧ row (i + 1) j = x}

def observations (fixed : List α) (row : ℕ → Stream α) (cut : ℕ → ℕ) : Set α :=
  {x | x ∈ fixed} ∪ Set.range (row 0) ∪ stopped row cut

def future (row : ℕ → Stream α) (n : ℕ) : Set α :=
  {x | ∃ i j, n < i ∧ row i j = x}

/-- An exact ledger after stopping the first `n` positive rows. -/
structure Stage (fixed : List α) (row : ℕ → Stream α) (n : ℕ) where
  history : List α
  cut : Fin n → ℕ
  positive : ∀ i, 0 < cut i
  values : ∀ x, x ∈ history ↔ x ∈ fixed ∨
    (∃ j, j < n ∧ row 0 j = x) ∨
    ∃ i : Fin n, ∃ j, j < cut i ∧ row (i + 1) j = x

def initial (fixed : List α) (row : ℕ → Stream α) : Stage fixed row 0 where
  history := fixed
  cut := Fin.elim0
  positive := fun i => Fin.elim0 i
  values := by simp

variable {fixed : List α} {row : ℕ → Stream α}

def base {n : ℕ} (state : Stage fixed row n) : List α :=
  state.history ++ [row 0 n]

def priorCut {n : ℕ} (state : Stage fixed row n) (i : Fin (n + 1)) : ℕ :=
  if hi : i.val = 0 then n + 1 else state.cut ⟨i.val - 1, by omega⟩

theorem priorCut_positive {n : ℕ} (state : Stage fixed row n) :
    ∀ i, 0 < priorCut state i := by
  intro i
  unfold priorCut
  split
  · omega
  · exact state.positive _

theorem base_values {n : ℕ} (state : Stage fixed row n) (x : α) :
    x ∈ base state ↔ x ∈ fixed ∨ x ∈ prior row (priorCut state) := by
  rw [base, List.mem_append, List.mem_singleton, state.values]
  constructor
  · rintro ((hx | hx | hx) | hx)
    · exact Or.inl hx
    · obtain ⟨j, hj, hrow⟩ := hx
      exact Or.inr ⟨⟨0, by omega⟩, j, by simp [priorCut]; omega, hrow⟩
    · obtain ⟨i, j, hj, hrow⟩ := hx
      refine Or.inr ⟨⟨i + 1, by omega⟩, j, ?_, hrow⟩
      simpa [priorCut] using hj
    · subst x
      exact Or.inr ⟨⟨0, by omega⟩, n, by simp [priorCut], rfl⟩
  · rintro (hx | ⟨i, j, hj, hrow⟩)
    · exact Or.inl (Or.inl hx)
    · by_cases hi : i.val = 0
      · have hj' : j < n + 1 := by simpa [priorCut, hi] using hj
        have hr : row 0 j = x := by simpa [hi] using hrow
        by_cases hjn : j < n
        · exact Or.inl (Or.inr (Or.inl ⟨j, hjn, hr⟩))
        · have : j = n := by omega
          subst j
          exact Or.inr hr.symm
      · refine Or.inl (Or.inr (Or.inr ⟨⟨i.val - 1, by omega⟩, j, ?_, ?_⟩))
        · simpa [priorCut, hi] using hj
        · simpa [Nat.sub_add_cancel (by omega : 1 ≤ i.val)] using hrow

def appendCut {n : ℕ} (state : Stage fixed row n) (k : ℕ) (i : Fin (n + 1)) : ℕ :=
  if hi : i.val < n then state.cut ⟨i.val, hi⟩ else k

/-- Append the next zeroth-row observation and a nonempty prefix of the
next positive row to the exact ledger. -/
def extend {n : ℕ} (state : Stage fixed row n) (k : ℕ) (hk : 0 < k) :
    Stage fixed row (n + 1) where
  history := base state ++ prefixList (row (n + 1)) k
  cut := appendCut state k
  positive := by
    intro i
    unfold appendCut
    split
    · exact state.positive _
    · exact hk
  values := by
    intro x
    simp only [List.mem_append, base, List.mem_singleton, mem_prefixList, state.values]
    constructor
    · rintro (((hx | hx | hx) | hx) | hx)
      · exact Or.inl hx
      · obtain ⟨j, hj, heq⟩ := hx
        exact Or.inr (Or.inl ⟨j, by omega, heq⟩)
      · obtain ⟨i, j, hj, heq⟩ := hx
        refine Or.inr (Or.inr ⟨⟨i, by omega⟩, j, ?_, heq⟩)
        simpa [appendCut, i.isLt] using hj
      · exact Or.inr (Or.inl ⟨n, by omega, hx.symm⟩)
      · obtain ⟨j, hj, heq⟩ := hx
        refine Or.inr (Or.inr ⟨⟨n, by omega⟩, j, ?_, heq⟩)
        simpa [appendCut] using hj
    · rintro (hx | ⟨j, hj, heq⟩ | ⟨i, j, hj, heq⟩)
      · exact Or.inl (Or.inl (Or.inl hx))
      · by_cases hjn : j < n
        · exact Or.inl (Or.inl (Or.inr (Or.inl ⟨j, hjn, heq⟩)))
        · have : j = n := by omega
          subst j
          exact Or.inl (Or.inr heq.symm)
      · by_cases hi : i.val < n
        · refine Or.inl (Or.inl (Or.inr (Or.inr ⟨⟨i, hi⟩, j, ?_, heq⟩)))
          simpa [appendCut, hi] using hj
        · have hin : i.val = n := by omega
          refine Or.inr ⟨j, ?_, ?_⟩
          · simpa [appendCut, hi] using hj
          · simpa [hin] using heq

/-- The source's three row-array hypotheses. Coverage by the union of the
three neighborhoods is packaged as coverage by their union of centers;
`closedNeighborhood_union` proves the equivalence. -/
structure Criterion (ρ : Distance α) (ε ε' : ℝ) (H : LanguageClass α)
    (fixed : List α) (row : ℕ → Stream α) (A : ℕ → Set α) : Prop where
  final_target : ∀ cut : ℕ → ℕ, (∀ i, 0 < cut i) → ∃ L, L ∈ H ∧
    observations fixed row cut ⊆ L ∧
    L ⊆ closedNeighborhood ρ (observations fixed row cut) ε ∧
    L ⊆ closedNeighborhood ρ {x | x ∈ fixed} ε' ∪ A 0 ∪
      closedNeighborhood ρ (stopped row cut) ε'
  phase_target : ∀ n (cut : Fin (n + 1) → ℕ), (∀ i, 0 < cut i) →
    ∃ L, L ∈ H ∧
    ({x | x ∈ fixed} ∪ Set.range (row (n + 1)) ∪ prior row cut) ⊆ L ∧
    L ⊆ closedNeighborhood ρ
      ({x | x ∈ fixed} ∪ Set.range (row (n + 1)) ∪ prior row cut) ε ∧
    L ⊆ closedNeighborhood ρ {x | x ∈ fixed} ε' ∪ A (n + 1) ∪
      closedNeighborhood ρ (prior row cut) ε'
  separated : ∀ n, Disjoint (A (n + 1))
    (A 0 ∪ closedNeighborhood ρ (future row (n + 1)) ε')

@[simp] theorem historyOutput_prefixList (G : Generator α) (stream : Stream α) (n : ℕ) :
    historyOutput G (prefixList stream n) = output G stream n := by
  have hget (i : Fin (prefixList stream n).length) :
      (prefixList stream n).get i = stream i := by
    have hi : i.val < n := by simpa only [prefixList_length] using i.isLt
    exact prefixList_get stream n ⟨i, hi⟩
  have heq := congrArg (G (prefixList stream n).length) (funext hget)
  change historyOutput G (prefixList stream n) = output G stream (prefixList stream n).length at heq
  simpa only [prefixList_length] using heq


structure SuccessfulPhase (G : Generator α) (A : ℕ → Set α)
    {n : ℕ} (state : Stage fixed row n) where
  cut : ℕ
  positive : 0 < cut
  output_current : historyOutput G (extend state cut positive).history ∈ A (n + 1)

/-- Following a temporary target forces a successful output in the current
row set after a finite nonempty prefix. -/
theorem exists_successful_phase
    {ρ : Distance α} {ε ε' : ℝ} {H : LanguageClass α} {A : ℕ → Set α}
    (criterion : Criterion ρ ε ε' H fixed row A)
    (G : Generator α) (hG : IsLimitGeneratorAt ρ ε ε' G H)
    {n : ℕ} (state : Stage fixed row n) :
    Nonempty (SuccessfulPhase G A state) := by
  classical
  obtain ⟨L, hLH, hmem, hcover, hparts⟩ :=
    criterion.phase_target n (priorCut state) (priorCut_positive state)
  let stream := prependStream (base state) (row (n + 1))
  have hrange : Set.range stream =
      {x | x ∈ fixed} ∪ Set.range (row (n + 1)) ∪ prior row (priorCut state) := by
    rw [show stream = prependStream (base state) (row (n + 1)) from rfl,
      range_prependStream]
    ext x
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset]
    rw [base_values]
    constructor
    · rintro ((hx | hx) | hx)
      · exact Or.inl (Or.inl hx)
      · exact Or.inr hx
      · exact Or.inl (Or.inr hx)
    · rintro ((hx | hx) | hx)
      · exact Or.inl (Or.inl hx)
      · exact Or.inr hx
      · exact Or.inl (Or.inr hx)
  have hp : MetricPresentation ρ ε stream L := by
    constructor
    · change Set.range stream ⊆ L
      rw [hrange]
      exact hmem
    · rw [hrange]
      exact hcover
  obtain ⟨T, hT⟩ := hG L hLH stream hp
  let k := T + 1
  let t := (base state).length + k
  have hk : 0 < k := by dsimp [k]; omega
  have hcorrect := hT t (by dsimp [t, k]; omega)
  have hbaseSample : {x | x ∈ base state} ⊆ (sample stream t : Set α) := by
    intro x hx
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
    apply mem_sample_iff.mpr
    refine ⟨i, ?_, ?_⟩
    · dsimp [t]; omega
    · exact (prependStream_apply_of_lt (base state) (row (n + 1)) i.isLt).trans hi
  have hfixed : {x | x ∈ fixed} ⊆ (sample stream t : Set α) := by
    intro x hx
    exact hbaseSample ((base_values state x).mpr (Or.inl hx))
  have hprior : prior row (priorCut state) ⊆ (sample stream t : Set α) := by
    intro x hx
    exact hbaseSample ((base_values state x).mpr (Or.inr hx))
  have hout : output G stream t ∈ A (n + 1) := by
    rcases hparts hcorrect.1 with (hfixedNear | hA) | hpriorNear
    · exact (hcorrect.2 (inClosedNeighborhood_mono_centers hfixed hfixedNear)).elim
    · exact hA
    · exact (hcorrect.2 (inClosedNeighborhood_mono_centers hprior hpriorNear)).elim
  refine ⟨⟨k, hk, ?_⟩⟩
  have heq : (extend state k hk).history = prefixList stream t :=
    (prefixList_prepend (base state) (row (n + 1)) k).symm
  rw [heq, historyOutput_prefixList]
  exact hout


def phase {ρ : Distance α} {ε ε' : ℝ} {H : LanguageClass α} {A : ℕ → Set α}
    (criterion : Criterion ρ ε ε' H fixed row A)
    (G : Generator α) (hG : IsLimitGeneratorAt ρ ε ε' G H)
    {n : ℕ} (state : Stage fixed row n) : SuccessfulPhase G A state :=
  Classical.choice (exists_successful_phase criterion G hG state)

def stage {ρ : Distance α} {ε ε' : ℝ} {H : LanguageClass α} {A : ℕ → Set α}
    (criterion : Criterion ρ ε ε' H fixed row A)
    (G : Generator α) (hG : IsLimitGeneratorAt ρ ε ε' G H) :
    (n : ℕ) → Stage fixed row n
  | 0 => initial fixed row
  | n + 1 =>
    let old := stage criterion G hG n
    let next := phase criterion G hG old
    extend old next.cut next.positive

variable {ρ : Distance α} {ε ε' : ℝ} {H : LanguageClass α} {A : ℕ → Set α}
variable (criterion : Criterion ρ ε ε' H fixed row A)
variable (G : Generator α) (hG : IsLimitGeneratorAt ρ ε ε' G H)

def chosenCut (i : ℕ) : ℕ := (phase criterion G hG (stage criterion G hG i)).cut

theorem stage_cut_eq (n : ℕ) : ∀ i : Fin n,
    (stage criterion G hG n).cut i = chosenCut criterion G hG i := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i
    change appendCut (stage criterion G hG n) (chosenCut criterion G hG n) i = _
    unfold appendCut
    split_ifs with hi
    · exact ih ⟨i, hi⟩
    · have hin : i.val = n := by omega
      simp [hin]

theorem stage_prefix (n : ℕ) :
    (stage criterion G hG n).history <+: (stage criterion G hG (n + 1)).history := by
  change (stage criterion G hG n).history <+:
    ((stage criterion G hG n).history ++ [row 0 n]) ++ _
  exact (List.prefix_append ..).trans (List.prefix_append ..)

theorem stage_length (n : ℕ) : n ≤ (stage criterion G hG n).history.length := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [stage]
    change n + 1 ≤ (base (stage criterion G hG n) ++
      prefixList (row (n + 1)) (chosenCut criterion G hG n)).length
    simp only [base, List.length_append, List.length_singleton, prefixList_length]
    omega

def chain : HistoryChain α where
  history n := (stage criterion G hG n).history
  prefix_succ := stage_prefix criterion G hG
  le_length := stage_length criterion G hG

theorem history_mem_range (n : ℕ) {x : α} (hx : x ∈ (stage criterion G hG n).history) :
    x ∈ Set.range (chain criterion G hG).stream := by
  classical
  exact (chain criterion G hG).history_toFinset_subset_stream_range n
    (List.mem_toFinset.mpr hx)

theorem chain_range : Set.range (chain criterion G hG).stream =
    observations fixed row (chosenCut criterion G hG) := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    have hx : (chain criterion G hG).stream t ∈ (stage criterion G hG (t + 1)).history := by
      exact List.get_mem _ _
    rcases ((stage criterion G hG (t + 1)).values _).mp hx with hfixed | hzero | hrow
    · exact Or.inl (Or.inl hfixed)
    · obtain ⟨j, _, hj⟩ := hzero
      exact Or.inl (Or.inr ⟨j, hj⟩)
    · obtain ⟨i, j, hj, heq⟩ := hrow
      exact Or.inr ⟨i, j, by rwa [stage_cut_eq] at hj, heq⟩
  · rintro x ((hfixed | ⟨i, rfl⟩) | ⟨i, j, hj, rfl⟩)
    · apply history_mem_range criterion G hG 0
      exact ((stage criterion G hG 0).values x).mpr (Or.inl hfixed)
    · apply history_mem_range criterion G hG (i + 1)
      exact ((stage criterion G hG (i + 1)).values _).mpr
        (Or.inr (Or.inl ⟨i, by omega, rfl⟩))
    · apply history_mem_range criterion G hG (i + 1)
      apply ((stage criterion G hG (i + 1)).values _).mpr
      refine Or.inr (Or.inr ⟨⟨i, by omega⟩, j, ?_, rfl⟩)
      rwa [stage_cut_eq]

theorem output_at_phase (n : ℕ) :
    output G (chain criterion G hG).stream (stage criterion G hG (n + 1)).history.length ∈
      A (n + 1) := by
  have hout := (phase criterion G hG (stage criterion G hG n)).output_current
  change historyOutput G (stage criterion G hG (n + 1)).history ∈ A (n + 1) at hout
  have heq : output G (chain criterion G hG).stream
      (stage criterion G hG (n + 1)).history.length =
      historyOutput G (stage criterion G hG (n + 1)).history := by
    unfold output historyOutput
    congr 1
    funext i
    exact (chain criterion G hG).stream_eq_get (n + 1) i i.isLt
  rwa [heq]

/-- The stopped rows split into the already observed finite prefix and
future rows. This is the finite-prefix/future distinction required by C.2. -/
theorem stopped_subset_past_union_future (n : ℕ) :
    stopped row (chosenCut criterion G hG) ⊆
      (sample (chain criterion G hG).stream
        (stage criterion G hG (n + 1)).history.length : Set α) ∪ future row (n + 1) := by
  classical
  rintro x ⟨i, j, hj, heq⟩
  by_cases hi : i < n + 1
  · apply Or.inl
    change x ∈ sample (chain criterion G hG).stream
      ((chain criterion G hG).history (n + 1)).length
    rw [(chain criterion G hG).sample_stream_at_history (n + 1)]
    apply List.mem_toFinset.mpr
    apply ((stage criterion G hG (n + 1)).values x).mpr
    refine Or.inr (Or.inr ⟨⟨i, hi⟩, j, ?_, heq⟩)
    rwa [stage_cut_eq]
  · exact Or.inr ⟨i + 1, j, by omega, heq⟩

end

end RowDiagonal

/-- Appendix Lemma C.2 (arXiv v2). The exact target-membership and coverage
hypotheses are packaged in `RowDiagonal.Criterion`. The proof does not need
extra UUS or metric assumptions once this criterion is supplied. -/
theorem lemma_C_2_not_generatable
    {α : Type*} {ρ : Distance α} {ε ε' : ℝ} {H : GenLimit.Generic.LanguageClass α}
    {fixed : List α} {row : ℕ → GenLimit.Generic.Stream α} {A : ℕ → Set α}
    (criterion : RowDiagonal.Criterion ρ ε ε' H fixed row A) :
    ¬ GeneratableInLimitAt ρ ε ε' H := by
  classical
  rintro ⟨G, hG⟩
  let cut := RowDiagonal.chosenCut criterion G hG
  let chain := RowDiagonal.chain criterion G hG
  have hpositive : ∀ i, 0 < cut i := fun i =>
    (RowDiagonal.phase criterion G hG (RowDiagonal.stage criterion G hG i)).positive
  obtain ⟨L, hLH, hmem, hcover, hparts⟩ := criterion.final_target cut hpositive
  have hrange : Set.range chain.stream = RowDiagonal.observations fixed row cut :=
    RowDiagonal.chain_range criterion G hG
  have hp : MetricPresentation ρ ε chain.stream L := by
    constructor
    · change Set.range chain.stream ⊆ L
      rwa [hrange]
    · rwa [hrange]
  obtain ⟨T, hT⟩ := hG L hLH chain.stream hp
  let t := (RowDiagonal.stage criterion G hG (T + 1)).history.length
  have ht : T ≤ t := (Nat.le_succ T).trans (RowDiagonal.stage_length criterion G hG (T + 1))
  have hcorrect := hT t ht
  have hout : GenLimit.Generic.output G chain.stream t ∈ A (T + 1) :=
    RowDiagonal.output_at_phase criterion G hG T
  have hfixed : {x | x ∈ fixed} ⊆ (GenLimit.Generic.sample chain.stream t : Set α) := by
    intro x hx
    change x ∈ GenLimit.Generic.sample chain.stream (chain.history (T + 1)).length
    rw [chain.sample_stream_at_history (T + 1)]
    apply List.mem_toFinset.mpr
    exact ((RowDiagonal.stage criterion G hG (T + 1)).values x).mpr (Or.inl hx)
  rcases hparts hcorrect.1 with (hfixedNear | hA0) | hstoppedNear
  · exact hcorrect.2 (inClosedNeighborhood_mono_centers hfixed hfixedNear)
  · exact Set.disjoint_left.mp (criterion.separated T) hout (Or.inl hA0)
  · have hnear := inClosedNeighborhood_mono_centers
      (RowDiagonal.stopped_subset_past_union_future criterion G hG T) hstoppedNear
    rw [closedNeighborhood_union] at hnear
    rcases hnear with hpast | hfuture
    · exact hcorrect.2 hpast
    · exact Set.disjoint_left.mp (criterion.separated T) hout (Or.inr hfuture)

end GenLimit.MetricSpaces
