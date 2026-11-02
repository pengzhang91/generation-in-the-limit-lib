import GenLimit.Paper21_GenerationInMetricSpaces.RowDiagonal
import Mathlib.Data.Set.Finite.Lattice

/-!
# Diagonal selection of infinitely many finite blocks

The negative Hilbert-space examples select new indices while excluding
predictions about future blocks. Pairwise disjoint blocks make the set of
indices forbidden by finitely many predictions finite.
-/

namespace GenLimit.MetricSpaces.BlockDiagonal

open GenLimit.Generic GenLimit.Support

noncomputable section

variable {α : Type*}

local instance : DecidableEq α := Classical.decEq α

theorem exists_unused_block
    {K : Set ℕ} (hK : K.Infinite) (blocks : ℕ → Finset α)
    (hdisjoint : ∀ i ∈ K, ∀ j ∈ K, i ≠ j →
      Disjoint (blocks i : Set α) (blocks j : Set α))
    (used : Finset ℕ) (predictions : Finset α) :
    ∃ i ∈ K, i ∉ used ∧ ∀ x ∈ blocks i, x ∉ predictions := by
  classical
  let bad := fun x : α => {i | i ∈ K ∧ x ∈ blocks i}
  have hbad : ∀ x, (bad x).Finite := by
    intro x
    apply Set.Subsingleton.finite
    intro i hi j hj
    by_contra hne
    exact Set.disjoint_left.mp (hdisjoint i hi.1 j hj.1 hne) hi.2 hj.2
  have hblocked : (⋃ x ∈ (predictions : Set α), bad x).Finite :=
    predictions.finite_toSet.biUnion (fun x _ => hbad x)
  obtain ⟨i, hiK, hiAvoid⟩ :=
    (hK.diff (used.finite_toSet.union hblocked)).nonempty
  refine ⟨i, hiK, fun hi => hiAvoid (Or.inl hi), ?_⟩
  intro x hx hpred
  apply hiAvoid
  exact Or.inr (Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hpred, hiK, hx⟩⟩)

structure State (α : Type*) where
  chosen : Finset ℕ
  predictions : Finset α
  history : List α

variable {K : Set ℕ} (hK : K.Infinite) (blocks : ℕ → Finset α)
variable (hdisjoint : ∀ i ∈ K, ∀ j ∈ K, i ≠ j →
  Disjoint (blocks i : Set α) (blocks j : Set α))

def nextIndex (state : State α) : ℕ :=
  Classical.choose (exists_unused_block hK blocks hdisjoint state.chosen state.predictions)

theorem nextIndex_spec (state : State α) :
    nextIndex hK blocks hdisjoint state ∈ K ∧
      nextIndex hK blocks hdisjoint state ∉ state.chosen ∧
      ∀ x ∈ blocks (nextIndex hK blocks hdisjoint state), x ∉ state.predictions :=
  Classical.choose_spec (exists_unused_block hK blocks hdisjoint state.chosen state.predictions)

variable (base : Stream α) (aux : ℕ → Stream α) (G : Generator α)

def auxiliaryPrefix (selected : Finset ℕ) (n : ℕ) : List α :=
  selected.toList.flatMap (fun i => RowDiagonal.prefixList (aux i) (n + 1))

def step (n : ℕ) (old : State α) : State α :=
  let i := nextIndex hK blocks hdisjoint old
  let chosen := insert i old.chosen
  let history := old.history ++ [base (n + 1)] ++ (blocks i).toList ++ auxiliaryPrefix aux chosen n
  { chosen := chosen
    predictions := insert (RowDiagonal.historyOutput G history) old.predictions
    history := history }

def run : ℕ → State α
  | 0 => ⟨∅, ∅, [base 0]⟩
  | n + 1 => step hK blocks hdisjoint base aux G n (run n)

def selectedIndex (n : ℕ) : ℕ := nextIndex hK blocks hdisjoint (run hK blocks hdisjoint base aux G n)

def selected : Set ℕ := Set.range (selectedIndex hK blocks hdisjoint base aux G)


theorem chosen_mono (n : ℕ) :
    (run hK blocks hdisjoint base aux G n).chosen ⊆
      (run hK blocks hdisjoint base aux G (n + 1)).chosen := by
  exact Finset.subset_insert _ _

theorem selectedIndex_mem_chosen {i n : ℕ} (hi : i < n) :
    selectedIndex hK blocks hdisjoint base aux G i ∈
      (run hK blocks hdisjoint base aux G n).chosen := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hin : i < n
    · exact chosen_mono hK blocks hdisjoint base aux G n (ih hin)
    · have hieq : i = n := by omega
      subst i
      exact Finset.mem_insert_self _ _

theorem selectedIndex_injective :
    Function.Injective (selectedIndex hK blocks hdisjoint base aux G) := by
  intro i j heq
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hnot : selectedIndex hK blocks hdisjoint base aux G j ∉
        (run hK blocks hdisjoint base aux G j).chosen :=
      (nextIndex_spec hK blocks hdisjoint (run hK blocks hdisjoint base aux G j)).2.1
    apply hnot
    rw [← heq]
    exact selectedIndex_mem_chosen hK blocks hdisjoint base aux G hij
  · have hnot : selectedIndex hK blocks hdisjoint base aux G i ∉
        (run hK blocks hdisjoint base aux G i).chosen :=
      (nextIndex_spec hK blocks hdisjoint (run hK blocks hdisjoint base aux G i)).2.1
    apply hnot
    rw [heq]
    exact selectedIndex_mem_chosen hK blocks hdisjoint base aux G hji

theorem selected_infinite : (selected hK blocks hdisjoint base aux G).Infinite :=
  Set.infinite_range_of_injective (selectedIndex_injective hK blocks hdisjoint base aux G)

theorem selected_subset : selected hK blocks hdisjoint base aux G ⊆ K := by
  rintro i ⟨n, rfl⟩
  exact (nextIndex_spec hK blocks hdisjoint (run hK blocks hdisjoint base aux G n)).1

theorem chosen_mem_iff (i n : ℕ) :
    i ∈ (run hK blocks hdisjoint base aux G n).chosen ↔
      ∃ j, j < n ∧ selectedIndex hK blocks hdisjoint base aux G j = i := by
  constructor
  · induction n with
    | zero => simp [run]
    | succ n ih =>
      intro hi
      change i ∈ insert (selectedIndex hK blocks hdisjoint base aux G n)
        (run hK blocks hdisjoint base aux G n).chosen at hi
      rcases Finset.mem_insert.mp hi with heq | hold
      · exact ⟨n, by omega, heq.symm⟩
      · obtain ⟨j, hj, heq⟩ := ih hold
        exact ⟨j, by omega, heq⟩
  · rintro ⟨j, hj, rfl⟩
    exact selectedIndex_mem_chosen hK blocks hdisjoint base aux G hj

theorem history_prefix (n : ℕ) :
    (run hK blocks hdisjoint base aux G n).history <+:
      (run hK blocks hdisjoint base aux G (n + 1)).history := by
  change (run hK blocks hdisjoint base aux G n).history <+:
    (((run hK blocks hdisjoint base aux G n).history ++ [base (n + 1)]) ++ _) ++ _
  exact ((List.prefix_append ..).trans (List.prefix_append ..)).trans (List.prefix_append ..)

theorem history_length (n : ℕ) :
    n ≤ (run hK blocks hdisjoint base aux G n).history.length := by
  induction n with
  | zero => omega
  | succ n ih =>
    change n + 1 ≤ ((((run hK blocks hdisjoint base aux G n).history ++
      [base (n + 1)]) ++ _ ) ++ _).length
    simp only [List.length_append, List.length_singleton]
    omega

def chain : HistoryChain α where
  history n := (run hK blocks hdisjoint base aux G n).history
  prefix_succ := history_prefix hK blocks hdisjoint base aux G
  le_length := history_length hK blocks hdisjoint base aux G


def language (base : Stream α) (blocks : ℕ → Finset α) (aux : ℕ → Stream α)
    (I : Set ℕ) : Set α :=
  Set.range base ∪ {x | ∃ i ∈ I, x ∈ blocks i} ∪ {x | ∃ i ∈ I, ∃ j, aux i j = x}

theorem history_mem_range (n : ℕ) {x : α}
    (hx : x ∈ (run hK blocks hdisjoint base aux G n).history) :
    x ∈ Set.range (chain hK blocks hdisjoint base aux G).stream :=
  (chain hK blocks hdisjoint base aux G).history_toFinset_subset_stream_range n
    (List.mem_toFinset.mpr hx)

theorem block_mem_next_history (n : ℕ) {x : α}
    (hx : x ∈ blocks (selectedIndex hK blocks hdisjoint base aux G n)) :
    x ∈ (run hK blocks hdisjoint base aux G (n + 1)).history := by
  change x ∈ (((run hK blocks hdisjoint base aux G n).history ++ [base (n + 1)]) ++
    (blocks (selectedIndex hK blocks hdisjoint base aux G n)).toList) ++ _
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
    (Or.inr (Finset.mem_toList.mpr hx))))

theorem chosen_block_observed {n i : ℕ}
    (hi : i ∈ (run hK blocks hdisjoint base aux G n).chosen) {x : α}
    (hx : x ∈ blocks i) : x ∈ (run hK blocks hdisjoint base aux G n).history := by
  obtain ⟨j, hj, hji⟩ := (chosen_mem_iff hK blocks hdisjoint base aux G i n).mp hi
  have hp := (chain hK blocks hdisjoint base aux G).toPrefixChain.prefix_of_le
    (Nat.succ_le_of_lt hj)
  apply hp.subset
  apply block_mem_next_history hK blocks hdisjoint base aux G j
  rwa [hji]

theorem history_values (n : ℕ) : ∀ x,
    x ∈ (run hK blocks hdisjoint base aux G n).history →
      x ∈ language base blocks aux (selected hK blocks hdisjoint base aux G) := by
  induction n with
  | zero =>
    intro x hx
    have : x = base 0 := by simpa [run] using hx
    subst x
    exact Or.inl (Or.inl ⟨0, rfl⟩)
  | succ n ih =>
    intro x hx
    change x ∈ (((run hK blocks hdisjoint base aux G n).history ++ [base (n + 1)]) ++
      (blocks (selectedIndex hK blocks hdisjoint base aux G n)).toList) ++
      auxiliaryPrefix aux (run hK blocks hdisjoint base aux G (n + 1)).chosen n at hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with ((hold | hbase) | hblock) | haux
    · exact ih x hold
    · subst x
      exact Or.inl (Or.inl ⟨n + 1, rfl⟩)
    · exact Or.inl (Or.inr ⟨selectedIndex hK blocks hdisjoint base aux G n,
        ⟨n, rfl⟩, Finset.mem_toList.mp hblock⟩)
    · obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp haux
      have hi' := (chosen_mem_iff hK blocks hdisjoint base aux G i (n + 1)).mp
        (Finset.mem_toList.mp hi)
      obtain ⟨j, _, hj⟩ := hi'
      obtain ⟨k, _, hk⟩ := RowDiagonal.mem_prefixList.mp hxi
      exact Or.inr ⟨i, ⟨j, hj⟩, k, hk⟩

theorem chain_range : Set.range (chain hK blocks hdisjoint base aux G).stream =
    language base blocks aux (selected hK blocks hdisjoint base aux G) := by
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    exact history_values hK blocks hdisjoint base aux G (n + 1) _ (List.get_mem _ _)
  · rintro x ((⟨n, rfl⟩ | ⟨i, ⟨n, hn⟩, hblock⟩) | ⟨i, ⟨j, hj⟩, k, rfl⟩)
    · cases n with
      | zero => exact history_mem_range hK blocks hdisjoint base aux G 0 (by simp [run])
      | succ n =>
        apply history_mem_range hK blocks hdisjoint base aux G (n + 1)
        change base (n + 1) ∈ (((run hK blocks hdisjoint base aux G n).history ++
          [base (n + 1)]) ++ _) ++ _
        exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
          (Or.inl (List.mem_append.mpr (Or.inr (by simp))))))
    · subst i
      exact history_mem_range hK blocks hdisjoint base aux G (n + 1)
        (block_mem_next_history hK blocks hdisjoint base aux G n hblock)
    · let n := max j k
      have hjn : j < n + 1 := Nat.lt_succ_of_le (Nat.le_max_left _ _)
      have hkn : k < n + 1 := Nat.lt_succ_of_le (Nat.le_max_right _ _)
      have hchosen : i ∈ (run hK blocks hdisjoint base aux G (n + 1)).chosen := by
        rw [← hj]
        exact selectedIndex_mem_chosen hK blocks hdisjoint base aux G hjn
      apply history_mem_range hK blocks hdisjoint base aux G (n + 1)
      change aux i k ∈ (((run hK blocks hdisjoint base aux G n).history ++
        [base (n + 1)]) ++ _) ++
        auxiliaryPrefix aux (run hK blocks hdisjoint base aux G (n + 1)).chosen n
      apply List.mem_append.mpr
      apply Or.inr
      apply List.mem_flatMap.mpr
      exact ⟨i, Finset.mem_toList.mpr hchosen, RowDiagonal.mem_prefixList.mpr ⟨k, hkn, rfl⟩⟩


theorem predictions_mono (n : ℕ) :
    (run hK blocks hdisjoint base aux G n).predictions ⊆
      (run hK blocks hdisjoint base aux G (n + 1)).predictions :=
  Finset.subset_insert _ _

theorem predictions_mono_of_le {n m : ℕ} (hnm : n ≤ m) :
    (run hK blocks hdisjoint base aux G n).predictions ⊆
      (run hK blocks hdisjoint base aux G m).predictions := by
  induction m, hnm using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ m hnm ih => exact ih.trans (predictions_mono hK blocks hdisjoint base aux G m)

theorem current_prediction_mem {n m : ℕ} (hnm : n + 1 ≤ m) :
    RowDiagonal.historyOutput G (run hK blocks hdisjoint base aux G (n + 1)).history ∈
      (run hK blocks hdisjoint base aux G m).predictions :=
  predictions_mono_of_le hK blocks hdisjoint base aux G hnm (Finset.mem_insert_self ..)

theorem sample_at_history (n : ℕ) :
    sample (chain hK blocks hdisjoint base aux G).stream
      (run hK blocks hdisjoint base aux G n).history.length =
      (run hK blocks hdisjoint base aux G n).history.toFinset :=
  (chain hK blocks hdisjoint base aux G).sample_stream_at_history n

theorem output_at_history (n : ℕ) :
    output G (chain hK blocks hdisjoint base aux G).stream
      (run hK blocks hdisjoint base aux G n).history.length =
      RowDiagonal.historyOutput G (run hK blocks hdisjoint base aux G n).history := by
  unfold output RowDiagonal.historyOutput
  congr 1
  funext i
  exact (chain hK blocks hdisjoint base aux G).stream_eq_get n i i.isLt

/-- Every phase-end output fails for the single target selected by the
construction. Previously selected block points have been observed; future
blocks exclude this prediction; base and auxiliary points are non-novel. -/
theorem failure_at_phase {ρ : Distance α} {ε' : ℝ}
    (hrefl : ∀ x, ρ x x = 0) (hε' : 0 ≤ ε')
    (hbase : Set.range base ⊆ closedNeighborhood ρ {base 0} ε')
    (haux : ∀ i ∈ K, Set.range (aux i) ⊆ closedNeighborhood ρ {base 0} ε') (n : ℕ) :
    ¬ MetricCorrectAt ρ ε' G (language base blocks aux (selected hK blocks hdisjoint base aux G))
      (chain hK blocks hdisjoint base aux G).stream
      (run hK blocks hdisjoint base aux G (n + 1)).history.length := by
  intro hcorrect
  have hzeroHistory : base 0 ∈ (run hK blocks hdisjoint base aux G (n + 1)).history := by
    apply ((chain hK blocks hdisjoint base aux G).toPrefixChain.prefix_of_le
      (Nat.zero_le (n + 1))).subset
    simp [chain, run]
  have hzero : base 0 ∈ sample (chain hK blocks hdisjoint base aux G).stream
      (run hK blocks hdisjoint base aux G (n + 1)).history.length := by
    rw [sample_at_history]
    exact List.mem_toFinset.mpr hzeroHistory
  have hsingleton : ({base 0} : Set α) ⊆
      (sample (chain hK blocks hdisjoint base aux G).stream
        (run hK blocks hdisjoint base aux G (n + 1)).history.length : Set α) := by
    intro x hx
    have hx0 : x = base 0 := Set.mem_singleton_iff.mp hx
    simpa [hx0] using hzero
  rcases hcorrect.1 with (hb | ⟨i, ⟨j, hji⟩, hi⟩) | ⟨i, hI, k, hk⟩
  · exact hcorrect.2 (inClosedNeighborhood_mono_centers hsingleton (hbase hb))
  · by_cases hj : j < n + 1
    · have hchosen : i ∈ (run hK blocks hdisjoint base aux G (n + 1)).chosen := by
        rw [← hji]
        exact selectedIndex_mem_chosen hK blocks hdisjoint base aux G hj
      have hseen := chosen_block_observed hK blocks hdisjoint base aux G hchosen hi
      apply hcorrect.2
      intro η hη
      refine ⟨output G (chain hK blocks hdisjoint base aux G).stream
        (run hK blocks hdisjoint base aux G (n + 1)).history.length, ?_, ?_⟩
      · rw [sample_at_history]
        exact List.mem_toFinset.mpr hseen
      · rw [hrefl]
        exact lt_of_le_of_lt hε' hη
    · have hpred := current_prediction_mem hK blocks hdisjoint base aux G
        (n := n) (m := j) (by omega)
      have hforbid := (nextIndex_spec hK blocks hdisjoint
        (run hK blocks hdisjoint base aux G j)).2.2
      apply hforbid (output G (chain hK blocks hdisjoint base aux G).stream
        (run hK blocks hdisjoint base aux G (n + 1)).history.length)
      · change output G (chain hK blocks hdisjoint base aux G).stream
          (run hK blocks hdisjoint base aux G (n + 1)).history.length ∈
          blocks (selectedIndex hK blocks hdisjoint base aux G j)
        rwa [hji]
      · rwa [output_at_history]
  · exact hcorrect.2 (inClosedNeighborhood_mono_centers hsingleton
      (haux i (selected_subset hK blocks hdisjoint base aux G hI) ⟨k, hk⟩))

end

end GenLimit.MetricSpaces.BlockDiagonal

namespace GenLimit.MetricSpaces

/-- A semantic diagonal obstruction for arbitrary infinite subfamilies of
disjoint finite blocks, with any additional points already non-novel after
one fixed observation. The stream enumerates the selected target exactly. -/
theorem not_limit_of_infinite_blocks
    {α : Type*} {ρ : Distance α} {ε ε' : ℝ} {H : GenLimit.Generic.LanguageClass α}
    {K : Set ℕ} (hK : K.Infinite) (blocks : ℕ → Finset α)
    (hdisjoint : ∀ i ∈ K, ∀ j ∈ K, i ≠ j →
      Disjoint (blocks i : Set α) (blocks j : Set α))
    (base : GenLimit.Generic.Stream α) (aux : ℕ → GenLimit.Generic.Stream α)
    (hrefl : ∀ x, ρ x x = 0) (hε : 0 ≤ ε) (hε' : 0 ≤ ε')
    (hbase : Set.range base ⊆ closedNeighborhood ρ {base 0} ε')
    (haux : ∀ i ∈ K, Set.range (aux i) ⊆ closedNeighborhood ρ {base 0} ε')
    (hTargets : ∀ I : Set ℕ, I.Infinite → I ⊆ K → BlockDiagonal.language base blocks aux I ∈ H) :
    ¬ GeneratableInLimitAt ρ ε ε' H := by
  classical
  rintro ⟨G, hG⟩
  let I := BlockDiagonal.selected hK blocks hdisjoint base aux G
  let chain := BlockDiagonal.chain hK blocks hdisjoint base aux G
  have hI : I.Infinite := BlockDiagonal.selected_infinite hK blocks hdisjoint base aux G
  have hIK : I ⊆ K := BlockDiagonal.selected_subset hK blocks hdisjoint base aux G
  have hrange : Set.range chain.stream = BlockDiagonal.language base blocks aux I :=
    BlockDiagonal.chain_range hK blocks hdisjoint base aux G
  have hp : MetricPresentation ρ ε chain.stream (BlockDiagonal.language base blocks aux I) := by
    constructor
    · change Set.range chain.stream ⊆ _
      exact hrange.subset
    · intro x hx η hη
      exact ⟨x, hrange.symm ▸ hx, by rw [hrefl]; exact lt_of_le_of_lt hε hη⟩
  obtain ⟨T, hT⟩ := hG _ (hTargets I hI hIK) chain.stream hp
  have hcorrect := hT (BlockDiagonal.run hK blocks hdisjoint base aux G (T + 1)).history.length
    ((Nat.le_succ T).trans (BlockDiagonal.history_length hK blocks hdisjoint base aux G (T + 1)))
  exact BlockDiagonal.failure_at_phase hK blocks hdisjoint base aux G hrefl hε' hbase haux T hcorrect

end GenLimit.MetricSpaces
