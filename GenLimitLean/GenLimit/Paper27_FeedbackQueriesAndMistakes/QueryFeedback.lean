import GenLimit.Paper27_FeedbackQueriesAndMistakes.MistakeFeedback
import GenLimit.Support.EnumerationProgress
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Finset

/-!
# Set generation with membership-query feedback

This file proves a countable-inner-cover characterization in an auxiliary
finite nonadaptive-query normal form.  In round `t` the strategy asks a square
table of `(t+1)^2` membership queries and maps the finite Boolean answer table
to a set output.  Any fixed finite adaptive tree can be expanded into a finite
table if efficiency is ignored; that normalization is not claimed as a
machine-level or running-time theorem here.

Definition 2 instead gives one cross-round membership query,
requires all outputs to be infinite, and requires eventual outputs to avoid
the positive sample.  Its literal semantic/classical Theorem 3.4 is in
`SourceQuery.lean`.  The square theorem below remains useful scheduling
infrastructure, but is not itself the source statement.
-/

namespace GenLimit.FeedbackQueries

open GenLimit.Generic

/-- A finite membership-query strategy in square-table normal form. -/
structure SetQueryStrategy (α : Type*) where
  query : ∀ t, Fin (t + 1) → Fin (t + 1) → α
  output :
    ∀ t, (Fin (t + 1) → Fin (t + 1) → Bool) → Set α

/-- The truthful Boolean answer to a membership query. -/
noncomputable def membershipAnswer
    (target : Set α) (x : α) : Bool := by
  classical
  exact decide (x ∈ target)

theorem membershipAnswer_eq_true_iff
    (target : Set α) (x : α) :
    membershipAnswer target x = true ↔ x ∈ target := by
  classical
  simp [membershipAnswer]

/-- The canonical square table of truthful answers in round `t`. -/
noncomputable def truthfulQueryTable
    (strategy : SetQueryStrategy α)
    (target : Set α) (t : ℕ) :
    Fin (t + 1) → Fin (t + 1) → Bool :=
  fun i k => membershipAnswer target (strategy.query t i k)

theorem truthfulQueryTable_apply
    (strategy : SetQueryStrategy α)
    (target : Set α) (t i k : ℕ)
    (hi : i < t + 1) (hk : k < t + 1) :
    truthfulQueryTable strategy target t ⟨i, hi⟩ ⟨k, hk⟩ =
        membershipAnswer target
          (strategy.query t ⟨i, hi⟩ ⟨k, hk⟩) := by
  rfl

/-- The actual set output in round `t` against a truthful target oracle. -/
noncomputable def setQueryOutput
    (strategy : SetQueryStrategy α)
    (target : Set α) (t : ℕ) : Set α :=
  strategy.output t (truthfulQueryTable strategy target t)

/-- Eventual set generation using finite membership queries. -/
def SetQuerySucceedsOn
    (strategy : SetQueryStrategy α)
    (target : Set α) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    (setQueryOutput strategy target t).Infinite ∧
      setQueryOutput strategy target t ⊆ target

def SetQueryGenerates
    (strategy : SetQueryStrategy α)
    (targets : LanguageClass α) : Prop :=
  ∀ L, L ∈ targets → SetQuerySucceedsOn strategy L

def SetQueryGeneratable
    (targets : LanguageClass α) : Prop :=
  ∃ strategy : SetQueryStrategy α,
    SetQueryGenerates strategy targets

/-! ## Necessity: finite query transcripts yield a countable inner cover -/

/-- Encode a finite Boolean table as the finite set of coordinates answered
`true`. -/
noncomputable def encodeQueryTable
    (t : ℕ)
    (table : Fin (t + 1) → Fin (t + 1) → Bool) :
    Finset (ℕ × ℕ) := by
  classical
  exact
    ((Finset.univ :
        Finset (Fin (t + 1) × Fin (t + 1))).filter
      (fun p => table p.1 p.2 = true)).image
        (fun p => (p.1.1, p.2.1))

/-- Decode any finite set of positive coordinates into a Boolean table. -/
noncomputable def decodeQueryTable
    (t : ℕ) (positive : Finset (ℕ × ℕ)) :
    Fin (t + 1) → Fin (t + 1) → Bool := by
  classical
  exact fun i k => decide ((i.1, k.1) ∈ positive)

theorem decode_encodeQueryTable
    (t : ℕ)
    (table : Fin (t + 1) → Fin (t + 1) → Bool) :
    decodeQueryTable t (encodeQueryTable t table) = table := by
  classical
  funext i k
  cases hanswer : table i k with
  | false =>
      have hnot :
          (i.1, k.1) ∉ encodeQueryTable t table := by
        intro hmem
        rw [encodeQueryTable] at hmem
        obtain ⟨p, hp, hpval⟩ := Finset.mem_image.mp hmem
        have hptrue :
            table p.1 p.2 = true :=
          (Finset.mem_filter.mp hp).2
        have hpi : p.1 = i := by
          apply Fin.ext
          exact congrArg Prod.fst hpval
        have hpk : p.2 = k := by
          apply Fin.ext
          exact congrArg Prod.snd hpval
        rw [hpi, hpk, hanswer] at hptrue
        contradiction
      simp [decodeQueryTable, hnot]
  | true =>
      have hmem :
          (i.1, k.1) ∈ encodeQueryTable t table := by
        rw [encodeQueryTable]
        apply Finset.mem_image.mpr
        refine ⟨(i, k), ?_, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hanswer⟩
      simp [decodeQueryTable, hmem]

/-- Countable code for a round number and its finite Boolean answer table. -/
abbrev QueryTranscript := ℕ × Finset (ℕ × ℕ)

noncomputable def countableInnerCoverOfSetQuery
    [Infinite α]
    {targets : LanguageClass α}
    (strategy : SetQueryStrategy α)
    (hstrategy : SetQueryGenerates strategy targets) :
    CountableInnerCover targets := by
  let output : QueryTranscript → Set α := fun transcript =>
    strategy.output transcript.1
      (decodeQueryTable transcript.1 transcript.2)
  apply CountableInnerCover.ofCountableOutputs output
  intro L hL
  obtain ⟨T, hT⟩ := hstrategy L hL
  have hgood := hT T (Nat.le_refl T)
  refine ⟨(T, encodeQueryTable T
    (truthfulQueryTable strategy L T)), ?_, ?_⟩
  · simpa [output, decode_encodeQueryTable] using hgood.1
  · simpa [output, decode_encodeQueryTable] using hgood.2

theorem setQuery_implies_countableInnerCover
    [Infinite α]
    {targets : LanguageClass α}
    (h : SetQueryGeneratable targets) :
    HasCountableInnerCover targets := by
  obtain ⟨strategy, hstrategy⟩ := h
  exact ⟨countableInnerCoverOfSetQuery strategy hstrategy⟩

/-! ## Sufficiency: finitely screen the first finitely many covers -/

/-- Candidate row `i` passes the finite table at round `t`. -/
def QueryRowPasses
    (t : ℕ)
    (table : Fin (t + 1) → Fin (t + 1) → Bool)
    (i : ℕ) : Prop :=
  i < t + 1 ∧
    ∀ hi : i < t + 1, ∀ k, ∀ hk : k < t + 1,
      table ⟨i, hi⟩ ⟨k, hk⟩ = true

/-- The least row passing the current finite screen, with a total fallback
used only when no row passes. -/
noncomputable def firstPassingQueryRow
    (t : ℕ)
    (table : Fin (t + 1) → Fin (t + 1) → Bool) : ℕ := by
  classical
  exact if h : ∃ i, QueryRowPasses t table i
    then Nat.find h
    else 0

theorem firstPassingQueryRow_spec
    {t : ℕ}
    {table : Fin (t + 1) → Fin (t + 1) → Bool}
    (hexists : ∃ i, QueryRowPasses t table i) :
    QueryRowPasses t table (firstPassingQueryRow t table) := by
  classical
  simp only [firstPassingQueryRow, dif_pos hexists]
  exact Nat.find_spec hexists

theorem firstPassingQueryRow_le
    {t : ℕ}
    {table : Fin (t + 1) → Fin (t + 1) → Bool}
    (hexists : ∃ i, QueryRowPasses t table i)
    {i : ℕ} (hi : QueryRowPasses t table i) :
    firstPassingQueryRow t table ≤ i := by
  classical
  simp only [firstPassingQueryRow, dif_pos hexists]
  exact Nat.find_min' hexists hi

/-- Query the first `t+1` points of each of the first `t+1` inner-cover
members, then output the least row with no negative answer. -/
noncomputable def innerCoverSetQueryStrategy
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets) :
    SetQueryStrategy α where
  query := fun _t i k =>
    GenLimit.Support.infiniteEnumeration
      (inner.cover i) (inner.infinite_cover i) k
  output := fun t table =>
    inner.cover (firstPassingQueryRow t table)

theorem innerCover_truthful_rowPasses_iff
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (L : Set α) (t i : ℕ) :
    QueryRowPasses t
        (truthfulQueryTable (innerCoverSetQueryStrategy inner) L t) i ↔
      i < t + 1 ∧
        ∀ k, k < t + 1 →
          GenLimit.Support.infiniteEnumeration
              (inner.cover i) (inner.infinite_cover i) k ∈ L := by
  constructor
  · rintro ⟨hi, hrow⟩
    refine ⟨hi, ?_⟩
    intro k hk
    have hans := hrow hi k hk
    change
      membershipAnswer L
          (GenLimit.Support.infiniteEnumeration
            (inner.cover i) (inner.infinite_cover i) k) =
        true at hans
    exact (membershipAnswer_eq_true_iff _ _).mp hans
  · rintro ⟨hi, hrow⟩
    refine ⟨hi, ?_⟩
    intro _hi k hk
    change
      membershipAnswer L
          (GenLimit.Support.infiniteEnumeration
            (inner.cover i) (inner.infinite_cover i) k) =
        true
    exact (membershipAnswer_eq_true_iff _ _).mpr (hrow k hk)

private theorem countableInnerCover_query_eventually
    [Countable α]
    {targets : LanguageClass α}
    (inner : CountableInnerCover targets)
    (L : Set α)
    (k : ℕ)
    (hgood : inner.cover k ⊆ L)
    (hminimal : ∀ i, i < k → ¬ inner.cover i ⊆ L) :
    ∃ T, ∀ t, T ≤ t →
      setQueryOutput (innerCoverSetQueryStrategy inner) L t =
        inner.cover k := by
  classical
  have hbadExists (i : Fin k) :
      ∃ n,
        GenLimit.Support.infiniteEnumeration
            (inner.cover i) (inner.infinite_cover i) n ∉ L := by
    obtain ⟨x, hxcover, hxL⟩ :=
      Set.not_subset.mp (hminimal i i.isLt)
    obtain ⟨n, hn⟩ :=
      GenLimit.Support.infiniteEnumeration_surjective
        (inner.cover i) (inner.infinite_cover i) hxcover
    exact ⟨n, by simpa [hn] using hxL⟩
  let bad : Fin k → ℕ :=
    fun i => Nat.find (hbadExists i)
  have hbad (i : Fin k) :
      GenLimit.Support.infiniteEnumeration
          (inner.cover i) (inner.infinite_cover i) (bad i) ∉ L := by
    exact Nat.find_spec (hbadExists i)
  let budget : ℕ := ∑ i : Fin k, (bad i + 1)
  let T := k + budget
  refine ⟨T, ?_⟩
  intro t hTt
  have hkt : k ≤ t :=
    le_trans (Nat.le_add_right k budget) hTt
  let table :=
    truthfulQueryTable (innerCoverSetQueryStrategy inner) L t
  have hkPass : QueryRowPasses t table k := by
    rw [innerCover_truthful_rowPasses_iff inner L t k]
    refine ⟨Nat.lt_succ_iff.mpr hkt, ?_⟩
    intro n _hn
    exact hgood
      (GenLimit.Support.infiniteEnumeration_mem
        (inner.cover k) (inner.infinite_cover k) n)
  have hexists : ∃ i, QueryRowPasses t table i :=
    ⟨k, hkPass⟩
  have hselected_le :
      firstPassingQueryRow t table ≤ k :=
    firstPassingQueryRow_le hexists hkPass
  have hselected_not_lt :
      ¬ firstPassingQueryRow t table < k := by
    intro hlt
    let i : Fin k := ⟨firstPassingQueryRow t table, hlt⟩
    have hibudget : bad i + 1 ≤ budget := by
      dsimp only [budget]
      exact Finset.single_le_sum
        (f := fun j : Fin k => bad j + 1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hbad_le_t : bad i < t + 1 := by
      have hbad_lt_budget : bad i < budget :=
        lt_of_lt_of_le (Nat.lt_succ_self (bad i)) hibudget
      have hbudget_le_T : budget ≤ T := by
        exact Nat.le_add_left budget k
      exact lt_of_lt_of_le hbad_lt_budget
        (le_trans hbudget_le_T
          (le_trans hTt (Nat.le_succ t)))
    have hselectedPass :=
      firstPassingQueryRow_spec hexists
    have hmember :
        GenLimit.Support.infiniteEnumeration
            (inner.cover i) (inner.infinite_cover i) (bad i) ∈ L := by
      have hrow :=
        (innerCover_truthful_rowPasses_iff inner L t
          (firstPassingQueryRow t table)).mp hselectedPass
      exact hrow.2 (bad i) hbad_le_t
    exact hbad i hmember
  have hselected :
      firstPassingQueryRow t table = k :=
    Nat.le_antisymm hselected_le
      (Nat.le_of_not_gt hselected_not_lt)
  change
    inner.cover
        (firstPassingQueryRow t
          (truthfulQueryTable (innerCoverSetQueryStrategy inner) L t)) =
      inner.cover k
  exact congrArg inner.cover hselected

theorem countableInnerCover_implies_setQuery
    [Countable α]
    {targets : LanguageClass α}
    (hinner : HasCountableInnerCover targets) :
    SetQueryGeneratable targets := by
  classical
  let inner := Nonempty.some hinner
  refine ⟨innerCoverSetQueryStrategy inner, ?_⟩
  intro L hL
  let hexists : ∃ i, inner.cover i ⊆ L :=
    inner.contained L hL
  let k := Nat.find hexists
  have hgood : inner.cover k ⊆ L := by
    simpa [k] using Nat.find_spec hexists
  have hminimal : ∀ i, i < k → ¬ inner.cover i ⊆ L := by
    intro i hi
    exact Nat.find_min hexists (by simpa [k] using hi)
  obtain ⟨T, hT⟩ :=
    countableInnerCover_query_eventually inner L k hgood hminimal
  refine ⟨T, ?_⟩
  intro t ht
  rw [hT t ht]
  exact ⟨inner.infinite_cover k, hgood⟩

/-- Characterization of the auxiliary square-table query model.  Source
Theorem 3.4 is `theorem_3_4_sourceSetQuery_characterization`. -/
theorem setQuery_squareCore_characterization
    [Countable α] [Infinite α]
    (targets : LanguageClass α) :
    SetQueryGeneratable targets ↔
      HasCountableInnerCover targets :=
  ⟨setQuery_implies_countableInnerCover,
    countableInnerCover_implies_setQuery⟩

end GenLimit.FeedbackQueries
