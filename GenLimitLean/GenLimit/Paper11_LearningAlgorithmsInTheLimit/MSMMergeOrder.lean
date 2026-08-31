import GenLimit.Paper11_LearningAlgorithmsInTheLimit.TaggedSimulation
import Mathlib.Data.Finset.Max
import Mathlib.Order.WellFounded

/-!
# Machine-independent maximum-similarity merge order

The proof of Theorem 21 uses a greedy maximum-similarity argument after
constructing the tagged two-step machine.  This file isolates the exact
finite-state argument that such a proof needs.

The result is deliberately conditional.  It proves that MSM terminates in a
complete sound configuration when:

* every sound incomplete configuration has an intended merge of score at
  least two;
* every unintended merge there has score at most one;
* intended merges preserve soundness;
* complete sound configurations are terminal; and
* every merge strictly decreases a natural-number measure.

These are machine-independent conditions on a finite candidate set.  The
printed proof does not establish the first two conditions for every
intermediate quotient (and its dummy-state sentence is incomplete), so this
file does not assert the unconditional MSM conclusion of Theorem 21.
-/

namespace GenLimit.LearningAlgorithmsLimit

variable {Candidate Config : Type*}

/-- A choice made by Maximum-Similarity Merging: it is an available
positive-score candidate whose score is maximal among all candidates. -/
def IsMSMChoice
    [DecidableEq Candidate]
    (candidates : Config → Finset Candidate)
    (score : Config → Candidate → ℕ)
    (config : Config) (choice : Candidate) : Prop :=
  choice ∈ candidates config ∧
    0 < score config choice ∧
    ∀ other ∈ candidates config,
      score config other ≤ score config choice

/-- One abstract MSM transition.  The candidate and score calculations may
depend on the current quotient configuration. -/
def MSMStep
    [DecidableEq Candidate]
    (candidates : Config → Finset Candidate)
    (score : Config → Candidate → ℕ)
    (merge : Config → Candidate → Config)
    (config next : Config) : Prop :=
  ∃ choice, IsMSMChoice candidates score config choice ∧
    next = merge config choice

/-- No positive-score maximum candidate remains. -/
def IsMSMTerminal
    [DecidableEq Candidate]
    (candidates : Config → Finset Candidate)
    (score : Config → Candidate → ℕ)
    (config : Config) : Prop :=
  ¬∃ choice, IsMSMChoice candidates score config choice

/-- The score-separation invariant needed by the greedy step: some intended
candidate has positive score strictly larger than every unintended one. -/
def SeparatesIntendedMerges
    [DecidableEq Candidate]
    (candidates : Config → Finset Candidate)
    (score : Config → Candidate → ℕ)
    (intended : Config → Candidate → Prop)
    (config : Config) : Prop :=
  ∃ good ∈ candidates config,
    intended config good ∧
      0 < score config good ∧
      ∀ bad ∈ candidates config,
        ¬intended config bad →
          score config bad < score config good

/-- A finite nonempty candidate set always contains a positive-score
maximum when it contains at least one positive-score candidate. -/
theorem exists_msmChoice_of_positive_candidate
    [DecidableEq Candidate]
    (candidates : Config → Finset Candidate)
    (score : Config → Candidate → ℕ)
    {config : Config} {candidate : Candidate}
    (hmem : candidate ∈ candidates config)
    (hpositive : 0 < score config candidate) :
    ∃ choice, IsMSMChoice candidates score config choice := by
  obtain ⟨choice, hchoice, hmax⟩ :=
    (candidates config).exists_max_image
      (score config) ⟨candidate, hmem⟩
  refine ⟨choice, hchoice, ?_, hmax⟩
  exact lt_of_lt_of_le hpositive (hmax candidate hmem)

/-- The abstract stopping rule agrees exactly with the paper's prose:
terminality means that every available similarity score is zero. -/
theorem msmTerminal_iff_all_scores_zero
    [DecidableEq Candidate]
    (candidates : Config → Finset Candidate)
    (score : Config → Candidate → ℕ)
    {config : Config} :
    IsMSMTerminal candidates score config ↔
      ∀ candidate ∈ candidates config,
        score config candidate = 0 := by
  constructor
  · intro hterminal candidate hmem
    apply Nat.eq_zero_of_not_pos
    intro hpositive
    obtain ⟨choice, hchoice⟩ :=
      exists_msmChoice_of_positive_candidate
        candidates score hmem hpositive
    exact hterminal ⟨choice, hchoice⟩
  · intro hall
    rintro ⟨choice, hchoice⟩
    have hzero := hall choice hchoice.1
    exact (by simpa [hzero] using hchoice.2.1)

/-- Under strict intended/unintended score separation, every maximizing
positive candidate is intended.  This is the missing local merge-order
implication in the printed Theorem 21 proof. -/
theorem msmChoice_intended_of_separation
    [DecidableEq Candidate]
    (candidates : Config → Finset Candidate)
    (score : Config → Candidate → ℕ)
    (intended : Config → Candidate → Prop)
    {config : Config} {choice : Candidate}
    (hchoice : IsMSMChoice candidates score config choice)
    (hseparation :
      SeparatesIntendedMerges candidates score intended config) :
    intended config choice := by
  rcases hchoice with ⟨hchoiceMem, _, hmax⟩
  rcases hseparation with
    ⟨good, hgoodMem, hgood, _, hdominates⟩
  by_contra hnotIntended
  have hlt :=
    hdominates choice hchoiceMem hnotIntended
  exact (not_lt_of_ge (hmax good hgoodMem)) hlt

/-- Source-shaped specialization: the paper's desired score regime
(`unintended ≤ 1`, some intended `≥ 2`) forces the greedy maximum to be an
intended merge. -/
theorem msmChoice_intended_of_unit_gap
    [DecidableEq Candidate]
    (candidates : Config → Finset Candidate)
    (score : Config → Candidate → ℕ)
    (intended : Config → Candidate → Prop)
    {config : Config} {choice good : Candidate}
    (hchoice : IsMSMChoice candidates score config choice)
    (hgoodMem : good ∈ candidates config)
    (hgood : intended config good)
    (hgoodScore : 2 ≤ score config good)
    (hbadScore :
      ∀ bad ∈ candidates config,
        ¬intended config bad → score config bad ≤ 1) :
    intended config choice := by
  apply msmChoice_intended_of_separation
    candidates score intended hchoice
  refine ⟨good, hgoodMem, hgood,
    lt_of_lt_of_le (by decide : 0 < 2) hgoodScore, ?_⟩
  intro bad hbadMem hbad
  exact lt_of_le_of_lt
    (hbadScore bad hbadMem hbad)
    (lt_of_lt_of_le (by decide : 1 < 2) hgoodScore)

/-- Reversing a merge relation makes it well-founded whenever every merge
strictly decreases a natural-number measure (for example, quotient-state
count). -/
theorem msmStep_reverse_wellFounded
    [DecidableEq Candidate]
    (candidates : Config → Finset Candidate)
    (score : Config → Candidate → ℕ)
    (merge : Config → Candidate → Config)
    (remaining : Config → ℕ)
    (hdecrease :
      ∀ config choice,
        IsMSMChoice candidates score config choice →
          remaining (merge config choice) < remaining config) :
    WellFounded
      (fun next config =>
        MSMStep candidates score merge config next) := by
  apply (measure remaining).wf.mono
  intro next config hstep
  rcases hstep with ⟨choice, hchoice, rfl⟩
  exact hdecrease config choice hchoice

/-- Every transition relation whose reverse is well-founded has a terminal
configuration reachable by finitely many forward steps. -/
theorem exists_terminal_reachable_of_reverse_wellFounded
    (step : Config → Config → Prop)
    (hwf : WellFounded (fun next config => step config next))
    (initial : Config) :
    ∃ final,
      Relation.ReflTransGen step initial final ∧
        ¬∃ next, step final next := by
  refine hwf.induction
    (C := fun config =>
      ∃ final,
        Relation.ReflTransGen step config final ∧
          ¬∃ next, step final next)
    initial ?_
  intro config ih
  by_cases hnext : ∃ next, step config next
  · obtain ⟨next, hstep⟩ := hnext
    obtain ⟨final, hrun, hterminal⟩ := ih next hstep
    exact ⟨final, Relation.ReflTransGen.head hstep hrun, hterminal⟩
  · exact ⟨config, Relation.ReflTransGen.refl, hnext⟩

/-- Soundness is preserved along every finite MSM run when incomplete sound
configurations satisfy separation, complete sound configurations are
terminal, and intended merges preserve soundness. -/
theorem msmRun_preserves_sound
    [DecidableEq Candidate]
    (candidates : Config → Finset Candidate)
    (score : Config → Candidate → ℕ)
    (merge : Config → Candidate → Config)
    (intended : Config → Candidate → Prop)
    (Sound Complete : Config → Prop)
    (hseparation :
      ∀ config, Sound config → ¬Complete config →
        SeparatesIntendedMerges candidates score intended config)
    (hpreserve :
      ∀ config choice, Sound config → intended config choice →
        Sound (merge config choice))
    (hcompleteTerminal :
      ∀ config, Sound config → Complete config →
        IsMSMTerminal candidates score config)
    {initial final : Config}
    (hrun :
      Relation.ReflTransGen
        (MSMStep candidates score merge) initial final)
    (hinitial : Sound initial) :
    Sound final := by
  induction hrun with
  | refl => exact hinitial
  | @tail middle final hrun hstep ih =>
      rcases hstep with ⟨choice, hchoice, rfl⟩
      by_cases hcomplete : Complete middle
      · have hterminal :=
          hcompleteTerminal middle ih hcomplete
        exact (hterminal ⟨choice, hchoice⟩).elim
      · exact hpreserve middle choice ih
          (msmChoice_intended_of_separation
            candidates score intended hchoice
            (hseparation middle ih hcomplete))

/-- Conditional machine-independent convergence theorem for the MSM part of
Theorem 21.  The unit score gap fixes the merge order, sound intended merges
preserve the invariant, and the decreasing measure forces termination at a
complete configuration. -/
theorem theorem_21_msm_merge_order_core
    [DecidableEq Candidate]
    (candidates : Config → Finset Candidate)
    (score : Config → Candidate → ℕ)
    (merge : Config → Candidate → Config)
    (remaining : Config → ℕ)
    (intended : Config → Candidate → Prop)
    (Sound Complete : Config → Prop)
    (initial : Config)
    (hinitial : Sound initial)
    (hgood :
      ∀ config, Sound config → ¬Complete config →
        ∃ good ∈ candidates config,
          intended config good ∧ 2 ≤ score config good)
    (hbad :
      ∀ config, Sound config → ¬Complete config →
        ∀ bad ∈ candidates config,
          ¬intended config bad → score config bad ≤ 1)
    (hpreserve :
      ∀ config choice, Sound config → intended config choice →
        Sound (merge config choice))
    (hcompleteTerminal :
      ∀ config, Sound config → Complete config →
        IsMSMTerminal candidates score config)
    (hdecrease :
      ∀ config choice,
        IsMSMChoice candidates score config choice →
          remaining (merge config choice) < remaining config) :
    ∃ final,
      Relation.ReflTransGen
          (MSMStep candidates score merge) initial final ∧
        Sound final ∧ Complete final ∧
        IsMSMTerminal candidates score final := by
  have hseparation :
      ∀ config, Sound config → ¬Complete config →
        SeparatesIntendedMerges candidates score intended config := by
    intro config hsound hincomplete
    obtain ⟨good, hgoodMem, hgoodIntended, hgoodScore⟩ :=
      hgood config hsound hincomplete
    refine ⟨good, hgoodMem, hgoodIntended,
      lt_of_lt_of_le (by decide : 0 < 2) hgoodScore, ?_⟩
    intro bad hbadMem hbadIntended
    exact lt_of_le_of_lt
      (hbad config hsound hincomplete bad hbadMem hbadIntended)
      (lt_of_lt_of_le (by decide : 1 < 2) hgoodScore)
  have hwf :
      WellFounded
        (fun next config =>
          MSMStep candidates score merge config next) :=
    msmStep_reverse_wellFounded
      candidates score merge remaining hdecrease
  obtain ⟨final, hrun, hterminalStep⟩ :=
    exists_terminal_reachable_of_reverse_wellFounded
      (MSMStep candidates score merge) hwf initial
  have hsound : Sound final :=
    msmRun_preserves_sound
      candidates score merge intended Sound Complete
      hseparation hpreserve hcompleteTerminal hrun hinitial
  have hterminal : IsMSMTerminal candidates score final := by
    intro hchoice
    obtain ⟨choice, hchoice⟩ := hchoice
    exact hterminalStep
      ⟨merge final choice, ⟨choice, hchoice, rfl⟩⟩
  have hcomplete : Complete final := by
    by_contra hincomplete
    obtain ⟨good, hgoodMem, _, hgoodScore⟩ :=
      hgood final hsound hincomplete
    obtain ⟨choice, hchoice⟩ :=
      exists_msmChoice_of_positive_candidate
        candidates score hgoodMem
        (lt_of_lt_of_le (by decide : 0 < 2) hgoodScore)
    exact hterminal ⟨choice, hchoice⟩
  exact ⟨final, hrun, hsound, hcomplete, hterminal⟩

end GenLimit.LearningAlgorithmsLimit
