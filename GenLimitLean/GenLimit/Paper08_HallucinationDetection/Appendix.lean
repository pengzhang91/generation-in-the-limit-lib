import GenLimit.Paper08_HallucinationDetection.AngluinCondition
import GenLimit.Core.ClassGeneration
import Mathlib.Data.Set.Countable

/-!
# Appendix A of the hallucination-detection paper

This module records the appendix's literal consecutive-guess formulation of
identification and its finite-language-aware formulation of generation. It
proves Theorem A.1 and the paper-native prerequisites for Theorem A.2. The
cross-paper proof of A.2 lives in a dedicated bridge module.
-/

namespace GenLimit.HallucinationDetection

open GenLimit.Generic

/-! ## Definition 3: consecutive stable guesses -/

/-- The literal tail condition in Definition 3: after some round, each guess
equals the preceding guess and denotes the target language. -/
def ConsecutivelyIdentifiesFrom
    (M : GenLimit.Angluin.SemanticIdentifier α)
    (C : GenLimit.Generic.LanguageFamily α) (z : ℕ)
    (stream : GenLimit.Generic.Stream α) : Prop :=
  ∃ T, ∀ t, T < t →
    M (GenLimit.textPrefix stream t) =
        M (GenLimit.textPrefix stream (t - 1)) ∧
      C (M (GenLimit.textPrefix stream t)) = C z

/-- Definition 3 for an entire indexed collection. -/
def ConsecutivelyIdentifies
    (M : GenLimit.Angluin.SemanticIdentifier α)
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : GenLimit.Generic.Stream α,
    GenLimit.Generic.Presents stream (C z) →
    ConsecutivelyIdentifiesFrom M C z stream

/-- The collection-level existential in Definition 3. -/
def ConsecutivelyIdentifiable
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ M : GenLimit.Angluin.SemanticIdentifier α,
    ConsecutivelyIdentifies M C

/-- A syntactically stable index gives the literal consecutive-guess
condition printed in Definition 3. -/
theorem semanticallyIdentifies_implies_consecutivelyIdentifies
    {M : GenLimit.Angluin.SemanticIdentifier α}
    {C : GenLimit.Generic.LanguageFamily α}
    (hM : GenLimit.Angluin.SemanticallyIdentifies M C) :
    ConsecutivelyIdentifies M C := by
  intro z stream hP
  obtain ⟨j, hj, T, hT⟩ := hM z stream hP
  refine ⟨T, ?_⟩
  intro t ht
  have htT : T ≤ t := Nat.le_of_lt ht
  have hpredT : T ≤ t - 1 := by omega
  have hnow : M (GenLimit.textPrefix stream t) = j := hT t htT
  have hprevious : M (GenLimit.textPrefix stream (t - 1)) = j :=
    hT (t - 1) hpredT
  constructor
  · exact hnow.trans hprevious.symm
  · rw [hnow, hj]

/-- Conversely, consecutive equality on a tail forces convergence to one
fixed syntactic index. -/
theorem consecutivelyIdentifies_implies_semanticallyIdentifies
    {M : GenLimit.Angluin.SemanticIdentifier α}
    {C : GenLimit.Generic.LanguageFamily α}
    (hM : ConsecutivelyIdentifies M C) :
    GenLimit.Angluin.SemanticallyIdentifies M C := by
  intro z stream hP
  obtain ⟨T, hT⟩ := hM z stream hP
  let j := M (GenLimit.textPrefix stream (T + 1))
  have hj : C j = C z := by
    exact (hT (T + 1) (Nat.lt_succ_self T)).2
  refine ⟨j, hj, T + 1, ?_⟩
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
      have hTsucc : T < t + 1 := by omega
      have hstep := (hT (t + 1) hTsucc).1
      simpa [Nat.succ_sub_one] using hstep.trans ih

/-- Definition 3 is extensionally equivalent to the shared stable-index
interface used by Theorem 2.1. -/
theorem definition_3_equivalence
    (C : GenLimit.Generic.LanguageFamily α) :
    ConsecutivelyIdentifiable C ↔ IdentifiableInLimit C := by
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M, consecutivelyIdentifies_implies_semanticallyIdentifies hM⟩
  · rintro ⟨M, hM⟩
    exact ⟨M, semanticallyIdentifies_implies_consecutivelyIdentifies hM⟩

/-! ## Theorem A.1 -/

/-- Theorem A.1 in the appendix, at the paper's semantic-oracle level.
Empty indexed languages require no positive presentation and have the empty
tell-tale; the nonempty cases use the locking-sequence proof. -/
theorem theorem_A_1
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    ConsecutivelyIdentifiable C ↔ GenLimit.Angluin.ConditionTwo C := by
  rw [definition_3_equivalence]
  exact (theorem_2_1 C).symm.trans (corollary_2_2 C)

/-! ## Definition 5 and Theorem A.2 -/

/-- Definition 5's round-wise requirement.  When the target has been
exhausted, the second disjunct makes the output unrestricted. -/
def AppendixGenerationCorrectAt
    (G : GenLimit.Generic.Generator α)
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Prop :=
  GenLimit.Generic.output G stream t ∈
      L \ (↑(GenLimit.Generic.sample stream t) : Set α) ∨
    L \ (↑(GenLimit.Generic.sample stream t) : Set α) = ∅

/-- A generator succeeds on every presentation of every indexed target in
the sense of Definition 5. -/
def AppendixGeneratesInLimit
    (G : GenLimit.Generic.Generator α)
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∀ z, ∀ stream : GenLimit.Generic.Stream α,
    GenLimit.Generic.Presents stream (C z) →
    ∃ T, ∀ t, T ≤ t →
      AppendixGenerationCorrectAt G (C z) stream t

/-- Collection-level generation in the limit from Definition 5. -/
def AppendixGeneratableInLimit
    (C : GenLimit.Generic.LanguageFamily α) : Prop :=
  ∃ G : GenLimit.Generic.Generator α, AppendixGeneratesInLimit G C

/-- The set of infinite members of an indexed family. -/
def infiniteMembers
    (C : GenLimit.Generic.LanguageFamily α) :
    GenLimit.Generic.LanguageClass α :=
  {L | L ∈ Set.range C ∧ L.Infinite}

theorem infiniteMembers_countable
    (C : GenLimit.Generic.LanguageFamily α) :
    (infiniteMembers C).Countable := by
  apply (Set.countable_range C).mono
  intro L hL
  exact hL.1

theorem infiniteMembers_uus
    (C : GenLimit.Generic.LanguageFamily α) :
    GenLimit.Generic.UUS (infiniteMembers C) := by
  intro L hL
  exact hL.2

end GenLimit.HallucinationDetection
