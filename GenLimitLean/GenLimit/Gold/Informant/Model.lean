import GenLimit.Gold.Text.Model

/-!
# Gold identification from informants

An informant supplies ordered Boolean-labelled data.  Correctness says that
every supplied label agrees with the target language, while completeness says
that every element of the universe is eventually labelled.  Repetitions and
an arbitrary presentation order are allowed.

Unlike positive text, a complete informant eventually distinguishes any two
extensionally different languages.  The final finite-scope stabilization
theorem is the semantic core used by identification by enumeration.
-/

namespace GenLimit
namespace Gold
namespace Informant

open Gold.Text

/-- One labelled observation: an element of the universe and its membership
label. -/
abbrev InformantDatum := ℕ × Bool

/-- An ordered stream of labelled observations. -/
abbrev InformantStream := ℕ → InformantDatum

/-- Every label supplied by `info` is correct for `L`. -/
def InformantCorrect (info : InformantStream) (L : Language) : Prop :=
  ∀ t, (info t).2 = true ↔ (info t).1 ∈ L

/-- Every element of the universe is eventually labelled by `info`. -/
def InformantComplete (info : InformantStream) : Prop :=
  ∀ u, ∃ t, (info t).1 = u

/-- `info` is a complete, correctly labelled presentation of `L`. -/
structure IsInformantFor (info : InformantStream) (L : Language) : Prop where
  correct : InformantCorrect info L
  complete : InformantComplete info

/-- A finite labelled history is compatible with `L` when all its labels
agree with membership in `L`. -/
def InformantCompatible
    (history : List InformantDatum) (L : Language) : Prop :=
  ∀ datum ∈ history, datum.2 = true ↔ datum.1 ∈ L

theorem informantCompatible_textPrefix_iff
    (info : InformantStream) (t : ℕ) (L : Language) :
    InformantCompatible (textPrefix info t) L ↔
      ∀ s, s < t → ((info s).2 = true ↔ (info s).1 ∈ L) := by
  constructor
  · intro h s hs
    exact h (info s) (mem_textPrefix_iff.mpr ⟨s, hs, rfl⟩)
  · intro h datum hdatum
    obtain ⟨s, hs, rfl⟩ := mem_textPrefix_iff.mp hdatum
    exact h s hs

/-- The true target is compatible with every finite prefix of a correct
informant. -/
theorem informantCompatible_target
    {info : InformantStream} {L : Language}
    (hI : IsInformantFor info L) (t : ℕ) :
    InformantCompatible (textPrefix info t) L := by
  rw [informantCompatible_textPrefix_iff]
  intro s _
  exact hI.correct s

/-- Every extensionally wrong language is permanently incompatible after the
informant has displayed one separating element. -/
theorem eventually_not_informantCompatible_of_ne
    {info : InformantStream} {L K : Language}
    (hI : IsInformantFor info L) (hne : K ≠ L) :
    ∃ T, ∀ t, T ≤ t →
      ¬ InformantCompatible (textPrefix info t) K := by
  classical
  have hdiff : ∃ u, ¬ (u ∈ K ↔ u ∈ L) := by
    by_contra h
    push_neg at h
    exact hne (Set.ext h)
  obtain ⟨u, hu⟩ := hdiff
  obtain ⟨s, hs⟩ := hI.complete u
  refine ⟨s + 1, ?_⟩
  intro t ht hcompat
  have hst : s < t :=
    lt_of_lt_of_le (Nat.lt_succ_self s) ht
  have hcandidate :
      (info s).2 = true ↔ (info s).1 ∈ K :=
    (informantCompatible_textPrefix_iff info t K).mp hcompat s hst
  have htarget :
      (info s).2 = true ↔ (info s).1 ∈ L :=
    hI.correct s
  apply hu
  simpa [hs] using hcandidate.symm.trans htarget

/-- For one fixed candidate, finite-prefix compatibility eventually agrees
exactly with extensional equality to the informed target. -/
theorem candidate_eventually_informantCompatible_iff_eq
    {info : InformantStream} {L K : Language}
    (hI : IsInformantFor info L) :
    ∃ T, ∀ t, T ≤ t →
      (InformantCompatible (textPrefix info t) K ↔ K = L) := by
  classical
  by_cases hKL : K = L
  · subst K
    exact ⟨0, fun t _ => ⟨fun _ => rfl,
      fun _ => informantCompatible_target hI t⟩⟩
  · obtain ⟨T, hT⟩ :=
      eventually_not_informantCompatible_of_ne hI hKL
    refine ⟨T, ?_⟩
    intro t ht
    constructor
    · intro hcompat
      exact False.elim ((hT t ht) hcompat)
    · intro heq
      exact False.elim (hKL heq)

/-- Compatibility stabilizes uniformly over every fixed finite prefix of an
indexed family. -/
theorem finite_scope_eventually_informantCompatible_iff_eq
    {C : LanguageFamily} {info : InformantStream} {z : ℕ}
    (hI : IsInformantFor info (C z)) (scope : ℕ) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i < scope →
      (InformantCompatible (textPrefix info t) (C i) ↔ C i = C z) := by
  induction scope with
  | zero =>
      exact ⟨0, by omega⟩
  | succ scope ih =>
      obtain ⟨Ts, hTs⟩ := ih
      obtain ⟨Ti, hTi⟩ :=
        candidate_eventually_informantCompatible_iff_eq
          (info := info) (L := C z) (K := C scope) hI
      refine ⟨max Ts Ti, ?_⟩
      intro t ht i his
      have hTs_t : Ts ≤ t :=
        le_trans (Nat.le_max_left Ts Ti) ht
      have hTi_t : Ti ≤ t :=
        le_trans (Nat.le_max_right Ts Ti) ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp his with his' | rfl
      · exact hTs t hTs_t i his'
      · exact hTi t hTi_t

/-- A learner from informants receives an ordered finite labelled history. -/
abbrev InformantLearner (Name : Type*) :=
  List InformantDatum → Name

/-- Exact-name identification on one informant. -/
def IdentifiesOnInformant {Name : Type*}
    (N : Naming Name) (M : InformantLearner Name)
    (info : InformantStream) (L : Language) : Prop :=
  ∃ n, N.language n = L ∧
    StabilizesTo (fun t => M (textPrefix info t)) n

/-- Identification of every member of an indexed family from every complete,
correct informant, using family indices as names. -/
def IdentifiesFamilyFromInformant
    (C : LanguageFamily) (M : InformantLearner ℕ) : Prop :=
  ∀ z info, IsInformantFor info (C z) →
    IdentifiesOnInformant (familyNaming C) M info (C z)

end Informant
end Gold
end GenLimit
