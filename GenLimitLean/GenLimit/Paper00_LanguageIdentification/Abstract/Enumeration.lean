import GenLimit.Paper00_LanguageIdentification.Abstract.Model

/-!
# #0 Language Identification: Theorem 7.1

This file formalizes all three clauses of Theorem 7.1 in E. Mark Gold,
*Language Identification in the Limit* (1967), pp. 458--459:

1. distinguishability is necessary for ineffective identification;
2. collapsing uncertainty makes identification by enumeration succeed for
   every enumeration;
3. if every object's set of allowable information sequences is countable,
   distinguishability is sufficient for ineffective identification.

The theorem is semantic: the enumerations, chosen names, translations, and
learners need not be computable.
-/

namespace GenLimit
namespace Gold
namespace Abstract

universe uInfo uObject uName

private theorem eventually_forall_lt
    {P : ℕ → ℕ → Prop} {n : ℕ}
    (hP : ∀ i, i < n → ∃ T, ∀ t, T ≤ t → P i t) :
    ∃ T, ∀ t, T ≤ t → ∀ i, i < n → P i t := by
  induction n with
  | zero =>
      exact ⟨0, by simp⟩
  | succ n ih =>
      obtain ⟨T₀, hT₀⟩ := ih (fun i hi => hP i (Nat.lt_succ_of_lt hi))
      obtain ⟨T₁, hT₁⟩ := hP n (Nat.lt_succ_self n)
      refine ⟨max T₀ T₁, ?_⟩
      intro t ht i hi
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hi | rfl
      · exact hT₀ t (le_trans (Nat.le_max_left _ _) ht) i hi
      · exact hT₁ t (le_trans (Nat.le_max_right _ _) ht)

/-- The least compatible enumeration index eventually becomes the first
index naming the target object.  This is the core of the second clause of
Gold's Theorem 7.1. -/
theorem firstCompatibleIndex_stabilizes
    {allowable : Allowable Info Object}
    (hcollapse : CollapsingUncertainty allowable)
    (enumeration : ℕ → Object)
    (henumeration : Function.Surjective enumeration)
    {target : Object} {stream : ℕ → Info}
    (hstream : stream ∈ allowable target) :
    StabilizesTo
      (fun t =>
        firstCompatibleIndex allowable enumeration (textPrefix stream t))
      (firstEnumerationIndex enumeration henumeration target) := by
  classical
  let targetIndex :=
    firstEnumerationIndex enumeration henumeration target
  have htargetIndex : enumeration targetIndex = target := by
    exact firstEnumerationIndex_spec enumeration henumeration target
  have hearlier :
      ∀ i, i < targetIndex → enumeration i ≠ target := by
    intro i hi
    exact firstEnumerationIndex_minimal
      enumeration henumeration target hi
  obtain ⟨T, hT⟩ :=
    eventually_forall_lt (n := targetIndex) (fun i hi =>
      hcollapse hstream (enumeration i) (hearlier i hi))
  refine ⟨T, ?_⟩
  intro t ht
  have htargetCompatible :
      Compatible allowable (textPrefix stream t)
        (enumeration targetIndex) := by
    rw [htargetIndex]
    exact compatible_textPrefix hstream t
  have hexists :
      ∃ i, Compatible allowable (textPrefix stream t)
        (enumeration i) :=
    ⟨targetIndex, htargetCompatible⟩
  simp only [firstCompatibleIndex, dif_pos hexists]
  apply Nat.le_antisymm
  · exact Nat.find_min' hexists htargetCompatible
  · by_contra hnot
    have hlt : Nat.find hexists < targetIndex :=
      Nat.lt_of_not_ge hnot
    exact (hT t ht (Nat.find hexists) hlt) (Nat.find_spec hexists)

/-- Identification in the limit implies Gold's distinguishability
condition. -/
theorem distinguishable_of_identifies
    {naming : Naming Name Object}
    {allowable : Allowable Info Object}
    {learner : Learner Info Name}
    (hlearner : Identifies naming allowable learner) :
    Distinguishable allowable := by
  intro object₁ object₂ stream hstream₁ hstream₂
  obtain ⟨name₁, hname₁, T₁, hT₁⟩ :=
    hlearner object₁ stream hstream₁
  obtain ⟨name₂, hname₂, T₂, hT₂⟩ :=
    hlearner object₂ stream hstream₂
  have hnames : name₁ = name₂ := by
    have h₁ := hT₁ (max T₁ T₂) (Nat.le_max_left _ _)
    have h₂ := hT₂ (max T₁ T₂) (Nat.le_max_right _ _)
    exact h₁.symm.trans h₂
  rw [← hname₁, ← hname₂, hnames]

/-- First clause of Gold's Theorem 7.1: distinguishability is necessary for
ineffective identifiability in the limit. -/
theorem distinguishable_of_identifiable
    {naming : Naming Name Object}
    {allowable : Allowable Info Object}
    (hidentifiable : Identifiable naming allowable) :
    Distinguishable allowable := by
  obtain ⟨learner, hlearner⟩ := hidentifiable
  exact distinguishable_of_identifies hlearner

/-- Second clause of Gold's Theorem 7.1: under collapsing uncertainty,
identification by enumeration succeeds for every enumeration of the object
class, including enumerations with repetitions. -/
theorem identificationByEnumeration_identifies
    (naming : Naming Name Object)
    {allowable : Allowable Info Object}
    (hcollapse : CollapsingUncertainty allowable)
    (enumeration : ℕ → Object)
    (henumeration : Function.Surjective enumeration) :
    Identifies naming allowable
      (identificationByEnumeration naming allowable enumeration) := by
  classical
  intro target stream hstream
  refine ⟨naming.nameOf target, naming.denotes_nameOf target, ?_⟩
  obtain ⟨T, hT⟩ :=
    firstCompatibleIndex_stabilizes
      hcollapse enumeration henumeration hstream
  refine ⟨T, ?_⟩
  intro t ht
  simp only [identificationByEnumeration]
  have hindex := hT t ht
  change
    firstCompatibleIndex allowable enumeration (textPrefix stream t) =
      firstEnumerationIndex enumeration henumeration target at hindex
  rw [hindex, firstEnumerationIndex_spec enumeration henumeration target]

/-- Collapsing uncertainty is sufficient for ineffective identification
whenever an enumeration of the object class is supplied. -/
theorem collapsingUncertainty_implies_identifiable
    (naming : Naming Name Object)
    {allowable : Allowable Info Object}
    (hcollapse : CollapsingUncertainty allowable)
    (enumeration : ℕ → Object)
    (henumeration : Function.Surjective enumeration) :
    Identifiable naming allowable :=
  ⟨identificationByEnumeration naming allowable enumeration,
    identificationByEnumeration_identifies
      naming hcollapse enumeration henumeration⟩

/-- A countable object class with countably many allowable sequences per
object has only countably many allowable sequences in total. -/
theorem allowableSequences_countable
    [Countable Object]
    {allowable : Allowable Info Object}
    (hcountable : ∀ object, (allowable object).Countable) :
    (allowableSequences allowable).Countable := by
  rw [allowableSequences_eq_iUnion]
  exact Set.countable_iUnion hcountable

private theorem pointwise_eq_of_textPrefix_eq
    {stream₁ stream₂ : ℕ → Info} {t : ℕ}
    (h : textPrefix stream₁ t = textPrefix stream₂ t)
    {i : ℕ} (hi : i < t) :
    stream₁ i = stream₂ i := by
  have hget := congrArg (fun history => history[i]?) h
  simpa [textPrefix, hi] using hget

private theorem singletonSequence_collapsingUncertainty
    (validSequences : Set (ℕ → Info)) :
    CollapsingUncertainty
      (fun stream : validSequences =>
        ({(stream : ℕ → Info)} :
          Set (ℕ → Info))) := by
  intro target observed hobserved object hne
  have hobserved_eq : observed = (target : ℕ → Info) := by
    simpa using hobserved
  have hfunctions :
      (object : ℕ → Info) ≠ (target : ℕ → Info) := by
    intro h
    exact hne (Subtype.ext h)
  have hnotforall :
      ¬ ∀ i, (object : ℕ → Info) i = (target : ℕ → Info) i := by
    intro h
    exact hfunctions (funext h)
  push_neg at hnotforall
  obtain ⟨i, hi⟩ := hnotforall
  refine ⟨i + 1, ?_⟩
  intro t ht hcompatible
  obtain ⟨candidate, hcandidatesingleton, hprefix⟩ := hcompatible
  have hcandidate_eq : candidate = (object : ℕ → Info) := by
    simpa using hcandidatesingleton
  subst candidate
  rw [hobserved_eq] at hprefix
  have hprefix' :
      textPrefix (object : ℕ → Info) t =
        textPrefix (target : ℕ → Info) t := by
    simpa using hprefix
  have heq :=
    pointwise_eq_of_textPrefix_eq hprefix'
      (lt_of_lt_of_le (Nat.lt_succ_self i) ht)
  exact hi heq

/-- Third clause of Gold's Theorem 7.1: for countable information and object
types, if each object has only countably many allowable information
sequences, distinguishability is sufficient for ineffective identification
in the limit. -/
theorem distinguishable_implies_identifiable_of_countable
    [Countable Info] [Countable Object] [Nonempty Object]
    (naming : Naming Name Object)
    {allowable : Allowable Info Object}
    (hcountable : ∀ object, (allowable object).Countable)
    (hdistinguishable : Distinguishable allowable) :
    Identifiable naming allowable := by
  classical
  let allSequences := allowableSequences allowable
  have hallCountable : allSequences.Countable :=
    allowableSequences_countable hcountable
  by_cases hallNonempty : allSequences.Nonempty
  · let ValidSequence := ↥allSequences
    haveI : Countable ValidSequence := hallCountable.to_subtype
    haveI : Nonempty ValidSequence := hallNonempty.to_subtype
    obtain ⟨enumeration, henumeration⟩ :=
      exists_surjective_nat ValidSequence
    let owner : ValidSequence → Object := fun stream =>
      Classical.choose stream.property
    have owner_spec (stream : ValidSequence) :
        (stream : ℕ → Info) ∈ allowable (owner stream) :=
      Classical.choose_spec stream.property
    have owner_unique
        {stream : ValidSequence} {object : Object}
        (hstream :
          (stream : ℕ → Info) ∈ allowable object) :
        owner stream = object :=
      hdistinguishable (owner_spec stream) hstream
    let sequenceAllowable : Allowable Info ValidSequence :=
      fun stream =>
        ({(stream : ℕ → Info)} :
          Set (ℕ → Info))
    have hsequenceCollapse :
        CollapsingUncertainty sequenceAllowable := by
      exact singletonSequence_collapsingUncertainty allSequences
    let learner : Learner Info Name := fun history =>
      naming.nameOf
        (owner
          (enumeration
            (firstCompatibleIndex
              sequenceAllowable enumeration history)))
    refine ⟨learner, ?_⟩
    intro target stream hstream
    let validStream : ValidSequence :=
      ⟨stream, ⟨target, hstream⟩⟩
    have hvalidOwner : owner validStream = target :=
      owner_unique hstream
    obtain ⟨T, hT⟩ :=
      firstCompatibleIndex_stabilizes
        hsequenceCollapse enumeration henumeration
        (target := validStream)
        (stream := stream)
        (by simp [sequenceAllowable, validStream])
    refine ⟨naming.nameOf target, naming.denotes_nameOf target, T, ?_⟩
    intro t ht
    simp only [learner]
    have hindex := hT t ht
    change
      firstCompatibleIndex sequenceAllowable enumeration
          (textPrefix stream t) =
        firstEnumerationIndex enumeration henumeration validStream at hindex
    rw [hindex,
      firstEnumerationIndex_spec enumeration henumeration validStream,
      hvalidOwner]
  · have hnone :
        ∀ object stream, stream ∉ allowable object := by
      intro object stream hstream
      exact hallNonempty ⟨stream, ⟨object, hstream⟩⟩
    let fallback : Name :=
      naming.nameOf (Classical.choice (inferInstance : Nonempty Object))
    refine ⟨fun _ => fallback, ?_⟩
    intro object stream hstream
    exact False.elim (hnone object stream hstream)

/-- Exact bundled form of Gold's Theorem 7.1.

The middle conjunct says that *every* surjective enumeration yields a
successful identification-by-enumeration learner. -/
theorem gold_theorem_7_1
    [Countable Info] [Countable Object] [Nonempty Object]
    (naming : Naming Name Object)
    (allowable : Allowable Info Object)
    (hcountable : ∀ object, (allowable object).Countable) :
    (Identifiable naming allowable → Distinguishable allowable) ∧
    (CollapsingUncertainty allowable →
      ∀ enumeration : ℕ → Object,
        Function.Surjective enumeration →
        Identifies naming allowable
          (identificationByEnumeration
            naming allowable enumeration)) ∧
    (Distinguishable allowable → Identifiable naming allowable) := by
  exact ⟨distinguishable_of_identifiable,
    fun hcollapse enumeration henumeration =>
      identificationByEnumeration_identifies
        naming hcollapse enumeration henumeration,
    distinguishable_implies_identifiable_of_countable
      naming hcountable⟩

end Abstract
end Gold
end GenLimit
