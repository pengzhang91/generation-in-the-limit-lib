import GenLimit.Paper30_TimeSensitiveLanguageGeneration.GCGCommon
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.GreedyAsymptotics
import GenLimit.Support.TurnTaking.Announcements

/-!
# Stable greedy stages in GCG

This file proves the rank-aware predecessor pairing used when one stage of
Algorithm 2 remains on a fixed canonically ordered language.  It reuses the
shared first-announcement partition, but counts prefixes in the language's
canonical order rather than in the ambient natural-number order.

The key conclusion is finite: after a fixed burn-in, every adversary-first
target value outside a finite exceptional prefix is paired injectively with
an earlier, timely generator-first value.  A later module converts this
pairing into the cardinal bound which forces a GCG stage to terminate.
-/

namespace GenLimit.TimeSensitive

open GenLimit
open GenLimit.KleinbergWei

/-- First time at which the adversary announces `x`.  The fallback branch is
never used once membership in the adversary range has been established. -/
noncomputable def firstAdversaryTime
    (adversary : ℕ → ℕ) (x : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, adversary t = x then Nat.find h else 0

theorem firstAdversaryTime_spec
    {adversary : ℕ → ℕ} {x : ℕ} (hx : x ∈ Set.range adversary) :
    adversary (firstAdversaryTime adversary x) = x := by
  classical
  simp only [firstAdversaryTime]
  split
  · exact Nat.find_spec ‹∃ t, adversary t = x›
  · exact False.elim (‹¬ ∃ t, adversary t = x› hx)

theorem firstAdversaryTime_min
    {adversary : ℕ → ℕ} {x t : ℕ} (hx : x ∈ Set.range adversary)
    (ht : adversary t = x) :
    firstAdversaryTime adversary x ≤ t := by
  classical
  simp only [firstAdversaryTime]
  split
  · exact Nat.find_min' ‹∃ q, adversary q = x› ht
  · exact False.elim (‹¬ ∃ q, adversary q = x› hx)

theorem firstAdversaryTime_not_mem_sample
    {adversary : ℕ → ℕ} {x : ℕ} (hx : x ∈ Set.range adversary) :
    x ∉ sample adversary (firstAdversaryTime adversary x) := by
  intro hmem
  rw [mem_sample_iff] at hmem
  obtain ⟨s, hs, hseq⟩ := hmem
  exact (Nat.not_lt_of_ge (firstAdversaryTime_min hx hseq)) hs

/-- From round `T` onward, the generator literally performs the
`OnTimeUnused` operation for one fixed ordered language. -/
def GreedyFrom
    (O : OrderedLanguage) (adversary generator : ℕ → ℕ) (T : ℕ) : Prop :=
  ∀ t, T ≤ t →
    generator t =
      onTimeUnused O
        (sample adversary (t + 1) ∪ sequencePrefix generator t) t

theorem greedyFrom_mem
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ} {T t : ℕ}
    (hgreedy : GreedyFrom O adversary generator T) (ht : T ≤ t) :
    generator t ∈ O.carrier := by
  rw [hgreedy t ht]
  exact onTimeUnused_mem _ _ _

theorem greedyFrom_rank_onTime
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ} {T t : ℕ}
    (hgreedy : GreedyFrom O adversary generator T) (ht : T ≤ t) :
    ∃ r, generator t = O.enumeration r ∧ t < r := by
  refine ⟨onTimeUnusedRank O
      (sample adversary (t + 1) ∪ sequencePrefix generator t) t, ?_,
    onTimeUnused_onTime _ _ _⟩
  rw [hgreedy t ht]
  rfl

/-- If a canonical-rank `j` value belongs to the adversary and was not
generated first, a stable greedy stage starting before `j` forces its first
adversary occurrence to happen by time `j`. -/
theorem firstAdversaryTime_le_rank
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ} {T j : ℕ}
    (hgreedy : GreedyFrom O adversary generator T)
    (hjT : T < j)
    (hadv : O.enumeration j ∈ AdversaryFirst adversary generator) :
    firstAdversaryTime adversary (O.enumeration j) ≤ j := by
  let x := O.enumeration j
  have hxRange : x ∈ Set.range adversary := by
    obtain ⟨q, hq, -⟩ := hadv
    exact ⟨q, hq⟩
  by_contra hnot
  have hjfirst : j < firstAdversaryTime adversary x :=
    Nat.lt_of_not_ge hnot
  have hjpos : 0 < j := lt_of_le_of_lt (Nat.zero_le T) hjT
  let used :=
    sample adversary ((j - 1) + 1) ∪ sequencePrefix generator (j - 1)
  have hxNotObserved : x ∉ sample adversary ((j - 1) + 1) := by
    have hnotSample := firstAdversaryTime_not_mem_sample hxRange
    intro hx
    apply hnotSample
    rw [mem_sample_iff] at hx ⊢
    obtain ⟨s, hs, hsx⟩ := hx
    exact ⟨s, lt_of_lt_of_le hs (by omega), hsx⟩
  have hxNotGenerated : x ∉ sequencePrefix generator (j - 1) := by
    intro hx
    obtain ⟨s, hs, hsx⟩ :=
      (mem_sequencePrefix_iff generator x (j - 1)).mp hx
    obtain ⟨q, hqx, hnoGenerator⟩ := hadv
    have hfirstq : firstAdversaryTime adversary x ≤ q :=
      firstAdversaryTime_min hxRange hqx
    exact hnoGenerator s (lt_trans hs (by omega)) hsx
  have hjEligible : OnTimeUnusedRank O used (j - 1) j := by
    refine ⟨by omega, ?_⟩
    exact Finset.notMem_union.mpr ⟨hxNotObserved, hxNotGenerated⟩
  have hleast : onTimeUnusedRank O used (j - 1) = j := by
    apply le_antisymm
    · exact onTimeUnusedRank_min O used (j - 1) hjEligible
    · have := onTimeUnused_onTime O used (j - 1)
      omega
  have houtput : generator (j - 1) = x := by
    rw [hgreedy (j - 1) (by omega)]
    change O.enumeration (onTimeUnusedRank O used (j - 1)) = x
    rw [hleast]
  obtain ⟨q, hqx, hnoGenerator⟩ := hadv
  have hfirstq : firstAdversaryTime adversary x ≤ q :=
    firstAdversaryTime_min hxRange hqx
  exact hnoGenerator (j - 1) (by omega) houtput

/-- Pair an adversary-first value with the generator output immediately
before its first adversary occurrence. -/
noncomputable def greedyPartner
    (adversary generator : ℕ → ℕ) (x : ℕ) : ℕ :=
  generator (firstAdversaryTime adversary x - 1)

/-- An output produced before canonical rank `k` is timely for the identity
deadline at that rank. -/
theorem mem_timelyElements_of_output_before_rank
    (O : OrderedLanguage) (generator : ℕ → ℕ)
    {q k i : ℕ} (hki : k < i) (hqk : q < k)
    (hout : generator q = O.enumeration k) :
    O.enumeration k ∈ timelyElements generator O.enumeration id i := by
  classical
  simp only [timelyElements, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range]
  refine ⟨k, ⟨hki, ?_⟩, rfl⟩
  rw [mem_sequencePrefix_iff]
  exact ⟨q, by simpa using hqk, hout⟩

/-- The predecessor partner of a late adversary-first value has a strictly
smaller canonical rank and is timely in every later target prefix. -/
theorem greedyPartner_mem_timely
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T i j : ℕ}
    (hgreedy : GreedyFrom O adversary generator T)
    (hTj : T < j)
    (hTfirst : T < firstAdversaryTime adversary (O.enumeration j))
    (hji : j < i)
    (hadv : O.enumeration j ∈ AdversaryFirst adversary generator) :
    greedyPartner adversary generator (O.enumeration j) ∈
      timelyElements generator O.enumeration id i := by
  let x := O.enumeration j
  let q := firstAdversaryTime adversary x
  have hTq : T < q := by
    simpa [q, x] using hTfirst
  have hxRange : x ∈ Set.range adversary := by
    obtain ⟨w, hw, -⟩ := hadv
    exact ⟨w, hw⟩
  have hqj : q ≤ j := by
    exact firstAdversaryTime_le_rank hgreedy hTj hadv
  have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le T) hTfirst
  let used := sample adversary ((q - 1) + 1) ∪
    sequencePrefix generator (q - 1)
  have hxNotObserved : x ∉ sample adversary ((q - 1) + 1) := by
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt hqpos))] using
        (firstAdversaryTime_not_mem_sample hxRange)
  have hxNotGenerated : x ∉ sequencePrefix generator (q - 1) := by
    intro hx
    obtain ⟨s, hs, hsx⟩ :=
      (mem_sequencePrefix_iff generator x (q - 1)).mp hx
    obtain ⟨w, hwx, hnoGenerator⟩ := hadv
    have hqw : q ≤ w := firstAdversaryTime_min hxRange hwx
    exact hnoGenerator s (lt_trans hs (by omega)) hsx
  have hjEligible : OnTimeUnusedRank O used (q - 1) j := by
    refine ⟨by omega, ?_⟩
    exact Finset.notMem_union.mpr ⟨hxNotObserved, hxNotGenerated⟩
  let k := onTimeUnusedRank O used (q - 1)
  have hkj : k ≤ j := onTimeUnusedRank_min O used (q - 1) hjEligible
  have hqk : q - 1 < k := onTimeUnused_onTime O used (q - 1)
  have hout : generator (q - 1) = O.enumeration k := by
    rw [hgreedy (q - 1) (by omega : T ≤ q - 1)]
    change onTimeUnused O used (q - 1) = O.enumeration k
    rfl
  have hkne : k ≠ j := by
    intro hkjEq
    obtain ⟨w, hwx, hnoGenerator⟩ := hadv
    have hqw : q ≤ w := firstAdversaryTime_min hxRange hwx
    apply hnoGenerator (q - 1) (by omega)
    rw [hout, hkjEq]
  have hkjStrict : k < j := lt_of_le_of_ne hkj hkne
  change generator (q - 1) ∈ timelyElements generator O.enumeration id i
  rw [hout]
  exact mem_timelyElements_of_output_before_rank O generator
    (lt_trans hkjStrict hji) hqk hout

/-- Predecessor pairing is injective on values whose first adversary time is
strictly after `T`; positivity removes the predecessor boundary ambiguity. -/
theorem greedyPartner_injOn
    {adversary generator : ℕ → ℕ} {T : ℕ}
    (hplay : FreshPlay adversary generator) :
    Set.InjOn (greedyPartner adversary generator)
      {x | x ∈ Set.range adversary ∧
        T < firstAdversaryTime adversary x} := by
  intro x hx y hy hxy
  have hqxpos : 0 < firstAdversaryTime adversary x :=
    lt_of_le_of_lt (Nat.zero_le T) hx.2
  have hqypos : 0 < firstAdversaryTime adversary y :=
    lt_of_le_of_lt (Nat.zero_le T) hy.2
  have hpred :
      firstAdversaryTime adversary x - 1 =
        firstAdversaryTime adversary y - 1 := by
    apply hplay.generator_injective
    exact hxy
  have htime :
      firstAdversaryTime adversary x =
        firstAdversaryTime adversary y := by
    omega
  calc
    x = adversary (firstAdversaryTime adversary x) :=
      (firstAdversaryTime_spec hx.1).symm
    _ = adversary (firstAdversaryTime adversary y) := by rw [htime]
    _ = y := firstAdversaryTime_spec hy.1

/-! ## Finite rank-prefix accounting -/

theorem targetPrefix_card_ordered (O : OrderedLanguage) (i : ℕ) :
    (targetPrefix O.enumeration i).card = i := by
  letI : DecidableEq ℕ := Classical.decEq ℕ
  rw [targetPrefix, sequencePrefix]
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a _ b _ hab
    exact O.enumeration_injective hab

theorem sequencePrefix_card_le (S : ℕ → ℕ) (i : ℕ) :
    (sequencePrefix S i).card ≤ i := by
  letI : DecidableEq ℕ := Classical.decEq ℕ
  rw [sequencePrefix]
  simpa only [Finset.card_range] using
    (Finset.card_image_le (s := Finset.range i) (f := S))

theorem sample_card_le (S : ℕ → ℕ) (i : ℕ) :
    (sample S i).card ≤ i := by
  unfold sample
  simpa only [Finset.card_range] using
    (Finset.card_image_le (s := Finset.range i) (f := S))

noncomputable def adversaryFirstPrefix
    (O : OrderedLanguage) (adversary generator : ℕ → ℕ)
    (i : ℕ) : Finset ℕ := by
  classical
  exact (targetPrefix O.enumeration i).filter fun x =>
    x ∈ AdversaryFirst adversary generator

noncomputable def generatorFirstPrefix
    (O : OrderedLanguage) (adversary generator : ℕ → ℕ)
    (i : ℕ) : Finset ℕ := by
  classical
  exact (targetPrefix O.enumeration i).filter fun x =>
    x ∈ GeneratorFirst adversary generator

@[simp] theorem mem_adversaryFirstPrefix
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ} {i x : ℕ} :
    x ∈ adversaryFirstPrefix O adversary generator i ↔
      x ∈ targetPrefix O.enumeration i ∧
        x ∈ AdversaryFirst adversary generator := by
  classical
  simp [adversaryFirstPrefix]

@[simp] theorem mem_generatorFirstPrefix
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ} {i x : ℕ} :
    x ∈ generatorFirstPrefix O adversary generator i ↔
      x ∈ targetPrefix O.enumeration i ∧
        x ∈ GeneratorFirst adversary generator := by
  classical
  simp [generatorFirstPrefix]

/-- Adversary-first values in the first `i` canonical ranks that are outside
both burn-in exception sets. -/
noncomputable def lateAdversaryPrefix
    (O : OrderedLanguage) (adversary generator : ℕ → ℕ)
    (T i : ℕ) : Finset ℕ := by
  classical
  exact (targetPrefix O.enumeration i).filter fun x =>
    x ∈ AdversaryFirst adversary generator ∧
      x ∉ targetPrefix O.enumeration (T + 1) ∧
      x ∉ sample adversary (T + 1)

/-- Generator-first values in the first `i` canonical ranks that were not
already emitted during burn-in. -/
noncomputable def lateGeneratorPrefix
    (O : OrderedLanguage) (adversary generator : ℕ → ℕ)
    (T i : ℕ) : Finset ℕ := by
  classical
  exact (targetPrefix O.enumeration i).filter fun x =>
    x ∈ GeneratorFirst adversary generator ∧
      x ∉ sequencePrefix generator T

@[simp] theorem mem_lateAdversaryPrefix
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T i x : ℕ} :
    x ∈ lateAdversaryPrefix O adversary generator T i ↔
      x ∈ targetPrefix O.enumeration i ∧
        x ∈ AdversaryFirst adversary generator ∧
        x ∉ targetPrefix O.enumeration (T + 1) ∧
        x ∉ sample adversary (T + 1) := by
  classical
  simp [lateAdversaryPrefix]

@[simp] theorem mem_lateGeneratorPrefix
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T i x : ℕ} :
    x ∈ lateGeneratorPrefix O adversary generator T i ↔
      x ∈ targetPrefix O.enumeration i ∧
        x ∈ GeneratorFirst adversary generator ∧
        x ∉ sequencePrefix generator T := by
  classical
  simp [lateGeneratorPrefix]

theorem lateAdversaryPrefix_card_le_timely
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T i : ℕ}
    (hplay : FreshPlay adversary generator)
    (hgreedy : GreedyFrom O adversary generator T) :
    (lateAdversaryPrefix O adversary generator T i).card ≤
      (timelyElements generator O.enumeration id i).card := by
  classical
  apply Finset.card_le_card_of_injOn (greedyPartner adversary generator)
  · intro x hx
    have hxFin : x ∈ lateAdversaryPrefix O adversary generator T i := hx
    rw [mem_lateAdversaryPrefix] at hxFin
    replace hx := hxFin
    obtain ⟨hxPrefix, hxAdv, hxNotRanks, hxNotSample⟩ := hx
    obtain ⟨j, hji, hjx⟩ :=
      (mem_sequencePrefix_iff O.enumeration x i).mp hxPrefix
    have hTj : T < j := by
      by_contra hnot
      apply hxNotRanks
      exact (mem_sequencePrefix_iff O.enumeration x (T + 1)).mpr
        ⟨j, by omega, hjx⟩
    have hxRange : x ∈ Set.range adversary := by
      obtain ⟨q, hqx, -⟩ := hxAdv
      exact ⟨q, hqx⟩
    have hTfirst : T < firstAdversaryTime adversary x := by
      by_contra hnot
      apply hxNotSample
      rw [mem_sample_iff]
      exact ⟨firstAdversaryTime adversary x, by omega,
        firstAdversaryTime_spec hxRange⟩
    subst x
    exact greedyPartner_mem_timely hgreedy hTj hTfirst hji hxAdv
  · intro x hx y hy hxy
    have hxFin : x ∈ lateAdversaryPrefix O adversary generator T i := hx
    have hyFin : y ∈ lateAdversaryPrefix O adversary generator T i := hy
    rw [mem_lateAdversaryPrefix] at hxFin hyFin
    replace hx := hxFin
    replace hy := hyFin
    have hxRange : x ∈ Set.range adversary := by
      obtain ⟨q, hqx, -⟩ := hx.2.1
      exact ⟨q, hqx⟩
    have hyRange : y ∈ Set.range adversary := by
      obtain ⟨q, hqy, -⟩ := hy.2.1
      exact ⟨q, hqy⟩
    have hxLate : T < firstAdversaryTime adversary x := by
      by_contra hnot
      exact hx.2.2.2 ((mem_sample_iff).mpr
        ⟨firstAdversaryTime adversary x, by omega,
          firstAdversaryTime_spec hxRange⟩)
    have hyLate : T < firstAdversaryTime adversary y := by
      by_contra hnot
      exact hy.2.2.2 ((mem_sample_iff).mpr
        ⟨firstAdversaryTime adversary y, by omega,
          firstAdversaryTime_spec hyRange⟩)
    exact greedyPartner_injOn hplay ⟨hxRange, hxLate⟩
      ⟨hyRange, hyLate⟩ hxy

theorem lateGeneratorPrefix_subset_timely
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T i : ℕ}
    (hgreedy : GreedyFrom O adversary generator T) :
    lateGeneratorPrefix O adversary generator T i ⊆
      timelyElements generator O.enumeration id i := by
  classical
  intro x hx
  rw [mem_lateGeneratorPrefix] at hx
  obtain ⟨hxPrefix, hxGen, hxNotEarly⟩ := hx
  obtain ⟨j, hji, hjx⟩ :=
    (mem_sequencePrefix_iff O.enumeration x i).mp hxPrefix
  obtain ⟨t, htx, -⟩ := hxGen
  have hTt : T ≤ t := by
    by_contra hnot
    apply hxNotEarly
    exact (mem_sequencePrefix_iff generator x T).mpr
      ⟨t, Nat.lt_of_not_ge hnot, htx⟩
  obtain ⟨k, hgenk, htk⟩ := greedyFrom_rank_onTime hgreedy hTt
  have hkj : k = j := by
    apply O.enumeration_injective
    rw [← hgenk, htx, hjx]
  subst k
  rw [← hjx]
  exact mem_timelyElements_of_output_before_rank O generator hji htk
    (htx.trans hjx.symm)

/-- After burn-in, every canonical value is first announced by one of the two
players even when the adversary does not enumerate the active language.  If
the adversary never announces the value, the literal greedy rule takes it no
later than its canonical rank. -/
theorem canonical_value_first_announced
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T j : ℕ}
    (hgreedy : GreedyFrom O adversary generator T)
    (hTj : T < j) :
    O.enumeration j ∈ AdversaryFirst adversary generator ∪
      GeneratorFirst adversary generator := by
  let x := O.enumeration j
  by_cases hxRange : x ∈ Set.range adversary
  · exact range_subset_first_announcements adversary generator hxRange
  · apply Set.mem_union_right
    by_cases hbefore : ∃ s, s < j ∧ generator s = x
    · obtain ⟨s, hsj, hsx⟩ := hbefore
      refine ⟨s, hsx, ?_⟩
      intro q hqs hqx
      exact hxRange ⟨q, hqx⟩
    · have hjpos : 0 < j := lt_of_le_of_lt (Nat.zero_le T) hTj
      let used := sample adversary ((j - 1) + 1) ∪
        sequencePrefix generator (j - 1)
      have hxNotObserved : x ∉ sample adversary ((j - 1) + 1) := by
        intro hx
        rw [mem_sample_iff] at hx
        obtain ⟨q, -, hqx⟩ := hx
        exact hxRange ⟨q, hqx⟩
      have hxNotGenerated : x ∉ sequencePrefix generator (j - 1) := by
        intro hx
        obtain ⟨s, hs, hsx⟩ :=
          (mem_sequencePrefix_iff generator x (j - 1)).mp hx
        exact hbefore ⟨s, lt_trans hs (by omega), hsx⟩
      have hjEligible : OnTimeUnusedRank O used (j - 1) j := by
        exact ⟨by omega,
          Finset.notMem_union.mpr ⟨hxNotObserved, hxNotGenerated⟩⟩
      have hleast : onTimeUnusedRank O used (j - 1) = j := by
        apply le_antisymm
        · exact onTimeUnusedRank_min O used (j - 1) hjEligible
        · have := onTimeUnused_onTime O used (j - 1)
          omega
      have hout : generator (j - 1) = x := by
        rw [hgreedy (j - 1) (by omega)]
        change O.enumeration (onTimeUnusedRank O used (j - 1)) = x
        rw [hleast]
      refine ⟨j - 1, hout, ?_⟩
      intro q hq hqx
      exact hxRange ⟨q, hqx⟩

/-- Restricting the preceding coverage to a finite canonical prefix leaves
only the first `T + 1` ranks as an explicit exception set. -/
theorem targetPrefix_card_le_announcement_cards_add_burnIn
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T : ℕ} (hgreedy : GreedyFrom O adversary generator T) (i : ℕ) :
    i ≤
      (adversaryFirstPrefix O adversary generator i).card +
      (generatorFirstPrefix O adversary generator i).card + (T + 1) := by
  classical
  let A := adversaryFirstPrefix O adversary generator i
  let G := generatorFirstPrefix O adversary generator i
  have hcover : targetPrefix O.enumeration i ⊆
      (A ∪ G) ∪ targetPrefix O.enumeration (T + 1) := by
    intro x hx
    obtain ⟨j, hji, hjx⟩ :=
      (mem_sequencePrefix_iff O.enumeration x i).mp hx
    by_cases hTj : T < j
    · rcases canonical_value_first_announced hgreedy hTj with hxA | hxG
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (mem_adversaryFirstPrefix.mpr ⟨hx, by simpa [hjx] using hxA⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (mem_generatorFirstPrefix.mpr ⟨hx, by simpa [hjx] using hxG⟩))
    · exact Finset.mem_union_right _
        ((mem_sequencePrefix_iff O.enumeration x (T + 1)).mpr
          ⟨j, by omega, hjx⟩)
  calc
    i = (targetPrefix O.enumeration i).card :=
      (targetPrefix_card_ordered O i).symm
    _ ≤ ((A ∪ G) ∪ targetPrefix O.enumeration (T + 1)).card :=
      Finset.card_le_card hcover
    _ ≤ (A.card + G.card) +
        (targetPrefix O.enumeration (T + 1)).card :=
      (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ = (adversaryFirstPrefix O adversary generator i).card +
        (generatorFirstPrefix O adversary generator i).card + (T + 1) := by
      rw [targetPrefix_card_ordered]

/-- Exact finite bound for a stable greedy stage.  The explicit `4T + 3`
term accounts for the partition boundary, early canonical ranks, early
adversary announcements, and early generator outputs. -/
theorem stableGreedy_card_bound
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T i : ℕ}
    (hplay : FreshPlay adversary generator)
    (hgreedy : GreedyFrom O adversary generator T) :
    i ≤ 2 * (timelyElements generator O.enumeration id i).card +
      (4 * T + 3) := by
  classical
  let A := adversaryFirstPrefix O adversary generator i
  let G := generatorFirstPrefix O adversary generator i
  let LA := lateAdversaryPrefix O adversary generator T i
  let LG := lateGeneratorPrefix O adversary generator T i
  have hAcover : A ⊆
      (LA ∪ targetPrefix O.enumeration (T + 1)) ∪ sample adversary (T + 1) := by
    intro x hx
    have hx' : x ∈ targetPrefix O.enumeration i ∧
        x ∈ AdversaryFirst adversary generator :=
      mem_adversaryFirstPrefix.mp (show x ∈ A from hx)
    by_cases hrank : x ∈ targetPrefix O.enumeration (T + 1)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hrank)
    by_cases hsample : x ∈ sample adversary (T + 1)
    · exact Finset.mem_union_right _ hsample
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hx'.1, hx'.2, hrank, hsample⟩
  have hGcover : G ⊆ LG ∪ sequencePrefix generator T := by
    intro x hx
    have hx' : x ∈ targetPrefix O.enumeration i ∧
        x ∈ GeneratorFirst adversary generator :=
      mem_generatorFirstPrefix.mp (show x ∈ G from hx)
    by_cases hearly : x ∈ sequencePrefix generator T
    · exact Finset.mem_union_right _ hearly
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hx'.1, hx'.2, hearly⟩)
  have hAcard : A.card ≤
      (timelyElements generator O.enumeration id i).card + 2 * (T + 1) := by
    calc
      A.card ≤ ((LA ∪ targetPrefix O.enumeration (T + 1)) ∪
          sample adversary (T + 1)).card := Finset.card_le_card hAcover
      _ ≤ LA.card + (targetPrefix O.enumeration (T + 1)).card +
          (sample adversary (T + 1)).card := by
        exact (Finset.card_union_le _ _).trans
          (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      _ ≤ (timelyElements generator O.enumeration id i).card +
          (T + 1) + (T + 1) := by
        exact Nat.add_le_add
          (Nat.add_le_add
            (lateAdversaryPrefix_card_le_timely hplay hgreedy)
            (Nat.le_of_eq (targetPrefix_card_ordered O (T + 1))))
          (sample_card_le adversary (T + 1))
      _ = (timelyElements generator O.enumeration id i).card +
          2 * (T + 1) := by omega
  have hGcard : G.card ≤
      (timelyElements generator O.enumeration id i).card + T := by
    calc
      G.card ≤ (LG ∪ sequencePrefix generator T).card :=
        Finset.card_le_card hGcover
      _ ≤ LG.card + (sequencePrefix generator T).card :=
        Finset.card_union_le _ _
      _ ≤ (timelyElements generator O.enumeration id i).card + T := by
        exact Nat.add_le_add
          (Finset.card_le_card (lateGeneratorPrefix_subset_timely hgreedy))
          (sequencePrefix_card_le generator T)
  have hpartition : i ≤ A.card + G.card + (T + 1) := by
    simpa [A, G] using
      targetPrefix_card_le_announcement_cards_add_burnIn hgreedy i
  change i ≤ 2 * (timelyElements generator O.enumeration id i).card +
    (4 * T + 3)
  omega

/-- A stable literal greedy stage eventually crosses every GCG threshold.
This is the rank-aware, machine-ready form of Appendix E's finite ownership
argument. -/
theorem stableGreedy_eventually_crosses_threshold
    {O : OrderedLanguage} {adversary generator : ℕ → ℕ}
    {T m : ℕ}
    (hplay : FreshPlay adversary generator)
    (hgreedy : GreedyFrom O adversary generator T) :
    ∀ᶠ i in Filter.atTop,
      gcgThreshold m ≤ timelyDensity generator O.enumeration id i := by
  have hcard : ∀ i,
      (i - 2 * (2 * T + 2)) / 2 ≤
        (timelyElements generator O.enumeration id i).card := by
    intro i
    have hbound := stableGreedy_card_bound
      (i := i) hplay hgreedy
    omega
  have hcross := stage_eventually_crosses_threshold m (2 * T + 2)
    (fun i => (timelyElements generator O.enumeration id i).card)
    (Filter.Eventually.of_forall hcard)
  filter_upwards [hcross, Filter.eventually_gt_atTop 0] with i hi hpos
  simpa [timelyDensity, Nat.ne_of_gt hpos] using hi

end GenLimit.TimeSensitive
