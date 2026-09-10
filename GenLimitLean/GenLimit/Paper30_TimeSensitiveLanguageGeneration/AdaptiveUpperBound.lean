import GenLimit.Paper30_TimeSensitiveLanguageGeneration.AdaptivePresentationExact
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.GreedyRun

/-!
# The adaptive half-density upper bound

Every timely target point first emitted on an ordinary round is paired with
the least-unused target point announced immediately before it.  The partner
has lower target rank, is never emitted by the generator, and the pairing is
injective.  Only the exponentially sparse catch-up rounds are exceptions;
there are at most `log2 i` of them before target rank `i`.
-/

namespace GenLimit.TimeSensitive

open Filter
open GenLimit.KleinbergWei

noncomputable def firstGeneratorTime
    (generator : ℕ → ℕ) (x : ℕ) : ℕ := by
  classical
  exact if h : x ∈ Set.range generator then Nat.find h else 0

theorem firstGeneratorTime_spec
    {generator : ℕ → ℕ} {x : ℕ} (hx : x ∈ Set.range generator) :
    generator (firstGeneratorTime generator x) = x := by
  classical
  simp only [firstGeneratorTime, dif_pos hx]
  exact Nat.find_spec hx

theorem firstGeneratorTime_min
    {generator : ℕ → ℕ} {x : ℕ} (hx : x ∈ Set.range generator)
    {t : ℕ} (ht : generator t = x) :
    firstGeneratorTime generator x ≤ t := by
  classical
  simp only [firstGeneratorTime, dif_pos hx]
  exact Nat.find_min' hx ht

theorem mem_timelyElements_iff_p30
    {S R : ℕ → ℕ} {D : ℕ → ℕ} {i x : ℕ} :
    x ∈ timelyElements S R D i ↔
      ∃ j, j < i ∧ R j = x ∧ ∃ q, q < D j ∧ S q = R j := by
  classical
  simp only [timelyElements, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range, mem_sequencePrefix_iff]
  constructor
  · rintro ⟨j, ⟨hji, q, hqD, hq⟩, hjx⟩
    exact ⟨j, hji, hjx, q, hqD, hq⟩
  · rintro ⟨j, hji, hjx, q, hqD, hq⟩
    exact ⟨j, ⟨hji, q, hqD, hq⟩, hjx⟩

theorem mem_timelyElements_rank_firstGeneratorTime
    {O : OrderedLanguage} {generator : ℕ → ℕ} {i x : ℕ}
    (hx : x ∈ timelyElements generator O.enumeration id i) :
    ∃ j, j < i ∧ O.enumeration j = x ∧
      firstGeneratorTime generator x < j ∧
      generator (firstGeneratorTime generator x) = x := by
  obtain ⟨j, hji, hjx, q, hqj, hq⟩ :=
    mem_timelyElements_iff_p30.mp hx
  have hxRange : x ∈ Set.range generator := ⟨q, hq.trans hjx⟩
  refine ⟨j, hji, hjx, ?_, firstGeneratorTime_spec hxRange⟩
  exact (firstGeneratorTime_min hxRange (hq.trans hjx)).trans_lt hqj

noncomputable def adaptiveCredited
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (i : ℕ) :
    Finset ℕ :=
  timelyElements (adaptiveGCGOutput F O) O.enumeration id i

noncomputable def adaptiveExceptionalCredits
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (i : ℕ) :
    Finset ℕ := by
  classical
  exact (adaptiveCredited F O i).filter fun x =>
    IsCatchupRound (firstGeneratorTime (adaptiveGCGOutput F O) x)

noncomputable def adaptivePairedCredits
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (i : ℕ) :
    Finset ℕ :=
  adaptiveCredited F O i \ adaptiveExceptionalCredits F O i

noncomputable def adaptivePartner
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (x : ℕ) : ℕ :=
  adaptivePresentation F O
    (firstGeneratorTime (adaptiveGCGOutput F O) x)

@[simp] theorem mem_adaptiveExceptionalCredits
    {F : CanonicallyOrderedFamily} {O : OrderedLanguage} {i x : ℕ} :
    x ∈ adaptiveExceptionalCredits F O i ↔
      x ∈ adaptiveCredited F O i ∧
        IsCatchupRound (firstGeneratorTime (adaptiveGCGOutput F O) x) := by
  classical
  simp [adaptiveExceptionalCredits]

@[simp] theorem mem_adaptivePairedCredits
    {F : CanonicallyOrderedFamily} {O : OrderedLanguage} {i x : ℕ} :
    x ∈ adaptivePairedCredits F O i ↔
      x ∈ adaptiveCredited F O i ∧
        ¬IsCatchupRound (firstGeneratorTime (adaptiveGCGOutput F O) x) := by
  classical
  constructor
  · intro hx
    have hcredit := (Finset.mem_sdiff.mp hx).1
    have hnotExceptional := (Finset.mem_sdiff.mp hx).2
    refine ⟨hcredit, ?_⟩
    intro hcatch
    exact hnotExceptional
      (mem_adaptiveExceptionalCredits.mpr ⟨hcredit, hcatch⟩)
  · rintro ⟨hcredit, hnotCatch⟩
    exact Finset.mem_sdiff.mpr ⟨hcredit, fun hexception =>
      hnotCatch (mem_adaptiveExceptionalCredits.mp hexception).2⟩

theorem adaptivePartner_mem_targetPrefix
    {F : CanonicallyOrderedFamily} {O : OrderedLanguage} {i x : ℕ}
    (hx : x ∈ adaptivePairedCredits F O i) :
    adaptivePartner F O x ∈ targetPrefix O.enumeration i := by
  classical
  have hxCredit := (mem_adaptivePairedCredits.mp hx).1
  have hqOrdinary := (mem_adaptivePairedCredits.mp hx).2
  obtain ⟨j, hji, hjx, hqj, hqx⟩ :=
    mem_timelyElements_rank_firstGeneratorTime hxCredit
  let q := firstGeneratorTime (adaptiveGCGOutput F O) x
  let used := adaptiveUsed (adaptiveGCGRun F O q)
  have hjUnused : UnusedTargetRank O used j := by
    intro hused
    rcases Finset.mem_union.mp hused with hobserved | houtput
    · rw [adaptiveGCGRun_observations_eq] at hobserved
      simp only [List.mem_toFinset, List.mem_map, List.mem_range] at hobserved
      obtain ⟨s, hsq, hs⟩ := hobserved
      exact (adaptiveGCG_freshPlay F O).fresh_adversary q s
        (Nat.le_of_lt hsq) (hs.trans (hjx.trans hqx.symm))
    · rw [adaptiveGCGRun_outputs_eq] at houtput
      simp only [List.mem_toFinset, List.mem_map, List.mem_range] at houtput
      obtain ⟨s, hsq, hs⟩ := houtput
      have hxmin : q ≤ s :=
        firstGeneratorTime_min ⟨q, hqx⟩ (hs.trans hjx)
      omega
  have hle : leastUnusedTargetRank O used ≤ j :=
    leastUnusedTargetRank_min O used hjUnused
  have hpartner : adaptivePartner F O x = leastUnusedTarget O used := by
    exact adaptivePresentation_eq_least_of_not_catchup F O hqOrdinary
  have hne : leastUnusedTargetRank O used ≠ j := by
    intro heq
    have heqValues : adaptivePartner F O x = x := by
      rw [hpartner]
      exact (congrArg O.enumeration heq).trans hjx
    exact (adaptiveGCG_freshPlay F O).fresh_adversary q q le_rfl
      (heqValues.trans hqx.symm)
  change adaptivePartner F O x ∈ sequencePrefix O.enumeration i
  rw [mem_sequencePrefix_iff]
  refine ⟨leastUnusedTargetRank O used,
    (lt_of_le_of_ne hle hne).trans hji, ?_⟩
  exact hpartner.symm

theorem adaptivePartner_not_mem_credited
    {F : CanonicallyOrderedFamily} {O : OrderedLanguage} {i x : ℕ}
    (hx : x ∈ adaptivePairedCredits F O i) :
    adaptivePartner F O x ∉ adaptiveCredited F O i := by
  classical
  intro hpartnerCredit
  have hqOrdinary := (mem_adaptivePairedCredits.mp hx).2
  let q := firstGeneratorTime (adaptiveGCGOutput F O) x
  have hpartnerEq : adaptivePartner F O x =
      leastUnusedTarget O (adaptiveUsed (adaptiveGCGRun F O q)) :=
    adaptivePresentation_eq_least_of_not_catchup F O hqOrdinary
  obtain ⟨k, hki, hkpartner, hrk, hrpartner⟩ :=
    mem_timelyElements_rank_firstGeneratorTime hpartnerCredit
  let r := firstGeneratorTime (adaptiveGCGOutput F O) (adaptivePartner F O x)
  by_cases hrq : r < q
  · apply leastUnusedTarget_fresh O (adaptiveUsed (adaptiveGCGRun F O q))
    rw [← hpartnerEq]
    apply Finset.mem_union_right
    rw [adaptiveGCGRun_outputs_eq]
    simp only [List.mem_toFinset, List.mem_map, List.mem_range]
    exact ⟨r, hrq, hrpartner⟩
  · exact (adaptiveGCG_freshPlay F O).fresh_adversary r q
      (Nat.le_of_not_gt hrq) (by
        simpa [adaptivePartner, q, r] using hrpartner.symm)

theorem adaptivePartner_injOn
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (i : ℕ) :
    Set.InjOn (adaptivePartner F O) (adaptivePairedCredits F O i) := by
  intro x hx y hy hxy
  have hxCredit := (mem_adaptivePairedCredits.mp hx).1
  have hyCredit := (mem_adaptivePairedCredits.mp hy).1
  have hxOrdinary := (mem_adaptivePairedCredits.mp hx).2
  have hyOrdinary := (mem_adaptivePairedCredits.mp hy).2
  obtain ⟨_, _, _, _, hxSpec⟩ :=
    mem_timelyElements_rank_firstGeneratorTime hxCredit
  obtain ⟨_, _, _, _, hySpec⟩ :=
    mem_timelyElements_rank_firstGeneratorTime hyCredit
  let qx := firstGeneratorTime (adaptiveGCGOutput F O) x
  let qy := firstGeneratorTime (adaptiveGCGOutput F O) y
  have htime : qx = qy := by
    rcases lt_trichotomy qx qy with hlt | heq | hgt
    · exact False.elim
        ((adaptivePresentation_ne_prior_of_not_catchup F O hlt hyOrdinary) hxy.symm)
    · exact heq
    · exact False.elim
        ((adaptivePresentation_ne_prior_of_not_catchup F O hgt hxOrdinary) hxy)
  calc
    x = adaptiveGCGOutput F O qx := hxSpec.symm
    _ = adaptiveGCGOutput F O qy := by rw [htime]
    _ = y := hySpec

noncomputable def catchupRounds (i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range i).filter IsCatchupRound

@[simp] theorem mem_catchupRounds {i q : ℕ} :
    q ∈ catchupRounds i ↔ q < i ∧ IsCatchupRound q := by
  classical
  simp [catchupRounds]

theorem catchupIndex_lt_log2_of_lt
    {q i : ℕ} (hcatch : IsCatchupRound q) (hqi : q < i) :
    catchupIndex q < Nat.log2 i := by
  have hqpos : q ≠ 0 := by
    rw [catchupIndex_spec hcatch]
    positivity
  have hipos : i ≠ 0 := by omega
  have hlogq : Nat.log2 q = catchupIndex q + 1 := by
    calc
      Nat.log2 q = Nat.log 2 q := Nat.log2_eq_log_two
      _ = Nat.log 2 (2 ^ (catchupIndex q + 1)) := by
        rw [← catchupIndex_spec hcatch]
      _ = catchupIndex q + 1 := Nat.log_pow (by omega : 1 < 2) _
  have hmono : Nat.log2 q ≤ Nat.log2 i := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (Nat.le_of_lt hqi)
  omega

theorem catchupIndex_injOn (i : ℕ) :
    Set.InjOn catchupIndex (catchupRounds i) := by
  intro q hq r hr hindex
  have hqCatch := (mem_catchupRounds.mp hq).2
  have hrCatch := (mem_catchupRounds.mp hr).2
  calc
    q = 2 ^ (catchupIndex q + 1) := catchupIndex_spec hqCatch
    _ = 2 ^ (catchupIndex r + 1) := by rw [hindex]
    _ = r := (catchupIndex_spec hrCatch).symm

theorem catchupRounds_card_le_log2 (i : ℕ) :
    (catchupRounds i).card ≤ Nat.log2 i := by
  classical
  have h := Finset.card_le_card_of_injOn
    (s := catchupRounds i) (t := Finset.range (Nat.log2 i)) catchupIndex
    (by
      intro q hq
      apply Finset.mem_coe.mpr
      apply Finset.mem_range.mpr
      exact catchupIndex_lt_log2_of_lt
        (mem_catchupRounds.mp hq).2 (mem_catchupRounds.mp hq).1)
    (catchupIndex_injOn i)
  simpa only [Finset.card_range] using h

theorem adaptiveExceptionalCredits_card_le_log2
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (i : ℕ) :
    (adaptiveExceptionalCredits F O i).card ≤ Nat.log2 i := by
  classical
  apply le_trans
    (Finset.card_le_card_of_injOn
      (firstGeneratorTime (adaptiveGCGOutput F O))
      (s := adaptiveExceptionalCredits F O i)
      (t := catchupRounds i) ?_ ?_)
    (catchupRounds_card_le_log2 i)
  · intro x hx
    change firstGeneratorTime (adaptiveGCGOutput F O) x ∈ catchupRounds i
    rw [mem_catchupRounds]
    have hxCredit := (mem_adaptiveExceptionalCredits.mp hx).1
    obtain ⟨j, hji, hjx, hqj, hqx⟩ :=
      mem_timelyElements_rank_firstGeneratorTime hxCredit
    exact ⟨hqj.trans hji, (mem_adaptiveExceptionalCredits.mp hx).2⟩
  · intro x hx y hy htime
    have hxCredit := (mem_adaptiveExceptionalCredits.mp hx).1
    have hyCredit := (mem_adaptiveExceptionalCredits.mp hy).1
    obtain ⟨_, _, _, _, hxSpec⟩ :=
      mem_timelyElements_rank_firstGeneratorTime hxCredit
    obtain ⟨_, _, _, _, hySpec⟩ :=
      mem_timelyElements_rank_firstGeneratorTime hyCredit
    calc
      x = adaptiveGCGOutput F O
          (firstGeneratorTime (adaptiveGCGOutput F O) x) := hxSpec.symm
      _ = adaptiveGCGOutput F O
          (firstGeneratorTime (adaptiveGCGOutput F O) y) := by rw [htime]
      _ = y := hySpec

/-- Finite turn-taking certificate for the concrete adaptive presentation. -/
theorem adaptive_turnTaking_finite_bound
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (i : ℕ) :
    2 * (timelyElements (adaptiveGCGOutput F O)
        O.enumeration id i).card ≤ i + 2 * Nat.log2 i := by
  classical
  apply turnTaking_finite_upper_bound
    (prefixSet := targetPrefix O.enumeration i)
    (credited := adaptiveCredited F O i)
    (paired := adaptivePairedCredits F O i)
    (exceptions := adaptiveExceptionalCredits F O i)
    (partner := adaptivePartner F O)
    (e := Nat.log2 i)
  · exact targetPrefix_card_ordered O i
  · intro x hx
    obtain ⟨j, hji, rfl, q, hqj, hq⟩ :=
      mem_timelyElements_iff_p30.mp hx
    exact (mem_sequencePrefix_iff O.enumeration (O.enumeration j) i).mpr
      ⟨j, hji, rfl⟩
  · intro x hx
    by_cases hexception : x ∈ adaptiveExceptionalCredits F O i
    · exact Finset.mem_union_right _ hexception
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hx, hexception⟩)
  · exact Finset.sdiff_subset
  · exact adaptiveExceptionalCredits_card_le_log2 F O i
  · exact fun x hx => adaptivePartner_mem_targetPrefix hx
  · exact fun x hx => adaptivePartner_not_mem_credited hx
  · exact adaptivePartner_injOn F O i

theorem catchupRatio_log2_tendsto_zero :
    Tendsto (catchupRatio Nat.log2) atTop (nhds 0) := by
  have heq : catchupRatio Nat.log2 =
      fun n : ℕ => (Nat.log2 n : ℝ) / (n : ℝ) := by
    funext n
    by_cases hn : n = 0 <;> simp [catchupRatio, hn]
  rw [heq]
  exact GenLimit.tendsto_natLog2_div

/-- The concrete adaptive exact presentation forces the repaired GCG's
instance-level timely upper density to be at most one half. -/
theorem adaptive_upperTimelyDensity_le_half
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) :
    upperTimelyDensity (adaptiveGCGOutput F O) O.enumeration id ≤
      (1 / 2 : ℝ) := by
  apply upperTimelyDensity_le_half_of_turnTaking _ _ Nat.log2
  · exact Filter.Eventually.of_forall
      (adaptive_turnTaking_finite_bound F O)
  · exact catchupRatio_log2_tendsto_zero

end GenLimit.TimeSensitive
