import GenLimit.Paper32_InfinitelyManyHallucinations.Definitions

/-! # Reading a single-step exhaustion as an element stream

Empty increments are allowed. Repeat the first observed word on those
rounds. Once a word has been observed, the whole resulting input prefix can
be reconstructed from the finite history. -/

namespace GenLimit.InfinitelyManyHallucinations

open Set

/-- A batch chosen from an exhaustion up to stage `n` may also use the
previous guess. Causality makes its implementation on finite histories
independent of the completion chosen here. -/
abbrev StageRule := Exhaustion → ℕ → Finset ℕ → Finset ℕ

def StageRule.Causal (R : StageRule) : Prop :=
  ∀ (A B : Exhaustion) n, (∀ i ≤ n, A.stage i = B.stage i) →
    ∀ previous, R A n previous = R B n previous

private def Matches (n : ℕ) (h : Fin (n+1) → Finset ℕ) (A : Exhaustion) : Prop :=
  ∀ i : Fin (n+1), A.stage i = h i

noncomputable def StageRule.toBatch (R : StageRule) : BatchGenerator := by
  classical
  exact fun n h previous =>
    if hex : ∃ A, Matches n h A then R hex.choose n previous else ∅

theorem StageRule.toBatch_apply {R : StageRule} (hc : R.Causal) (A : Exhaustion) (n : ℕ)
    (previous : Finset ℕ) : R.toBatch n (fun i => A.stage i) previous = R A n previous := by
  classical
  have hex : ∃ B, Matches n (fun i => A.stage i) B := ⟨A, fun _ => rfl⟩
  simp only [StageRule.toBatch, dif_pos hex]
  exact hc _ A n (fun i hi => hex.choose_spec ⟨i,by omega⟩) previous

namespace Exhaustion

noncomputable def chooseWord (S : Finset ℕ) (d : ℕ) :=
  if h : S.Nonempty then S.min' h else d

theorem chooseWord_mem {S : Finset ℕ} (h : S.Nonempty) (d : ℕ) : chooseWord S d ∈ S := by
  simpa [chooseWord, h] using Finset.min'_mem S h

noncomputable def openingTime (A : Exhaustion) : ℕ := by
  classical
  exact if h : ∃ n, (A.stage n).Nonempty then Nat.find h else 0

theorem openingTime_spec (A : Exhaustion) {n : ℕ} (hn : (A.stage n).Nonempty) :
    (A.stage A.openingTime).Nonempty ∧ A.openingTime ≤ n := by
  classical
  have he : ∃ t, (A.stage t).Nonempty := ⟨n,hn⟩
  simp only [openingTime, dif_pos he]
  exact ⟨Nat.find_spec he, Nat.find_min' he hn⟩

noncomputable def inputWord (A : Exhaustion) (t : ℕ) : ℕ :=
  chooseWord (A.increment (t+1)) (chooseWord (A.stage A.openingTime) 0)

theorem inputWord_prefix {A B : Exhaustion} {n : ℕ}
    (h : ∀ i ≤ n+1, A.stage i = B.stage i) (ha : (A.stage (n+1)).Nonempty) :
    ∀ t ≤ n, A.inputWord t = B.inputWord t := by
  have hb := (h _ le_rfl) ▸ ha
  obtain ⟨ha',hla⟩ := A.openingTime_spec ha
  obtain ⟨hb',hlb⟩ := B.openingTime_spec hb
  have hbAt : (B.stage A.openingTime).Nonempty := (h _ hla) ▸ ha'
  have haAt : (A.stage B.openingTime).Nonempty := (h _ hlb).symm ▸ hb'
  have eqTime := le_antisymm (A.openingTime_spec haAt).2 (B.openingTime_spec hbAt).2
  intro t ht
  simp only [inputWord, increment, h t (by omega), h (t+1) (by omega), eqTime, h _ hlb]

/-- Every currently revealed word occurred in the padded element prefix. -/
theorem stage_mem_inputWord {A : Exhaustion} (hA : A.IsSingleStep) (t : ℕ) :
    ∀ x ∈ A.stage (t+1), ∃ j ≤ t, A.inputWord j = x := by
  have newest (i x : ℕ) (hx : x ∈ A.increment (i+1)) : A.inputWord i = x :=
    Finset.card_le_one.mp (hA i) _ (chooseWord_mem ⟨x,hx⟩ _) _ hx
  induction t with
  | zero =>
    intro x hx
    refine ⟨0,le_rfl,newest 0 x ?_⟩
    simpa [increment, A.stage_zero] using hx
  | succ t ih =>
    intro x hx
    by_cases old : x ∈ A.stage (t+1)
    · obtain ⟨j,hj,he⟩ := ih x old
      exact ⟨j,by omega,he⟩
    · exact ⟨t+1,le_rfl,newest _ x (Finset.mem_sdiff.mpr ⟨hx,old⟩)⟩

theorem inputWord_presents {A : Exhaustion} (hA : A.IsSingleStep) (hi : A.limit.Nonempty) :
    GenLimit.Presents A.inputWord A.limit := by
  obtain ⟨x,n,hx⟩ := hi
  have ho := (A.openingTime_spec (show (A.stage n).Nonempty from ⟨x,hx⟩)).1
  apply Set.Subset.antisymm
  · rintro _ ⟨t,rfl⟩
    by_cases he : (A.increment (t+1)).Nonempty
    · exact A.stage_subset_limit _ (Finset.mem_sdiff.mp (chooseWord_mem he _)).1
    · simp only [inputWord, chooseWord, dif_neg he, dif_pos ho]
      exact A.stage_subset_limit _ (Finset.min'_mem _ _)
  · rintro y ⟨m,hm⟩
    obtain ⟨j,_,hj⟩ := stage_mem_inputWord hA m y (A.monotone_stage (Nat.le_succ _) hm)
    exact ⟨j,hj⟩

end Exhaustion

end GenLimit.InfinitelyManyHallucinations
