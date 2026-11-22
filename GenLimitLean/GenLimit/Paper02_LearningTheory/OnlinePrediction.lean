import GenLimit.Paper02_LearningTheory.Prediction

/-! # Realizable online classification, Definition 2.10 -/

namespace GenLimit.LiRamanTewari

abbrev OnlinePredictor (α : Type*) := List (α × Bool) → α → Bool

def labeledBy (K : Set α) (xs : List (α × Bool)) : Prop :=
  ∀ p ∈ xs, p.1 ∈ K ↔ p.2 = true

def mistakesFrom (A : OnlinePredictor α) (history : List (α × Bool)) : List (α × Bool) → ℕ
  | [] => 0
  | (x,b) :: tail => (if A history x = b then 0 else 1) + mistakesFrom A (history ++ [(x,b)]) tail

/-- Reciprocal-integer formulation of sublinear regret. -/
def OnlineLearnable (H : Generic.LanguageClass α) : Prop :=
  ∃ A : OnlinePredictor α, ∃ R : ℕ → ℕ,
    (∀ k : ℕ, ∃ T, ∀ t ≥ T, k * R t ≤ t) ∧
    ∀ K ∈ H, ∀ xs, labeledBy K xs → mistakesFrom A [] xs ≤ R xs.length

private abbrev Version (α : Type*) := Generic.LanguageClass α × ℕ

/-- Predict a branch that preserves the current mistake budget if such a
branch exists. Both branches cannot realize a tree of the budget depth. -/
noncomputable def dimensionPrediction (v : Version α) (x : α) : Bool := by
  classical
  exact !decide (HasShatteredLittlestoneTree (labelClass v.1 x false) v.2)

private noncomputable def updateVersion (v : Version α) (p : α × Bool) : Version α :=
  (labelClass v.1 p.1 p.2, if dimensionPrediction v p.1 = p.2 then v.2 else v.2-1)

private theorem tree_split {H : Generic.LanguageClass α} {d : ℕ} (x : α)
    (hl : HasShatteredLittlestoneTree (labelClass H x false) d)
    (hr : HasShatteredLittlestoneTree (labelClass H x true) d) :
    HasShatteredLittlestoneTree H (d+1) := by
  obtain ⟨l,hl⟩ := hl
  obtain ⟨r,hr⟩ := hr
  exact ⟨.node x l r,hl,hr⟩

noncomputable def boundedPredictor (H : Generic.LanguageClass α) (d : ℕ) : OnlinePredictor α :=
  fun hist => dimensionPrediction (hist.foldl updateVersion (H,d))

private theorem budget_step {v : Version α} (x : α) (b : Bool)
    (hbound : ¬HasShatteredLittlestoneTree v.1 (v.2+1))
    (hne : (labelClass v.1 x b).Nonempty) :
    let v' := updateVersion v (x,b)
    (if dimensionPrediction v x = b then 0 else 1) + v'.2 ≤ v.2 ∧
      ¬HasShatteredLittlestoneTree v'.1 (v'.2+1) := by
  classical
  by_cases he : dimensionPrediction v x = b
  · simp only [updateVersion, he, if_true, zero_add, le_refl, true_and]
    rintro ⟨T,hT⟩
    exact hbound ⟨T,littlestoneShattered_mono (fun _ h => h.1) hT⟩
  have hsmall : ¬HasShatteredLittlestoneTree (labelClass v.1 x b) v.2 := by
    cases b with
    | false => simpa [dimensionPrediction] using he
    | true =>
      have hl : HasShatteredLittlestoneTree (labelClass v.1 x false) v.2 := by
        simpa [dimensionPrediction] using he
      exact fun hr => hbound (tree_split x hl hr)
  have hpos : v.2 ≠ 0 := by
    intro h
    rw [h] at hsmall
    exact hsmall ⟨.leaf,hne⟩
  simp only [updateVersion, if_neg he]
  exact ⟨by omega, by simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hpos)] using hsmall⟩

private theorem bounded_mistakes {H : Generic.LanguageClass α} {d : ℕ} (K : Set α)
    (xs history : List (α × Bool))
    (hlabels : labeledBy K xs)
    (hK : K ∈ (history.foldl updateVersion (H,d)).1)
    (hbound : ¬HasShatteredLittlestoneTree (history.foldl updateVersion (H,d)).1
      ((history.foldl updateVersion (H,d)).2+1)) :
    mistakesFrom (boundedPredictor H d) history xs ≤ (history.foldl updateVersion (H,d)).2 := by
  induction xs generalizing history with
  | nil => exact Nat.zero_le _
  | cons p tail ih =>
    rcases p with ⟨x,b⟩
    let v := history.foldl updateVersion (H,d)
    have hK' : K ∈ labelClass v.1 x b := ⟨hK,hlabels (x,b) (by simp)⟩
    obtain ⟨hstep,hnext⟩ := budget_step x b hbound ⟨K,hK'⟩
    have ht := ih (history ++ [(x,b)]) (fun p hp => hlabels p (List.mem_cons_of_mem _ hp))
      (by simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using hK')
      (by simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using hnext)
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at ht
    exact (Nat.add_le_add_left ht _).trans hstep

/-- Finite dimension gives an absolute mistake bound on every realizable
sequence, hence sublinear regret. -/
theorem onlineLearnable_of_finiteLittlestone {H : Generic.LanguageClass α}
    (h : HasFiniteLittlestoneDimension H) : OnlineLearnable H := by
  obtain ⟨d, hd⟩ := h
  exact ⟨boundedPredictor H d, fun _ => d, fun k => ⟨k*d,fun _ ht => ht⟩,
    fun K hK xs hx => bounded_mistakes K xs [] hx hK hd⟩

private theorem adversarial_path (A : OnlinePredictor α) {d : ℕ} (T : LittlestoneTree α d)
    {H : Generic.LanguageClass α} (hs : LittlestoneShattered T H) (hist : List (α × Bool)) :
    ∃ xs, xs.length = d ∧ mistakesFrom A hist xs = d ∧ ∃ K ∈ H, labeledBy K xs := by
  induction T generalizing H hist with
  | leaf =>
    obtain ⟨K,hK⟩ := hs
    exact ⟨[],rfl,rfl,K,hK,by simp [labeledBy]⟩
  | @node d x l r il ir =>
    let b := !(A hist x)
    have hbranch : ∃ xs, xs.length = d ∧ mistakesFrom A (hist ++ [(x,b)]) xs = d ∧
        ∃ K ∈ labelClass H x b, labeledBy K xs := by
      cases he : b with
      | false => exact il hs.1 _
      | true => exact ir hs.2 _
    obtain ⟨xs,hx,hm,K,hK,hl⟩ := hbranch
    refine ⟨(x,b)::xs, by simp [hx], ?_,K,hK.1,?_⟩
    · have hn : A hist x ≠ b := by simp [b]
      simp [mistakesFrom, hn, hm, Nat.add_comm]
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hK.2
      · exact hl _ hp

/-- A shattered tree produces a fixed realizable sequence on which every
prediction is wrong. Arbitrarily deep trees exclude sublinear regret. -/
theorem not_onlineLearnable_of_infiniteLittlestone {H : Generic.LanguageClass α}
    (h : HasInfiniteLittlestoneDimension H) : ¬OnlineLearnable H := by
  rintro ⟨A,R,sublinear,guarantee⟩
  obtain ⟨T,hT⟩ := sublinear 2
  obtain ⟨tree,htree⟩ := h (T+1)
  obtain ⟨xs,hlen,hm,K,hK,hxs⟩ := adversarial_path A tree htree []
  have hb := guarantee K hK xs hxs
  rw [hm, hlen] at hb
  have := hT (T+1) (Nat.le_succ _)
  omega

theorem onlineLearnable_iff_finiteLittlestone (H : Generic.LanguageClass α) :
    OnlineLearnable H ↔ HasFiniteLittlestoneDimension H := by
  refine ⟨fun h => ?_, onlineLearnable_of_finiteLittlestone⟩
  by_contra hn
  unfold HasFiniteLittlestoneDimension at hn
  push_neg at hn
  apply not_onlineLearnable_of_infiniteLittlestone (H := H) _ h
  intro d
  cases d with
  | zero =>
    obtain ⟨tree,ht⟩ := hn 0
    exact ⟨.leaf,littlestoneShattered_nonempty ht⟩
  | succ n => exact hn n

end GenLimit.LiRamanTewari
