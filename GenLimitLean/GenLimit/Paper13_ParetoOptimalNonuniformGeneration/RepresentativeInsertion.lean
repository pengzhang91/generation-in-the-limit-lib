import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.Representative

/-! # Procedure 3 computes the representative complexity

Process the old coordinates from right to left in their sorted order.
The displayed raw scarcity maximum is recomputed before each comparison.
A crossed coordinate cannot be part of a witness at which its existing
deadline applies. At the stopping position every remaining coordinate's
deadline applies at the raw maximum. This identifies the inserted score
with the intrinsic obstruction maximum used in Theorems 7 and 9. -/
namespace GenLimit.ParetoGeneration.Representative
open RepresentativeGeneration
variable {α : Type*} [DecidableEq α]

private def candidates (F : ℕ → Set α) (g : ℕ → Set α) (ε : ℝ)
    (i : ℕ) (scope : List ℕ) (eligible : ℕ → ℕ → Prop) : Set ℕ :=
  insert 0 {n | ∃ (S : Finset α) (W : Finset ℕ), S.card = n ∧ S.Nonempty ∧ i ∈ W ∧
    (∀ j ∈ W, (j = i ∨ j ∈ scope) ∧ (↑S : Set α) ⊆ F j ∧ (j ≠ i → eligible j n)) ∧
    ¬ Feasible F g ε S W}

/-- Existence of the raw maximum at the initial comparison of every insertion.
All subsequent comparisons use a subcollection of this initial scope. -/
def BoundedRawScores (F : ℕ → Set α) (g : ℕ → Set α) (ε : ℝ) :=
  ∀ i, BddAbove (insert 0 {n | Obstruction F g ε i (fun _ _ ↦ 0) n})

theorem BoundedRawScores.intrinsic {F : ℕ → Set α} {g : ℕ → Set α} {ε : ℝ}
    (h : BoundedRawScores F g ε) : BoundedObstructions F g ε := by
  intro i
  apply (h i).mono
  rintro n (rfl | ⟨S,W,rfl,hS,hi,hW,hb⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨S,W,rfl,hS,hi,fun j hj ↦
      ⟨(hW j hj).1,(hW j hj).2.1,fun _ ↦ Finset.card_pos.mpr hS⟩,hb⟩

private theorem candidates_bounded (F : ℕ → Set α) (g : ℕ → Set α)
    (ε : ℝ) (hb : BoundedRawScores F g ε) (i : ℕ) (l : List ℕ)
    (hl : ∀ j ∈ l, j < i) (p : ℕ → ℕ → Prop) :
    BddAbove (candidates F g ε i l p) := by
  apply (hb i).mono
  rintro n (rfl | ⟨S,W,rfl,hS,hi,hW,hb⟩)
  · exact Set.mem_insert _ _
  · refine Or.inr ⟨S,W,rfl,hS,hi,fun j hj ↦ ?_,hb⟩
    obtain ⟨hm,hs,_⟩ := hW j hj
    exact ⟨hm.elim (fun he ↦ he.le) (fun h ↦ (hl j h).le),hs,fun _ ↦ Finset.card_pos.mpr hS⟩

/-- Largest sample witnessing group scarcity in a subcollection containing
the newly inserted language. Zero totalizes the empty maximum. -/
noncomputable def rawScore (F : ℕ → Set α) (g : ℕ → Set α) (ε : ℝ)
    (i : ℕ) (l : List ℕ) := sSup (candidates F g ε i l (fun _ _ ↦ True))

/-- Numerical part of Procedure 3, traversing the old sorted order in reverse.
An equality triggers a swap, in accordance with the printed comparator. -/
noncomputable def insertionValue (F : ℕ → Set α) (g : ℕ → Set α) (ε : ℝ)
    (d : ℕ → ℕ) (i : ℕ) : List ℕ → ℕ
  | [] => rawScore F g ε i []
  | j :: tail => if d j < rawScore F g ε i (j::tail) then rawScore F g ε i (j::tail)
      else insertionValue F g ε d i tail

private theorem insertion_eq_sup (F : ℕ → Set α) (g : ℕ → Set α)
    (ε : ℝ) (hb : BoundedRawScores F g ε)
    (d : ℕ → ℕ) (i : ℕ) (l : List ℕ) (hl : ∀ j ∈ l, j < i)
    (hsort : l.Pairwise (fun a b ↦ d b ≤ d a)) :
    insertionValue F g ε d i l = sSup (candidates F g ε i l (fun j n ↦ d j < n)) := by
  classical
  have bounded' (l : List ℕ) (hl : ∀ j ∈ l, j < i) (p : ℕ → ℕ → Prop) :=
    candidates_bounded F g ε hb i l hl p
  have weaken (l : List ℕ) : candidates F g ε i l (fun j n ↦ d j < n) ⊆
      candidates F g ε i l (fun _ _ ↦ True) := by
    rintro n (rfl | ⟨S,W,he,hS,hi,hW,hb⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨S,W,he,hS,hi,fun j hj ↦ ⟨(hW j hj).1,(hW j hj).2.1,fun _ ↦ trivial⟩,hb⟩
  induction l with
  | nil =>
    apply congrArg sSup
    apply Set.Subset.antisymm _ (weaken [])
    rintro n (rfl | ⟨S,W,he,hS,hi,hW,hb⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨S,W,he,hS,hi,fun j hj ↦ ⟨(hW j hj).1,(hW j hj).2.1,fun hn ↦
        (hn ((hW j hj).1.resolve_right (by simp))).elim⟩,hb⟩
  | cons j l ih =>
    let scope := j::l
    let m := rawScore F g ε i scope
    have hj : j < i := hl j (by simp)
    have hl' (x) (hx : x ∈ l) := hl x (List.mem_cons_of_mem _ hx)
    have boundRaw := bounded' scope hl (fun _ _ ↦ True)
    have boundCon := bounded' scope hl (fun j n ↦ d j < n)
    have nr (l : List ℕ) (p : ℕ → ℕ → Prop) : (candidates F g ε i l p).Nonempty :=
      ⟨0,Or.inl rfl⟩
    change (if d j < m then m else insertionValue F g ε d i l) = _
    by_cases h : d j < m
    · rw [if_pos h]
      apply le_antisymm _ (csSup_le (nr _ _) (fun n hn ↦ le_csSup boundRaw (weaken scope hn)))
      apply le_csSup boundCon
      have hm : m ∈ candidates F g ε i scope (fun _ _ ↦ True) := Nat.sSup_mem (nr _ _) boundRaw
      rcases hm with he | ⟨S,W,he,hS,hi,hW,hb⟩
      · exact Or.inl he
      · refine Or.inr ⟨S,W,he,hS,hi,fun a ha ↦ ⟨(hW a ha).1,(hW a ha).2.1,fun hn ↦ ?_⟩,hb⟩
        rcases List.mem_cons.mp ((hW a ha).1.resolve_left hn) with rfl | hmem
        · exact h
        · exact ((List.pairwise_cons.mp hsort).1 a hmem).trans_lt h
    · rw [if_neg h,ih hl' (List.pairwise_cons.mp hsort).2]
      apply congrArg sSup
      ext n
      constructor
      · rintro (hn | ⟨S,W,he,hS,hi,hW,hb⟩)
        · exact Or.inl hn
        · refine Or.inr ⟨S,W,he,hS,hi,fun a ha ↦ ?_,hb⟩
          obtain ⟨ha',hs,hd⟩ := hW a ha
          exact ⟨ha'.imp_right (List.mem_cons_of_mem _),hs,hd⟩
      · intro hn
        have hnm : n ≤ m := le_csSup boundRaw (weaken scope hn)
        rcases hn with hn | ⟨S,W,he,hS,hi,hW,hb⟩
        · exact Or.inl hn
        · refine Or.inr ⟨S,W,he,hS,hi,fun a ha ↦ ?_,hb⟩
          obtain ⟨ha',hs,hd⟩ := hW a ha
          refine ⟨ha'.imp_right (fun hmem ↦ ?_),hs,hd⟩
          rcases List.mem_cons.mp hmem with rfl | ha
          · exact (h ((hd hj.ne).trans_le hnm)).elim
          · exact ha

/-- Any reverse-sorted old order containing exactly the preceding indices
gives the same new complexity by the published insertion comparisons. -/
theorem procedure_3_score_bounded (F : ℕ → Set α) (g : ℕ → Set α)
    (ε : ℝ) (hb : BoundedRawScores F g ε) (i : ℕ) (l : List ℕ)
    (hl : ∀ j, j ∈ l ↔ j < i)
    (hsort : l.Pairwise (fun a b ↦ complexity F g ε b ≤ complexity F g ε a)) :
    insertionValue F g ε (complexity F g ε) i l = complexity F g ε i := by
  let d := complexity F g ε
  rw [insertion_eq_sup F g ε hb d i l (fun j ↦ (hl j).mp) hsort]
  conv_rhs => rw [complexity]
  apply congrArg sSup
  ext n
  constructor
  · rintro (he | ⟨S,W,he,hS,hi,hW,hb⟩)
    · exact Or.inl he
    · refine Or.inr ⟨S,W,he,hS,hi,fun j hj ↦ ?_,hb⟩
      obtain ⟨hm,hs,hd⟩ := hW j hj
      exact ⟨hm.elim (fun h ↦ h.le) (fun h ↦ ((hl j).mp h).le),hs,fun h ↦ hd h.ne⟩
  · rintro (he | ⟨S,W,he,hS,hi,hW,hb⟩)
    · exact Or.inl he
    · refine Or.inr ⟨S,W,he,hS,hi,fun j hj ↦ ?_,hb⟩
      obtain ⟨hm,hs,hd⟩ := hW j hj
      exact ⟨hm.eq_or_lt.imp_right (hl j).mpr,hs,fun h ↦ hd (lt_of_le_of_ne hm h)⟩

theorem procedure_3_score {k : ℕ} (F : ℕ → Set α) (groups : Fin k → Set α)
    (hp : IsFinitePartition groups) (ε : ℝ) (hε : 0 < ε) (i : ℕ) (l : List ℕ)
    (hl : ∀ j, j ∈ l ↔ j < i)
    (hsort : l.Pairwise (fun a b ↦ complexity F (extendFinitePartition groups) ε b ≤
      complexity F (extendFinitePartition groups) ε a)) :
    insertionValue F (extendFinitePartition groups) ε
      (complexity F (extendFinitePartition groups) ε) i l =
      complexity F (extendFinitePartition groups) ε i :=
  procedure_3_score_bounded F _ ε (fun j ↦ obstruction_sizes_bounded F groups hp ε hε j _) i l hl hsort

/-- Theorem 9 whenever Procedure 3 defines finite scores, including zero
tolerance if its required maxima exist. -/
theorem theorem_9_of_defined_scores [Nonempty α] (F : ℕ → Set α) (g : ℕ → Set α)
    (ε : ℝ) (hb : BoundedRawScores F g ε) (hf : FiniteSublevels (complexity F g ε)) :
    variantCanonicalTime (complexity F g ε) ∈ Realizable F g ε ∧
      ParetoOptimal (Realizable F g ε) (variantCanonicalTime (complexity F g ε)) :=
  variant_exactPareto_of_finiteSublevels (of_bounded_scarcity F g ε hb.intrinsic) hf

end GenLimit.ParetoGeneration.Representative
