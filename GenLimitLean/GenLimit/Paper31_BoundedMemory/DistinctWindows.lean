import GenLimit.Paper31_BoundedMemory.OutputSeparations

/-!
# Distinct sliding windows

Source: Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas,
*On Language Generation in the Limit with Bounded Memory*,
arXiv:2605.30324v1, Definition 11 and Lemma 4.11.

This module formalizes the repetition-free sliding-window model used in
Section 4.2 and proves the exact finite-exception conclusion of Lemma 4.11.
The source's global minimax definition is phrased for finitely repeating
presentations, but Section 4.2 explicitly restricts its window model to
repetition-free presentations.  The definitions below retain that local
regime: streams are injective exact presentations, and each window is an
ordered tuple of distinct examples.
-/

namespace GenLimit.BoundedMemory

open Function

variable {α : Type*}

/-- Ordered `W`-tuples with no repeated entries. -/
abbrev DistinctWindow (α : Type*) (W : ℕ) :=
  {w : Fin W → α // Function.Injective w}

/-- A generator which sees one ordered distinct window and always returns an
infinite language, as required by the codomain in source Definition 11. -/
structure WindowSetGenerator (α : Type*) (W : ℕ) where
  output : DistinctWindow α W → Set α
  output_infinite : ∀ w, (output w).Infinite

instance : CoeFun (WindowSetGenerator α W)
    (fun _ => DistinctWindow α W → Set α) :=
  ⟨WindowSetGenerator.output⟩

/-- A window output is source-valid when it lies inside the target language;
its infinitude is part of `WindowSetGenerator`. -/
def ValidWindowOutput
    (G : WindowSetGenerator α W) (L : Set α)
    (w : DistinctWindow α W) : Prop :=
  G w ⊆ L

/-- The length-`W` window beginning at `start` in an injective stream. -/
def windowAt (stream : ℕ → α) (hstream : Injective stream)
    (start : ℕ) (W : ℕ) : DistinctWindow α W :=
  ⟨fun i => stream (start + i), by
    intro i j hij
    apply Fin.ext
    have hindex := hstream hij
    omega⟩

/-- Success on one language under every repetition-free exact presentation.

Indexing windows by their first position is equivalent to indexing them by
their last position for eventual statements. -/
def IsRepetitionFreeWindowGeneratorOn
    (G : WindowSetGenerator α W) (L : Set α) : Prop :=
  ∀ stream : ℕ → α, ∀ hstream : Injective stream,
    GenLimit.Generic.Presents stream L →
      ∃ T, ∀ start, T ≤ start →
        ValidWindowOutput G L (windowAt stream hstream start W)

section Adversary

variable [Countable α] {W : ℕ} (hW : 0 < W)
variable (L : Set α) (hL : L.Infinite)
variable (G : WindowSetGenerator α W)

noncomputable local instance : DecidableEq α := Classical.decEq α
attribute [local instance] Classical.propDecidable

noncomputable def baseEnum : ℕ → α :=
  infiniteEnumeration L hL

theorem baseEnum_mem (n : ℕ) :
    baseEnum L hL n ∈ L :=
  infiniteEnumeration_mem L hL n

theorem baseEnum_injective :
    Injective (baseEnum L hL) :=
  infiniteEnumeration_injective L hL

theorem exists_baseEnum_not_mem (F : Finset α) :
    ∃ n, baseEnum L hL n ∉ F := by
  by_contra h
  push_neg at h
  have hsub : Set.range (baseEnum L hL) ⊆ (F : Set α) := by
    rintro x ⟨n, rfl⟩
    exact h n
  have hfin : (Set.range (baseEnum L hL)).Finite :=
    F.finite_toSet.subset hsub
  exact (Set.infinite_range_of_injective
    (baseEnum_injective L hL)) hfin

noncomputable def nextBase (F : Finset α) : α :=
  baseEnum L hL (Nat.find (exists_baseEnum_not_mem L hL F))

theorem nextBase_mem (F : Finset α) :
    nextBase L hL F ∈ L :=
  baseEnum_mem L hL _

theorem nextBase_not_mem (F : Finset α) :
    nextBase L hL F ∉ F :=
  Nat.find_spec (exists_baseEnum_not_mem L hL F)

/-- Every finite forbidden set admits a bad window disjoint from it. -/
def BadWindowsOutsideFinite : Prop :=
  ∀ F : Finset α,
    ∃ w : DistinctWindow α W,
      (∀ i, w.1 i ∈ L ∧ w.1 i ∉ F) ∧
        ¬ G w ⊆ L

variable (hbad : BadWindowsOutsideFinite L G)

noncomputable def badWindow (F : Finset α) :
    DistinctWindow α W :=
  Classical.choose (hbad F)

omit [Countable α] in
theorem badWindow_mem (F : Finset α) (i : Fin W) :
    (badWindow L G hbad F).1 i ∈ L :=
  (Classical.choose_spec (hbad F)).1 i |>.1

omit [Countable α] in
theorem badWindow_not_mem (F : Finset α) (i : Fin W) :
    (badWindow L G hbad F).1 i ∉ F :=
  (Classical.choose_spec (hbad F)).1 i |>.2

omit [Countable α] in
theorem badWindow_bad (F : Finset α) :
    ¬ G (badWindow L G hbad F) ⊆ L :=
  (Classical.choose_spec (hbad F)).2

/-- One stage: a fresh point from a fixed enumeration, followed by a bad
window disjoint from every point used earlier and from that fresh point. -/
noncomputable def selectedBlock (F : Finset α) : Fin (W + 1) → α :=
  Fin.cases (nextBase L hL F)
    (fun i => (badWindow L G hbad (insert (nextBase L hL F) F)).1 i)

@[simp] theorem selectedBlock_zero (F : Finset α) :
    selectedBlock L hL G hbad F 0 = nextBase L hL F := by
  simp [selectedBlock]

@[simp] theorem selectedBlock_succ (F : Finset α) (i : Fin W) :
    selectedBlock L hL G hbad F i.succ =
      (badWindow L G hbad (insert (nextBase L hL F) F)).1 i := by
  simp [selectedBlock]

theorem selectedBlock_mem (F : Finset α) (i : Fin (W + 1)) :
    selectedBlock L hL G hbad F i ∈ L := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using nextBase_mem L hL F
  · simpa using
      badWindow_mem L G hbad (insert (nextBase L hL F) F) j

theorem selectedBlock_not_mem (F : Finset α) (i : Fin (W + 1)) :
    selectedBlock L hL G hbad F i ∉ F := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using nextBase_not_mem L hL F
  · have hnot := badWindow_not_mem L G hbad
      (insert (nextBase L hL F) F) j
    intro hi
    apply hnot
    apply Finset.mem_insert.mpr
    exact Or.inr (by simpa using hi)

theorem selectedBlock_injective (F : Finset α) :
    Injective (selectedBlock L hL G hbad F) := by
  intro i j hij
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · rfl
    · exfalso
      have hnot := badWindow_not_mem L G hbad
        (insert (nextBase L hL F) F) j'
      apply hnot
      exact Finset.mem_insert.mpr (Or.inl (by simpa using hij.symm))
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · exfalso
      have hnot := badWindow_not_mem L G hbad
        (insert (nextBase L hL F) F) i'
      apply hnot
      exact Finset.mem_insert.mpr (Or.inl (by simpa using hij))
    · have hij' : i' = j' := by
        apply (badWindow L G hbad
          (insert (nextBase L hL F) F)).2
        simpa using hij
      exact congrArg Fin.succ hij'

noncomputable def advance (F : Finset α) : Finset α :=
  F ∪ Finset.univ.image (selectedBlock L hL G hbad F)

theorem subset_advance (F : Finset α) :
    F ⊆ advance L hL G hbad F :=
  Finset.subset_union_left

theorem selectedBlock_mem_advance (F : Finset α) (i : Fin (W + 1)) :
    selectedBlock L hL G hbad F i ∈ advance L hL G hbad F := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

noncomputable def used : ℕ → Finset α
  | 0 => ∅
  | s + 1 => advance L hL G hbad (used s)

theorem used_mono {s t : ℕ} (hst : s ≤ t) :
    used L hL G hbad s ⊆ used L hL G hbad t := by
  induction t with
  | zero =>
      have : s = 0 := by omega
      subst s
      exact fun _ hx => hx
  | succ t ih =>
      by_cases h : s = t + 1
      · subst s
        exact Finset.Subset.rfl
      · have hst' : s ≤ t := by omega
        exact (ih hst').trans
          (subset_advance L hL G hbad (used L hL G hbad t))

theorem block_fresh_at_stage (s : ℕ) (i : Fin (W + 1)) :
    selectedBlock L hL G hbad (used L hL G hbad s) i ∉
      used L hL G hbad s :=
  selectedBlock_not_mem L hL G hbad _ i

theorem earlier_block_used {s t : ℕ} (hst : s < t)
    (i : Fin (W + 1)) :
    selectedBlock L hL G hbad (used L hL G hbad s) i ∈
      used L hL G hbad t := by
  have hnext :
      selectedBlock L hL G hbad (used L hL G hbad s) i ∈
        used L hL G hbad (s + 1) := by
    simpa [used] using selectedBlock_mem_advance L hL G hbad
      (used L hL G hbad s) i
  exact used_mono L hL G hbad (by omega) hnext

/-- Flatten the constant-size stages into a stream. -/
noncomputable def badPresentation (t : ℕ) : α :=
  selectedBlock L hL G hbad
    (used L hL G hbad (t / (W + 1)))
    ⟨t % (W + 1), Nat.mod_lt _ (by omega)⟩

theorem badPresentation_mem (t : ℕ) :
    badPresentation hW L hL G hbad t ∈ L :=
  selectedBlock_mem L hL G hbad _ _

theorem badPresentation_injective :
    Injective (badPresentation hW L hL G hbad) := by
  intro a b hab
  let sa := a / (W + 1)
  let sb := b / (W + 1)
  let ia : Fin (W + 1) :=
    ⟨a % (W + 1), Nat.mod_lt _ (by omega)⟩
  let ib : Fin (W + 1) :=
    ⟨b % (W + 1), Nat.mod_lt _ (by omega)⟩
  have heq :
      selectedBlock L hL G hbad (used L hL G hbad sa) ia =
        selectedBlock L hL G hbad (used L hL G hbad sb) ib := by
    simpa [badPresentation, sa, sb, ia, ib] using hab
  have hs : sa = sb := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmem := earlier_block_used L hL G hbad hlt ia
      exact (block_fresh_at_stage L hL G hbad sb ib) (heq ▸ hmem)
    · have hmem := earlier_block_used L hL G hbad hgt ib
      exact (block_fresh_at_stage L hL G hbad sa ia) (heq.symm ▸ hmem)
  have hi : ia = ib := by
    have hused :
        used L hL G hbad sa = used L hL G hbad sb :=
      congrArg (used L hL G hbad) hs
    rw [hused] at heq
    exact selectedBlock_injective L hL G hbad _ heq
  have hdiv : a / (W + 1) = b / (W + 1) := by simpa [sa, sb] using hs
  have hmod : a % (W + 1) = b % (W + 1) := by
    simpa [ia, ib] using congrArg Fin.val hi
  exact (Nat.div_add_mod a (W + 1)).symm.trans <|
    (by rw [hdiv, hmod]; exact Nat.div_add_mod b (W + 1))

theorem pivot_at_stage (s : ℕ) :
    badPresentation hW L hL G hbad (s * (W + 1)) =
      nextBase L hL (used L hL G hbad s) := by
  simp [badPresentation]

theorem base_prefix_used (s : ℕ) :
    ∀ n < s, baseEnum L hL n ∈ used L hL G hbad s := by
  induction s with
  | zero =>
      intro n hn
      omega
  | succ s ih =>
      intro n hn
      by_cases hns : n < s
      · exact used_mono L hL G hbad (by omega) (ih n hns)
      · have hns_eq : n = s := by omega
        subst n
        by_cases hsused :
            baseEnum L hL s ∈ used L hL G hbad s
        · exact used_mono L hL G hbad (by omega) hsused
        · have hfind :
              Nat.find
                (exists_baseEnum_not_mem L hL
                  (used L hL G hbad s)) = s := by
            apply (Nat.find_eq_iff
              (exists_baseEnum_not_mem L hL
                (used L hL G hbad s))).mpr
            refine ⟨hsused, ?_⟩
            intro m hm
            exact fun hnot => hnot (ih m hm)
          have hpivot :
              selectedBlock L hL G hbad
                  (used L hL G hbad s) 0 =
                baseEnum L hL s := by
            simp [selectedBlock, nextBase, hfind]
          rw [← hpivot]
          simpa [used] using selectedBlock_mem_advance L hL G hbad
            (used L hL G hbad s) 0

theorem base_eventually_used (n : ℕ) :
    ∃ s, baseEnum L hL n ∈ used L hL G hbad s :=
  ⟨n + 1, base_prefix_used L hL G hbad (n + 1) n (by omega)⟩

theorem mem_used_exists_block {s : ℕ} {x : α}
    (hx : x ∈ used L hL G hbad s) :
    ∃ r < s, ∃ i : Fin (W + 1),
      selectedBlock L hL G hbad (used L hL G hbad r) i = x := by
  induction s with
  | zero =>
      simp [used] at hx
  | succ s ih =>
      rw [used, advance, Finset.mem_union, Finset.mem_image] at hx
      rcases hx with hxold | ⟨i, _, hi⟩
      · obtain ⟨r, hrs, i, hi⟩ := ih hxold
        exact ⟨r, by omega, i, hi⟩
      · exact ⟨s, by omega, i, hi⟩

theorem badPresentation_presents :
    GenLimit.Generic.Presents (badPresentation hW L hL G hbad) L := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    exact badPresentation_mem hW L hL G hbad t
  · intro x hx
    rw [← infiniteEnumeration_presents L hL] at hx
    obtain ⟨n, rfl⟩ := hx
    have hs := (base_eventually_used L hL G hbad n).choose_spec
    obtain ⟨r, _, i, hi⟩ :=
      mem_used_exists_block L hL G hbad hs
    refine ⟨r * (W + 1) + i, ?_⟩
    have hi_lt : (i : ℕ) < W + 1 := i.isLt
    simp only [badPresentation]
    have hdiv :
        (r * (W + 1) + (i : ℕ)) / (W + 1) = r := by
      rw [show r * (W + 1) + (i : ℕ) =
        (W + 1) * r + (i : ℕ) by
          simp [Nat.mul_comm]]
      rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi_lt]
      simp
    have hmod :
        (r * (W + 1) + (i : ℕ)) % (W + 1) = i := by
      rw [show r * (W + 1) + (i : ℕ) =
        (i : ℕ) + (W + 1) * r by
          simp [Nat.mul_comm, Nat.add_comm]]
      rw [Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hi_lt]
    simp only [hdiv]
    simpa [hmod] using hi

theorem bad_window_occurs (s : ℕ) :
    windowAt (badPresentation hW L hL G hbad)
      (badPresentation_injective hW L hL G hbad)
      (s * (W + 1) + 1) W =
        badWindow L G hbad
          (insert (nextBase L hL (used L hL G hbad s))
            (used L hL G hbad s)) := by
  apply Subtype.ext
  funext i
  simp only [windowAt, badPresentation]
  have hi_lt : 1 + (i : ℕ) < W + 1 := by omega
  have hdiv :
      (s * (W + 1) + 1 + (i : ℕ)) / (W + 1) = s := by
    rw [show s * (W + 1) + 1 + (i : ℕ) =
      (W + 1) * s + (1 + (i : ℕ)) by
        simp [Nat.mul_comm, Nat.add_assoc]]
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi_lt]
    simp
  have hmod :
      (s * (W + 1) + 1 + (i : ℕ)) % (W + 1) = 1 + (i : ℕ) := by
    rw [show s * (W + 1) + 1 + (i : ℕ) =
      (1 + (i : ℕ)) + (W + 1) * s by
        simp [Nat.mul_comm, Nat.add_comm, Nat.add_assoc]]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi_lt]
  simp only [hdiv]
  rw [show (⟨(s * (W + 1) + 1 + (i : ℕ)) % (W + 1),
    Nat.mod_lt _ (by omega)⟩ : Fin (W + 1)) = i.succ by
      apply Fin.ext
      change
        (s * (W + 1) + 1 + (i : ℕ)) % (W + 1) =
          (i : ℕ) + 1
      rw [hmod]
      omega]
  exact selectedBlock_succ L hL G hbad _ i

theorem badWindows_force_failure
    (hW : 0 < W) (hL : L.Infinite)
    (hbad : BadWindowsOutsideFinite L G) :
    ¬ IsRepetitionFreeWindowGeneratorOn G L := by
  intro hsuccess
  obtain ⟨T, hT⟩ := hsuccess
    (badPresentation hW L hL G hbad)
    (badPresentation_injective hW L hL G hbad)
    (badPresentation_presents hW L hL G hbad)
  let s := T
  have hsafe := hT (s * (W + 1) + 1) (by
    exact (Nat.le_mul_of_pos_right T (by omega)).trans
      (Nat.le_add_right (T * (W + 1)) 1))
  rw [bad_window_occurs hW L hL G hbad s] at hsafe
  exact badWindow_bad L G hbad _ hsafe

end Adversary

/-- Exact finite-exception conclusion of source Lemma 4.11. -/
theorem lemma_4_11_finite_exception
    [Countable α] {W : ℕ} (hW : 0 < W)
    {L : Set α} (hL : L.Infinite)
    {G : WindowSetGenerator α W}
    (hG : IsRepetitionFreeWindowGeneratorOn G L) :
    ∃ B : Finset α, (B : Set α) ⊆ L ∧
      ∀ w : DistinctWindow α W,
        (∀ i, w.1 i ∈ L ∧ w.1 i ∉ B) →
          G w ⊆ L := by
  classical
  by_contra h
  push_neg at h
  have hbad : BadWindowsOutsideFinite L G := by
    intro F
    by_cases hFL : (F : Set α) ⊆ L
    · exact h F hFL
    · let F' := F.filter fun x => x ∈ L
      obtain ⟨w, hw, hGbad⟩ := h F' (by
        intro x hx
        exact (Finset.mem_filter.mp (by simpa [F'] using hx)).2)
      refine ⟨w, ?_, hGbad⟩
      intro i
      refine ⟨(hw i).1, ?_⟩
      intro hiF
      exact (hw i).2 (by simp [F', hiF, (hw i).1])
  exact badWindows_force_failure (L := L) (G := G) hW hL hbad hG

end GenLimit.BoundedMemory
