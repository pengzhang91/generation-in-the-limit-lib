import GenLimit.Support.KleinbergWei.TowerTopology.Converse

/-!
# Extracting a source-literal perfect tower

The adaptive construction retains prior finite constraints, adds one omitted
terminal element, and advances a presentation. This supplies the paper's
nonredundancy clause as well as convergence.
-/

namespace GenLimit.KleinbergWei.TowerTopology

/-- Data carried by one adaptive stage. -/
structure AdaptiveStage
    (X : Set Language) (terminal : Point X) where
  fixed : Finset ℕ
  fixed_subset_terminal : (↑fixed : Set ℕ) ⊆ terminal.1
  point : Point X
  point_ne_terminal : point ≠ terminal
  point_in_neighborhood :
    point ∈ basicNeighborhood X terminal fixed
  missing : ℕ
  missing_mem_terminal : missing ∈ terminal.1
  missing_not_mem_point : missing ∉ point.1

/-- Choose a proper approximant containing F and one terminal point it omits. -/
noncomputable def adaptiveStageOf
    {X : Set Language} (terminal : Point X)
    (hterminal : BasisLimitPoint terminal)
    (F : Finset ℕ) (hF : (↑F : Set ℕ) ⊆ terminal.1) :
    AdaptiveStage X terminal := by
  classical
  let point : Point X := Classical.choose (hterminal F hF)
  have hpoint :
      point ≠ terminal ∧ point ∈ basicNeighborhood X terminal F :=
    Classical.choose_spec (hterminal F hF)
  have hmissing : ∃ u, u ∈ terminal.1 ∧ u ∉ point.1 := by
    by_contra h
    push_neg at h
    have hterminal_point : terminal.1 ⊆ point.1 := fun u hu => h u hu
    have heq : point.1 = terminal.1 :=
      Set.Subset.antisymm hpoint.2.2 hterminal_point
    exact hpoint.1 (Subtype.ext heq)
  let missing := Classical.choose hmissing
  have hmissing_spec : missing ∈ terminal.1 ∧ missing ∉ point.1 :=
    Classical.choose_spec hmissing
  exact
    { fixed := F
      fixed_subset_terminal := hF
      point := point
      point_ne_terminal := hpoint.1
      point_in_neighborhood := hpoint.2
      missing := missing
      missing_mem_terminal := hmissing_spec.1
      missing_not_mem_point := hmissing_spec.2 }

@[simp] theorem adaptiveStageOf_fixed
    {X : Set Language} (terminal : Point X)
    (hterminal : BasisLimitPoint terminal)
    (F : Finset ℕ) (hF : (↑F : Set ℕ) ⊆ terminal.1) :
    (adaptiveStageOf terminal hterminal F hF).fixed = F := by
  simp [adaptiveStageOf]

/-- Retain old constraints, add the omitted point, and advance the terminal
presentation. -/
def nextFixed
    {X : Set Language} {terminal : Point X}
    (enumeration : ℕ → ℕ) (n : ℕ)
    (stage : AdaptiveStage X terminal) : Finset ℕ :=
  insert stage.missing (insert (enumeration (n + 1)) stage.fixed)

theorem fixed_subset_nextFixed
    {X : Set Language} {terminal : Point X}
    (enumeration : ℕ → ℕ) (n : ℕ)
    (stage : AdaptiveStage X terminal) :
    stage.fixed ⊆ nextFixed enumeration n stage := by
  intro u hu
  simp [nextFixed, hu]

theorem missing_mem_nextFixed
    {X : Set Language} {terminal : Point X}
    (enumeration : ℕ → ℕ) (n : ℕ)
    (stage : AdaptiveStage X terminal) :
    stage.missing ∈ nextFixed enumeration n stage := by
  simp [nextFixed]

noncomputable def advance
    {X : Set Language} (terminal : Point X)
    (hterminal : BasisLimitPoint terminal)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1)
    (n : ℕ) (stage : AdaptiveStage X terminal) :
    AdaptiveStage X terminal :=
  adaptiveStageOf terminal hterminal (nextFixed enumeration n stage) (by
    intro u hu
    simp only [nextFixed, Finset.mem_coe, Finset.mem_insert] at hu
    rcases hu with rfl | rfl | hu
    · exact stage.missing_mem_terminal
    · rw [← hP]
      exact ⟨n + 1, rfl⟩
    · exact stage.fixed_subset_terminal hu)

@[simp] theorem advance_fixed
    {X : Set Language} (terminal : Point X)
    (hterminal : BasisLimitPoint terminal)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1)
    (n : ℕ) (stage : AdaptiveStage X terminal) :
    (advance terminal hterminal enumeration hP n stage).fixed =
      nextFixed enumeration n stage := by
  simp [advance]

/-- Adaptive stages; stage zero contains the first presented point. -/
noncomputable def adaptiveStages
    {X : Set Language} (terminal : Point X)
    (hterminal : BasisLimitPoint terminal)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1) :
    ℕ → AdaptiveStage X terminal
  | 0 =>
      adaptiveStageOf terminal hterminal {enumeration 0} (by
        intro u hu
        simp only [Finset.mem_coe, Finset.mem_singleton] at hu
        subst u
        rw [← hP]
        exact ⟨0, rfl⟩)
  | n + 1 =>
      advance terminal hterminal enumeration hP n
        (adaptiveStages terminal hterminal enumeration hP n)

@[simp] theorem adaptiveStages_succ_fixed
    {X : Set Language} (terminal : Point X)
    (hterminal : BasisLimitPoint terminal)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1)
    (n : ℕ) :
    (adaptiveStages terminal hterminal enumeration hP (n + 1)).fixed =
      nextFixed enumeration n
        (adaptiveStages terminal hterminal enumeration hP n) := by
  simp [adaptiveStages]

theorem adaptiveStages_fixed_mono_succ
    {X : Set Language} (terminal : Point X)
    (hterminal : BasisLimitPoint terminal)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1)
    (n : ℕ) :
    (adaptiveStages terminal hterminal enumeration hP n).fixed ⊆
      (adaptiveStages terminal hterminal enumeration hP (n + 1)).fixed := by
  rw [adaptiveStages_succ_fixed]
  exact fixed_subset_nextFixed enumeration n
    (adaptiveStages terminal hterminal enumeration hP n)

theorem adaptiveStages_fixed_mono
    {X : Set Language} (terminal : Point X)
    (hterminal : BasisLimitPoint terminal)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1)
    {i j : ℕ} (hij : i ≤ j) :
    (adaptiveStages terminal hterminal enumeration hP i).fixed ⊆
      (adaptiveStages terminal hterminal enumeration hP j).fixed := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => simp
  | succ d ih =>
      exact ih.trans (by
        simpa [Nat.add_assoc] using
          adaptiveStages_fixed_mono_succ terminal hterminal
            enumeration hP (i + d))

/-- Point sequence extracted from the adaptive states. -/
noncomputable def adaptiveTower
    {X : Set Language} (terminal : Point X)
    (hterminal : BasisLimitPoint terminal)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1) :
    ℕ → Point X :=
  fun n => (adaptiveStages terminal hterminal enumeration hP n).point

theorem fixed_mem_adaptiveTower
    {X : Set Language} (terminal : Point X)
    (hterminal : BasisLimitPoint terminal)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1)
    {n u : ℕ}
    (hu : u ∈ (adaptiveStages terminal hterminal enumeration hP n).fixed) :
    u ∈ (adaptiveTower terminal hterminal enumeration hP n).1 :=
  (adaptiveStages terminal hterminal enumeration hP n).point_in_neighborhood.1 hu

theorem enumeration_mem_fixed
    {X : Set Language} (terminal : Point X)
    (hterminal : BasisLimitPoint terminal)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1)
    (n : ℕ) :
    enumeration n ∈
      (adaptiveStages terminal hterminal enumeration hP n).fixed := by
  cases n with
  | zero => simp [adaptiveStages, adaptiveStageOf]
  | succ n =>
      rw [adaptiveStages_succ_fixed]
      simp [nextFixed]

theorem adaptiveTower_eventually_contains
    {X : Set Language} (terminal : Point X)
    (hterminal : BasisLimitPoint terminal)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1)
    (u : ℕ) (hu : u ∈ terminal.1) :
    ∃ N, ∀ n, N ≤ n →
      u ∈ (adaptiveTower terminal hterminal enumeration hP n).1 := by
  rw [← hP] at hu
  obtain ⟨N, rfl⟩ := hu
  refine ⟨N, ?_⟩
  intro n hNn
  apply fixed_mem_adaptiveTower terminal hterminal enumeration hP
  exact adaptiveStages_fixed_mono terminal hterminal enumeration hP hNn
    (enumeration_mem_fixed terminal hterminal enumeration hP N)

theorem adaptiveTower_proper
    {X : Set Language} (terminal : Point X)
    (hterminal : BasisLimitPoint terminal)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1)
    (n : ℕ) :
    (adaptiveTower terminal hterminal enumeration hP n).1 ⊂ terminal.1 := by
  let stage := adaptiveStages terminal hterminal enumeration hP n
  exact Set.ssubset_iff_subset_ne.mpr
    ⟨stage.point_in_neighborhood.2, fun heq =>
      stage.point_ne_terminal (Subtype.ext heq)⟩

/-- Any eventually permanent occurrence has a first permanent stage. -/
theorem exists_fixesAt_of_eventually
    {tower : ℕ → Language} {u : ℕ}
    (h : ∃ N, ∀ n, N ≤ n → u ∈ tower n) :
    ∃ N, FixesAt tower N u := by
  classical
  let first : ℕ := Nat.find h
  have hfirst : ∀ n, first ≤ n → u ∈ tower n := Nat.find_spec h
  refine ⟨first, hfirst, ?_⟩
  by_cases hzero : first = 0
  · exact Or.inl hzero
  · refine Or.inr ?_
    by_contra hprev
    have hprev_all : ∀ n, first - 1 ≤ n → u ∈ tower n := by
      intro n hn
      by_cases hnf : n < first
      · have hn_eq : n = first - 1 := by omega
        simpa [hn_eq] using hprev
      · exact hfirst n (Nat.le_of_not_gt hnf)
    have hminimal := Nat.find_min' h hprev_all
    omega

/-- Exact converse of Paper #07 Claim 6.1 and Paper #23 Claim 3.6. -/
theorem perfectTower_of_basisLimitPoint
    {X : Set Language} {terminal : Point X}
    (hterminal : BasisLimitPoint terminal)
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1) :
    PerfectTower X
      (adaptiveTower terminal hterminal enumeration hP) terminal := by
  refine ⟨adaptiveTower_proper terminal hterminal enumeration hP, ?_, ?_⟩
  · intro n
    cases n with
    | zero =>
        refine ⟨enumeration 0, ?_, ?_⟩
        · rw [← hP]
          exact ⟨0, rfl⟩
        · refine ⟨?_, Or.inl rfl⟩
          intro m _
          apply fixed_mem_adaptiveTower terminal hterminal enumeration hP
          exact adaptiveStages_fixed_mono terminal hterminal enumeration hP
            (Nat.zero_le m) (by simp [adaptiveStages, adaptiveStageOf])
    | succ n =>
        let stage := adaptiveStages terminal hterminal enumeration hP n
        refine ⟨stage.missing, stage.missing_mem_terminal, ?_⟩
        refine ⟨?_, Or.inr ?_⟩
        · intro m hm
          apply fixed_mem_adaptiveTower terminal hterminal enumeration hP
          apply adaptiveStages_fixed_mono terminal hterminal enumeration hP hm
          rw [adaptiveStages_succ_fixed]
          exact missing_mem_nextFixed enumeration n stage
        · simpa [adaptiveTower, stage] using stage.missing_not_mem_point
  · intro u hu
    apply exists_fixesAt_of_eventually
    exact adaptiveTower_eventually_contains terminal hterminal enumeration hP u hu

theorem basisLimitPoint_iff_exists_perfectTower
    {X : Set Language} {terminal : Point X}
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1) :
    BasisLimitPoint terminal ↔
      ∃ tower : ℕ → Point X, PerfectTower X tower terminal := by
  constructor
  · intro hterminal
    exact ⟨adaptiveTower terminal hterminal enumeration hP,
      perfectTower_of_basisLimitPoint hterminal enumeration hP⟩
  · rintro ⟨tower, htower⟩
    exact basisLimitPoint_iff_isLimitPoint.mpr
      (limitPoint_of_perfectTower htower)

theorem isLimitPoint_iff_exists_perfectTower
    {X : Set Language} {terminal : Point X}
    (enumeration : ℕ → ℕ) (hP : Presents enumeration terminal.1) :
    IsLimitPoint terminal ↔
      ∃ tower : ℕ → Point X, PerfectTower X tower terminal := by
  rw [← basisLimitPoint_iff_isLimitPoint]
  exact basisLimitPoint_iff_exists_perfectTower enumeration hP

end GenLimit.KleinbergWei.TowerTopology
