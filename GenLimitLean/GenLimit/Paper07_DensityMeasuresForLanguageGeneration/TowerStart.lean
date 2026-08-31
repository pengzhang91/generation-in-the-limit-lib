import GenLimit.Support.KleinbergWei.TowerTopology.PerfectConverse

/-!
# #07 Starting a perfect tower at a prescribed sublanguage

Printed Claim 6.6 omits a necessary nonemptiness condition: a perfect tower
cannot start at the empty language because its first stage must fix a string.
The corrected theorem assumes the prescribed strict sublanguage is nonempty;
this is automatic under the paper's standing infinite-language convention.
-/

namespace GenLimit.KleinbergWei.DensityMeasures

open TowerTopology

/-- Prepend J to a tail of an existing tower. -/
def prependTower
    {X : Set Language} (J : Point X)
    (tower : ℕ → Point X) (N : ℕ) : ℕ → Point X
  | 0 => J
  | n + 1 => tower (N + n)

@[simp] theorem prependTower_zero
    {X : Set Language} (J : Point X)
    (tower : ℕ → Point X) (N : ℕ) :
    prependTower J tower N 0 = J :=
  rfl

@[simp] theorem prependTower_succ
    {X : Set Language} (J : Point X)
    (tower : ℕ → Point X) (N n : ℕ) :
    prependTower J tower N (n + 1) = tower (N + n) :=
  rfl

theorem perfectTower_first_stage_nonempty
    {X : Set Language} {tower : ℕ → Point X} {terminal : Point X}
    (h : PerfectTower X tower terminal) :
    (tower 0).1.Nonempty := by
  obtain ⟨u, _huK, hfix⟩ := h.stage_fixes 0
  exact ⟨u, hfix.1 0 le_rfl⟩

/-- The empty-language exception in printed Claim 6.6 is genuine. -/
theorem no_perfectTower_starting_at_empty
    {X : Set Language} {tower : ℕ → Point X} {terminal : Point X}
    (hzero : (tower 0).1 = ∅) :
    ¬PerfectTower X tower terminal := by
  intro h
  obtain ⟨u, hu⟩ := perfectTower_first_stage_nonempty h
  rw [hzero] at hu
  exact hu

/-- Corrected Claim 6.6. -/
theorem claim_6_6
    {X : Set Language} {tower : ℕ → Point X} {terminal J : Point X}
    (htower : PerfectTower X tower terminal)
    (hJ : J.1 ⊂ terminal.1)
    (hJnonempty : J.1.Nonempty) :
    ∃ newTower : ℕ → Point X,
      newTower 0 = J ∧ PerfectTower X newTower terminal := by
  classical
  obtain ⟨inside, hinsideJ⟩ := hJnonempty
  have hinsideK : inside ∈ terminal.1 := hJ.le hinsideJ
  obtain ⟨insideStage, hinsideFix⟩ := htower.complete inside hinsideK
  obtain ⟨outside, houtsideK, houtsideJ⟩ := Set.exists_of_ssubset hJ
  obtain ⟨outsideStage, houtsideFix⟩ :=
    htower.complete outside houtsideK
  let N := max insideStage outsideStage
  let newTower := prependTower J tower N
  refine ⟨newTower, rfl, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero => simpa [newTower] using hJ
    | succ n => simpa [newTower] using htower.proper (N + n)
  · intro n
    cases n with
    | zero =>
        refine ⟨inside, hinsideK, ?_⟩
        refine ⟨?_, Or.inl rfl⟩
        intro m _
        cases m with
        | zero => simpa [newTower] using hinsideJ
        | succ m =>
            apply hinsideFix.1 (N + m)
            exact (Nat.le_max_left _ _).trans (Nat.le_add_right N m)
    | succ n =>
        cases n with
        | zero =>
            refine ⟨outside, houtsideK, ?_⟩
            refine ⟨?_, Or.inr ?_⟩
            · intro m hm
              cases m with
              | zero => omega
              | succ m =>
                  apply houtsideFix.1 (N + m)
                  exact (Nat.le_max_right _ _).trans (Nat.le_add_right N m)
            · simpa [newTower] using houtsideJ
        | succ n =>
            obtain ⟨u, huK, hfix⟩ := htower.stage_fixes (N + n + 1)
            refine ⟨u, huK, ?_⟩
            refine ⟨?_, Or.inr ?_⟩
            · intro m hm
              cases m with
              | zero => omega
              | succ m =>
                  apply hfix.1 (N + m)
                  omega
            · have hindex_ne : N + n + 1 ≠ 0 := by omega
              have hprev : u ∉ (tower (N + n + 1 - 1)).1 := by
                rcases hfix.2 with hzero | hnot
                · exact (hindex_ne hzero).elim
                · exact hnot
              simpa [newTower] using hprev
  · intro u huK
    apply exists_fixesAt_of_eventually
    obtain ⟨stage, hfix⟩ := htower.complete u huK
    refine ⟨stage + 1, ?_⟩
    intro n hn
    cases n with
    | zero => omega
    | succ n =>
        apply hfix.1 (N + n)
        omega

end GenLimit.KleinbergWei.DensityMeasures
