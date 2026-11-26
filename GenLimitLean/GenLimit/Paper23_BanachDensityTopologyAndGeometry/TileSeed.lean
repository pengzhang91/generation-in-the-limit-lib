import GenLimit.Paper23_BanachDensityTopologyAndGeometry.IntervalGenerator

/-! The first visit to a finite cell fixes its forest seed. All but finitely
many cells start after the selector's guesses reach the true target. -/
namespace GenLimit.KleinbergWei.Banach.TileSeed
open Set TowerTopology DensityMeasures DensityMeasures.FiniteRankParent
open scoped Classical
noncomputable section
variable {K : Type*} (cellOf : ℕ → K) (C : LanguageFamily)

private def visit (s : ℕ → ℕ) (k : K) := if h : ∃ t, cellOf (s t)=k then Nat.find h else 0

private theorem first {s : ℕ → ℕ} {k t} (h : cellOf (s t)=k) :
    cellOf (s (visit cellOf s k))=k ∧ visit cellOf s k ≤ t ∧
      ∀ a < visit cellOf s k, cellOf (s a) ≠ k := by
  have ex : ∃ t, cellOf (s t)=k := ⟨_,h⟩
  rw [visit,dif_pos ex]
  exact ⟨Nat.find_spec ex,Nat.find_min' ex h,fun a ha => Nat.find_min ex ha⟩

def seed (s : ℕ → ℕ) (k : K) :=
  familyPoint C (indexHistoryRule C (textPrefix s (visit cellOf s k+1)))

def atHistory (h : List ℕ) (x : ℕ) := seed cellOf C
    (Generic.historyThenFallback (h++[x]) 0) (cellOf x)

theorem agrees (s : ℕ → ℕ) (t : ℕ) :
    atHistory cellOf C (textPrefix s t) (s t) = seed cellOf C s (cellOf (s t)) := by
  let k := cellOf (s t)
  let r := Generic.historyThenFallback (textPrefix s (t+1)) 0
  have eq (a) (ha : a ≤ t) : r a = s a := by
    simp [r,Generic.historyThenFallback,textPrefix,show a < t+1 by omega]
  obtain ⟨ha,al,am⟩ := first cellOf (s := s) (k := k) (t := t) rfl
  obtain ⟨hb,bl,bm⟩ := first cellOf (s := r) (k := k) (t := t) (by rw [eq t le_rfl])
  have same : visit cellOf r k = visit cellOf s k := by
    apply le_antisymm
    · exact le_of_not_gt fun lt => bm _ lt (by rwa [eq _ al])
    · exact le_of_not_gt fun lt => am _ lt (by rwa [←eq _ bl])
  have pre : textPrefix r (visit cellOf s k+1) = textPrefix s (visit cellOf s k+1) := by
    unfold textPrefix
    apply List.map_congr_left
    intro a ha; exact eq a ((Nat.le_of_lt_succ (List.mem_range.mp ha)).trans al)
  unfold atHistory
  rw [←textPrefix_succ]
  change familyPoint C (indexHistoryRule C (textPrefix r (visit cellOf r k+1))) = _
  rw [same,pre]; rfl

theorem eventually_reaches {R : ℕ} (rank : FiniteRankAtMost (FamilySpace C) R)
    {z s} (pres : Presents s (C z)) :
    ∃ bad : Finset K, ∀ t, cellOf (s t) ∉ bad →
      StaticForest.Reaches rank (seed cellOf C s (cellOf (s t))) (familyPoint C z) := by
  obtain ⟨T,good⟩ := StaticForest.guesses_reach rank pres
  let bad := (Finset.range T).image (fun t => cellOf (s t))
  refine ⟨bad,fun t outside => ?_⟩
  let k := cellOf (s t)
  have late : T ≤ visit cellOf s k := by
    by_contra! low
    exact outside (Finset.mem_image.mpr ⟨_,Finset.mem_range.mpr low,(first cellOf (s := s) (t := t) rfl).1⟩)
  simpa [seed,k,indexHistoryRule_prefix] using (good _ late).1

end
end GenLimit.KleinbergWei.Banach.TileSeed
