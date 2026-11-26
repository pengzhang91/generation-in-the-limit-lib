import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.TargetAncestor

/-! A static ranked forest for the finite-rank generation theorems.
For each child, inspect the earlier higher-rank supersets. Retain a
candidate when it is contained in every earlier candidate, and use the
last such index. This specifies the inclusion and index priorities even
when two candidates are incomparable. The forest uses no observations.
A finite isolating sample at the target's CB level then suffices to put
every sufficiently late consistent sublanguage below the target. -/
namespace GenLimit.KleinbergWei.Banach.StaticForest
open Set TowerTopology DensityMeasures DensityMeasures.FiniteRankParent
open scoped Classical
noncomputable section
variable {C : LanguageFamily} {R : ℕ} (hr : FiniteRankAtMost (FamilySpace C) R)

private def index (L : FamilyPoint C) := Nat.find L.property

private theorem names (L : FamilyPoint C) : C (index L) = L.val := Nat.find_spec L.property

private def candidate (L : FamilyPoint C) (i : ℕ) : Prop :=
  L.val ⊆ C i ∧ levelOf hr L < levelOf hr (familyPoint C i)

private def parents (L : FamilyPoint C) : Finset ℕ :=
  (Finset.range (index L)).filter fun i => candidate hr L i ∧ ∀ j < i, candidate hr L j → C i ⊆ C j

private theorem in_parents {L : FamilyPoint C} {i : ℕ} : i ∈ parents hr L ↔
    i < index L ∧ candidate hr L i ∧ ∀ j < i, candidate hr L j → C i ⊆ C j := by
  simp [parents]

/-- A root is its own parent. Vertices represent languages, including
when the family indexing lists the same language more than once. -/
def parent (L : FamilyPoint C) : FamilyPoint C :=
  if h : (parents hr L).Nonempty then familyPoint C ((parents hr L).max' h) else L

theorem sub_parent (L : FamilyPoint C) : L.val ⊆ (parent hr L).val := by
  unfold parent; split
  next h => exact ((in_parents hr).mp (Finset.max'_mem _ h)).2.1.1
  next => exact Subset.rfl

theorem parent_rank {L : FamilyPoint C} (h : parent hr L ≠ L) :
    levelOf hr L < levelOf hr (parent hr L) := by
  by_cases ne : (parents hr L).Nonempty
  · rw [parent,dif_pos ne]; exact ((in_parents hr).mp (Finset.max'_mem _ ne)).2.1.2
  · exact (h (dif_neg ne)).elim

/-- A stable target is an eligible parent of every consistent proper
sublanguage of lower rank. Later retained candidates refine that target. -/
private theorem parent_below {s : ℕ → ℕ} {t z : ℕ} {L : FamilyPoint C}
    (strict : StrictCritical C s (t+1) z) (remains : RemainingAt C s t L)
    (proper : L.val ⊂ C z) (rank : levelOf hr L < levelOf hr (familyPoint C z)) :
    (parent hr L).val ⊆ C z ∧ levelOf hr L < levelOf hr (parent hr L) := by
  have lt : z < index L := by
    rcases lt_trichotomy (index L) z with earlier | eq | later
    · have consistent : Consistent C s (t+1) (index L) := by
        change (↑(sample s (t+1)) : Set ℕ) ⊆ C (index L)
        rw [names L]; exact remains
      have bad := (strict.2 _ earlier consistent).le
      rw [names L] at bad; exact (proper.not_ge bad).elim
    · exact (proper.ne (by rw [←names L,eq])).elim
    · exact later
  have eligible : candidate hr L z := ⟨proper.le,rank⟩
  have hz : z ∈ parents hr L := (in_parents hr).mpr ⟨lt,eligible,fun j hj cand =>
    (strict.2 j hj (remains.trans cand.1)).le⟩
  have hn : (parents hr L).Nonempty := ⟨z,hz⟩
  let j := (parents hr L).max' hn
  have picked := (in_parents hr).mp (Finset.max'_mem _ hn)
  have chosen : parent hr L = familyPoint C j := dif_pos hn
  rw [chosen]
  refine ⟨?_,picked.2.1.2⟩
  rcases (Finset.le_max' _ z hz).eq_or_lt with e | later
  · change C j ⊆ C z; rw [show j=z from e.symm]
  · exact picked.2.2 z later eligible

/-- The second vertex is on the first vertex's path to its root. -/
def Reaches (L K : FamilyPoint C) := ∃ n : ℕ, (parent hr)^[n] L = K

theorem refl (L : FamilyPoint C) : Reaches hr L L := ⟨0,rfl⟩

theorem trans {L J K : FamilyPoint C} (h : Reaches hr L J) (g : Reaches hr J K) : Reaches hr L K := by
  obtain ⟨a,rfl⟩ := h; obtain ⟨b,rfl⟩ := g
  exact ⟨b+a,Function.iterate_add_apply ..⟩

theorem subset_of_reaches {L K : FamilyPoint C} (h : Reaches hr L K) : L.val ⊆ K.val := by
  obtain ⟨n,rfl⟩ := h
  induction n with
  | zero => exact Subset.rfl
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.trans (sub_parent hr _)

/-- Lemma 4.12's eventual ancestry, uniformly over all remaining
sublanguages, using one fixed forest throughout the run. -/
theorem eventual_ancestry {s : ℕ → ℕ} {z : ℕ} (pres : Presents s (C z)) (first : FirstOccurrence C z) :
    ∃ T, ∀ t ≥ T, ∀ L : FamilyPoint C, RemainingAt C s t L → L.val ⊆ C z →
      Reaches hr L (familyPoint C z) := by
  obtain ⟨T₁,critical⟩ := lemma_3_3 pres first
  obtain ⟨T₂,purged⟩ := claim_6_7_eventual_purge hr pres
  refine ⟨max T₁ T₂,?_⟩
  intro t ht L rem sub
  let K := familyPoint C z
  have climb (n : ℕ) (L : FamilyPoint C) (measure : R-levelOf hr L=n)
      (rem : RemainingAt C s t L) (sub : L.val ⊆ C z) : Reaches hr L K := by
    induction n using Nat.strong_induction_on generalizing L with
    | h n ih =>
      by_cases eq : L.val=C z
      · have same : L=K := Subtype.ext eq; exact same ▸ refl hr _
      have proper : L.val ⊂ C z := lt_of_le_of_ne sub eq
      have rank : levelOf hr L < levelOf hr K := lt_of_not_ge fun bad =>
        purged t (by omega) L proper bad rem
      obtain ⟨below,rise⟩ := parent_below hr (critical (t+1) (by omega)) rem proper rank
      have top := levelOf_lt hr (parent hr L)
      obtain ⟨k,hk⟩ := ih (R-levelOf hr (parent hr L)) (by omega) _ rfl (rem.trans (sub_parent hr L)) below
      exact ⟨k+1,by rwa [Function.iterate_succ_apply]⟩
  exact climb _ L rfl rem sub

/-- A reached vertex appears among the first R vertices on the path,
even if a witness traversed the self-loop at a root. -/
theorem bounded_path {L K : FamilyPoint C} (h : Reaches hr L K) :
    ∃ m < R, (parent hr)^[m] L = K := by
  obtain ⟨n,rfl⟩ := h
  have short (k : ℕ) : ∃ m, m + levelOf hr L ≤ levelOf hr ((parent hr)^[k] L) ∧
      (parent hr)^[m] L = (parent hr)^[k] L := by
    induction k with
    | zero => exact ⟨0,by simp,rfl⟩
    | succ k ih =>
      obtain ⟨m,lb,eq⟩ := ih
      rw [Function.iterate_succ_apply']
      by_cases root : parent hr ((parent hr)^[k] L) = (parent hr)^[k] L
      · exact ⟨m,root.symm ▸ lb,eq.trans root.symm⟩
      · have rise := parent_rank hr root
        exact ⟨m+1,by omega,by rw [Function.iterate_succ_apply',eq]⟩
  obtain ⟨m,lb,eq⟩ := short n
  have cap := levelOf_lt hr ((parent hr)^[n] L)
  exact ⟨m,by omega,eq⟩

/-- The first common ancestor found when climbing from the old hypothesis.
For disconnected trees the new hypothesis initializes a fresh path. -/
def pullback (old new : FamilyPoint C) : FamilyPoint C :=
  if h : ∃ n : ℕ, Reaches hr new ((parent hr)^[n] old)
  then (parent hr)^[Nat.find h] old else new

theorem pullback_spec {old new K : FamilyPoint C} (a : Reaches hr old K) (b : Reaches hr new K) :
    Reaches hr old (pullback hr old new) ∧ Reaches hr new (pullback hr old new) ∧
      Reaches hr (pullback hr old new) K := by
  obtain ⟨m,rfl⟩ := a
  have ex : ∃ n : ℕ, Reaches hr new ((parent hr)^[n] old) := ⟨m,b⟩
  rw [pullback,dif_pos ex]
  have small := Nat.find_min' ex b
  refine ⟨⟨Nat.find ex,rfl⟩,Nat.find_spec ex,m-Nat.find ex,?_⟩
  rw [←Function.iterate_add_apply,Nat.sub_add_cancel small]

/-- The actual finite-observation index selector of 4.8 eventually
produces descendants of the target. -/
theorem guesses_reach {s : ℕ → ℕ} {z : ℕ} (pres : Presents s (C z)) :
    ∃ T, ∀ t ≥ T, Reaches hr (familyPoint C (guessIndex C s (t+1))) (familyPoint C z) ∧
      s t ∈ C (guessIndex C s (t+1)) := by
  obtain ⟨j,first,same⟩ := exists_first_occurrence C z
  have eq : familyPoint C j=familyPoint C z := Subtype.ext same
  have pres' : Presents s (C j) := same ▸ pres
  obtain ⟨T,all⟩ := eventual_ancestry hr pres' first
  obtain ⟨U,crit⟩ := lemma_3_3 pres' first
  refine ⟨max T (max j U),?_⟩
  intro t late
  have critical := crit t (by omega)
  have cur := mem_language_of_mem_sample_of_presents pres' (value_mem_sample (Nat.lt_succ_self t))
  have hrem := identifiedPointAt_remaining_of_stable_target (by omega : j ≤ t) critical cur
  have sub := (selectIndex_spec (by omega : j ≤ t) critical cur).2.2
  exact ⟨eq ▸ all t (by omega) _ hrem sub, hrem (value_mem_sample (Nat.lt_succ_self t))⟩

end
end GenLimit.KleinbergWei.Banach.StaticForest
