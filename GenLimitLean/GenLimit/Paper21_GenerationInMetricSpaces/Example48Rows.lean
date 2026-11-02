import GenLimit.Paper21_GenerationInMetricSpaces.Example48Negative

/-!
# Prime-power rows for the adversary-scale obstruction in Example 4.8

The fixed observations include `g_3`, accounting for the natural exponent
zero in the optimal-set family. All selected row
points belong to the constructed source targets, as required by v2 Lemma C.2.
-/

namespace GenLimit.MetricSpaces.HilbertAxisReservoir.Example48Rows

open GenLimit.Generic

noncomputable section

def power (i k : ℕ) : ℕ := RealLineThreshold.diagonalOddPrime i ^ (k + 1)

def powers (i : ℕ) : Set ℕ := Set.range (power i)

theorem powers_infinite (i : ℕ) : (powers i).Infinite := by
  apply Set.infinite_range_of_injective
  intro k l h
  apply Nat.succ_injective
  exact Nat.pow_right_injective (Nat.le_of_lt (RealLineThreshold.diagonalOddPrime_two_lt i)) h

theorem power_ne {i j : ℕ} (hij : i ≠ j) (k l : ℕ) : power i k ≠ power j l := by
  intro h
  apply hij
  apply RealLineThreshold.diagonalOddPrime_injective
  exact (Nat.Prime.pow_inj (RealLineThreshold.diagonalOddPrime_prime i)
    (RealLineThreshold.diagonalOddPrime_prime j) h).1

theorem powers_pos {i q : ℕ} (hq : q ∈ powers i) : 0 < q := by
  obtain ⟨k, rfl⟩ := hq
  exact pow_pos (RealLineThreshold.diagonalOddPrime_prime i).pos (k + 1)

theorem powers_pow {i q n : ℕ} (hq : q ∈ powers i) (hn : 0 < n) : q ^ n ∈ powers i := by
  obtain ⟨k, rfl⟩ := hq
  have hpos : 0 < (k + 1) * n := Nat.mul_pos (Nat.succ_pos k) hn
  refine ⟨(k + 1) * n - 1, ?_⟩
  simp only [power, Nat.sub_add_cancel (by omega : 1 ≤ (k + 1) * n)]
  exact pow_mul _ _ _

def row (r ε' : ℝ) (i j : ℕ) : Hilbert2 :=
  if j % 2 = 0 then example48U r (power i (j / 2))
  else example48G ε' (2 * power i (j / 2) + 1)

theorem row_forms (r ε' : ℝ) (i j : ℕ) :
    ∃ q ∈ powers i, row r ε' i j = example48U r q ∨
      row r ε' i j = example48G ε' (2 * q + 1) := by
  refine ⟨power i (j / 2), ⟨j / 2, rfl⟩, ?_⟩
  unfold row
  split <;> simp

theorem u_mem_row (r ε' : ℝ) {i q : ℕ} (hq : q ∈ powers i) :
    example48U r q ∈ Set.range (row r ε' i) := by
  obtain ⟨k, rfl⟩ := hq
  refine ⟨2 * k, ?_⟩
  simp [row, show (2 * k) % 2 = 0 by omega, show (2 * k) / 2 = k by omega]

theorem g_mem_row (r ε' : ℝ) {i q : ℕ} (hq : q ∈ powers i) :
    example48G ε' (2 * q + 1) ∈ Set.range (row r ε' i) := by
  obtain ⟨k, rfl⟩ := hq
  refine ⟨2 * k + 1, ?_⟩
  simp [row, show (2 * k + 1) / 2 = k by omega]

def fixed (ε' : ℝ) : List Hilbert2 := [0, example48G ε' 3]

def protectedSet (r ε ε' : ℝ) (i : ℕ) : Set Hilbert2 :=
  example48USet r (powers i) ∪
    {x | ∃ q ∈ powers i, x = example48A ε (2 * q)} ∪
    example48Disturbing ε' (powers i)

def uIndices (r : ℝ) (B : Set Hilbert2) : Set ℕ := {q | 0 < q ∧ example48U r q ∈ B}

def gIndices (ε' : ℝ) (B : Set Hilbert2) : Set ℕ :=
  {q | 0 < q ∧ example48G ε' (2 * q + 1) ∈ B}

def modelTarget (r ε ε' : ℝ) (i : ℕ) (B : Set Hilbert2) : Set Hilbert2 :=
  example48Language r ε ε' (powers i ∪ uIndices r B) (powers i) (powers i ∪ gIndices ε' B)

def HasRowForm (r ε' : ℝ) (B : Set Hilbert2) : Prop :=
  ∀ x ∈ B, ∃ q, 0 < q ∧ (x = example48U r q ∨ x = example48G ε' (2 * q + 1))

theorem modelTarget_mem (r ε ε' : ℝ) (i : ℕ) (B : Set Hilbert2) :
    modelTarget r ε ε' i B ∈ example48LanguageClass r ε ε' :=
  ⟨_, _, _, (powers_infinite i).mono Set.subset_union_left, powers_infinite i,
    (powers_infinite i).mono Set.subset_union_left,
    (fun _ hq => hq.elim powers_pos (fun h => h.1)),
    (fun _ hq => powers_pos hq),
    (fun _ hq => hq.elim powers_pos (fun h => h.1)), rfl⟩

theorem modelTarget_eq (r ε ε' : ℝ) (i : ℕ) (B : Set Hilbert2) (hB : HasRowForm r ε' B) :
    modelTarget r ε ε' i B = {x | x ∈ fixed ε'} ∪ protectedSet r ε ε' i ∪ B := by
  ext x
  constructor
  · rintro (hzero | ⟨q, hq, hx⟩ | (⟨q, hq, hx⟩ | ⟨q, hq, n, hx⟩) | ⟨q, hq, hx⟩)
    · have hx0 : x = 0 := by simpa [example48Zero] using hzero
      exact Or.inl (Or.inl (by simp [fixed, hx0]))
    · rcases hq with hq | hq
      · exact Or.inl (Or.inr (Or.inl (Or.inl ⟨q, hq, hx⟩)))
      · exact Or.inr (hx.symm ▸ hq.2)
    · exact Or.inl (Or.inr (Or.inl (Or.inr ⟨q, hq, hx⟩)))
    · by_cases hn : n = 0
      · subst n
        exact Or.inl (Or.inl (by simp [fixed, hx]))
      · exact Or.inl (Or.inr (Or.inr ⟨q ^ n, powers_pow hq (Nat.pos_of_ne_zero hn), hx⟩))
    · rcases hq with hq | hq
      · exact Or.inl (Or.inr (Or.inr ⟨q, hq, hx⟩))
      · exact Or.inr (hx.symm ▸ hq.2)
  · rintro ((hf | ((hU | hA) | hG)) | hxB)
    · simp only [fixed, List.mem_cons] at hf
      rcases hf with hf | hf
      · exact Or.inl (by simpa [example48Zero] using hf)
      · exact Or.inr (Or.inr (Or.inl (Or.inr
          ⟨power i 0, ⟨0, rfl⟩, 0, by simpa using hf⟩)))
    · obtain ⟨q, hq, hx⟩ := hU
      exact Or.inr (Or.inl ⟨q, Or.inl hq, hx⟩)
    · obtain ⟨q, hq, hx⟩ := hA
      exact Or.inr (Or.inr (Or.inl (Or.inl ⟨q, hq, hx⟩)))
    · obtain ⟨q, hq, hx⟩ := hG
      exact Or.inr (Or.inr (Or.inr ⟨q, Or.inl hq, hx⟩))
    · obtain ⟨q, hqpos, hxU | hxG⟩ := hB x hxB
      · exact Or.inr (Or.inl ⟨q,
          Or.inr ⟨hqpos, show example48U r q ∈ B from hxU ▸ hxB⟩, hxU⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨q,
          Or.inr ⟨hqpos, show example48G ε' (2 * q + 1) ∈ B from hxG ▸ hxB⟩, hxG⟩))

theorem mem_protectedSet {r ε ε' : ℝ} {i : ℕ} {x : Hilbert2} :
    x ∈ protectedSet r ε ε' i ↔ ∃ q ∈ powers i,
      x = example48U r q ∨ x = example48A ε (2 * q) ∨ x = example48G ε' (2 * q + 1) := by
  constructor
  · rintro ((⟨q, hq, hx⟩ | ⟨q, hq, hx⟩) | ⟨q, hq, hx⟩)
    · exact ⟨q, hq, Or.inl hx⟩
    · exact ⟨q, hq, Or.inr (Or.inl hx)⟩
    · exact ⟨q, hq, Or.inr (Or.inr hx)⟩
  · rintro ⟨q, hq, hx | hx | hx⟩
    · exact Or.inl (Or.inl ⟨q, hq, hx⟩)
    · exact Or.inl (Or.inr ⟨q, hq, hx⟩)
    · exact Or.inr ⟨q, hq, hx⟩

theorem powers_ne {i j q q' : ℕ} (hij : i ≠ j) (hq : q ∈ powers i) (hq' : q' ∈ powers j) :
    q ≠ q' := by
  obtain ⟨k, rfl⟩ := hq
  obtain ⟨l, rfl⟩ := hq'
  exact power_ne hij k l

theorem protectedSet_disjoint {r ε ε' : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε' : 0 < ε')
    (hεr : ε ≤ r) (hε'r : ε' ≤ r) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (protectedSet r ε ε' i) (protectedSet r ε ε' j) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨q, hq, hx⟩ := mem_protectedSet.mp hx
  obtain ⟨q', hq', hy⟩ := mem_protectedSet.mp hy
  have hqq := powers_ne hij hq hq'
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
  all_goals
    have heq := hx.symm.trans hy
    simp only [example48U, example48A, example48G] at heq
    obtain ⟨hamp, hcoord⟩ := axisPoint_eq_axisPoint_of_left_ne_zero (by positivity) heq
    first | exact hqq (by omega) | omega | linarith

theorem amplitude_gap_le_dist (c d : ℝ) (i j : ℕ) :
    |c| - |d| ≤ dist (axisPoint d j) (axisPoint c i) := by
  have h := norm_sub_norm_le (axisPoint c i) (axisPoint d j)
  rw [← dist_eq_norm, dist_comm] at h
  simpa only [norm_axisPoint] using h

theorem protectedSet_row_distance {r ε ε' : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε' : 0 < ε')
    (hεr : ε ≤ r) (hε'r : ε' ≤ r) {i j : ℕ} (hij : i ≠ j)
    {x y : Hilbert2} (hx : x ∈ protectedSet r ε ε' i) (hy : y ∈ Set.range (row r ε' j)) :
    ε' ≤ dist y x := by
  obtain ⟨q, hq, hx⟩ := mem_protectedSet.mp hx
  obtain ⟨k, rfl⟩ := hy
  obtain ⟨q', hq', hy⟩ := row_forms r ε' j k
  have hqq := powers_ne hij hq hq'
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy
  · rw [hx, hy]
    have hfar := abs_amplitude_le_dist_axisPoint_of_ne (4 * r) (4 * r) (Ne.symm hqq)
    dsimp only [hilbertDistance] at hfar
    rw [abs_of_pos (by positivity : 0 < 4 * r)] at hfar
    exact (by linarith : ε' ≤ 4 * r).trans hfar
  · rw [hx, hy]
    have hfar := amplitude_gap_le_dist (4 * r) ε' q (2 * q' + 1)
    rw [abs_of_pos (by positivity : 0 < 4 * r), abs_of_pos hε'] at hfar
    exact (by linarith : ε' ≤ 4 * r - ε').trans hfar
  · rw [hx, hy]
    have hfar := amplitude_gap_le_dist (4 * r) ε q' (2 * q)
    rw [dist_comm, abs_of_pos (by positivity : 0 < 4 * r), abs_of_pos hε] at hfar
    exact (by linarith : ε' ≤ 4 * r - ε).trans hfar
  · rw [hx, hy]
    have hcoord : 2 * q ≠ 2 * q' + 1 := by omega
    have hfar := abs_amplitude_le_dist_axisPoint_of_ne ε ε' hcoord
    dsimp only [hilbertDistance] at hfar
    rw [dist_comm, abs_of_pos hε'] at hfar
    exact hfar
  · rw [hx, hy]
    have hfar := amplitude_gap_le_dist (4 * r) ε' q' (2 * q + 1)
    rw [dist_comm, abs_of_pos (by positivity : 0 < 4 * r), abs_of_pos hε'] at hfar
    exact (by linarith : ε' ≤ 4 * r - ε').trans hfar
  · rw [hx, hy]
    have hcoord : 2 * q' + 1 ≠ 2 * q + 1 := by omega
    have hfar := abs_amplitude_le_dist_axisPoint_of_ne ε' ε' hcoord
    dsimp only [hilbertDistance] at hfar
    rw [abs_of_pos hε'] at hfar
    exact hfar

theorem row_subset_protectedSet (r ε ε' : ℝ) (i : ℕ) :
    Set.range (row r ε' i) ⊆ protectedSet r ε ε' i := by
  rintro x ⟨j, rfl⟩
  obtain ⟨q, hq, hU | hG⟩ := row_forms r ε' i j
  · exact mem_protectedSet.mpr ⟨q, hq, Or.inl hU⟩
  · exact mem_protectedSet.mpr ⟨q, hq, Or.inr (Or.inr hG)⟩

theorem mem_neighborhood_of_mem {C : Set Hilbert2} {γ : ℝ} (hγ : 0 ≤ γ)
    {x : Hilbert2} (hx : x ∈ C) : x ∈ closedNeighborhood dist C γ := by
  intro η hη
  exact ⟨x, hx, by rw [dist_self]; exact lt_of_le_of_lt hγ hη⟩

theorem protectedSet_covered {r ε ε' γ : ℝ} (hε : 0 ≤ ε) (hεγ : ε ≤ γ)
    (i : ℕ) (C : Set Hilbert2) (hfixed : {x | x ∈ fixed ε'} ⊆ C)
    (hrow : Set.range (row r ε' i) ⊆ C) :
    protectedSet r ε ε' i ⊆ closedNeighborhood dist C γ := by
  intro x hx
  obtain ⟨q, hq, hU | hA | hG⟩ := mem_protectedSet.mp hx
  · rw [hU]
    exact mem_neighborhood_of_mem (hε.trans hεγ) (hrow (u_mem_row r ε' hq))
  · rw [hA]
    apply inClosedNeighborhood_mono_centers
      (show ({0} : Set Hilbert2) ⊆ C from fun y hy => by
        have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
        apply hfixed
        simp [fixed, hy0])
    rw [mem_closedNeighborhood_singleton_iff]
    simpa [example48A, abs_of_nonneg hε] using hεγ
  · rw [hG]
    exact mem_neighborhood_of_mem (hε.trans hεγ) (hrow (g_mem_row r ε' hq))

theorem modelTarget_conditions {r ε ε' γ γ' : ℝ}
    (hε : 0 ≤ ε) (hεγ : ε ≤ γ) (hγ' : 0 ≤ γ')
    (i : ℕ) (B : Set Hilbert2) (hB : HasRowForm r ε' B) :
    ({x | x ∈ fixed ε'} ∪ Set.range (row r ε' i) ∪ B) ⊆ modelTarget r ε ε' i B ∧
    modelTarget r ε ε' i B ⊆ closedNeighborhood dist
      ({x | x ∈ fixed ε'} ∪ Set.range (row r ε' i) ∪ B) γ ∧
    modelTarget r ε ε' i B ⊆ closedNeighborhood dist {x | x ∈ fixed ε'} γ' ∪
      protectedSet r ε ε' i ∪ closedNeighborhood dist B γ' := by
  rw [modelTarget_eq r ε ε' i B hB]
  refine ⟨?_, ?_, ?_⟩
  · rintro x ((hf | hr) | hb)
    · exact Or.inl (Or.inl hf)
    · exact Or.inl (Or.inr (row_subset_protectedSet r ε ε' i hr))
    · exact Or.inr hb
  · rintro x ((hf | hp) | hb)
    · exact mem_neighborhood_of_mem (hε.trans hεγ) (Or.inl (Or.inl hf))
    · exact protectedSet_covered hε hεγ i _
        (fun _ hx => Or.inl (Or.inl hx)) (fun _ hx => Or.inl (Or.inr hx)) hp
    · exact mem_neighborhood_of_mem (hε.trans hεγ) (Or.inr hb)
  · rintro x ((hf | hp) | hb)
    · exact Or.inl (Or.inl (mem_neighborhood_of_mem hγ' hf))
    · exact Or.inl (Or.inr hp)
    · exact Or.inr (mem_neighborhood_of_mem hγ' hb)

theorem all_rows_form {r ε' : ℝ} {B : Set Hilbert2}
    (hB : ∀ x ∈ B, ∃ i j, row r ε' i j = x) : HasRowForm r ε' B := by
  intro x hx
  obtain ⟨i, j, hrow⟩ := hB x hx
  obtain ⟨q, hq, hU | hG⟩ := row_forms r ε' i j
  · exact ⟨q, powers_pos hq, Or.inl (hrow.symm.trans hU)⟩
  · exact ⟨q, powers_pos hq, Or.inr (hrow.symm.trans hG)⟩

theorem rowCriterion {r ε ε' γ γ' : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hε' : 0 < ε') (hεr : ε ≤ r) (hε'r : ε' ≤ r)
    (hεγ : ε ≤ γ) (hγ' : 0 ≤ γ') (hγ'ε' : γ' < ε') :
    RowDiagonal.Criterion dist γ γ' (example48LanguageClass r ε ε')
      (fixed ε') (row r ε') (protectedSet r ε ε') := by
  constructor
  · intro cut hcut
    let B := RowDiagonal.stopped (row r ε') cut
    have hB : HasRowForm r ε' B := all_rows_form (by
      rintro x ⟨i, j, hj, hrow⟩
      exact ⟨i + 1, j, hrow⟩)
    exact ⟨modelTarget r ε ε' 0 B, modelTarget_mem r ε ε' 0 B,
      modelTarget_conditions hε.le hεγ hγ' 0 B hB⟩
  · intro n cut hcut
    let B := RowDiagonal.prior (row r ε') cut
    have hB : HasRowForm r ε' B := all_rows_form (by
      rintro x ⟨i, j, hj, hrow⟩
      exact ⟨i, j, hrow⟩)
    exact ⟨modelTarget r ε ε' (n + 1) B, modelTarget_mem r ε ε' (n + 1) B,
      modelTarget_conditions hε.le hεγ hγ' (n + 1) B hB⟩
  · intro n
    apply Set.disjoint_left.mpr
    rintro x hx (hzero | hfuture)
    · exact Set.disjoint_left.mp (protectedSet_disjoint hr hε hε' hεr hε'r
        (Nat.succ_ne_zero n)) hx hzero
    · obtain ⟨y, ⟨i, j, hi, rfl⟩, hnear⟩ := hfuture ε' hγ'ε'
      exact (not_lt_of_ge (protectedSet_row_distance hr hε hε' hεr hε'r
        (by omega : n + 1 ≠ i) hx ⟨j, rfl⟩)) hnear

theorem not_limit_of_large_adversary_scale {r ε ε' γ γ' : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hε' : 0 < ε') (hεr : ε ≤ r) (hε'r : ε' ≤ r)
    (hεγ : ε ≤ γ) (hγ' : 0 ≤ γ') (hγ'ε' : γ' < ε') :
    ¬ GeneratableInLimitAt dist γ γ' (example48LanguageClass r ε ε') :=
  lemma_C_2_not_generatable (rowCriterion hr hε hε' hεr hε'r hεγ hγ' hγ'ε')


end

end GenLimit.MetricSpaces.HilbertAxisReservoir.Example48Rows
