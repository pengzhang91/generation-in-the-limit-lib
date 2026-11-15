import GenLimit.NoRegretLanguageGeneration.Comparisons

namespace PredictionToGeneration.Transversal
open Classical
open Blocks

abbrev X := Space (fun n => n+2)

def H : HypothesisClass X := fun h =>
  ∀ x y, h x = false → h y = false → block x = block y → x = y

instance : Infinite X := space_infinite _ (by omega)

theorem uus : UUS H := by
  intro h hh seen
  let n := Cofinite.freshAbove (seen.map block)
  let a : X := ⟨n, ⟨0, by dsimp; omega⟩⟩
  let b : X := ⟨n, ⟨1, by dsimp; omega⟩⟩
  have hf : ∀ z : X, block z = n → z ∉ seen := by
    intro z hz hm
    have hn : n ∈ seen.map block := List.mem_map.mpr ⟨z, hm, hz⟩
    exact Cofinite.freshAbove_not_mem (seen.map block) hn
  by_cases ha : h a = true
  · exact ⟨a, hf a rfl, ha⟩
  · have ha' : h a = false := by cases he : h a <;> simp_all
    have hb : h b = true := by
      cases he : h b with
      | true => rfl
      | false =>
        have hab := hh a b ha' he rfl
        have hval : (0 : Nat) = 1 := congrArg (fun z : X => z.2.val) hab
        omega
    exact ⟨b, hf b rfl, hb⟩

theorem nonempty_class : ∃ h, H h := by
  exact ⟨fun _ => true, by intro x y hx; contradiction⟩

private theorem mistakes_congr_outputs (h g : Hypothesis X) (τ : Trajectory X)
    (hc : ∀ z ∈ τ.map Prod.fst, h z = g z) : mistakes h τ = mistakes g τ := by
  induction τ with
  | nil => rfl
  | cons p τ ih =>
    have he := hc p.1 (by simp)
    have ht := ih (fun z hz => hc z (by simp [hz]))
    simp [mistakes, loss, he, ht]

private theorem finite_bad_representative (m : Nat) (τ : Trajectory X)
    (hb : RealizableBad H m τ) : RealizableBad (Class (fun n => n+2) (fun _ => 1)) m τ := by
  obtain ⟨h, hh, hr, hm⟩ := hb
  let E := (τ.map Prod.fst).toFinset.filter (fun z => h z = false)
  have hE : Separated E := by
    intro x hx y hy he
    exact hh x y (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 he
  have heq : mistakes h τ = mistakes (cofiniteHypothesis E) τ := by
    apply mistakes_congr_outputs
    intro z hz
    have hz' : z ∈ (τ.map Prod.fst).toFinset := List.mem_toFinset.mpr hz
    cases he : h z <;> simp [E, cofiniteHypothesis, hz', he]
  have hre : Realizes (cofiniteHypothesis E) τ := by
    have aux : ∀ t : Trajectory X, Realizes h t → Realizes (cofiniteHypothesis E) t := by
      intro t ht
      induction t with
      | nil => trivial
      | cons p t ih =>
        refine ⟨?_, ih ht.2⟩
        have hp := ht.1
        simp [cofiniteHypothesis, E, hp]
    exact aux τ hr
  exact ⟨_, ⟨E, separated_admissible E hE, rfl⟩, hre, by omega⟩

theorem mf_le_one (T : Nat) : MF H T ≤ 1 := by
  have hf := (mf_spec H uus nonempty_class T).1
  have hg : MFForces (Class (fun n => n+2) (fun _ => 1)) T (MF H T) :=
    forces_mono (fun τ => finite_bad_representative (MF H T) τ) T [] hf
  have hl := (mf_spec (Class (fun n => n+2) (fun _ => 1))
    (Blocks.uus _ _ (by omega)) (Blocks.nonempty_class _ _) T).2 _ hg
  exact Nat.le_trans hl (mf_upper _ _ (by omega) (2*T) T (by omega))

theorem no_regret : RealizableNoRegret H := by
  apply (realizable_no_regret_iff_sublinear H uus nonempty_class).mpr
  intro k
  exact ⟨k, fun t ht => Nat.le_trans (Nat.mul_le_mul_left k (mf_le_one t)) (by simpa using ht)⟩

private theorem priority_exists (R : Finset X) (xs : List X) :
    ∃ z : X, z ∉ R ∧ z ∉ xs ∧ ∀ y : X, y ∉ R → y ∉ xs → Encodable.encode z ≤ Encodable.encode y := by
  obtain ⟨x, hx⟩ := Finset.exists_notMem (R ∪ xs.toFinset)
  simp only [Finset.mem_union, not_or, List.mem_toFinset] at hx
  have hex : ∃ k : Nat, ∃ z : X, Encodable.encode z = k ∧ z ∉ R ∧ z ∉ xs :=
    ⟨Encodable.encode x, x, rfl, hx.1, hx.2⟩
  obtain ⟨z, hz, hR, hxs⟩ := Nat.find_spec hex
  refine ⟨z, hR, hxs, fun y hy hy' => ?_⟩
  rw [hz]
  exact Nat.find_min' hex ⟨y, rfl, hy, hy'⟩

private noncomputable def priority (R : Finset X) (xs : List X) : X :=
  Classical.choose (priority_exists R xs)

private theorem priority_spec (R : Finset X) (xs : List X) :
    priority R xs ∉ R ∧ priority R xs ∉ xs ∧
    ∀ y : X, y ∉ R → y ∉ xs → Encodable.encode (priority R xs) ≤ Encodable.encode y :=
  Classical.choose_spec (priority_exists R xs)

private noncomputable def reserveNext (G : Generator X) (R : Finset X) (xs : List X) : Finset X :=
  if G.output xs ∈ visitedPoints R then R else insert (G.output xs) R

private theorem reserveNext_subset (G : Generator X) (R : Finset X) (xs : List X) :
    R ⊆ reserveNext G R xs := by
  unfold reserveNext
  split
  · exact Finset.Subset.refl _
  · exact Finset.subset_insert _ _

private theorem reserveNext_separated (G : Generator X) (R : Finset X) (xs : List X)
    (hs : Separated R) : Separated (reserveNext G R xs) := by
  unfold reserveNext
  split
  · exact hs
  · rename_i hn
    apply separated_insert R (G.output xs) hs
    intro r hr he
    exact hn ((mem_visitedPoints R _).mpr ⟨r, hr, he⟩)

private structure DiagonalState where
  reserve : Finset X
  history : List X
  separated : Separated reserve
  nodup : history.Nodup
  avoids : ∀ x ∈ history, x ∉ reserve

private noncomputable def DiagonalState.next (s : DiagonalState) (G : Generator X) : DiagonalState where
  reserve := reserveNext G s.reserve s.history
  history := priority (reserveNext G s.reserve s.history) s.history :: s.history
  separated := reserveNext_separated G s.reserve s.history s.separated
  nodup := List.nodup_cons.mpr ⟨(priority_spec _ _).2.1, s.nodup⟩
  avoids := by
    intro x hx
    obtain rfl | hx := List.mem_cons.mp hx
    · exact (priority_spec _ _).1
    · unfold reserveNext
      split
      · exact s.avoids x hx
      · intro hm
        obtain he | hm := Finset.mem_insert.mp hm
        · exact G.fresh s.history (he ▸ hx)
        · exact s.avoids x hx hm

private noncomputable def state (G : Generator X) : Nat → DiagonalState
  | 0 => ⟨∅, [], separated_empty _, by simp, by simp⟩
  | n+1 => (state G n).next G

private theorem state_reserve_mono (G : Generator X) {i j : Nat} (hij : i ≤ j) :
    (state G i).reserve ⊆ (state G j).reserve := by
  induction hij with
  | refl => exact Finset.Subset.refl _
  | @step j hij ih => exact ih.trans (reserveNext_subset _ _ _)

private theorem state_history_mono (G : Generator X) {i j : Nat} (hij : i ≤ j) :
    (state G i).history ⊆ (state G j).history := by
  induction hij with
  | refl => exact List.Subset.refl _
  | @step j hij ih => exact fun x hx => List.mem_cons.mpr (Or.inr (ih hx))

private theorem state_length (G : Generator X) (n : Nat) : (state G n).history.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [state, DiagonalState.next] using congrArg Nat.succ ih

private def finalReserve (G : Generator X) : Set X := {x | ∃ n, x ∈ (state G n).reserve}

private theorem history_avoids_final (G : Generator X) (n : Nat) (x : X)
    (hx : x ∈ (state G n).history) : x ∉ finalReserve G := by
  rintro ⟨j, hj⟩
  exact (state G (max n j)).avoids x
    (state_history_mono G (Nat.le_max_left _ _) hx)
    (state_reserve_mono G (Nat.le_max_right _ _) hj)

private noncomputable def target (G : Generator X) : Hypothesis X :=
  fun x => decide (x ∉ finalReserve G)

private theorem target_mem (G : Generator X) : H (target G) := by
  intro x y hx hy he
  simp only [target, decide_eq_false_iff_not, not_not] at hx hy
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hj⟩ := hy
  exact (state G (max i j)).separated x (state_reserve_mono G (Nat.le_max_left _ _) hi)
    y (state_reserve_mono G (Nat.le_max_right _ _) hj) he

private noncomputable def play (G : Generator X) : PositiveContinuation (target G) [] where
  history n := (state G n).history
  start := rfl
  step n := ⟨priority (reserveNext G (state G n).reserve (state G n).history) (state G n).history,
    (priority_spec _ _).2.1, by
      apply decide_eq_true (history_avoids_final G (n+1) _ (by exact List.mem_cons_self)), rfl⟩

/-- The least-code priority rule eventually reveals every point outside the
final reserve; a point cannot be postponed behind infinitely many lower codes. -/
private theorem play_enumerates (G : Generator X) : (play G).Enumerates := by
  intro x hx
  have hxR : x ∉ finalReserve G := by simpa [target] using hx
  by_contra hnone
  push_neg at hnone
  have hall : ∀ n, ∀ y ∈ (state G n).history, Encodable.encode y < Encodable.encode x := by
    intro n
    induction n with
    | zero => simp [state]
    | succ n ih =>
      intro y hy
      change y ∈ priority (reserveNext G (state G n).reserve (state G n).history)
        (state G n).history :: (state G n).history at hy
      obtain rfl | hy := List.mem_cons.mp hy
      · have hnot : x ∉ reserveNext G (state G n).reserve (state G n).history :=
          fun hm => hxR ⟨n+1, hm⟩
        have hle := (priority_spec _ _).2.2 x hnot (hnone n)
        dsimp [play] at hle
        have hne : Encodable.encode (priority (reserveNext G (state G n).reserve (state G n).history)
            (state G n).history) ≠ Encodable.encode x := by
          intro he
          have he' := Encodable.encode_injective he
          apply hnone (n+1)
          change x ∈ _ :: _
          exact List.mem_cons.mpr (Or.inl he'.symm)
        omega
      · exact ih y hy
  let N := Encodable.encode x + 1
  have hn := (state G N).nodup.map Encodable.encode_injective
  have hsub : (((state G N).history.map Encodable.encode).toFinset) ⊆
      Finset.range (Encodable.encode x) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
    exact Finset.mem_range.mpr (hall N z hz)
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hn, List.length_map, state_length, Finset.card_range] at hc
  dsimp [N] at hc
  omega

private theorem finite_eventually_demonstrated (G : Generator X) (F : Finset X)
    (hF : ∀ x ∈ F, ∃ n, x ∈ (state G n).history) :
    ∃ N, ∀ x ∈ F, x ∈ (state G N).history := by
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x F hx ih =>
    obtain ⟨n, hn⟩ := hF x (by simp)
    obtain ⟨M, hM⟩ := ih (fun y hy => hF y (by simp [hy]))
    refine ⟨max n M, fun y hy => ?_⟩
    obtain rfl | hy := Finset.mem_insert.mp hy
    · exact state_history_mono G (Nat.le_max_left _ _) hn
    · exact state_history_mono G (Nat.le_max_right _ _) (hM y hy)

/-- Every generator makes infinitely many errors on the fair enumeration
constructed for its single final transversal target. -/
theorem not_limit : ¬ GenerationInLimit H := by
  rintro ⟨G, hg⟩
  obtain ⟨B, hb⟩ := hg (target G) (target_mem G) (play G) (play_enumerates G)
  have hcorrect : ∀ n, B ≤ n → G.output (state G n).history ∉ finalReserve G := by
    intro n hn
    simpa [target, play] using hb n hn
  have hvisited : ∀ n, B ≤ n → G.output (state G n).history ∈ visitedPoints (state G n).reserve := by
    intro n hn
    by_contra hv
    apply hcorrect n hn
    refine ⟨n+1, ?_⟩
    change G.output (state G n).history ∈ reserveNext G (state G n).reserve (state G n).history
    simp [reserveNext, hv]
  have hstable : ∀ n, B ≤ n → (state G n).reserve = (state G B).reserve := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      change reserveNext G (state G n).reserve (state G n).history = _
      rw [reserveNext, if_pos (hvisited n hn), ih]
  let F := (visitedPoints (state G B).reserve).filter (fun x => x ∉ finalReserve G)
  have hF : ∀ x ∈ F, ∃ n, x ∈ (state G n).history := by
    intro x hx
    have hp : target G x = true := by
      simpa [target] using (Finset.mem_filter.mp hx).2
    exact play_enumerates G x hp
  obtain ⟨N, hN⟩ := finite_eventually_demonstrated G F hF
  let t := max B N
  have hv := hvisited t (Nat.le_max_left _ _)
  rw [hstable t (Nat.le_max_left _ _)] at hv
  have hz : G.output (state G t).history ∈ F :=
    Finset.mem_filter.mpr ⟨hv, hcorrect t (Nat.le_max_left _ _)⟩
  exact G.fresh (state G t).history
    (state_history_mono G (Nat.le_max_right _ _) (hN _ hz))

/-- Realizable no-regret and zero-rate generation do not imply generation in the limit. -/
theorem transversal_comparison_witness :
    RealizableNoRegret H ∧ ZeroRateGeneration H ∧ ¬ GenerationInLimit H :=
  ⟨no_regret, no_regret_implies_zero_rate H no_regret, not_limit⟩

end PredictionToGeneration.Transversal
