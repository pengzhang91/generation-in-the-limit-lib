import GenLimit.Paper30_TimeSensitiveLanguageGeneration.MeasureZeroDensity
import GenLimit.Support.HistoryChainText
import GenLimit.Support.StreamPrefix

/-! # A single exact presentation with small scores at arbitrarily late positions

Each finite history can be prolonged inside a sparse intermediate language.
Freeze enough of its presentation to determine the score, then include the
next natural number. The resulting adversary is independent of any random tape.
-/
namespace GenLimit.TimeSensitive
open Filter GenLimit.Support
open scoped Topology

def sparseFamily : Generic.LanguageFamily ℕ
  | 0 => Set.univ
  | j+1 => markerIntervalLanguage j

theorem sparseFamily_infinite (j : ℕ) : (sparseFamily j).Infinite := by
  cases j with
  | zero => exact Set.infinite_univ
  | succ j => exact markerIntervalLanguage_infinite j

private theorem strict_marker_levels : StrictMono markerIntervalLanguage := by
  have mono : Monotone marker := by
    intro a b hab
    by_cases ha : a = 0
    · simp [ha,marker]
    · simp only [marker,if_neg ha,if_neg (show b ≠ 0 by omega)]
      exact Nat.pow_le_pow_right (by decide) hab
  intro i j hij
  apply lt_of_le_of_ne (markerIntervalLanguage_nested hij.le)
  let t := i+2
  let x := marker t + (i+1)
  have hx : x ∈ markerIntervalLanguage j := ⟨t, Nat.le_add_right .., Nat.add_le_add_left hij _⟩
  have jump : x < marker (t+1) := by
    have big : i+2 < (3:ℕ)^(i+2) := Nat.lt_pow_self (by decide : 1 < (3:ℕ))
    simp only [x,marker,if_neg (show t ≠ 0 by omega),if_neg (Nat.succ_ne_zero t),pow_succ]
    change 3^(i+2) + (i+1) < 3^(i+2)*3
    omega
  intro eq
  obtain ⟨a,lower,upper⟩ := (eq.symm ▸ hx : x ∈ markerIntervalLanguage i)
  by_cases le : a ≤ t
  · have := mono le
    dsimp [x] at upper
    omega
  · exact (not_le_of_gt jump) ((mono (show t+1 ≤ a by omega)).trans lower)

/-- The fixed hard collection contains countably infinitely many distinct
infinite supports, even when a family is required to have unique indices. -/
theorem sparseFamily_injective : Function.Injective sparseFamily := by
  have proper (j : ℕ) : markerIntervalLanguage j ≠ Set.univ := by
    have h := strict_marker_levels (Nat.lt_succ_self j)
    intro eq
    rw [eq] at h
    exact (not_lt_of_ge (Set.subset_univ _)) h
  intro i j eq
  cases i <;> cases j
  · rfl
  · exact ((proper _).symm eq).elim
  · exact (proper _ eq).elim
  · exact congrArg Nat.succ (strict_marker_levels.injective eq)

private theorem extend_in_marker (xs : List ℕ) :
    ∃ j s, Generic.Presents s (markerIntervalLanguage j) ∧
      ∀ i (hi : i < xs.length), s i = xs[i] := by
  classical
  let j := xs.toFinset.sup id
  have mem (x : ℕ) (hx : x ∈ xs) : x ∈ markerIntervalLanguage j := by
    refine ⟨0, ?_, ?_⟩
    · simp [marker]
    · simpa [marker] using (Finset.le_sup (f := id) (List.mem_toFinset.mpr hx))
  let tail := fun x => if x ∈ markerIntervalLanguage j then x else marker 0
  have pres : Generic.Presents tail (markerIntervalLanguage j) := by
    ext x
    constructor
    · rintro ⟨n,rfl⟩
      simp only [tail]
      split
      · assumption
      · exact marker_mem_markerIntervalLanguage j 0
    · intro hx
      exact ⟨x, by simp [tail,hx]⟩
  exact ⟨j, _, prependStream_presents mem pres,
    fun _ hi => prependStream_apply_of_lt xs tail hi⟩

theorem sparse_presentation_diagonal (score : (ℕ → ℕ) → ℕ → ℝ) (horizon : ℕ → ℕ)
    (causal : ∀ s r n, (∀ i < horizon n, s i = r i) → score s n = score r n)
    (small : ∀ j s, Generic.Presents s (markerIntervalLanguage j) →
      Tendsto (fun m => score s (3^m)) atTop (𝓝 0)) :
    ∃ s, Generic.Presents s Set.univ ∧ ∃ pos : ℕ → ℕ,
      Tendsto pos atTop atTop ∧ ∀ k, score s (pos k) ≤ 1 / ((k:ℝ)+1) := by
  classical
  have step (xs : List ℕ) (k : ℕ) :
      ∃ ys : List ℕ, ∃ n : ℕ, xs <+: ys ∧ xs.length < ys.length ∧ k ∈ ys ∧ k ≤ n ∧
        ∀ r : ℕ → ℕ, (∀ i (hi : i < ys.length), r i = ys[i]) →
          score r n ≤ 1 / ((k:ℝ)+1) := by
    let ws := xs ++ [k]
    obtain ⟨j,s,hp,hw⟩ := extend_in_marker ws
    have hs := (tendsto_order.mp (small j s hp)).2 (1 / ((k:ℝ)+1)) (by positivity)
    have hn : Tendsto (fun m : ℕ => 3^m) atTop atTop :=
      Nat.tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (3 : ℕ))
    obtain ⟨m,hm,hk⟩ := (hs.and (hn.eventually_ge_atTop k)).exists
    let N := max ws.length (horizon (3^m))
    let ys := textPrefix s N
    have len : ys.length = N := by simp [ys,textPrefix]
    have pre : ws <+: ys := by
      apply List.prefix_iff_getElem.mpr
      refine ⟨len ▸ le_max_left .., ?_⟩
      intro i hi
      simpa [ys,textPrefix] using (hw i hi).symm
    have grow : xs.length < ys.length := by
      have := pre.length_le
      simp [ws] at this
      omega
    refine ⟨ys, 3^m, (List.prefix_append xs [k]).trans pre, grow,
      pre.subset (by simp [ws]), hk, ?_⟩
    intro r hr
    apply le_trans (le_of_eq (causal r s _ ?_)) hm.le
    intro i hi
    have bound : i < ys.length := len ▸ lt_of_lt_of_le hi (le_max_right ..)
    simpa [ys,textPrefix] using hr i bound
  choose next pos spec using step
  let w : ℕ → List ℕ := Nat.rec [] (fun k xs => next xs k)
  have grow (k : ℕ) : (w k).length < (w (k+1)).length := (spec (w k) k).2.1
  let chain : HistoryChain ℕ := {
    history := w
    prefix_succ := fun k => (spec (w k) k).1
    le_length := by
      intro n
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (grow n)) }
  refine ⟨chain.stream, Set.eq_univ_of_forall (fun k =>
    chain.history_toFinset_subset_stream_range (k+1)
      (List.mem_toFinset.mpr (spec (w k) k).2.2.1)), fun k => pos (w k) k, ?_, ?_⟩
  · exact tendsto_atTop_mono (fun k => (spec (w k) k).2.2.2.1) tendsto_id
  · intro k
    exact (spec (w k) k).2.2.2.2 _ (fun i hi => chain.stream_eq_get (k+1) i hi)

end GenLimit.TimeSensitive
