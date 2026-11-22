import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.Fallback
import Mathlib.Data.Nat.Pairing
import Mathlib.Order.Filter.Cofinite

/-! # Repeated observations and Claim 6.11

On the rank-one family consisting only of the whole universe, the concrete
finite-rank machine emits the least unused word. The adversary claims
adjacent pairs far past the machine's frontier, then replays every word
arbitrarily late. Both replay-time outputs exceed the successor by then.
This tests the literal time-indexed definition of W on exact presentations.
-/
namespace GenLimit.KleinbergWei.DensityMeasures.ReplayCounterexample

open FiniteRankFallback FiniteRankParent TowerTopology Filter

private def C : LanguageFamily := fun _ ↦ Set.univ
private theorem hi (i : ℕ) : (C i).Infinite := Set.infinite_univ

private theorem whole (x : FamilyPoint C) : x.val = Set.univ := by
  obtain ⟨i,he⟩ := x.property
  exact he.symm

private theorem rank_one : FiniteRankAtMost (FamilySpace C) 1 := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro K h
  obtain ⟨L,_,hne,_⟩ := h.2 ∅ (by simp)
  exact hne (Subtype.ext ((whole L).trans (whole K).symm))

private def base (n : ℕ) := 10 * (n+1)
private def input (t : ℕ) :=
  if t % 3 < 2 then base (t/3) + t%3 else (t/3).unpair.1

private theorem early (n k : ℕ) (hk : k < 2) : input (3*n+k) = base n + k := by
  have hd : (3*n+k)/3 = n := by omega
  have hm : (3*n+k)%3 = k := by omega
  simp [input,hd,hm,hk]

private theorem replay (x N : ℕ) : ∃ t ≥ N, input t = x := by
  let j := Nat.pair x N
  refine ⟨3*j+2,by have := Nat.right_le_pair x N; dsimp [j]; omega,?_⟩
  have hd : (3*j+2)/3 = j := by omega
  have hm : (3*j+2)%3 = 2 := by omega
  simp [input,hd,hm,j]

private abbrev current := identifiedPointAt C input
private noncomputable abbrev fallback := canonicalFallbackAt C input 1 rank_one
private noncomputable abbrev state := runState hi input current fallback
private noncomputable abbrev out := runOutput hi input current fallback

private theorem used_card (t : ℕ) : (state t).used.card ≤ 2*t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih =>
    change (insert (out t) (insert (input t) (state t).used)).card ≤ _
    have h := Finset.card_insert_le (out t) (insert (input t) (state t).used)
    have h' := Finset.card_insert_le (input t) (state t).used
    omega

private theorem output_bound (t : ℕ) : out t ≤ 2*t+1 := by
  let S := insert (input t) (state t).used
  have hcard : S.card ≤ 2*t+1 := (Finset.card_insert_le ..).trans (Nat.add_le_add_right (used_card t) 1)
  have hn : ¬ Finset.range (2*t+2) ⊆ S := by
    intro h
    have := Finset.card_le_card h
    rw [Finset.card_range] at this
    omega
  obtain ⟨x,hx,hfresh⟩ := Finset.not_subset.mp hn
  have hxL : x ∈ (current t).val := (whole _).symm ▸ Set.mem_univ _
  have h := emittedAtStep_le_candidate hi (state t) (input t) (current t) (fallback t)
    hfresh (Or.inr hxL)
  exact h.trans (Nat.le_of_lt_succ (Finset.mem_range.mp hx))

private theorem omitted (n k : ℕ) (hk : k < 2) : base n + k ∉ Set.range out := by
  rintro ⟨t,ht⟩
  by_cases h : t ≤ 3*n+k
  · have := output_bound t
    dsimp [base] at ht
    omega
  · exact (runOutput_fresh hi input current fallback t) (Finset.mem_insert_of_mem
      ((mem_runState_used_iff hi input current fallback t _).2
        (Or.inl ⟨3*n+k,by omega,(early n k hk).trans ht.symm⟩)))

private def ordering : OrderedLanguage := ⟨Set.univ,id,Function.injective_id,Set.range_id⟩

private theorem replay_bad (x : ℕ) (hx : x ∉ Set.range out) : x ∈ badInputs ordering input out := by
  let y := orderedSuccessor ordering x (Set.mem_univ _)
  have ev := (runOutput_injective hi input current fallback).nat_tendsto_atTop.eventually
    (eventually_gt_atTop y)
  obtain ⟨N,hN⟩ := eventually_atTop.1 ev
  obtain ⟨t,ht,he⟩ := replay x (N+1)
  refine ⟨t,he,by omega,Set.mem_univ _,?_,?_,?_⟩
  · simpa [he,outputSet] using hx
  · simpa [he,y] using hN t (by omega)
  · simpa [he,y] using hN (t-1) (by omega)

/-- The literal bad-run conclusion fails for the canonical finite-rank
algorithm under the repository's repetition-permitting exact enumerations. -/
theorem not_claim_6_11_on_repeated_presentations :
    ∃ (F : LanguageFamily) (hF : ∀ i, (F i).Infinite)
      (hr : FiniteRankAtMost (FamilySpace F) 1) (s : ℕ → ℕ) (O : OrderedLanguage),
      O.carrier = F 0 ∧ Presents s (F 0) ∧
      ¬ EventuallyNoBadRun 1 O (badInputs O s (canonicalRunOutput hF s 1 hr)) := by
  refine ⟨C,hi,rank_one,input,ordering,rfl,Set.eq_univ_iff_forall.mpr (fun x ↦ ?_),?_⟩
  · obtain ⟨t,_,he⟩ := replay x 0
    exact ⟨t,he⟩
  · rintro ⟨m,hm⟩
    apply hm (base m) (by dsimp [base]; omega)
    intro k hk
    exact replay_bad _ (omitted m k hk)

end GenLimit.KleinbergWei.DensityMeasures.ReplayCounterexample
