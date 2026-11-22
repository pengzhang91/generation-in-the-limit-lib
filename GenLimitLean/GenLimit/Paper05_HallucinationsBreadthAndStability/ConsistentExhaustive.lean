import GenLimit.Paper05_HallucinationsBreadthAndStability.CriticalSampler
import GenLimit.Paper05_HallucinationsBreadthAndStability.ExhaustiveGeneration

/-! # Exhaustive generation with an eventually fresh and valid range (Lemma 7.5) -/

namespace GenLimit.BreadthCharacterizations
open GenLimit.HallucinationModeCollapse GenLimit.CharikarPabbaraju

/-- Lemma 7.5 only promises correct answers for proper sublanguages.
The first index denotes the smaller language. -/
structure NestedDifferenceOracle (F : Generic.LanguageFamily ℕ) where
  query : ℕ → ℕ → Bool
  spec : ∀ i j, F i ⊂ F j → (query i j = true ↔ (F j \ F i).Finite)

namespace ConsistentExhaustive

/-- Search only the training scope. The difference query is made for a
properly nested pair, after the two subset tests. -/
def candidates (O : OracleFamily) (S : SubsetOracle O.language)
    (D : NestedDifferenceOracle O.language) (xs : List ℕ) : Finset ℕ :=
  let k := subsetIdentifier (familyMembership O) S xs
  (Finset.range xs.length).filter (fun i ↦ xs.all (O.query i) &&
    S.query k i && (S.query i k || D.query k i))

def focus (O : OracleFamily) (S : SubsetOracle O.language)
    (D : NestedDifferenceOracle O.language) (xs : List ℕ) : ℕ :=
  let C := candidates O S D xs
  if h : C.Nonempty then C.min' h else 0

private theorem mem_candidates (O : OracleFamily) (S : SubsetOracle O.language)
    (D : NestedDifferenceOracle O.language) (xs : List ℕ) (i : ℕ) :
    let k := subsetIdentifier (familyMembership O) S xs
    i ∈ candidates O S D xs ↔ i < xs.length ∧ (∀ x ∈ xs, x ∈ O.language i) ∧
      O.language k ⊆ O.language i ∧ (O.language i \ O.language k).Finite := by
  let k := subsetIdentifier (familyMembership O) S xs
  simp only [candidates,Finset.mem_filter,Finset.mem_range,Bool.and_eq_true,List.all_eq_true,
    O.query_spec,S.query_spec,Bool.or_eq_true]
  refine ⟨fun ⟨h,⟨cons,sub⟩,diff⟩ ↦ ⟨h,cons,sub,?_⟩,fun ⟨h,cons,sub,diff⟩ ↦ ⟨h,⟨cons,sub⟩,?_⟩⟩
  · by_cases rev : O.language i ⊆ O.language k
    · exact Set.finite_empty.subset (fun x hx ↦ (hx.2 (rev hx.1)).elim)
    · exact (D.spec k i ⟨sub,rev⟩).mp (diff.resolve_left rev)
  · by_cases rev : O.language i ⊆ O.language k
    · exact Or.inl rev
    · exact Or.inr ((D.spec k i ⟨sub,rev⟩).mpr diff)

private theorem focus_bounds (O : OracleFamily) (S : SubsetOracle O.language)
    (D : NestedDifferenceOracle O.language) (hw : WeakAngluinCondition O.language)
    {s : ℕ → ℕ} {z : ℕ} (hp : Generic.Presents s (O.language z)) :
    ∃ N, ∀ t ≥ N, let i := focus O S D (textPrefix s t)
      O.language z ⊆ O.language i ∧ ∀ x ∈ O.language i, t ≤ x → x ∈ O.language z := by
  classical
  let F := O.language
  obtain ⟨W,hW,htell⟩ := hw z
  obtain ⟨M,hM⟩ := Generic.finset_eventually_subset_sample hp W hW
  obtain ⟨N,hN⟩ := critical_focus_between O S hp
  obtain ⟨L,hL⟩ := exhaustiveFiniteScope_eventually_consistent_iff_target_subset hp (z+1)
  have tail (j : ℕ) : ∃ B, ∀ t ≥ B, (F j \ F z).Finite → ∀ x ∈ F j, t ≤ x → x ∈ F z := by
    by_cases hf : (F j \ F z).Finite
    · obtain ⟨b,hb⟩ := hf.bddAbove
      refine ⟨b+1, fun t ht _ x hx hxt ↦ ?_⟩
      by_contra hn
      have := hb (show x ∈ F j \ F z from ⟨hx,hn⟩)
      omega
    · exact ⟨0,fun _ _ h ↦ (hf h).elim⟩
  obtain ⟨B,hB⟩ := Angluin.eventually_all_lt (k := z+1) (fun j _ ↦ tail j)
  refine ⟨max (max (z+1) M) (max N (max L B)),fun t bound ↦ ?_⟩
  let xs := textPrefix s t
  let k := subsetIdentifier (familyMembership O) S xs
  obtain ⟨seen,sub⟩ := hN t (by omega)
  have finite : (F z \ F k).Finite := by
    rcases eq_or_lt_of_le sub with eq | strict
    · change (F z \ O.language (subsetIdentifier ..)).Finite
      rw [eq]; simp [F]
    · exact htell k (fun x hx ↦ seen (Generic.sample_mono (by omega : M ≤ t) (hM hx))) strict
  have cand : z ∈ candidates O S D xs := by
    apply (mem_candidates ..).mpr
    refine ⟨by dsimp [xs]; rw [textPrefix_length]; omega,?_,sub,finite⟩
    intro x hx
    exact Generic.mem_language_of_mem_sample_of_presents hp (Generic.mem_sample_iff.mpr (mem_textPrefix_iff.mp hx))
  let i := focus O S D xs
  have ne : (candidates O S D xs).Nonempty := ⟨z,cand⟩
  have eq : i = (candidates O S D xs).min' ne := by simp [i,focus,ne]
  have iz : i ≤ z := eq ▸ Finset.min'_le _ _ cand
  obtain ⟨_,cons,_,diff⟩ := (mem_candidates O S D xs i).mp (eq ▸ Finset.min'_mem _ ne)
  have incl : O.language z ⊆ O.language i := (hL t (by omega) i (by omega)).mp
    (exhaustiveHistoryConsistent_prefix_iff.mpr (fun x hx ↦ cons x (mem_textPrefix_iff.mpr (Generic.mem_sample_iff.mp hx))))
  exact ⟨incl,hB t (by omega) i (by omega) (diff.subset (fun _ hx ↦ ⟨hx.1,fun h ↦ hx.2 (sub h)⟩))⟩

/-- At round t, seed zero starts its membership search at t. Every fresh
word x in the chosen language can be reached by the seed x-t when t ≤ x. -/
def algorithm (O : OracleFamily) (S : SubsetOracle O.language)
    (D : NestedDifferenceOracle O.language) : Enumerator ℕ := fun xs n ↦
  seededFreshSample O (xs ++ List.range xs.length) (focus O S D xs) (xs.length+n)

private theorem range_at (O : OracleFamily) (S : SubsetOracle O.language)
    (D : NestedDifferenceOracle O.language) (xs : List ℕ) :
    Set.range (algorithm O S D xs) =
      {x | x ∈ O.language (focus O S D xs) ∧ x ∉ xs ∧ xs.length ≤ x} := by
  ext x
  constructor
  · rintro ⟨n,rfl⟩
    have h := seededFreshSample_spec O (xs ++ List.range xs.length) (focus O S D xs) (xs.length+n)
    simpa only [algorithm,List.mem_append,List.mem_range,not_or,not_lt] using h
  · rintro ⟨h,unused,bound⟩
    refine ⟨x-xs.length,?_⟩
    unfold algorithm
    rw [Nat.add_sub_of_le bound]
    exact seededFreshSample_self _ _ _ _ h (by simp [unused,bound])

end ConsistentExhaustive

/-- Lemma 7.5. The same exhaustive enumerator eventually has a range
entirely inside the fresh target. It uses membership, subset, and finite-
difference answers with no tell-tale information. -/
theorem lemma_7_5 (O : OracleFamily) (S : SubsetOracle O.language)
    (D : NestedDifferenceOracle O.language) (hw : WeakAngluinCondition O.language) :
    let A := ConsistentExhaustive.algorithm O S D
    EnumeratesExhaustively A O.language ∧ IsLimitGenerator (enumeratorSupport A) O.language := by
  intro A
  have both (z : ℕ) (s : ℕ → ℕ) (hp : Generic.Presents s (O.language z)) :
      ∃ T, ∀ t ≥ T, let R := Set.range (A (textPrefix s t))
        R ⊆ O.language z \ (Generic.sample s t : Set ℕ) ∧
        O.language z ⊆ (Generic.sample s t : Set ℕ) ∪ {x | ∃ j < t, A (textPrefix s j) 0 = x} ∪ R := by
    classical
    obtain ⟨N,hN⟩ := ConsistentExhaustive.focus_bounds O S D hw hp
    let W := (Finset.range N).filter (· ∈ O.language z)
    obtain ⟨M,hM⟩ := Generic.finset_eventually_subset_sample hp W
      (fun x hx ↦ (Finset.mem_filter.mp hx).2)
    refine ⟨max M N,fun t ht ↦ ?_⟩
    dsimp only
    rw [show A = _ from (rfl : A = ConsistentExhaustive.algorithm O S D),ConsistentExhaustive.range_at]
    obtain ⟨incl,correct⟩ := hN t (by omega)
    constructor
    · rintro x ⟨hx,unseen,hxt⟩
      exact ⟨correct x hx (by simpa using hxt),fun h ↦ unseen (mem_textPrefix_iff.mpr (Generic.mem_sample_iff.mp h))⟩
    · intro x hx
      by_cases seen : x ∈ Generic.sample s t
      · exact Or.inl (Or.inl seen)
      by_cases late : t ≤ x
      · exact Or.inr ⟨incl hx,fun h ↦ seen (Generic.mem_sample_iff.mpr (mem_textPrefix_iff.mp h)),by simpa using late⟩
      have after : N ≤ x := by
        by_contra! small
        exact seen (Generic.sample_mono (by omega : M ≤ t) (hM (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr small,hx⟩)))
      refine Or.inl (Or.inr ⟨x,by omega,?_⟩)
      unfold A ConsistentExhaustive.algorithm
      rw [textPrefix_length,Nat.add_zero]
      apply seededFreshSample_self _ _ _ _ ((hN x after).1 hx)
      simp only [List.mem_append,List.mem_range,lt_self_iff_false,or_false]
      exact fun h ↦ seen (Generic.sample_mono (by omega : x ≤ t) (Generic.mem_sample_iff.mpr (mem_textPrefix_iff.mp h)))
  constructor
  · intro z s hp
    obtain ⟨T,hT⟩ := both _ _ hp
    exact ⟨T,fun t ht ↦ ⟨Set.finite_empty.subset (fun x hx ↦ (hx.2 ((hT t ht).1 hx.1).1).elim),(hT t ht).2⟩⟩
  · intro z s hp
    obtain ⟨T,hT⟩ := both _ _ hp
    exact ⟨T,fun t ht ↦ (hT t ht).1⟩

end GenLimit.BreadthCharacterizations
