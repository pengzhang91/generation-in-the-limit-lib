import GenLimit.NoRegretLanguageGeneration.Comparisons
import GenLimit.NoRegretLanguageGeneration.Support
import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace PredictionToGeneration.CountableGeneration
open Classical

noncomputable def commonSupport (hs : Nat → Hypothesis X) (s : Finset Nat) : Set X :=
  {x | ∀ i∈s,hs i x=true}

noncomputable def consistentIndices (hs : Nat → Hypothesis X) (n : Nat) (xs : List X) : Finset Nat :=
  (Finset.range n).filter (fun i => ∀ x∈xs,hs i x=true)

noncomputable def finitePart (hs : Nat → Hypothesis X) (s : Finset Nat) : Finset X :=
  if hf : (commonSupport hs s).Finite then hf.toFinset else ∅

/-- Union of all finite intersections among the first n languages. -/
noncomputable def obstruction (hs : Nat → Hypothesis X) (n : Nat) : Finset X :=
  (Finset.range n).powerset.biUnion (finitePart hs)

def Good (hs : Nat → Hypothesis X) (n : Nat) (xs : List X) : Prop :=
  (commonSupport hs (consistentIndices hs n xs)).Infinite

theorem good_long_history (hs : Nat → Hypothesis X) (n : Nat) (xs : List X)
    (hnd : xs.Nodup) (hsize : (obstruction hs n).card < xs.length) : Good hs n xs := by
  intro hf
  have hsub : xs.toFinset ⊆ obstruction hs n := by
    intro x hx
    apply Finset.mem_biUnion.mpr
    refine ⟨consistentIndices hs n xs,Finset.mem_powerset.mpr (Finset.filter_subset _ _),?_⟩
    have hcommon : x∈commonSupport hs (consistentIndices hs n xs) := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2 x (List.mem_toFinset.mp hx)
    simpa [finitePart,hf] using hcommon
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at hc
  omega

theorem good_zero (hs : Nat → Hypothesis X) (hX : (Set.univ : Set X).Infinite) (xs : List X) :
    Good hs 0 xs := by simpa [Good,consistentIndices,commonSupport] using hX

noncomputable def selected (hs : Nat → Hypothesis X) (xs : List X) : Nat :=
  thresholdMax (fun n => Good hs n xs) xs.length

theorem selected_good (hs : Nat → Hypothesis X) (hX : (Set.univ : Set X).Infinite) (xs : List X) :
    Good hs (selected hs xs) xs := (thresholdMax_spec (fun n => Good hs n xs) (good_zero hs hX xs) xs.length).1

theorem output_exists (hs : Nat → Hypothesis X) (hX : (Set.univ : Set X).Infinite) (xs : List X) :
    ∃ x,x∉xs ∧ x∈commonSupport hs (consistentIndices hs (selected hs xs) xs) := by
  obtain ⟨x,hx,hf⟩ := (selected_good hs hX xs).exists_notMem_finset xs.toFinset
  exact ⟨x,by simpa using hf,hx⟩

noncomputable def generator (hs : Nat → Hypothesis X) (hX : (Set.univ : Set X).Infinite) : Generator X :=
  ⟨fun xs => Classical.choose (output_exists hs hX xs),fun xs => (Classical.choose_spec (output_exists hs hX xs)).1⟩

theorem generator_common (hs : Nat → Hypothesis X) (hX : (Set.univ : Set X).Infinite) (xs : List X) :
    (generator hs hX).output xs ∈ commonSupport hs (consistentIndices hs (selected hs xs) xs) :=
  (Classical.choose_spec (output_exists hs hX xs)).2

/-- Uniform over streams for each fixed index; no validity-label feedback is used. -/
theorem indexed_nonuniform (hs : Nat → Hypothesis X) (hX : (Set.univ : Set X).Infinite) (j : Nat) :
    ∃ B, LastMistakeBound (generator hs hX) (hs j) B := by
  refine ⟨max (j+1) ((obstruction hs (j+1)).card+1),?_⟩
  intro xs hnd hr hlen
  have hn : j+1≤xs.length := by omega
  have hg := good_long_history hs (j+1) xs hnd (by omega)
  have hsel : j+1≤selected hs xs := (thresholdMax_spec _ (good_zero hs hX xs) _).2 _ hn hg
  have hconsistent : ∀ x∈xs,hs j x=true := (realizes_play_iff _ _ _).mp hr
  have hj : j∈consistentIndices hs (selected hs xs) xs :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hconsistent⟩
  exact generator_common hs hX xs j hj

end PredictionToGeneration.CountableGeneration

namespace PredictionToGeneration

/-- The cited countable-class nonuniform generation theorem, proved directly. -/
theorem countable_uus_nonuniform (H : HypothesisClass X) [Countable {h // H h}]
    (hu : UUS H) (hne : ∃ h,H h) : NonuniformGeneration H := by
  classical
  letI : Nonempty {h // H h} := ⟨⟨Classical.choose hne,Classical.choose_spec hne⟩⟩
  obtain ⟨e,he⟩ := exists_surjective_nat {h // H h}
  let hs : Nat → Hypothesis X := fun n => (e n).val
  have hX : (Set.univ : Set X).Infinite := by
    obtain ⟨h,hh⟩ := hne
    exact ((uus_iff_infinite_support H).mp hu h hh).mono (Set.subset_univ _)
  refine ⟨CountableGeneration.generator hs hX,?_⟩
  intro h hh
  obtain ⟨j,hj⟩ := he ⟨h,hh⟩
  have hj' : hs j=h := congrArg Subtype.val hj
  simpa [hj'] using CountableGeneration.indexed_nonuniform hs hX j

end PredictionToGeneration




