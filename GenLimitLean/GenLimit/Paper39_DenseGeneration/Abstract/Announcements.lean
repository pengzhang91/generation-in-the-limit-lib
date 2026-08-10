import GenLimit.Core.Basic
import Mathlib.Data.Nat.Find

/-!
# First announcements

In each round the adversary speaks before the generator.  These definitions
record which party first announces a value.  They allow repetitions in either
sequence; freshness of a particular algorithm is a separate property.
-/

namespace GenLimit

/-- Values announced by the adversary before any earlier generator output. -/
def AdversaryFirst (adversary generator : ℕ → ℕ) : Set ℕ :=
  {x | ∃ t, adversary t = x ∧ ∀ s, s < t → generator s ≠ x}

/-- Values announced by the generator before any adversary announcement up to
and including the same round. -/
def GeneratorFirst (adversary generator : ℕ → ℕ) : Set ℕ :=
  {x | ∃ t, generator t = x ∧ ∀ s, s ≤ t → adversary s ≠ x}

theorem adversaryFirst_disjoint_generatorFirst
    (adversary generator : ℕ → ℕ) :
    Disjoint (AdversaryFirst adversary generator)
      (GeneratorFirst adversary generator) := by
  rw [Set.disjoint_left]
  intro x hxA hxD
  obtain ⟨t, hat, hnoG⟩ := hxA
  obtain ⟨s, hgs, hnoA⟩ := hxD
  by_cases hst : s < t
  · exact hnoG s hst hgs
  · exact hnoA t (Nat.le_of_not_gt hst) hat

/-- Every value ever announced by the adversary has a first-announcing
party, even when the adversary does not enumerate the whole universe. -/
theorem range_subset_first_announcements
    (adversary generator : ℕ → ℕ) :
    Set.range adversary ⊆
      AdversaryFirst adversary generator ∪
        GeneratorFirst adversary generator := by
  classical
  intro x hx
  let t := Nat.find hx
  have hat : adversary t = x := Nat.find_spec hx
  have htmin : ∀ q, adversary q = x → t ≤ q := by
    intro q hq
    exact Nat.find_min' hx hq
  by_cases hgen : ∃ s, s < t ∧ generator s = x
  · obtain ⟨s, hst, hgs⟩ := hgen
    refine Set.mem_union_right _ ⟨s, hgs, ?_⟩
    intro q hqs haq
    exact (Nat.not_lt_of_ge (htmin q haq)) (lt_of_le_of_lt hqs hst)
  · refine Set.mem_union_left _ ⟨t, hat, ?_⟩
    intro s hst hgs
    exact hgen ⟨s, hst, hgs⟩

/-- If the adversary eventually announces every value, every value has a
unique first-announcing party. -/
theorem adversaryFirst_union_generatorFirst
    {adversary generator : ℕ → ℕ}
    (hsurj : Function.Surjective adversary) :
    AdversaryFirst adversary generator ∪
        GeneratorFirst adversary generator = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact range_subset_first_announcements adversary generator
    ⟨Classical.choose (hsurj x), Classical.choose_spec (hsurj x)⟩

/-- Exact presentations of the normalized target `Set.univ` satisfy the
surjectivity premise of the first-announcement partition. -/
theorem first_announcement_partition_of_presents_univ
    {adversary generator : ℕ → ℕ}
    (hP : Presents adversary Set.univ) :
    AdversaryFirst adversary generator ∪
        GeneratorFirst adversary generator = Set.univ := by
  apply adversaryFirst_union_generatorFirst
  intro x
  have hx : x ∈ Set.range adversary := by
    rw [hP]
    exact Set.mem_univ x
  exact hx

end GenLimit
