import GenLimit.Paper39_DenseGeneration.Patient.MachineInvariant
import GenLimit.Paper39_DenseGeneration.Patient.Output

/-!
# Example 3.15: why the untransformed family is insufficient

This is a zero-based version of Example 3.15.  The paper works over the
positive integers.  Here language zero contains the positive odd numbers and
the positive multiples of four; language `i > 0` is the tail
`{2 * j | i ≤ j}`.  Thus language one is the true language of positive even
numbers.

The phrase "enumerates the multiples of four" does not determine their order.
For a completely precise machine trace we choose the increasing presentation
`4, 8, 12, ...`.  On this trace the direct (untransformed) patient-scope
machine outputs exactly `1, 3, 5, ...`, and hence never outputs an element of
the true language.  The structural part of the example--that language zero is
the only recursively critical language--does not depend on this ordering.
-/

namespace GenLimit
namespace PartialEnumeration
namespace Counterexample

open PatientMachine

/-- The first language in Example 3.15. -/
def firstLanguage : Language :=
  {x | x % 2 = 1 ∨ (x ≠ 0 ∧ x % 4 = 0)}

/-- The zero-based family from Example 3.15. -/
def family : LanguageFamily
  | 0 => firstLanguage
  | i + 1 => {x | ∃ j, i + 1 ≤ j ∧ x = 2 * j}

theorem family_infinite (i : ℕ) : (family i).Infinite := by
  cases i with
  | zero =>
      have hrange : Set.range (fun n : ℕ => 2 * n + 1) ⊆ family 0 := by
        rintro _ ⟨n, rfl⟩
        simp [family, firstLanguage, Nat.add_mod]
      exact (Set.infinite_range_of_injective (fun _ _ h => by omega)).mono hrange
  | succ i =>
      have hrange : Set.range (fun n : ℕ => 2 * (i + 1 + n)) ⊆
          family (i + 1) := by
        rintro _ ⟨n, rfl⟩
        exact ⟨i + 1 + n, by omega, rfl⟩
      exact (Set.infinite_range_of_injective (fun _ _ h => by omega)).mono hrange

/-- The example as an `OracleFamily`.  The Boolean oracle is included only to
fit the common interface; the semantic patient-scope machine does not query
it. -/
noncomputable def oracle : OracleFamily := by
  classical
  exact
    { language := family
      infinite' := family_infinite
      query := fun i x => if x ∈ family i then true else false
      query_spec := by intro i x; simp }

/-- We make the paper's partial enumeration fully explicit by taking the
increasing sequence of positive multiples of four. -/
def stream (t : ℕ) : ℕ := 4 * (t + 1)

/-- The true language is family index one: all positive even numbers. -/
def trueLanguage : Language := family 1

/-- The language actually presented by the adversary. -/
def enumeratedLanguage : Language := Set.range stream

@[simp] theorem mem_family_zero_iff {x : ℕ} :
    x ∈ family 0 ↔ x % 2 = 1 ∨ (x ≠ 0 ∧ x % 4 = 0) := Iff.rfl

@[simp] theorem mem_trueLanguage_iff {x : ℕ} :
    x ∈ trueLanguage ↔ ∃ j, 1 ≤ j ∧ x = 2 * j := Iff.rfl

theorem stream_mem_firstLanguage (t : ℕ) : stream t ∈ family 0 := by
  right
  simp only [stream]
  constructor <;> omega

theorem stream_mem_trueLanguage (t : ℕ) : stream t ∈ trueLanguage := by
  refine ⟨2 * (t + 1), ?_, ?_⟩
  · have hpos : 0 < 2 * (t + 1) :=
      Nat.mul_pos (by omega) (Nat.succ_pos t)
    exact hpos
  · change 4 * (t + 1) = 2 * (2 * (t + 1))
    calc
      4 * (t + 1) = (2 * 2) * (t + 1) := by rfl
      _ = 2 * (2 * (t + 1)) := Nat.mul_assoc 2 2 (t + 1)

/-- The chosen stream is, by construction, an exact presentation of the
partial language rather than of the true language. -/
theorem presents_enumeratedLanguage : Presents stream enumeratedLanguage := rfl

theorem stream_injective : Function.Injective stream := by
  intro s t h
  simp only [stream] at h
  omega

theorem enumeratedLanguage_infinite : enumeratedLanguage.Infinite := by
  exact Set.infinite_range_of_injective stream_injective

theorem enumeratedLanguage_subset_trueLanguage :
    enumeratedLanguage ⊆ trueLanguage := by
  rintro _ ⟨t, rfl⟩
  exact stream_mem_trueLanguage t

/-- Any stream whose values lie in the first language keeps index zero
consistent.  No ordering assumption is needed. -/
theorem consistent_zero_of_values
    {adversary : ℕ → ℕ} (hvalues : ∀ t, adversary t ∈ family 0)
    (t : ℕ) : Consistent family adversary t 0 := by
  intro x hx
  change x ∈ sample adversary t at hx
  rw [mem_sample_iff] at hx
  obtain ⟨s, -, rfl⟩ := hx
  exact hvalues s

theorem consistent_zero (t : ℕ) : Consistent family stream t 0 :=
  consistent_zero_of_values stream_mem_firstLanguage t

@[simp] theorem recursiveCritical_zero_of_values
    {adversary : ℕ → ℕ} (hvalues : ∀ t, adversary t ∈ family 0)
    (t : ℕ) : RecursiveCritical family adversary t 0 := by
  simpa only [RecursiveCritical] using consistent_zero_of_values hvalues t

@[simp] theorem recursiveCritical_zero (t : ℕ) :
    RecursiveCritical family stream t 0 :=
  recursiveCritical_zero_of_values stream_mem_firstLanguage t

/-- Every even-tail language has an element congruent to two modulo four, so
it is not contained in the first language. -/
theorem tail_not_subset_first {i : ℕ} (hi : 0 < i) :
    ¬ family i ⊆ family 0 := by
  intro hsub
  have hmem : 4 * i + 2 ∈ family i := by
    cases i with
    | zero => omega
    | succ k =>
        exact ⟨2 * (k + 1) + 1, by omega, by omega⟩
  have := hsub hmem
  simp only [mem_family_zero_iff] at this
  omega

/-- For any announcement order contained in the first language, language zero
is the only recursively critical language at every finite time.  This is the
order-independent structural claim in Example 3.15. -/
theorem recursiveCritical_iff_eq_zero_of_values
    {adversary : ℕ → ℕ} (hvalues : ∀ t, adversary t ∈ family 0)
    (t i : ℕ) : RecursiveCritical family adversary t i ↔ i = 0 := by
  constructor
  · intro hcritical
    by_contra hi
    have hiPos : 0 < i := Nat.pos_of_ne_zero hi
    cases i with
    | zero => contradiction
    | succ k =>
        rw [RecursiveCritical] at hcritical
        have hsub : family (k + 1) ⊆ family 0 :=
          hcritical.2 0 (by omega)
            (recursiveCritical_zero_of_values hvalues t)
        exact tail_not_subset_first (i := k + 1) (by omega) hsub
  · rintro rfl
    exact recursiveCritical_zero_of_values hvalues t

theorem recursiveCritical_iff_eq_zero (t i : ℕ) :
    RecursiveCritical family stream t i ↔ i = 0 :=
  recursiveCritical_iff_eq_zero_of_values stream_mem_firstLanguage t i

theorem onModel : OnModel oracle stream := by
  intro t
  exact ⟨0, consistent_zero t⟩

/-- Consequently the direct patient-scope run always focuses on language
zero, no matter how its scope grows. -/
@[simp] theorem run_focus_eq_zero (t : ℕ) :
    (run oracle stream t).focus = 0 := by
  have hfocus := run_focus_isFocus_of_onModel oracle onModel t
  exact (recursiveCritical_iff_eq_zero t _).1 hfocus.2.1

/-- For the explicitly chosen increasing enumeration, the direct machine
outputs the positive odd numbers in order. -/
theorem output_eq_odd : ∀ t : ℕ, output oracle stream t = 2 * t + 1 := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      classical
      let candidate := 2 * t + 1
      have hcandidateLanguage : candidate ∈ family 0 := by
        left
        simp only [candidate]
        omega
      have hcandidateSample : candidate ∉ sample stream (t + 1) := by
        rw [mem_sample_iff]
        rintro ⟨s, -, hs⟩
        simp only [candidate, stream] at hs
        omega
      have hcandidateUsed : candidate ∉ (run oracle stream t).used := by
        intro hused
        rw [run_used_eq_outputsBefore] at hused
        simp only [outputsBefore] at hused
        rw [Finset.mem_image] at hused
        obtain ⟨s, hs, heq⟩ := hused
        have hst : s < t := Finset.mem_range.mp hs
        rw [ih s hst] at heq
        simp only [candidate] at heq
        omega
      have hcandidate : Available family stream (t + 1)
          (run oracle stream t).used (run oracle stream (t + 1)).focus
          candidate := by
        rw [run_focus_eq_zero]
        exact ⟨hcandidateLanguage, hcandidateSample, hcandidateUsed⟩
      have houtLe : output oracle stream t ≤ candidate :=
        output_minimal_post_focus oracle stream t candidate hcandidate
      have houtAvailable := output_available_post_focus oracle stream t
      rw [run_focus_eq_zero] at houtAvailable
      have hcandLe : candidate ≤ output oracle stream t := by
        by_contra hnot
        have houtLt : output oracle stream t < candidate := by omega
        rcases houtAvailable.1 with hodd | hmultiple
        · let s := output oracle stream t / 2
          have hs : s < t := by
            simp only [s, candidate] at *
            omega
          have hform : output oracle stream t = 2 * s + 1 := by
            simp only [s]
            omega
          have hprior : output oracle stream s ∈ (run oracle stream t).used :=
            output_mem_run_used oracle stream hs
          rw [ih s hs, ← hform] at hprior
          exact houtAvailable.2.2 hprior
        · have hsample : output oracle stream t ∈ sample stream (t + 1) := by
            rw [mem_sample_iff]
            let s := output oracle stream t / 4 - 1
            refine ⟨s, ?_, ?_⟩
            · simp only [s, candidate] at *
              omega
            · simp only [s, stream]
              omega
          exact houtAvailable.2.1 hsample
      simp only [candidate] at houtLe hcandLe ⊢
      omega

/-- The direct patient-scope machine never outputs an element of the true
language.  In particular, it does not generate the true language in the
limit. -/
theorem output_not_mem_trueLanguage (t : ℕ) :
    output oracle stream t ∉ trueLanguage := by
  rw [output_eq_odd]
  rintro ⟨j, -, hj⟩
  omega

end Counterexample
end PartialEnumeration
end GenLimit
