import GenLimit.Core.OracleFamily
import GenLimit.Paper01_LanguageGeneration.Critical
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic

/-!
# #01 Language Generation: observed-set interface

Equation (4.1) presents the generator as a function of the finite observed set,
whereas the round-indexed construction in (4.5) scans the first `t` candidate
languages.  The construction below uses the number of *distinct* observations
as its candidate scope.  This equals the round on injective presentations, but
the final theorem does not require injectivity: every exact presentation of an
infinite target eventually contains arbitrarily many distinct observations.

The construction remains semantic and noncomputable.  It tests inclusion
between whole languages and chooses a fresh member classically; it is not a
finite-query implementation.
-/

namespace GenLimit
namespace KM
namespace SetInterface

/-- Consistency expressed using only the observed finite set. -/
def ConsistentOn
    (C : LanguageFamily) (S : Finset ℕ) (n : ℕ) : Prop :=
  (↑S : Set ℕ) ⊆ C n

/-- KM criticality expressed using only the observed finite set. -/
def CriticalOn
    (C : LanguageFamily) (S : Finset ℕ) (n : ℕ) : Prop :=
  ConsistentOn C S n ∧
    ∀ i, i ≤ n → ConsistentOn C S i → C n ⊆ C i

@[simp] theorem consistentOn_sample_iff
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ} :
    ConsistentOn C (sample stream t) n ↔ Consistent C stream t n :=
  Iff.rfl

@[simp] theorem criticalOn_sample_iff
    {C : LanguageFamily} {stream : ℕ → ℕ} {t n : ℕ} :
    CriticalOn C (sample stream t) n ↔ Critical C stream t n :=
  Iff.rfl

/-- Set-indexed critical languages form the same descending inclusion chain as
the round-indexed critical languages. -/
theorem criticalOn_subset_of_le
    {C : LanguageFamily} {S : Finset ℕ} {i j : ℕ}
    (hij : i ≤ j) (hi : CriticalOn C S i)
    (hj : CriticalOn C S j) :
    C j ⊆ C i :=
  hj.2 i hij hi.1

/-- Critical indices scanned by the literal finite-set interface.  The scope
is recovered as the number of distinct observations. -/
noncomputable def criticalIndices
    (C : LanguageFamily) (S : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.range S.card).filter (CriticalOn C S)

@[simp] theorem mem_criticalIndices
    {C : LanguageFamily} {S : Finset ℕ} {n : ℕ} :
    n ∈ criticalIndices C S ↔ n < S.card ∧ CriticalOn C S n := by
  classical
  simp [criticalIndices]

/-- Highest set-critical candidate below the recovered scope, with an
arbitrary default before any candidate is in scope. -/
noncomputable def focus
    (C : LanguageFamily) (S : Finset ℕ) : ℕ := by
  classical
  let candidates := criticalIndices C S
  exact if h : candidates.Nonempty then candidates.max' h else 0

theorem focus_spec
    {C : LanguageFamily} {S : Finset ℕ} {z : ℕ}
    (hzScope : z < S.card) (hz : CriticalOn C S z) :
    focus C S < S.card ∧
      CriticalOn C S (focus C S) ∧
      z ≤ focus C S := by
  classical
  let candidates := criticalIndices C S
  have hzmem : z ∈ candidates := by
    simpa [candidates] using
      (mem_criticalIndices.mpr ⟨hzScope, hz⟩)
  have hne : candidates.Nonempty := ⟨z, hzmem⟩
  have hfmem : candidates.max' hne ∈ candidates :=
    Finset.max'_mem candidates hne
  have hfocus : focus C S = candidates.max' hne := by
    simp [focus, candidates, hne]
  rw [hfocus]
  have hparts :
      candidates.max' hne < S.card ∧
        CriticalOn C S (candidates.max' hne) := by
    simpa [candidates] using (mem_criticalIndices.mp hfmem)
  exact ⟨hparts.1, hparts.2,
    Finset.le_max' candidates z hzmem⟩

/-- Least member of language `i` outside the observed finite set. -/
noncomputable def fresh
    (O : OracleFamily) (S : Finset ℕ) (i : ℕ) : ℕ := by
  classical
  exact Nat.find ((O.infinite' i).exists_notMem_finset S)

theorem fresh_spec
    (O : OracleFamily) (S : Finset ℕ) (i : ℕ) :
    fresh O S i ∈ O.language i ∧ fresh O S i ∉ S := by
  classical
  exact Nat.find_spec ((O.infinite' i).exists_notMem_finset S)

/-- A literal function of the observed finite set. -/
noncomputable def generator
    (O : OracleFamily) (S : Finset ℕ) : ℕ :=
  fresh O S (focus O.language S)

theorem generator_spec
    (O : OracleFamily) (S : Finset ℕ) :
    generator O S ∈ O.language (focus O.language S) ∧
      generator O S ∉ S :=
  fresh_spec O S (focus O.language S)

/-- An injective prefix of length `t` has exactly `t` distinct observations. -/
theorem sample_card_of_injective
    (stream : ℕ → ℕ) (hinjective : Function.Injective stream) (t : ℕ) :
    (sample stream t).card = t := by
  classical
  rw [sample, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    exact hinjective hab

/-- Along any exact presentation of an infinite target, the distinct-observation
scope eventually contains the target index.  Repetitions may delay this point,
but cannot prevent it. -/
theorem eventually_target_below_sample_card
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    ∃ T, ∀ t, T ≤ t → z < (sample stream t).card := by
  classical
  obtain ⟨S, hS, hcard⟩ :=
    (O.infinite' z).exists_subset_card_eq (z + 1)
  have hEventually :
      ∀ R : Finset ℕ, (↑R : Set ℕ) ⊆ O.language z →
        ∃ T, R ⊆ sample stream T := by
    intro R
    induction R using Finset.induction_on with
    | empty =>
        intro _
        exact ⟨0, by simp⟩
    | @insert u R huR ih =>
        intro hR
        have huTarget : u ∈ O.language z := hR (by simp)
        have hRTarget : (↑R : Set ℕ) ⊆ O.language z := by
          intro v hv
          exact hR (by simp [hv])
        obtain ⟨Tu, hTu⟩ := eventually_mem_sample_of_presents hP huTarget
        obtain ⟨TR, hTR⟩ := ih hRTarget
        refine ⟨max Tu TR, ?_⟩
        intro v hv
        rw [Finset.mem_insert] at hv
        rcases hv with rfl | hv
        · exact hTu _ (Nat.le_max_left _ _)
        · exact sample_mono (Nat.le_max_right _ _) (hTR hv)
  obtain ⟨T, hST⟩ := hEventually S hS
  refine ⟨T, ?_⟩
  intro t hTt
  apply Nat.lt_of_succ_le
  have hle : S.card ≤ (sample stream t).card :=
    Finset.card_le_card
      (fun _ hu => sample_mono hTt (hST hu))
  simpa [Nat.succ_eq_add_one, hcard] using hle

/-- Paper equation (4.1)'s finite-set-only conclusion, on the exact boundary
where the observed set determines the round. -/
def GeneratesFromObservedSet
    (O : OracleFamily) (stream : ℕ → ℕ) (z : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    generator O (sample stream t) ∈ O.language z ∧
      generator O (sample stream t) ∉ sample stream t

/-- The semantic KM theorem through the literal observed-set interface for
repetition-free presentations. -/
theorem kleinbergMullainathan_set_interface
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z))
    (hinjective : Function.Injective stream) :
    GeneratesFromObservedSet O stream z := by
  obtain ⟨T, hcritical⟩ := target_eventually_critical hP
  refine ⟨max T (z + 1), ?_⟩
  intro t ht
  have hT : T ≤ t :=
    le_trans (Nat.le_max_left T (z + 1)) ht
  have hzt : z < t :=
    Nat.lt_of_succ_le
      (le_trans (Nat.le_max_right T (z + 1)) ht)
  have hcard : (sample stream t).card = t :=
    sample_card_of_injective stream hinjective t
  have hzScope : z < (sample stream t).card := by
    simpa [hcard] using hzt
  have hzCritical :
      CriticalOn O.language (sample stream t) z :=
    criticalOn_sample_iff.mpr (hcritical t hT)
  have hf := focus_spec hzScope hzCritical
  have hout := generator_spec O (sample stream t)
  have hsub :
      O.language (focus O.language (sample stream t)) ⊆
        O.language z :=
    criticalOn_subset_of_le hf.2.2 hzCritical hf.2.1
  exact ⟨hsub hout.1, hout.2⟩

/-- Equation (4.1)'s literal finite-set-only generator works for arbitrary
exact presentations, including presentations with repetitions.  The raw round
cannot be recovered from the observed set, but it is not needed: the
distinct-observation cardinality is a nondecreasing, unbounded candidate
scope. -/
theorem kleinbergMullainathan_set_interface_with_repetitions
    (O : OracleFamily) {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    GeneratesFromObservedSet O stream z := by
  obtain ⟨Tcritical, hcritical⟩ := target_eventually_critical hP
  obtain ⟨Tscope, hscope⟩ :=
    eventually_target_below_sample_card O hP
  refine ⟨max Tcritical Tscope, ?_⟩
  intro t ht
  have hCritical :
      CriticalOn O.language (sample stream t) z :=
    criticalOn_sample_iff.mpr
      (hcritical t ((Nat.le_max_left _ _).trans ht))
  have hzScope : z < (sample stream t).card :=
    hscope t ((Nat.le_max_right _ _).trans ht)
  have hf := focus_spec hzScope hCritical
  have hout := generator_spec O (sample stream t)
  have hsub :
      O.language (focus O.language (sample stream t)) ⊆
        O.language z :=
    criticalOn_subset_of_le hf.2.2 hCritical hf.2.1
  exact ⟨hsub hout.1, hout.2⟩

end SetInterface
end KM
end GenLimit
