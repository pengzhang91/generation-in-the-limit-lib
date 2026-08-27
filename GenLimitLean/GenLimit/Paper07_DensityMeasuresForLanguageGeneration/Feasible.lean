import GenLimit.Core.Basic
import GenLimit.Support.Presentations
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.WellFounded

/-!
# #07 Feasible sequences

Definition 4.4 and Claims 4.2--4.7. Indices are shifted from the paper's
one-based convention: stage n contains presentation positions 0 through n.
-/

namespace GenLimit.KleinbergWei.DensityMeasures

/-- Definition 4.4: proper approximations containing progressively longer
prefixes of one presentation of the terminal language. -/
structure FeasibleSequence
    (sequence : ℕ → Language) (terminal : Language) where
  proper : ∀ n, sequence n ⊂ terminal
  enumeration : ℕ → ℕ
  presents : Presents enumeration terminal
  prefix_mem : ∀ n i, i ≤ n → enumeration i ∈ sequence n

/-- Union of stages at or after t. -/
def tailUnion (sequence : ℕ → Language) (t : ℕ) : Language :=
  {u | ∃ n, t ≤ n ∧ u ∈ sequence n}

/-- Claim 4.2. -/
theorem claim_4_2
    {sequence : ℕ → Language} {terminal : Language}
    (h : FeasibleSequence sequence terminal) (t : ℕ) :
    tailUnion sequence t = terminal := by
  ext u
  constructor
  · rintro ⟨n, _htn, hun⟩
    exact (h.proper n).le hun
  · intro huK
    rw [← h.presents] at huK
    obtain ⟨i, rfl⟩ := huK
    exact ⟨max t i, Nat.le_max_left _ _,
      h.prefix_mem (max t i) i (Nat.le_max_right _ _)⟩

/-- Claim 4.3: every infinite subsequence remains feasible. -/
def claim_4_3
    {sequence : ℕ → Language} {terminal : Language}
    (h : FeasibleSequence sequence terminal)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    FeasibleSequence (fun n => sequence (φ n)) terminal where
  proper n := h.proper (φ n)
  enumeration := h.enumeration
  presents := h.presents
  prefix_mem n i hin :=
    h.prefix_mem (φ n) i (hin.trans hφ.le_apply)

/-- Eventual form of Claim 4.4. -/
theorem claim_4_4_eventually_absent
    {sequence : ℕ → Language} {terminal L : Language}
    (h : FeasibleSequence sequence terminal) :
    ∃ T, ∀ n, T ≤ n → sequence n ≠ L := by
  by_cases hoccurs : ∃ n, sequence n = L
  · obtain ⟨n₀, hn₀⟩ := hoccurs
    have hproper : L ⊂ terminal := by simpa [hn₀] using h.proper n₀
    obtain ⟨u, huK, huL⟩ := Set.exists_of_ssubset hproper
    rw [← h.presents] at huK
    obtain ⟨T, hTu⟩ := huK
    refine ⟨T, ?_⟩
    intro n hTn heq
    apply huL
    rw [← hTu]
    simpa [heq] using h.prefix_mem n T hTn
  · push_neg at hoccurs
    exact ⟨0, fun n _ => hoccurs n⟩

/-- Claim 4.4: a fixed proper language occurs only finitely often. -/
theorem claim_4_4
    {sequence : ℕ → Language} {terminal L : Language}
    (h : FeasibleSequence sequence terminal) :
    {n | sequence n = L}.Finite := by
  obtain ⟨T, hT⟩ := claim_4_4_eventually_absent h
  apply (Finset.range T).finite_toSet.subset
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hnot
  exact hT n (Nat.le_of_not_gt hnot) hn

/-- Claim 4.5: a feasible sequence has infinitely many distinct languages. -/
theorem claim_4_5
    {sequence : ℕ → Language} {terminal : Language}
    (h : FeasibleSequence sequence terminal) :
    (Set.range sequence).Infinite := by
  by_contra hnot
  have hrange : (Set.range sequence).Finite := not_not.mp hnot
  letI : Finite (Set.range sequence) := Set.finite_coe_iff.mpr hrange
  let indexedRange : ℕ → Set.range sequence :=
    fun n => ⟨sequence n, ⟨n, rfl⟩⟩
  obtain ⟨L, hfiber⟩ := Finite.exists_infinite_fiber indexedRange
  have hfiber_set :
      (indexedRange ⁻¹' ({L} : Set (Set.range sequence))).Infinite :=
    Set.infinite_coe_iff.mp hfiber
  have hsub :
      indexedRange ⁻¹' ({L} : Set (Set.range sequence)) ⊆
        {n | sequence n = L.1} := by
    intro n hn
    have heq : indexedRange n = L := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hn
    exact congrArg Subtype.val heq
  exact hfiber_set.mono hsub (claim_4_4 h)

theorem finite_eventually_subset_sequence
    {sequence : ℕ → Language} {terminal : Language}
    (h : FeasibleSequence sequence terminal)
    (F : Finset ℕ) (hF : (↑F : Set ℕ) ⊆ terminal) :
    ∃ T, ∀ n, T ≤ n → (↑F : Set ℕ) ⊆ sequence n := by
  have hP : GenLimit.Generic.Presents h.enumeration terminal := h.presents
  obtain ⟨T, hT⟩ :=
    GenLimit.Support.finite_eventually_subset_sample hP F hF
  refine ⟨T, ?_⟩
  intro n hTn u hu
  have husample : u ∈ GenLimit.Generic.sample h.enumeration n :=
    hT n hTn hu
  obtain ⟨i, hin, hiu⟩ := GenLimit.Generic.mem_sample_iff.mp husample
  rw [← hiu]
  exact h.prefix_mem n i (Nat.le_of_lt hin)

/-- Union of sequence languages containing F. -/
def constrainedUnion
    (sequence : ℕ → Language) (F : Finset ℕ) : Language :=
  {u | ∃ n, (↑F : Set ℕ) ⊆ sequence n ∧ u ∈ sequence n}

/-- Claim 4.6. -/
theorem claim_4_6
    {sequence : ℕ → Language} {terminal : Language}
    (h : FeasibleSequence sequence terminal)
    (F : Finset ℕ) (hF : (↑F : Set ℕ) ⊆ terminal) :
    constrainedUnion sequence F = terminal := by
  obtain ⟨T, hT⟩ := finite_eventually_subset_sequence h F hF
  ext u
  constructor
  · rintro ⟨n, _hFn, hun⟩
    exact (h.proper n).le hun
  · intro huK
    have huTail : u ∈ tailUnion sequence T := by
      rw [claim_4_2 h T]
      exact huK
    obtain ⟨n, hTn, hun⟩ := huTail
    exact ⟨n, hT n hTn, hun⟩

/-- Distinct sequence languages containing F. -/
def constrainedLanguages
    (sequence : ℕ → Language) (F : Finset ℕ) : Set Language :=
  {L | ∃ n, (↑F : Set ℕ) ⊆ sequence n ∧ L = sequence n}

/-- Claim 4.7. The source states strict containment of `F`; non-strict
containment is equivalent here because every feasible terminal language is
infinite whereas `F` is finite. -/
theorem claim_4_7
    {sequence : ℕ → Language} {terminal : Language}
    (h : FeasibleSequence sequence terminal)
    (F : Finset ℕ) (hF : (↑F : Set ℕ) ⊆ terminal) :
    (constrainedLanguages sequence F).Infinite := by
  obtain ⟨T, hT⟩ := finite_eventually_subset_sequence h F hF
  by_contra hnot
  have hfinite : (constrainedLanguages sequence F).Finite := not_not.mp hnot
  letI : Finite (constrainedLanguages sequence F) :=
    Set.finite_coe_iff.mpr hfinite
  let tailRange : ℕ → constrainedLanguages sequence F :=
    fun n =>
      ⟨sequence (T + n),
        ⟨T + n, hT (T + n) (Nat.le_add_right T n), rfl⟩⟩
  obtain ⟨L, hfiber⟩ := Finite.exists_infinite_fiber tailRange
  have hfiber_set :
      (tailRange ⁻¹' ({L} : Set (constrainedLanguages sequence F))).Infinite :=
    Set.infinite_coe_iff.mp hfiber
  have hsub :
      tailRange ⁻¹' ({L} : Set (constrainedLanguages sequence F)) ⊆
        {n | sequence (T + n) = L.1} := by
    intro n hn
    have heq : tailRange n = L := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hn
    exact congrArg Subtype.val heq
  have hinfinite_shifted : {n | sequence (T + n) = L.1}.Infinite :=
    hfiber_set.mono hsub
  have hfinite_shifted : {n | sequence (T + n) = L.1}.Finite := by
    exact (claim_4_4 (h := h) (L := L.1)).preimage
      (fun _ _ heq => by omega)
  exact hinfinite_shifted hfinite_shifted

end GenLimit.KleinbergWei.DensityMeasures
