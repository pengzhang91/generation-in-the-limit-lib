import GenLimit.Paper39_DenseGeneration.Partial.Closure
import GenLimit.Paper39_DenseGeneration.Dynamics
import GenLimit.Paper39_DenseGeneration.Patient.MachineInvariant

/-!
# Eventual criticality under partial enumeration

This module formalizes the structural argument in Lemma 3.16.  Although the
enumerated language need not be a member of the transformed family, finite
prefixes of consistency stabilize.  The binary finite-intersection closure
then contains one fixed language which is eventually always recursively
critical and is contained in the true language.
-/

namespace GenLimit
namespace PartialEnumeration

/-- Once consistency has its stable, presented-set characterization on a
finite scope, recursive criticality is also stable there. -/
theorem recursiveCritical_eventually_stable
    {C : LanguageFamily} {stream : ℕ → ℕ} {E : Language} {T s : ℕ}
    (hstable : ∀ t, T ≤ t → ∀ i, i < s →
      (Consistent C stream t i ↔ E ⊆ C i)) :
    ∀ t, T ≤ t → ∀ i, i < s →
      (RecursiveCritical C stream t i ↔
        RecursiveCritical C stream T i) := by
  intro t hTt
  apply recursiveCritical_iff_of_old_critical_consistent hTt
  intro i his hi
  apply (hstable t hTt i his).2
  exact (hstable T (Nat.le_refl _) i his).1
    (recursiveCritical_consistent hi)

/-- Index of the singleton intersection representing the original language
`O.language z` in the filtered closure. -/
noncomputable def singletonIndex (O : OracleFamily) (z : ℕ) : ℕ :=
  closureIndex O (2 ^ z)

@[simp] theorem closure_language_singletonIndex
    (O : OracleFamily) (z : ℕ) :
    (closure O).language (singletonIndex O z) = O.language z := by
  rw [singletonIndex, closure_language_closureIndex O (goodCode_two_pow O z)]
  exact codedIntersection_two_pow O.language z

/-- A partial presentation contained in one original language keeps the
closure machine on-model. -/
theorem closure_onModel
    (O : OracleFamily) {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (hP : Presents stream E) (hsub : E ⊆ O.language z) :
    PatientMachine.OnModel (closure O) stream := by
  intro t
  refine ⟨singletonIndex O z, ?_⟩
  apply consistent_of_presented_subset hP
  rw [closure_language_singletonIndex]
  exact hsub

/-- Structural core of Lemma 3.16: one fixed retained finite intersection is
eventually always critical and is contained in the true language. -/
theorem exists_eventually_critical_subset_target
    (O : OracleFamily) {stream : ℕ → ℕ} {E : Language} {z : ℕ}
    (hP : Presents stream E) (hE : E.Infinite)
    (hsub : E ⊆ O.language z) :
    ∃ w T,
      (closure O).language w ⊆ O.language z ∧
      ∀ t, T ≤ t →
        RecursiveCritical (closure O).language stream t w := by
  classical
  let p := 2 ^ z
  let a := singletonIndex O z
  let cap := closureIndex O (2 ^ (z + 1))
  have hpGood : GoodCode O p := by
    simpa [p] using goodCode_two_pow O z
  have hcapGood : GoodCode O (2 ^ (z + 1)) :=
    goodCode_two_pow O (z + 1)
  have hpa : closureCode O a = p := by
    simpa [a, singletonIndex] using closureCode_closureIndex O hpGood
  have haCap : a < cap := by
    apply closureIndex_lt_closureIndex O hpGood
    rw [pow_succ]
    have hpPos : 0 < 2 ^ z := Nat.two_pow_pos z
    omega
  obtain ⟨T, hstable⟩ :=
    finite_scope_eventually_consistent_iff_presented_subset
      (C := (closure O).language) hP cap
  have hcritStable :=
    recursiveCritical_eventually_stable hstable
  have haCon : Consistent (closure O).language stream T a := by
    apply consistent_of_presented_subset hP
    simpa only [a, closure_language_singletonIndex] using hsub
  have hexistsCon : ∃ i, Consistent (closure O).language stream T i :=
    ⟨a, haCon⟩
  let m := Nat.find hexistsCon
  have hmCon : Consistent (closure O).language stream T m :=
    Nat.find_spec hexistsCon
  have hmMin : ∀ i, i < m →
      ¬ Consistent (closure O).language stream T i :=
    fun i hi => Nat.find_min hexistsCon hi
  have hmCrit : RecursiveCritical (closure O).language stream T m :=
    PatientMachine.recursiveCritical_of_consistent_of_minimal hmCon hmMin
  have hma : m ≤ a := Nat.find_min' hexistsCon haCon
  obtain ⟨j, hjFocus⟩ :=
    exists_focus_of_critical_in_scope
      (C := (closure O).language) (stream := stream)
      (t := T) (s := a + 1) (z := m)
      (Nat.lt_succ_of_le hma) hmCrit
  have hjCrit : RecursiveCritical (closure O).language stream T j :=
    hjFocus.2.1
  have hja : j ≤ a := Nat.le_of_lt_succ hjFocus.1
  rcases eq_or_lt_of_le hja with hjaEq | hjaLt
  · subst j
    refine ⟨a, T, ?_, ?_⟩
    · rw [show (closure O).language a = O.language z by
        simpa only [a] using closure_language_singletonIndex O z]
    · intro t hTt
      exact (hcritStable t hTt a haCap).2 hjCrit
  · let q := closureCode O j
    have hqGood : GoodCode O q := closureCode_good O j
    have hqLt : q < p := by
      have := closureCode_strictMono O hjaLt
      simpa [q, hpa] using this
    have hESubJ : E ⊆ (closure O).language j :=
      (hstable T (Nat.le_refl _) j (lt_of_le_of_lt hja haCap)).1
        (recursiveCritical_consistent hjCrit)
    have hESubRaw : E ⊆ codedIntersection O.language q := by
      simpa [q] using hESubJ
    have hESubExtended :
        E ⊆ codedIntersection O.language (q + p) := by
      rw [codedIntersection_add_two_pow (by simpa [p] using hqLt)]
      exact fun x hx => ⟨hESubRaw hx, hsub hx⟩
    have hExtendedGood : GoodCode O (q + p) := by
      have hpPos : 0 < p := by exact Nat.two_pow_pos z
      refine ⟨(Nat.add_pos_right q hpPos).ne', ?_⟩
      exact hE.mono hESubExtended
    let b := closureIndex O (q + p)
    have hcodeB : closureCode O b = q + p := by
      simpa [b] using closureCode_closureIndex O hExtendedGood
    have hjb : j < b := by
      have hpPos : 0 < p := by exact Nat.two_pow_pos z
      have hindex := closureIndex_lt_closureIndex O hqGood
        (Nat.lt_add_of_pos_right hpPos)
      simpa [q, b, closureIndex_closureCode] using hindex
    have hqbHigh : q + p < 2 ^ (z + 1) := by
      rw [pow_succ]
      dsimp [p] at hqLt ⊢
      omega
    have hbCap : b < cap := by
      exact closureIndex_lt_closureIndex O hExtendedGood hqbHigh
    have hbCon : Consistent (closure O).language stream T b := by
      apply consistent_of_presented_subset hP
      simpa [b, hcodeB] using hESubExtended
    have hBSubJ : (closure O).language b ⊆
        (closure O).language j := by
      rw [closure_language, closure_language]
      rw [hcodeB]
      rw [codedIntersection_add_two_pow (by simpa [p] using hqLt)]
      intro x hx
      simpa [q] using hx.1
    have hexistsLater : ∃ k, j < k ∧ k ≤ b ∧
        RecursiveCritical (closure O).language stream T k := by
      by_contra hnone
      push_neg at hnone
      have hbCrit :
          RecursiveCritical (closure O).language stream T b := by
        have hbPos : 0 < b := by omega
        have hbEq : b = (b - 1) + 1 := by omega
        rw [hbEq, RecursiveCritical]
        refine ⟨by simpa only [← hbEq] using hbCon, ?_⟩
        intro i hi hiCrit
        have hib : i < b := by omega
        have hij : i ≤ j := by
          by_contra hnot
          have hji : j < i := Nat.lt_of_not_ge hnot
          exact hnone i hji (Nat.le_of_lt hib) hiCrit
        simpa only [← hbEq] using hBSubJ.trans
          (recursiveCritical_subset_of_le hij hiCrit hjCrit)
      exact hnone b hjb (Nat.le_refl _) hbCrit
    obtain ⟨w, hjw, hwb, hwCrit⟩ := hexistsLater
    have haw : a ≤ w := by
      by_contra hnot
      have hwa : w < a := Nat.lt_of_not_ge hnot
      have hwj : w ≤ j := hjFocus.2.2 w (by omega) hwCrit
      omega
    have hwCap : w < cap := lt_of_le_of_lt hwb hbCap
    have hpCodeW : p ≤ closureCode O w := by
      have := (closureCode_strictMono O).monotone haw
      simpa [hpa] using this
    have hcodeWHigh : closureCode O w < 2 ^ (z + 1) := by
      have hmono := (closureCode_strictMono O).monotone hwb
      exact lt_of_le_of_lt (by simpa [hcodeB] using hmono) hqbHigh
    refine ⟨w, T, ?_, ?_⟩
    · rw [closure_language]
      exact codedIntersection_subset_target_of_mem_block
        hpCodeW hcodeWHigh
    · intro t hTt
      exact (hcritStable t hTt w hwCap).2 hwCrit

end PartialEnumeration
end GenLimit
