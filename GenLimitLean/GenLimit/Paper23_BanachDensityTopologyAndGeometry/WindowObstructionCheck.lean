import GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity
import GenLimit.Paper39_DenseGeneration.Patient.Main

/-! A check on the final adversarial target ℕ in the proof of P23
Theorem 4.1. Definition 3.2 permits the unbounded start bound 1+⌊k/8⌋.
Any output with prefix lower density at least one half has positive
window lower density for this bound. -/
namespace GenLimit.KleinbergWei.Banach

open Filter Set
open scoped Classical ENNReal
noncomputable section

def linearWindow (k : ℕ) : WithTop ℕ := (↑(1+k/8) : WithTop ℕ)

theorem linearWindow_admissible : AdmissibleWindowBound linearWindow := by
  refine ⟨fun a b h => ?_,fun k => ?_⟩
  · exact WithTop.coe_le_coe.mpr (Nat.add_le_add_left (Nat.div_le_div_right h) 1)
  · exact WithTop.coe_le_coe.mpr (show 1 ≤ 1+k/8 by omega)

theorem linearWindow_unbounded (T : ℕ) : ∃ k, (T : WithTop ℕ) < linearWindow k := by
  refine ⟨8*T,?_⟩
  unfold linearWindow; exact WithTop.coe_lt_coe.mpr (show T < 1+8*T/8 by omega)

/-- Discarding the portion of the prefix before m loses at most m words. -/
private theorem shift_count (A : Set ℕ) (m k : ℕ) :
    ((Finset.range k).filter (· ∈ A)).card ≤ m+windowCount A m k := by
  let W := (Finset.Ico m (m+k)).filter (· ∈ A)
  have sub : (Finset.range k).filter (· ∈ A) ⊆ Finset.range m ∪ W := by
    intro x hx; obtain ⟨hn,mem⟩ := Finset.mem_filter.mp hx
    by_cases h : x < m
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr h)
    · have lt := Finset.mem_range.mp hn
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,mem⟩)
  simpa [W,windowCount] using (Finset.card_le_card sub).trans (Finset.card_union_le ..)

/-- The same estimate applies when positions and window lengths are
measured in the increasing ranks of any target language. -/
theorem window_pos_of_prefix_half (K : OrderedLanguage) (A : Set ℕ) (half : 1/2 ≤ K.lowerDensity A) :
    ENNReal.ofReal (1/8) ≤ lowerWindowDensity linearWindow (K.rankSet A) := by
  have high : ∀ᶠ k : ℕ in atTop, (3/8:ℝ) < K.prefixRatio A k :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le (by norm_num : (3/8:ℝ)<1/2) half)
      (isBoundedUnder_of ⟨0,fun _ => OrderedLanguage.prefixRatio_nonneg ..⟩)
  apply le_liminf_of_le
  · exact isCoboundedUnder_ge_of_le atTop (fun _ => le_top)
  filter_upwards [high,eventually_ge_atTop 8] with k hk large
  apply le_iInf
  intro m
  split_ifs with allowed
  · have hm : m ≤ 1+k/8 := WithTop.coe_le_coe.mp allowed.2
    have pos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    rw [OrderedLanguage.prefixRatio,if_neg (by omega : k ≠ 0)] at hk
    have h := (lt_div_iff₀ pos).mp hk
    have card := shift_count (K.rankSet A) m k
    change K.prefixCount A k ≤ _ at card
    have c : (K.prefixCount A k:ℝ) ≤ (m:ℝ)+windowCount (K.rankSet A) m k := by exact_mod_cast card
    have bound : 8*(m:ℝ) ≤ (k:ℝ)+8 := by exact_mod_cast (show 8*m ≤ k+8 by omega)
    have fraction : (1/8:ℝ) ≤ (windowCount (K.rankSet A) m k:ℝ)/k := by
      apply (le_div_iff₀ pos).mpr
      have l : (8:ℝ) ≤ k := by exact_mod_cast large
      linarith
    simpa only [windowRatio,if_neg (by omega : k ≠ 0),ENNReal.ofReal_div_of_pos pos,ENNReal.ofReal_natCast]
      using ENNReal.ofReal_le_ofReal fraction
  · exact le_top

/-- Every exact target presentation gives positive density for windows
measured in the increasing ranks of that target. -/
theorem patient_rank_windows (O : OracleFamily) (s : ℕ → ℕ) {z : ℕ}
    (presentation : Presents s (O.language z)) :
    ENNReal.ofReal (1/8) ≤ lowerWindowDensity linearWindow
      ((OrderedLanguage.increasing (O.language z) (O.infinite' z)).rankSet
        (range (PatientMachine.output O s))) := by
  let K := OrderedLanguage.increasing (O.language z) (O.infinite' z)
  have sub : GeneratorFirst s (PatientMachine.output O s) ∩ O.language z ⊆ range (PatientMachine.output O s) := by
    rintro x ⟨⟨t,eq,_⟩,_⟩; exact ⟨t,eq⟩
  exact window_pos_of_prefix_half K _ ((PatientMachine.patientScope_lowerDensity_half O s presentation).trans
    (K.lowerDensity_mono sub))

/-- On the all-natural target at the end of the source diagonal, the
rank windows are exactly the ambient windows of Definition 3.2. -/
theorem patient_windows_on_univ (O : OracleFamily) (s : ℕ → ℕ) {z : ℕ}
    (target : O.language z = univ) (presentation : Presents s (O.language z)) :
    ENNReal.ofReal (1/8) ≤ lowerWindowDensity linearWindow (range (PatientMachine.output O s)) := by
  have eq : (OrderedLanguage.increasing (O.language z) (O.infinite' z)).rankSet
      (range (PatientMachine.output O s)) = range (PatientMachine.output O s) := by
    ext x; simp [OrderedLanguage.rankSet,OrderedLanguage.increasing,target]
  simpa only [eq] using patient_rank_windows O s presentation

end
end GenLimit.KleinbergWei.Banach
