import GenLimit.Paper39_DenseGeneration.Abstract.PartialEnumeration
import GenLimit.Paper39_DenseGeneration.Patient.Fact312

/-!
# Partial-enumeration game traces

Unlike `PatientScope.GameTrace`, this trace distinguishes the enumerated set
from the true density target.  This is the precise ownership interface needed
by Section 3.3.
-/

namespace GenLimit
namespace PartialEnumeration

structure PartialGameTrace where
  target : Language
  enumerated : Language
  enumerated_subset_target : enumerated ⊆ target
  adversary : ℕ → ℕ
  generator : ℕ → ℕ
  presents : Presents adversary enumerated
  fresh_adversary : ∀ t s, s ≤ t → adversary s ≠ generator t
  fresh_generator : ∀ t s, s < t → generator s ≠ generator t
  validFrom : ℕ
  eventual_target : ∀ t, validFrom ≤ t → generator t ∈ target

namespace PartialGameTrace

variable (G : PartialGameTrace)

def attacker : Set ℕ := AdversaryFirst G.adversary G.generator

def defender : Set ℕ := GeneratorFirst G.adversary G.generator

theorem output_range : Set.range G.generator = G.defender := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, rfl, G.fresh_adversary t⟩
  · rintro ⟨t, htx, -⟩
    exact ⟨t, htx⟩

theorem generator_injective : Function.Injective G.generator := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij' | hji'
  · exact G.fresh_generator j i hij' hij
  · exact G.fresh_generator i j hji' hij.symm

theorem enumerated_covered : G.enumerated ⊆ G.attacker ∪ G.defender := by
  intro x hx
  apply range_subset_first_announcements G.adversary G.generator
  rw [G.presents]
  exact hx

theorem attacker_subset_target : G.attacker ⊆ G.target := by
  rintro x ⟨t, htx, -⟩
  apply G.enumerated_subset_target
  rw [← G.presents]
  exact ⟨t, htx⟩

theorem ownership_disjoint : Disjoint G.attacker G.defender :=
  adversaryFirst_disjoint_generatorFirst G.adversary G.generator

noncomputable def earlyAttacker : Finset ℕ := by
  classical
  exact (sample G.adversary (G.validFrom + 1)).filter
    (fun x => x ∈ G.attacker)

noncomputable def firstAdversaryTime (x : ℕ) : ℕ := by
  classical
  exact if h : ∃ t, G.adversary t = x then Nat.find h else 0

theorem firstAdversaryTime_spec {x : ℕ} (hx : x ∈ G.attacker) :
    G.adversary (G.firstAdversaryTime x) = x := by
  classical
  obtain ⟨t, htx, -⟩ := hx
  simp only [firstAdversaryTime]
  split
  · exact Nat.find_spec ‹∃ t, G.adversary t = x›
  · exact False.elim (‹¬ ∃ t, G.adversary t = x› ⟨t, htx⟩)

theorem firstAdversaryTime_min {x t : ℕ} (hx : x ∈ G.attacker)
    (ht : G.adversary t = x) : G.firstAdversaryTime x ≤ t := by
  classical
  obtain ⟨w, hw, -⟩ := hx
  simp only [firstAdversaryTime]
  split
  · exact Nat.find_min' ‹∃ q, G.adversary q = x› ht
  · exact False.elim (‹¬ ∃ q, G.adversary q = x› ⟨w, hw⟩)

theorem firstAdversaryTime_not_mem_sample {x : ℕ}
    (hx : x ∈ G.attacker) :
    x ∉ sample G.adversary (G.firstAdversaryTime x) := by
  intro hmem
  rw [mem_sample_iff] at hmem
  obtain ⟨s, hs, hseq⟩ := hmem
  exact (Nat.not_lt_of_ge (G.firstAdversaryTime_min hx hseq)) hs

theorem validFrom_lt_firstAdversaryTime
    {switchLoss : Set ℕ} {x : ℕ}
    (hx : x ∈ PatientScope.ordinaryAttacker
      G.target G.attacker switchLoss G.earlyAttacker) :
    G.validFrom < G.firstAdversaryTime x := by
  have hxA : x ∈ G.attacker := hx.1.1
  have hnotEarly : x ∉ G.earlyAttacker := by
    intro hearly
    exact hx.2 (Set.mem_union_left _ hearly)
  by_contra hnot
  have htime : G.firstAdversaryTime x < G.validFrom + 1 := by omega
  apply hnotEarly
  classical
  simp only [earlyAttacker, Finset.mem_filter]
  refine ⟨?_, hxA⟩
  rw [mem_sample_iff]
  exact ⟨G.firstAdversaryTime x, htime,
    G.firstAdversaryTime_spec hxA⟩

noncomputable def predecessorPartner (x : ℕ) : ℕ :=
  G.generator (G.firstAdversaryTime x - 1)

def HasPredecessorComparison (switchLoss : Set ℕ) : Prop :=
  ∀ t, G.validFrom < t →
    G.adversary t ∈ G.attacker →
    G.adversary t ∉ sample G.adversary t →
    G.adversary t ∉ switchLoss →
    G.generator (t - 1) < G.adversary t

theorem predecessorPartner_mem
    {switchLoss : Set ℕ} {x : ℕ}
    (hx : x ∈ PatientScope.ordinaryAttacker
      G.target G.attacker switchLoss G.earlyAttacker) :
    G.predecessorPartner x ∈ G.defender ∩ G.target := by
  have htime := G.validFrom_lt_firstAdversaryTime hx
  refine ⟨?_, ?_⟩
  · rw [← G.output_range]
    exact ⟨G.firstAdversaryTime x - 1, rfl⟩
  · apply G.eventual_target
    omega

theorem predecessorPartner_lt
    {switchLoss : Set ℕ}
    (hcompare : G.HasPredecessorComparison switchLoss)
    {x : ℕ}
    (hx : x ∈ PatientScope.ordinaryAttacker
      G.target G.attacker switchLoss G.earlyAttacker) :
    G.predecessorPartner x < x := by
  have htime := G.validFrom_lt_firstAdversaryTime hx
  have hxA : x ∈ G.attacker := hx.1.1
  have hspec := G.firstAdversaryTime_spec hxA
  have hAat : G.adversary (G.firstAdversaryTime x) ∈ G.attacker := by
    rw [hspec]
    exact hxA
  have hnotSwitch : G.adversary (G.firstAdversaryTime x) ∉
      switchLoss := by
    rw [hspec]
    intro hswitch
    exact hx.2 (Set.mem_union_right _ hswitch)
  have hfresh : G.adversary (G.firstAdversaryTime x) ∉
      sample G.adversary (G.firstAdversaryTime x) := by
    simpa [hspec] using G.firstAdversaryTime_not_mem_sample hxA
  have h := hcompare (G.firstAdversaryTime x) htime hAat
    hfresh hnotSwitch
  simpa [predecessorPartner, hspec] using h

theorem predecessorPartner_injective
    {switchLoss : Set ℕ} :
    Set.InjOn G.predecessorPartner
      (PatientScope.ordinaryAttacker
        G.target G.attacker switchLoss G.earlyAttacker) := by
  intro x hx y hy hxy
  have htx := G.validFrom_lt_firstAdversaryTime hx
  have hty := G.validFrom_lt_firstAdversaryTime hy
  have hpred : G.firstAdversaryTime x - 1 =
      G.firstAdversaryTime y - 1 := by
    apply G.generator_injective
    exact hxy
  have htime : G.firstAdversaryTime x = G.firstAdversaryTime y := by omega
  have hxA : x ∈ G.attacker := hx.1.1
  have hyA : y ∈ G.attacker := hy.1.1
  calc
    x = G.adversary (G.firstAdversaryTime x) :=
      (G.firstAdversaryTime_spec hxA).symm
    _ = G.adversary (G.firstAdversaryTime y) := by rw [htime]
    _ = y := G.firstAdversaryTime_spec hyA

noncomputable def toCertificate
    (switchLoss : Set ℕ)
    (hswitch : switchLoss ⊆ G.attacker ∩ G.target)
    (hcompare : G.HasPredecessorComparison switchLoss)
    (switchBudget : ℕ → ℕ)
    (hbudget : ∀ n, PatientScope.prefixCount switchLoss n ≤
      switchBudget n) : PatientScope.PartialEnumerationCertificate where
  target := G.target
  enumerated := G.enumerated
  enumerated_subset_target := G.enumerated_subset_target
  attacker := G.attacker
  defender := G.defender
  output := G.generator
  output_range := G.output_range
  output_injective := G.generator_injective
  validFrom := G.validFrom
  eventual_target := G.eventual_target
  enumerated_covered := G.enumerated_covered
  attacker_subset_target := G.attacker_subset_target
  ownership_disjoint := G.ownership_disjoint
  earlyAttacker := G.earlyAttacker
  switchLoss := switchLoss
  switchLoss_subset := hswitch
  partner := G.predecessorPartner
  partner_mem := fun _ hx => G.predecessorPartner_mem hx
  partner_lt := fun _ hx => G.predecessorPartner_lt hcompare hx
  partner_injective := G.predecessorPartner_injective
  switchBudget := switchBudget
  switch_prefix_le := hbudget

end PartialGameTrace

/-- Concrete partial trace induced by a semantic patient-scope run. -/
noncomputable def machineTrace
    (O : OracleFamily) (stream : ℕ → ℕ) (E K : Language)
    (validFrom : ℕ) (hP : Presents stream E) (hsub : E ⊆ K)
    (hvalid : ∀ t, validFrom ≤ t →
      PatientMachine.output O stream t ∈ K) : PartialGameTrace where
  target := K
  enumerated := E
  enumerated_subset_target := hsub
  adversary := stream
  generator := PatientMachine.output O stream
  presents := hP
  fresh_adversary := fun t s hst =>
    PatientMachine.stream_ne_output O stream t s hst
  fresh_generator := fun _ _ hst =>
    PatientMachine.output_ne_of_lt O stream hst
  validFrom := validFrom
  eventual_target := hvalid

theorem machineTrace_hasPredecessorComparison
    (O : OracleFamily) (stream : ℕ → ℕ) (E K : Language)
    (validFrom : ℕ) (hP : Presents stream E) (hsub : E ⊆ K)
    (hvalid : ∀ t, validFrom ≤ t →
      PatientMachine.output O stream t ∈ K) :
    PartialGameTrace.HasPredecessorComparison
      (machineTrace O stream E K validFrom hP hsub hvalid)
        (PatientMachine.lateSwitchLoss O stream validFrom) := by
  intro t htime hattacker hfresh hnotSwitch
  exact PatientMachine.previous_output_lt_of_not_lateSwitch
    O stream htime hattacker hfresh hnotSwitch

end PartialEnumeration
end GenLimit
