import GenLimit.Paper28_ContrastiveGeneration.DefectInfimum
import GenLimit.Paper28_ContrastiveGeneration.AbsenceCount

/-! # Identification under pairwise infinite defects

The learner enumerates pairs consisting of a hypothesis index and a finite
set of exceptional rounds. It selects the first pair consistent with the
observed cuts outside its exceptions. Positive coverage forces any
permanently consistent pair to denote the target.
-/
namespace GenLimit.ContrastiveGeneration

/-- Distinct co-singletons have exactly the edge joining the two holes
as their common crossing graph. Their directed defect is infinite. -/
theorem coSingleton_defect [Infinite α] {u v : α} (hne : u ≠ v) :
    (∀ e : Edge α, CommonCrossing (coSingletonSupport u) (coSingletonSupport v) e ↔
      Incident u e ∧ Incident v e) ∧
    defectNumber (coSingletonSupport u) (coSingletonSupport v) = ⊤ := by
  classical
  constructor
  · intro e
    simp only [CommonCrossing, crosses_coSingletonSupport_iff_incident]
  · apply Set.encard_eq_top_iff.mpr
    apply (Set.infinite_univ.diff (Set.toFinite ({u,v} : Set α))).mono
    rintro x ⟨_, hx⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
    refine ⟨hx.1, ?_⟩
    rintro ⟨e, ⟨a, b⟩, inc⟩
    have hu := (crosses_coSingletonSupport_iff_incident u e).mp a
    have hv := (crosses_coSingletonSupport_iff_incident v e).mp b
    exact (incident_eq_of_two_distinct_incident hne hu hv inc).elim hx.1 hx.2

private theorem finite_defect_of_compatible {h g : Set α} {s : ℕ → Edge α} {k : ℕ}
    (hp : IsKCorruptedContrastivePresentation k s h) (B : Finset ℕ)
    (hg : ∀ j, j ∉ B → Crosses g (s j)) : (positiveDefectSet h g).Finite := by
  let times := Generic.ViolationIndices s (Crosses h) ∪ (↑B : Set ℕ)
  have htimes : times.Finite := hp.1.union B.finite_toSet
  apply ((htimes.image fun j => (s j).left).union
    (htimes.image fun j => (s j).right)).subset
  intro x hx
  obtain ⟨j, inc⟩ := hp.2.2 hx.1
  have hj : j ∈ times := by
    by_contra habs
    have ch : Crosses h (s j) := by
      by_contra bad
      exact habs (Or.inl bad)
    have cg := hg j (fun hjB => habs (Or.inr hjB))
    exact hx.2 ⟨s j, ⟨ch, cg⟩, inc⟩
  rcases inc with h | h
  · exact Or.inl ⟨j, hj, h.symm⟩
  · exact Or.inr ⟨j, hj, h.symm⟩

private def Fits (F : Generic.LanguageFamily α) {t : ℕ} (xs : Fin t → Edge α)
    (guess : ℕ × Finset ℕ) : Prop :=
  ∀ j : Fin t, j.val ∉ guess.2 → Crosses (F guess.1) (xs j)

private noncomputable def defectLearner (F : Generic.LanguageFamily α)
    (code : ℕ → ℕ × Finset ℕ) : ContrastiveIdentifier α := by
  classical
  exact fun _ xs => if h : ∃ n, Fits F xs (code n) then (code (Nat.find h)).1 else 0

/-- The general robustness implication in Section 1.1, main result (4).
One identifier is fixed before the target, presentation and corruption budget. -/
theorem finiteCorruption_of_infinite_defects (F : Generic.LanguageFamily α)
    (gap : ∀ i j, F i ≠ F j → defectNumber (F i) (F j) = ⊤) :
    FinitelyCorruptionContrastivelyIdentifiable F := by
  classical
  obtain ⟨code, surj⟩ := exists_surjective_nat (ℕ × Finset ℕ)
  refine ⟨defectLearner F code, ?_⟩
  intro k z s hp
  let survives (n : ℕ) := ∀ j, j ∉ (code n).2 → Crosses (F (code n).1) (s j)
  have hex : ∃ n, survives n := by
    obtain ⟨n, hn⟩ := surj (z, hp.1.toFinset)
    refine ⟨n, ?_⟩
    intro j
    rw [hn]
    exact fun h => by
      by_contra bad
      exact h (hp.1.mem_toFinset.mpr bad)
  let m := Nat.find hex
  have good : survives m := Nat.find_spec hex
  have same : F (code m).1 = F z := by
    by_contra ne
    have inf := Set.encard_eq_top_iff.mp (gap z (code m).1 (Ne.symm ne))
    exact inf (finite_defect_of_compatible hp _ good)
  have lower (n : ℕ) (hn : n < m) :
      ∃ T, ∀ t, T ≤ t → ¬Fits F (streamPrefix s t) (code n) := by
    have bad := Nat.find_min hex hn
    change ¬∀ j, j ∉ (code n).2 → Crosses (F (code n).1) (s j) at bad
    push_neg at bad
    obtain ⟨j, hj, hcut⟩ := bad
    exact ⟨j+1, fun t ht fits => hcut (fits ⟨j, by omega⟩ hj)⟩
  obtain ⟨T, hT⟩ := Angluin.eventually_all_lt lower
  refine ⟨(code m).1, same, T, ?_⟩
  intro t ht
  have viable : Fits F (streamPrefix s t) (code m) := fun j => good j.val
  have h : ∃ n, Fits F (streamPrefix s t) (code n) := ⟨m, viable⟩
  have eq : Nat.find h = m := by
    apply Nat.le_antisymm (Nat.find_min' h viable)
    by_contra! small
    exact hT t ht _ small (Nat.find_spec h)
  simp [contrastiveIdentifierOutput, defectLearner, h, eq]

end GenLimit.ContrastiveGeneration
