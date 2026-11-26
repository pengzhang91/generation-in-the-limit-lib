import GenLimit.Core.ClassGeneration
import Mathlib.Tactic

/-!
# Finite positive witnesses for ordinary generation

This extension uses the upstream sequence-input model without redefining it.
`SetDriven` below refers to dependence on the input set, not set-valued output.
-/

namespace GenLimit.FiniteWitness

open GenLimit.Generic

variable {α : Type*}

/-- Run an input-set function on an ordered finite history. -/
noncomputable def ofSet (g : Finset α → α) : Generator α :=
  fun _ xs => g (sequenceSample xs)

@[simp] theorem output_ofSet (g : Finset α → α) (stream : Stream α) (t : ℕ) :
    output (ofSet g) stream t = g (sample stream t) := by
  simp [output, ofSet, sequenceSample_prefix]

/-- A finite set after which every consistent finite extension is good. -/
def Locks (g : Finset α → α) (L : Language α) : Prop :=
  ∃ T : Finset α, (↑T : Set α) ⊆ L ∧
    ∀ S : Finset α, T ⊆ S → (↑S : Set α) ⊆ L → g S ∈ L ∧ g S ∉ S

/-- Existence of one input-set generator in the original positive-text model. -/
def SetDrivenGeneratable (H : LanguageClass α) : Prop :=
  ∃ g : Finset α → α, IsLimitGenerator (ofSet g) H

/-- Consistent targets whose assigned positive witnesses have been observed. -/
def active (H : LanguageClass α) (T : Language α → Finset α)
    (S : Finset α) : Set (Language α) :=
  {L | L ∈ H ∧ T L ⊆ S ∧ (↑S : Set α) ⊆ L}

/-- The simultaneous common intersection of all active targets. -/
def activeCore (H : LanguageClass α) (T : Language α → Finset α)
    (S : Finset α) : Set α :=
  {x | ∀ L, L ∈ active H T S → x ∈ L}

/-- The paper's condition, with an assignment extended arbitrarily off `H`. -/
def HasFiniteWitnesses (H : LanguageClass α) : Prop :=
  ∃ T : Language α → Finset α,
    (∀ L, L ∈ H → (↑(T L) : Set α) ⊆ L) ∧
    ∀ S : Finset α, (active H T S).Nonempty → (activeCore H T S).Infinite

theorem locks_eventually_correct {g : Finset α → α} {L : Language α}
    (h : Locks g L) {stream : Stream α} (hP : Presents stream L) :
    ∃ t₀, ∀ t, t₀ ≤ t → CorrectAt (ofSet g) L stream t := by
  obtain ⟨T, hTL, hT⟩ := h
  obtain ⟨t₀, ht₀⟩ := finset_eventually_subset_sample hP T hTL
  refine ⟨t₀, ?_⟩
  intro t ht
  have hSL : (↑(sample stream t) : Set α) ⊆ L := by
    intro x hx
    exact mem_language_of_mem_sample_of_presents hP hx
  simpa [CorrectAt] using hT (sample stream t)
    (ht₀.trans (sample_mono ht)) hSL

theorem locks_imply_setDriven {H : LanguageClass α}
    (h : ∃ g : Finset α → α, ∀ L, L ∈ H → Locks g L) :
    SetDrivenGeneratable H := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun L hL _ hP => locks_eventually_correct (hg L hL) hP⟩

theorem setDriven_implies_ordinary {H : LanguageClass α}
    (h : SetDrivenGeneratable H) : GeneratableInLimit H := by
  obtain ⟨g, hg⟩ := h
  exact ⟨ofSet g, hg⟩

noncomputable def lockingWitness (g : Finset α → α) (L : Language α) : Finset α := by
  classical
  exact if h : Locks g L then h.choose else ∅

theorem lockingWitness_spec {g : Finset α → α} {L : Language α}
    (h : Locks g L) :
    (↑(lockingWitness g L) : Set α) ⊆ L ∧
      ∀ S : Finset α, lockingWitness g L ⊆ S → (↑S : Set α) ⊆ L →
        g S ∈ L ∧ g S ∉ S := by
  classical
  simpa [lockingWitness, h] using h.choose_spec

/-- A finite active intersection is itself a forbidden common input. -/
theorem locks_imply_finiteWitnesses {H : LanguageClass α}
    (h : ∃ g : Finset α → α, ∀ L, L ∈ H → Locks g L) :
    HasFiniteWitnesses H := by
  classical
  obtain ⟨g, hg⟩ := h
  let T := lockingWitness g
  refine ⟨T, fun L hL => (lockingWitness_spec (hg L hL)).1, ?_⟩
  intro S hactive
  let C := activeCore H T S
  change ¬ C.Finite
  intro hC
  let R := hC.toFinset
  have hSR : S ⊆ R := by
    intro x hx
    apply hC.mem_toFinset.mpr
    intro L hL
    exact hL.2.2 hx
  have hgood : ∀ L, L ∈ active H T S → g R ∈ L ∧ g R ∉ R := by
    intro L hL
    apply (lockingWitness_spec (hg L hL.1)).2 R (hL.2.1.trans hSR)
    intro x hx
    exact (hC.mem_toFinset.mp hx) L hL
  have hmemC : g R ∈ C := fun L hL => (hgood L hL).1
  obtain ⟨L, hL⟩ := hactive
  exact (hgood L hL).2 (hC.mem_toFinset.mpr hmemC)

noncomputable def witnessGenerator [Nonempty α]
    (H : LanguageClass α) (T : Language α → Finset α) (S : Finset α) : α := by
  classical
  exact if h : ∃ x, x ∈ activeCore H T S ∧ x ∉ S then h.choose
  else Classical.choice inferInstance

/-- A witness assignment gives one total function with all required locks. -/
theorem finiteWitnesses_imply_locks [Nonempty α] {H : LanguageClass α}
    (h : HasFiniteWitnesses H) :
    ∃ g : Finset α → α, ∀ L, L ∈ H → Locks g L := by
  classical
  obtain ⟨T, hT, hcore⟩ := h
  refine ⟨witnessGenerator H T, ?_⟩
  intro L hL
  refine ⟨T L, hT L hL, ?_⟩
  intro S hTS hSL
  have hactive : L ∈ active H T S := ⟨hL, hTS, hSL⟩
  have hex : ∃ x, x ∈ activeCore H T S ∧ x ∉ S :=
    (hcore S ⟨L, hactive⟩).exists_notMem_finset S
  simp only [witnessGenerator, dif_pos hex]
  exact ⟨hex.choose_spec.1 L hactive, hex.choose_spec.2⟩

theorem finiteWitnesses_imply_ordinary [Nonempty α] {H : LanguageClass α}
    (h : HasFiniteWitnesses H) : GeneratableInLimit H :=
  setDriven_implies_ordinary (locks_imply_setDriven (finiteWitnesses_imply_locks h))

end GenLimit.FiniteWitness
