import GenLimit.Paper15_PartialEnumeration.Deletion
import Mathlib.Topology.Separation.Basic

/-! # The printed partial-text topology and Theorem 4.12

For a fixed partial text set C, all languages containing C have identical
neighborhoods. Every other language has an open singleton, and each
container has a basic neighborhood excluding any given noncontainer. Thus the
Kolmogorov quotient is always T₁. The countable class consisting of the whole
universe and its one-point deletions fails partial identification. -/

namespace GenLimit.KleinbergWei.PartialEnumeration.PartialTopology
open Set Filter
open scoped Topology

noncomputable def basic {X : Set Language} (C : Language) (L : X) (F : Finset ℕ) : Set X := by
  classical
  exact if C ⊆ L.val then {K | (↑F : Set ℕ) ⊆ K.val ∧ (K.val ∩ C).Infinite} else {L}

def generators (X : Set Language) (C : Language) : Set (Set X) :=
  {O | ∃ (L : X) (F : Finset ℕ), (↑F : Set ℕ) ⊆ C ∧ O = basic C L F}

def topology (X : Set Language) (C : Language) : TopologicalSpace X :=
  TopologicalSpace.generateFrom (generators X C)

private theorem containers {X : Set Language} {C : Language} (hi : C.Infinite)
    {x y : X} (hx : C ⊆ x.val) (hy : C ⊆ y.val) :
    @Specializes X (topology X C) x y := by
  classical
  letI := topology X C
  apply specializes_iff_forall_open.mpr
  intro O hO
  change TopologicalSpace.GenerateOpen (generators X C) O at hO
  induction hO with
  | basic O h =>
    obtain ⟨L,F,hF,rfl⟩ := h
    by_cases hL : C ⊆ L.val
    · intro _
      rw [basic,if_pos hL]
      exact ⟨hF.trans hx,hi.mono (fun _ h ↦ ⟨hx h,h⟩)⟩
    · rw [basic,if_neg hL]
      rintro (rfl : y = L)
      exact (hL hy).elim
  | univ => exact fun _ ↦ trivial
  | inter s t _ _ ih jh => exact fun h ↦ ⟨ih h.1,jh h.2⟩
  | sUnion S _ ih =>
    rintro ⟨U,hU,hyU⟩
    exact ⟨U,hU,ih U hU hyU⟩

theorem r0 (X : Set Language) (C : Language) (hi : C.Infinite) :
    @R0Space X (topology X C) := by
  classical
  letI := topology X C
  have hopen (L : X) (F : Finset ℕ) (hF : (↑F : Set ℕ) ⊆ C) : IsOpen (basic C L F) :=
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨L,F,hF,rfl⟩
  constructor
  intro x y h
  by_cases hy : C ⊆ y.val
  · by_cases hx : C ⊆ x.val
    · exact containers hi hy hx
    · obtain ⟨a,ha,hax⟩ := Set.not_subset.mp hx
      have hu := hopen y {a} (by simpa using ha)
      have hmem : y ∈ basic C y {a} := by
        rw [basic,if_pos hy]
        exact ⟨by simpa using hy ha,hi.mono (fun _ hc ↦ ⟨hy hc,hc⟩)⟩
      have hh := h.mem_open hu hmem
      rw [basic,if_pos hy] at hh
      exact (hax (hh.1 (Finset.mem_singleton_self a))).elim
  · have hu := hopen y ∅ (by simp)
    rw [basic,if_neg hy] at hu
    have he : x = y := h.mem_open hu (Set.mem_singleton y)
    subst x
    exact specializes_rfl

/-- The quotient required by the source satisfies the stronger T₁ property
for every class and infinite observed set. -/
theorem quotient_t1 (X : Set Language) (C : Language) (hi : C.Infinite) :
    letI := topology X C
    T1Space (SeparationQuotient X) := by
  letI := topology X C
  exact SeparationQuotient.t1Space_iff.mpr (r0 X C hi)

/-- The derived set of each singleton is closed (the T_D condition). -/
def QuotientTD (X : Set Language) (C : Language) : Prop :=
  letI := topology X C
  ∀ a : SeparationQuotient X, IsClosed (closure ({a} : Set _) \ {a})

theorem quotient_td (X : Set Language) (C : Language) (hi : C.Infinite) : QuotientTD X C := by
  letI := topology X C
  letI := quotient_t1 X C hi
  intro a
  rw [isClosed_singleton.closure_eq,Set.diff_self]
  exact isClosed_empty

def coSingleClass : Set Language :=
  insert Set.univ (Set.range (fun a : ℕ ↦ ({a} : Language)ᶜ))

theorem coSingle_countable : coSingleClass.Countable := (Set.countable_range _).insert _

theorem coSingle_infinite (L : Language) (h : L ∈ coSingleClass) : L.Infinite := by
  rcases h with rfl | ⟨a,rfl⟩
  · exact Set.infinite_univ
  · exact (Set.finite_singleton a).infinite_compl

theorem coSingle_not_identifiable : ¬ PartialIdentifiable coSingleClass := by
  rintro ⟨A,hA⟩
  have full : Angluin.ExtensionallyIdentifiable coSingleClass := by
    refine ⟨A,fun L hL s hs ↦ ⟨L,rfl,?_⟩⟩
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hA L hL L s (coSingle_infinite L hL) Subset.rfl hs)
    exact ⟨N,fun n hn ↦ (hN n hn).2.antisymm (hN n hn).1⟩
  have tell := (Angluin.countable_extensionallyIdentifiable_iff_extensionalTellTaleCondition
    coSingle_countable).mp full
  obtain ⟨T,_,ht⟩ := tell Set.univ (Set.mem_insert _ _)
  obtain ⟨a,ha⟩ := T.exists_notMem
  have hT : (↑T : Set ℕ) ⊆ ({a} : Language)ᶜ := by
    intro x hx he
    exact ha ((Set.mem_singleton_iff.mp he) ▸ hx)
  have h := ht _ (Set.mem_insert_of_mem _ ⟨a,rfl⟩) hT (Set.subset_univ _)
  exact h (Set.mem_univ a) (Set.mem_singleton a)

/-- Negation of the biconditional in Theorem 4.12 / 1.10 under the
displayed basic opens, witnessed by a countable class of infinite languages. -/
theorem not_theorem_4_12 :
    ¬ (PartialIdentifiable coSingleClass ↔
      ∀ L ∈ coSingleClass, ∀ C : Language, C.Infinite → C ⊆ L → QuotientTD coSingleClass C) :=
  fun h ↦ coSingle_not_identifiable (h.mpr (fun _ _ C hi _ ↦ quotient_td _ C hi))

end GenLimit.KleinbergWei.PartialEnumeration.PartialTopology
