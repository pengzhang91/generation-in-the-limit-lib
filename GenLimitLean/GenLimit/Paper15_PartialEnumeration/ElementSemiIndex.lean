import GenLimit.Paper15_PartialEnumeration.SemiIndex

/-!
# Lemma 2.3: element/semi-index generation equivalence

This file kernel-checks the generation-in-the-limit part of Lemma 2.3 in
Kleinberg--Wei, *Language Generation and Identification From Partial
Enumeration* (arXiv:2511.05295v1).

For the forward reduction, an element trace `output` is converted at time
`t` into the finite set of the first `s ≤ t` candidate indices which

* are consistent with the observations before `t`, and
* contain `output t`,

where `s` is the largest visible scope whose resulting intersection is
infinite.  The empty scope is always available.  Once `output` is valid and
consistency has stabilized through the true index, the selected semi-index
contains the true index.  Its intersection is therefore a subset of the true
language.

For the reverse reduction, an infinite semi-index intersection supplies an
element outside the finite observed sample.  This is the semantic,
noncomputable interpretation used throughout the partial-enumeration
development; no decidability of infinitude is assumed.

The separate density-optimality sentence in Lemma 2.3 is not asserted here:
the source does not define an output set for a set-valued semi-index trace,
so an ordered-density comparison first needs an explicit coupling.
-/

namespace GenLimit
namespace KleinbergWei
namespace PartialEnumeration

/-- Pathwise element-based generation in the partial-enumeration model.
Every output is fresh from the observed prefix, and outputs are eventually in
the true language. -/
def ElementTraceGenerates
    (C : LanguageFamily) (stream output : ℕ → ℕ) (z : ℕ) : Prop :=
  (∀ t, output t ∉ sample stream t) ∧
    ∃ T, ∀ t, T ≤ t → output t ∈ C z

/-- Pathwise semi-index generation.  Each finite conjunction has infinite
intersection, and the intersections are eventually contained in the true
language. -/
def SemiIndexTraceGenerates
    (C : LanguageFamily) (indices : ℕ → Finset ℕ) (z : ℕ) : Prop :=
  (∀ t, (intersectionOf C (indices t)).Infinite) ∧
    ∃ T, ∀ t, T ≤ t → intersectionOf C (indices t) ⊆ C z

/-- The candidate intersection used in the element-to-semi-index reduction,
before the largest infinite scope is selected. -/
def elementPrefixIntersection
    (C : LanguageFamily) (stream output : ℕ → ℕ) (t s : ℕ) : Language :=
  {u | ∀ i, i < s →
    Consistent C stream t i → output t ∈ C i → u ∈ C i}

@[simp] theorem elementPrefixIntersection_zero
    (C : LanguageFamily) (stream output : ℕ → ℕ) (t : ℕ) :
    elementPrefixIntersection C stream output t 0 = Set.univ := by
  ext u
  simp [elementPrefixIntersection]

/-- The visible scopes `s ≤ t` whose candidate intersection is infinite.
Using `s ≤ t` gives the source's bound of at most `t` indices (with Lean time
starting at zero). -/
noncomputable def elementAdmissibleScopes
    (C : LanguageFamily) (stream output : ℕ → ℕ) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (t + 1)).filter fun s =>
    (elementPrefixIntersection C stream output t s).Infinite

@[simp] theorem mem_elementAdmissibleScopes
    {C : LanguageFamily} {stream output : ℕ → ℕ} {t s : ℕ} :
    s ∈ elementAdmissibleScopes C stream output t ↔
      s ≤ t ∧ (elementPrefixIntersection C stream output t s).Infinite := by
  classical
  simp [elementAdmissibleScopes, Nat.lt_succ_iff]

theorem zero_mem_elementAdmissibleScopes
    (C : LanguageFamily) (stream output : ℕ → ℕ) (t : ℕ) :
    0 ∈ elementAdmissibleScopes C stream output t := by
  classical
  simp [Set.infinite_univ]

/-- Largest visible scope with infinite intersection. -/
noncomputable def elementSelectedScope
    (C : LanguageFamily) (stream output : ℕ → ℕ) (t : ℕ) : ℕ := by
  classical
  let S := elementAdmissibleScopes C stream output t
  exact S.max' ⟨0, zero_mem_elementAdmissibleScopes C stream output t⟩

theorem elementSelectedScope_mem
    (C : LanguageFamily) (stream output : ℕ → ℕ) (t : ℕ) :
    elementSelectedScope C stream output t ∈
      elementAdmissibleScopes C stream output t := by
  classical
  let S := elementAdmissibleScopes C stream output t
  simpa [elementSelectedScope, S] using
    Finset.max'_mem S
      ⟨0, zero_mem_elementAdmissibleScopes C stream output t⟩

theorem le_elementSelectedScope_of_admissible
    {C : LanguageFamily} {stream output : ℕ → ℕ} {t s : ℕ}
    (hs : s ∈ elementAdmissibleScopes C stream output t) :
    s ≤ elementSelectedScope C stream output t := by
  classical
  let S := elementAdmissibleScopes C stream output t
  simpa [elementSelectedScope, S] using Finset.le_max' S s (by
    simpa [S] using hs)

/-- The finite semi-index produced from an element output at time `t`. -/
noncomputable def elementSemiIndex
    (C : LanguageFamily) (stream output : ℕ → ℕ) (t : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (elementSelectedScope C stream output t)).filter
    fun i => Consistent C stream t i ∧ output t ∈ C i

@[simp] theorem mem_elementSemiIndex
    {C : LanguageFamily} {stream output : ℕ → ℕ} {t i : ℕ} :
    i ∈ elementSemiIndex C stream output t ↔
      i < elementSelectedScope C stream output t ∧
        Consistent C stream t i ∧ output t ∈ C i := by
  classical
  simp [elementSemiIndex]

theorem intersectionOf_elementSemiIndex
    (C : LanguageFamily) (stream output : ℕ → ℕ) (t : ℕ) :
    intersectionOf C (elementSemiIndex C stream output t) =
      elementPrefixIntersection C stream output t
        (elementSelectedScope C stream output t) := by
  ext u
  constructor
  · intro hu i hi hconsistent hout
    exact hu i (mem_elementSemiIndex.mpr
      ⟨hi, hconsistent, hout⟩)
  · intro hu i hi
    obtain ⟨hiscope, hconsistent, hout⟩ :=
      mem_elementSemiIndex.mp hi
    exact hu i hiscope hconsistent hout

theorem elementSemiIndex_intersection_infinite
    (C : LanguageFamily) (stream output : ℕ → ℕ) (t : ℕ) :
    (intersectionOf C (elementSemiIndex C stream output t)).Infinite := by
  rw [intersectionOf_elementSemiIndex]
  exact (mem_elementAdmissibleScopes.mp
    (elementSelectedScope_mem C stream output t)).2

/-- The forward reduction uses at most `t` indices at Lean time `t`. -/
theorem elementSemiIndex_card_le_time
    (C : LanguageFamily) (stream output : ℕ → ℕ) (t : ℕ) :
    (elementSemiIndex C stream output t).card ≤ t := by
  classical
  calc
    (elementSemiIndex C stream output t).card
        ≤ (Finset.range
            (elementSelectedScope C stream output t)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = elementSelectedScope C stream output t := Finset.card_range _
    _ ≤ t := (mem_elementAdmissibleScopes.mp
      (elementSelectedScope_mem C stream output t)).1

theorem elementPrefixIntersection_infinite_of_stable
    {C : LanguageFamily} {stream output : ℕ → ℕ}
    {E : Language} {t s : ℕ}
    (hE : E.Infinite)
    (hstable : ∀ i, i < s →
      (Consistent C stream t i ↔ E ⊆ C i)) :
    (elementPrefixIntersection C stream output t s).Infinite := by
  apply hE.mono
  intro u hu i hi hconsistent _
  exact (hstable i hi).mp hconsistent hu

/-- Once the element trace is valid and the finite consistency prefix has
stabilized, the transformed semi-index contains the true family index. -/
theorem elementSemiIndex_eventually_contains_target
    {C : LanguageFamily} {stream output : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z)
    (hout : ∃ T, ∀ t, T ≤ t → output t ∈ C z) :
    ∃ T, ∀ t, T ≤ t → z ∈ elementSemiIndex C stream output t := by
  obtain ⟨Ts, hstable⟩ :=
    finite_scope_eventually_consistent_iff_presented_subset
      (C := C) (stream := stream) (E := E) hP (z + 1)
  obtain ⟨To, hout⟩ := hout
  refine ⟨max (max Ts To) (z + 1), ?_⟩
  intro t ht
  have htTs : Ts ≤ t :=
    le_trans (Nat.le_max_left Ts To)
      (le_trans (Nat.le_max_left (max Ts To) (z + 1)) ht)
  have htTo : To ≤ t :=
    le_trans (Nat.le_max_right Ts To)
      (le_trans (Nat.le_max_left (max Ts To) (z + 1)) ht)
  have hzt : z + 1 ≤ t :=
    le_trans (Nat.le_max_right (max Ts To) (z + 1)) ht
  have hinfinite :
      (elementPrefixIntersection C stream output t (z + 1)).Infinite :=
    elementPrefixIntersection_infinite_of_stable hE (hstable t htTs)
  have hadmissible :
      z + 1 ∈ elementAdmissibleScopes C stream output t :=
    mem_elementAdmissibleScopes.mpr ⟨hzt, hinfinite⟩
  have hzscope : z < elementSelectedScope C stream output t := by
    have hle := le_elementSelectedScope_of_admissible hadmissible
    omega
  exact mem_elementSemiIndex.mpr
    ⟨hzscope, consistent_of_presented_subset hP hEz, hout t htTo⟩

/-- Lemma 2.3, forward generation direction: an eventually valid element
trace gives a semi-index trace with infinite intersections, eventual
validity, and the source's at-most-`t` size bound. -/
theorem lemma_2_3_element_to_semiIndex
    {C : LanguageFamily} {stream output : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z)
    (hgenerate : ElementTraceGenerates C stream output z) :
    SemiIndexTraceGenerates C
        (elementSemiIndex C stream output) z ∧
      ∀ t, (elementSemiIndex C stream output t).card ≤ t := by
  refine ⟨⟨elementSemiIndex_intersection_infinite C stream output, ?_⟩,
    elementSemiIndex_card_le_time C stream output⟩
  obtain ⟨T, htarget⟩ :=
    elementSemiIndex_eventually_contains_target
      hP hE hEz hgenerate.2
  refine ⟨T, ?_⟩
  intro t ht u hu
  exact hu z (htarget t ht)

/-- A fresh element selected from the infinite intersection named by a
semi-index trace. -/
noncomputable def semiIndexFreshOutput
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (indices : ℕ → Finset ℕ)
    (hinfinite : ∀ t, (intersectionOf C (indices t)).Infinite)
    (t : ℕ) : ℕ :=
  Classical.choose
    ((hinfinite t).exists_notMem_finset (sample stream t))

theorem semiIndexFreshOutput_spec
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (indices : ℕ → Finset ℕ)
    (hinfinite : ∀ t, (intersectionOf C (indices t)).Infinite)
    (t : ℕ) :
    semiIndexFreshOutput C stream indices hinfinite t ∈
        intersectionOf C (indices t) ∧
      semiIndexFreshOutput C stream indices hinfinite t ∉
        sample stream t :=
  Classical.choose_spec
    ((hinfinite t).exists_notMem_finset (sample stream t))

/-- Lemma 2.3, reverse generation direction: an eventually valid semi-index
trace gives a fresh element trace that is eventually valid. -/
theorem lemma_2_3_semiIndex_to_element
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {indices : ℕ → Finset ℕ} {z : ℕ}
    (hgenerate : SemiIndexTraceGenerates C indices z) :
    ElementTraceGenerates C stream
      (semiIndexFreshOutput C stream indices hgenerate.1) z := by
  refine ⟨fun t => (semiIndexFreshOutput_spec
    C stream indices hgenerate.1 t).2, ?_⟩
  obtain ⟨T, hvalid⟩ := hgenerate.2
  refine ⟨T, ?_⟩
  intro t ht
  exact hvalid t ht
    (semiIndexFreshOutput_spec C stream indices hgenerate.1 t).1

/-- Lemma 2.3's pathwise generation equivalence, separated from its
under-specified density-optimality sentence. -/
theorem lemma_2_3_generation_equivalence
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {E : Language} {z : ℕ}
    (hP : Presents stream E)
    (hE : E.Infinite)
    (hEz : E ⊆ C z) :
    (∃ output, ElementTraceGenerates C stream output z) ↔
      ∃ indices, SemiIndexTraceGenerates C indices z := by
  constructor
  · rintro ⟨output, houtput⟩
    exact ⟨elementSemiIndex C stream output,
      (lemma_2_3_element_to_semiIndex hP hE hEz houtput).1⟩
  · rintro ⟨indices, hindices⟩
    exact ⟨semiIndexFreshOutput C stream indices hindices.1,
      lemma_2_3_semiIndex_to_element hindices⟩

end PartialEnumeration
end KleinbergWei
end GenLimit
