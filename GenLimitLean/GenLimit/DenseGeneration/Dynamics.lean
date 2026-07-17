import GenLimit.DenseGeneration.Critical

/-!
# Fixed-scope dynamics of recursive criticality

This module records the local invariants used by the patient-scope state
machine.  Consistency can only be lost as the sample grows.  Nevertheless, if
the current focus remains consistent, then every old critical language in the
same fixed scope remains consistent: the focus is contained in all earlier
critical languages.  The recursive definition of `RecursiveCritical` then
implies that every critical status, and hence the focus, is unchanged in that
scope.

The main results are stated for arbitrary times `t ≤ u`; the one-step version
`fixed_scope_one_step` specializes them to the arrival of one new sample.
-/

namespace GenLimit

/-- Consistency is antitone in time: a candidate consistent with a later
sample was consistent with every earlier sample. -/
theorem consistent_of_time_le
    {C : LanguageFamily} {stream : ℕ → ℕ} {t u i : ℕ}
    (htu : t ≤ u) (h : Consistent C stream u i) :
    Consistent C stream t i := by
  intro x hx
  exact h (sample_mono htu hx)

/-- If a later-indexed old critical language remains consistent, then every
earlier old critical language remains consistent as well.  This is the local
descending-chain argument behind the patient-scope focus invariant.

No ordering assumption on `t` and `u` is needed: the conclusion follows just
from the static inclusion `C f ⊆ C i` and consistency of `f` at `u`. -/
theorem old_critical_consistent_of_later_critical_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {t u i f : ℕ}
    (hif : i ≤ f)
    (hi : RecursiveCritical C stream t i)
    (hf : RecursiveCritical C stream t f)
    (hstay : Consistent C stream u f) :
    Consistent C stream u i := by
  intro x hx
  exact recursiveCritical_subset_of_le hif hi hf (hstay hx)

/-- If every old critical language in a finite scope remains consistent at a
later time, recursive criticality is unchanged throughout that scope.

This lemma isolates the induction on Definition 3.2.  The patient-scope
application below derives `hkeep` from consistency of the old focus. -/
theorem recursiveCritical_iff_of_old_critical_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {t u s : ℕ}
    (htu : t ≤ u)
    (hkeep : ∀ i, i < s → RecursiveCritical C stream t i →
      Consistent C stream u i) :
    ∀ i, i < s →
      (RecursiveCritical C stream u i ↔ RecursiveCritical C stream t i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro his
      cases i with
      | zero =>
          simp only [RecursiveCritical]
          constructor
          · exact consistent_of_time_le htu
          · intro hzero
            exact hkeep 0 his (by simpa only [RecursiveCritical] using hzero)
      | succ n =>
          rw [RecursiveCritical, RecursiveCritical]
          constructor
          · intro hnew
            refine ⟨consistent_of_time_le htu hnew.1, ?_⟩
            intro j hj hjold
            have hji : j < n + 1 := Nat.lt_succ_of_le hj
            have hjs : j < s := lt_trans hji his
            have hjnew : RecursiveCritical C stream u j :=
              (ih j hji hjs).2 hjold
            exact hnew.2 j hj hjnew
          · intro hold
            have hold' : RecursiveCritical C stream t (n + 1) := by
              simpa only [RecursiveCritical] using hold
            refine ⟨hkeep (n + 1) his hold', ?_⟩
            intro j hj hjnew
            have hji : j < n + 1 := Nat.lt_succ_of_le hj
            have hjs : j < s := lt_trans hji his
            have hjold : RecursiveCritical C stream t j :=
              (ih j hji hjs).1 hjnew
            exact hold.2 j hj hjold

/-- If the old focus remains consistent, all old critical languages in its
fixed scope remain consistent. -/
theorem old_critical_in_scope_consistent_of_focus_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {t u s f i : ℕ}
    (hf : IsFocus C stream t s f)
    (hi : i < s)
    (hicrit : RecursiveCritical C stream t i)
    (hstay : Consistent C stream u f) :
    Consistent C stream u i := by
  have hif : i ≤ f := hf.2.2 i hi hicrit
  exact old_critical_consistent_of_later_critical_consistent
    hif hicrit hf.2.1 hstay

/-- Stability of every critical status in a fixed scope when its old focus
remains consistent.  This version permits any later time `u`, not only the
next round. -/
theorem recursiveCritical_iff_of_focus_consistent
    {C : LanguageFamily} {stream : ℕ → ℕ} {t u s f : ℕ}
    (htu : t ≤ u)
    (hf : IsFocus C stream t s f)
    (hstay : Consistent C stream u f) :
    ∀ i, i < s →
      (RecursiveCritical C stream u i ↔ RecursiveCritical C stream t i) := by
  apply recursiveCritical_iff_of_old_critical_consistent htu
  intro i hi hicrit
  exact old_critical_in_scope_consistent_of_focus_consistent
    hf hi hicrit hstay

/-- With a fixed scope, a focus which remains consistent is still the focus at
every later time. -/
theorem isFocus_of_consistent_at_later_time
    {C : LanguageFamily} {stream : ℕ → ℕ} {t u s f : ℕ}
    (htu : t ≤ u)
    (hf : IsFocus C stream t s f)
    (hstay : Consistent C stream u f) :
    IsFocus C stream u s f := by
  have hstable := recursiveCritical_iff_of_focus_consistent htu hf hstay
  refine ⟨hf.1, (hstable f hf.1).2 hf.2.1, ?_⟩
  intro j hjs hjcrit
  exact hf.2.2 j hjs ((hstable j hjs).1 hjcrit)

/-- A fixed finite scope has at most one highest-indexed critical language. -/
theorem isFocus_unique
    {C : LanguageFamily} {stream : ℕ → ℕ} {t s f g : ℕ}
    (hf : IsFocus C stream t s f)
    (hg : IsFocus C stream t s g) : f = g := by
  apply Nat.le_antisymm
  · exact hg.2.2 f hf.1 hf.2.1
  · exact hf.2.2 g hg.1 hg.2.1

/-- One-step fixed-scope invariant.  If the announcement arriving between
times `t` and `t + 1` does not falsify the old focus, then every critical
status in the scope and the focus itself are unchanged. -/
theorem fixed_scope_one_step
    {C : LanguageFamily} {stream : ℕ → ℕ} {t s f : ℕ}
    (hf : IsFocus C stream t s f)
    (hstay : Consistent C stream (t + 1) f) :
    (∀ i, i < s →
        (RecursiveCritical C stream (t + 1) i ↔
          RecursiveCritical C stream t i)) ∧
      IsFocus C stream (t + 1) s f := by
  have htu : t ≤ t + 1 := by omega
  exact ⟨recursiveCritical_iff_of_focus_consistent htu hf hstay,
    isFocus_of_consistent_at_later_time htu hf hstay⟩

end GenLimit
