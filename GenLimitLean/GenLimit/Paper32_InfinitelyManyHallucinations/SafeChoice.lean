import GenLimit.Paper15_PartialEnumeration.FiniteScope
import GenLimit.Paper32_InfinitelyManyHallucinations.SingleStepInput

/-! # A safe choice outside a finite set in the partial-exhaustion model -/

namespace GenLimit.InfinitelyManyHallucinations

open Set KleinbergWei.PartialEnumeration

private theorem intersection_prefix {C : LanguageFamily} {s d : ℕ → ℕ} {t : ℕ}
    (h : ∀ i ≤ t, s i = d i) : selectedIntersection C s t = selectedIntersection C d t := by
  have hs : sample s t = sample d t := Finset.image_congr (fun i hi => h i (Finset.mem_range.mp hi).le)
  have hc (j) : prefixIntersection C s t j = prefixIntersection C d t j := by
    simp only [prefixIntersection, Consistent, hs]
  have ha : admissibleScopes C s t = admissibleScopes C d t := by
    ext j
    simp only [mem_admissibleScopes, hc]
  have hl : selectedScope C s t = selectedScope C d t := by
    simp only [selectedScope, ha]
  simp only [selectedIntersection, hl, hc]

private noncomputable def safeSet (C : LanguageFamily) (A : Exhaustion) (t : ℕ) : Language :=
  if (A.stage (t+1)).Nonempty then selectedIntersection C A.inputWord t else Set.univ

private theorem safeSet_infinite (C : LanguageFamily) (A : Exhaustion) (t : ℕ) :
    (safeSet C A t).Infinite := by
  unfold safeSet
  split
  · exact selectedIntersection_infinite C A.inputWord t
  · exact Set.infinite_univ

private theorem safeSet_prefix {C : LanguageFamily} {A B : Exhaustion} {t : ℕ}
    (h : ∀ i ≤ t+1, A.stage i = B.stage i) : safeSet C A t = safeSet C B t := by
  by_cases ha : (A.stage (t+1)).Nonempty
  · simp only [safeSet, ← h _ le_rfl, if_pos ha]
    exact intersection_prefix (Exhaustion.inputWord_prefix h ha)
  · simp [safeSet, ← h _ le_rfl, ha]

private noncomputable def freshIn (S : Language) (hi : S.Infinite) (blocked : Finset ℕ) :=
  (hi.diff blocked.finite_toSet).nonempty.choose

private theorem freshIn_spec (S : Language) (hi : S.Infinite) (blocked : Finset ℕ) :
    freshIn S hi blocked ∈ S ∧ freshIn S hi blocked ∉ blocked :=
  (hi.diff blocked.finite_toSet).nonempty.choose_spec

noncomputable def safeChoice (C : LanguageFamily) (A : Exhaustion) (t : ℕ) (prev : Finset ℕ) :=
  freshIn (safeSet C A t) (safeSet_infinite C A t) (A.stage (t+1) ∪ prev)

theorem safeChoice_fresh (C : LanguageFamily) (A : Exhaustion) (t : ℕ) (prev : Finset ℕ) :
    safeChoice C A t prev ∉ A.stage (t+1) ∪ prev := (freshIn_spec ..).2

theorem safeChoice_prefix {C : LanguageFamily} {A B : Exhaustion} {t : ℕ}
    (h : ∀ i ≤ t+1, A.stage i = B.stage i) (prev : Finset ℕ) :
    safeChoice C A t prev = safeChoice C B t prev := by
  simp only [safeChoice, safeSet_prefix (C := C) h, h _ le_rfl]

theorem safeChoice_eventual {C : LanguageFamily} {A : Exhaustion} {z : ℕ}
    (single : A.IsSingleStep) (hi : A.limit.Infinite) (hs : A.limit ⊆ C z) :
    ∃ T, ∀ t ≥ T, ∀ prev, safeChoice C A t prev ∈ C z := by
  obtain ⟨T,hT⟩ := selectedIntersection_eventually_subset_target
    (Exhaustion.inputWord_presents single hi.nonempty) hi hs
  obtain ⟨x,m,hm⟩ := hi.nonempty
  refine ⟨max T m,fun t ht prev => hT t ((le_max_left ..).trans ht) ?_⟩
  have hnow : (A.stage (t+1)).Nonempty := ⟨x,A.monotone_stage (by omega) hm⟩
  have hm := (freshIn_spec (safeSet C A t) (safeSet_infinite C A t) (A.stage (t+1) ∪ prev)).1
  simpa only [safeChoice, safeSet, if_pos hnow] using hm

end GenLimit.InfinitelyManyHallucinations
