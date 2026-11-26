import GenLimit.Paper26_IdentificationWithComputationalTrace.FiniteControl
import GenLimit.Paper26_IdentificationWithComputationalTrace.Indistinguishable

namespace GenLimit.ComputationalTrace.Control

variable {μ O A H : Type} (D : Device μ O A)

def FiniteStates (M : Machine ℕ O A) (Q : Finset ℕ) : Prop :=
  M.initial ∈ Q ∧ ∀ q ∈ Q, ∀ o r a, M.table q o = some (r,a) → r ∈ Q

private theorem states_of_run {M : Machine ℕ O A} {Q : Finset ℕ} (hq : FiniteStates M Q)
    {c ds} (hf : Finish D M c ds) (hc : c.1 ∈ Q) : ∀ e ∈ c :: ds, e.1 ∈ Q := by
  induction hf with
  | halt => simpa using hc
  | @next c d ds _ hm _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hc
    · apply ih _ e he
      unfold move at hm
      cases h : M.table c.1 (D.read c.2) with
      | none => simp [h] at hm
      | some v =>
        simp only [h,Option.map_some,Option.some.injEq] at hm
        subst d
        exact hq.2 _ hc _ _ _ h

/-- Uniformly indistinguishable valid observations on all shared words
suffice for the impossibility result, even for unrestricted hypothesis names. -/
theorem no_learner_of_chain
    (budget : ℕ → List (Frame ℕ μ) → List (Frame ℕ μ) → Prop)
    (machine : Option ℕ → Machine ℕ O A) (word : ℕ → List Bool) (inj : Function.Injective word)
    (noisy : ℕ → List (Frame ℕ μ)) (finite : ∀ i, ∃ Q, FiniteStates (machine i) Q)
    (langs : ∀ i, language D (machine i) = word '' extent i)
    (valid : ∀ i n, n ∈ extent i → ∃ ds, Finish D (machine i) ((machine i).initial,D.load (word n)) ds ∧
      budget (word n).length (((machine i).initial,D.load (word n)) :: ds) (noisy n) ∧
      ∀ e ∈ noisy n, e ∈ ((machine i).initial,D.load (word n)) :: ds)
    (denote : H → Set (List Bool)) (learner : List (Sample μ) → H) :
    ¬ (∀ i s, Presentation D (machine i) budget s → IdentifiesInLimit denote learner s (language D (machine i))) := by
  intro learns
  apply common_noise_obstruction word noisy denote learner
  intro i s hs
  let stream : ℕ → Sample μ := fun n => (word (s n),noisy (s n))
  have hi (n : ℕ) : s n ∈ extent i := hs ▸ ⟨n,rfl⟩
  obtain ⟨Q,hQ⟩ := finite i
  have pres : Presentation D (machine i) budget stream := by
    constructor
    · rw [langs,← hs,← Set.range_comp]
      rfl
    · refine ⟨Q,hQ.1,hQ.2,fun n e he => ?_⟩
      obtain ⟨ds,hf,_,hsub⟩ := valid i _ (hi n)
      exact states_of_run D hQ hf hQ.1 e (hsub e he)
    · intro n
      obtain ⟨ds,hf,he,_⟩ := valid i _ (hi n)
      exact ⟨ds,hf,he⟩
  obtain ⟨g,hg,ht⟩ := learns i _ pres
  refine ⟨g,fun n => ?_,ht⟩
  rw [hg,langs]
  exact inj.mem_set_image

end GenLimit.ComputationalTrace.Control
