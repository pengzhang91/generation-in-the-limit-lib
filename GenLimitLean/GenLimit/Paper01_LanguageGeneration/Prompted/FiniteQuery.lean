import GenLimit.Paper01_LanguageGeneration.FiniteQuery.Machine

/-!
# P01 Appendix A.5: finite-query generation under robust constraints

The critical-language selector is exactly the Section 5 selector. Step (iv')
of Appendix A.5 searches the entire finite universe prefix, returning its
least fresh accepted point that satisfies the current Boolean constraint.
This differs from Section 5's endpoint-only test.

Robustness supplies infinitely many matching points in every candidate
language. It is used only to certify termination of `Nat.find`; it is not
tested by the algorithm. The generator receives no target index. The final
stabilization time is uniform over all robust constraint sequences.
-/

namespace GenLimit.KM.Prompted

variable {P : Type*} (O : OracleFamily) (accepts : P → ℕ → Bool)

/-- The current constraint leaves infinitely many points in every language. -/
def Robust (p : P) : Prop :=
  ∀ i, {x | x ∈ O.language i ∧ accepts p x = true}.Infinite

/-- All eligible points in the selected finite prefix, as in step (iv'). -/
def candidates (stream : ℕ → ℕ) (t q : ℕ)
    (h : O.HasConsistent stream t) (p : P) : Finset ℕ :=
  (O.finitePrefix (O.selected stream t q h) q).filter
    (fun x => x ∉ sample stream t ∧ accepts p x = true)

@[simp] theorem mem_candidates
    {stream : ℕ → ℕ} {t q x : ℕ} (h : O.HasConsistent stream t) (p : P) :
    x ∈ candidates O accepts stream t q h p ↔
      x < q ∧ x ∈ O.language (O.selected stream t q h) ∧
        x ∉ sample stream t ∧ accepts p x = true := by
  simp only [candidates, Finset.mem_filter, O.mem_finitePrefix]
  tauto

/-- Robustness and stabilization of the selector imply termination of a round. -/
theorem stop_exists
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t)
    (p : P) (hp : Robust O accepts p) (b : ℕ) :
    ∃ q, b < q ∧ (candidates O accepts stream t q h p).Nonempty := by
  obtain ⟨M, hM⟩ := O.selected_eventually_constant h
  obtain ⟨x, hx, hlarge⟩ :=
    ((hp (O.selected stream t M h)).diff
      (sample stream t).finite_toSet).exists_gt (max b M)
  have hMq : M ≤ x + 1 := by omega
  refine ⟨x + 1, by omega, x, ?_⟩
  apply (mem_candidates O accepts h p).2
  rw [hM (x + 1) hMq]
  exact ⟨Nat.lt_succ_self x, hx.1.1, hx.2, hx.1.2⟩

/-- First successful cutoff strictly after the carried starting cutoff. -/
def roundCounter
    (stream : ℕ → ℕ) (t : ℕ) (h : O.HasConsistent stream t)
    (p : P) (hp : Robust O accepts p) (b : ℕ) : ℕ :=
  Nat.find (stop_exists O accepts h p hp b)

theorem roundCounter_spec
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t)
    (p : P) (hp : Robust O accepts p) (b : ℕ) :
    b < roundCounter O accepts stream t h p hp b ∧
      (candidates O accepts stream t
        (roundCounter O accepts stream t h p hp b) h p).Nonempty :=
  Nat.find_spec (stop_exists O accepts h p hp b)

/-- The finite-prefix search really uses the first successful cutoff. -/
theorem roundCounter_minimal
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t)
    (p : P) (hp : Robust O accepts p) (b q : ℕ)
    (hbq : b < q)
    (hq : (candidates O accepts stream t q h p).Nonempty) :
    roundCounter O accepts stream t h p hp b ≤ q :=
  Nat.find_min' (stop_exists O accepts h p hp b) ⟨hbq, hq⟩

/-- One round. If no candidate is consistent, use the Section 5 fallback. -/
def processRound (stream : ℕ → ℕ) (t : ℕ)
    (p : P) (hp : Robust O accepts p) (b : ℕ) : OracleFamily.MachineState :=
  if h : O.HasConsistent stream t then
    let q := roundCounter O accepts stream t h p hp b
    ⟨q, (candidates O accepts stream t q h p).min'
      (roundCounter_spec O accepts h p hp b).2⟩
  else
    ⟨b, 0⟩

/-- The successful output is the least eligible point, not just an arbitrary
point witnessing termination. -/
theorem processRound_output_minimal
    {stream : ℕ → ℕ} {t : ℕ} (h : O.HasConsistent stream t)
    (p : P) (hp : Robust O accepts p) (b x : ℕ)
    (hx : x ∈ candidates O accepts stream t
      (roundCounter O accepts stream t h p hp b) h p) :
    (processRound O accepts stream t p hp b).output ≤ x := by
  simp only [processRound, dif_pos h]
  exact Finset.min'_le _ x hx

/-- State after `t` observations. Prompt `t` is used in round `t`; round zero
is an initial dummy state. Only the observed prefix and current prompt are
consulted. The robustness certificates are proof arguments. -/
def run (stream : ℕ → ℕ) (prompts : ℕ → P)
    (hrob : ∀ t, Robust O accepts (prompts t)) : ℕ → OracleFamily.MachineState
  | 0 => ⟨0, 0⟩
  | t + 1 =>
      let previous := run stream prompts hrob t
      processRound O accepts stream (t + 1) (prompts (t + 1)) (hrob (t + 1))
        (max previous.counter (stream t + 1))

/-- Robustness proofs cannot influence the generated outputs. -/
theorem run_proof_irrel (stream : ℕ → ℕ) (prompts : ℕ → P)
    (h₁ h₂ : ∀ t, Robust O accepts (prompts t)) :
    run O accepts stream prompts h₁ = run O accepts stream prompts h₂ := by
  rfl

/-- Appendix (A.1): successful-round invariant, with matching and freshness. -/
theorem run_round_spec
    (stream : ℕ → ℕ) (prompts : ℕ → P)
    (hrob : ∀ t, Robust O accepts (prompts t))
    {t : ℕ} (ht : 0 < t) (h : O.HasConsistent stream t) :
    ∃ n, n < t ∧
      FinitelyCritical O.language stream t (run O accepts stream prompts hrob t).counter n ∧
      (∀ j, j < t →
        FinitelyCritical O.language stream t (run O accepts stream prompts hrob t).counter j →
        j ≤ n) ∧
      (run O accepts stream prompts hrob t).output ∈
        O.finitePrefix n (run O accepts stream prompts hrob t).counter ∧
      (run O accepts stream prompts hrob t).output ∉ sample stream t ∧
      accepts (prompts t) (run O accepts stream prompts hrob t).output = true := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  simp only [run, processRound, dif_pos h]
  let b := max (run O accepts stream prompts hrob s).counter (stream s + 1)
  let q := roundCounter O accepts stream (s + 1) h (prompts (s + 1)) (hrob (s + 1)) b
  have hout := (mem_candidates O accepts h (prompts (s + 1))).1
    (Finset.min'_mem (candidates O accepts stream (s + 1) q h (prompts (s + 1)))
      (roundCounter_spec O accepts h (prompts (s + 1)) (hrob (s + 1)) b).2)
  refine ⟨O.selected stream (s + 1) q h, O.selected_lt h,
    O.selected_finitelyCritical h, ?_, ?_, hout.2.2⟩
  · intro j hj hcritical
    exact O.selected_max h hj (O.finitelyCriticalAt_iff.mpr hcritical)
  · exact O.mem_finitePrefix.mpr ⟨hout.1, hout.2.1⟩

def generator (stream : ℕ → ℕ) (prompts : ℕ → P)
    (hrob : ∀ t, Robust O accepts (prompts t)) (t : ℕ) : ℕ :=
  (run O accepts stream prompts hrob t).output

/-- Appendix (A.2), strengthened to make independence of the prompt sequence
explicit: the stabilization threshold depends only on the target presentation. -/
theorem eventual_correctness_uniform
    {stream : ℕ → ℕ} {z : ℕ} (hP : Presents stream (O.language z)) :
    ∃ T, ∀ (prompts : ℕ → P) (hrob : ∀ t, Robust O accepts (prompts t)),
      ∀ t, T ≤ t →
        accepts (prompts t) (generator O accepts stream prompts hrob t) = true ∧
        generator O accepts stream prompts hrob t ∈ O.language z ∧
        generator O accepts stream prompts hrob t ∉ sample stream t := by
  obtain ⟨T, hcritical⟩ := target_eventually_finitelyCritical hP
  refine ⟨max T (z + 1), ?_⟩
  intro prompts hrob t ht
  have hT : T ≤ t := by omega
  have hzt : z < t := by omega
  have hhas : O.HasConsistent stream t :=
    ⟨z, O.mem_consistentCandidates.mpr
      ⟨hzt, O.consistentAt_iff.mpr (presents_consistent hP)⟩⟩
  obtain ⟨n, _, hncritical, hmaximal, hout, hfresh, hmatch⟩ :=
    run_round_spec O accepts stream prompts hrob (by omega) hhas
  have hzcritical := hcritical t hT (run O accepts stream prompts hrob t).counter
  have hnest := finitelyCritical_prefix_subset
    (hmaximal z hzt hzcritical) hzcritical hncritical
  have hout' := O.mem_finitePrefix.mp hout
  exact ⟨hmatch, hnest _ hout'.1 hout'.2, hfresh⟩

end GenLimit.KM.Prompted
