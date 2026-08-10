import GenLimit.Paper31_BoundedMemory.IncrementalIdentification
import Mathlib.Tactic.FinCases

/-!
# Three languages obstruct exact incremental identification

Source: Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas,
*On Language Generation in the Limit with Bounded Memory*,
arXiv:2605.30324v1, Proposition 5.1 and Section 5.1.

This file formalizes the paper's exact three-language obstruction.  The
learner's state space is exactly the three language indices, so there are no
synonym indices or hidden states.  Four finite positive prefixes must leave
the learner in pairwise distinct states: if two states merged, appending the
same repetition-free enumeration of the common infinite core would force
identical future behavior on two different target languages.

The constructed counterexample uses the paper's literal languages

* `C ∪ {1}`,
* `C ∪ {2}`,
* `C ∪ {1, 2}`,

where `C = {3n : n ∈ ℕ}`.  Every adversarial presentation used below is
finitely repeating.  Thus the result proves the stronger final clause of
Proposition 5.1, without a computability or running-time claim.
-/

namespace GenLimit.BoundedMemory

section PrefixStream

variable {α : Type*}

/-- Insert one finite-prefix observation before a shared infinite suffix. -/
def exactPrepend (head : α) (tail : ℕ → α) : ℕ → α
  | 0 => head
  | n + 1 => tail n

@[simp]
private theorem prepend_zero (head : α) (tail : ℕ → α) :
    exactPrepend head tail 0 = head :=
  rfl

@[simp]
private theorem prepend_succ (head : α) (tail : ℕ → α) (n : ℕ) :
    exactPrepend head tail (n + 1) = tail n :=
  rfl

private theorem prepend_presents_insert
    (head : α) {tail : ℕ → α} {K : Set α}
    (htail : GenLimit.Generic.Presents tail K) :
    GenLimit.Generic.Presents (exactPrepend head tail) (insert head K) := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    cases t with
    | zero => exact Set.mem_insert head K
    | succ n =>
        apply Set.mem_insert_of_mem
        rw [← htail]
        exact ⟨n, rfl⟩
  · intro x hx
    rcases hx with rfl | hx
    · exact ⟨0, rfl⟩
    · rw [← htail] at hx
      obtain ⟨n, rfl⟩ := hx
      exact ⟨n + 1, rfl⟩

private theorem prepend_finitelyRepeating
    (head : α) {tail : ℕ → α} (htail : FinitelyRepeating tail) :
    FinitelyRepeating (exactPrepend head tail) := by
  classical
  intro x
  have hSucc :
      ((fun n => n + 1) '' {n | tail n = x}).Finite :=
    (htail x).image _
  apply ((Set.finite_singleton 0).union hSucc).subset
  intro t ht
  cases t with
  | zero => exact Set.mem_union_left _ (Set.mem_singleton 0)
  | succ n =>
      apply Set.mem_union_right
      exact ⟨n, by simpa using ht, rfl⟩

private theorem injective_finitelyRepeating
    {stream : ℕ → α} (hstream : Function.Injective stream) :
    FinitelyRepeating stream := by
  intro x
  have hpre :
      (stream ⁻¹' ({x} : Set α)).Finite :=
    Set.Finite.preimage hstream.injOn (Set.finite_singleton x)
  simpa only [Set.preimage_setOf_eq, Set.mem_singleton_iff] using hpre

end PrefixStream

local notation "prepend" => exactPrepend

section ExactIdentification

variable {α ι : Type*}

/-- Exact convergence of one incremental run to its target index. -/
def ExactlyIdentifiesRun
    (learner : IncrementalLearner α ι) (initial target : ι)
    (stream : ℕ → α) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    incrementalRun learner initial stream t = target

/-- Exact incremental identification on finitely repeating presentations.

For Proposition 5.1 the index type is `Fin 3`, so the learner has exactly
three persistent states, interpreted as the three hypotheses. -/
def IncrementallyExactlyIdentifiableOnFinitelyRepeating
    (langs : ι → Set α) : Prop :=
  ∃ learner : IncrementalLearner α ι,
    ∃ initial,
      ∀ target stream,
        GenLimit.Generic.Presents stream (langs target) →
          FinitelyRepeating stream →
            ExactlyIdentifiesRun learner initial target stream

/-- After one prefixed observation, the rest of an incremental run is the
run from the updated state on the common tail. -/
theorem incrementalRun_prepend
    (learner : IncrementalLearner α ι) (initial : ι)
    (head : α) (tail : ℕ → α) (t : ℕ) :
    incrementalRun learner initial (prepend head tail) (t + 1) =
      incrementalRun learner (learner initial head) tail t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change
        learner
            (incrementalRun learner initial (prepend head tail) (t + 1))
            (tail t) =
          learner
            (incrementalRun learner (learner initial head) tail t)
            (tail t)
      exact congrArg (fun q => learner q (tail t)) ih

/-- If two finite histories reach the same state, a shared infinite suffix
produces identical future states.  Therefore two runs which converge to
different target indices cannot have merged before that suffix. -/
theorem states_distinct_of_aligned_exact_runs
    {learner : IncrementalLearner α ι} {initial state₁ state₂ : ι}
    {tail stream₁ stream₂ : ℕ → α} {offset₁ offset₂ : ℕ}
    {target₁ target₂ : ι}
    (halign₁ : ∀ t,
      incrementalRun learner initial stream₁ (offset₁ + t) =
        incrementalRun learner state₁ tail t)
    (halign₂ : ∀ t,
      incrementalRun learner initial stream₂ (offset₂ + t) =
        incrementalRun learner state₂ tail t)
    (hconv₁ : ExactlyIdentifiesRun learner initial target₁ stream₁)
    (hconv₂ : ExactlyIdentifiesRun learner initial target₂ stream₂)
    (htarget : target₁ ≠ target₂) :
    state₁ ≠ state₂ := by
  intro hstates
  obtain ⟨T₁, hT₁⟩ := hconv₁
  obtain ⟨T₂, hT₂⟩ := hconv₂
  let t := max T₁ T₂
  have hout₁ :
      incrementalRun learner initial stream₁ (offset₁ + t) = target₁ :=
    hT₁ _ (by
      dsimp [t]
      omega)
  have hout₂ :
      incrementalRun learner initial stream₂ (offset₂ + t) = target₂ :=
    hT₂ _ (by
      dsimp [t]
      omega)
  apply htarget
  calc
    target₁ =
        incrementalRun learner initial stream₁ (offset₁ + t) := hout₁.symm
    _ = incrementalRun learner state₁ tail t := halign₁ t
    _ = incrementalRun learner state₂ tail t := by rw [hstates]
    _ = incrementalRun learner initial stream₂ (offset₂ + t) :=
      (halign₂ t).symm
    _ = target₂ := hout₂

end ExactIdentification

section PropositionFiveOne

/-- The common infinite core `C = {3n : n ∈ ℕ}`. -/
def exactObstructionCore : Set ℕ :=
  Set.range fun n : ℕ => 3 * n

/-- The paper's repetition-free canonical enumeration of `C`. -/
def exactObstructionCoreStream (n : ℕ) : ℕ :=
  3 * n

theorem exactObstructionCoreStream_injective :
    Function.Injective exactObstructionCoreStream := by
  intro m n h
  simp only [exactObstructionCoreStream] at h
  omega

theorem exactObstructionCoreStream_presents :
    GenLimit.Generic.Presents
      exactObstructionCoreStream exactObstructionCore :=
  rfl

theorem exactObstructionCoreStream_finitelyRepeating :
    FinitelyRepeating exactObstructionCoreStream :=
  injective_finitelyRepeating exactObstructionCoreStream_injective

theorem exactObstructionCore_infinite :
    exactObstructionCore.Infinite :=
  Set.infinite_range_of_injective exactObstructionCoreStream_injective

@[simp]
theorem one_not_mem_exactObstructionCore :
    1 ∉ exactObstructionCore := by
  rintro ⟨n, hn⟩
  change 3 * n = 1 at hn
  omega

@[simp]
theorem two_not_mem_exactObstructionCore :
    2 ∉ exactObstructionCore := by
  rintro ⟨n, hn⟩
  change 3 * n = 2 at hn
  omega

/-- The three languages in Proposition 5.1, indexed by `Fin 3`. -/
def exactObstructionLanguages : Fin 3 → Set ℕ
  | ⟨0, _⟩ => insert 1 exactObstructionCore
  | ⟨1, _⟩ => insert 2 exactObstructionCore
  | ⟨2, _⟩ => insert 1 (insert 2 exactObstructionCore)

@[simp]
theorem exactObstructionLanguages_zero :
    exactObstructionLanguages 0 = insert 1 exactObstructionCore :=
  rfl

@[simp]
theorem exactObstructionLanguages_one :
    exactObstructionLanguages 1 = insert 2 exactObstructionCore :=
  rfl

@[simp]
theorem exactObstructionLanguages_two :
    exactObstructionLanguages 2 =
      insert 1 (insert 2 exactObstructionCore) :=
  rfl

theorem exactObstructionLanguages_infinite
    (i : Fin 3) :
    (exactObstructionLanguages i).Infinite := by
  apply exactObstructionCore_infinite.mono
  fin_cases i <;> intro x hx <;> simp [hx]

theorem exactObstructionLanguages_injective :
    Function.Injective exactObstructionLanguages := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try rfl
  · have hmem := Set.ext_iff.mp hij 1
    simp at hmem
  · have hmem := Set.ext_iff.mp hij 2
    simp at hmem
  · have hmem := Set.ext_iff.mp hij 1
    simp at hmem
  · have hmem := Set.ext_iff.mp hij 1
    simp at hmem
  · have hmem := Set.ext_iff.mp hij 2
    simp at hmem
  · have hmem := Set.ext_iff.mp hij 1
    simp at hmem

private theorem insert_two_one_core_eq_language_two :
    insert 2 (insert 1 exactObstructionCore) =
      exactObstructionLanguages 2 := by
  ext x
  simp only [exactObstructionLanguages_two, Set.mem_insert_iff]
  constructor
  · rintro (hx | hx | hx)
    · exact Or.inr (Or.inl hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inr hx)
  · rintro (hx | hx | hx)
    · exact Or.inr (Or.inl hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inr hx)

private theorem insert_one_two_one_core_eq_language_two :
    insert 1 (insert 2 (insert 1 exactObstructionCore)) =
      exactObstructionLanguages 2 := by
  ext x
  simp only [exactObstructionLanguages_two, Set.mem_insert_iff]
  constructor
  · rintro (hx | hx | _hx | hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inl _hx
    · exact Or.inr (Or.inr hx)
  · rintro (hx | hx | hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inr hx))

private theorem core_suffix_alignment_one
    (learner : IncrementalLearner ℕ (Fin 3)) (initial : Fin 3)
    (head : ℕ) (t : ℕ) :
    incrementalRun learner initial
        (prepend head exactObstructionCoreStream) (1 + t) =
      incrementalRun learner (learner initial head)
        exactObstructionCoreStream t := by
  simpa [Nat.add_comm] using
    incrementalRun_prepend learner initial head
      exactObstructionCoreStream t

private theorem core_suffix_alignment_two
    (learner : IncrementalLearner ℕ (Fin 3)) (initial : Fin 3)
    (head₁ head₂ : ℕ) (t : ℕ) :
    incrementalRun learner initial
        (prepend head₁ (prepend head₂ exactObstructionCoreStream)) (2 + t) =
      incrementalRun learner (learner (learner initial head₁) head₂)
        exactObstructionCoreStream t := by
  rw [show 2 + t = (t + 1) + 1 by omega,
    incrementalRun_prepend]
  simpa [Nat.add_comm] using
    incrementalRun_prepend learner (learner initial head₁) head₂
      exactObstructionCoreStream t

private theorem exact_run_on_prefixed_core
    {learner : IncrementalLearner ℕ (Fin 3)} {initial target : Fin 3}
    (hident :
      ∀ target stream,
        GenLimit.Generic.Presents stream
            (exactObstructionLanguages target) →
          FinitelyRepeating stream →
            ExactlyIdentifiesRun learner initial target stream)
    {stream : ℕ → ℕ}
    (hP :
      GenLimit.Generic.Presents stream
        (exactObstructionLanguages target))
    (hR : FinitelyRepeating stream) :
    ExactlyIdentifiesRun learner initial target stream :=
  hident target stream hP hR

/-- Proposition 5.1: the literal three-language family cannot be identified
exactly by a last-guess learner whose only states are its three hypothesis
indices.  The obstruction already uses finitely repeating presentations. -/
theorem proposition_5_1 :
    (∀ i, (exactObstructionLanguages i).Infinite) ∧
    Function.Injective exactObstructionLanguages ∧
    ¬IncrementallyExactlyIdentifiableOnFinitelyRepeating
      exactObstructionLanguages := by
  refine ⟨exactObstructionLanguages_infinite,
    exactObstructionLanguages_injective, ?_⟩
  rintro ⟨learner, initial, hident⟩
  let q₀ : Fin 3 := initial
  let q₁ : Fin 3 := learner initial 1
  let q₂ : Fin 3 := learner initial 2
  let q₁₂ : Fin 3 := learner (learner initial 1) 2

  have hCoreRepeat := exactObstructionCoreStream_finitelyRepeating
  have hL₁ :
      GenLimit.Generic.Presents
        (prepend 1 exactObstructionCoreStream)
        (exactObstructionLanguages 0) := by
    simpa using
      prepend_presents_insert 1 exactObstructionCoreStream_presents
  have hL₂ :
      GenLimit.Generic.Presents
        (prepend 2 exactObstructionCoreStream)
        (exactObstructionLanguages 1) := by
    simpa using
      prepend_presents_insert 2 exactObstructionCoreStream_presents
  have hL₃₁₂ :
      GenLimit.Generic.Presents
        (prepend 1 (prepend 2 exactObstructionCoreStream))
        (exactObstructionLanguages 2) := by
    simpa using
      prepend_presents_insert 1
        (prepend_presents_insert 2 exactObstructionCoreStream_presents)
  have hL₃₂₁ :
      GenLimit.Generic.Presents
        (prepend 2 (prepend 1 exactObstructionCoreStream))
        (exactObstructionLanguages 2) := by
    have h :=
      prepend_presents_insert 2
        (prepend_presents_insert 1 exactObstructionCoreStream_presents)
    rw [insert_two_one_core_eq_language_two] at h
    exact h
  have hL₃₁₂₁ :
      GenLimit.Generic.Presents
        (prepend 1
          (prepend 2 (prepend 1 exactObstructionCoreStream)))
        (exactObstructionLanguages 2) := by
    have h :=
      prepend_presents_insert 1
        (prepend_presents_insert 2
          (prepend_presents_insert 1
            exactObstructionCoreStream_presents))
    rw [insert_one_two_one_core_eq_language_two] at h
    exact h

  have hR₁ :
      FinitelyRepeating (prepend 1 exactObstructionCoreStream) :=
    prepend_finitelyRepeating 1 hCoreRepeat
  have hR₂ :
      FinitelyRepeating (prepend 2 exactObstructionCoreStream) :=
    prepend_finitelyRepeating 2 hCoreRepeat
  have hR₁₂ :
      FinitelyRepeating
        (prepend 1 (prepend 2 exactObstructionCoreStream)) :=
    prepend_finitelyRepeating 1
      (prepend_finitelyRepeating 2 hCoreRepeat)
  have hR₂₁ :
      FinitelyRepeating
        (prepend 2 (prepend 1 exactObstructionCoreStream)) :=
    prepend_finitelyRepeating 2
      (prepend_finitelyRepeating 1 hCoreRepeat)
  have hR₁₂₁ :
      FinitelyRepeating
        (prepend 1
          (prepend 2 (prepend 1 exactObstructionCoreStream))) :=
    prepend_finitelyRepeating 1
      (prepend_finitelyRepeating 2
        (prepend_finitelyRepeating 1 hCoreRepeat))

  have hRunL₁ :=
    exact_run_on_prefixed_core hident hL₁ hR₁
  have hRunL₂ :=
    exact_run_on_prefixed_core hident hL₂ hR₂
  have hRunL₃₁₂ :=
    exact_run_on_prefixed_core hident hL₃₁₂ hR₁₂
  have hRunL₃₂₁ :=
    exact_run_on_prefixed_core hident hL₃₂₁ hR₂₁
  have hRunL₃₁₂₁ :=
    exact_run_on_prefixed_core hident hL₃₁₂₁ hR₁₂₁

  have hq₁q₂ : q₁ ≠ q₂ := by
    apply states_distinct_of_aligned_exact_runs
      (learner := learner) (initial := initial)
      (tail := exactObstructionCoreStream)
      (stream₁ := prepend 1 exactObstructionCoreStream)
      (stream₂ := prepend 2 exactObstructionCoreStream)
      (offset₁ := 1) (offset₂ := 1)
      (target₁ := (0 : Fin 3)) (target₂ := (1 : Fin 3))
    · simpa [q₁] using core_suffix_alignment_one learner initial 1
    · simpa [q₂] using core_suffix_alignment_one learner initial 2
    · exact hRunL₁
    · exact hRunL₂
    · decide
  have hq₁q₁₂ : q₁ ≠ q₁₂ := by
    apply states_distinct_of_aligned_exact_runs
      (learner := learner) (initial := initial)
      (tail := exactObstructionCoreStream)
      (stream₁ := prepend 1 exactObstructionCoreStream)
      (stream₂ := prepend 1 (prepend 2 exactObstructionCoreStream))
      (offset₁ := 1) (offset₂ := 2)
      (target₁ := (0 : Fin 3)) (target₂ := (2 : Fin 3))
    · simpa [q₁] using core_suffix_alignment_one learner initial 1
    · simpa [q₁₂] using
        core_suffix_alignment_two learner initial 1 2
    · exact hRunL₁
    · exact hRunL₃₁₂
    · decide
  have hq₂q₁₂ : q₂ ≠ q₁₂ := by
    apply states_distinct_of_aligned_exact_runs
      (learner := learner) (initial := initial)
      (tail := exactObstructionCoreStream)
      (stream₁ := prepend 2 exactObstructionCoreStream)
      (stream₂ := prepend 1 (prepend 2 exactObstructionCoreStream))
      (offset₁ := 1) (offset₂ := 2)
      (target₁ := (1 : Fin 3)) (target₂ := (2 : Fin 3))
    · simpa [q₂] using core_suffix_alignment_one learner initial 2
    · simpa [q₁₂] using
        core_suffix_alignment_two learner initial 1 2
    · exact hRunL₂
    · exact hRunL₃₁₂
    · decide
  have hq₀q₁ : q₀ ≠ q₁ := by
    apply states_distinct_of_aligned_exact_runs
      (learner := learner) (initial := initial)
      (tail := prepend 2 exactObstructionCoreStream)
      (stream₁ := prepend 2 exactObstructionCoreStream)
      (stream₂ := prepend 1 (prepend 2 exactObstructionCoreStream))
      (offset₁ := 0) (offset₂ := 1)
      (target₁ := (1 : Fin 3)) (target₂ := (2 : Fin 3))
    · intro t
      simp [q₀]
    · simpa [q₁, Nat.add_comm] using
        incrementalRun_prepend learner initial 1
          (prepend 2 exactObstructionCoreStream)
    · exact hRunL₂
    · exact hRunL₃₁₂
    · decide
  have hq₀q₂ : q₀ ≠ q₂ := by
    apply states_distinct_of_aligned_exact_runs
      (learner := learner) (initial := initial)
      (tail := prepend 1 exactObstructionCoreStream)
      (stream₁ := prepend 1 exactObstructionCoreStream)
      (stream₂ := prepend 2 (prepend 1 exactObstructionCoreStream))
      (offset₁ := 0) (offset₂ := 1)
      (target₁ := (0 : Fin 3)) (target₂ := (2 : Fin 3))
    · intro t
      simp [q₀]
    · simpa [q₂, Nat.add_comm] using
        incrementalRun_prepend learner initial 2
          (prepend 1 exactObstructionCoreStream)
    · exact hRunL₁
    · exact hRunL₃₂₁
    · decide
  have hq₀q₁₂ : q₀ ≠ q₁₂ := by
    apply states_distinct_of_aligned_exact_runs
      (learner := learner) (initial := initial)
      (tail := prepend 1 exactObstructionCoreStream)
      (stream₁ := prepend 1 exactObstructionCoreStream)
      (stream₂ :=
        prepend 1
          (prepend 2 (prepend 1 exactObstructionCoreStream)))
      (offset₁ := 0) (offset₂ := 2)
      (target₁ := (0 : Fin 3)) (target₂ := (2 : Fin 3))
    · intro t
      simp [q₀]
    · intro t
      rw [show 2 + t = (t + 1) + 1 by omega,
        incrementalRun_prepend]
      simpa [q₁₂, Nat.add_comm] using
        incrementalRun_prepend learner (learner initial 1) 2
          (prepend 1 exactObstructionCoreStream) t
    · exact hRunL₁
    · exact hRunL₃₁₂₁
    · decide

  let fourStates : Fin 4 → Fin 3
    | ⟨0, _⟩ => q₀
    | ⟨1, _⟩ => q₁
    | ⟨2, _⟩ => q₂
    | ⟨3, _⟩ => q₁₂
  have hFourStates : Function.Injective fourStates := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals simp_all [fourStates]
  have hcard := Fintype.card_le_of_injective fourStates hFourStates
  simp at hcard

end PropositionFiveOne

end GenLimit.BoundedMemory
