import GenLimit.Paper00A_PositiveDataInference.Effective.Definitions
import Mathlib.Computability.PartrecCode

/-!
# Effective machines with request and guess events

A position consists of the data already read and the number of guesses already
issued since the most recent request. Evaluating a position returns the next
observable event (a guess or a request), or runs forever. One can implement
this representation by replaying a deterministic source machine on the finite
input, stopping at the indicated event. Conversely one runs the partial
procedure at successive positions, incrementing the guess count or reading
one datum and resetting the count. The two prefix laws ensure every reported
event is reachable in this execution.
-/

namespace GenLimit.Angluin

/-- The effective next event at each reachable position in a positive-data run. -/
structure InferenceMachine where
  event : List ℕ → ℕ →. Option ℕ
  effective : Partrec₂ event
  previous_guess : ∀ {h k a}, a ∈ event h (k + 1) → ∃ j, some j ∈ event h k
  previous_request : ∀ {h x k a}, a ∈ event (h ++ [x]) k → ∃ l, none ∈ event h l

namespace InferenceMachine

/-- A guess made after reading exactly `n` examples, at offset `k` in that block. -/
def Guesses (M : InferenceMachine) (s : ℕ → ℕ) (n k j : ℕ) : Prop :=
  some j ∈ M.event (textPrefix s n) k

/-- Event positions in chronological order, including multiple guesses
without any intervening request. -/
def Earlier (n k m l : ℕ) : Prop := n < m ∨ n = m ∧ k < l

/-- A correct guess is actually issued, and every subsequent guess has
the same index. This includes a finite sequence ending in a correct guess. -/
def Identifies (M : InferenceMachine) (F : EffectiveIndexedFamily) : Prop :=
  ∀ i s, Generic.Presents s (F.language i) →
    ∃ n k j, M.Guesses s n k j ∧ F.language j = F.language i ∧
      ∀ m l g, Earlier n k m l → M.Guesses s m l g → g = j

def Conservative (M : InferenceMachine) (F : EffectiveIndexedFamily) : Prop :=
  ∀ i s, Generic.Presents s (F.language i) →
    ∀ n k j m l g, Earlier n k m l → M.Guesses s n k j →
      M.Guesses s m l g → g ≠ j → ∃ t < m, s t ∉ F.language j

def Consistent (M : InferenceMachine) (F : EffectiveIndexedFamily) : Prop :=
  ∀ i s, Generic.Presents s (F.language i) →
    ∀ n k j, M.Guesses s n k j → ∀ t < n, s t ∈ F.language j

/-- Between any two consecutive requests at least one guess is issued. -/
def Responsive (M : InferenceMachine) (F : EffectiveIndexedFamily) : Prop :=
  ∀ i s, Generic.Presents s (F.language i) →
    ∀ n k, none ∈ M.event (textPrefix s (n + 1)) k → 0 < k

/-- A single partial recursive code enumerates the actual guesses at every
observable position. A request or divergence contributes no guess. -/
theorem exists_guess_code (M : InferenceMachine) :
    ∃ e : Nat.Partrec.Code, ∀ (h : List ℕ) (k j : ℕ),
      j ∈ e.eval (Encodable.encode (h, k)) ↔ some j ∈ M.event h k := by
  have hg : Partrec (fun p : List ℕ × ℕ => (M.event p.1 p.2).bind Part.ofOption) :=
    M.effective.bind (Computable.snd.ofOption.to₂)
  obtain ⟨e, he⟩ := Nat.Partrec.Code.exists_code.mp hg
  refine ⟨e, fun h k j => ?_⟩
  rw [he]
  simp [Part.mem_bind_iff, eq_comm]

/-- Run an ordinary computable prefix learner as a machine that alternates
one guess and one request. -/
def ofIdentifier (learner : EffectiveIdentifier) (hc : Computable learner) : InferenceMachine where
  event h k := Part.ofOption (bif k == 0 then some (some (learner h))
    else bif k == 1 then some none else none)
  effective := ((Primrec.beq.to_comp.comp Computable.snd (Computable.const 0)).cond
    (Computable.option_some.comp (Computable.option_some.comp (hc.comp Computable.fst)))
    ((Primrec.beq.to_comp.comp Computable.snd (Computable.const 1)).cond
      (Computable.const (some none)) (Computable.const none))).ofOption.to₂
  previous_guess := by
    intro h k a ha
    cases k with
    | zero => exact ⟨learner h, by simp⟩
    | succ k => simp at ha
  previous_request := by intros; exact ⟨1, by simp⟩

theorem ofIdentifier_identifies {learner : EffectiveIdentifier} {F : EffectiveIndexedFamily}
    (hc : Computable learner) (hid : SemanticallyIdentifies learner F.language) :
    (ofIdentifier learner hc).Identifies F := by
  intro i s hp
  obtain ⟨j, hj, N, hN⟩ := hid i s hp
  refine ⟨N, 0, j, ?_, hj, ?_⟩
  · simpa [Guesses, ofIdentifier] using (hN N le_rfl).symm
  · intro m l g he hg
    have hle : N ≤ m := by rcases he with h | h <;> omega
    cases l with
    | zero => simpa [Guesses, ofIdentifier, hN m hle] using hg
    | succ l => cases l <;> simp [Guesses, ofIdentifier] at hg

/-- If the entire presentation is compatible with a conjecture already
issued, a conservative successful machine must have guessed the target. -/
theorem correct_of_compatible_guess {M : InferenceMachine} {F : EffectiveIndexedFamily}
    (hid : M.Identifies F) (hcons : M.Conservative F) {i s n k j}
    (hp : Generic.Presents s (F.language i)) (hg : M.Guesses s n k j)
    (hsub : F.language i ⊆ F.language j) : F.language j = F.language i := by
  obtain ⟨m, l, g, hg', heq, hstable⟩ := hid i s hp
  suffices j = g by rwa [this]
  by_contra hne
  by_cases hfirst : Earlier n k m l
  · obtain ⟨t, _, ht⟩ := hcons i s hp n k j m l g hfirst hg hg' (Ne.symm hne)
    exact ht (hsub (hp ▸ Set.mem_range_self t : s t ∈ F.language i))
  · by_cases hlast : Earlier m l n k
    · exact hne (hstable _ _ _ hlast hg)
    · simp only [Earlier] at hfirst hlast
      obtain rfl : m = n := by omega
      obtain rfl : l = k := by omega
      exact hne (Option.some.inj (Part.mem_unique hg hg'))

end InferenceMachine

end GenLimit.Angluin
