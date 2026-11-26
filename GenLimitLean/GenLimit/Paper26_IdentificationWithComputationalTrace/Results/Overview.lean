import GenLimit.Paper26_IdentificationWithComputationalTrace.PerfectTrace
import GenLimit.Paper26_IdentificationWithComputationalTrace.DFALearner
import GenLimit.Paper26_IdentificationWithComputationalTrace.PushdownLearner
import GenLimit.Paper26_IdentificationWithComputationalTrace.BlockPDA
import GenLimit.Paper26_IdentificationWithComputationalTrace.UnaryTM
import GenLimit.Paper26_IdentificationWithComputationalTrace.Diminishing

/-! # Main results of Peng, Saberi and Velegkas (ICLR 2026) -/
namespace GenLimit.ComputationalTrace.Results

/-- Theorem 3.1. Accepting configurations identify the language of a deterministic
Turing recognizer. The same finite transition table is output at all late stages. -/
theorem theorem_3_1 {ι : Type*} (code : ι ↪ ℕ) (M : Recognizer) (hM : M.Deterministic)
    (s : ℕ → Example ι) (hs : PerfectPresentation M code s) :
    ∃ H : Recognizer, H.Deterministic ∧ H.language code = M.language code ∧
      ∃ N, ∀ t ≥ N, traceLearner (textPrefix s t) = H :=
  identifies_perfect M hM code s hs

/-- Theorem 4.1. For each known constant rate below one and input-length
threshold there is a single DFA learner that succeeds on every eligible text. -/
theorem theorem_4_1 (rate : ℝ) (hr : 0 < rate ∧ rate < 1) (cutoff : ℕ) :
    ∃ d : ℕ, ∀ (M : BinaryDFA ℕ) (s : ℕ → DFAExample),
      DFAPresentation M rate cutoff s →
      ∃ H : DFAHypothesis, H.product.language = M.language ∧
        ∃ T, ∀ t ≥ T, dfaLearner cutoff d (textPrefix s t) = H :=
  identifies_dfa rate hr.2 cutoff

/-- Theorem 4.3. A known diminishing-rate modulus suffices for binary
deterministic pushdown machines in the paper's empty-stack normal form.
For every positive constant rate, identification can already fail with
input-length threshold one. -/
theorem theorem_4_3 :
    (∀ (cut : ℝ → ℕ) (P : PDA.Program ℕ) (s : ℕ → Control.Sample PDA.Memory),
      Control.Presentation PDA.device P.machine (AllRates cut) s →
        IdentifiesInLimit (fun H : Control.Guess PDA.Observation PDA.Action => H.language PDA.device)
          (PDA.learner (fun d => cut (1 / ((d : ℝ)+2)))) s (Control.language PDA.device P.machine)) ∧
    (∀ rate : ℝ, 0 < rate → ∀ (H : Type) (denote : H → Set (List Bool))
      (learn : List (Control.Sample PDA.Memory) → H),
      ¬ ∀ (P : PDA.Program ℕ) s, Control.Presentation PDA.device P.machine (RateBound rate 1) s →
        IdentifiesInLimit denote learn s (Control.language PDA.device P.machine)) := by
  refine ⟨fun cut P s hs => ?_,fun rate hr _ => PDA.impossible_constant rate hr⟩
  apply PDA.identifies_diminishing
  refine ⟨hs.covers,hs.finiteStates,fun n => ?_⟩
  obtain ⟨ds,hf,he⟩ := hs.traces n
  exact ⟨ds,hf,he.reciprocals⟩

/-- Theorem 4.5. Boundedly many edits on long inputs allow identification.
Even when the learner knows a common modulus for every real error rate,
a diminishing fraction of edits can preclude identification. -/
theorem theorem_4_5 :
    (∀ C cutoff (M : Control.Machine ℕ TM.Observation TM.Action) (s : ℕ → Control.Sample TM.Memory),
      Control.Presentation TM.device M (FiniteBound C cutoff) s →
        IdentifiesInLimit (fun H : Control.Guess TM.Observation TM.Action => H.language TM.device)
          (Control.learner TM.device C cutoff) s (Control.language TM.device M)) ∧
    (∃ cut : ℝ → ℕ, ∀ (H : Type) (denote : H → Set (List Bool))
      (learn : List (Control.Sample TM.Memory) → H),
      ¬ ∀ M s, Control.Presentation TM.device M (AllRates cut) s →
        IdentifiesInLimit denote learn s (Control.language TM.device M)) := by
  refine ⟨TM.identifies_finite,realCutoff (fun d => 2*(d+2)), fun H denote learn h => ?_⟩
  apply TM.impossible_diminishing denote learn
  intro M s hs
  apply h M s
  refine ⟨hs.covers, hs.finiteStates, fun n => ?_⟩
  obtain ⟨ds,hf,he⟩ := hs.traces n
  exact ⟨ds,hf,he.allRates⟩

end GenLimit.ComputationalTrace.Results
