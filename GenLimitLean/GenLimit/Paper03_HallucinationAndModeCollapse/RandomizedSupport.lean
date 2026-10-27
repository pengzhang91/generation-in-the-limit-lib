import GenLimit.Support.RandomBitMachine.Probability
import Mathlib.Computability.PartrecCode

/-!
# Section 6.1: support membership for a total local randomized computation

The machine has computable encoded transitions and a fair binary random tape.
Totality means termination for every input and every tape, not almost-sure
termination. Compactness supplies the missing uniform-bound argument in the
printed proof of Lemma 6.3. The executable search needs no bound as advice.

The code witness is for a fixed supplied computable machine; this module does
not decide which arbitrary machine descriptions satisfy the totality promise.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Support.RandomBitMachine Encodable

/-- Lemma 6.1: an ordinary computable predicate decides positive-probability
finite output of an every-tape terminating local machine. -/
theorem lemma_6_1 (M : Machine) (hM : M.AlwaysHalts) :
    Computable₂ (M.supportDecider hM) ∧
      ∀ input output, M.supportDecider hM input output = true ↔ M.PositiveFiniteOutput input output :=
  ⟨M.supportDecider_computable hM, fun input output =>
    (M.supportDecider_spec hM input output).trans (M.positiveFiniteOutput_iff input output).symm⟩

/-- A stronger execution form of Lemma 6.2: on any tape the complete
small-step trace is finite, so every gap between its coin reads is finite. -/
theorem lemma_6_2 (M : Machine) (hM : M.AlwaysHalts) (input : ℕ) (tape : ℕ → Bool) :
    ∃ n output, M.run input tape n = .inr output ∧
      M.Executes (M.initial input) (M.readTrace (.inl (M.initial input)) (Machine.tapePrefix tape n)) output := by
  obtain ⟨n, output, hn⟩ := hM input tape
  exact ⟨n, output, hn, M.evaluate_executes _ _ _ hn⟩

/-- Lemma 6.3: a finite, tape-independent bound on actual random-bit reads.
In fact the same search gives a bound on the entire padded small-step trace. -/
theorem lemma_6_3 (M : Machine) (hM : M.AlwaysHalts) (input : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧
      (∀ tape, ∃ output, M.run input tape N = .inr output) ∧
      ∀ reads output, M.Executes (M.initial input) reads output → reads.length ≤ N := by
  refine ⟨M.executionBound hM input + 1, by omega, ?_, ?_⟩
  · intro tape
    obtain ⟨output, ho⟩ := (M.allFinished_iff input _).mp (M.executionBound_spec hM input)
      (Machine.tapePrefix tape (M.executionBound hM input)) (by simp [Machine.tapePrefix])
    exact ⟨output, M.run_halted_mono input tape (Nat.le_succ _) ho⟩
  · intro reads output hr
    exact (hr.reads_bounded hM).trans (Nat.le_succ _)

/-- A finite partial-recursive program description for the local support
decider, total on every encoded input/output pair for the supplied machine. -/
theorem randomized_support_has_code (M : Machine) (hM : M.AlwaysHalts) :
    ∃ code : Nat.Partrec.Code, ∀ input output,
      code.eval (encode (input, output)) = Part.some (encode (M.supportDecider hM input output)) := by
  let f : ℕ → ℕ := fun n =>
    let data := (decode (α := ℕ × ℕ) n).getD (0, 0)
    encode (M.supportDecider hM data.1 data.2)
  have hd : Computable (fun n : ℕ => (decode (α := ℕ × ℕ) n).getD (0, 0)) :=
    Computable.option_getD Computable.decode (Computable.const (0, 0))
  have hf : Computable f := Computable.encode.comp
    ((M.supportDecider_computable hM).comp (Computable.fst.comp hd) (Computable.snd.comp hd))
  obtain ⟨code, hc⟩ := Nat.Partrec.Code.exists_code.mp hf.partrec
  exact ⟨code, fun input output => by simpa [f] using congrFun hc (encode (input, output))⟩

end GenLimit.HallucinationModeCollapse
