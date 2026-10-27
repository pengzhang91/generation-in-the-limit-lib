import GenLimit.Support.RandomBitMachine.Semantics
import GenLimit.Support.DiscreteIID

/-!
# Positive-probability execution and normalized local output laws

Finite independent fair-bit words have full support. Thus a completed output
has positive finite-execution probability exactly when it is operationally
possible. For an every-tape terminating machine, the computed finite bound
also defines a normalized output PMF with exactly that support.
-/

namespace GenLimit.Support.RandomBitMachine.Machine

open GenLimit.DiscreteIID

noncomputable def fairCoin : PMF Bool := PMF.bernoulli (1 / 2) (by norm_num)

theorem fairCoin_support (b : Bool) : b ∈ fairCoin.support := by
  cases b <;> simp [fairCoin]

noncomputable def boundedLaw (M : Machine) (input n : ℕ) : PMF Configuration :=
  (samples fairCoin n).map (M.evaluate (.inl (M.initial input)))

theorem boundedLaw_support (M : Machine) (input n : ℕ) (c : Configuration) :
    c ∈ (M.boundedLaw input n).support ↔ c ∈ M.boundedResults input n := by
  simp only [boundedLaw, PMF.support_map, Set.mem_image, boundedResults, List.mem_map]
  constructor
  · rintro ⟨bits, hb, he⟩
    exact ⟨bits, (mem_binaryWords bits n).mpr ((samples_support fairCoin n bits).mp hb).1, he⟩
  · rintro ⟨bits, hb, he⟩
    exact ⟨bits, (samples_support fairCoin n bits).mpr
      ⟨(mem_binaryWords bits n).mp hb, fun b _ => fairCoin_support b⟩, he⟩

def PositiveFiniteOutput (M : Machine) (input output : ℕ) : Prop :=
  ∃ n, 0 < (M.boundedLaw input n (.inr output)).toReal

theorem positiveFiniteOutput_iff (M : Machine) (input output : ℕ) :
    M.PositiveFiniteOutput input output ↔ M.CanOutput input output := by
  constructor
  · rintro ⟨n, hn⟩
    have hs : Sum.inr output ∈ (M.boundedLaw input n).support :=
      (ENNReal.toReal_pos_iff.mp hn).1.ne'
    obtain ⟨bits, _, hbits⟩ := List.mem_map.mp ((M.boundedLaw_support input n _).mp hs)
    exact ⟨bits, hbits⟩
  · rintro ⟨bits, hbits⟩
    have hs : Sum.inr output ∈ (M.boundedLaw input bits.length).support :=
      (M.boundedLaw_support input bits.length _).mpr
        (List.mem_map.mpr ⟨bits, (mem_binaryWords bits bits.length).mpr rfl, hbits⟩)
    exact ⟨bits.length, ENNReal.toReal_pos hs ((M.boundedLaw input bits.length).apply_ne_top _)⟩

def outputOrZero : Configuration → ℕ := Sum.elim (fun _ => 0) id

noncomputable def outputLaw (M : Machine) (hM : M.AlwaysHalts) (input : ℕ) : PMF ℕ :=
  (M.boundedLaw input (M.executionBound hM input)).map outputOrZero

theorem outputLaw_support (M : Machine) (hM : M.AlwaysHalts) (input output : ℕ) :
    output ∈ (M.outputLaw hM input).support ↔ M.CanOutput input output := by
  rw [outputLaw, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨c, hc, he⟩
    have hc' := (M.boundedLaw_support input _ c).mp hc
    obtain ⟨bits, hb, hbits⟩ := List.mem_map.mp hc'
    obtain ⟨y, hy⟩ := (M.allFinished_iff input _).mp (M.executionBound_spec hM input) bits
      ((mem_binaryWords _ _).mp hb)
    have hcy : c = .inr y := hbits.symm.trans hy
    subst c
    have hyo : y = output := by simpa [hy, outputOrZero] using he
    exact hyo ▸ (M.outputs_spec hM input y).mp
      ((mem_outputValues _ y).mpr (List.mem_map.mpr ⟨bits, hb, hy⟩))
  · intro h
    refine ⟨.inr output, ?_, rfl⟩
    apply (M.boundedLaw_support input _ _).mpr
    exact (mem_outputValues _ output).mp ((M.outputs_spec hM input output).mpr h)

end GenLimit.Support.RandomBitMachine.Machine
