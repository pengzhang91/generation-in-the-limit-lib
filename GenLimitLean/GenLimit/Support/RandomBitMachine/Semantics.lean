import GenLimit.Support.RandomBitMachine.Effective

/-!
# Exact finite-output semantics and an effective support decider

The finite output list is proved equal to possible finite execution, including
executions longer than the computed bound. `Executes` records only actual
coin reads; its equivalence with padded finite execution shows that ignored
coordinates introduce no extra possible outputs.
-/

namespace GenLimit.Support.RandomBitMachine.Machine

theorem tapePrefix_extend (bits : List Bool) :
    tapePrefix (fun k => (bits[k]?).getD false) bits.length = bits := by
  apply List.ext_getElem
  · simp [tapePrefix]
  · intro k hk hk'
    simp only [tapePrefix, List.getElem_map, List.getElem_range]
    simp [List.getElem?_eq_getElem hk']

theorem run_output_unique (M : Machine) (input : ℕ) (tape : ℕ → Bool)
    {n m x y : ℕ} (hx : M.run input tape n = .inr x) (hy : M.run input tape m = .inr y) : x = y := by
  rcases le_total n m with h | h
  · exact Sum.inr.inj ((M.run_halted_mono input tape h hx).symm.trans hy)
  · exact Sum.inr.inj (hx.symm.trans (M.run_halted_mono input tape h hy))

theorem canOutput_iff_run (M : Machine) (input output : ℕ) :
    M.CanOutput input output ↔ ∃ tape n, M.run input tape n = .inr output := by
  constructor
  · rintro ⟨bits, hbits⟩
    exact ⟨fun k => (bits[k]?).getD false, bits.length,
      by simpa only [run, tapePrefix_extend] using hbits⟩
  · rintro ⟨tape, n, h⟩
    exact ⟨tapePrefix tape n, h⟩

theorem outputs_spec (M : Machine) (hM : M.AlwaysHalts) (input output : ℕ) :
    output ∈ M.outputs hM input ↔ M.CanOutput input output := by
  rw [outputs, mem_outputValues]
  constructor
  · intro h
    obtain ⟨bits, _, hbits⟩ := List.mem_map.mp h
    exact ⟨bits, hbits⟩
  · intro h
    obtain ⟨tape, n, hn⟩ := (M.canOutput_iff_run input output).mp h
    let N := M.executionBound hM input
    have hlen : (tapePrefix tape N).length = N := by simp [tapePrefix]
    obtain ⟨y, hy⟩ := (M.allFinished_iff input N).mp (M.executionBound_spec hM input)
      (tapePrefix tape N) hlen
    have hxy : y = output := M.run_output_unique input tape hy hn
    apply List.mem_map.mpr
    refine ⟨tapePrefix tape N, (mem_binaryWords _ N).mpr hlen, ?_⟩
    exact hxy ▸ hy

def supportDecider (M : Machine) (hM : M.AlwaysHalts) (input output : ℕ) : Bool :=
  listContains (M.outputs hM input) output

theorem supportDecider_computable (M : Machine) (hM : M.AlwaysHalts) : Computable₂ (M.supportDecider hM) :=
  (listContains_computable.comp ((M.outputs_computable hM).comp Computable.fst) Computable.snd).to₂

theorem supportDecider_spec (M : Machine) (hM : M.AlwaysHalts) (input output : ℕ) :
    M.supportDecider hM input output = true ↔ M.CanOutput input output := by
  rw [supportDecider, listContains_eq_true_iff, outputs_spec]

/-- Finite execution with no random-bit padding: deterministic transitions
consume no bits, and a coin action consumes exactly its selected bit. -/
inductive Executes (M : Machine) : ℕ → List Bool → ℕ → Prop
  | halt {state output} (h : M.action state = .inl output) : Executes M state [] output
  | deterministic {state next bits output} (h : M.action state = .inr (.inl next))
      (tail : Executes M next bits output) : Executes M state bits output
  | coin {state left right bit bits output} (h : M.action state = .inr (.inr (left, right)))
      (tail : Executes M (if bit then right else left) bits output) : Executes M state (bit :: bits) output

theorem evaluate_executes (M : Machine) (state : ℕ) (bits : List Bool) (output : ℕ)
    (h : M.evaluate (.inl state) bits = .inr output) :
    M.Executes state (M.readTrace (.inl state) bits) output := by
  induction bits generalizing state with
  | nil => simp at h
  | cons b bs ih =>
    cases ha : M.action state with
    | inl y =>
      have hy : y = output := by simpa [evaluate_cons, advance, ha] using h
      subst output
      simpa [readTrace, ha] using Executes.halt ha
    | inr a =>
      cases a with
      | inl next =>
        have ht : M.evaluate (.inl next) bs = .inr output := by simpa [evaluate_cons, advance, ha] using h
        simpa [readTrace, ha] using Executes.deterministic ha (ih next ht)
      | inr next =>
        have ht : M.evaluate (.inl (if b then next.2 else next.1)) bs = .inr output := by
          simpa [evaluate_cons, advance, ha] using h
        simpa [readTrace, ha] using Executes.coin ha (ih _ ht)

theorem Executes.exists_padded {M : Machine} {state : ℕ} {reads : List Bool} {output : ℕ}
    (h : M.Executes state reads output) :
    ∃ bits : List Bool, M.evaluate (.inl state) bits = .inr output ∧
      M.readTrace (.inl state) bits = reads := by
  induction h with
  | halt h => exact ⟨[false], by simp [evaluate_cons, advance, h], by simp [readTrace, h]⟩
  | deterministic h tail ih =>
    obtain ⟨bits, hb, hr⟩ := ih
    exact ⟨false :: bits, by simpa [evaluate_cons, advance, h] using hb,
      by simpa [readTrace, h] using hr⟩
  | @coin state left right bit reads output h tail ih =>
    obtain ⟨bits, hb, hr⟩ := ih
    refine ⟨bit :: bits, ?_, ?_⟩
    · simpa [evaluate_cons, advance, h] using hb
    · simp [readTrace, h, hr]

theorem canOutput_iff_executes (M : Machine) (input output : ℕ) :
    M.CanOutput input output ↔ ∃ reads, M.Executes (M.initial input) reads output := by
  constructor
  · rintro ⟨bits, hbits⟩
    exact ⟨_, M.evaluate_executes _ _ _ hbits⟩
  · rintro ⟨reads, hreads⟩
    obtain ⟨bits, hb, _⟩ := hreads.exists_padded
    exact ⟨bits, hb⟩

theorem readTrace_append (M : Machine) (c : Configuration) (xs ys : List Bool) :
    M.readTrace c (xs ++ ys) = M.readTrace c xs ++ M.readTrace (M.evaluate c xs) ys := by
  induction xs generalizing c with
  | nil => simp [readTrace]
  | cons b bs ih =>
    cases c with
    | inr output => cases ys <;> simp [readTrace, advance]
    | inl state =>
      cases ha : M.action state with
      | inl output => cases ys <;> simp [readTrace, evaluate_cons, advance, ha]
      | inr a => cases a <;> simp [readTrace, evaluate_cons, advance, ha, ih]

/-- The derived bound also bounds actual coin reads along every finite
execution, including padded executions longer than the bound. -/
theorem readTrace_uniform_bound (M : Machine) (hM : M.AlwaysHalts) (input : ℕ) (bits : List Bool) :
    (M.readTrace (.inl (M.initial input)) bits).length ≤ M.executionBound hM input := by
  let N := M.executionBound hM input
  by_cases hlen : bits.length ≤ N
  · exact (M.readTrace_length_le _ bits).trans hlen
  · have hN : N ≤ bits.length := by omega
    obtain ⟨output, hout⟩ := (M.allFinished_iff input N).mp (M.executionBound_spec hM input)
      (bits.take N) (List.length_take_of_le hN)
    have he : M.readTrace (.inl (M.initial input)) bits =
        M.readTrace (.inl (M.initial input)) (bits.take N) := by
      conv_lhs => rw [← List.take_append_drop N bits]
      rw [readTrace_append, hout]
      cases bits.drop N <;> simp [readTrace]
    rw [he]
    exact (M.readTrace_length_le _ _).trans (by simp [N])

theorem Executes.reads_bounded {M : Machine} (hM : M.AlwaysHalts) {input output : ℕ}
    {reads : List Bool} (h : M.Executes (M.initial input) reads output) :
    reads.length ≤ M.executionBound hM input := by
  obtain ⟨bits, _, hr⟩ := h.exists_padded
  rw [← hr]
  exact M.readTrace_uniform_bound hM input bits

end GenLimit.Support.RandomBitMachine.Machine
