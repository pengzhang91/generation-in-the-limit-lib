import GenLimit.Support.RandomBitMachine.Compactness
import GenLimit.Support.OracleSearchProgram

/-!
# Effective finite exploration of an always-halting randomized machine

Enumerate all padded Boolean traces of a proposed length, simulate them, and
test whether all have halted. Search increasing lengths until this happens.
Compactness proves termination of that search, not a supplied halting bound.
The resulting finite output list is computable and contains exactly the
possible outputs of the original machine.
-/

namespace GenLimit.Support.RandomBitMachine.Machine

private def chooseNext (b : Bool) (p : ℕ × ℕ) : Configuration := .inl (if b then p.2 else p.1)
private def nextAction (b : Bool) (a : ℕ ⊕ (ℕ × ℕ)) : Configuration :=
  a.elim Sum.inl (chooseNext b)
private def resolveAction (b : Bool) (a : Action) : Configuration :=
  a.elim Sum.inr (nextAction b)

private theorem chooseNext_computable : Computable₂ chooseNext := by
  have hc : Computable (fun z : Bool × (ℕ × ℕ) => if z.1 then z.2.2 else z.2.1) :=
    (Computable.cond Computable.fst (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.snd)).of_eq (fun z => by cases z.1 <;> rfl)
  exact ((Computable.sumInl (α := ℕ) (β := ℕ)).comp hc).to₂

private theorem nextAction_computable : Computable₂ nextAction := by
  have hr : Computable₂ (fun z : Bool × (ℕ ⊕ (ℕ × ℕ)) => fun p : ℕ × ℕ => chooseNext z.1 p) :=
    (chooseNext_computable.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  exact (Computable.sumCasesOn Computable.snd (Computable.sumInl.comp Computable.snd).to₂ hr).to₂

private theorem resolveAction_computable : Computable₂ resolveAction := by
  have hr : Computable₂ (fun z : Bool × Action => fun a : ℕ ⊕ (ℕ × ℕ) => nextAction z.1 a) :=
    (nextAction_computable.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  exact (Computable.sumCasesOn Computable.snd (Computable.sumInr.comp Computable.snd).to₂ hr).to₂

theorem advance_computable (M : Machine) :
    Computable (fun z : Bool × Configuration => M.advance z.1 z.2) := by
  have hl : Computable₂ (fun z : Bool × Configuration => fun s : ℕ => resolveAction z.1 (M.action s)) :=
    (resolveAction_computable.comp (Computable.fst.comp Computable.fst)
      (M.action_computable.comp Computable.snd)).to₂
  apply (Computable.sumCasesOn Computable.snd hl (Computable.sumInr.comp Computable.snd).to₂).of_eq
  rintro ⟨b, c⟩
  cases c with
  | inr output => rfl
  | inl state =>
    cases h : M.action state with
    | inl output => simp [advance, resolveAction, h]
    | inr a => cases a <;> simp [advance, resolveAction, nextAction, chooseNext, h]

theorem evaluate_computable (M : Machine) :
    Computable (fun z : Configuration × List Bool => M.evaluate z.1 z.2) := by
  have hstep : Computable₂ (fun (_z : Configuration × List Bool) (r : Configuration × Bool) =>
      M.advance r.2 r.1) :=
    ((M.advance_computable).comp (Computable.pair (Computable.snd.comp Computable.snd)
      (Computable.fst.comp Computable.snd))).to₂
  exact ComputableLists.foldl Computable.snd Computable.fst hstep

def boundedResults (M : Machine) (input n : ℕ) : List Configuration :=
  (binaryWords n).map (M.evaluate (.inl (M.initial input)))

theorem boundedResults_computable (M : Machine) : Computable₂ M.boundedResults := by
  have he : Computable₂ (fun z : ℕ × ℕ => fun bits : List Bool =>
      M.evaluate (.inl (M.initial z.1)) bits) :=
    (M.evaluate_computable.comp (Computable.pair
      (Computable.sumInl.comp (M.initial_computable.comp (Computable.fst.comp Computable.fst)))
      Computable.snd)).to₂
  exact (ComputableLists.map (binaryWords_primrec.to_comp.comp Computable.snd) he).to₂

def halted (c : Configuration) : Bool := c.isRight

theorem halted_computable : Computable halted := by
  apply (Computable.sumCasesOn (Computable.id (α := Configuration))
    (Computable.const false).to₂ (Computable.const true).to₂).of_eq
  intro c
  cases c <;> rfl

theorem halted_iff (c : Configuration) : halted c = true ↔ ∃ output, c = .inr output := by
  cases c <;> simp [halted]

def allFinished (M : Machine) (input n : ℕ) : Bool := (M.boundedResults input n).all halted

theorem allFinished_computable (M : Machine) : Computable₂ M.allFinished :=
  (ComputableLists.all M.boundedResults_computable
    (halted_computable.comp Computable.snd).to₂).to₂

theorem allFinished_iff (M : Machine) (input n : ℕ) :
    M.allFinished input n = true ↔
      ∀ bits : List Bool, bits.length = n → ∃ output, M.evaluate (.inl (M.initial input)) bits = .inr output := by
  simp only [allFinished, boundedResults, List.all_map, List.all_eq_true, mem_binaryWords,
    Function.comp_apply, halted_iff]

theorem exists_allFinished (M : Machine) (hM : M.AlwaysHalts) (input : ℕ) :
    ∃ n, M.allFinished input n = true := by
  obtain ⟨N, hN⟩ := M.uniform_halting_bound hM input
  refine ⟨N, (M.allFinished_iff input N).mpr ?_⟩
  intro bits hlen
  let tape : ℕ → Bool := fun k => (bits[k]?).getD false
  obtain ⟨output, hout⟩ := hN tape
  have he : tapePrefix tape N = bits := by
    apply List.ext_getElem
    · simp [tapePrefix, hlen]
    · intro k hk hk'
      simp only [tapePrefix, List.getElem_map, List.getElem_range]
      simp [tape, List.getElem?_eq_getElem hk']
  exact ⟨output, by simpa only [run, he] using hout⟩

def boundProgram (M : Machine) : OracleSearchProgram where
  queries := fun _ => []
  queries_primrec := Primrec.const []
  output := fun data => if M.allFinished ((data.1.1[0]?).getD 0) data.1.2 then some data.1.2 else none
  output_computable :=
    (Computable.cond
      (M.allFinished_computable.comp (Computable.option_getD
        (Computable.list_getElem?.comp (Computable.fst.comp Computable.fst) (Computable.const 0))
        (Computable.const 0)) (Computable.snd.comp Computable.fst))
      (Computable.option_some.comp (Computable.snd.comp Computable.fst)) (Computable.const none)).of_eq
      (fun data => by cases M.allFinished ((data.1.1[0]?).getD 0) data.1.2 <;> rfl)

theorem boundProgram_terminates (M : Machine) (hM : M.AlwaysHalts) :
    M.boundProgram.Terminates (fun _ => 0) := by
  intro xs
  obtain ⟨n, hn⟩ := M.exists_allFinished hM ((xs[0]?).getD 0)
  exact ⟨n, n, by simp [OracleSearchProgram.stage, boundProgram, hn]⟩

def executionBound (M : Machine) (hM : M.AlwaysHalts) (input : ℕ) : ℕ :=
  M.boundProgram.run (fun _ => 0) (M.boundProgram_terminates hM) [input]

theorem executionBound_computable (M : Machine) (hM : M.AlwaysHalts) : Computable (M.executionBound hM) :=
  ((M.boundProgram).run_computable (Computable.const 0) (M.boundProgram_terminates hM)).comp
    (Computable.list_cons.comp Computable.id (Computable.const []))

theorem executionBound_spec (M : Machine) (hM : M.AlwaysHalts) (input : ℕ) :
    M.allFinished input (M.executionBound hM input) = true := by
  obtain ⟨n, hn⟩ := M.boundProgram.run_stage (fun _ => 0) (M.boundProgram_terminates hM) [input]
  change (if M.allFinished input n then some n else none) = some (M.executionBound hM input) at hn
  split at hn
  · rename_i h
    exact (Option.some.inj hn) ▸ h
  · simp at hn

def outputValues (xs : List Configuration) : List ℕ :=
  xs.flatMap (fun c => c.elim (fun _ => []) (fun output => [output]))

theorem outputValues_computable : Computable outputValues := by
  have hf : Computable₂ (fun (_xs : List Configuration) (c : Configuration) =>
      c.elim (fun _ => ([] : List ℕ)) (fun output => [output])) :=
    (Computable.sumCasesOn Computable.snd (Computable.const []).to₂
      (Computable.list_cons.comp Computable.snd (Computable.const [])).to₂).to₂
  exact ComputableLists.flatMap Computable.id hf

theorem mem_outputValues (xs : List Configuration) (output : ℕ) :
    output ∈ outputValues xs ↔ Sum.inr output ∈ xs := by
  induction xs with
  | nil => simp [outputValues]
  | cons c cs _ => cases c <;> simp [outputValues]

def outputs (M : Machine) (hM : M.AlwaysHalts) (input : ℕ) : List ℕ :=
  outputValues (M.boundedResults input (M.executionBound hM input))

theorem outputs_computable (M : Machine) (hM : M.AlwaysHalts) : Computable (M.outputs hM) :=
  outputValues_computable.comp (M.boundedResults_computable.comp Computable.id (M.executionBound_computable hM))

end GenLimit.Support.RandomBitMachine.Machine
