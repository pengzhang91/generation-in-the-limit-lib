import GenLimit.Paper03_HallucinationAndModeCollapse.SupportMembership
import GenLimit.Support.RandomBitMachine.Probability
import Mathlib.Computability.Halting

/-! # Support membership for program descriptions and the Appendix A machine -/

namespace GenLimit.HallucinationModeCollapse.CodeMOP

open Nat.Partrec (Code)
open Denumerable (ofNat)
open GenLimit.DiscreteIID GenLimit.Support.RandomBitMachine

/-- A finite random transcript is specified by its natural code. Zero is the
running flag and a successor encodes a completed output. -/
def HasOutput (description : Code) (input output : ℕ) : Prop :=
  ∃ transcript, output + 1 ∈ description.eval (Nat.pair input transcript)

/-- Definition 6 asks for a decider for each trained description. -/
def DecidableFor (trained : List ℕ → Code) : Prop :=
  ∀ xs, ComputablePred (HasOutput (trained xs) 0)

theorem decidableFor_iff (trained : List ℕ → Code) (G : StatisticalGenerator)
    (h : ∀ xs x, HasOutput (trained xs) 0 x ↔ x ∈ (G xs).support) :
    DecidableFor trained ↔ DecidableMOP G := by
  simp only [DecidableFor, DecidableMOP, ComputablePred.computable_iff]
  constructor
  · intro hd xs
    obtain ⟨f, hf, he⟩ := hd xs
    exact ⟨f, hf, fun x => (Iff.of_eq (congrFun he x)).symm.trans (h xs x)⟩
  · intro hd xs
    obtain ⟨f, hf, he⟩ := hd xs
    refine ⟨f, hf, funext fun x => propext ?_⟩
    exact (h xs x).trans (he x).symm

/-- Every operational random-bit machine admits such a numeric description,
including machines with divergent runs. Positive finite execution is the
event that some halting trace has positive probability. -/
theorem represents_machine (M : Machine) :
    ∃ c : Code, ∀ i x, HasOutput c i x ↔ M.PositiveFiniteOutput i x := by
  let bits := fun r : ℕ => (Encodable.decode (α := List Bool) r).getD []
  have hbits : Computable bits :=
    Computable.option_getD Primrec.decode.to_comp (Computable.const [])
  let result : Configuration → ℕ := Sum.elim (fun _ => 0) Nat.succ
  have hr : Computable result := Computable.sumCasesOn Computable.id
    (Computable.const 0).to₂ (Computable.succ.comp Computable.snd).to₂
  let evaluate := fun n : ℕ =>
    result (M.evaluate (.inl (M.initial n.unpair.1)) (bits n.unpair.2))
  have hev : Computable evaluate := hr.comp (M.evaluate_computable.comp
    ((Computable.sumInl.comp (M.initial_computable.comp (Computable.fst.comp Computable.unpair))).pair
      (hbits.comp (Computable.snd.comp Computable.unpair))))
  obtain ⟨c, hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hev)
  refine ⟨c, fun i x => ?_⟩
  rw [Machine.positiveFiniteOutput_iff]
  have hcode (r) : c.eval (Nat.pair i r) = Part.some
      (result (M.evaluate (.inl (M.initial i)) (bits r))) := by
    rw [hc]
    simp [evaluate]
  constructor
  · rintro ⟨r, h⟩
    rw [hcode, Part.mem_some_iff] at h
    refine ⟨bits r, ?_⟩
    cases he : M.evaluate (.inl (M.initial i)) (bits r) <;> simp_all [result]
  · rintro ⟨bs, hb⟩
    refine ⟨Encodable.encode bs, ?_⟩
    rw [hcode]
    simp [bits, hb, result]

/-- Zero represents a malformed delimited word. A valid word consists of a
program and an input. The source run waits indefinitely for its simulation. -/
def runWord : ℕ → Part ℕ
  | 0 => Part.some 0
  | w+1 => ((ofNat Code w.unpair.1).eval w.unpair.2).map (fun _ => w+1)

theorem runWord_partrec : Partrec runWord := by
  have prev := Computable.pred
  have row := Computable.fst.comp (Computable.unpair.comp prev)
  have col := Computable.snd.comp (Computable.unpair.comp prev)
  have sim := Code.eval_part.comp ((Computable.ofNat Code).comp row) col
  apply (Partrec.cond (Primrec.beq.to_comp.comp Computable.id (Computable.const 0))
    (show Computable (fun _ : ℕ => (0 : ℕ)) from Computable.const 0)
    (sim.map (Computable.fst : Computable (@Prod.fst ℕ ℕ)).to₂)).of_eq
  intro u
  cases u <;> rfl

def marked (c : Code) (x : ℕ) := Nat.pair (Encodable.encode c) x + 1

/-- The first delimiter gives each finite word positive probability, so the
machine's possible outputs are exactly the outputs on some delimited word. -/
def wordSupport (y : ℕ) : Prop := ∃ w, y ∈ runWord w

theorem marked_mem_wordSupport (c : Code) (x : ℕ) :
    wordSupport (marked c x) ↔ (c.eval x).Dom := by
  constructor
  · rintro ⟨_ | w, h⟩
    · simp [runWord, marked] at h
    · obtain ⟨v, hv, he⟩ := (Part.mem_map_iff _).mp h
      have hw : w = Nat.pair (Encodable.encode c) x := Nat.succ.inj he
      subst w
      exact Part.dom_iff_mem.mpr ⟨v, by simpa using hv⟩
  · intro h
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
    refine ⟨marked c x, (Part.mem_map_iff _).mpr ⟨v, ?_, rfl⟩⟩
    simpa [marked] using hv

/-- Compile the Appendix A procedure into a single trained description.
Every possible finite random word occurs under the delimiter convention. -/
theorem wordMachine_description : ∃ c : Code, ∀ y, HasOutput c 0 y ↔ wordSupport y := by
  let f := fun n : ℕ => (runWord n.unpair.2).map Nat.succ
  have hf : Partrec f := (runWord_partrec.comp (Computable.snd.comp Computable.unpair)).map
    (Computable.succ.comp Computable.snd).to₂
  obtain ⟨c, hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hf)
  refine ⟨c, fun y => ?_⟩
  simp [HasOutput, wordSupport, hc, f, Part.mem_map_iff]

private theorem undecidable_of_marks (P : ℕ → Prop)
    (hm : ∀ c : Code, P (marked c 0) ↔ (c.eval 0).Dom) : ¬ ComputablePred P := by
  intro h
  obtain ⟨f, hf, he⟩ := ComputablePred.computable_iff.mp h
  apply ComputablePred.halting_problem 0
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun c => f (marked c 0), hf.comp (Computable.succ.comp
    (Primrec₂.natPair.to_comp.comp Computable.encode (Computable.const 0))), ?_⟩
  exact funext fun c => propext ((hm c).symm.trans (Iff.of_eq (congrFun he _)))

/-- Proposition A.1 for the corrected validity branch of the partial machine. -/
theorem proposition_A_1 : ¬ ComputablePred wordSupport :=
  undecidable_of_marks _ (fun c => marked_mem_wordSupport c 0)

/-- Total normalized variant. A geometric seed supplies both a word and a
finite simulation budget. A timeout returns the unmarked sentinel. -/
def boundedOutput (seed : ℕ) : ℕ :=
  let w := seed.unpair.1
  if (Code.evaln seed.unpair.2 (ofNat Code w.unpair.1) w.unpair.2).isSome
    then w+1 else 0

theorem boundedOutput_computable : Computable boundedOutput := by
  let w := Primrec.fst.comp Primrec.unpair
  have he := Code.primrec_evaln.comp (((Primrec.snd.comp Primrec.unpair).pair
    ((Primrec.ofNat Code).comp (w.comp w))).pair ((Primrec.snd.comp Primrec.unpair).comp w))
  exact ((Primrec.cond (Primrec.option_isSome.comp he) (Primrec.succ.comp w)
    (Primrec.const 0)).to_comp).of_eq (fun s => by simp [boundedOutput, Bool.cond_eq_ite])

noncomputable def staticGenerator : StatisticalGenerator := fun _ =>
  positiveGeometric.map boundedOutput

theorem bounded_marked (xs : List ℕ) (c : Code) (x : ℕ) :
    marked c x ∈ (staticGenerator xs).support ↔ (c.eval x).Dom := by
  simp only [staticGenerator, PMF.support_map, Set.mem_image]
  constructor
  · rintro ⟨r, _, hr⟩
    unfold boundedOutput at hr
    cases he : Code.evaln r.unpair.2 (ofNat Code r.unpair.1.unpair.1) r.unpair.1.unpair.2 with
    | none => simp [he, marked] at hr
    | some v =>
      have hw : r.unpair.1 = Nat.pair (Encodable.encode c) x := by simpa [he, marked] using hr
      exact Part.dom_iff_mem.mpr ⟨v, Code.evaln_sound (k := r.unpair.2)
        (by simpa [hw] using he : v ∈ Code.evaln r.unpair.2 c x)⟩
  · intro hd
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hd
    obtain ⟨t, ht⟩ := Code.evaln_complete.mp hv
    let r := Nat.pair (Nat.pair (Encodable.encode c) x) t
    exact ⟨r, positiveGeometric_support _, by simp [r, boundedOutput, marked, Option.mem_def.mp ht]⟩

/-- Even a total computable sampler with a normalized output law may fail
pointwise decidability of support membership. -/
theorem normalized_undecidability : HasComputableSampler staticGenerator ∧ ¬ DecidableMOP staticGenerator := by
  refine ⟨⟨fun z => boundedOutput z.2, boundedOutput_computable.comp Computable.snd, fun _ => rfl⟩, ?_⟩
  intro hd
  obtain ⟨f, hf, he⟩ := hd []
  apply undecidable_of_marks (fun y => y ∈ (staticGenerator []).support) (bounded_marked [] · 0)
  exact ComputablePred.computable_iff.mpr ⟨f, hf, funext fun y => propext (he y).symm⟩

end GenLimit.HallucinationModeCollapse.CodeMOP
