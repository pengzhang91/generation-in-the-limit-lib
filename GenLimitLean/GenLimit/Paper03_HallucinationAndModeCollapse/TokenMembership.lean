import GenLimit.Paper03_HallucinationAndModeCollapse.TokenGeneration
import GenLimit.Paper03_HallucinationAndModeCollapse.BreadthModel
import Mathlib.Computability.PartrecCode

/-!
# Theorem 3.4: deciding finite-word support of token-by-token generation

The algorithm carries the finite set/list of reachable auxiliary states along
the queried stem and checks EOS only after the last requested token. It does
not require the outer generator to halt. Its computation uses the effective
finite outcome lists of the every-tape-total local machine.
-/

namespace GenLimit.HallucinationModeCollapse.TokenGenerator

open GenLimit.Support GenLimit.Support.RandomBitMachine Encodable

def successors (G : TokenGenerator) (hG : G.machine.AlwaysHalts)
    (stem states : List ℕ) (token : ℕ) : List ℕ :=
  states.flatMap (fun aux => (G.nextOutputs hG stem aux).flatMap
    (fun out => if out.1 = some token then [out.2] else []))

theorem successors_computable (G : TokenGenerator) (hG : G.machine.AlwaysHalts) :
    Computable (fun z : (List ℕ × List ℕ) × ℕ => G.successors hG z.1.1 z.1.2 z.2) := by
  let D := (List ℕ × List ℕ) × ℕ
  have hl : Computable (fun z : D × ℕ => G.nextOutputs hG z.1.1.1 z.2) :=
    (G.nextOutputs_computable hG).comp (Computable.fst.comp (Computable.fst.comp Computable.fst)) Computable.snd
  have hf : Computable₂ (fun z : D × ℕ => fun out : Option ℕ × ℕ =>
      if out.1 = some z.1.2 then [out.2] else []) :=
    (Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.option_some.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [])) (Primrec.const [])).to_comp.to₂
  exact ComputableLists.flatMap (Computable.snd.comp Computable.fst)
    (ComputableLists.flatMap hl hf).to₂

theorem mem_successors (G : TokenGenerator) (hG : G.machine.AlwaysHalts)
    (stem states : List ℕ) (token nextAux : ℕ) :
    nextAux ∈ G.successors hG stem states token ↔
      ∃ aux ∈ states, (some token, nextAux) ∈ (G.nextLaw hG stem aux).support := by
  simp only [successors, List.mem_flatMap]
  constructor
  · rintro ⟨aux, ha, ⟨⟨nextToken, nextAux'⟩, ho, ht⟩⟩
    by_cases he : nextToken = some token
    · subst nextToken
      have ht' : nextAux = nextAux' := by simpa using ht
      clear ht
      subst nextAux'
      exact ⟨aux, ha, (G.nextLaw_support hG _ _ _).mpr ho⟩
    · simp [he] at ht
  · rintro ⟨aux, ha, ho⟩
    exact ⟨aux, ha, (some token, nextAux), (G.nextLaw_support hG _ _ _).mp ho, by simp⟩

def frontierStep (G : TokenGenerator) (hG : G.machine.AlwaysHalts)
    (state : List ℕ × List ℕ) (token : ℕ) : List ℕ × List ℕ :=
  (state.1 ++ [token], G.successors hG state.1 state.2 token)

theorem frontierStep_computable (G : TokenGenerator) (hG : G.machine.AlwaysHalts) :
    Computable₂ (G.frontierStep hG) :=
  (Computable.pair
    (Computable.list_append.comp (Computable.fst.comp Computable.fst)
      (Computable.list_cons.comp Computable.snd (Computable.const [])))
    (G.successors_computable hG)).to₂

def frontierFrom (G : TokenGenerator) (hG : G.machine.AlwaysHalts)
    (stem states word : List ℕ) : List ℕ × List ℕ :=
  word.foldl (G.frontierStep hG) (stem, states)

theorem frontierFrom_computable (G : TokenGenerator) (hG : G.machine.AlwaysHalts) :
    Computable (fun z : (List ℕ × List ℕ) × List ℕ => G.frontierFrom hG z.1.1 z.1.2 z.2) := by
  let D := (List ℕ × List ℕ) × List ℕ
  have hf : Computable (fun r : (List ℕ × List ℕ) × ℕ => G.frontierStep hG r.1 r.2) :=
    G.frontierStep_computable hG
  have hs : Computable₂ (fun (_z : D) (r : (List ℕ × List ℕ) × ℕ) => G.frontierStep hG r.1 r.2) :=
    (Computable.comp hf Computable.snd).to₂
  change Computable (fun z : D => z.2.foldl (fun s b => G.frontierStep hG s b) z.1)
  exact ComputableLists.foldl (l := fun z : D => z.2) (g := fun z => z.1)
    (f := fun _ r => G.frontierStep hG r.1 r.2) Computable.snd Computable.fst hs

def eosFrom (G : TokenGenerator) (hG : G.machine.AlwaysHalts)
    (stem states : List ℕ) : Bool :=
  states.any (fun aux => (G.nextOutputs hG stem aux).any (fun out => out.1.isNone))

theorem eosFrom_computable (G : TokenGenerator) (hG : G.machine.AlwaysHalts) :
    Computable₂ (G.eosFrom hG) := by
  let D := List ℕ × List ℕ
  have hn : Computable (fun z : List ℕ × ℕ => G.nextOutputs hG z.1 z.2) := G.nextOutputs_computable hG
  have hl : Computable (fun z : D × ℕ => G.nextOutputs hG z.1.1 z.2) :=
    Computable.comp (f := fun z : List ℕ × ℕ => G.nextOutputs hG z.1 z.2)
      (g := fun z : D × ℕ => (z.1.1, z.2)) hn
      (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)
  have hnone : Computable (fun out : Option ℕ × ℕ => out.1.isNone) := by
    have hh : Computable (fun out : Option ℕ × ℕ => !(out.1.isSome)) :=
      Primrec.not.to_comp.comp (Primrec.option_isSome.to_comp.comp Computable.fst)
    exact hh.of_eq (fun out => by cases out.1 <;> rfl)
  have hp : Computable₂ (fun (_z : D × ℕ) (out : Option ℕ × ℕ) => out.1.isNone) :=
    (Computable.comp (f := fun out : Option ℕ × ℕ => out.1.isNone)
      (g := fun z : (D × ℕ) × (Option ℕ × ℕ) => z.2) hnone Computable.snd).to₂
  have hi : Computable (fun z : D × ℕ =>
      (G.nextOutputs hG z.1.1 z.2).any (fun out => out.1.isNone)) :=
    ComputableLists.any (l := fun z : D × ℕ => G.nextOutputs hG z.1.1 z.2)
      (f := fun _ out => out.1.isNone) hl hp
  change Computable (fun z : D => z.2.any (fun aux =>
    (G.nextOutputs hG z.1 aux).any (fun out => out.1.isNone)))
  exact ComputableLists.any (l := fun z : D => z.2)
    (f := fun z aux => (G.nextOutputs hG z.1 aux).any (fun out => out.1.isNone))
    Computable.snd hi.to₂

theorem eosFrom_spec (G : TokenGenerator) (hG : G.machine.AlwaysHalts) (stem states : List ℕ) :
    G.eosFrom hG stem states = true ↔ ∃ aux ∈ states, G.Produces hG stem aux [] := by
  simp only [eosFrom, List.any_eq_true]
  constructor
  · rintro ⟨aux, ha, ⟨⟨token, nextAux⟩, ho, ht⟩⟩
    cases token with
    | none => exact ⟨aux, ha, nextAux, (G.nextLaw_support hG _ _ _).mpr ho⟩
    | some token => simp at ht
  · rintro ⟨aux, ha, nextAux, ho⟩
    exact ⟨aux, ha, (none, nextAux), (G.nextLaw_support hG _ _ _).mp ho, rfl⟩

def decideFrom (G : TokenGenerator) (hG : G.machine.AlwaysHalts)
    (stem states word : List ℕ) : Bool :=
  let final := G.frontierFrom hG stem states word
  G.eosFrom hG final.1 final.2

theorem decideFrom_spec (G : TokenGenerator) (hG : G.machine.AlwaysHalts)
    (word stem states : List ℕ) :
    G.decideFrom hG stem states word = true ↔ ∃ aux ∈ states, G.Produces hG stem aux word := by
  induction word generalizing stem states with
  | nil => exact G.eosFrom_spec hG stem states
  | cons token rest ih =>
    change G.decideFrom hG (stem ++ [token]) (G.successors hG stem states token) rest = true ↔ _
    rw [ih]
    constructor
    · rintro ⟨nextAux, hm, ht⟩
      obtain ⟨aux, ha, hs⟩ := (G.mem_successors hG _ _ _ _).mp hm
      exact ⟨aux, ha, nextAux, hs, ht⟩
    · rintro ⟨aux, ha, nextAux, hs, ht⟩
      exact ⟨nextAux, (G.mem_successors hG _ _ _ _).mpr ⟨aux, ha, hs⟩, ht⟩

def wordDecider (G : TokenGenerator) (hG : G.machine.AlwaysHalts) (word : List ℕ) : Bool :=
  G.decideFrom hG [] [G.initialAux] word

theorem wordDecider_computable (G : TokenGenerator) (hG : G.machine.AlwaysHalts) : Computable (G.wordDecider hG) := by
  have hf : Computable (fun word : List ℕ => G.frontierFrom hG [] [G.initialAux] word) :=
    (G.frontierFrom_computable hG).comp (Computable.pair (Computable.const ([], [G.initialAux])) Computable.id)
  exact (G.eosFrom_computable hG).comp (Computable.fst.comp hf) (Computable.snd.comp hf)

theorem wordDecider_spec (G : TokenGenerator) (hG : G.machine.AlwaysHalts) (word : List ℕ) :
    G.wordDecider hG word = true ↔ word ∈ G.WordSupport hG := by
  rw [wordDecider, decideFrom_spec, G.wordSupport_iff hG word]
  simp

/-- Theorem 3.4 in the encoded operational machine model. Local execution
halts on every Boolean tape. Outer generation can continue forever. The
support is defined by the positive probability of the full word plus EOS. -/
theorem theorem_3_4 (G : TokenGenerator) (hG : G.machine.AlwaysHalts) :
    ∃ query : List ℕ → Bool, Computable query ∧
      ∀ word, query word = true ↔ 0 < G.wordProbability hG word :=
  ⟨G.wordDecider hG, G.wordDecider_computable hG, G.wordDecider_spec hG⟩

/-- Natural encodings of complete words in positive-probability support.
Mathlib's `List ℕ` encoding is a computable bijection with the naturals. -/
def EncodedWordSupport (G : TokenGenerator) (hG : G.machine.AlwaysHalts) : Set ℕ :=
  {n | ∃ word : List ℕ, encode word = n ∧ word ∈ G.WordSupport hG}

def encodedWordDecider (G : TokenGenerator) (hG : G.machine.AlwaysHalts) (n : ℕ) : Bool :=
  G.wordDecider hG (Denumerable.ofNat (List ℕ) n)

theorem encodedWordDecider_computable (G : TokenGenerator) (hG : G.machine.AlwaysHalts) :
    Computable (G.encodedWordDecider hG) :=
  (G.wordDecider_computable hG).comp (Primrec.ofNat (List ℕ)).to_comp

theorem encodedWordDecider_spec (G : TokenGenerator) (hG : G.machine.AlwaysHalts) (n : ℕ) :
    G.encodedWordDecider hG n = true ↔ n ∈ G.EncodedWordSupport hG := by
  constructor
  · intro h
    exact ⟨Denumerable.ofNat (List ℕ) n, Denumerable.encode_ofNat n, (G.wordDecider_spec hG _).mp h⟩
  · rintro ⟨word, rfl, hw⟩
    simpa [encodedWordDecider] using (G.wordDecider_spec hG word).mpr hw

/-- Ordinary finite program code for the complete-word support predicate. -/
theorem wordSupport_has_code (G : TokenGenerator) (hG : G.machine.AlwaysHalts) :
    ∃ code : Nat.Partrec.Code, ∀ n,
      code.eval n = Part.some (encode (G.encodedWordDecider hG n)) := by
  have hc := Computable.encode.comp (G.encodedWordDecider_computable hG)
  obtain ⟨code, he⟩ := Nat.Partrec.Code.exists_code.mp hc.partrec
  exact ⟨code, fun n => by simpa using congrFun he n⟩

/-- Bridge to Definition 6's trained statistical-generator interface. Each
trained generator may have its own token machine. A normalized output PMF is
used only by this bridge and must have exactly the encoded finite-word support.
The main theorem does not assume termination of outer generation. -/
theorem decidableMOP_of_token_support (F : List ℕ → TokenGenerator)
    (hF : ∀ xs, (F xs).machine.AlwaysHalts) (H : StatisticalGenerator)
    (hsupport : ∀ xs n, n ∈ (H xs).support ↔ n ∈ (F xs).EncodedWordSupport (hF xs)) :
    DecidableMOP H := by
  intro xs
  exact ⟨(F xs).encodedWordDecider (hF xs), (F xs).encodedWordDecider_computable (hF xs),
    fun n => ((F xs).encodedWordDecider_spec (hF xs) n).trans (hsupport xs n).symm⟩

/-- A generator that can never emit EOS has no complete finite-word output.
This is permitted even when every local computation always terminates. -/
theorem wordSupport_empty_of_no_eos (G : TokenGenerator) (hG : G.machine.AlwaysHalts)
    (hEOS : ∀ stem aux nextAux, (none, nextAux) ∉ (G.nextLaw hG stem aux).support) :
    G.WordSupport hG = ∅ := by
  have hp : ∀ word stem aux, ¬G.Produces hG stem aux word := by
    intro word
    induction word with
    | nil => intro stem aux ⟨nextAux, hs⟩; exact hEOS stem aux nextAux hs
    | cons token rest ih => intro stem aux ⟨nextAux, _, ht⟩; exact ih _ _ ht
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro word hw
  exact hp word [] G.initialAux ((G.wordSupport_iff hG word).mp hw)

end GenLimit.HallucinationModeCollapse.TokenGenerator
