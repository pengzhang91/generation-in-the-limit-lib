import GenLimit.Support.RandomBitMachine.Probability

/-!
# Definition 15: token generation with auxiliary state

A local randomized operational machine receives the encoded visible stem
and auxiliary state. Its completed output is computably read as a token/EOS
and the next auxiliary state. Tokens have natural-number encodings; `none`
denotes EOS and is not part of the returned word. The outer generator is not
assumed to terminate. A queried finite word has positive probability exactly
when its tokens and a final EOS can be produced along one compatible path.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Support GenLimit.Support.RandomBitMachine
open GenLimit.DiscreteIID Encodable

structure TokenGenerator where
  machine : Machine
  readOutput : ℕ → Option ℕ × ℕ
  readOutput_computable : Computable readOutput
  initialAux : ℕ

namespace TokenGenerator

def inputCode (stem : List ℕ) (aux : ℕ) : ℕ := encode (stem, aux)

noncomputable def nextLaw (G : TokenGenerator) (hG : G.machine.AlwaysHalts)
    (stem : List ℕ) (aux : ℕ) : PMF (Option ℕ × ℕ) :=
  (G.machine.outputLaw hG (inputCode stem aux)).map G.readOutput

def nextOutputs (G : TokenGenerator) (hG : G.machine.AlwaysHalts)
    (stem : List ℕ) (aux : ℕ) : List (Option ℕ × ℕ) :=
  (G.machine.outputs hG (inputCode stem aux)).map G.readOutput

theorem nextOutputs_computable (G : TokenGenerator) (hG : G.machine.AlwaysHalts) :
    Computable₂ (G.nextOutputs hG) := by
  have hi : Computable (fun z : List ℕ × ℕ => inputCode z.1 z.2) := Computable.encode
  have hl := (G.machine.outputs_computable hG).comp hi
  exact (ComputableLists.map hl (G.readOutput_computable.comp Computable.snd).to₂).to₂

theorem nextLaw_support (G : TokenGenerator) (hG : G.machine.AlwaysHalts)
    (stem : List ℕ) (aux : ℕ) (out : Option ℕ × ℕ) :
    out ∈ (G.nextLaw hG stem aux).support ↔ out ∈ G.nextOutputs hG stem aux := by
  simp only [nextLaw, PMF.mem_support_map_iff, nextOutputs, List.mem_map]
  constructor
  · rintro ⟨raw, hraw, he⟩
    exact ⟨raw, (G.machine.outputs_spec hG _ raw).mpr ((G.machine.outputLaw_support hG _ raw).mp hraw), he⟩
  · rintro ⟨raw, hraw, he⟩
    exact ⟨raw, (G.machine.outputLaw_support hG _ raw).mpr ((G.machine.outputs_spec hG _ raw).mp hraw), he⟩

/-- One auxiliary-state path must witness every token and the final EOS. -/
def Produces (G : TokenGenerator) (hG : G.machine.AlwaysHalts)
    (stem : List ℕ) (aux : ℕ) : List ℕ → Prop
  | [] => ∃ nextAux, (none, nextAux) ∈ (G.nextLaw hG stem aux).support
  | token :: rest => ∃ nextAux, (some token, nextAux) ∈ (G.nextLaw hG stem aux).support ∧
      G.Produces hG (stem ++ [token]) nextAux rest

/-- Finite experiment for producing exactly a given remaining word. A wrong
token or premature EOS fails; after the last token, EOS is required. -/
noncomputable def wordExperiment (G : TokenGenerator) (hG : G.machine.AlwaysHalts)
    (stem : List ℕ) (aux : ℕ) : List ℕ → PMF Bool
  | [] => (G.nextLaw hG stem aux).map (fun out => out.1.isNone)
  | token :: rest => (G.nextLaw hG stem aux).bind (fun out =>
      if out.1 = some token then G.wordExperiment hG (stem ++ [token]) out.2 rest else PMF.pure false)

theorem wordExperiment_support (G : TokenGenerator) (hG : G.machine.AlwaysHalts)
    (word : List ℕ) (stem : List ℕ) (aux : ℕ) :
    true ∈ (G.wordExperiment hG stem aux word).support ↔ G.Produces hG stem aux word := by
  induction word generalizing stem aux with
  | nil =>
    rw [wordExperiment, PMF.mem_support_map_iff]
    constructor
    · rintro ⟨⟨token, nextAux⟩, hs, he⟩
      cases token with
      | none => exact ⟨nextAux, hs⟩
      | some token => simp at he
    · rintro ⟨nextAux, hs⟩
      exact ⟨(none, nextAux), hs, rfl⟩
  | cons token rest ih =>
    rw [wordExperiment, PMF.mem_support_bind_iff]
    constructor
    · rintro ⟨⟨nextToken, nextAux⟩, hs, ht⟩
      by_cases he : nextToken = some token
      · subst nextToken
        exact ⟨nextAux, hs, (ih _ _).mp (by simpa using ht)⟩
      · simp [he] at ht
    · rintro ⟨nextAux, hs, ht⟩
      exact ⟨(some token, nextAux), hs, by simpa using (ih _ _).mpr ht⟩

noncomputable def wordProbability (G : TokenGenerator) (hG : G.machine.AlwaysHalts) (word : List ℕ) : ℝ :=
  (G.wordExperiment hG [] G.initialAux word true).toReal

def WordSupport (G : TokenGenerator) (hG : G.machine.AlwaysHalts) : Set (List ℕ) :=
  {word | 0 < G.wordProbability hG word}

theorem wordSupport_iff (G : TokenGenerator) (hG : G.machine.AlwaysHalts) (word : List ℕ) :
    word ∈ G.WordSupport hG ↔ G.Produces hG [] G.initialAux word := by
  rw [WordSupport, Set.mem_setOf_eq, wordProbability, ← G.wordExperiment_support hG word [] G.initialAux]
  change 0 < (G.wordExperiment hG [] G.initialAux word true).toReal ↔
    G.wordExperiment hG [] G.initialAux word true ≠ 0
  exact ⟨fun h => (ENNReal.toReal_pos_iff.mp h).1.ne',
    fun h => ENNReal.toReal_pos h ((G.wordExperiment hG [] G.initialAux word).apply_ne_top true)⟩

end TokenGenerator
end GenLimit.HallucinationModeCollapse
