import GenLimit.Paper03_HallucinationAndModeCollapse.ExactSampler
import GenLimit.Support.OracleProcedureComputability

/-!
# Certified support-membership procedures

Definition 6 asks for a decider for each trained generator. `OracleMOP`
records an actual certified truth-table procedure for each such support,
relative to the standing family-membership oracle. Every ordinary decidable
support also fits this interface by ignoring the oracle. A computable oracle
turns each certificate into ordinary `DecidableMOP`.

`HasComputableSampler` is a sufficient implementation certificate for the
constructed generators: one full-support geometric natural-number draw,
followed by a total computable numerical-seed map. It does not assert that
all computable PMFs must have this representation.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit GenLimit.Support GenLimit.DiscreteIID

def OracleMOP (oracle : ℕ → ℕ) (G : StatisticalGenerator) : Prop :=
  ∀ xs, ∃ P : TruthTableProgram, ∀ x,
    P.run oracle [x] = 1 ↔ x ∈ (G xs).support

def HasComputableSampler (G : StatisticalGenerator) : Prop :=
  ∃ sample : List ℕ × ℕ → ℕ, Computable sample ∧
    ∀ xs, G xs = positiveGeometric.map (fun seed => sample (xs, seed))

theorem OracleMOP.ordinary {oracle : ℕ → ℕ} {G : StatisticalGenerator}
    (h : OracleMOP oracle G) (ho : Computable oracle) : DecidableMOP G := by
  intro xs
  obtain ⟨P, hP⟩ := h xs
  let query := fun x => P.run oracle [x] == 1
  have hr : Computable (fun x : ℕ => P.run oracle [x]) :=
    (P.run_computable ho).comp (Computable.list_cons.comp Computable.id (Computable.const []))
  refine ⟨query, Primrec.beq.to_comp.comp hr (Computable.const 1), ?_⟩
  intro x
  simpa [query] using hP x

theorem DecidableMOP.oracle {G : StatisticalGenerator} (h : DecidableMOP G)
    (oracle : ℕ → ℕ) : OracleMOP oracle G := by
  intro xs
  obtain ⟨query, hq, hspec⟩ := h xs
  let P : TruthTableProgram := {
    queries := fun _ => []
    queries_primrec := Primrec.const []
    output := fun data => if query ((data.1[0]?).getD 0) then 1 else 0
    output_computable := (Computable.cond
      (hq.comp (Computable.option_getD
        (Computable.list_getElem?.comp Computable.fst (Computable.const 0)) (Computable.const 0)))
      (Computable.const 1) (Computable.const 0)).of_eq (fun data => by
        cases query ((data.1[0]?).getD 0) <;> rfl) }
  refine ⟨P, ?_⟩
  intro x
  simpa [P, TruthTableProgram.run] using hspec x

def singletonMOPProgram (a : ℕ) : TruthTableProgram where
  queries := fun _ => []
  queries_primrec := Primrec.const []
  output := fun data => if (data.1[0]?).getD 0 = a then 1 else 0
  output_computable := (Primrec.ite
    (Primrec.eq.comp (Primrec.option_getD.comp
      (Primrec.list_getElem?.comp Primrec.fst (Primrec.const 0)) (Primrec.const 0)) (Primrec.const a))
    (Primrec.const 1) (Primrec.const 0)).to_comp

theorem deterministic_oracleMOP (oracle : ℕ → ℕ) (A : GenLimit.Learner ℕ ℕ) :
    OracleMOP oracle (deterministicIdentifier A) := by
  intro xs
  refine ⟨singletonMOPProgram (A xs), ?_⟩
  intro x
  simp [singletonMOPProgram, TruthTableProgram.run, deterministicIdentifier]

def freshMOPProgram (xs : List ℕ) (j : ℕ) : TruthTableProgram where
  queries := fun input => [Nat.pair j ((input[0]?).getD 0)]
  queries_primrec := Primrec.list_cons.comp
    (Primrec₂.natPair.comp (Primrec.const j) (Primrec.option_getD.comp
      (Primrec.list_getElem?.comp Primrec.id (Primrec.const 0)) (Primrec.const 0))) (Primrec.const [])
  output := fun data => if (data.2[0]?).getD 0 = 1 ∧ (data.1[0]?).getD 0 ∉ xs then 1 else 0
  output_computable := by
    have hx : Primrec (fun data : List ℕ × List ℕ => (data.1[0]?).getD 0) :=
      Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst (Primrec.const 0)) (Primrec.const 0)
    have hm : PrimrecPred (fun data : List ℕ × List ℕ => (data.1[0]?).getD 0 ∈ xs) :=
      (Primrec.nat_lt.comp (Primrec.list_idxOf.comp hx (Primrec.const xs)) (Primrec.const xs.length)).of_eq
        (fun _ => List.idxOf_lt_length_iff)
    have ha : PrimrecPred (fun data : List ℕ × List ℕ => (data.2[0]?).getD 0 = 1) :=
      Primrec.eq.comp (Primrec.option_getD.comp
        (Primrec.list_getElem?.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)) (Primrec.const 1)
    exact (Primrec.ite (ha.and hm.not) (Primrec.const 1) (Primrec.const 0)).to_comp

theorem freshMOPProgram_correct (O : OracleFamily) (xs : List ℕ) (j x : ℕ) :
    (freshMOPProgram xs j).run (generationOracle O) [x] = 1 ↔
      x ∈ (exactFreshSampler O xs j).support := by
  rw [exactFreshSampler_support]
  simp [freshMOPProgram, TruthTableProgram.run, generationOracle, O.query_spec]

theorem exactFreshSampler_oracleMOP (O : OracleFamily) (A : GenLimit.Learner ℕ ℕ) :
    OracleMOP (generationOracle O) (fun xs => exactFreshSampler O xs (A xs)) := by
  intro xs
  exact ⟨freshMOPProgram xs (A xs), freshMOPProgram_correct O xs (A xs)⟩

end GenLimit.HallucinationModeCollapse
