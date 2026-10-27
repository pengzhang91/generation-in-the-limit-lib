import GenLimit.Support.OracleTruthTable

/-!
# Certified oracle programs with unbounded search

Each stage asks a primitive-recursive finite list of natural-number queries
and applies a computable postprocessor. Stages are tried in increasing order
until an output appears. The oracle is the sole external information source.
Termination is a separate obligation, so unbounded search does not hide a
noncomputable stopping test. A computable oracle gives a partial-recursive
program, and a termination proof gives a computable total function.
-/

namespace GenLimit.Support

/-- Mapping a total computable numerical function over a finite list. -/
theorem map_computable {f : ℕ → ℕ} (hf : Computable f) :
    Computable (List.map f) := by
  have hstep : Computable₂ (fun z : List ℕ × ℕ => fun r : ℕ × List ℕ =>
      r.2 ++ [f (z.1[r.1]?.getD 0)]) := by
    have hx : Computable (fun z : (List ℕ × ℕ) × (ℕ × List ℕ) =>
        f (z.1.1[z.2.1]?.getD 0)) :=
      hf.comp (Computable.option_getD
        (Computable.list_getElem?.comp (Computable.fst.comp Computable.fst)
          (Computable.fst.comp Computable.snd)) (Computable.const 0))
    exact (Computable.list_append.comp (Computable.snd.comp Computable.snd)
      (Computable.list_cons.comp hx (Computable.const []))).to₂
  have hrec : Computable₂ (fun xs : List ℕ => fun n =>
      (List.range n).map (fun k => f (xs[k]?.getD 0))) := by
    apply (Computable.nat_rec Computable.snd (Computable.const []) hstep).to₂.of_eq
    rintro ⟨xs, n⟩
    dsimp only
    induction n with
    | zero => rfl
    | succ n ih => simp [List.range_succ, ih]
  apply (hrec.comp Computable.id Computable.list_length).of_eq
  intro xs
  apply List.ext_getElem
  · simp
  · intro k hk hk'
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getElem?_eq_getElem (by simpa using hk)]
    rfl

structure OracleSearchProgram where
  queries : List ℕ × ℕ → List ℕ
  queries_primrec : Primrec queries
  output : (List ℕ × ℕ) × List ℕ → Option ℕ
  output_computable : Computable output

namespace OracleSearchProgram

def stage (P : OracleSearchProgram) (oracle : ℕ → ℕ) (xs : List ℕ) (q : ℕ) : Option ℕ :=
  P.output ((xs, q), (P.queries (xs, q)).map oracle)

def partialRun (P : OracleSearchProgram) (oracle : ℕ → ℕ) (xs : List ℕ) : Part ℕ :=
  Nat.rfindOpt (P.stage oracle xs)

def Terminates (P : OracleSearchProgram) (oracle : ℕ → ℕ) : Prop :=
  ∀ xs, ∃ q y, P.stage oracle xs q = some y

theorem run_dom (P : OracleSearchProgram) (oracle : ℕ → ℕ)
    (h : P.Terminates oracle) (xs : List ℕ) : (P.partialRun oracle xs).Dom := by
  apply Nat.rfindOpt_dom.mpr
  obtain ⟨q, y, hy⟩ := h xs
  exact ⟨q, y, hy⟩

def run (P : OracleSearchProgram) (oracle : ℕ → ℕ) (h : P.Terminates oracle)
    (xs : List ℕ) : ℕ :=
  (P.partialRun oracle xs).get (P.run_dom oracle h xs)

theorem run_stage (P : OracleSearchProgram) (oracle : ℕ → ℕ)
    (h : P.Terminates oracle) (xs : List ℕ) :
    ∃ q, P.stage oracle xs q = some (P.run oracle h xs) := by
  exact Nat.rfindOpt_spec (Part.get_mem (P.run_dom oracle h xs))

theorem stage_computable (P : OracleSearchProgram) {oracle : ℕ → ℕ}
    (ho : Computable oracle) : Computable₂ (P.stage oracle) := by
  have hmap : Computable (fun z : List ℕ × ℕ => (P.queries z).map oracle) := by
    exact (map_computable ho).comp P.queries_primrec.to_comp
  exact (P.output_computable.comp (Computable.pair Computable.id hmap)).to₂

theorem partialRun_partrec (P : OracleSearchProgram) {oracle : ℕ → ℕ}
    (ho : Computable oracle) : Partrec (P.partialRun oracle) :=
  Partrec.rfindOpt (P.stage_computable ho)

theorem run_computable (P : OracleSearchProgram) {oracle : ℕ → ℕ}
    (ho : Computable oracle) (h : P.Terminates oracle) : Computable (P.run oracle h) :=
  (P.partialRun_partrec ho).of_eq_tot fun xs => Part.get_mem (P.run_dom oracle h xs)

end OracleSearchProgram
end GenLimit.Support
