import GenLimit.Support.OracleSearchProgram

/-! # Ordinary computability of a certified truth-table oracle procedure -/

namespace GenLimit.Support

theorem TruthTableProgram.run_computable (P : TruthTableProgram) {oracle : ℕ → ℕ}
    (ho : Computable oracle) : Computable (P.run oracle) :=
  P.output_computable.comp (Computable.pair Computable.id
    ((map_computable ho).comp P.queries_primrec.to_comp))

end GenLimit.Support
