import GenLimit.Paper08_HallucinationDetection.Definitions

/-!
# #08 Hallucination Detection: negative examples

This is the algorithm and proof of Theorem 2.3 in Karbasi, Montasser, Sous,
and Velegkas.  The detector asks about exactly the finitely many negatively
labeled domain points seen so far and rejects as soon as one belongs to the
candidate set.
-/

namespace GenLimit.HallucinationDetection

noncomputable local instance negativeExamplesPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The first `t` labeled examples as a chronological list. -/
def labeledPrefix (stream : LabeledStream α) (t : ℕ) : List (α × Bool) :=
  List.ofFn (fun i : Fin t => stream i)

theorem mem_labeledPrefix_iff
    {stream : LabeledStream α} {t : ℕ} {q : α × Bool} :
    q ∈ labeledPrefix stream t ↔ ∃ i < t, stream i = q := by
  constructor
  · intro hq
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hq
    exact ⟨i, i.isLt, hi⟩
  · rintro ⟨i, hi, hiq⟩
    exact List.mem_ofFn.mpr ⟨⟨i, hi⟩, hiq⟩

/-- Query every point carrying a negative label and reject at the first
positive oracle response. -/
def negativeExampleTree : List (α × Bool) → OracleTree α
  | [] => .answer true
  | (_x, true) :: xs => negativeExampleTree xs
  | (x, false) :: xs =>
      .query x (.answer false) (negativeExampleTree xs)

theorem eval_negativeExampleTree_eq_true_iff
    (G : Set α) (xs : List (α × Bool)) :
    OracleTree.eval G (negativeExampleTree xs) = true ↔
      ∀ x b, (x, b) ∈ xs → b = false → x ∉ G := by
  classical
  induction xs with
  | nil => simp [negativeExampleTree, OracleTree.eval]
  | cons q xs ih =>
      obtain ⟨x, b⟩ := q
      cases b <;> by_cases hxG : x ∈ G <;>
        simp [negativeExampleTree, OracleTree.eval, hxG, ih]

/-- The detector used in Theorem 2.3. -/
def negativeExampleDetector : NegativeExampleDetector α :=
  fun _t xs => negativeExampleTree (List.ofFn xs)

/-- Theorem 2.3.  The proof does not use countability of the indexed
collection; a complete labeled enumeration of the countable domain supplies
all of the information needed by the detector. -/
theorem theorem_2_3
    (C : GenLimit.Generic.LanguageFamily α) :
    DetectableWithNegativeExamples C := by
  classical
  refine ⟨negativeExampleDetector, ?_⟩
  intro z stream hstream G
  rcases hstream with ⟨hcomplete, hlabels⟩
  by_cases hGK : G ⊆ C z
  · refine ⟨0, ?_⟩
    intro t _ht
    rw [NegativeDetectorCorrectAt, negativeDetectorOutput,
      negativeExampleDetector, eval_negativeExampleTree_eq_true_iff]
    constructor
    · intro _
      exact hGK
    · intro _ x b hmem hbfalse hxG
      obtain ⟨i, _hit, hi⟩ :=
        mem_labeledPrefix_iff.mp (show (x, b) ∈ labeledPrefix stream t by
          simpa [labeledPrefix] using hmem)
      have hfirst : (stream i).1 = x := congrArg Prod.fst hi
      have hsecond : (stream i).2 = b := congrArg Prod.snd hi
      have hxnotTarget : x ∉ C z := by
        intro hxTarget
        have htrue : (stream i).2 = true :=
          (hlabels i).mpr (by simpa [hfirst] using hxTarget)
        rw [hsecond, hbfalse] at htrue
        cases htrue
      exact hxnotTarget (hGK hxG)
  · obtain ⟨x, hxG, hxnotTarget⟩ := Set.not_subset.mp hGK
    have hxUniv : x ∈ Set.univ := Set.mem_univ x
    rw [← hcomplete] at hxUniv
    obtain ⟨i, hi⟩ := hxUniv
    have hlabelFalse : (stream i).2 = false := by
      cases hvalue : (stream i).2 with
      | false => rfl
      | true =>
          have hxTarget : (stream i).1 ∈ C z :=
            (hlabels i).mp hvalue
          exact False.elim (hxnotTarget (by simpa [hi] using hxTarget))
    refine ⟨i + 1, ?_⟩
    intro t ht
    have hit : i < t :=
      lt_of_lt_of_le (Nat.lt_succ_self i) ht
    rw [NegativeDetectorCorrectAt, negativeDetectorOutput,
      negativeExampleDetector, eval_negativeExampleTree_eq_true_iff]
    constructor
    · intro hout
      have hpair : stream i ∈ labeledPrefix stream t :=
        mem_labeledPrefix_iff.mpr ⟨i, hit, rfl⟩
      have hxnotG := hout (stream i).1 (stream i).2 hpair hlabelFalse
      exact False.elim (hxnotG (by simpa [hi] using hxG))
    · intro hsubset
      exact False.elim (hGK hsubset)

end GenLimit.HallucinationDetection
