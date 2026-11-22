import GenLimit.Paper00A_PositiveDataInference.Effective.InferenceMachine
import GenLimit.Paper00A_PositiveDataInference.Effective.Corollaries
import GenLimit.Support.StreamPrefixText

/-!
# Angluin's Theorem 4

Each row contains a whole column and at most two distinct finite initial
segments. A conservative identifier must actually conjecture the unique full
index on the canonical text. The partial program searching for such a guess
has a row of its own. Its return value bounds the observed sample, producing
a finite member on which the same guess is irrevocable.
-/

namespace GenLimit.Angluin.ConservativeSeparation

open Nat.Partrec (Code)
open Denumerable (ofNat)

private abbrev row (n : ℕ) := n.unpair.1
private abbrev col (n : ℕ) := n.unpair.2

private def cutoff (r t : ℕ) :=
  (Code.evaln t (ofNat Code r) r).getD 0

private def language (i : ℕ) : Set ℕ :=
  {x | row x = row i ∧ (col i = 0 ∨ col x ≤ cutoff (row i) (col i).pred)}

private theorem cutoff_comp : Computable₂ cutoff := by
  have hc : Primrec (fun p : ℕ × ℕ => ofNat Code p.1) := (Primrec.ofNat Code).comp Primrec.fst
  exact (Computable.option_getD
    (Code.primrec_evaln.comp ((Primrec.snd.pair hc).pair Primrec.fst)).to_comp
    (Computable.const 0)).to₂

private def family : EffectiveIndexedFamily where
  language := language
  membership i x := row x == row i && (col i == 0 || decide (col x ≤ cutoff (row i) (col i).pred))
  membership_spec := by intros; simp [language]
  membership_computable := by
    have hr : Computable row := (Primrec.fst.comp Primrec.unpair).to_comp
    have hc : Computable col := (Primrec.snd.comp Primrec.unpair).to_comp
    exact (Primrec.and.to_comp.comp (Primrec.beq.to_comp.comp (hr.comp Computable.snd) (hr.comp Computable.fst))
      (Primrec.or.to_comp.comp (Primrec.beq.to_comp.comp (hc.comp Computable.fst) (Computable.const 0))
        (Primrec.nat_le.decide.to_comp.comp (hc.comp Computable.snd)
          (cutoff_comp.comp (hr.comp Computable.fst) (Primrec.pred.to_comp.comp (hc.comp Computable.fst)))))).to₂
  nonempty i := ⟨Nat.pair (row i) 0, by simp [language, row, col]⟩

private theorem finiteThickness : ConditionThree family.language := by
  intro S hS
  obtain ⟨x, hx⟩ := hS
  let r := row x
  obtain ⟨b, hb⟩ : ∃ b, ∀ t, cutoff r t = 0 ∨ cutoff r t = b := by
    classical
    by_cases hh : ((ofNat Code r).eval r).Dom
    · refine ⟨((ofNat Code r).eval r).get hh, fun t => ?_⟩
      cases he : Code.evaln t (ofNat Code r) r with
      | none => exact Or.inl (by simp [cutoff, he])
      | some v =>
        right
        simpa [cutoff, he] using Part.mem_unique (Code.evaln_sound (Option.mem_def.mpr he)) (Part.get_mem hh)
    · refine ⟨0, fun t => Or.inl ?_⟩
      cases he : Code.evaln t (ofNat Code r) r with
      | none => simp [cutoff, he]
      | some v => exact False.elim (hh (Part.dom_iff_mem.mpr
          ⟨v, Code.evaln_sound (Option.mem_def.mpr he)⟩))
  let segment (b : ℕ) := {y : ℕ | row y = r ∧ col y ≤ b}
  apply (show ({ {y : ℕ | row y = r}, segment 0, segment b} : Set (Set ℕ)).Finite by simp).subset
  rintro _ ⟨⟨i, rfl⟩, hs⟩
  have hr : row i = r := (hs hx : x ∈ language i).1.symm
  change language i ∈ _
  by_cases ht : col i = 0
  · left; ext; simp [language, ht, hr]
  · right
    rcases hb (col i).pred with hz | he
    · left; ext; simp only [language, segment, hr, ht, false_or, hz]
    · right; apply Set.mem_singleton_iff.mpr
      ext; simp only [language, segment, hr, ht, false_or, he]

private theorem full_unique {r j} (heq : language j = language (Nat.pair r 0)) :
    j = Nat.pair r 0 := by
  have h (k : ℕ) : Nat.pair r k ∈ language j := heq ▸ (by simp [language, row, col])
  have hr : r = row j := by simpa [row] using (h 0).1
  have ht := (h (cutoff (row j) (col j).pred + 1)).2
  simp only [col, Nat.unpair_pair, Nat.not_succ_le_self, or_false] at ht
  calc j = Nat.pair (row j) (col j) := (Nat.pair_unpair j).symm
       _ = _ := congrArg₂ Nat.pair hr.symm ht

private theorem canonical (r : ℕ) :
    Generic.Presents (Nat.pair r) (language (Nat.pair r 0)) := by
  ext x
  change (∃ n, Nat.pair r n = x) ↔ _
  constructor
  · rintro ⟨n, rfl⟩; simp [language, row, col]
  · intro hx
    have hr : row x = r := by simpa [row] using hx.1
    exact ⟨col x, by simp [← hr, row, col]⟩

/-- Search the machine's effective event graph on a canonical text for a
guess of the full index. Return exactly the number of examples read. -/
private theorem guessSearch (M : InferenceMachine) :
    ∃ f : ℕ →. ℕ, Partrec f ∧ ∀ r,
      ((∃ n k, M.Guesses (Nat.pair r) n k (Nat.pair r 0)) → (f r).Dom) ∧
      ∀ n ∈ f r, ∃ k, M.Guesses (Nat.pair r) n k (Nat.pair r 0) := by
  obtain ⟨e, he⟩ := M.exists_guess_code
  let input (r w : ℕ) := Encodable.encode (textPrefix (Nat.pair r) (row w), row (col w))
  let check (r w : ℕ) := decide (Code.evaln (col (col w)) e (input r w) =
    some (Nat.pair r 0))
  have hc : Computable₂ check := by
    have hr : Primrec (fun p : ℕ × ℕ => row p.2) :=
      Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
    have hrest : Primrec (fun p : ℕ × ℕ => (col p.2).unpair) :=
      Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
    have hpref : Primrec (fun p : ℕ × ℕ => textPrefix (Nat.pair p.1) (row p.2)) :=
      Primrec.list_map (Primrec.list_range.comp hr)
        (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
    have hi := Primrec.encode.comp (hpref.pair (Primrec.fst.comp hrest))
    have hout : Primrec (fun p : ℕ × ℕ => some (Nat.pair p.1 0)) :=
      Primrec.option_some.comp (Primrec₂.natPair.comp Primrec.fst (Primrec.const 0))
    exact (Primrec.eq.decide.comp (Code.primrec_evaln.comp
      (((Primrec.snd.comp hrest).pair (Primrec.const e)).pair hi)) hout).to_comp.to₂
  let search (r : ℕ) := Nat.rfind (fun w => Part.some (check r w))
  have hsearch : Partrec search := Partrec.rfind hc.partrec₂
  refine ⟨fun r => (search r).map row,
    hsearch.map ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp.to₂), fun r => ⟨?_, ?_⟩⟩
  · rintro ⟨n, k, hg⟩
    obtain ⟨b, hb⟩ := Code.evaln_complete.mp ((he _ _ _).2 hg)
    have hh : (search r).Dom := by
      apply Nat.rfind_dom.mpr
      refine ⟨Nat.pair n (Nat.pair k b), ?_, fun _ => trivial⟩
      simpa [check, input, row, col] using Option.mem_def.mp hb
    exact Part.dom_iff_mem.mpr ⟨_, Part.mem_map row (Part.get_mem hh)⟩
  · intro n hn
    obtain ⟨w, hw, rfl⟩ := (Part.mem_map_iff _).mp hn
    refine ⟨row (col w), (he _ _ _).1 (Code.evaln_sound (k := col (col w)) ?_)⟩
    have hcheck : true ∈ Part.some (check r w) := Nat.rfind_spec hw
    simpa [check, input, Option.mem_def] using hcheck

private theorem separation : ¬ ∃ M : InferenceMachine, M.Identifies family ∧ M.Conservative family := by
  rintro ⟨M, hid, hcons⟩
  obtain ⟨f, hf, hsearch⟩ := guessSearch M
  obtain ⟨c, hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hf)
  let r := Encodable.encode c
  obtain ⟨n, k, j, hg, heq, _⟩ := hid (Nat.pair r 0) _ (canonical r)
  obtain rfl := full_unique heq
  obtain ⟨m, hm⟩ := Part.dom_iff_mem.mp ((hsearch r).1 ⟨n, k, hg⟩)
  obtain ⟨l, hl⟩ := (hsearch r).2 m hm
  obtain ⟨b, hb⟩ := Code.evaln_complete.mp (show m ∈ c.eval r from hc ▸ hm)
  have hbound : cutoff r b = m := by simp [cutoff, r, Option.mem_def.mp hb]
  let j := Nat.pair r (b + 1)
  let hist := textPrefix (Nat.pair r) m
  let tail := GenLimit.Support.exactPresentation (family.language j) (family.nonempty j)
  let s := GenLimit.Support.prependStream hist tail
  have hp : Generic.Presents s (family.language j) := by
    apply GenLimit.Support.prependStream_presents _ (GenLimit.Support.exactPresentation_presents _ _)
    intro y hy
    obtain ⟨t, ht, rfl⟩ := mem_textPrefix_iff.mp hy
    change Nat.pair r t ∈ language (Nat.pair r (b + 1))
    simpa [language, row, col, hbound] using ht.le
  have hprefix : textPrefix s m = hist := by
    have hz := GenLimit.Support.textPrefix_prependStream hist tail 0
    simpa [hist] using hz
  have hagain : M.Guesses s m l (Nat.pair r 0) := by
    simpa only [InferenceMachine.Guesses, hprefix] using hl
  have hbad := InferenceMachine.correct_of_compatible_guess hid hcons hp hagain (by
    intro x hx; change x ∈ language (Nat.pair r 0)
    simpa [language, row, col] using (show row x = r by simpa [j, row] using hx.1))
  have hbnd := (hbad ▸ (show Nat.pair r (m + 1) ∈ family.language (Nat.pair r 0) by
    change _ ∈ language _; simp [language, row, col]) : Nat.pair r (m + 1) ∈ family.language j)
  change _ ∈ language _ at hbnd
  simp [language, row, col, j, hbound] at hbnd

end GenLimit.Angluin.ConservativeSeparation

namespace GenLimit.Angluin

/-- Angluin (1980), Theorem 4. -/
theorem theoremFour : ∃ F : EffectiveIndexedFamily, EffectiveInferrable F ∧
    ¬ ∃ M : InferenceMachine, M.Identifies F ∧ M.Conservative F :=
  ⟨_, corollaryTwo _ ConservativeSeparation.finiteThickness, ConservativeSeparation.separation⟩

end GenLimit.Angluin
