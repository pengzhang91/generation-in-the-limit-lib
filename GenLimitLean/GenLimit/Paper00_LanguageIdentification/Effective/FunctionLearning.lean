import GenLimit.Paper00_LanguageIdentification.Effective.PrimitivePrograms
import GenLimit.Paper00_LanguageIdentification.Effective.RestrictedTexts

/-! # Gold's enumeration learners for primitive recursive functions (I.4 and I.7) -/

namespace GenLimit.Gold.Effective

open Nat.Partrec (Code)
open GenLimit.Support PrimitivePrograms

/-- The fixed methodical informant supplies membership bits in word order. -/
noncomputable def bit (L : Language) (x : ℕ) : ℕ := by
  classical exact if x ∈ L then 1 else 0

def methodical : Method ℕ := fun L => {bit L}
def primitiveLanguages : Set Language := {L | Primrec (bit L)}
def recursiveLanguages : Set Language := {L | Computable (bit L)}
def enumerableLanguages : Set Language := {L | ∃ e, Generator e L}

private def fits (h : List ℕ) (i : ℕ) :=
  boundedAll (fun (p : List ℕ × ℕ) x => p.1[x]? == some (evaluate p.2 x)) (h, i) h.length

private theorem fits_comp : Computable₂ fits := by
  have test := Primrec.beq.to_comp.comp
    (Computable.list_getElem?.comp (Computable.fst.comp Computable.fst) Computable.snd)
    (Computable.option_some.comp (evaluate_computable.comp (Computable.snd.comp Computable.fst) Computable.snd))
  apply ((boundedAll_computable test.to₂).comp Computable.id
    (Computable.list_length.comp Computable.fst)).of_eq
  intro p
  congr 1
  funext a x
  apply Bool.eq_iff_iff.mpr
  simp

private theorem fits_spec (s : ℕ → ℕ) (i t : ℕ) :
    fits (textPrefix s t) i = true ↔ ∀ x < t, s x = evaluate i x := by
  rw [fits, boundedAll_eq_true_iff, textPrefix_length]
  exact forall_congr' fun x => imp_congr_right fun hx => by simp [textPrefix, hx]

private def guess (h : List ℕ) :=
  (firstTrue fits h h.length).getD 0

private theorem guess_comp : Computable guess :=
  Computable.option_getD ((firstTrue_computable fits_comp).comp Computable.id Computable.list_length)
    (Computable.const 0)

/-- A single effective learner eventually guesses a fixed program computing
the whole presented function at every argument. -/
theorem learns_primitive_functions : ∃ M : List ℕ → Code, Computable M ∧
    ∀ s : ℕ → ℕ, Primrec s → ∃ c, (∀ x, c.eval x = Part.some (s x)) ∧
      ∃ T, ∀ t ≥ T, M (textPrefix s t) = c := by
  classical
  refine ⟨fun h => program (guess h), program_computable.comp guess_comp, fun s hs => ?_⟩
  let ex := exists_index hs
  let k := Nat.find ex
  have hk : evaluate k = s := Nat.find_spec ex
  have hr (i : ℕ) (hi : i < k) : ∃ S, ∀ t ≥ S, fits (textPrefix s t) i = false := by
    have hn := Nat.find_min ex hi
    obtain ⟨x, hx⟩ : ∃ x, s x ≠ evaluate i x := by
      by_contra! h
      exact hn (funext fun x => (h x).symm)
    exact ⟨x + 1, fun t ht => Bool.eq_false_iff.mpr fun h => hx ((fits_spec ..).mp h x (by omega))⟩
  obtain ⟨S, hS⟩ := eventually_forall_lt hr
  refine ⟨program k, fun x => (program_spec k x).trans (congrArg Part.some (congrFun hk x)),
    max (k + 1) S, fun t ht => ?_⟩
  apply congrArg program
  have hkt : k < t := lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left ..).trans ht)
  have good := (fits_spec s k t).mpr fun x _ => (congrFun hk x).symm
  have noneFalse : firstTrue fits (textPrefix s t) t ≠ none :=
    fun bad => Bool.noConfusion (good.symm.trans ((firstTrue_eq_none_iff ..).mp bad k hkt))
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp noneFalse
  have hjk := firstTrue_le_of_true hj hkt good
  have hkj : k ≤ j := by
    by_contra! h
    have bad := hS t ((le_max_right ..).trans ht) j h
    exact Bool.noConfusion ((firstTrue_spec hj).2.1.symm.trans bad)
  simp [guess, hj, Nat.le_antisymm hjk hkj]

/-- Appendix I.4. -/
theorem primitive_languages_methodical :
    Identifiable Tester methodical primitiveLanguages := by
  obtain ⟨M, hc, hm⟩ := learns_primitive_functions
  refine ⟨M, hc, fun L hl s hs => ?_⟩
  obtain rfl : s = bit L := hs
  obtain ⟨c, h, stable⟩ := hm (bit L) hl
  exact ⟨c, fun x => ⟨fun hx => by simp [h, bit, hx], fun hx => by simp [h, bit, hx]⟩, stable⟩

/-- Appendix I.7. The stabilized program computes the actual text and
therefore has precisely the target language as its range. -/
theorem generator_primitive_text (C : Set Language) :
    Identifiable Generator primitiveRecursiveText C := by
  obtain ⟨M, hc, hm⟩ := learns_primitive_functions
  refine ⟨M, hc, fun L _ s hs => ?_⟩
  obtain ⟨c, h, stable⟩ := hm s hs.1
  refine ⟨c, fun x => ?_, stable⟩
  rw [← hs.2]
  simp [Set.mem_range, h, eq_comm]

theorem enumerable_languages_primitive_text :
    Identifiable Generator primitiveRecursiveText enumerableLanguages :=
  generator_primitive_text _

end GenLimit.Gold.Effective
