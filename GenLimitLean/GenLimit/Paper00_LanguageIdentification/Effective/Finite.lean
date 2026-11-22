import GenLimit.Paper00_LanguageIdentification.Effective.Names
import GenLimit.Paper00_LanguageIdentification.Text.Finite
import GenLimit.Support.ComputableLists
import GenLimit.Support.ComputableSearch

/-! # Finite languages from arbitrary positive text (Appendix I.6) -/

namespace GenLimit.Gold.Effective

open Nat.Partrec (Code)
open GenLimit.Support

def arbitraryText : Method ℕ := fun L => {s | Presents s L}

private def insertNew (seen : List ℕ) (x : ℕ) :=
  bif listContains seen x then seen else x :: seen

private def observations (h : List ℕ) := h.foldl insertNew []

private theorem observations_comp : Computable observations := by
  have hc : Computable₂ insertNew :=
    (listContains_computable.cond Computable.fst
      (Computable.list_cons.comp Computable.snd Computable.fst)).to₂
  exact ComputableLists.foldl Computable.id (Computable.const [])
    ((hc.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)).to₂)

private theorem mem_fold (x : ℕ) (h seen : List ℕ) :
    x ∈ h.foldl insertNew seen ↔ x ∈ seen ∨ x ∈ h := by
  induction h generalizing seen with
  | nil => simp
  | cons y h ih =>
    simp only [List.foldl_cons, ih, List.mem_cons]
    by_cases hy : y ∈ seen
    · simp [insertNew, listContains, hy]
      grind
    · simp [insertNew, listContains, hy]
      tauto

private theorem mem_observations (x : ℕ) (h : List ℕ) :
    x ∈ observations h ↔ x ∈ h := by simp [observations, mem_fold]

/-- The index is specialized only when a previously unseen word arrives. -/
theorem finite_tester_identification :
    Identifiable Tester arbitraryText Text.finiteLanguages := by
  obtain ⟨compileList, hc, spec⟩ := compile (f := fun (h : List ℕ) x =>
    Part.some (listContains h x).toNat)
    (((Primrec.dom_bool Bool.toNat).to_comp.comp listContains_computable).partrec)
  refine ⟨fun h => compileList (observations h), hc.comp observations_comp, ?_⟩
  intro L hL s hs
  have hp : Presents s L := hs
  obtain ⟨T, hT⟩ := Text.eventually_sample_eq_of_finite hp hL
  have seen (x : ℕ) : x ∈ observations (textPrefix s T) ↔ x ∈ L := by
    rw [mem_observations, ← hT T le_rfl, ← textPrefix_toFinset]
    simp
  refine ⟨compileList (observations (textPrefix s T)), fun x => ?_, T, fun t ht => ?_⟩
  · rw [spec]
    constructor
    · intro hx
      simp [listContains, (seen x).mpr hx]
    · intro hx
      simp [listContains, seen x, hx]
  · apply congrArg compileList
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t _ ih =>
      have hx := (seen (s t)).mpr (hp ▸ Set.mem_range_self t)
      rw [textPrefix_succ]
      change (textPrefix s t ++ [s t]).foldl insertNew [] = _
      rw [List.foldl_append]
      change insertNew (observations (textPrefix s t)) (s t) = _
      simp [ih, insertNew, listContains, hx]

end GenLimit.Gold.Effective
