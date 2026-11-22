import GenLimit.Paper00A_PositiveDataInference.Effective.Corollaries
import GenLimit.Support.ComputableLists
import Mathlib.Computability.Halting

/-!
# Angluin's Theorem 3

A terminating procedure can return its complete finite output as a list.
Angluin's Condition 1 only requires enumeration of a finite range. To separate
the two, use two languages per machine code: a whole column and the part of
that column for which bounded evaluation has yet to halt. Pairing codes the
disjoint columns of words; height zero belongs even to an immediately halting
machine's column.
-/

namespace GenLimit.Angluin

/-- Condition 1': a single halting procedure returns a complete tell-tale
for each family member. List order and repeated outputs are immaterial. -/
def ConditionOnePrime (F : EffectiveIndexedFamily) : Prop :=
  ∃ output : ℕ → List ℕ, Computable output ∧
    ∀ i, IsTellTale F.language i (output i).toFinset

namespace HaltingTellTales

open Nat.Partrec (Code)
open Denumerable (ofNat)

private def language (i : ℕ) : Set ℕ :=
  {x | x.unpair.1 = i.unpair.1 ∧
    (i.unpair.2 = 0 ∨ Code.evaln x.unpair.2 (ofNat Code i.unpair.1) 0 = none)}

private def membership (i x : ℕ) : Bool :=
  x.unpair.1 == i.unpair.1 &&
    (i.unpair.2 == 0 || !(Code.evaln x.unpair.2 (ofNat Code i.unpair.1) 0).isSome)

private theorem membership_computable : Computable₂ membership := by
  have row := Primrec.fst.comp Primrec.unpair
  have height := Primrec.snd.comp Primrec.unpair
  have hcode : Primrec (fun z : ℕ × ℕ => ofNat Code z.1.unpair.1) := (Primrec.ofNat Code).comp (row.comp Primrec.fst)
  have hrun := Code.primrec_evaln.comp
    (((height.comp Primrec.snd).pair hcode).pair (Primrec.const 0))
  exact (Primrec.and.comp (Primrec.beq.comp (row.comp Primrec.snd) (row.comp Primrec.fst))
    (Primrec.or.comp (Primrec.beq.comp (height.comp Primrec.fst) (Primrec.const 0))
      (Primrec.not.comp (Primrec.option_isSome.comp hrun)))).to_comp.to₂

private def family : EffectiveIndexedFamily where
  language := language
  membership := membership
  membership_spec := by
    intro i x
    simp [membership, language]
  membership_computable := membership_computable
  nonempty := by
    intro i
    exact ⟨Nat.pair i.unpair.1 0, by simp [language, Code.evaln]⟩

private theorem finiteThickness : ConditionThree family.language := by
  intro S hS
  obtain ⟨x, hx⟩ := hS
  have hfin : ({language (Nat.pair x.unpair.1 0),
      language (Nat.pair x.unpair.1 1)} : Set (Set ℕ)).Finite := by simp
  apply hfin.subset
  rintro _ ⟨⟨i, rfl⟩, h⟩
  have hr := (h hx : x ∈ language i).1
  change language i ∈ _
  by_cases hi : i.unpair.2 = 0
  · left
    ext y
    simp [language, hi, hr]
  · right
    apply Set.mem_singleton_iff.mpr
    ext y
    simp [language, hi, hr]

private theorem all_in_cut_iff (c : Code) (xs : List ℕ)
    (ht : IsTellTale language (Nat.pair (Encodable.encode c) 0) xs.toFinset) :
    xs.all (membership (Nat.pair (Encodable.encode c) 1)) = true ↔
      ¬ (c.eval 0).Dom := by
  let r := Encodable.encode c
  have hcut : language (Nat.pair r 1) ⊆ language (Nat.pair r 0) := by
    intro y hy
    simpa [language] using (show y.unpair.1 = r by simpa using hy.1)
  rw [List.all_eq_true]
  constructor
  · intro hall hdom
    have hcontains : (↑xs.toFinset : Set ℕ) ⊆ language (Nat.pair r 1) := by
      intro y hy
      exact (family.membership_spec _ _).1 (hall y (by simpa using hy))
    have heq := ht.2 (Nat.pair r 1) hcontains hcut
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp hv
    have hbad := heq (show Nat.pair r k ∈ language (Nat.pair r 0) by simp [language])
    have hn : Code.evaln k c 0 = none := by simpa [language, r] using hbad
    simp [hn] at hk
  · intro hdom y hy
    apply (family.membership_spec _ _).2
    have hrow := (ht.1 (by simpa using hy : y ∈ xs.toFinset)).1
    change y ∈ language (Nat.pair (Encodable.encode c) 1)
    simp only [language, Set.mem_setOf_eq, Nat.unpair_pair, Denumerable.ofNat_encode,
      one_ne_zero, false_or]
    refine ⟨by simpa using hrow, ?_⟩
    cases he : Code.evaln y.unpair.2 c 0 with
    | none => rfl
    | some v => exact False.elim (hdom (Part.dom_iff_mem.mpr
        ⟨v, Code.evaln_sound (show v ∈ Code.evaln y.unpair.2 c 0 from he)⟩))

private theorem noCompletedOutput : ¬ ConditionOnePrime family := by
  rintro ⟨output, hcomp, ht⟩
  let idx (tag : ℕ) (c : Code) := Nat.pair (Encodable.encode c) tag
  have hi (tag) : Computable (idx tag) :=
    (Primrec₂.natPair.comp Primrec.encode (Primrec.const tag)).to_comp
  have hb := GenLimit.Support.ComputableLists.all (hcomp.comp (hi 0))
    ((membership_computable.comp ((hi 1).comp Computable.fst) Computable.snd).to₂)
  apply ComputablePred.halting_problem 0
  apply ComputablePred.computable_iff.mpr
  refine ⟨_, Primrec.not.to_comp.comp hb, ?_⟩
  funext c
  apply propext
  have he := all_in_cut_iff c (output (idx 0 c)) (ht (idx 0 c))
  classical
  simpa only [Bool.not_eq_true', Bool.eq_false_iff, not_not] using (not_congr he).symm

end HaltingTellTales

/-- Angluin (1980), Theorem 3. -/
theorem theoremThree : ∃ F : EffectiveIndexedFamily,
    EffectiveInferrable F ∧ ¬ ConditionOnePrime F :=
  ⟨_, corollaryTwo _ HaltingTellTales.finiteThickness, HaltingTellTales.noCompletedOutput⟩

end GenLimit.Angluin
