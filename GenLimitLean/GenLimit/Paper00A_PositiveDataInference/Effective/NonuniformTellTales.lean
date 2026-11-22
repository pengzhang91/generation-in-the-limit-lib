import GenLimit.Paper00A_PositiveDataInference.Effective.Necessity
import Mathlib.Computability.PartrecCode
import Mathlib.Data.Nat.Lattice

/-!
# Angluin's Theorem 2

Diagonalize against Condition 1 using its equivalence with effective inference.
Each row has a full data column and competitors with finite data prefixes.
A competitor receives private marker words as soon as another computation
returns a larger cutoff. Thus only maximal cutoffs can give a proper sublanguage
of the full column. A uniform tell-tale enumerator would itself have a row on
which such a maximal cutoff already contains its entire tell-tale.
-/

namespace GenLimit.Angluin.NonuniformTellTales

open Nat.Partrec (Code)
open Denumerable (ofNat)

private abbrev row (x : ℕ) := x.unpair.1
private abbrev col (x : ℕ) := x.unpair.2
private def word (r tag height : ℕ) := Nat.pair (Nat.pair r tag) height

private def cutoff (r stage : ℕ) : ℕ :=
  (Code.evaln (col stage) (ofNat Code r) (Nat.pair r (row stage))).getD 0

private theorem cutoff_computable : Computable₂ cutoff := by
  have hs : Primrec (fun p : ℕ × ℕ => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have he := Code.primrec_evaln.comp
    (((Primrec.snd.comp hs).pair ((Primrec.ofNat Code).comp Primrec.fst)).pair
      (Primrec₂.natPair.comp Primrec.fst (Primrec.fst.comp hs)))
  exact (Computable.option_getD he.to_comp (Computable.const 0)).to₂

/-- Tag zero records ordinary data. Every other tag is private to one
competitor and can occur only in the presence of a larger cutoff. -/
private def language (i : ℕ) : Set ℕ :=
  {x | row (row x) = row i ∧
    (col (row x) = 0 ∧ (col i = 0 ∨ col x ≤ cutoff (row i) (col i).pred) ∨
      col i ≠ 0 ∧ col (row x) = col i ∧ cutoff (row i) (col i).pred < cutoff (row i) (col x))}

private def membership (i x : ℕ) : Bool :=
  row (row x) == row i &&
    ((col (row x) == 0 && (col i == 0 || decide (col x ≤ cutoff (row i) (col i).pred))) ||
      (!(col i == 0) && (col (row x) == col i) &&
        decide (cutoff (row i) (col i).pred < cutoff (row i) (col x))))

private theorem membership_computable : Computable₂ membership := by
  have hr : Computable row := (Primrec.fst.comp Primrec.unpair).to_comp
  have hc : Computable col := (Primrec.snd.comp Primrec.unpair).to_comp
  have hi : Computable (fun p : ℕ × ℕ => row p.1) := hr.comp Computable.fst
  have ht : Computable (fun p : ℕ × ℕ => col p.1) := hc.comp Computable.fst
  have hw : Computable (fun p : ℕ × ℕ => row p.2) := hr.comp Computable.snd
  have hk : Computable (fun p : ℕ × ℕ => col p.2) := hc.comp Computable.snd
  have hbound := cutoff_computable.comp hi (Primrec.pred.to_comp.comp ht)
  have hzero := Primrec.beq.to_comp.comp ht (Computable.const 0)
  exact (Primrec.and.to_comp.comp (Primrec.beq.to_comp.comp (hr.comp hw) hi)
    (Primrec.or.to_comp.comp
      (Primrec.and.to_comp.comp (Primrec.beq.to_comp.comp (hc.comp hw) (Computable.const 0))
        (Primrec.or.to_comp.comp hzero (Primrec.nat_le.decide.to_comp.comp hk hbound)))
      (Primrec.and.to_comp.comp
        (Primrec.and.to_comp.comp (Primrec.not.to_comp.comp hzero)
          (Primrec.beq.to_comp.comp (hc.comp hw) ht))
        (Primrec.nat_lt.decide.to_comp.comp hbound (cutoff_computable.comp hi hk))))).to₂

@[simp] private theorem word_mem {r tag k s t : ℕ} :
    word r tag k ∈ language (Nat.pair s t) ↔
      r = s ∧ (tag = 0 ∧ (t = 0 ∨ k ≤ cutoff s t.pred) ∨
        t ≠ 0 ∧ tag = t ∧ cutoff s t.pred < cutoff s k) := by
  simp [word, language, row, col]

private theorem word_rep (x : ℕ) : word (row (row x)) (col (row x)) (col x) = x := by
  simp [word, row, col]

private def family : EffectiveIndexedFamily where
  language := language
  membership := membership
  membership_spec := by intros; simp [membership, language, and_assoc]
  membership_computable := membership_computable
  nonempty := by
    intro i
    obtain ⟨⟨r, t⟩, rfl⟩ := Nat.pairEquiv.surjective i
    exact ⟨word r 0 0, (word_mem).mpr ⟨rfl, Or.inl ⟨rfl, Or.inr (Nat.zero_le _)⟩⟩⟩

private theorem full_tellTale (r : ℕ) : ∃ T, IsTellTale language (Nat.pair r 0) T := by
  classical
  by_cases hb : ∃ n, ∀ k, cutoff r k ≤ cutoff r n
  · obtain ⟨n, hn⟩ := hb
    refine ⟨{word r 0 (cutoff r n + 1)}, by simp, ?_⟩
    intro j h _
    obtain ⟨⟨s, t⟩, rfl⟩ := Nat.pairEquiv.surjective j
    have hmem := word_mem.mp (h (Finset.mem_singleton_self _))
    obtain ⟨rfl, hm⟩ := hmem
    by_cases ht : t = 0
    · subst t; rfl
    · simp [ht] at hm
      have := hn (t - 1)
      omega
  · refine ⟨{word r 0 0}, by simp, ?_⟩
    intro j h hsub
    obtain ⟨⟨s, t⟩, rfl⟩ := Nat.pairEquiv.surjective j
    obtain ⟨rfl, _⟩ := word_mem.mp (h (Finset.mem_singleton_self _))
    by_cases ht : t = 0
    · subst t; rfl
    · obtain ⟨k, hk⟩ : ∃ k, cutoff r t.pred < cutoff r k := by
        by_contra! h
        exact hb ⟨_, h⟩
      have hmark := hsub (show word r t k ∈ language (Nat.pair r t) by
        exact word_mem.mpr ⟨rfl, Or.inr ⟨ht, rfl, hk⟩⟩)
      simp [ht] at hmark

private theorem competitor_tellTale (r n : ℕ) :
    ∃ T, IsTellTale language (Nat.pair r (n + 1)) T := by
  classical
  by_cases hm : ∃ k, cutoff r n < cutoff r k
  · obtain ⟨k, hk⟩ := hm
    refine ⟨{word r (n + 1) k}, by simp [hk], ?_⟩
    intro j hj _
    obtain ⟨⟨s, t⟩, rfl⟩ := Nat.pairEquiv.surjective j
    obtain ⟨rfl, h⟩ := word_mem.mp (hj (Finset.mem_singleton_self _))
    simp only [Nat.succ_ne_zero, false_and, false_or] at h
    rw [h.2.1]
    rfl
  · refine ⟨{word r 0 (cutoff r n)}, by simp, ?_⟩
    intro j hj _ x hx
    obtain ⟨⟨s, t⟩, rfl⟩ := Nat.pairEquiv.surjective j
    obtain ⟨rfl, h⟩ := word_mem.mp (hj (Finset.mem_singleton_self _))
    rw [← word_rep x] at hx ⊢
    obtain ⟨hr, hd | hmark⟩ := word_mem.mp hx
    · apply word_mem.mpr
      refine ⟨hr, Or.inl ⟨hd.1, ?_⟩⟩
      have hle : col x ≤ cutoff r n := by simpa using hd.2
      rcases h with ⟨_, hzero | hbound⟩ | ⟨hne, heq, _⟩
      · exact Or.inl hzero
      · exact Or.inr (hle.trans hbound)
      · exact False.elim (hne heq.symm)
    · exact False.elim (hm ⟨col x, by simpa using hmark.2.2⟩)

private theorem conditionTwo : ConditionTwo family.language := by
  intro i
  obtain ⟨⟨r, t⟩, rfl⟩ := Nat.pairEquiv.surjective i
  cases t with
  | zero => exact full_tellTale r
  | succ n => exact competitor_tellTale r n

private theorem notConditionOne : ¬ ConditionOne family := by
  rintro ⟨emit, hcomp, hgood⟩
  let f (z : ℕ) := (emit (Nat.pair (row z) 0) (col z)).getD 0
  have hf : Computable f := Computable.option_getD (hcomp.comp
    ((Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0)).to_comp)
    (Primrec.snd.comp Primrec.unpair).to_comp) (Computable.const 0)
  obtain ⟨c, hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp hf)
  let r := Encodable.encode c
  let i := Nat.pair r 0
  obtain ⟨hfin, hfull, ht⟩ := hgood i
  have hvalues (k : ℕ) : cutoff r k = 0 ∨ cutoff r k ∈ enumeratedSet emit i := by
    unfold cutoff
    simp only [r, Denumerable.ofNat_encode]
    cases he : Code.evaln (col k) c (Nat.pair r (row k)) with
    | none => exact Or.inl rfl
    | some a =>
      have ha := Code.evaln_sound (show a ∈ Code.evaln (col k) c (Nat.pair r (row k)) from he)
      rw [hc] at ha
      have heq : (emit i (row k)).getD 0 = a := by
        simpa [f, row, col, i, eq_comm] using ha
      cases hs : emit i (row k) with
      | none => exact Or.inl (by simpa [hs] using heq.symm)
      | some x => exact Or.inr ⟨row k, by simpa [hs] using heq⟩
  -- Every observed cutoff is either a word in the finite output or zero.
  have hbounded : BddAbove (Set.range (cutoff r)) := by
    apply (hfin.insert 0).bddAbove.mono
    rintro _ ⟨k, rfl⟩
    exact (Set.mem_insert_iff).mpr (hvalues k)
  obtain ⟨n, hn⟩ := Nat.sSup_mem (Set.range_nonempty (cutoff r)) hbounded
  have hmax (k) : cutoff r k ≤ cutoff r n :=
    hn ▸ le_csSup hbounded (Set.mem_range_self k)
  let j := Nat.pair r (n + 1)
  have hsub : language j ⊆ language i := by
    intro x hx
    rw [← word_rep x] at hx ⊢
    obtain ⟨hr, hd | hm⟩ := word_mem.mp hx
    · exact word_mem.mpr ⟨hr, Or.inl ⟨hd.1, Or.inl rfl⟩⟩
    · exact False.elim (Nat.not_lt_of_ge (hmax (col x)) (by simpa using hm.2.2))
  -- The maximum-cutoff competitor has no markers and contains every emitted word.
  have hcontains : enumeratedSet emit i ⊆ language j := by
    intro x hx
    obtain ⟨s, hs⟩ := hx
    have hv : x ∈ c.eval (Nat.pair r s) := by
      rw [hc]
      change x ∈ Part.some (f (Nat.pair r s))
      have : emit (Nat.pair r 0) s = some x := hs
      simp [f, row, col, this]
    obtain ⟨k, hk⟩ := Code.evaln_complete.mp hv
    have hout : cutoff r (Nat.pair s k) = x := by simp [cutoff, row, col, r, Option.mem_def.mp hk]
    have hle := (Nat.unpair_right_le x).trans (hout ▸ hmax (Nat.pair s k))
    have hh := hfull (show x ∈ enumeratedSet emit i from ⟨s, hs⟩)
    rw [← word_rep x] at hh ⊢
    obtain ⟨hr, hd | hm⟩ := word_mem.mp hh
    · exact word_mem.mpr ⟨hr, Or.inl ⟨hd.1, Or.inr hle⟩⟩
    · exact False.elim (hm.1 rfl)
  have hbad := ht j hcontains hsub (show word r 0 (cutoff r n + 1) ∈ language i by simp [i])
  simp [j, family] at hbad

end GenLimit.Angluin.NonuniformTellTales

namespace GenLimit.Angluin

/-- Angluin (1980), Theorem 2. -/
theorem theoremTwo : TheoremTwoStatement :=
  ⟨_, NonuniformTellTales.conditionTwo, fun h =>
    NonuniformTellTales.notConditionOne (effectiveInferrable_conditionOne h)⟩

end GenLimit.Angluin
