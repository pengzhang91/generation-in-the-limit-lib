import GenLimit.Paper18_SafeLanguageGeneration.DiffEmpty

/-!
# The printed Safe Generation Corollary 6.1 reduction

This module formalizes the exact pair constructed in the proof of Theorem 6.1
of Anastasopoulos--Ateniese--Kornaropoulos and used by the subsequent
Corollary 6.1 argument.  Its right language omits the first bounded-halting
witness, if one exists.  Membership is uniformly primitive recursive, both
languages are infinite, and their difference is empty exactly for a
nonhalting code and a singleton otherwise.

The final theorem exposes the source defect: Definition 2 sends *every finite
difference* to the same eventual-bottom branch.  Consequently the printed
empty-versus-singleton reduction has identical required asymptotic behavior
in its two cases and cannot decide halting.
-/

namespace GenLimit.SafeGeneration.DiffEmpty.PrintedReduction

open GenLimit.Generic Nat.Partrec

/-- The first fuel at which bounded evaluation witnesses halting. -/
def FirstBoundedHalt (c : Code) (n : ℕ) : Prop :=
  boundedHalts c n = true ∧
    ∀ k < n, boundedHalts c k ≠ true

/-- The right language from the printed proof: all natural numbers except
the possible first bounded-halting witness. -/
def printedRightLanguage (c : Code) : Set ℕ :=
  {n | ¬ FirstBoundedHalt c n}

/-- “First bounded halt” is uniformly primitive recursive in the program
code and candidate step. -/
theorem firstBoundedHalt_uniform_primrec :
    PrimrecPred (fun p : Code × ℕ =>
      FirstBoundedHalt p.1 p.2) := by
  have hcurrent :
      PrimrecPred (fun p : Code × ℕ =>
        boundedHalts p.1 p.2 = true) := by
    exact Primrec.eq.comp boundedHalts_uniform_primrec
      (Primrec.const true)
  have hnotEarlierPair :
      PrimrecPred (fun p : ℕ × Code =>
        boundedHalts p.2 p.1 ≠ true) := by
    have hswapped :
        Primrec (fun p : ℕ × Code =>
          boundedHalts p.2 p.1) :=
      boundedHalts_uniform_primrec.comp
        (Primrec.snd.pair Primrec.fst)
    have heq :
        PrimrecPred (fun p : ℕ × Code =>
          boundedHalts p.2 p.1 = true) := by
      exact Primrec.eq.comp hswapped (Primrec.const true)
    exact heq.not
  have hpairs :
      Primrec (fun p : Code × ℕ =>
        (List.range p.2).map fun k => (k, p.1)) := by
    exact Primrec.list_map
      (Primrec.list_range.comp Primrec.snd)
      (Primrec₂.pair.comp₂ Primrec₂.right
        (Primrec.fst.comp₂ Primrec₂.left))
  have hprior :
      PrimrecPred (fun p : Code × ℕ =>
        ∀ k < p.2, boundedHalts p.1 k ≠ true) := by
    exact
      (hnotEarlierPair.forall_mem_list.comp hpairs).of_eq (by
        intro p
        simp)
  exact (hcurrent.and hprior).of_eq (by
    intro p
    rfl)

/-- The source's right-language membership test is uniformly primitive
recursive, not merely pointwise decidable. -/
theorem printedRightLanguage_uniform_primrec :
    PrimrecPred (fun p : Code × ℕ =>
      p.2 ∈ printedRightLanguage p.1) :=
  firstBoundedHalt_uniform_primrec.not.of_eq (by
    intro p
    rfl)

theorem firstBoundedHalt_unique
    {c : Code} {m n : ℕ}
    (hm : FirstBoundedHalt c m)
    (hn : FirstBoundedHalt c n) :
    m = n := by
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · exact (hn.2 m hmn hm.1).elim
  · exact hmn
  · exact (hm.2 n hnm hn.1).elim

@[simp] theorem mem_printed_difference_iff
    {c : Code} {n : ℕ} :
    n ∈ leftLanguage \ printedRightLanguage c ↔
      FirstBoundedHalt c n := by
  simp [leftLanguage, printedRightLanguage]

/-- The printed reduction never leaves Definition 2's finite branch: its
difference has at most one element for every code. -/
theorem printed_difference_finite (c : Code) :
    (leftLanguage \ printedRightLanguage c).Finite := by
  apply Set.Subsingleton.finite
  intro m hm n hn
  exact firstBoundedHalt_unique
    (mem_printed_difference_iff.mp hm)
    (mem_printed_difference_iff.mp hn)

/-- Both inputs in the printed reduction satisfy its infinitude promise. -/
theorem printedRightLanguage_infinite (c : Code) :
    (printedRightLanguage c).Infinite := by
  apply Set.infinite_of_finite_compl
  have hfinite := printed_difference_finite c
  have heq :
      (printedRightLanguage c)ᶜ =
        leftLanguage \ printedRightLanguage c := by
    ext n
    simp [leftLanguage]
  rw [heq]
  exact hfinite

theorem exists_firstBoundedHalt_iff_dom (c : Code) :
    (∃ n, FirstBoundedHalt c n) ↔
      (Code.eval c 0).Dom := by
  constructor
  · rintro ⟨n, hn⟩
    exact (eval_dom_iff_exists_boundedHalts c).mpr ⟨n, hn.1⟩
  · intro hdom
    have hex :
        ∃ n, boundedHalts c n = true :=
      (eval_dom_iff_exists_boundedHalts c).mp hdom
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    intro k hk
    exact Nat.find_min hex hk

/-- Exact semantic content of the source's halting reduction. -/
theorem printed_difference_eq_empty_iff_not_dom (c : Code) :
    leftLanguage \ printedRightLanguage c = ∅ ↔
      ¬(Code.eval c 0).Dom := by
  rw [Set.eq_empty_iff_forall_notMem]
  constructor
  · intro hempty hdom
    obtain ⟨n, hn⟩ :=
      (exists_firstBoundedHalt_iff_dom c).mpr hdom
    exact hempty n (mem_printed_difference_iff.mpr hn)
  · intro hnot n hn
    apply hnot
    exact (exists_firstBoundedHalt_iff_dom c).mp
      ⟨n, mem_printed_difference_iff.mp hn⟩

/-- The printed pair itself gives a code-level noncomputability theorem. -/
theorem printed_diffEmpty_not_computable :
    ¬ComputablePred
      (fun c : Code =>
        leftLanguage \ printedRightLanguage c = ∅) := by
  intro hdec
  apply theorem_6_1_restricted
  exact hdec.of_eq fun c =>
    (printed_difference_eq_empty_iff_not_dom c).trans
      (diffEmptyInstance_iff_not_dom c).symm

/-- Under the literal Definition 2, every instance in the printed
Corollary 6.1 reduction has exactly the same required asymptotic mode:
eventual bottom. -/
theorem printed_corollary_6_1_reduction_collapses
    (G : SafeGenerator ℕ)
    (stream : Stream (Tagged ℕ))
    (c : Code) :
    SafelyGenerates G leftLanguage (printedRightLanguage c) stream ↔
      EventuallyBottom G stream :=
  safelyGenerates_iff_eventuallyBottom_of_finite
    G leftLanguage (printedRightLanguage c) stream
      (printed_difference_finite c)

end GenLimit.SafeGeneration.DiffEmpty.PrintedReduction
