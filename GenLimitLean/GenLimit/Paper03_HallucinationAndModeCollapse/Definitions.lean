import GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.SymmDiff

/-!
# Hallucination versus mode collapse: online definitions

This directory formalizes the deterministic core of Kalavasis--Mehrotra--
Velegkas, *On the Limits of Language Generation: Trade-Offs Between
Hallucination and Mode Collapse*, arXiv:2411.09642v3.

The paper's statistical theorems quantify over probability distributions and
rates.  The declarations in this file instead pin the exact support-valued
objects used by the online reductions in Theorems 3.5, 3.7, and 3.9.  No
probabilistic theorem is asserted here.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic
open scoped symmDiff

/-- A support-valued generator together with the Boolean membership oracle
required by Definitions 5--6.  This is a semantic oracle interface: it records
total correctness of each membership answer, but does not claim that an
arbitrary Lean function is a Turing-computable program. -/
structure SupportGenerator where
  support : ∀ t : ℕ, (Fin t → ℕ) → Set ℕ
  query : ∀ t : ℕ, (Fin t → ℕ) → ℕ → Bool
  query_spec :
    ∀ t xs x, query t xs x = true ↔ x ∈ support t xs

/-- The support produced from the prefix strictly before time `t`. -/
def supportAt
    (G : SupportGenerator) (stream : Stream ℕ) (t : ℕ) : Set ℕ :=
  G.support t (fun i => stream i)

/-- The support completed by the observed positive sample.  This is the
quantity that equals the target under the paper's fresh-output convention. -/
def completedSupport
    (G : SupportGenerator) (stream : Stream ℕ) (t : ℕ) : Set ℕ :=
  supportAt G stream t ∪ ↑(Generic.sample stream t)

/-- Definition 7: support stabilization along every positive presentation. -/
def Stable
    (G : SupportGenerator) (C : Generic.LanguageFamily ℕ) : Prop :=
  ∀ z stream, Generic.Presents stream (C z) →
    ∃ T, ∀ s t, T ≤ s → T ≤ t →
      supportAt G stream s = supportAt G stream t

/-- Fresh-output breadth in the online convention stated immediately before
Theorem 3.5: the support is eventually exactly `K \ S_t`. -/
def FreshBreadthInLimit
    (G : SupportGenerator) (C : Generic.LanguageFamily ℕ) : Prop :=
  ∀ z stream, Generic.Presents stream (C z) →
    ∃ T, ∀ t, T ≤ t →
      supportAt G stream t = C z \ ↑(Generic.sample stream t)

/-- The repetition-allowing breadth convention used literally in the printed
proof of Theorem 3.5: the support is eventually the whole target. -/
def RepeatingBreadthInLimit
    (G : SupportGenerator) (C : Generic.LanguageFamily ℕ) : Prop :=
  ∀ z stream, Generic.Presents stream (C z) →
    ∃ T, ∀ t, T ≤ t → supportAt G stream t = C z

/-- The exact strict symmetric-difference comparison in Definition 8.
`Set.encard` is the extended natural cardinality, so it faithfully represents
both finite and countably infinite differences. -/
def UnambiguousAt
    (C : Generic.LanguageFamily ℕ) (z : ℕ) (S : Set ℕ) : Prop :=
  ∀ i, C i ≠ C z →
    (S ∆ C z).encard < (S ∆ C i).encard

/-- Definition 8 in the online model. -/
def UnambiguousInLimit
    (G : SupportGenerator) (C : Generic.LanguageFamily ℕ) : Prop :=
  ∀ z stream, Generic.Presents stream (C z) →
    ∃ T, ∀ t, T ≤ t → UnambiguousAt C z (supportAt G stream t)

/-- Definition 9 at one support: no hallucinations and only finitely many
omitted target points. -/
def ApproximateBreadthAt (S K : Set ℕ) : Prop :=
  S ⊆ K ∧ (K \ S).Finite

/-- Definition 9 in the online model. -/
def ApproximateBreadthInLimit
    (G : SupportGenerator) (C : Generic.LanguageFamily ℕ) : Prop :=
  ∀ z stream, Generic.Presents stream (C z) →
    ∃ T, ∀ t, T ≤ t →
      ApproximateBreadthAt (supportAt G stream t) (C z)

/-- The family contains two extensionally distinct languages.  This mild
hypothesis is automatic in the non-identifiable case and is used only to
extract finiteness from a strict extended-cardinality comparison. -/
def HasDistinctLanguages (C : Generic.LanguageFamily ℕ) : Prop :=
  ∃ i j, C i ≠ C j

/-- `z` is the first index denoting its target language. -/
def IsLeastTargetIndex (C : Generic.LanguageFamily ℕ) (z : ℕ) : Prop :=
  ∀ i, i < z → C i ≠ C z

/-- Paper-facing name for positive-data identifiability in the shared
semantic Angluin interface. -/
abbrev IdentifiableInLimit (C : Generic.LanguageFamily ℕ) : Prop :=
  GenLimit.Angluin.SemanticallyInferrable C

theorem completedSupport_of_freshBreadth
    {G : SupportGenerator} {C : Generic.LanguageFamily ℕ}
    {z : ℕ} {stream : Stream ℕ} {t : ℕ}
    (hP : Generic.Presents stream (C z))
    (h : supportAt G stream t = C z \ ↑(Generic.sample stream t)) :
    completedSupport G stream t = C z := by
  rw [completedSupport, h]
  apply Set.diff_union_of_subset
  intro x hx
  exact Generic.mem_language_of_mem_sample_of_presents hP hx

theorem completedSupport_of_repeatingBreadth
    {G : SupportGenerator} {C : Generic.LanguageFamily ℕ}
    {z : ℕ} {stream : Stream ℕ} {t : ℕ}
    (hP : Generic.Presents stream (C z))
    (h : supportAt G stream t = C z) :
    completedSupport G stream t = C z := by
  rw [completedSupport, h]
  exact Set.union_eq_left.mpr fun _ hx =>
    Generic.mem_language_of_mem_sample_of_presents hP hx

end GenLimit.HallucinationModeCollapse
