import GenLimit.Core.OnlineGeneration
import GenLimit.Gold.Text.Finite
import GenLimit.Gold.Text.Superfinite
import GenLimit.KM
import Mathlib.Data.Set.Finite.Basic

/-!
# Gold identification and KM generation

This bridge keeps the two success criteria distinct:

* Gold identification stabilizes to one exact name of the target language.
* KM generation eventually outputs target elements fresh from the positive
  sample, without identifying a name.

The first theorem shows that identification is sufficient for generation on
an infinite indexed family. The explicit co-singleton family below supplies
a converse separation using Gold's finite-tell-tale obstruction.
-/

namespace GenLimit

namespace Gold

open Text

/-- Use the language currently conjectured by an identifier and select a
fresh element from it. -/
noncomputable def outputOfIdentifier
    (O : OracleFamily) (M : TextLearner ℕ)
    (stream : ℕ → ℕ) (t : ℕ) : ℕ :=
  KM.Semantic.fresh O stream t (M (textPrefix stream t))

/-- Gold identification of an infinite indexed family is sufficient for the
KM trace-level guarantee. -/
theorem identifier_implies_fresh_generation
    (O : OracleFamily) {M : TextLearner ℕ}
    (hM : IdentifiesFamily O.language M)
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (O.language z)) :
    FreshGeneratesInLimit stream (outputOfIdentifier O M stream)
      (O.language z) := by
  obtain ⟨n, hn, T, hT⟩ := hM z stream hP
  change O.language n = O.language z at hn
  refine ⟨T, ?_⟩
  intro t ht
  have hguess : M (textPrefix stream t) = n := hT t ht
  have hfresh :=
    KM.Semantic.fresh_spec O stream t (M (textPrefix stream t))
  constructor
  · simpa [outputOfIdentifier, hguess, hn] using hfresh.1
  · simpa [outputOfIdentifier] using hfresh.2

/-- An exactly presented finite language cannot support the KM requirement
of fresh valid outputs forever: its whole content eventually lies in the
observed sample. -/
theorem finite_target_not_fresh_generatable
    {stream output : ℕ → ℕ} {L : Language}
    (hP : Presents stream L) (hfin : L.Finite) :
    ¬ FreshGeneratesInLimit stream output L := by
  rintro ⟨Tg, hG⟩
  obtain ⟨Ts, hS⟩ := eventually_sample_eq_of_finite hP hfin
  let t := max Tg Ts
  have hgt : Tg ≤ t := Nat.le_max_left _ _
  have hst : Ts ≤ t := Nat.le_max_right _ _
  obtain ⟨houtL, houtFresh⟩ := hG t hgt
  apply houtFresh
  have hset : (↑(sample stream t) : Set ℕ) = L := hS t hst
  change output t ∈ (↑(sample stream t) : Set ℕ)
  rw [hset]
  exact houtL

end Gold

namespace GoldKMSeparation

open Gold.Text

/-- `0` names the universal language; `n + 1` names its co-singleton
obtained by deleting `n`. -/
def coSingletonLanguage : LanguageFamily
  | 0 => Set.univ
  | n + 1 => ({n} : Set ℕ)ᶜ

/-- Uniform Boolean membership test for `coSingletonLanguage`. -/
def coSingletonQuery : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, u => decide (u ≠ n)

theorem coSingletonQuery_spec (i u : ℕ) :
    coSingletonQuery i u = true ↔ u ∈ coSingletonLanguage i := by
  cases i with
  | zero => simp [coSingletonQuery, coSingletonLanguage]
  | succ n => simp [coSingletonQuery, coSingletonLanguage]

theorem coSingletonLanguage_infinite (i : ℕ) :
    (coSingletonLanguage i).Infinite := by
  cases i with
  | zero =>
      simpa [coSingletonLanguage] using (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
  | succ n =>
      simpa [coSingletonLanguage] using
        (Set.finite_singleton n).infinite_compl

/-- An explicit uniformly decidable indexed family of infinite languages. -/
def coSingletonOracle : OracleFamily where
  language := coSingletonLanguage
  infinite' := coSingletonLanguage_infinite
  query := coSingletonQuery
  query_spec := coSingletonQuery_spec

/-- The class underlying the indexed co-singleton family. -/
def coSingletonClass : Set Language :=
  Set.range coSingletonLanguage

/-- No semantic Gold learner identifies the co-singleton family from every
arbitrary positive text.  The universal member has no finite tell-tale:
every finite set is contained in a proper co-singleton sublanguage. -/
theorem coSingleton_not_semanticallyIdentifiable :
    ¬ Gold.Text.SemanticallyIdentifiable coSingletonClass := by
  intro hident
  have huniv_mem : (Set.univ : Language) ∈ coSingletonClass := by
    exact ⟨0, rfl⟩
  obtain ⟨D, hD⟩ :=
    Gold.Text.finite_tellTale_of_semanticallyIdentifiable
      hident huniv_mem
        (Set.infinite_univ : (Set.univ : Set ℕ).Infinite)
  obtain ⟨n, hn⟩ := D.finite_toSet.infinite_compl.nonempty
  have hnD : n ∉ D := by
    simpa using hn
  let K := coSingletonLanguage (n + 1)
  have hKmem : K ∈ coSingletonClass := ⟨n + 1, rfl⟩
  have hDK : (↑D : Language) ⊆ K := by
    intro u hu
    change u ≠ n
    intro hun
    subst u
    exact hnD hu
  have hKeq : K = (Set.univ : Language) :=
    hD.2 K hKmem hDK (fun _ _ => Set.mem_univ _)
  have hnK : n ∉ K := by
    simp [K, coSingletonLanguage]
  exact hnK (hKeq.symm ▸ Set.mem_univ n)

/-- Consequently the same class is not identifiable relative to any fixed
grammar naming relation. -/
theorem coSingleton_not_identifiableWith
    {Name : Type*} (N : Gold.Text.Naming Name) :
    ¬ Gold.Text.IdentifiableWith N coSingletonClass := by
  intro h
  exact coSingleton_not_semanticallyIdentifiable
    (Gold.Text.identifiableWith_implies_semanticallyIdentifiable h)

/-- In particular, no natural-index learner identifies the indexed
co-singleton family in Gold's `IdentifiesFamily` interface. -/
theorem coSingleton_not_identifiesFamily :
    ¬ ∃ M : Gold.Text.TextLearner ℕ,
      Gold.Text.IdentifiesFamily coSingletonLanguage M := by
  rintro ⟨M, hM⟩
  apply coSingleton_not_identifiableWith
    (Gold.Text.familyNaming coSingletonLanguage)
  refine ⟨M, ?_⟩
  intro L hL stream hP
  obtain ⟨z, rfl⟩ := hL
  exact hM z stream hP

/-- The existing finite-query KM machine generates from every member of the
co-singleton family on every exact presentation. -/
theorem coSingleton_km_generates
    {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (coSingletonOracle.language z)) :
    FreshGeneratesInLimit stream
      (coSingletonOracle.kmGenerator stream)
      (coSingletonOracle.language z) := by
  exact coSingletonOracle.kleinbergMullainathan_main hP

/-- Same-family separation: KM generates from every target and every exact
positive presentation, although Gold identification from arbitrary positive
text is impossible for the family. -/
theorem generation_without_identification :
    (¬ Gold.Text.SemanticallyIdentifiable coSingletonClass) ∧
      ∀ z stream,
        Presents stream (coSingletonOracle.language z) →
          FreshGeneratesInLimit stream
            (coSingletonOracle.kmGenerator stream)
            (coSingletonOracle.language z) := by
  exact ⟨coSingleton_not_semanticallyIdentifiable,
    fun _ _ hP => coSingleton_km_generates hP⟩

end GoldKMSeparation

end GenLimit
