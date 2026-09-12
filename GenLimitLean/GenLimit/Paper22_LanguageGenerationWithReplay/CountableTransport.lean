import GenLimit.Paper22_LanguageGenerationWithReplay.WitnessProtectionMachine
import Mathlib.Logic.Denumerable

/-!
# Transporting Witness Protection to an arbitrary countable domain

The proof of Theorem 6.1 in Racca--Valko--Sanyal begins by identifying its
countable domain with `ℕ`.  This file makes that "without loss of generality"
step explicit.  A family over an arbitrary type is pushed forward along an
equivalence with `ℕ`; the checked natural-number Witness Protection generator
is then pulled back to the original domain.

The resulting theorem is semantic.  It proves the exact replay-enumeration
and eventual fresh-valid-output statement on every countable domain.  The
underlying natural-number machine is executable and has a finite-query trace
in `FiniteQueryTrace.lean`; the arbitrary `[Countable α]` wrapper still uses a
classically chosen equivalence and therefore makes no machine-computability
claim.
-/

namespace GenLimit
namespace Replay

open GenLimit.Generic

/-- An indexed infinite family over an arbitrary domain, equipped with the
same uniform Boolean membership oracle assumed by Theorem 6.1. -/
structure CountableDomainOracleFamily (α : Type*) where
  language : Generic.LanguageFamily α
  infinite' : ∀ i, (language i).Infinite
  query : ℕ → α → Bool
  query_spec : ∀ i x, query i x = true ↔ x ∈ language i

namespace CountableDomainOracleFamily

variable {α β : Type*}

/-- Push a language forward along a domain equivalence. -/
def mapLanguage (e : α ≃ β) (L : Generic.Language α) :
    Generic.Language β :=
  e '' L

/-- Push a stream forward pointwise along a domain equivalence. -/
def mapStream (e : α ≃ β) (stream : Generic.Stream α) :
    Generic.Stream β :=
  fun t => e (stream t)

/-- Pull a generator on the encoded domain back to the original domain. -/
def pullGenerator (e : α ≃ β) (gen : Generic.Generator β) :
    Generic.Generator α :=
  fun t history =>
    e.symm (gen t (fun k => e (history k)))

@[simp] theorem mapStream_apply
    (e : α ≃ β) (stream : Generic.Stream α) (t : ℕ) :
    mapStream e stream t = e (stream t) := rfl

@[simp] theorem output_pullGenerator
    (e : α ≃ β) (gen : Generic.Generator β)
    (stream : Generic.Stream α) (t : ℕ) :
    e (Generic.output (pullGenerator e gen) stream t) =
      Generic.output gen (mapStream e stream) t := by
  simp [Generic.output, pullGenerator, mapStream]

theorem mem_mapLanguage_iff
    (e : α ≃ β) (L : Generic.Language α) (x : α) :
    e x ∈ mapLanguage e L ↔ x ∈ L := by
  constructor
  · rintro ⟨y, hy, hey⟩
    have hyx : y = x := e.injective hey
    simpa [hyx] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem mem_sample_mapStream_iff
    (e : α ≃ β) (stream : Generic.Stream α) (t : ℕ) (x : α) :
    e x ∈ Generic.sample (mapStream e stream) t ↔
      x ∈ Generic.sample stream t := by
  simp only [Generic.mem_sample_iff]
  constructor
  · rintro ⟨s, hst, hs⟩
    refine ⟨s, hst, ?_⟩
    exact e.injective hs
  · rintro ⟨s, hst, rfl⟩
    exact ⟨s, hst, rfl⟩

/-- Replay legality is invariant under a bijective renaming of the domain. -/
theorem isReplaySequence_pullGenerator_iff
    (e : α ≃ β) (gen : Generic.Generator β)
    (L : Generic.Language α) (stream : Generic.Stream α) :
    IsReplaySequence (pullGenerator e gen) L stream ↔
      IsReplaySequence gen (mapLanguage e L) (mapStream e stream) := by
  constructor
  · intro hreplay n
    rcases hreplay n with htarget | ⟨k, hkpos, hkn, hkout⟩
    · exact Or.inl ⟨stream n, htarget, rfl⟩
    · refine Or.inr ⟨k, hkpos, hkn, ?_⟩
      rw [← output_pullGenerator e gen stream k, hkout]
      rfl
  · intro hreplay n
    rcases hreplay n with htarget | ⟨k, hkpos, hkn, hkout⟩
    · exact Or.inl ((mem_mapLanguage_iff e L (stream n)).mp htarget)
    · refine Or.inr ⟨k, hkpos, hkn, ?_⟩
      apply e.injective
      rw [output_pullGenerator]
      exact hkout

/-- Exact target coverage, including replay legality, is invariant under the
same bijective renaming. -/
theorem isReplayEnumeration_pullGenerator_iff
    (e : α ≃ β) (gen : Generic.Generator β)
    (L : Generic.Language α) (stream : Generic.Stream α) :
    IsReplayEnumeration (pullGenerator e gen) L stream ↔
      IsReplayEnumeration gen (mapLanguage e L) (mapStream e stream) := by
  constructor
  · rintro ⟨hreplay, hcover⟩
    refine ⟨(isReplaySequence_pullGenerator_iff e gen L stream).mp hreplay,
      ?_⟩
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := hcover x hx
    exact ⟨n, by simp [mapStream, hn]⟩
  · rintro ⟨hreplay, hcover⟩
    refine ⟨(isReplaySequence_pullGenerator_iff e gen L stream).mpr hreplay,
      ?_⟩
    intro x hx
    obtain ⟨n, hn⟩ := hcover (e x) ⟨x, hx, rfl⟩
    exact ⟨n, e.injective hn⟩

/-- Fresh target-valid output is invariant under a bijective domain
renaming. -/
theorem correctAt_pullGenerator_iff
    (e : α ≃ β) (gen : Generic.Generator β)
    (L : Generic.Language α) (stream : Generic.Stream α) (t : ℕ) :
    Generic.CorrectAt (pullGenerator e gen) L stream t ↔
      Generic.CorrectAt gen (mapLanguage e L) (mapStream e stream) t := by
  constructor
  · rintro ⟨htarget, hfresh⟩
    refine ⟨?_, ?_⟩
    · rw [← output_pullGenerator]
      exact (mem_mapLanguage_iff e L _).mpr htarget
    · intro hsample
      apply hfresh
      rw [← mem_sample_mapStream_iff e stream t]
      simpa only [output_pullGenerator] using hsample
  · rintro ⟨htarget, hfresh⟩
    refine ⟨?_, ?_⟩
    · apply (mem_mapLanguage_iff e L _).mp
      simpa only [output_pullGenerator] using htarget
    · intro hsample
      apply hfresh
      rw [← output_pullGenerator]
      exact (mem_sample_mapStream_iff e stream t _).mpr hsample

/-- Encode an arbitrary-domain oracle family as the natural-number family
consumed by the existing Witness Protection development. -/
def encode (F : CountableDomainOracleFamily α) (e : α ≃ ℕ) :
    GenLimit.OracleFamily where
  language i := mapLanguage e (F.language i)
  infinite' i := (F.infinite' i).image e.injective.injOn
  query i n := F.query i (e.symm n)
  query_spec i n := by
    rw [F.query_spec]
    constructor
    · intro hn
      exact ⟨e.symm n, hn, e.apply_symm_apply n⟩
    · rintro ⟨x, hx, hxn⟩
      have : x = e.symm n := by
        apply e.injective
        simpa using hxn
      simpa [this] using hx

/-- Witness Protection pulled back from the natural-number encoding. -/
def witnessProtectionGenerator
    (F : CountableDomainOracleFamily α) (e : α ≃ ℕ) :
    Generic.Generator α :=
  pullGenerator e ((F.encode e).witnessProtectionGenerator)

/-- The already checked Witness Protection correctness theorem transported
to an arbitrary domain through an explicit enumeration equivalence. -/
theorem witnessProtection_eventual_correctness
    (F : CountableDomainOracleFamily α) (e : α ≃ ℕ)
    {z : ℕ} {stream : Generic.Stream α}
    (henum :
      IsReplayEnumeration (F.witnessProtectionGenerator e)
        (F.language z) stream) :
    ∃ T, ∀ t, T ≤ t →
      Generic.CorrectAt (F.witnessProtectionGenerator e)
        (F.language z) stream t := by
  let O := F.encode e
  have hencoded :
      IsReplayEnumeration O.witnessProtectionGenerator
        (O.language z) (mapStream e stream) := by
    exact
      (isReplayEnumeration_pullGenerator_iff e
        O.witnessProtectionGenerator (F.language z) stream).mp henum
  obtain ⟨T, hT⟩ := O.witnessProtection_eventual_correctness hencoded
  refine ⟨T, ?_⟩
  intro t ht
  exact
    (correctAt_pullGenerator_iff e O.witnessProtectionGenerator
      (F.language z) stream t).mpr (hT t ht)

/-- Theorem 6.1's semantic conclusion on an arbitrary domain equipped with
an explicit bijective enumeration by `ℕ`. -/
theorem theorem_6_1_equiv
    (F : CountableDomainOracleFamily α) (e : α ≃ ℕ) :
    IsLimitReplayGenerator (F.witnessProtectionGenerator e)
      (Set.range F.language) := by
  intro L hL stream henum
  obtain ⟨z, rfl⟩ := hL
  exact F.witnessProtection_eventual_correctness e henum

/-- Every countable domain supporting an infinite target language is
noncomputably equivalent to `ℕ`.  The choice is used only for the semantic
transport layer. -/
noncomputable def countableEquivNat
    (F : CountableDomainOracleFamily α) [Countable α] : α ≃ ℕ := by
  letI : Infinite α :=
    Set.infinite_univ_iff.mp
      ((F.infinite' 0).mono (Set.subset_univ _))
  letI : Denumerable α :=
    Classical.choice (nonempty_denumerable α)
  exact Denumerable.eqv α

/-- Paper-shaped arbitrary-countable-domain semantic generator. -/
noncomputable def countableWitnessProtectionGenerator
    (F : CountableDomainOracleFamily α) [Countable α] :
    Generic.Generator α :=
  F.witnessProtectionGenerator (F.countableEquivNat)

/-- Theorem 6.1's semantic countable-domain boundary: every indexed infinite
family over an arbitrary countable domain has a replay-limit generator.  Its
natural-number finite-query realization is stated separately. -/
theorem theorem_6_1_countable
    (F : CountableDomainOracleFamily α) [Countable α] :
    IsLimitReplayGenerator F.countableWitnessProtectionGenerator
      (Set.range F.language) := by
  exact F.theorem_6_1_equiv F.countableEquivNat

/-- Existential form of the arbitrary-countable-domain semantic theorem. -/
theorem theorem_6_1_countable_paper
    (F : CountableDomainOracleFamily α) [Countable α] :
    ∃ gen : Generic.Generator α,
      IsLimitReplayGenerator gen (Set.range F.language) :=
  ⟨F.countableWitnessProtectionGenerator, F.theorem_6_1_countable⟩

end CountableDomainOracleFamily
end Replay
end GenLimit
