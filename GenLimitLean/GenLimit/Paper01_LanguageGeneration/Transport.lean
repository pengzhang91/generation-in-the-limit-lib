import GenLimit.Paper01_LanguageGeneration.FiniteQuery.Main
import GenLimit.Paper01_LanguageGeneration.FiniteFamily
import GenLimit.Support.Renaming
import Mathlib.Logic.Denumerable

/-!
# #01 Language Generation: transport from a countable universe

The NeurIPS statement permits an arbitrary explicitly enumerable countably
infinite universe.  The finite-query machine is implemented over `ℕ`.  This
module transports that machine along an explicit equivalence `α ≃ ℕ`, then
packages the result for an arbitrary countable type.

The explicit-equivalence theorem preserves the finite-membership-query access
model: each encoded query is answered by decoding the queried natural and
calling the original family oracle.  The final countable wrapper chooses an
equivalence classically and therefore does not by itself assert an executable
encoding.
-/

namespace GenLimit.KM.Transport

/-- An indexed family of infinite languages over `α`, equipped with one
uniform Boolean membership oracle. -/
structure IndexedOracleFamily (α : Type*) where
  language : GenLimit.Generic.LanguageFamily α
  infinite' : ∀ i, (language i).Infinite
  query : ℕ → α → Bool
  query_spec : ∀ i x, query i x = true ↔ x ∈ language i

/-- Encode an arbitrary-universe oracle family as the `ℕ`-universe family used
by the NeurIPS finite-query machine. -/
def encodeFamily (e : α ≃ ℕ) (O : IndexedOracleFamily α) : GenLimit.OracleFamily where
  language i := GenLimit.Support.renameLanguage e (O.language i)
  infinite' i :=
    (O.infinite' i).image (Set.injOn_of_injective e.injective)
  query i n := O.query i (e.symm n)
  query_spec i n := by
    rw [O.query_spec]
    change e.symm n ∈ O.language i ↔
      n ∈ GenLimit.Support.renameLanguage e (O.language i)
    simpa using
      (GenLimit.Support.mem_renameLanguage_iff
        e (O.language i) (e.symm n)).symm

/-- Run the `ℕ`-universe NeurIPS generator after encoding the observations,
then decode its output back into the original universe. -/
def generatorOfEquiv
    (e : α ≃ ℕ) (O : IndexedOracleFamily α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : α :=
  e.symm
    ((encodeFamily e O).kmGenerator
      (GenLimit.Support.renameStream e stream) t)

/-- Eventual target membership and freshness for the transported generator. -/
def GeneratesInLimit
    (e : α ≃ ℕ) (O : IndexedOracleFamily α)
    (stream : GenLimit.Generic.Stream α) (z : ℕ) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    generatorOfEquiv e O stream t ∈ O.language z ∧
      generatorOfEquiv e O stream t ∉ GenLimit.Generic.sample stream t

@[simp] theorem mem_encoded_sample_iff
    (e : α ≃ ℕ) (stream : GenLimit.Generic.Stream α) (t : ℕ) (x : α) :
    e x ∈ GenLimit.sample (GenLimit.Support.renameStream e stream) t ↔
      x ∈ GenLimit.Generic.sample stream t := by
  rw [GenLimit.mem_sample_iff, GenLimit.Generic.mem_sample_iff]
  constructor
  · rintro ⟨s, hs, hstream⟩
    refine ⟨s, hs, ?_⟩
    apply e.injective
    simpa [GenLimit.Support.renameStream] using hstream
  · rintro ⟨s, hs, hstream⟩
    refine ⟨s, hs, ?_⟩
    simp [GenLimit.Support.renameStream, hstream]

/-- NeurIPS Theorem 2.1 transported along an explicit coding of the universe.

The transported generator uses only the supplied coding and the original
uniform membership oracle. -/
theorem kleinbergMullainathan_main_of_equiv
    (e : α ≃ ℕ) (O : IndexedOracleFamily α)
    {stream : GenLimit.Generic.Stream α} {z : ℕ}
    (hP : GenLimit.Generic.Presents stream (O.language z)) :
    GeneratesInLimit e O stream z := by
  have hPnat :
      GenLimit.Presents
        (GenLimit.Support.renameStream e stream)
        ((encodeFamily e O).language z) := by
    exact GenLimit.Support.presents_renameStream e hP
  obtain ⟨T, hT⟩ :=
    GenLimit.OracleFamily.kleinbergMullainathan_main
      (O := encodeFamily e O) hPnat
  refine ⟨T, ?_⟩
  intro t ht
  have hmain := hT t ht
  constructor
  · change
      e.symm
          ((encodeFamily e O).kmGenerator
            (GenLimit.Support.renameStream e stream) t) ∈
        O.language z
    have hrenamed :
        e
            (e.symm
              ((encodeFamily e O).kmGenerator
                (GenLimit.Support.renameStream e stream) t)) ∈
          GenLimit.Support.renameLanguage e (O.language z) := by
      simpa [encodeFamily] using hmain.1
    exact
      (GenLimit.Support.mem_renameLanguage_iff
        e (O.language z)
        (e.symm
          ((encodeFamily e O).kmGenerator
            (GenLimit.Support.renameStream e stream) t))).mp hrenamed
  · intro hseen
    apply hmain.2
    have hencoded :=
      (mem_encoded_sample_iff e stream t
        (generatorOfEquiv e O stream t)).2 hseen
    simpa [generatorOfEquiv] using hencoded

/-- A classically selected coding of a countable universe.  Infinitude of the
ambient type follows from any one infinite language in the indexed family. -/
noncomputable def countableEquivNat
    [Countable α] (O : IndexedOracleFamily α) : α ≃ ℕ := by
  letI : Infinite (O.language 0) := Set.Infinite.to_subtype (O.infinite' 0)
  letI : Infinite α :=
    Infinite.of_injective ((↑) : O.language 0 → α) Subtype.val_injective
  exact Classical.choice (inferInstance : Nonempty (α ≃ ℕ))

/-- NeurIPS Theorem 2.1 for an arbitrary countable universe.

This wrapper chooses the universe coding classically.  Use
`kleinbergMullainathan_main_of_equiv` when an explicit coding is part of the
algorithmic input. -/
theorem kleinbergMullainathan_main_countable
    [Countable α] (O : IndexedOracleFamily α)
    {stream : GenLimit.Generic.Stream α} {z : ℕ}
    (hP : GenLimit.Generic.Presents stream (O.language z)) :
    GeneratesInLimit (countableEquivNat O) O stream z :=
  kleinbergMullainathan_main_of_equiv (countableEquivNat O) O hP

namespace FiniteFamily

/-- Encode a finite sample along the supplied universe equivalence. -/
def encodeSample (e : α ≃ ℕ) (S : Finset α) : Finset ℕ :=
  S.map e.toEmbedding

@[simp] theorem mem_encodeSample
    (e : α ≃ ℕ) (S : Finset α) (x : α) :
    e x ∈ encodeSample e S ↔ x ∈ S := by
  simp [encodeSample]

@[simp] theorem card_encodeSample
    (e : α ≃ ℕ) (S : Finset α) :
    (encodeSample e S).card = S.card := by
  simp [encodeSample]

/-- Decode the finite-family scan over `ℕ` back into the original
explicitly enumerable universe. -/
def outputOfEquiv
    (e : α ≃ ℕ) (O : IndexedOracleFamily α)
    (members : Finset ℕ) (S : Finset α)
    (hInfinite :
      (KM.FiniteFamily.acceptedSet
        (encodeFamily e O) members (encodeSample e S)).Infinite) :
    ℕ → α :=
  fun k ↦
    e.symm
      (KM.FiniteFamily.enumerateAccepted
        (encodeFamily e O) members (encodeSample e S) hInfinite k)

/-- Generic-universe form of the output contract in result (2.2). -/
def ProducesFromSample
    (O : IndexedOracleFamily α) (S : Finset α) (z : ℕ)
    (output : ℕ → α) : Prop :=
  Function.Injective output ∧
    Set.range output ⊆ O.language z \ (↑S : Set α)

theorem outputOfEquiv_producesFromSample
    (e : α ≃ ℕ) (O : IndexedOracleFamily α)
    {members : Finset ℕ} {S : Finset α} {z : ℕ}
    (hz : z ∈ members) (hS : (↑S : Set α) ⊆ O.language z)
    (hInfinite :
      (KM.FiniteFamily.acceptedSet
        (encodeFamily e O) members (encodeSample e S)).Infinite) :
    ProducesFromSample O S z
      (outputOfEquiv e O members S hInfinite) := by
  have hSencoded :
      (↑(encodeSample e S) : Set ℕ) ⊆ (encodeFamily e O).language z := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hn
    change e x ∈ GenLimit.Support.renameLanguage e (O.language z)
    exact (GenLimit.Support.mem_renameLanguage_iff e (O.language z) x).2
      (hS hx)
  have hnat :=
    KM.FiniteFamily.enumerateAccepted_producesFromSample
      (encodeFamily e O) hz hSencoded hInfinite
  constructor
  · exact e.symm.injective.comp hnat.1
  · rintro x ⟨k, rfl⟩
    let n :=
      KM.FiniteFamily.enumerateAccepted
        (encodeFamily e O) members (encodeSample e S) hInfinite k
    have hn :
        n ∈ (encodeFamily e O).language z \ (↑(encodeSample e S) : Set ℕ) :=
      hnat.2 ⟨k, rfl⟩
    constructor
    · have hrenamed :
          e (e.symm n) ∈ GenLimit.Support.renameLanguage e (O.language z) := by
        simpa [encodeFamily, n] using hn.1
      exact
        (GenLimit.Support.mem_renameLanguage_iff
          e (O.language z) (e.symm n)).1 hrenamed
    · intro hxS
      apply hn.2
      change n ∈ encodeSample e S
      have := (mem_encodeSample e S (e.symm n)).2 hxS
      simpa using this

/-- NeurIPS result (2.2), transported along an explicit coding `α ≃ ℕ`.

The decoded scan uses only the supplied coding and the original family
membership oracle. -/
theorem theorem_2_2_of_equiv
    (e : α ≃ ℕ) (O : IndexedOracleFamily α)
    (members : Finset ℕ) :
    ∃ tC : ℕ, ∀ (S : Finset α), tC ≤ S.card →
      ∀ z ∈ members, (↑S : Set α) ⊆ O.language z →
        ∃ hInfinite :
            (KM.FiniteFamily.acceptedSet
              (encodeFamily e O) members (encodeSample e S)).Infinite,
          ProducesFromSample O S z
            (outputOfEquiv e O members S hInfinite) := by
  obtain ⟨tC, hmain⟩ :=
    KM.FiniteFamily.theorem_2_2 (encodeFamily e O) members
  refine ⟨tC, ?_⟩
  intro S hlarge z hz hS
  have hlargeEncoded : tC ≤ (encodeSample e S).card := by
    simpa using hlarge
  have hSencoded :
      (↑(encodeSample e S) : Set ℕ) ⊆ (encodeFamily e O).language z := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hn
    change e x ∈ GenLimit.Support.renameLanguage e (O.language z)
    exact (GenLimit.Support.mem_renameLanguage_iff e (O.language z) x).2
      (hS hx)
  obtain ⟨hInfinite, -⟩ :=
    hmain (encodeSample e S) hlargeEncoded z hz hSencoded
  exact
    ⟨hInfinite,
      outputOfEquiv_producesFromSample e O hz hS hInfinite⟩

/-- Abstract countable-universe wrapper for result (2.2).

As for Theorem 2.1, this convenience statement chooses the universe coding
classically.  The preceding explicit-equivalence theorem is the executable
relative-to-oracle interface. -/
theorem theorem_2_2_countable
    [Countable α] (O : IndexedOracleFamily α)
    (members : Finset ℕ) :
    ∃ tC : ℕ, ∀ (S : Finset α), tC ≤ S.card →
      ∀ z ∈ members, (↑S : Set α) ⊆ O.language z →
        ∃ hInfinite :
            (KM.FiniteFamily.acceptedSet
              (encodeFamily (countableEquivNat O) O) members
              (encodeSample (countableEquivNat O) S)).Infinite,
          ProducesFromSample O S z
            (outputOfEquiv
              (countableEquivNat O) O members S hInfinite) :=
  theorem_2_2_of_equiv (countableEquivNat O) O members

end FiniteFamily

end GenLimit.KM.Transport
