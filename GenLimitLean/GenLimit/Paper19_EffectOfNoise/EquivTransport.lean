import GenLimit.Paper19_EffectOfNoise.RejectedScan
import GenLimit.Support.Renaming
import Mathlib.Data.Nat.Pairing

/-!
# Equivalence transport for quantified-noise generation

The semantic notions in `QuantifyingNoise.Definitions` are invariant under
bijective renaming of the example universe.  This file makes that invariance
explicit and then transports the tagged Theorem 2.17 witness to the paper's
literal universe `ℕ × ℕ`.
-/

namespace GenLimit.QuantifyingNoise

section EquivTransport

variable {α β : Type*}

/-- Rename a language along an equivalence of example universes. -/
abbrev renameLanguage (e : α ≃ β) (L : GenLimit.Generic.Language α) :
    GenLimit.Generic.Language β :=
  GenLimit.Support.renameLanguage e L

/-- Rename every language in a class along an equivalence. -/
abbrev renameClass (e : α ≃ β) (C : GenLimit.Generic.LanguageClass α) :
    GenLimit.Generic.LanguageClass β :=
  GenLimit.Support.renameLanguageClass e C

/-- Rename a stream pointwise. -/
abbrev renameStream (e : α ≃ β) (stream : GenLimit.Generic.Stream α) :
    GenLimit.Generic.Stream β :=
  GenLimit.Support.renameStream e stream

/-- Conjugate a generator by an equivalence of example universes. -/
abbrev renameGenerator (e : α ≃ β) (gen : GenLimit.Generic.Generator α) :
    GenLimit.Generic.Generator β :=
  GenLimit.Support.renameGenerator e gen

@[simp] theorem mem_renameLanguage_iff
    (e : α ≃ β) (L : GenLimit.Generic.Language α) (y : β) :
    y ∈ renameLanguage e L ↔ e.symm y ∈ L := by
  simpa using
    (GenLimit.Support.mem_renameLanguage_iff e L (e.symm y))

@[simp] theorem renameLanguage_symm
    (e : α ≃ β) (L : GenLimit.Generic.Language α) :
    renameLanguage e.symm (renameLanguage e L) = L :=
  GenLimit.Support.renameLanguage_symm e L

@[simp] theorem renameClass_symm
    (e : α ≃ β) (C : GenLimit.Generic.LanguageClass α) :
    renameClass e.symm (renameClass e C) = C :=
  GenLimit.Support.renameLanguageClass_symm e C

@[simp] theorem renameStream_symm
    (e : α ≃ β) (stream : GenLimit.Generic.Stream α) :
    renameStream e.symm (renameStream e stream) = stream :=
  GenLimit.Support.renameStream_symm e stream

theorem range_renameStream
    (e : α ≃ β) (stream : GenLimit.Generic.Stream α) :
    Set.range (renameStream e stream) =
      renameLanguage e (Set.range stream) :=
  GenLimit.Support.range_renameStream e stream

theorem missingAtMost_rename
    (e : α ≃ β) {S L : Set α} {i : ℕ}
    (h : MissingAtMost S L i) :
    MissingAtMost (renameLanguage e S) (renameLanguage e L) i := by
  classical
  obtain ⟨F, hF, hcard⟩ := h
  refine ⟨F.map e.toEmbedding, ?_, ?_⟩
  · rw [Finset.coe_map, hF]
    simpa [renameLanguage] using Set.image_diff e.injective S L
  · simpa using hcard

theorem enumerationWithNoiseAtMost_rename
    (e : α ≃ β)
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {i : ℕ}
    (h : EnumerationWithNoiseAtMost stream L i) :
    EnumerationWithNoiseAtMost
      (renameStream e stream) (renameLanguage e L) i := by
  refine ⟨e.injective.comp h.1, ?_, ?_⟩
  · rw [range_renameStream]
    exact Set.image_mono h.2.1
  · change MissingAtMost
      (Set.range (renameStream e stream)) (renameLanguage e L) i
    rw [range_renameStream]
    exact missingAtMost_rename e h.2.2

@[simp] theorem enumerationWithNoiseAtMost_rename_iff
    (e : α ≃ β)
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {i : ℕ} :
    EnumerationWithNoiseAtMost
        (renameStream e stream) (renameLanguage e L) i ↔
      EnumerationWithNoiseAtMost stream L i := by
  constructor
  · intro h
    have h' := enumerationWithNoiseAtMost_rename e.symm h
    simpa using h'
  · exact enumerationWithNoiseAtMost_rename e

theorem observed_rename
    (e : α ≃ β) (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    observed (renameStream e stream) t =
      (observed stream t).map e.toEmbedding := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨n, hn, hny⟩ :=
      GenLimit.Generic.mem_sample_iff.mp hy
    apply Finset.mem_map.mpr
    refine ⟨stream n, ?_, ?_⟩
    · exact GenLimit.Generic.mem_sample_iff.mpr ⟨n, hn, rfl⟩
    · exact hny
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
    obtain ⟨n, hn, hnx⟩ :=
      GenLimit.Generic.mem_sample_iff.mp hx
    apply GenLimit.Generic.mem_sample_iff.mpr
    refine ⟨n, hn, ?_⟩
    change e (stream n) = y
    rw [hnx]
    exact hxy

@[simp] theorem outputAt_rename
    (e : α ≃ β) (gen : GenLimit.Generic.Generator α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    outputAt (renameGenerator e gen) (renameStream e stream) t =
      e (outputAt gen stream t) := by
  change
    GenLimit.Generic.output
        (GenLimit.Support.renameGenerator e gen)
        (GenLimit.Support.renameStream e stream) (t + 1) =
      e (GenLimit.Generic.output gen stream (t + 1))
  exact GenLimit.Support.output_rename e gen stream (t + 1)

@[simp] theorem correctAt_rename_iff
    (e : α ≃ β) (gen : GenLimit.Generic.Generator α)
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    CorrectAt (renameGenerator e gen) (renameLanguage e L)
        (renameStream e stream) t ↔
      CorrectAt gen L stream t := by
  classical
  rw [CorrectAt, outputAt_rename, observed_rename]
  change
    (e (outputAt gen stream t) ∈ renameLanguage e L ∧
      e (outputAt gen stream t) ∉
        (observed stream t).map e.toEmbedding) ↔
      (outputAt gen stream t ∈ L ∧
        outputAt gen stream t ∉ observed stream t)
  simp

theorem isUniformGeneratorAtNoiseLevel_rename
    (e : α ≃ β) {gen : GenLimit.Generic.Generator α}
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (h : IsUniformGeneratorAtNoiseLevel gen C i) :
    IsUniformGeneratorAtNoiseLevel
      (renameGenerator e gen) (renameClass e C) i := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, ?_⟩
  rintro K ⟨L, hLC, rfl⟩ stream henum t ht
  let sourceStream := renameStream e.symm stream
  have hstream :
      renameStream e sourceStream = stream := by
    funext n
    simp [sourceStream, renameStream]
  have henumSource :
      EnumerationWithNoiseAtMost sourceStream L i := by
    have :=
      (enumerationWithNoiseAtMost_rename_iff e
        (stream := sourceStream) (L := L)).mp
        (by simpa [hstream] using henum)
    exact this
  have hcorrect := hT L hLC sourceStream henumSource t ht
  have :=
    (correctAt_rename_iff e gen L sourceStream t).mpr hcorrect
  simpa [hstream] using this

theorem isNonuniformGeneratorAtNoiseLevel_rename
    (e : α ≃ β) {gen : GenLimit.Generic.Generator α}
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (h : IsNonuniformGeneratorAtNoiseLevel gen C i) :
    IsNonuniformGeneratorAtNoiseLevel
      (renameGenerator e gen) (renameClass e C) i := by
  rintro K ⟨L, hLC, rfl⟩
  obtain ⟨T, hT⟩ := h L hLC
  refine ⟨T, ?_⟩
  intro stream henum t ht
  let sourceStream := renameStream e.symm stream
  have hstream :
      renameStream e sourceStream = stream := by
    funext n
    simp [sourceStream, renameStream]
  have henumSource :
      EnumerationWithNoiseAtMost sourceStream L i := by
    apply (enumerationWithNoiseAtMost_rename_iff e).mp
    simpa [hstream] using henum
  have hcorrect := hT sourceStream henumSource t ht
  have :=
    (correctAt_rename_iff e gen L sourceStream t).mpr hcorrect
  simpa [hstream] using this

theorem uniformGeneratableAtNoiseLevel_rename
    (e : α ≃ β)
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (h : UniformGeneratableAtNoiseLevel C i) :
    UniformGeneratableAtNoiseLevel (renameClass e C) i := by
  obtain ⟨gen, hgen⟩ := h
  exact ⟨renameGenerator e gen,
    isUniformGeneratorAtNoiseLevel_rename e hgen⟩

theorem nonuniformGeneratableAtNoiseLevel_rename
    (e : α ≃ β)
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (h : NonuniformGeneratableAtNoiseLevel C i) :
    NonuniformGeneratableAtNoiseLevel (renameClass e C) i := by
  obtain ⟨gen, hgen⟩ := h
  exact ⟨renameGenerator e gen,
    isNonuniformGeneratorAtNoiseLevel_rename e hgen⟩

theorem uniformGeneratableAtNoiseLevel_rename_iff
    (e : α ≃ β)
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ} :
    UniformGeneratableAtNoiseLevel (renameClass e C) i ↔
      UniformGeneratableAtNoiseLevel C i := by
  constructor
  · intro h
    have := uniformGeneratableAtNoiseLevel_rename e.symm h
    simpa using this
  · exact uniformGeneratableAtNoiseLevel_rename e

theorem nonuniformGeneratableAtNoiseLevel_rename_iff
    (e : α ≃ β)
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ} :
    NonuniformGeneratableAtNoiseLevel (renameClass e C) i ↔
      NonuniformGeneratableAtNoiseLevel C i := by
  constructor
  · intro h
    have := nonuniformGeneratableAtNoiseLevel_rename e.symm h
    simpa using this
  · exact nonuniformGeneratableAtNoiseLevel_rename e

end EquivTransport

/-! ## The paper's literal `ℕ × ℕ` column universe -/

abbrev PaperColumnPoint := ℕ × ℕ

/-- The equivalence that collapses the tagged column index to one natural. -/
def columnPointPairingEquiv : ColumnPoint ≃ PaperColumnPoint :=
  Equiv.prodCongr Nat.pairEquiv (Equiv.refl ℕ)

/-- One of the paper's literal columns `B_c = {(c,n) | n ∈ ℕ}`. -/
def paperColumn (c : ℕ) : Set PaperColumnPoint :=
  {x | x.1 = c}

/-- The paper's language `L_T`, a union of columns indexed by `T`. -/
def paperUnionOfColumns (T : Set ℕ) :
    GenLimit.Generic.Language PaperColumnPoint :=
  {x | x.1 ∈ T}

/-- The exact witness class printed in the proof of Theorem 2.17. -/
def paperColumnUnionClass :
    GenLimit.Generic.LanguageClass PaperColumnPoint :=
  {L | ∃ T : Set ℕ, T.Nonempty ∧ L = paperUnionOfColumns T}

theorem paperColumn_subset_unionOfColumns
    {T : Set ℕ} {c : ℕ} (hc : c ∈ T) :
    paperColumn c ⊆ paperUnionOfColumns T := by
  intro x hx
  change x.1 ∈ T
  rw [show x.1 = c by simpa [paperColumn] using hx]
  exact hc

theorem paperColumn_infinite (c : ℕ) :
    (paperColumn c).Infinite := by
  let row : ℕ → PaperColumnPoint := fun n => (c, n)
  have hrange : (Set.range row).Infinite := by
    apply Set.infinite_range_of_injective
    intro m n hmn
    exact congrArg Prod.snd hmn
  apply hrange.mono
  rintro _ ⟨n, rfl⟩
  simp [row, paperColumn]

theorem paperColumnUnionClass_infinite :
    AllLanguagesInfinite paperColumnUnionClass := by
  rintro L ⟨T, hT, rfl⟩
  obtain ⟨c, hc⟩ := hT
  exact (paperColumn_infinite c).mono
    (paperColumn_subset_unionOfColumns hc)

theorem rename_column
    (c : ColumnIndex) :
    renameLanguage columnPointPairingEquiv (column c) =
      paperColumn (Nat.pairEquiv c) := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    change x.1 = Nat.pairEquiv c
    have hfirst :=
      congrArg Prod.fst hxy
    simpa [columnPointPairingEquiv, column] using hfirst.symm.trans
      (congrArg Nat.pairEquiv hy)
  · intro hx
    refine ⟨(c, x.2), by simp [column], ?_⟩
    apply Prod.ext
    · simpa [paperColumn] using hx.symm
    · simp [columnPointPairingEquiv]

theorem rename_unionOfColumns
    (T : Set ColumnIndex) :
    renameLanguage columnPointPairingEquiv (unionOfColumns T) =
      paperUnionOfColumns (Nat.pairEquiv '' T) := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y.1, hy, ?_⟩
    simpa [columnPointPairingEquiv] using congrArg Prod.fst hxy
  · rintro ⟨c, hc, hcx⟩
    refine ⟨(c, x.2), hc, ?_⟩
    apply Prod.ext
    · simpa [columnPointPairingEquiv] using hcx
    · simp [columnPointPairingEquiv]

theorem rename_columnUnionClass :
    renameClass columnPointPairingEquiv columnUnionClass =
      paperColumnUnionClass := by
  ext L
  constructor
  · rintro ⟨K, ⟨T, hT, rfl⟩, rfl⟩
    refine ⟨Nat.pairEquiv '' T, hT.image Nat.pairEquiv, ?_⟩
    exact rename_unionOfColumns T
  · rintro ⟨T, hT, rfl⟩
    let S : Set ColumnIndex := Nat.pairEquiv.symm '' T
    have hS : S.Nonempty := hT.image Nat.pairEquiv.symm
    refine ⟨unionOfColumns S, ⟨S, hS, rfl⟩, ?_⟩
    have himage : Nat.pairEquiv '' S = T := by
      change Nat.pairEquiv '' (Nat.pairEquiv.symm '' T) = T
      rw [Set.image_image]
      change
        (fun a => Nat.pairEquiv (Nat.pairEquiv.symm a)) '' T = T
      have hfun :
          (fun a => Nat.pairEquiv (Nat.pairEquiv.symm a)) = id := by
        funext a
        exact Nat.pairEquiv.apply_symm_apply a
      rw [hfun, Set.image_id]
    exact (rename_unionOfColumns S).trans (by rw [himage])

/-- Theorem 2.17 on the paper's exact universe and exact column class. -/
theorem theorem_2_17_paper :
    UniformGeneratableAtNoiseLevel paperColumnUnionClass 0 ∧
      ¬NonuniformGeneratableAtNoiseLevel paperColumnUnionClass 1 := by
  rw [← rename_columnUnionClass]
  constructor
  · exact
      (uniformGeneratableAtNoiseLevel_rename_iff
        columnPointPairingEquiv).2 theorem_2_17.1
  · intro h
    exact theorem_2_17.2
      ((nonuniformGeneratableAtNoiseLevel_rename_iff
        columnPointPairingEquiv).1 h)

/-- Theorem 2.17 on the exact source universe, with the rejected iterations
of Algorithm 1 retained in the lower-bound path. -/
theorem theorem_2_17_paper_rejectedScan :
    UniformGeneratableAtNoiseLevel paperColumnUnionClass 0 ∧
      ¬NonuniformGeneratableAtNoiseLevel paperColumnUnionClass 1 := by
  rw [← rename_columnUnionClass]
  constructor
  · exact
      (uniformGeneratableAtNoiseLevel_rename_iff
        columnPointPairingEquiv).2 theorem_2_17_rejectedScan.1
  · intro h
    exact theorem_2_17_rejectedScan.2
      ((nonuniformGeneratableAtNoiseLevel_rename_iff
        columnPointPairingEquiv).1 h)

/-- The existential separation clause of Theorem 2.18, witnessed on the
paper's exact `ℕ × ℕ` universe. -/
theorem theorem_2_18_separation_clause_paper :
    UniformGeneratableAtNoiseLevel paperColumnUnionClass 0 ∧
      ¬UniformGeneratableAtNoiseLevel paperColumnUnionClass 1 := by
  refine ⟨theorem_2_17_paper.1, ?_⟩
  intro h
  exact theorem_2_17_paper.2
    (uniform_fixed_level_implies_nonuniform h)

/-- The existential separation clause of Theorem 2.19, witnessed on the
paper's exact `ℕ × ℕ` universe. -/
theorem theorem_2_19_separation_clause_paper :
    NonuniformGeneratableAtNoiseLevel paperColumnUnionClass 0 ∧
      ¬NonuniformGeneratableAtNoiseLevel paperColumnUnionClass 1 :=
  ⟨uniform_fixed_level_implies_nonuniform theorem_2_17_paper.1,
    theorem_2_17_paper.2⟩

end GenLimit.QuantifyingNoise
