import GenLimit.Paper19_EffectOfNoise.Nonuniform
import GenLimit.Support.PrefixCompletion

/-!
# Quantifying Noise: the column separation

This file develops the explicit column family used in Li--Zhang Theorem
2.17 (arXiv:2601.21237v2).  The paper uses columns indexed by natural
numbers.  We use the canonically isomorphic countable index type
`ℕ × ℕ`: the first coordinate names one adversarial block and the second
coordinate is its position inside that block.  This makes the disjoint
blocks in the proof definitionally separate and removes irrelevant interval
arithmetic.

The first part below proves the full noiseless uniform upper bound and a
general ordered-prefix continuation theorem.  The subsequent declarations
formalize all three infinite branches of the paper's lower bound.  In the
last branch, the source's scan-and-insert Algorithm 1 is compressed to its
accepted updates: `algorithmNext` chooses the future successful iteration
whose existence is proved in the paper, and `algorithmSelection n` is the
state after `n` successful insertions.  Thus the theorem-level diagonal is
literal, while these declarations are an equivalent semantic compression
of the displayed for-loop rather than an executable transcription of every
rejected iteration.
-/

namespace GenLimit.QuantifyingNoise

/-! ## The class of nonempty unions of infinite columns -/

abbrev ColumnIndex := ℕ × ℕ
abbrev ColumnPoint := ColumnIndex × ℕ

/-- One infinite vertical column. -/
def column (c : ColumnIndex) : Set ColumnPoint :=
  {x | x.1 = c}

/-- The language obtained by taking all columns indexed by `T`. -/
def unionOfColumns (T : Set ColumnIndex) :
    GenLimit.Generic.Language ColumnPoint :=
  {x | x.1 ∈ T}

/-- The Theorem 2.17 class: every nonempty union of columns. -/
def columnUnionClass :
    GenLimit.Generic.LanguageClass ColumnPoint :=
  {L | ∃ T : Set ColumnIndex, T.Nonempty ∧ L = unionOfColumns T}

theorem column_subset_unionOfColumns
    {T : Set ColumnIndex} {c : ColumnIndex} (hc : c ∈ T) :
    column c ⊆ unionOfColumns T := by
  intro x hx
  change x.1 ∈ T
  rw [show x.1 = c by simpa [column] using hx]
  exact hc

theorem column_infinite (c : ColumnIndex) :
    (column c).Infinite := by
  let row : ℕ → ColumnPoint := fun n => (c, n)
  have hrange : (Set.range row).Infinite := by
    apply Set.infinite_range_of_injective
    intro m n hmn
    exact congrArg Prod.snd hmn
  apply hrange.mono
  rintro _ ⟨n, rfl⟩
  simp [row, column]

theorem unionOfColumns_infinite
    {T : Set ColumnIndex} (hT : T.Nonempty) :
    (unionOfColumns T).Infinite := by
  obtain ⟨c, hc⟩ := hT
  exact (column_infinite c).mono (column_subset_unionOfColumns hc)

theorem columnUnionClass_infinite :
    AllLanguagesInfinite columnUnionClass := by
  rintro L ⟨T, hT, rfl⟩
  exact unionOfColumns_infinite hT

theorem missingAtMost_zero_iff_subset
    (S L : Set α) :
    MissingAtMost S L 0 ↔ S ⊆ L := by
  constructor
  · rintro ⟨F, hF, hcard⟩ x hxS
    have hFempty : F = ∅ := Finset.card_eq_zero.mp (by omega)
    by_contra hxL
    have hxF : x ∈ (↑F : Set α) := by
      rw [hF]
      exact ⟨hxS, hxL⟩
    rw [hFempty] at hxF
    simp at hxF
  · intro hSL
    refine ⟨∅, ?_, by simp⟩
    ext x
    constructor
    · simp
    · rintro ⟨hxS, hxNotL⟩
      exact (hxNotL (hSL hxS)).elim

/-! ## A uniform noiseless generator -/

/-- Given a nonempty history, choose a fresh point in the column of the
first observed point. -/
noncomputable def firstColumnFreshGenerator :
    GenLimit.Generic.Generator ColumnPoint :=
  fun n xs => by
    classical
    if hn : 0 < n then
      let c := (xs ⟨0, hn⟩).1
      have hfresh :
          (column c \
            (GenLimit.Generic.sequenceSample xs : Set ColumnPoint)).Nonempty :=
        ((column_infinite c).diff
          (GenLimit.Generic.sequenceSample xs).finite_toSet).nonempty
      exact Classical.choose hfresh
    else
      exact ((0, 0), 0)

theorem firstColumnFreshGenerator_spec
    {n : ℕ} {xs : Fin n → ColumnPoint} (hn : 0 < n) :
    firstColumnFreshGenerator n xs ∈
      column ((xs ⟨0, hn⟩).1) \
        (GenLimit.Generic.sequenceSample xs : Set ColumnPoint) := by
  classical
  simp only [firstColumnFreshGenerator, dif_pos hn]
  exact Classical.choose_spec _

/-- The upper-bound half of Theorem 2.17: the column-union class is
uniformly generatable with no noise, from paper time zero. -/
theorem columnUnionClass_uniform_noiseless :
    UniformGeneratableAtNoiseLevel columnUnionClass 0 := by
  refine ⟨firstColumnFreshGenerator, 0, ?_⟩
  intro L hLC stream henum t _ht
  obtain ⟨T, hT, rfl⟩ := hLC
  have hrangeTarget : Set.range stream ⊆ unionOfColumns T :=
    (missingAtMost_zero_iff_subset _ _).mp henum.2.2
  have hfirstTarget : stream 0 ∈ unionOfColumns T :=
    hrangeTarget ⟨0, rfl⟩
  have hfirstColumn : (stream 0).1 ∈ T := by
    simpa [unionOfColumns] using hfirstTarget
  have hspec :=
    firstColumnFreshGenerator_spec
      (xs := fun k : Fin (t + 1) => stream k)
      (Nat.zero_lt_succ t)
  have hprefix :
      GenLimit.Generic.sequenceSample
          (fun k : Fin (t + 1) => stream k) =
        observed stream t := by
    exact (observed_eq_sequenceSample stream t).symm
  rw [CorrectAt, outputAt]
  constructor
  · have hcol :
        (firstColumnFreshGenerator (t + 1)
          (fun k : Fin (t + 1) => stream k)).1 =
            (stream 0).1 := by
      simpa [column] using hspec.1
    simpa [unionOfColumns, hcol] using hfirstColumn
  · rw [← hprefix]
    exact hspec.2

/-! ## Ordered continuations of a noisy finite prefix -/

/-- Every ordered injective finite prefix having at most `i` noisy values
extends, without reordering, to an injective infinite enumeration of the
target with noise level at most `i`. -/
theorem enumerationWithNoise_extending_ordered_prefix
    [Countable α]
    {n : ℕ} {xs : Fin n → α}
    (hxs : Function.Injective xs)
    {L : Set α} (hL : L.Infinite) {i : ℕ}
    (hnoise :
      MissingAtMost
        (GenLimit.Generic.sequenceSample xs : Set α) L i) :
    let hrest :
        (L \ (GenLimit.Generic.sequenceSample xs : Set α)).Infinite :=
      hL.diff (GenLimit.Generic.sequenceSample xs).finite_toSet
    EnumerationWithNoiseAtMost
      (GenLimit.Support.prefixThenTarget xs L hrest) L i := by
  classical
  let hrest :
      (L \ (GenLimit.Generic.sequenceSample xs : Set α)).Infinite :=
    hL.diff (GenLimit.Generic.sequenceSample xs).finite_toSet
  let stream :=
    GenLimit.Support.prefixThenTarget xs L hrest
  have hrange :
      Set.range stream =
        (GenLimit.Generic.sequenceSample xs : Set α) ∪ L :=
    GenLimit.Support.range_prefixThenTarget_eq_prefix_union xs L hrest
  refine
    ⟨GenLimit.Support.prefixThenTarget_injective
        hxs L hrest, ?_, ?_⟩
  · rw [hrange]
    exact Set.subset_union_right
  · change MissingAtMost (Set.range stream) L i
    obtain ⟨F, hF, hFcard⟩ := hnoise
    refine ⟨F, ?_, hFcard⟩
    rw [hrange]
    calc
      (↑F : Set α) =
          (GenLimit.Generic.sequenceSample xs : Set α) \ L := hF
      _ = ((GenLimit.Generic.sequenceSample xs : Set α) ∪ L) \ L := by
        ext x
        simp only [Set.mem_diff, Set.mem_union]
        aesop

/-! ## The growing disjoint adversarial blocks -/

/-- The `i`th block contains `i+1` column indices. -/
def adversarialBlock (i : ℕ) : Finset ColumnIndex :=
  (Finset.range (i + 1)).image fun k => (i, k)

theorem adversarialBlock_mem_iff
    {i : ℕ} {c : ColumnIndex} :
    c ∈ adversarialBlock i ↔ c.1 = i ∧ c.2 < i + 1 := by
  classical
  constructor
  · intro hc
    obtain ⟨k, hk, rfl⟩ :=
      Finset.mem_image.mp (show c ∈ adversarialBlock i from hc)
    simpa using hk
  · rintro ⟨hfirst, hsecond⟩
    rcases c with ⟨a, b⟩
    simp only at hfirst hsecond
    subst a
    exact Finset.mem_image.mpr
      ⟨b, Finset.mem_range.mpr hsecond, rfl⟩

theorem adversarialBlock_disjoint
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint (adversarialBlock i) (adversarialBlock j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro c hci hcj
  have hi := (adversarialBlock_mem_iff.mp hci).1
  have hj := (adversarialBlock_mem_iff.mp hcj).1
  exact hij (hi.symm.trans hj)

theorem adversarialBlock_card (i : ℕ) :
    (adversarialBlock i).card = i + 1 := by
  classical
  rw [adversarialBlock, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    exact congrArg Prod.snd hab

/-- The ordered prefix containing row zero from every column of block `i`. -/
def adversarialPrefix (i : ℕ) : Fin (i + 1) → ColumnPoint :=
  fun k => ((i, k), 0)

theorem adversarialPrefix_injective (i : ℕ) :
    Function.Injective (adversarialPrefix i) := by
  intro a b hab
  have hsnd :
      (a : ℕ) = (b : ℕ) :=
    congrArg (fun x : ColumnPoint => x.1.2) hab
  exact Fin.ext hsnd

theorem adversarialPrefix_column_mem
    (i : ℕ) (k : Fin (i + 1)) :
    (adversarialPrefix i k).1 ∈ adversarialBlock i := by
  apply adversarialBlock_mem_iff.mpr
  exact ⟨rfl, k.isLt⟩

/-- The output and its column on the `i`th adversarial prefix. -/
def adversarialOutput
    (gen : GenLimit.Generic.Generator ColumnPoint) (i : ℕ) :
    ColumnPoint :=
  gen (i + 1) (adversarialPrefix i)

def adversarialOutputColumn
    (gen : GenLimit.Generic.Generator ColumnPoint) (i : ℕ) :
    ColumnIndex :=
  (adversarialOutput gen i).1

/-- Indices on which the generator outputs inside the currently presented
block. -/
def insideBlockIndices
    (gen : GenLimit.Generic.Generator ColumnPoint) : Set ℕ :=
  {i | adversarialOutputColumn gen i ∈ adversarialBlock i}

/-- In the first lower-bound branch, retain every column of each selected
block except the generator's own output column. -/
def insideBranchColumns
    (gen : GenLimit.Generic.Generator ColumnPoint) : Set ColumnIndex :=
  {c | ∃ i, i ∈ insideBlockIndices gen ∧
    c ∈ adversarialBlock i ∧
    c ≠ adversarialOutputColumn gen i}

theorem insideBranchColumns_nonempty
    {gen : GenLimit.Generic.Generator ColumnPoint}
    (hinside : (insideBlockIndices gen).Infinite) :
    (insideBranchColumns gen).Nonempty := by
  obtain ⟨i, hiInside, hiNotZero⟩ :=
    hinside.exists_notMem_finset {0}
  have hiPos : 0 < i := by
    have : i ≠ 0 := by simpa using hiNotZero
    omega
  let c0 : ColumnIndex := (i, 0)
  let c1 : ColumnIndex := (i, 1)
  have hc0 : c0 ∈ adversarialBlock i := by
    apply adversarialBlock_mem_iff.mpr
    exact ⟨by simp [c0], by simp [c0]⟩
  have hc1 : c1 ∈ adversarialBlock i := by
    apply adversarialBlock_mem_iff.mpr
    exact ⟨by simp [c1], by simp [c1]; exact hiPos⟩
  by_cases hout : adversarialOutputColumn gen i = c0
  · refine ⟨c1, i, hiInside, hc1, ?_⟩
    intro heq
    have : c0 = c1 := hout.symm.trans heq.symm
    exact Nat.zero_ne_one (congrArg Prod.snd this)
  · exact ⟨c0, i, hiInside, hc0, fun h => hout h.symm⟩

theorem adversarialOutputColumn_not_insideBranch
    {gen : GenLimit.Generic.Generator ColumnPoint} {i : ℕ}
    (hi : i ∈ insideBlockIndices gen) :
    adversarialOutputColumn gen i ∉ insideBranchColumns gen := by
  intro hout
  obtain ⟨j, hjInside, hjBlock, hjNe⟩ := hout
  have hiBlock :
      adversarialOutputColumn gen i ∈ adversarialBlock i := hi
  by_cases hij : i = j
  · subst j
    exact hjNe rfl
  · exact
      Finset.disjoint_left.mp (adversarialBlock_disjoint hij)
        hiBlock hjBlock

theorem adversarialPrefix_missingAtMost_one_insideBranch
    {gen : GenLimit.Generic.Generator ColumnPoint} {i : ℕ}
    (hi : i ∈ insideBlockIndices gen) :
    MissingAtMost
      (↑(GenLimit.Generic.sequenceSample (adversarialPrefix i)) :
        Set ColumnPoint)
      (unionOfColumns (insideBranchColumns gen)) 1 := by
  classical
  let noisyPoint : ColumnPoint :=
    (adversarialOutputColumn gen i, 0)
  refine ⟨{noisyPoint}, ?_, by simp⟩
  ext x
  constructor
  · intro hx
    have hxEq : x = noisyPoint := by
      simpa using hx
    subst x
    constructor
    · have hiBlock :
          adversarialOutputColumn gen i ∈ adversarialBlock i := hi
      obtain ⟨k, hk, hcol⟩ :=
        Finset.mem_image.mp
          (show adversarialOutputColumn gen i ∈
            adversarialBlock i from hiBlock)
      apply GenLimit.Generic.mem_sequenceSample_iff.mpr
      refine ⟨⟨k, by simpa using hk⟩, ?_⟩
      simp [adversarialPrefix, noisyPoint, ← hcol]
    · simpa [unionOfColumns, noisyPoint] using
        adversarialOutputColumn_not_insideBranch hi
  · intro hx
    have hxSample := hx.1
    obtain ⟨k, hk⟩ :=
      GenLimit.Generic.mem_sequenceSample_iff.mp hxSample
    have hxEq : x = adversarialPrefix i k := hk.symm
    have hxBlock :
        x.1 ∈ adversarialBlock i := by
      rw [hxEq]
      exact adversarialPrefix_column_mem i k
    have hxNotColumns :
        x.1 ∉ insideBranchColumns gen := by
      simpa [unionOfColumns] using hx.2
    have hxColumn :
        x.1 = adversarialOutputColumn gen i := by
      by_contra hne
      exact hxNotColumns ⟨i, hi, hxBlock, hne⟩
    rw [Finset.mem_coe, Finset.mem_singleton]
    apply Prod.ext
    · exact hxColumn
    · rw [hxEq]
      rfl

/-- The complete first infinite branch of the Theorem 2.17 lower bound. -/
theorem infinite_inside_blocks_defeats_nonuniform
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (hinside : (insideBlockIndices gen).Infinite) :
    ¬IsNonuniformGeneratorAtNoiseLevel gen columnUnionClass 1 := by
  intro hgen
  let columns := insideBranchColumns gen
  let L := unionOfColumns columns
  have hcolumns : columns.Nonempty :=
    insideBranchColumns_nonempty hinside
  have hLC : L ∈ columnUnionClass :=
    ⟨columns, hcolumns, rfl⟩
  obtain ⟨T, hT⟩ := hgen L hLC
  obtain ⟨i, hiInside, hiLarge⟩ :=
    hinside.exists_notMem_finset (Finset.range T)
  have hTi : T ≤ i := by
    have : ¬i < T := by simpa using hiLarge
    omega
  let xs := adversarialPrefix i
  have hLInfinite : L.Infinite :=
    unionOfColumns_infinite hcolumns
  let hrest :
      (L \ (GenLimit.Generic.sequenceSample xs : Set ColumnPoint)).Infinite :=
    hLInfinite.diff (GenLimit.Generic.sequenceSample xs).finite_toSet
  let stream :=
    GenLimit.Support.prefixThenTarget xs L hrest
  have henum :
      EnumerationWithNoiseAtMost stream L 1 := by
    exact
      enumerationWithNoise_extending_ordered_prefix
        (adversarialPrefix_injective i) hLInfinite
        (adversarialPrefix_missingAtMost_one_insideBranch hiInside)
  have hcorrect := hT stream henum i hTi
  have hprefix :
      (fun k : Fin (i + 1) => stream k) =
        adversarialPrefix i := by
    funext k
    exact
      GenLimit.Support.prefixThenTarget_prefix
        xs L hrest k
  have hout :
      outputAt gen stream i = adversarialOutput gen i := by
    unfold outputAt adversarialOutput
    rw [hprefix]
  have houtNotL : adversarialOutput gen i ∉ L := by
    simpa [L, columns, unionOfColumns, adversarialOutputColumn] using
      adversarialOutputColumn_not_insideBranch hiInside
  exact houtNotL (hout ▸ hcorrect.1)

/-! ## The outside-block branches -/

/-- Indices on which the output column is outside the presented block. -/
def outsideBlockIndices
    (gen : GenLimit.Generic.Generator ColumnPoint) : Set ℕ :=
  (insideBlockIndices gen)ᶜ

theorem mem_outsideBlockIndices_iff
    {gen : GenLimit.Generic.Generator ColumnPoint} {i : ℕ} :
    i ∈ outsideBlockIndices gen ↔
      adversarialOutputColumn gen i ∉ adversarialBlock i := by
  rfl

/-- A generic lower-bound wrapper for the two remaining branches: infinitely
many full blocks lie in one target column set, while the corresponding
outputs lie outside that set. -/
theorem infinite_full_blocks_defeat_nonuniform
    (gen : GenLimit.Generic.Generator ColumnPoint)
    {I : Set ℕ} (hI : I.Infinite)
    {targetColumns : Set ColumnIndex}
    (hcolumns : targetColumns.Nonempty)
    (hblocks :
      ∀ i, i ∈ I → (↑(adversarialBlock i) : Set ColumnIndex) ⊆
        targetColumns)
    (houtputs :
      ∀ i, i ∈ I → adversarialOutputColumn gen i ∉ targetColumns) :
    ¬IsNonuniformGeneratorAtNoiseLevel gen columnUnionClass 1 := by
  intro hgen
  let L := unionOfColumns targetColumns
  have hLC : L ∈ columnUnionClass :=
    ⟨targetColumns, hcolumns, rfl⟩
  obtain ⟨T, hT⟩ := hgen L hLC
  obtain ⟨i, hiI, hiLarge⟩ :=
    hI.exists_notMem_finset (Finset.range T)
  have hTi : T ≤ i := by
    have : ¬i < T := by simpa using hiLarge
    omega
  let xs := adversarialPrefix i
  have hLInfinite : L.Infinite :=
    unionOfColumns_infinite hcolumns
  have hprefixInTarget :
      (GenLimit.Generic.sequenceSample xs : Set ColumnPoint) ⊆ L := by
    intro x hx
    obtain ⟨k, hk⟩ :=
      GenLimit.Generic.mem_sequenceSample_iff.mp hx
    have hcolBlock :
        x.1 ∈ adversarialBlock i := by
      rw [← hk]
      exact adversarialPrefix_column_mem i k
    have hcolTarget : x.1 ∈ targetColumns :=
      hblocks i hiI hcolBlock
    simpa [L, unionOfColumns] using hcolTarget
  have hnoise :
      MissingAtMost
        (GenLimit.Generic.sequenceSample xs : Set ColumnPoint) L 0 :=
    (missingAtMost_zero_iff_subset _ _).mpr hprefixInTarget
  let hrest :
      (L \ (GenLimit.Generic.sequenceSample xs : Set ColumnPoint)).Infinite :=
    hLInfinite.diff (GenLimit.Generic.sequenceSample xs).finite_toSet
  let stream :=
    GenLimit.Support.prefixThenTarget xs L hrest
  have henumZero :
      EnumerationWithNoiseAtMost stream L 0 := by
    exact
      enumerationWithNoise_extending_ordered_prefix
        (adversarialPrefix_injective i) hLInfinite hnoise
  have henumOne :
      EnumerationWithNoiseAtMost stream L 1 :=
    enumerationWithNoiseAtMost_mono (by omega) henumZero
  have hcorrect := hT stream henumOne i hTi
  have hprefix :
      (fun k : Fin (i + 1) => stream k) =
        adversarialPrefix i := by
    funext k
    exact
      GenLimit.Support.prefixThenTarget_prefix
        xs L hrest k
  have hout :
      outputAt gen stream i = adversarialOutput gen i := by
    unfold outputAt adversarialOutput
    rw [hprefix]
  have houtNotL : adversarialOutput gen i ∉ L := by
    simpa [L, unionOfColumns, adversarialOutputColumn] using
      houtputs i hiI
  exact houtNotL (hout ▸ hcorrect.1)

/-- Outside-block indices whose output lands in a fixed block `j`. -/
def indicesHittingBlock
    (gen : GenLimit.Generic.Generator ColumnPoint) (j : ℕ) : Set ℕ :=
  {i | i ∈ outsideBlockIndices gen ∧
    adversarialOutputColumn gen i ∈ adversarialBlock j}

/-- The target columns in the repeated-hit branch: take every full block
whose output lands in the fixed block `j`. -/
def repeatedHitBranchColumns
    (gen : GenLimit.Generic.Generator ColumnPoint) (j : ℕ) :
    Set ColumnIndex :=
  {c | ∃ i, i ∈ indicesHittingBlock gen j ∧
    c ∈ adversarialBlock i}

theorem repeatedHitBranchColumns_nonempty
    {gen : GenLimit.Generic.Generator ColumnPoint} {j : ℕ}
    (hhits : (indicesHittingBlock gen j).Infinite) :
    (repeatedHitBranchColumns gen j).Nonempty := by
  obtain ⟨i, hi⟩ := hhits.nonempty
  refine ⟨(i, 0), i, hi, ?_⟩
  apply adversarialBlock_mem_iff.mpr
  exact ⟨rfl, by omega⟩

theorem repeatedHit_output_not_target
    {gen : GenLimit.Generic.Generator ColumnPoint} {j i : ℕ}
    (hi : i ∈ indicesHittingBlock gen j) :
    adversarialOutputColumn gen i ∉ repeatedHitBranchColumns gen j := by
  intro hout
  obtain ⟨k, hkHit, hkBlock⟩ := hout
  have hiJ :
      adversarialOutputColumn gen i ∈ adversarialBlock j := hi.2
  have hjk : j = k := by
    by_contra hne
    exact
      Finset.disjoint_left.mp (adversarialBlock_disjoint hne)
        hiJ hkBlock
  subst k
  have hjOutside :
      adversarialOutputColumn gen j ∉ adversarialBlock j :=
    (mem_outsideBlockIndices_iff.mp hkHit.1)
  exact hjOutside hkHit.2

/-- The second branch in the paper's lower bound: one fixed block receives
outputs from infinitely many outside-block prefixes. -/
theorem infinite_hits_to_one_block_defeats_nonuniform
    (gen : GenLimit.Generic.Generator ColumnPoint) {j : ℕ}
    (hhits : (indicesHittingBlock gen j).Infinite) :
    ¬IsNonuniformGeneratorAtNoiseLevel gen columnUnionClass 1 := by
  apply infinite_full_blocks_defeat_nonuniform
    gen hhits
    (repeatedHitBranchColumns_nonempty hhits)
  · intro i hi c hc
    exact ⟨i, hi, hc⟩
  · exact fun i hi => repeatedHit_output_not_target hi

/-! ## Algorithm 1's accepted-update compression -/

/-- The finite set excluded before one accepted update of Algorithm 1.

* `chosen` prevents repetitions;
* the image of output first coordinates prevents an old output from lying
  in the new block; and
* the finite incoming sets prevent the new output from lying in an old
  block.
-/
noncomputable def algorithmForbidden
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    (chosen : Finset ℕ) : Finset ℕ := by
  classical
  exact
    chosen ∪
      chosen.image (fun i => (adversarialOutputColumn gen i).1) ∪
      chosen.biUnion (fun j => (hhits j).toFinset)

theorem chosen_subset_algorithmForbidden
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    (chosen : Finset ℕ) :
    chosen ⊆ algorithmForbidden gen hhits chosen := by
  intro i hi
  simp [algorithmForbidden, hi]

theorem outputFirst_mem_algorithmForbidden
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    {chosen : Finset ℕ} {i : ℕ} (hi : i ∈ chosen) :
    (adversarialOutputColumn gen i).1 ∈
      algorithmForbidden gen hhits chosen := by
  classical
  simp only [algorithmForbidden, Finset.mem_union,
    Finset.mem_image, Finset.mem_biUnion]
  exact Or.inl (Or.inr ⟨i, hi, rfl⟩)

theorem hit_mem_algorithmForbidden
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    {chosen : Finset ℕ} {i j : ℕ}
    (hj : j ∈ chosen) (hi : i ∈ indicesHittingBlock gen j) :
    i ∈ algorithmForbidden gen hhits chosen := by
  classical
  simp only [algorithmForbidden, Finset.mem_union,
    Finset.mem_image, Finset.mem_biUnion]
  exact Or.inr ⟨j, hj, (hhits j).mem_toFinset.mpr hi⟩

/-- A future successful index selected in the proof of Algorithm 1. -/
noncomputable def algorithmNext
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    (chosen : Finset ℕ) : ℕ :=
  Classical.choose
    (houtside.exists_notMem_finset
      (algorithmForbidden gen hhits chosen))

theorem algorithmNext_mem_outside
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    (chosen : Finset ℕ) :
    algorithmNext gen houtside hhits chosen ∈ outsideBlockIndices gen :=
  (Classical.choose_spec
    (houtside.exists_notMem_finset
      (algorithmForbidden gen hhits chosen))).1

theorem algorithmNext_not_forbidden
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    (chosen : Finset ℕ) :
    algorithmNext gen houtside hhits chosen ∉
      algorithmForbidden gen hhits chosen :=
  (Classical.choose_spec
    (houtside.exists_notMem_finset
      (algorithmForbidden gen hhits chosen))).2

/-- The finite state after `n` successful insertions.  Rejected source-loop
iterations are omitted. -/
noncomputable def algorithmSelection
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 =>
      insert
        (algorithmNext gen houtside hhits
          (algorithmSelection gen houtside hhits n))
        (algorithmSelection gen houtside hhits n)

theorem algorithmSelection_subset_succ
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    (n : ℕ) :
    algorithmSelection gen houtside hhits n ⊆
      algorithmSelection gen houtside hhits (n + 1) := by
  intro i hi
  simp [algorithmSelection, hi]

theorem algorithmSelection_mono
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    Monotone (algorithmSelection gen houtside hhits) :=
  monotone_nat_of_le_succ
    (algorithmSelection_subset_succ gen houtside hhits)

theorem algorithmNext_not_mem_selection
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    (n : ℕ) :
    algorithmNext gen houtside hhits
        (algorithmSelection gen houtside hhits n) ∉
      algorithmSelection gen houtside hhits n := by
  intro hmem
  exact
    algorithmNext_not_forbidden gen houtside hhits _
      (chosen_subset_algorithmForbidden gen hhits _ hmem)

theorem algorithmSelection_card
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    ∀ n, (algorithmSelection gen houtside hhits n).card = n := by
  intro n
  induction n with
  | zero => simp [algorithmSelection]
  | succ n ih =>
      rw [algorithmSelection, Finset.card_insert_of_notMem
        (algorithmNext_not_mem_selection gen houtside hhits n), ih]

theorem algorithmSelection_mem_outside
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    ∀ n i, i ∈ algorithmSelection gen houtside hhits n →
      i ∈ outsideBlockIndices gen := by
  intro n
  induction n with
  | zero =>
      intro i hi
      simp [algorithmSelection] at hi
  | succ n ih =>
      intro i hi
      rw [algorithmSelection] at hi
      rcases Finset.mem_insert.mp hi with hiNew | hiOld
      · subst i
        exact algorithmNext_mem_outside gen houtside hhits _
      · exact ih i hiOld

/-- The state invariant maintained across accepted updates. -/
def SelectionConflictFree
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (chosen : Finset ℕ) : Prop :=
  ∀ i, i ∈ chosen → ∀ j, j ∈ chosen →
    adversarialOutputColumn gen i ∉ adversarialBlock j

theorem algorithmSelection_conflictFree
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    ∀ n,
      SelectionConflictFree gen
        (algorithmSelection gen houtside hhits n) := by
  intro n
  induction n with
  | zero =>
      intro i hi
      simp [algorithmSelection] at hi
  | succ n ih =>
      let chosen := algorithmSelection gen houtside hhits n
      let q := algorithmNext gen houtside hhits chosen
      have hqOutside : q ∈ outsideBlockIndices gen :=
        algorithmNext_mem_outside gen houtside hhits chosen
      have hqNot :
          q ∉ algorithmForbidden gen hhits chosen :=
        algorithmNext_not_forbidden gen houtside hhits chosen
      intro i hi j hj
      change i ∈ insert q chosen at hi
      change j ∈ insert q chosen at hj
      rcases Finset.mem_insert.mp hi with rfl | hiOld
      · rcases Finset.mem_insert.mp hj with rfl | hjOld
        · exact (mem_outsideBlockIndices_iff.mp hqOutside)
        · intro hbad
          apply hqNot
          apply hit_mem_algorithmForbidden gen hhits hjOld
          exact ⟨hqOutside, hbad⟩
      · rcases Finset.mem_insert.mp hj with rfl | hjOld
        · intro hbad
          apply hqNot
          have hfirst :
              (adversarialOutputColumn gen i).1 = q :=
            (adversarialBlock_mem_iff.mp hbad).1
          rw [← hfirst]
          exact outputFirst_mem_algorithmForbidden
            gen hhits hiOld
        · exact ih i hiOld j hjOld

/-- The infinite set of all indices eventually accepted by the compressed
construction. -/
def algorithmSelectedIndices
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) : Set ℕ :=
  ⋃ n, (↑(algorithmSelection gen houtside hhits n) : Set ℕ)

theorem algorithmSelectedIndices_infinite
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    (algorithmSelectedIndices gen houtside hhits).Infinite := by
  by_contra hnot
  have hfinite :
      (algorithmSelectedIndices gen houtside hhits).Finite :=
    Set.not_infinite.mp hnot
  let N := hfinite.toFinset.card + 1
  have hsub :
      algorithmSelection gen houtside hhits N ⊆ hfinite.toFinset := by
    intro i hi
    apply hfinite.mem_toFinset.mpr
    exact Set.mem_iUnion.mpr ⟨N, hi⟩
  have hcard :=
    Finset.card_le_card hsub
  rw [algorithmSelection_card gen houtside hhits N] at hcard
  simp [N] at hcard

theorem algorithmSelectedIndices_mem_outside
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    {i : ℕ}
    (hi : i ∈ algorithmSelectedIndices gen houtside hhits) :
    i ∈ outsideBlockIndices gen := by
  obtain ⟨n, hin⟩ := Set.mem_iUnion.mp hi
  exact algorithmSelection_mem_outside
    gen houtside hhits n i hin

theorem algorithmSelectedIndices_conflictFree
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    {i j : ℕ}
    (hi : i ∈ algorithmSelectedIndices gen houtside hhits)
    (hj : j ∈ algorithmSelectedIndices gen houtside hhits) :
    adversarialOutputColumn gen i ∉ adversarialBlock j := by
  obtain ⟨n, hin⟩ := Set.mem_iUnion.mp hi
  obtain ⟨m, hjm⟩ := Set.mem_iUnion.mp hj
  let k := max n m
  have hik :
      i ∈ algorithmSelection gen houtside hhits k :=
    algorithmSelection_mono gen houtside hhits
      (Nat.le_max_left n m) hin
  have hjk :
      j ∈ algorithmSelection gen houtside hhits k :=
    algorithmSelection_mono gen houtside hhits
      (Nat.le_max_right n m) hjm
  exact algorithmSelection_conflictFree
    gen houtside hhits k i hik j hjk

/-- The target columns assembled by the final branch. -/
def algorithmBranchColumns
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    Set ColumnIndex :=
  {c | ∃ i,
    i ∈ algorithmSelectedIndices gen houtside hhits ∧
    c ∈ adversarialBlock i}

theorem algorithmBranchColumns_nonempty
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    (algorithmBranchColumns gen houtside hhits).Nonempty := by
  obtain ⟨i, hi⟩ :=
    (algorithmSelectedIndices_infinite gen houtside hhits).nonempty
  refine ⟨(i, 0), i, hi, ?_⟩
  apply adversarialBlock_mem_iff.mpr
  exact ⟨rfl, by omega⟩

theorem algorithmBranch_output_not_target
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite)
    {i : ℕ}
    (hi : i ∈ algorithmSelectedIndices gen houtside hhits) :
    adversarialOutputColumn gen i ∉
      algorithmBranchColumns gen houtside hhits := by
  intro hout
  obtain ⟨j, hj, houtBlock⟩ := hout
  exact
    algorithmSelectedIndices_conflictFree
      gen houtside hhits hi hj houtBlock

/-- The final branch of Theorem 2.17, using the accepted-update compression
of Algorithm 1. -/
theorem algorithm_branch_defeats_nonuniform
    (gen : GenLimit.Generic.Generator ColumnPoint)
    (houtside : (outsideBlockIndices gen).Infinite)
    (hhits : ∀ j, (indicesHittingBlock gen j).Finite) :
    ¬IsNonuniformGeneratorAtNoiseLevel gen columnUnionClass 1 := by
  let I := algorithmSelectedIndices gen houtside hhits
  let target := algorithmBranchColumns gen houtside hhits
  apply infinite_full_blocks_defeat_nonuniform
    gen
    (algorithmSelectedIndices_infinite gen houtside hhits)
    (algorithmBranchColumns_nonempty gen houtside hhits)
  · intro i hi c hc
    exact ⟨i, hi, hc⟩
  · intro i hi
    exact algorithmBranch_output_not_target gen houtside hhits hi

/-! ## The complete separation -/

/-- Every fixed generator is defeated by one of the paper's three infinite
branches. -/
theorem columnUnionClass_defeats_every_generator
    (gen : GenLimit.Generic.Generator ColumnPoint) :
    ¬IsNonuniformGeneratorAtNoiseLevel gen columnUnionClass 1 := by
  by_cases hinside : (insideBlockIndices gen).Infinite
  · exact infinite_inside_blocks_defeats_nonuniform gen hinside
  · have hinsideFinite :
        (insideBlockIndices gen).Finite :=
      Set.not_infinite.mp hinside
    have houtside : (outsideBlockIndices gen).Infinite := by
      exact hinsideFinite.infinite_compl
    by_cases hrepeat :
        ∃ j, (indicesHittingBlock gen j).Infinite
    · obtain ⟨j, hj⟩ := hrepeat
      exact infinite_hits_to_one_block_defeats_nonuniform gen hj
    · have hhits :
          ∀ j, (indicesHittingBlock gen j).Finite := by
        intro j
        exact Set.not_infinite.mp (fun h => hrepeat ⟨j, h⟩)
      exact algorithm_branch_defeats_nonuniform
        gen houtside hhits

/-- The lower-bound half of Theorem 2.17. -/
theorem columnUnionClass_not_nonuniform_level_one :
    ¬NonuniformGeneratableAtNoiseLevel columnUnionClass 1 := by
  rintro ⟨gen, hgen⟩
  exact columnUnionClass_defeats_every_generator gen hgen

/-- Fixed-level uniform generation implies fixed-level non-uniform
generation with the same generator and threshold. -/
theorem uniform_fixed_level_implies_nonuniform
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (h : UniformGeneratableAtNoiseLevel C i) :
    NonuniformGeneratableAtNoiseLevel C i := by
  obtain ⟨gen, T, hT⟩ := h
  refine ⟨gen, ?_⟩
  intro L hLC
  exact ⟨T, hT L hLC⟩

/-- Theorem 2.17 in the paper's literal semantic model. -/
theorem theorem_2_17 :
    UniformGeneratableAtNoiseLevel columnUnionClass 0 ∧
      ¬NonuniformGeneratableAtNoiseLevel columnUnionClass 1 :=
  ⟨columnUnionClass_uniform_noiseless,
    columnUnionClass_not_nonuniform_level_one⟩

/-- The separate existence clause in Theorem 2.18.  The stronger
non-uniform lower bound from Theorem 2.17 immediately implies the printed
uniform lower bound. -/
theorem theorem_2_18_separation_clause :
    UniformGeneratableAtNoiseLevel columnUnionClass 0 ∧
      ¬UniformGeneratableAtNoiseLevel columnUnionClass 1 := by
  refine ⟨columnUnionClass_uniform_noiseless, ?_⟩
  intro h
  exact columnUnionClass_not_nonuniform_level_one
    (uniform_fixed_level_implies_nonuniform h)

end GenLimit.QuantifyingNoise
