import GenLimit.Paper19_EffectOfNoise.FixedLevel
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Quantifying Noise: square-root descent infrastructure

This file formalizes the representation-independent parts of Li--Zhang
Lemma 3.2 (arXiv:2601.21237v2).  The source first restricts an arbitrarily
large witness to exactly `k²` points, partitions it into `k` blocks, and then
transfers finiteness through an inclusion of version spaces.  The exact-size
restriction and the version-space transfer are proved below.

The remaining paper-specific combinatorial obligation is to construct the
balanced block partition with a nonempty level-`i-1` version space in every
block.  The fresh representative construction and the proof that every
level-`i` language misses at most one representative are kernel-checked
below.  Keeping the partition obligation explicit avoids treating the
source's informal "without loss of generality, `S = {1,...,k²}`" as a
definitional equality.
-/

namespace GenLimit.QuantifyingNoise

/-! ## Balanced finite partitions -/

/-- The `j`th row of a finite set after identifying it with a `k × k`
grid.  Using an equivalence rather than an ambient enumeration keeps the
construction valid on an arbitrary universe. -/
private noncomputable def blockOfGridEquiv
    (S : Finset α) (e : S ≃ Fin k × Fin k) (j : Fin k) : Finset α := by
  classical
  exact Finset.univ.image (fun r : Fin k => (e.symm (j, r)).1)

private theorem blockOfGridEquiv_card
    (S : Finset α) (e : S ≃ Fin k × Fin k) (j : Fin k) :
    (blockOfGridEquiv S e j).card = k := by
  classical
  rw [blockOfGridEquiv, Finset.card_image_of_injective]
  · simp
  · intro r s hrs
    have hsub :
        e.symm (j, r) = e.symm (j, s) :=
      Subtype.ext hrs
    have hpairs : (j, r) = (j, s) :=
      e.symm.injective hsub
    exact congrArg Prod.snd hpairs

private theorem blockOfGridEquiv_subset
    (S : Finset α) (e : S ≃ Fin k × Fin k) (j : Fin k) :
    blockOfGridEquiv S e j ⊆ S := by
  classical
  intro x hx
  simp only [blockOfGridEquiv] at hx
  obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hx
  exact (e.symm (j, r)).2

private theorem blockOfGridEquiv_disjoint
    (S : Finset α) (e : S ≃ Fin k × Fin k)
    {j l : Fin k} (hjl : j ≠ l) :
    Disjoint (blockOfGridEquiv S e j) (blockOfGridEquiv S e l) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxj hxl
  simp only [blockOfGridEquiv] at hxj hxl
  obtain ⟨r, -, hr⟩ := Finset.mem_image.mp hxj
  obtain ⟨s, -, hs⟩ := Finset.mem_image.mp hxl
  have hsub :
      e.symm (j, r) = e.symm (l, s) := by
    apply Subtype.ext
    exact hr.trans hs.symm
  have hpairs : (j, r) = (l, s) :=
    e.symm.injective hsub
  exact hjl (congrArg Prod.fst hpairs)

/-- Every `k²`-element finite set has a partition into `k` disjoint
`k`-element rows. -/
theorem exists_balanced_grid_partition
    {S : Finset α} {k : ℕ} (hcard : S.card = k * k) :
    ∃ B : Fin k → Finset α,
      (∀ j, (B j).card = k) ∧
      (∀ j, B j ⊆ S) ∧
      (∀ j l, j ≠ l → Disjoint (B j) (B l)) := by
  classical
  let e : S ≃ Fin k × Fin k :=
    (S.equivFinOfCardEq hcard).trans finProdFinEquiv.symm
  refine ⟨blockOfGridEquiv S e,
    blockOfGridEquiv_card S e,
    blockOfGridEquiv_subset S e, ?_⟩
  intro j l hjl
  exact blockOfGridEquiv_disjoint S e hjl

/-- If `N ⊆ S` has at most `k` points, a balanced `k × k` partition can be
chosen so that every row contains at most one point of `N`.  This is the
finite combinatorial construction used in the `k ≥ i` case of Lemma 3.2. -/
theorem exists_balanced_grid_partition_spreading
    {S N : Finset α} {k : ℕ}
    (hk : 0 < k) (hNS : N ⊆ S)
    (hNcard : N.card ≤ k) (hScard : S.card = k * k) :
    ∃ B : Fin k → Finset α,
      (∀ j, (B j).card = k) ∧
      (∀ j, B j ⊆ S) ∧
      (∀ j l, j ≠ l → Disjoint (B j) (B l)) ∧
      (∀ j a, a ∈ B j → a ∈ N →
        ∀ b, b ∈ B j → b ∈ N → a = b) := by
  classical
  let zeroK : Fin k := ⟨0, hk⟩
  let row : N → Fin k :=
    fun x => Fin.castLE hNcard (N.equivFin x)
  let marked : Finset S :=
    Finset.univ.filter (fun x => (x : α) ∈ N)
  let prescribed : S → Fin k × Fin k :=
    fun x =>
      if hx : (x : α) ∈ N then
        (row ⟨x, hx⟩, zeroK)
      else
        (zeroK, zeroK)
  have hprescribedMaps :
      Finset.image prescribed marked ⊆
        (Finset.univ : Finset (Fin k × Fin k)) := by
    simp
  have hprescribedInj :
      Set.InjOn prescribed (marked : Set S) := by
    intro a ha b hb hab
    have haN : (a : α) ∈ N := by
      simpa [marked] using ha
    have hbN : (b : α) ∈ N := by
      simpa [marked] using hb
    have hrow :
        row ⟨a, haN⟩ = row ⟨b, hbN⟩ := by
      simpa [prescribed, haN, hbN] using congrArg Prod.fst hab
    have hindex :
        N.equivFin ⟨a, haN⟩ =
          N.equivFin ⟨b, hbN⟩ :=
      Fin.castLE_injective hNcard hrow
    have hnsub :
        (⟨a, haN⟩ : N) = ⟨b, hbN⟩ :=
      N.equivFin.injective hindex
    have hab : (a : α) = (b : α) :=
      congrArg (fun z : N => (z : α)) hnsub
    exact Subtype.ext hab
  have hcardTarget :
      Fintype.card S =
        (Finset.univ : Finset (Fin k × Fin k)).card := by
    simp [hScard]
  obtain ⟨eFinset, heFinset⟩ :=
    Finset.exists_equiv_extend_of_card_eq
      hcardTarget hprescribedMaps hprescribedInj
  let univEquiv :
      (Finset.univ : Finset (Fin k × Fin k)) ≃
        Fin k × Fin k := {
    toFun x := x
    invFun x := ⟨x, Finset.mem_univ x⟩
    left_inv _ := rfl
    right_inv _ := rfl
  }
  let e : S ≃ Fin k × Fin k :=
    eFinset.trans univEquiv
  have hePrescribed (a : S) (ha : (a : α) ∈ N) :
      e a = (row ⟨a, ha⟩, zeroK) := by
    change (eFinset a : Fin k × Fin k) =
      (row ⟨a, ha⟩, zeroK)
    rw [heFinset a]
    · simp [prescribed, ha]
    · simp [marked, ha]
  let B : Fin k → Finset α := blockOfGridEquiv S e
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro j
    exact blockOfGridEquiv_card S e j
  · intro j
    exact blockOfGridEquiv_subset S e j
  · intro j l hjl
    exact blockOfGridEquiv_disjoint S e hjl
  · intro j a haB haN b hbB hbN
    have haS : a ∈ S := hNS haN
    have hbS : b ∈ S := hNS hbN
    change a ∈ blockOfGridEquiv S e j at haB
    change b ∈ blockOfGridEquiv S e j at hbB
    simp only [blockOfGridEquiv] at haB hbB
    obtain ⟨r, -, hra⟩ := Finset.mem_image.mp haB
    obtain ⟨s, -, hsb⟩ := Finset.mem_image.mp hbB
    have hea : e ⟨a, haS⟩ = (j, r) := by
      have hsub :
          e.symm (j, r) = ⟨a, haS⟩ :=
        Subtype.ext hra
      have := congrArg e hsub
      simpa using this.symm
    have heb : e ⟨b, hbS⟩ = (j, s) := by
      have hsub :
          e.symm (j, s) = ⟨b, hbS⟩ :=
        Subtype.ext hsb
      have := congrArg e hsub
      simpa using this.symm
    have hrowa : row ⟨a, haN⟩ = j := by
      rw [hePrescribed ⟨a, haS⟩ haN] at hea
      exact congrArg Prod.fst hea
    have hrowb : row ⟨b, hbN⟩ = j := by
      rw [hePrescribed ⟨b, hbS⟩ hbN] at heb
      exact congrArg Prod.fst heb
    have hindex :
        N.equivFin ⟨a, haN⟩ =
          N.equivFin ⟨b, hbN⟩ := by
      apply Fin.castLE_injective hNcard
      exact hrowa.trans hrowb.symm
    have hnsub :
        (⟨a, haN⟩ : N) = ⟨b, hbN⟩ :=
      N.equivFin.injective hindex
    exact congrArg Subtype.val hnsub

/-- The first half of Lemma 3.2: a `k²`-point level-`i` version space
admits a balanced partition whose every row has a nonempty level-`i-1`
version space.  The proof follows the source's two cases, but chooses one
level-`i` language first and then tests whether that language already works
at level `i-1`. -/
theorem exists_balanced_partition_with_lower_version
    {C : GenLimit.Generic.LanguageClass α}
    {S : Finset α} {i k : ℕ}
    (hi : 2 ≤ i) (hk : 1 ≤ k)
    (hScard : S.card = k * k)
    (hSversion :
      (consistentLanguages C (↑S : Set α) i).Nonempty) :
    ∃ B : Fin k → Finset α,
      (∀ j, (B j).card = k) ∧
      (∀ j, B j ⊆ S) ∧
      (∀ j l, j ≠ l → Disjoint (B j) (B l)) ∧
      (∀ j,
        (consistentLanguages C
          (↑(B j) : Set α) (i - 1)).Nonempty) := by
  classical
  obtain ⟨L, hLS⟩ := hSversion
  by_cases hsmall : k ≤ i - 1
  · obtain ⟨B, hBcard, hBsubset, hBdisjoint⟩ :=
      exists_balanced_grid_partition hScard
    refine ⟨B, hBcard, hBsubset, hBdisjoint, ?_⟩
    intro j
    refine ⟨L, hLS.1, ?_⟩
    apply missingAtMost_mono hsmall
    rw [missingAtMost_finset_iff]
    exact
      (Finset.card_filter_le (B j) (fun x => x ∉ L)).trans_eq
        (hBcard j)
  · have hik : i ≤ k := by omega
    by_cases hLlower :
        L ∈ consistentLanguages C (↑S : Set α) (i - 1)
    · obtain ⟨B, hBcard, hBsubset, hBdisjoint⟩ :=
        exists_balanced_grid_partition hScard
      refine ⟨B, hBcard, hBsubset, hBdisjoint, ?_⟩
      intro j
      refine ⟨L, hLlower.1, ?_⟩
      rw [missingAtMost_finset_iff]
      apply (Finset.card_le_card ?_).trans
        ((missingAtMost_finset_iff S L (i - 1)).mp hLlower.2)
      intro x hx
      simp only [GenLimit.NoisyExamples.negativePart,
        Finset.mem_filter] at hx ⊢
      exact ⟨hBsubset j hx.1, hx.2⟩
    · let N := GenLimit.NoisyExamples.negativePart S L
      have hNsubset : N ⊆ S := by
        intro x hx
        exact (Finset.mem_filter.mp hx).1
      have hNle : N.card ≤ i := by
        simpa [N, missingAtMost_finset_iff] using hLS.2
      have hNnotLe : ¬N.card ≤ i - 1 := by
        intro hle
        apply hLlower
        refine ⟨hLS.1, ?_⟩
        rw [missingAtMost_finset_iff]
        simpa [N] using hle
      have hNcard : N.card = i := by omega
      obtain
          ⟨B, hBcard, hBsubset, hBdisjoint, hspread⟩ :=
        exists_balanced_grid_partition_spreading
          (lt_of_lt_of_le Nat.zero_lt_one hk)
          hNsubset (by simpa [hNcard] using hik) hScard
      refine ⟨B, hBcard, hBsubset, hBdisjoint, ?_⟩
      intro j
      refine ⟨L, hLS.1, ?_⟩
      rw [missingAtMost_finset_iff]
      have hcardOne :
          (GenLimit.NoisyExamples.negativePart (B j) L).card ≤ 1 := by
        rw [Finset.card_le_one_iff]
        intro a b ha hb
        have haParts :
            a ∈ B j ∧ a ∉ L := by
          simpa [GenLimit.NoisyExamples.negativePart] using ha
        have hbParts :
            b ∈ B j ∧ b ∉ L := by
          simpa [GenLimit.NoisyExamples.negativePart] using hb
        apply hspread j a haParts.1
        · simpa [N, GenLimit.NoisyExamples.negativePart] using
            ⟨hBsubset j haParts.1, haParts.2⟩
        · exact hbParts.1
        · simpa [N, GenLimit.NoisyExamples.negativePart] using
            ⟨hBsubset j hbParts.1, hbParts.2⟩
      exact hcardOne.trans (by omega)

private theorem arbitrarily_large_witness_for_square_root
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (hnot : ¬FiniteNoisyClosureDimensionAt C i) :
    ∀ D, ∃ d, D < d ∧ NoisyClosureWitnessAt C i d := by
  intro D
  by_contra hnone
  apply hnot
  refine ⟨D, ?_⟩
  intro d hDd hwit
  exact hnone ⟨d, hDd, hwit⟩

theorem missingAtMost_finset_of_subset
    {S T : Finset α} {L : Set α} {i : ℕ}
    (hST : S ⊆ T)
    (hT : MissingAtMost (↑T : Set α) L i) :
    MissingAtMost (↑S : Set α) L i := by
  classical
  rw [missingAtMost_finset_iff] at hT ⊢
  apply (Finset.card_le_card ?_).trans hT
  intro x hx
  simp only [GenLimit.NoisyExamples.negativePart,
    Finset.mem_filter] at hx ⊢
  exact ⟨hST hx.1, hx.2⟩

theorem consistentLanguages_finset_antitone
    {C : GenLimit.Generic.LanguageClass α}
    {S T : Finset α} {i : ℕ}
    (hST : S ⊆ T) :
    consistentLanguages C (↑T : Set α) i ⊆
      consistentLanguages C (↑S : Set α) i := by
  rintro L ⟨hLC, hmissing⟩
  exact ⟨hLC, missingAtMost_finset_of_subset hST hmissing⟩

/-- Restricting the observed finite set enlarges the version space and hence
shrinks its noisy closure, provided the original version space was nonempty.
This is the monotonicity used in the first paragraph of Lemma 3.2. -/
theorem noisyClosure_finset_antitone
    {C : GenLimit.Generic.LanguageClass α}
    {S T : Finset α} {i : ℕ}
    (hST : S ⊆ T)
    (hT : (consistentLanguages C (↑T : Set α) i).Nonempty) :
    noisyClosure C (↑S : Set α) i ⊆
      noisyClosure C (↑T : Set α) i := by
  have hTS :=
    consistentLanguages_finset_antitone
      (C := C) (i := i) hST
  have hS :
      (consistentLanguages C (↑S : Set α) i).Nonempty :=
    hT.mono hTS
  rw [noisyClosure_eq_commonCore hS,
    noisyClosure_eq_commonCore hT]
  intro x hx L hLT
  exact hx L (hTS hLT)

/-- A witness of size at least `d` can be restricted to a witness of size
exactly `d`.  This supplies the step that the paper phrases as choosing a
`k²`-element subset of a larger witness. -/
theorem noisyClosureWitnessAt_restrict
    {C : GenLimit.Generic.LanguageClass α}
    {i d e : ℕ} (hde : d ≤ e)
    (h : NoisyClosureWitnessAt C i e) :
    NoisyClosureWitnessAt C i d := by
  classical
  obtain ⟨T, hTcard, hTversion, hTfinite⟩ := h
  have hdT : d ≤ T.card := by simpa [hTcard] using hde
  obtain ⟨S, hST, hScard⟩ := Finset.exists_subset_card_eq hdT
  have hSversion :
      (consistentLanguages C (↑S : Set α) i).Nonempty :=
    hTversion.mono
      (consistentLanguages_finset_antitone
        (C := C) (i := i) hST)
  refine ⟨S, hScard, hSversion, ?_⟩
  exact hTfinite.subset
    (noisyClosure_finset_antitone
      (C := C) (i := i) hST hTversion)

/-- If every language in the first version space belongs to the second, the
second closure is contained in the first closure. -/
theorem noisyClosure_subset_of_consistentLanguages_subset
    {C : GenLimit.Generic.LanguageClass α}
    {S A : Set α} {i j : ℕ}
    (hS : (consistentLanguages C S i).Nonempty)
    (hA : (consistentLanguages C A j).Nonempty)
    (hversion :
      consistentLanguages C S i ⊆ consistentLanguages C A j) :
    noisyClosure C A j ⊆ noisyClosure C S i := by
  rw [noisyClosure_eq_commonCore hA,
    noisyClosure_eq_commonCore hS]
  intro x hx L hLS
  exact hx L (hversion hLS)

/-- The closing transfer in Lemma 3.2: once the representative set `A` has
size `k`, a nonempty level-`j` version space, and contains every level-`i`
version of the original witness `S`, it is itself a size-`k` finite-closure
witness at level `j`. -/
theorem noisyClosureWitnessAt_of_version_space_transfer
    {C : GenLimit.Generic.LanguageClass α}
    {S A : Finset α} {i j k : ℕ}
    (hAcard : A.card = k)
    (hS : (consistentLanguages C (↑S : Set α) i).Nonempty)
    (hA : (consistentLanguages C (↑A : Set α) j).Nonempty)
    (hversion :
      consistentLanguages C (↑S : Set α) i ⊆
        consistentLanguages C (↑A : Set α) j)
    (hSfinite : (noisyClosure C (↑S : Set α) i).Finite) :
    NoisyClosureWitnessAt C j k := by
  refine ⟨A, hAcard, hA, ?_⟩
  exact hSfinite.subset
    (noisyClosure_subset_of_consistentLanguages_subset
      hS hA hversion)

/-! ## The representative-set half of Lemma 3.2 -/

/-- Two disjoint blocks cannot both be inconsistent at level `i-1` with a
language that is consistent with their ambient witness at level `i`.
This is the source proof's `2i > i` counting contradiction. -/
theorem at_most_one_inconsistent_disjoint_block
    {C : GenLimit.Generic.LanguageClass α}
    {S : Finset α} {i : ℕ}
    (hi : 2 ≤ i)
    {B : Fin k → Finset α}
    (hBsubset : ∀ j, B j ⊆ S)
    (hBdisjoint : ∀ j l, j ≠ l → Disjoint (B j) (B l))
    {L : GenLimit.Generic.Language α}
    (hLS : L ∈ consistentLanguages C (↑S : Set α) i)
    {j l : Fin k} (hjl : j ≠ l)
    (hjbad :
      L ∉ consistentLanguages C (↑(B j) : Set α) (i - 1))
    (hlbad :
      L ∉ consistentLanguages C (↑(B l) : Set α) (i - 1)) :
    False := by
  classical
  let Nj := GenLimit.NoisyExamples.negativePart (B j) L
  let Nl := GenLimit.NoisyExamples.negativePart (B l) L
  let NS := GenLimit.NoisyExamples.negativePart S L
  have hjmissing :
      ¬MissingAtMost (↑(B j) : Set α) L (i - 1) := by
    intro h
    exact hjbad ⟨hLS.1, h⟩
  have hlmissing :
      ¬MissingAtMost (↑(B l) : Set α) L (i - 1) := by
    intro h
    exact hlbad ⟨hLS.1, h⟩
  have hjcard : i ≤ Nj.card := by
    rw [missingAtMost_finset_iff] at hjmissing
    dsimp [Nj]
    omega
  have hlcard : i ≤ Nl.card := by
    rw [missingAtMost_finset_iff] at hlmissing
    dsimp [Nl]
    omega
  have hdisjoint : Disjoint Nj Nl := by
    apply Finset.disjoint_left.mpr
    intro x hxj hxl
    have hxjB : x ∈ B j := by
      change x ∈ GenLimit.NoisyExamples.negativePart (B j) L at hxj
      exact (Finset.mem_filter.mp hxj).1
    have hxlB : x ∈ B l := by
      change x ∈ GenLimit.NoisyExamples.negativePart (B l) L at hxl
      exact (Finset.mem_filter.mp hxl).1
    exact Finset.disjoint_left.mp (hBdisjoint j l hjl) hxjB hxlB
  have hunion : Nj ∪ Nl ⊆ NS := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxj | hxl
    · have hxparts :
          x ∈ B j ∧ x ∉ L := by
        simpa [Nj, GenLimit.NoisyExamples.negativePart] using hxj
      simpa [NS, GenLimit.NoisyExamples.negativePart] using
        ⟨hBsubset j hxparts.1, hxparts.2⟩
    · have hxparts :
          x ∈ B l ∧ x ∉ L := by
        simpa [Nl, GenLimit.NoisyExamples.negativePart] using hxl
      simpa [NS, GenLimit.NoisyExamples.negativePart] using
        ⟨hBsubset l hxparts.1, hxparts.2⟩
  have hScard : NS.card ≤ i := by
    simpa [NS, missingAtMost_finset_iff] using hLS.2
  have hsum : Nj.card + Nl.card ≤ i := by
    calc
      Nj.card + Nl.card = (Nj ∪ Nl).card :=
        (Finset.card_union_of_disjoint hdisjoint).symm
      _ ≤ NS.card := Finset.card_le_card hunion
      _ ≤ i := hScard
  omega

/-- Given disjoint blocks and distinct representatives from their
level-`i-1` closures, the representative set is a size-`k` witness at level
`i-1`.  This formalizes the second half of the paper's square-root proof; the
balanced partition/representative construction is a separate obligation. -/
theorem squareRootWitness_of_partition_representatives
    {C : GenLimit.Generic.LanguageClass α}
    {S : Finset α} {i k : ℕ}
    (hi : 2 ≤ i)
    (hSversion :
      (consistentLanguages C (↑S : Set α) i).Nonempty)
    (hSfinite : (noisyClosure C (↑S : Set α) i).Finite)
    (B : Fin k → Finset α)
    (hBsubset : ∀ j, B j ⊆ S)
    (hBdisjoint : ∀ j l, j ≠ l → Disjoint (B j) (B l))
    (x : Fin k → α)
    (hxInjective : Function.Injective x)
    (hxClosure :
      ∀ j, x j ∈ noisyClosure C (↑(B j) : Set α) (i - 1)) :
    NoisyClosureWitnessAt C (i - 1) k := by
  classical
  let A : Finset α := Finset.univ.image x
  have hAcard : A.card = k := by
    dsimp [A]
    rw [Finset.card_image_of_injective Finset.univ hxInjective]
    simp
  have hversion :
      consistentLanguages C (↑S : Set α) i ⊆
        consistentLanguages C (↑A : Set α) (i - 1) := by
    intro L hLS
    refine ⟨hLS.1, (missingAtMost_finset_iff A L (i - 1)).mpr ?_⟩
    have hcardOne :
        (GenLimit.NoisyExamples.negativePart A L).card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro a b ha hb
      have haParts :
          a ∈ A ∧ a ∉ L := by
        simpa [GenLimit.NoisyExamples.negativePart] using ha
      have hbParts :
          b ∈ A ∧ b ∉ L := by
        simpa [GenLimit.NoisyExamples.negativePart] using hb
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp haParts.1
      obtain ⟨l, -, hl⟩ := Finset.mem_image.mp hbParts.1
      have hjnot : x j ∉ L := by simpa [hj] using haParts.2
      have hlnot : x l ∉ L := by simpa [hl] using hbParts.2
      by_cases hjl : j = l
      · calc
          a = x j := hj.symm
          _ = x l := congrArg x hjl
          _ = b := hl
      · have hjbad :
            L ∉ consistentLanguages C
              (↑(B j) : Set α) (i - 1) := by
          intro hLj
          exact hjnot (lemma_2_11 hLj (hxClosure j))
        have hlbad :
            L ∉ consistentLanguages C
              (↑(B l) : Set α) (i - 1) := by
          intro hLl
          exact hlnot (lemma_2_11 hLl (hxClosure l))
        exact False.elim
          (at_most_one_inconsistent_disjoint_block
            hi hBsubset hBdisjoint hLS hjl hjbad hlbad)
    exact hcardOne.trans (by omega)
  have hAversion :
      (consistentLanguages C (↑A : Set α) (i - 1)).Nonempty :=
    hSversion.mono hversion
  exact noisyClosureWitnessAt_of_version_space_transfer
    hAcard hSversion hAversion hversion hSfinite

/-- A finite family of infinite sets admits a system of distinct
representatives.  This kernel-checks the iterative fresh-choice step in the
source proof of Lemma 3.2. -/
theorem exists_injective_representatives_of_infinite
    (sets : Fin k → Set α)
    (hinfinite : ∀ j, (sets j).Infinite) :
    ∃ x : Fin k → α, Function.Injective x ∧
      ∀ j, x j ∈ sets j := by
  classical
  induction k with
  | zero =>
      refine ⟨fun j => Fin.elim0 j, ?_, ?_⟩
      · exact fun j => Fin.elim0 j
      · exact fun j => Fin.elim0 j
  | succ k ih =>
      let initialSets : Fin k → Set α :=
        fun j => sets j.castSucc
      obtain ⟨previous, hpreviousInjective, hpreviousMem⟩ :=
        ih initialSets (fun j => hinfinite j.castSucc)
      let used : Finset α := Finset.univ.image previous
      obtain ⟨fresh, hfreshMem, hfreshNotUsed⟩ :=
        (hinfinite (Fin.last k)).exists_notMem_finset used
      let chosen : Fin (k + 1) → α :=
        Fin.lastCases fresh previous
      refine ⟨chosen, ?_, ?_⟩
      · intro a b hab
        cases a using Fin.lastCases with
        | last =>
            cases b using Fin.lastCases with
            | last => rfl
            | cast b =>
                exfalso
                apply hfreshNotUsed
                apply Finset.mem_image.mpr
                refine ⟨b, Finset.mem_univ _, ?_⟩
                simpa [chosen] using hab.symm
        | cast a =>
            cases b using Fin.lastCases with
            | last =>
                exfalso
                apply hfreshNotUsed
                apply Finset.mem_image.mpr
                refine ⟨a, Finset.mem_univ _, ?_⟩
                simpa [chosen] using hab
            | cast b =>
                have habPrevious : previous a = previous b := by
                  simpa [chosen] using hab
                exact congrArg Fin.castSucc
                  (hpreviousInjective habPrevious)
      · intro j
        cases j using Fin.lastCases with
        | last =>
            simpa [chosen] using hfreshMem
        | cast j =>
            simpa [chosen, initialSets] using hpreviousMem j

/-- The paper's finite/infinite block-closure case split.  A finite block
closure is already the required witness.  If all block closures are
infinite, a system of distinct representatives finishes the construction
through `squareRootWitness_of_partition_representatives`. -/
theorem squareRootWitness_of_balanced_partition
    {C : GenLimit.Generic.LanguageClass α}
    {S : Finset α} {i k : ℕ}
    (hi : 2 ≤ i)
    (hSversion :
      (consistentLanguages C (↑S : Set α) i).Nonempty)
    (hSfinite : (noisyClosure C (↑S : Set α) i).Finite)
    (B : Fin k → Finset α)
    (hBcard : ∀ j, (B j).card = k)
    (hBsubset : ∀ j, B j ⊆ S)
    (hBdisjoint : ∀ j l, j ≠ l → Disjoint (B j) (B l))
    (hBversion :
      ∀ j,
        (consistentLanguages C (↑(B j) : Set α) (i - 1)).Nonempty) :
    NoisyClosureWitnessAt C (i - 1) k := by
  classical
  by_cases hfinite :
      ∃ j,
        (noisyClosure C (↑(B j) : Set α) (i - 1)).Finite
  · obtain ⟨j, hjfinite⟩ := hfinite
    exact ⟨B j, hBcard j, hBversion j, hjfinite⟩
  · have hinfinite :
        ∀ j,
          (noisyClosure C (↑(B j) : Set α) (i - 1)).Infinite := by
      intro j
      by_contra hnot
      exact hfinite ⟨j, Set.not_infinite.mp hnot⟩
    obtain ⟨x, hxInjective, hxClosure⟩ :=
      exists_injective_representatives_of_infinite
        (fun j =>
          noisyClosure C (↑(B j) : Set α) (i - 1))
        hinfinite
    exact squareRootWitness_of_partition_representatives
      hi hSversion hSfinite B hBsubset hBdisjoint
        x hxInjective hxClosure

/-- The local witness implication isolated by the square-root argument. -/
def SquareRootWitnessTransfer
    (C : GenLimit.Generic.LanguageClass α) (i : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    NoisyClosureWitnessAt C i (k * k) →
      NoisyClosureWitnessAt C (i - 1) k

/-- Lemma 3.2, exact local form: every size-`k²` witness at noise level
`i ≥ 2` yields a size-`k` witness at level `i-1`. -/
theorem lemma_3_2_squareRootWitnessTransfer
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (hi : 2 ≤ i) :
    SquareRootWitnessTransfer C i := by
  intro k hk hSquare
  obtain ⟨S, hScard, hSversion, hSfinite⟩ := hSquare
  obtain ⟨B, hBcard, hBsubset, hBdisjoint, hBversion⟩ :=
    exists_balanced_partition_with_lower_version
      hi hk hScard hSversion
  exact squareRootWitness_of_balanced_partition
    hi hSversion hSfinite B hBcard hBsubset hBdisjoint hBversion

/-- Once the local `k² ↦ k` transfer is available, infinite noisy-closure
dimension descends from level `i` to level `i-1`.  This is the "in
particular" clause of Lemma 3.2, stated using the project's unbounded-witness
definition rather than an artificial infinity value. -/
theorem infinite_dimension_descends_of_squareRootWitnessTransfer
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (htransfer : SquareRootWitnessTransfer C i)
    (hi : ¬FiniteNoisyClosureDimensionAt C i) :
    ¬FiniteNoisyClosureDimensionAt C (i - 1) := by
  intro hpred
  obtain ⟨D, hD⟩ := hpred
  let k := D + 1
  obtain ⟨e, he, heWitness⟩ :=
    arbitrarily_large_witness_for_square_root hi (k * k)
  have hSquare :
      NoisyClosureWitnessAt C i (k * k) :=
    noisyClosureWitnessAt_restrict (Nat.le_of_lt he) heWitness
  have hkpos : 1 ≤ k := by
    simp [k]
  have hkWitness :
      NoisyClosureWitnessAt C (i - 1) k :=
    htransfer k hkpos hSquare
  exact hD k (by simp [k]) hkWitness

/-- Lemma 3.2, infinite-dimension clause. -/
theorem lemma_3_2_infinite_dimension_descends
    {C : GenLimit.Generic.LanguageClass α} {i : ℕ}
    (hi : 2 ≤ i)
    (hInfinite : ¬FiniteNoisyClosureDimensionAt C i) :
    ¬FiniteNoisyClosureDimensionAt C (i - 1) :=
  infinite_dimension_descends_of_squareRootWitnessTransfer
    (lemma_3_2_squareRootWitnessTransfer hi) hInfinite

/-! ## Uniform finite-noise collapse -/

/-- The contrapositive iteration of Lemma 3.2: finite noisy-closure
dimension at level one implies finiteness at every positive finite level. -/
theorem finite_dimension_propagates_from_one
    {C : GenLimit.Generic.LanguageClass α}
    (hOne : FiniteNoisyClosureDimensionAt C 1) :
    ∀ i : ℕ, 1 ≤ i → FiniteNoisyClosureDimensionAt C i := by
  intro i hi
  induction i with
  | zero => omega
  | succ i ih =>
      by_cases hiZero : i = 0
      · simpa [hiZero] using hOne
      · have hiPos : 1 ≤ i :=
          Nat.one_le_iff_ne_zero.mpr hiZero
        have hPrev :
            FiniteNoisyClosureDimensionAt C i :=
          ih hiPos
        by_contra hNext
        have hDesc :
            ¬FiniteNoisyClosureDimensionAt C ((i + 1) - 1) :=
          lemma_3_2_infinite_dimension_descends
            (i := i + 1) (by omega) hNext
        have hDesc' :
            ¬FiniteNoisyClosureDimensionAt C i := by
          simpa using hDesc
        exact hDesc' hPrev

/-- Theorem 3.3, and the uniform half of Theorem 2.16: every positive
finite noise level is equivalent to noise level one. -/
theorem theorem_3_3_uniform_finite_noise_collapse
    [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α}
    (hInfinite : AllLanguagesInfinite C)
    {i : ℕ} (hi : 1 ≤ i) :
    UniformGeneratableAtNoiseLevel C i ↔
      UniformGeneratableAtNoiseLevel C 1 := by
  constructor
  · exact uniformGeneratableAtNoiseLevel_anti hi
  · intro hOne
    have hDimOne :
        FiniteNoisyClosureDimensionAt C 1 :=
      (lemma_3_1 hInfinite).mp hOne
    have hDimI :
        FiniteNoisyClosureDimensionAt C i :=
      finite_dimension_propagates_from_one hDimOne i hi
    exact (lemma_3_1 hInfinite).mpr hDimI

/-- Paper-numbered alias for the uniform half of Theorem 2.16. -/
theorem theorem_2_16_uniform
    [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α}
    (hInfinite : AllLanguagesInfinite C)
    {i : ℕ} (hi : 1 ≤ i) :
    UniformGeneratableAtNoiseLevel C i ↔
      UniformGeneratableAtNoiseLevel C 1 :=
  theorem_3_3_uniform_finite_noise_collapse hInfinite hi

/-- Theorem 3.5: uniform noise-dependent generation is equivalent to
uniform generation with one noisy value. -/
theorem theorem_3_5_uniform_noise_dependent_iff_level_one
    [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α}
    (hInfinite : AllLanguagesInfinite C) :
    UniformNoiseDependentGeneratable C ↔
      UniformGeneratableAtNoiseLevel C 1 := by
  constructor
  · rintro ⟨gen, hgen⟩
    exact ⟨gen, hgen 1⟩
  · intro hOne
    have hDimOne :
        FiniteNoisyClosureDimensionAt C 1 :=
      (lemma_3_1 hInfinite).mp hOne
    apply finite_dimensions_imply_uniformNoiseDependent
    intro i
    by_cases hi : i = 0
    · subst i
      exact finiteNoisyClosureDimensionAt_anti
        (i := 0) (j := 1) (by omega) hDimOne
    · exact finite_dimension_propagates_from_one
        hDimOne i (Nat.one_le_iff_ne_zero.mpr hi)

/-- The three equivalent conditions in the positive, uniform part of
Theorem 2.18.  The paper's separate noiseless/noisy separation is not part
of this declaration. -/
theorem theorem_2_18_uniform_equivalences
    [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α}
    (hInfinite : AllLanguagesInfinite C) :
    FiniteNoisyClosureDimensionAt C 1 ↔
      ((∀ i : ℕ, 1 ≤ i →
          UniformGeneratableAtNoiseLevel C i) ∧
        UniformNoiseDependentGeneratable C) := by
  constructor
  · intro hDimOne
    have hOne :
        UniformGeneratableAtNoiseLevel C 1 :=
      (lemma_3_1 hInfinite).mpr hDimOne
    refine ⟨?_, ?_⟩
    · intro i hi
      exact
        (theorem_3_3_uniform_finite_noise_collapse
          hInfinite hi).mpr hOne
    · exact
        (theorem_3_5_uniform_noise_dependent_iff_level_one
          hInfinite).mpr hOne
  · rintro ⟨hLevels, _hDependent⟩
    exact (lemma_3_1 hInfinite).mp (hLevels 1 (by omega))

/-- Literal three-way packaging of the positive uniform equivalences in
Theorem 2.18.  Both other conditions are separately equivalent to the
level-one finite noisy-closure dimension condition. -/
theorem theorem_2_18_uniform_equivalences_full
    [Countable α] [Nonempty α]
    {C : GenLimit.Generic.LanguageClass α}
    (hInfinite : AllLanguagesInfinite C) :
    (FiniteNoisyClosureDimensionAt C 1 ↔
      ∀ i : ℕ, 1 ≤ i → UniformGeneratableAtNoiseLevel C i) ∧
    (FiniteNoisyClosureDimensionAt C 1 ↔
      UniformNoiseDependentGeneratable C) := by
  refine ⟨?_, (lemma_3_1 hInfinite).symm.trans ?_⟩
  · constructor
    · intro hDimension
      exact (theorem_2_18_uniform_equivalences hInfinite).mp hDimension |>.1
    · intro hLevels
      exact (lemma_3_1 hInfinite).mp (hLevels 1 (by omega))
  · exact
      (theorem_3_5_uniform_noise_dependent_iff_level_one
        hInfinite).symm

end GenLimit.QuantifyingNoise
