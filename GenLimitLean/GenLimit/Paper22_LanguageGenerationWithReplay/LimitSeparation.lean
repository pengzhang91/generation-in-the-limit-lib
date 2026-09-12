import GenLimit.Paper22_LanguageGenerationWithReplay.Uniform
import GenLimit.Paper10_UnionClosednessOfLanguageGeneration.Cardinality
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Replay separates generation in the limit on an uncountable class

Source: Giorgio Racca, Michal Valko, and Amartya Sanyal,
*Language Generation with Replay: A Learning-Theoretic View of Model
Collapse*, arXiv:2603.11784v2, Definition 3.4 and Theorem 6.6,
including Lemmas 6.7--6.8.

The source domain is `ℤ ∪ {∗ⁿ | n ∈ ℕ}`.  We use `Sum ℤ ℕ`, with
`Sum.inr n` representing the paper marker `∗^(n+1)`.  Thus the marker
block `∗¹, ..., ∗ᵇ` is represented by the zero-based predicate `n < b`.

The ordinary upper-bound generator is a semantic simplification of the
displayed generator in Lemma 6.7.  It uses the same marker-index recovery
and the same two integer directions, but chooses an explicit integer beyond
the magnitude of the whole finite history instead of remembering its earlier
outputs.  This is sufficient because the paper's novelty condition excludes
the observed examples, not earlier outputs.
-/

namespace GenLimit
namespace Replay

open GenLimit.Generic

abbrev LimitReplayPoint := Sum ℤ ℕ

/-! ## Definition 3.4 -/

/-- A replay sequence that eventually reveals every target element.  Unlike
an ordinary exact presentation, it may additionally contain replayed outputs
outside the target. -/
def IsReplayEnumeration
    (gen : Generic.Generator α) (L : Generic.Language α)
    (stream : Generic.Stream α) : Prop :=
  IsReplaySequence gen L stream ∧
    ∀ x, x ∈ L → ∃ n, stream n = x

/-- A fixed generator succeeds in the limit on every enumeration with replay. -/
def IsLimitReplayGenerator
    (gen : Generic.Generator α)
    (H : Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ∀ stream : Generic.Stream α,
    IsReplayEnumeration gen L stream →
      ∃ T, ∀ t, T ≤ t → Generic.CorrectAt gen L stream t

/-- Definition 3.4: generation in the limit with replay. -/
def GeneratableInLimitWithReplay
    (H : Generic.LanguageClass α) : Prop :=
  ∃ gen : Generic.Generator α, IsLimitReplayGenerator gen H

/-! ## The literal hard class from Theorem 6.6 -/

/-- The paper's all-marker hypothesis `hᵐᵏ`. -/
def allMarkerLanguage : Generic.Language LimitReplayPoint
  | .inl _ => False
  | .inr _ => True

/-- A member of the padded first subclass `H̃₁ᵇ`.

On the integer copy this is `{b} ∪ A ∪ {z : z > j}` with `j > b`;
on the marker copy it contains exactly the first `b` markers. -/
def replayOneLanguage
    (b : ℕ) (A : Set ℤ) (j : ℤ) :
    Generic.Language LimitReplayPoint
  | .inl z => z = (b : ℤ) ∨ z ∈ A ∨ j < z
  | .inr n => n < b

/-- A member of the padded second subclass `H̃₂ᵇ`.

The side condition `A ⊆ ℤ \ {b}` is recorded by `replayTwoClass` below. -/
def replayTwoLanguage
    (b : ℕ) (A : Set ℤ) :
    Generic.Language LimitReplayPoint
  | .inl z => z < (b : ℤ) ∨ z ∈ A
  | .inr n => n < b

def replayOneClass (b : ℕ) :
    Generic.LanguageClass LimitReplayPoint :=
  {L | ∃ A : Set ℤ, ∃ j : ℤ,
    (b : ℤ) < j ∧ L = replayOneLanguage b A j}

def replayTwoClass (b : ℕ) :
    Generic.LanguageClass LimitReplayPoint :=
  {L | ∃ A : Set ℤ,
    A ⊆ ({z : ℤ | z ≠ (b : ℤ)}) ∧
      L = replayTwoLanguage b A}

/-- The source class
`{hᵐᵏ} ∪ ⋃ b, (H̃₁ᵇ ∪ H̃₂ᵇ)`. -/
def replayLimitHardClass :
    Generic.LanguageClass LimitReplayPoint :=
  {allMarkerLanguage} ∪
    ⋃ b : ℕ, (replayOneClass b ∪ replayTwoClass b)

theorem allMarkerLanguage_mem :
    allMarkerLanguage ∈ replayLimitHardClass := by
  exact Set.mem_union_left _ (Set.mem_singleton _)

theorem replayOneLanguage_mem
    (b : ℕ) (A : Set ℤ) (j : ℤ) (hbj : (b : ℤ) < j) :
    replayOneLanguage b A j ∈ replayLimitHardClass := by
  apply Set.mem_union_right
  apply Set.mem_iUnion.mpr
  refine ⟨b, Or.inl ?_⟩
  exact ⟨A, j, hbj, rfl⟩

theorem replayTwoLanguage_mem
    (b : ℕ) (A : Set ℤ)
    (hA : A ⊆ {z : ℤ | z ≠ (b : ℤ)}) :
    replayTwoLanguage b A ∈ replayLimitHardClass := by
  apply Set.mem_union_right
  apply Set.mem_iUnion.mpr
  refine ⟨b, Or.inr ?_⟩
  exact ⟨A, hA, rfl⟩

theorem allMarkerLanguage_infinite :
    allMarkerLanguage.Infinite := by
  have hrange :
      Set.range (Sum.inr : ℕ → LimitReplayPoint) ⊆
        allMarkerLanguage := by
    rintro _ ⟨n, rfl⟩
    trivial
  exact
    (Set.infinite_range_of_injective Sum.inr_injective).mono
      hrange

theorem replayOneLanguage_infinite
    (b : ℕ) (A : Set ℤ) (j : ℤ) :
    (replayOneLanguage b A j).Infinite := by
  let tail : ℕ → LimitReplayPoint :=
    fun n => Sum.inl (j + (n : ℤ) + 1)
  have hinjective : Function.Injective tail := by
    intro m n hmn
    have hz :
        j + (m : ℤ) + 1 =
          j + (n : ℤ) + 1 :=
      Sum.inl.inj hmn
    exact Int.ofNat_inj.mp (by omega)
  have hrange :
      Set.range tail ⊆ replayOneLanguage b A j := by
    rintro _ ⟨n, rfl⟩
    exact Or.inr (Or.inr (by
      omega))
  exact
    (Set.infinite_range_of_injective hinjective).mono hrange

theorem replayTwoLanguage_infinite
    (b : ℕ) (A : Set ℤ) :
    (replayTwoLanguage b A).Infinite := by
  let tail : ℕ → LimitReplayPoint :=
    fun n => Sum.inl ((b : ℤ) - (n : ℤ) - 1)
  have hinjective : Function.Injective tail := by
    intro m n hmn
    have hz :
        (b : ℤ) - (m : ℤ) - 1 =
          (b : ℤ) - (n : ℤ) - 1 :=
      Sum.inl.inj hmn
    exact Int.ofNat_inj.mp (by omega)
  have hrange :
      Set.range tail ⊆ replayTwoLanguage b A := by
    rintro _ ⟨n, rfl⟩
    exact Or.inl (by
      omega)
  exact
    (Set.infinite_range_of_injective hinjective).mono hrange

/-- The source's standing UUS condition for the Theorem 6.6 witness. -/
theorem replayLimitHardClass_uus :
    UUS replayLimitHardClass := by
  intro L hL
  change
    L ∈ ({allMarkerLanguage} :
      Set (Generic.Language LimitReplayPoint)) ∪
      ⋃ b : ℕ, (replayOneClass b ∪ replayTwoClass b)
      at hL
  rcases hL with hmarker | hindexed
  · have hL' : L = allMarkerLanguage := by
      simpa using hmarker
    subst L
    exact allMarkerLanguage_infinite
  · obtain ⟨b, hL⟩ := Set.mem_iUnion.mp hindexed
    rcases hL with
      ⟨A, j, _hbj, rfl⟩ | ⟨A, _hA, rfl⟩
    · exact replayOneLanguage_infinite b A j
    · exact replayTwoLanguage_infinite b A

/-! ## Uncountability of the literal class -/

/-- Positive integers encode an arbitrary set of naturals inside
`H̃₂⁰`; the required negative half-line remains fixed. -/
def replayPositiveEncoding (S : Set ℕ) : Set ℤ :=
  {z | ∃ n : ℕ, n ∈ S ∧ z = (n : ℤ) + 1}

def replayEncodedLanguage (S : Set ℕ) :
    Generic.Language LimitReplayPoint :=
  replayTwoLanguage 0 (replayPositiveEncoding S)

theorem replayPositiveEncoding_avoids_zero (S : Set ℕ) :
    replayPositiveEncoding S ⊆ {z : ℤ | z ≠ 0} := by
  rintro z ⟨n, _hn, rfl⟩
  have hn : (0 : ℤ) ≤ (n : ℤ) :=
    Int.ofNat_zero_le n
  have hpos : (0 : ℤ) < (n : ℤ) + 1 := by
    omega
  exact ne_of_gt hpos

theorem replayEncodedLanguage_mem (S : Set ℕ) :
    replayEncodedLanguage S ∈ replayLimitHardClass := by
  exact replayTwoLanguage_mem 0 (replayPositiveEncoding S)
    (by simpa using replayPositiveEncoding_avoids_zero S)

@[simp] theorem positiveProbe_mem_replayEncodedLanguage
    (S : Set ℕ) (n : ℕ) :
    Sum.inl ((n : ℤ) + 1) ∈ replayEncodedLanguage S ↔
      n ∈ S := by
  constructor
  · intro h
    change
      (n : ℤ) + 1 < 0 ∨
        (n : ℤ) + 1 ∈ replayPositiveEncoding S at h
    rcases h with hneg | ⟨k, hk, heq⟩
    · omega
    · have hkn : k = n := by
        exact Int.ofNat_inj.mp (by omega)
      simpa [hkn] using hk
  · intro hn
    exact Or.inr ⟨n, hn, rfl⟩

theorem replayEncodedLanguage_injective :
    Function.Injective replayEncodedLanguage := by
  classical
  intro S T hST
  apply Set.ext
  intro n
  have hprobe :=
    Set.ext_iff.mp hST (Sum.inl ((n : ℤ) + 1))
  simpa using hprobe

/-- The class in Theorem 6.6 is genuinely uncountable, not merely presented
without an enumeration. -/
theorem replayLimitHardClass_uncountable :
    ¬replayLimitHardClass.Countable := by
  intro hcountable
  let f : Set ℕ → replayLimitHardClass :=
    fun S => ⟨replayEncodedLanguage S,
      replayEncodedLanguage_mem S⟩
  have hf : Function.Injective f := by
    intro S T hST
    apply replayEncodedLanguage_injective
    exact congrArg Subtype.val hST
  letI : Countable replayLimitHardClass :=
    hcountable.to_subtype
  have hpower : Countable (Set ℕ) := hf.countable
  exact
    GenLimit.UnionClosedness.powerSet_not_countable ℕ hpower

/-! ## Lemma 6.7: ordinary generation in the limit -/

def limitReplayMarkerRank : LimitReplayPoint → ℕ
  | .inl _ => 0
  | .inr n => n + 1

def limitReplayMagnitude : LimitReplayPoint → ℕ
  | .inl z => z.natAbs
  | .inr _ => 0

noncomputable def historyMarkerBound
    {t : ℕ} (xs : Fin t → LimitReplayPoint) : ℕ :=
  Finset.sup Finset.univ (fun i => limitReplayMarkerRank (xs i))

noncomputable def historyMagnitude
    {t : ℕ} (xs : Fin t → LimitReplayPoint) : ℕ :=
  Finset.sup Finset.univ (fun i => limitReplayMagnitude (xs i))

theorem markerRank_le_historyMarkerBound
    {t : ℕ} (xs : Fin t → LimitReplayPoint) (i : Fin t) :
    limitReplayMarkerRank (xs i) ≤ historyMarkerBound xs := by
  exact
    Finset.le_sup
      (s := (Finset.univ : Finset (Fin t)))
      (f := fun i => limitReplayMarkerRank (xs i))
      (Finset.mem_univ i)

theorem magnitude_le_historyMagnitude
    {t : ℕ} (xs : Fin t → LimitReplayPoint) (i : Fin t) :
    limitReplayMagnitude (xs i) ≤ historyMagnitude xs := by
  exact
    Finset.le_sup
      (s := (Finset.univ : Finset (Fin t)))
      (f := fun i => limitReplayMagnitude (xs i))
      (Finset.mem_univ i)

theorem historyMarkerBound_le
    {t b : ℕ} {xs : Fin t → LimitReplayPoint}
    (hmarkers :
      ∀ i n, xs i = Sum.inr n → n < b) :
    historyMarkerBound xs ≤ b := by
  apply Finset.sup_le
  intro i _hi
  cases hxi : xs i with
  | inl z =>
      simp [limitReplayMarkerRank]
  | inr n =>
      simp only [limitReplayMarkerRank]
      exact Nat.succ_le_iff.mpr
        (hmarkers i n hxi)

theorem historyMarkerBound_eq
    {t b : ℕ} {xs : Fin t → LimitReplayPoint}
    (hmarkers :
      ∀ i n, xs i = Sum.inr n → n < b)
    (hlast :
      b = 0 ∨ ∃ i : Fin t, xs i = Sum.inr (b - 1)) :
    historyMarkerBound xs = b := by
  apply Nat.le_antisymm
  · exact historyMarkerBound_le hmarkers
  · rcases hlast with rfl | ⟨i, hi⟩
    · simp
    · have hbound :=
        markerRank_le_historyMarkerBound xs i
      rw [hi] at hbound
      simp only [limitReplayMarkerRank] at hbound
      omega

noncomputable def historyFreshAbove
    (b : ℕ) {t : ℕ} (xs : Fin t → LimitReplayPoint) : ℤ :=
  (b + historyMagnitude xs + 1 : ℕ)

noncomputable def historyFreshBelow
    (b : ℕ) {t : ℕ} (xs : Fin t → LimitReplayPoint) : ℤ :=
  -((b + historyMagnitude xs + 1 : ℕ) : ℤ)

theorem integer_lt_historyFreshAbove
    (b : ℕ) {t : ℕ} {xs : Fin t → LimitReplayPoint}
    {i : Fin t} {z : ℤ} (hi : xs i = Sum.inl z) :
    z < historyFreshAbove b xs := by
  have habs :=
    magnitude_le_historyMagnitude xs i
  rw [hi] at habs
  simp only [limitReplayMagnitude] at habs
  have hzabs : z ≤ (z.natAbs : ℤ) :=
    Int.le_natAbs
  have hcast :
      (z.natAbs : ℤ) ≤
        (historyMagnitude xs : ℤ) := by
    exact_mod_cast habs
  have hnat :
      historyMagnitude xs <
        b + historyMagnitude xs + 1 := by
    omega
  have hstrict :
      (historyMagnitude xs : ℤ) <
        ((b + historyMagnitude xs + 1 : ℕ) : ℤ) := by
    exact_mod_cast hnat
  exact lt_of_le_of_lt (hzabs.trans hcast) hstrict

theorem base_lt_historyFreshAbove
    (b : ℕ) {t : ℕ} (xs : Fin t → LimitReplayPoint) :
    (b : ℤ) < historyFreshAbove b xs := by
  have hnat :
      b < b + historyMagnitude xs + 1 := by
    omega
  change
    (b : ℤ) <
      ((b + historyMagnitude xs + 1 : ℕ) : ℤ)
  exact_mod_cast hnat

theorem historyFreshBelow_lt_integer
    (b : ℕ) {t : ℕ} {xs : Fin t → LimitReplayPoint}
    {i : Fin t} {z : ℤ} (hi : xs i = Sum.inl z) :
    historyFreshBelow b xs < z := by
  have habs :=
    magnitude_le_historyMagnitude xs i
  rw [hi] at habs
  simp only [limitReplayMagnitude] at habs
  have hnegabs : -((z.natAbs : ℕ) : ℤ) ≤ z := by
    have h :=
      Int.le_natAbs (a := -z)
    rw [Int.natAbs_neg] at h
    omega
  have hcast :
      (z.natAbs : ℤ) ≤
        (historyMagnitude xs : ℤ) := by
    exact_mod_cast habs
  have hnat :
      historyMagnitude xs <
        b + historyMagnitude xs + 1 := by
    omega
  have hstrict :
      -(((b + historyMagnitude xs + 1 : ℕ) : ℤ)) <
        -(historyMagnitude xs : ℤ) := by
    have hcastStrict :
        (historyMagnitude xs : ℤ) <
          ((b + historyMagnitude xs + 1 : ℕ) : ℤ) := by
      exact_mod_cast hnat
    omega
  have hleft :
      -(historyMagnitude xs : ℤ) ≤ z := by
    omega
  exact hstrict.trans_le hleft

theorem historyFreshBelow_lt_base
    (b : ℕ) {t : ℕ} (xs : Fin t → LimitReplayPoint) :
    historyFreshBelow b xs < (b : ℤ) := by
  have hnegative :
      historyFreshBelow b xs < 0 := by
    simp only [historyFreshBelow]
    have hpos :
        0 < b + historyMagnitude xs + 1 := by
      omega
    have hcast :
        (0 : ℤ) <
          ((b + historyMagnitude xs + 1 : ℕ) : ℤ) := by
      exact_mod_cast hpos
    omega
  exact hnegative.trans_le (Int.ofNat_zero_le b)

/-- Lemma 6.7's generator.  Marker-only histories advance past the largest
seen marker.  Once an integer is present, the recovered marker bound chooses
the rightward (`H̃₁`) or leftward (`H̃₂`) integer branch. -/
noncomputable def replayOrdinaryGenerator :
    Generic.Generator LimitReplayPoint := by
  classical
  intro t xs
  if hall : ∀ i : Fin t, ∃ n, xs i = Sum.inr n then
    exact Sum.inr (historyMarkerBound xs)
  else
    let b := historyMarkerBound xs
    if hseen : ∃ i : Fin t, xs i = Sum.inl (b : ℤ) then
      exact Sum.inl (historyFreshAbove b xs)
    else
      exact Sum.inl (historyFreshBelow b xs)

def replayMarkerPrefix (b : ℕ) : Finset LimitReplayPoint :=
  (Finset.range b).image Sum.inr

theorem mem_replayMarkerPrefix_iff
    {b : ℕ} {x : LimitReplayPoint} :
    x ∈ replayMarkerPrefix b ↔
      ∃ n, n < b ∧ x = Sum.inr n := by
  classical
  simp only [replayMarkerPrefix, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro ⟨n, hn, hnx⟩
    exact ⟨n, hn, hnx.symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩

theorem replayMarkerPrefix_subset_one
    (b : ℕ) (A : Set ℤ) (j : ℤ) :
    (↑(replayMarkerPrefix b) : Set LimitReplayPoint) ⊆
      replayOneLanguage b A j := by
  intro x hx
  obtain ⟨n, hn, rfl⟩ :=
    mem_replayMarkerPrefix_iff.mp hx
  exact hn

theorem replayMarkerPrefix_subset_two
    (b : ℕ) (A : Set ℤ) :
    (↑(replayMarkerPrefix b) : Set LimitReplayPoint) ⊆
      replayTwoLanguage b A := by
  intro x hx
  obtain ⟨n, hn, rfl⟩ :=
    mem_replayMarkerPrefix_iff.mp hx
  exact hn

theorem replayOrdinaryGenerator_correct_allMarker
    (stream : Generic.Stream LimitReplayPoint)
    (hstream :
      Generic.Presents stream allMarkerLanguage) :
    ∀ t, Generic.CorrectAt replayOrdinaryGenerator
      allMarkerLanguage stream t := by
  intro t
  have hstreamIn :
      Generic.StreamIn stream allMarkerLanguage :=
    Generic.streamIn_of_presents hstream
  have hall :
      ∀ i : Fin t, ∃ n, stream i = Sum.inr n := by
    intro i
    have hi := hstreamIn ⟨i, rfl⟩
    cases hvalue : stream i with
    | inl z =>
        rw [hvalue] at hi
        exact False.elim hi
    | inr n =>
        exact ⟨n, rfl⟩
  have hout :
      Generic.output replayOrdinaryGenerator stream t =
        Sum.inr
          (historyMarkerBound (fun i : Fin t => stream i)) := by
    simp [Generic.output, replayOrdinaryGenerator, hall]
  constructor
  · rw [hout]
    trivial
  · intro hseen
    obtain ⟨s, hs, heq⟩ :=
      Generic.mem_sample_iff.mp hseen
    have hrank :=
      markerRank_le_historyMarkerBound
        (fun i : Fin t => stream i) ⟨s, hs⟩
    have hvalue :
        stream s =
          Sum.inr
            (historyMarkerBound
              (fun i : Fin t => stream i)) := by
      exact heq.trans hout
    rw [hvalue] at hrank
    simp only [limitReplayMarkerRank] at hrank
    omega

theorem replayOrdinaryGenerator_correct_one
    (b : ℕ) (A : Set ℤ) (j : ℤ)
    (stream : Generic.Stream LimitReplayPoint)
    (hstream :
      Generic.Presents stream (replayOneLanguage b A j)) :
    ∃ T, ∀ t, T ≤ t →
      Generic.CorrectAt replayOrdinaryGenerator
        (replayOneLanguage b A j) stream t := by
  classical
  let required : Finset LimitReplayPoint :=
    insert (Sum.inl (b : ℤ))
      (insert (Sum.inl (j + 1)) (replayMarkerPrefix b))
  have hrequired :
      (↑required : Set LimitReplayPoint) ⊆
        replayOneLanguage b A j := by
    intro x hx
    change
      x ∈ insert (Sum.inl (b : ℤ))
        (insert (Sum.inl (j + 1))
          (replayMarkerPrefix b)) at hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (by omega))
    · exact replayMarkerPrefix_subset_one b A j hx
  obtain ⟨T, hrequiredT⟩ :=
    Generic.finset_eventually_subset_sample
      hstream required hrequired
  refine ⟨T, ?_⟩
  intro t hTt
  have hrequiredNow :
      required ⊆ Generic.sample stream t :=
    fun _ hx =>
      Generic.sample_mono hTt (hrequiredT hx)
  have hbSample :
      Sum.inl (b : ℤ) ∈ Generic.sample stream t :=
    hrequiredNow (by simp [required])
  have hjSample :
      Sum.inl (j + 1) ∈ Generic.sample stream t :=
    hrequiredNow (by simp [required])
  have hmarkersSample :
      replayMarkerPrefix b ⊆ Generic.sample stream t := by
    intro x hx
    exact hrequiredNow (by simp [required, hx])
  have hstreamIn :
      Generic.StreamIn stream (replayOneLanguage b A j) :=
    Generic.streamIn_of_presents hstream
  have hmarkers :
      ∀ i n, stream (i : Fin t) = Sum.inr n → n < b := by
    intro i n hi
    have hmem := hstreamIn ⟨i, rfl⟩
    simpa [hi, replayOneLanguage] using hmem
  have hlast :
      b = 0 ∨
        ∃ i : Fin t, stream i = Sum.inr (b - 1) := by
    by_cases hb0 : b = 0
    · exact Or.inl hb0
    · right
      have hprefix :
          Sum.inr (b - 1) ∈ replayMarkerPrefix b := by
        apply mem_replayMarkerPrefix_iff.mpr
        exact ⟨b - 1, by omega, rfl⟩
      obtain ⟨s, hs, heq⟩ :=
        Generic.mem_sample_iff.mp
          (hmarkersSample hprefix)
      exact ⟨⟨s, hs⟩, heq⟩
  have hbound :
      historyMarkerBound
          (fun i : Fin t => stream i) = b :=
    historyMarkerBound_eq hmarkers hlast
  obtain ⟨ib, hib, hibValue⟩ :=
    Generic.mem_sample_iff.mp hbSample
  have hnotAll :
      ¬(∀ i : Fin t, ∃ n, stream i = Sum.inr n) := by
    intro hall
    obtain ⟨n, hn⟩ := hall ⟨ib, hib⟩
    rw [hibValue] at hn
    cases hn
  have hseen :
      ∃ i : Fin t,
        stream i =
          Sum.inl
            (historyMarkerBound
              (fun i : Fin t => stream i) : ℤ) := by
    refine ⟨⟨ib, hib⟩, ?_⟩
    simpa [hbound] using hibValue
  have hseenB :
      ∃ i : Fin t, stream i = Sum.inl (b : ℤ) :=
    ⟨⟨ib, hib⟩, hibValue⟩
  have hout :
      Generic.output replayOrdinaryGenerator stream t =
        Sum.inl
          (historyFreshAbove b
            (fun i : Fin t => stream i)) := by
    simp [Generic.output, replayOrdinaryGenerator,
      hnotAll, hseenB, hbound]
  rw [Generic.CorrectAt, hout]
  constructor
  · exact Or.inr (Or.inr (by
      obtain ⟨ij, hij, hijValue⟩ :=
        Generic.mem_sample_iff.mp hjSample
      have hlt :=
        integer_lt_historyFreshAbove b
          (xs := fun i : Fin t => stream i)
          (i := ⟨ij, hij⟩) hijValue
      omega))
  · intro hfreshSeen
    obtain ⟨i, hi, hiValue⟩ :=
      Generic.mem_sample_iff.mp hfreshSeen
    cases hvalue : stream i with
    | inl z =>
        have hlt :=
          integer_lt_historyFreshAbove b
            (xs := fun i : Fin t => stream i)
            (i := ⟨i, hi⟩) hvalue
        rw [hvalue] at hiValue
        exact (ne_of_lt hlt) (Sum.inl.inj hiValue)
    | inr n =>
        rw [hvalue] at hiValue
        cases hiValue

theorem replayOrdinaryGenerator_correct_two
    (b : ℕ) (A : Set ℤ)
    (hA : A ⊆ {z : ℤ | z ≠ (b : ℤ)})
    (stream : Generic.Stream LimitReplayPoint)
    (hstream :
      Generic.Presents stream (replayTwoLanguage b A)) :
    ∃ T, ∀ t, T ≤ t →
      Generic.CorrectAt replayOrdinaryGenerator
        (replayTwoLanguage b A) stream t := by
  classical
  let seed : ℤ := (b : ℤ) - 1
  let required : Finset LimitReplayPoint :=
    insert (Sum.inl seed) (replayMarkerPrefix b)
  have hrequired :
      (↑required : Set LimitReplayPoint) ⊆
        replayTwoLanguage b A := by
    intro x hx
    change
      x ∈ insert (Sum.inl seed)
        (replayMarkerPrefix b) at hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact Or.inl (by
        dsimp only [seed]
        omega)
    · exact replayMarkerPrefix_subset_two b A hx
  obtain ⟨T, hrequiredT⟩ :=
    Generic.finset_eventually_subset_sample
      hstream required hrequired
  refine ⟨T, ?_⟩
  intro t hTt
  have hrequiredNow :
      required ⊆ Generic.sample stream t :=
    fun _ hx =>
      Generic.sample_mono hTt (hrequiredT hx)
  have hseedSample :
      Sum.inl seed ∈ Generic.sample stream t :=
    hrequiredNow (by simp [required])
  have hmarkersSample :
      replayMarkerPrefix b ⊆ Generic.sample stream t := by
    intro x hx
    exact hrequiredNow (by simp [required, hx])
  have hstreamIn :
      Generic.StreamIn stream (replayTwoLanguage b A) :=
    Generic.streamIn_of_presents hstream
  have hmarkers :
      ∀ i n, stream (i : Fin t) = Sum.inr n → n < b := by
    intro i n hi
    have hmem := hstreamIn ⟨i, rfl⟩
    simpa [hi, replayTwoLanguage] using hmem
  have hlast :
      b = 0 ∨
        ∃ i : Fin t, stream i = Sum.inr (b - 1) := by
    by_cases hb0 : b = 0
    · exact Or.inl hb0
    · right
      have hprefix :
          Sum.inr (b - 1) ∈ replayMarkerPrefix b := by
        apply mem_replayMarkerPrefix_iff.mpr
        exact ⟨b - 1, by omega, rfl⟩
      obtain ⟨s, hs, heq⟩ :=
        Generic.mem_sample_iff.mp
          (hmarkersSample hprefix)
      exact ⟨⟨s, hs⟩, heq⟩
  have hbound :
      historyMarkerBound
          (fun i : Fin t => stream i) = b :=
    historyMarkerBound_eq hmarkers hlast
  obtain ⟨iseed, hiseed, hseedValue⟩ :=
    Generic.mem_sample_iff.mp hseedSample
  have hnotAll :
      ¬(∀ i : Fin t, ∃ n, stream i = Sum.inr n) := by
    intro hall
    obtain ⟨n, hn⟩ := hall ⟨iseed, hiseed⟩
    rw [hseedValue] at hn
    cases hn
  have hnotSeen :
      ¬∃ i : Fin t,
        stream i =
          Sum.inl
            (historyMarkerBound
              (fun i : Fin t => stream i) : ℤ) := by
    rintro ⟨i, hi⟩
    have hmem := hstreamIn ⟨i, rfl⟩
    rw [hi, hbound] at hmem
    change (b : ℤ) < (b : ℤ) ∨ (b : ℤ) ∈ A at hmem
    rcases hmem with hbad | hmemA
    · omega
    · exact (hA hmemA) rfl
  have hnotSeenB :
      ¬∃ i : Fin t, stream i = Sum.inl (b : ℤ) := by
    rintro ⟨i, hi⟩
    apply hnotSeen
    refine ⟨i, ?_⟩
    simpa [hbound] using hi
  have hout :
      Generic.output replayOrdinaryGenerator stream t =
        Sum.inl
          (historyFreshBelow b
            (fun i : Fin t => stream i)) := by
    simp [Generic.output, replayOrdinaryGenerator,
      hnotAll, hnotSeenB, hbound]
  rw [Generic.CorrectAt, hout]
  constructor
  · exact Or.inl
      (historyFreshBelow_lt_base b
        (fun i : Fin t => stream i))
  · intro hfreshSeen
    obtain ⟨i, hi, hiValue⟩ :=
      Generic.mem_sample_iff.mp hfreshSeen
    cases hvalue : stream i with
    | inl z =>
        have hlt :=
          historyFreshBelow_lt_integer b
            (xs := fun i : Fin t => stream i)
            (i := ⟨i, hi⟩) hvalue
        rw [hvalue] at hiValue
        exact (ne_of_lt hlt) (Sum.inl.inj hiValue).symm
    | inr n =>
        rw [hvalue] at hiValue
        cases hiValue

/-- Lemma 6.7: the literal uncountable class is generatable in the ordinary
in-the-limit model. -/
theorem lemma_6_7 :
    GeneratableInLimit replayLimitHardClass := by
  refine ⟨replayOrdinaryGenerator, ?_⟩
  intro L hL stream hstream
  change
    L ∈ ({allMarkerLanguage} :
      Set (Generic.Language LimitReplayPoint)) ∪
      ⋃ b : ℕ, (replayOneClass b ∪ replayTwoClass b)
      at hL
  rcases hL with hmarker | hindexed
  · have hL' : L = allMarkerLanguage := by
      simpa using hmarker
    rw [hL'] at hstream ⊢
    exact
      ⟨0, fun t _ht =>
        replayOrdinaryGenerator_correct_allMarker
          stream hstream t⟩
  · obtain ⟨b, hL⟩ := Set.mem_iUnion.mp hindexed
    rcases hL with
      ⟨A, j, _hbj, rfl⟩ | ⟨A, hA, rfl⟩
    · exact replayOrdinaryGenerator_correct_one
        b A j stream hstream
    · exact replayOrdinaryGenerator_correct_two
        b A hA stream hstream

/-! ## Lemma 6.8: the one-replayed-marker phase construction -/

/-- The canonical all-marker stream used in the first step of Lemma 6.8. -/
def canonicalMarkerStream : Generic.Stream LimitReplayPoint :=
  fun n => Sum.inr n

theorem canonicalMarkerStream_replayEnumeration
    (gen : Generic.Generator LimitReplayPoint) :
    IsReplayEnumeration gen allMarkerLanguage
      canonicalMarkerStream := by
  constructor
  · intro n
    exact Or.inl trivial
  · intro x hx
    cases x with
    | inl z => exact False.elim hx
    | inr n => exact ⟨n, rfl⟩

/-- The displayed marker prefix through the replayed marker:
`∗¹, ..., ∗^(q+1)` in the paper's notation. -/
def replayMarkerPrelude (q : ℕ) :
    List LimitReplayPoint :=
  (List.range (q + 1)).map Sum.inr

@[simp] theorem replayMarkerPrelude_length (q : ℕ) :
    (replayMarkerPrelude q).length = q + 1 := by
  simp [replayMarkerPrelude]

@[simp] theorem replayMarkerPrelude_get
    (q : ℕ) (i : Fin (q + 1)) :
    (replayMarkerPrelude q).get
        ⟨i.val, by
          rw [replayMarkerPrelude_length]
          exact i.isLt⟩ =
      Sum.inr i.val := by
  rw [List.get_eq_getElem]
  simp [replayMarkerPrelude]

theorem mem_replayMarkerPrelude_iff
    {q n : ℕ} :
    Sum.inr n ∈ replayMarkerPrelude q ↔ n ≤ q := by
  simpa [replayMarkerPrelude] using
    (Nat.lt_succ_iff : n < q + 1 ↔ n ≤ q)

/-- The integer placed at the beginning of phase `phase`.  With the paper
marker exponent `q+1`, this is `(q+1) - (phase+1) = q - phase` in `ℤ`. -/
def replayPhaseSeed (q phase : ℕ) : ℤ :=
  (q : ℤ) - (phase : ℤ)

def replayPhaseAuxiliarySet
    (history : List LimitReplayPoint) (seed : ℤ) :
    Set ℤ :=
  {z | Sum.inl z ∈ history ∨ z = seed}

/-- The provisional `H̃₁^q` target used to force one phase to terminate. -/
def replayPhaseTarget
    (q : ℕ) (history : List LimitReplayPoint)
    (seed cutoff : ℤ) :
    Generic.Language LimitReplayPoint :=
  replayOneLanguage q
    (replayPhaseAuxiliarySet history seed) cutoff

/-- A finite history followed by the increasing integer tail
`cutoff+1, cutoff+2, ...`. -/
def historyThenReplayUpperTail
    (history : List LimitReplayPoint) (cutoff : ℤ) :
    Generic.Stream LimitReplayPoint :=
  fun n =>
    if h : n < history.length then
      history.get ⟨n, h⟩
    else
      Sum.inl (cutoff + (n - history.length : ℕ) + 1)

@[simp] theorem historyThenReplayUpperTail_prefix
    (history : List LimitReplayPoint) (cutoff : ℤ)
    {n : ℕ} (hn : n < history.length) :
    historyThenReplayUpperTail history cutoff n =
      history.get ⟨n, hn⟩ := by
  simp [historyThenReplayUpperTail, hn]

@[simp] theorem historyThenReplayUpperTail_tail
    (history : List LimitReplayPoint) (cutoff : ℤ)
    (k : ℕ) :
    historyThenReplayUpperTail history cutoff
        (history.length + k) =
      Sum.inl (cutoff + (k : ℤ) + 1) := by
  simp [historyThenReplayUpperTail]

def replayUpperIntegerList
    (cutoff : ℤ) (extra : ℕ) : List ℤ :=
  List.ofFn
    (fun k : Fin extra =>
      cutoff + (k.val : ℤ) + 1)

def replayUpperTailList
    (cutoff : ℤ) (extra : ℕ) :
    List LimitReplayPoint :=
  (replayUpperIntegerList cutoff extra).map Sum.inl

def replayPhaseExtension
    (history : List LimitReplayPoint)
    (seed cutoff : ℤ) (extra : ℕ) :
    List LimitReplayPoint :=
  history ++ [Sum.inl seed] ++
    replayUpperTailList cutoff extra

@[simp] theorem replayUpperTailList_length
    (cutoff : ℤ) (extra : ℕ) :
    (replayUpperTailList cutoff extra).length = extra := by
  simp [replayUpperTailList, replayUpperIntegerList]

@[simp] theorem replayPhaseExtension_length
    (history : List LimitReplayPoint)
    (seed cutoff : ℤ) (extra : ℕ) :
    (replayPhaseExtension history seed cutoff extra).length =
      history.length + 1 + extra := by
  simp [replayPhaseExtension, Nat.add_assoc]
  omega

theorem replayPhaseExtension_prefix
    (history : List LimitReplayPoint)
    (seed cutoff : ℤ) (extra : ℕ) :
    history <+:
      replayPhaseExtension history seed cutoff extra := by
  simp [replayPhaseExtension, List.append_assoc]

/-- The phase extension is exactly the corresponding prefix of the
provisional increasing-tail stream. -/
theorem replayPhaseExtension_get
    (history : List LimitReplayPoint)
    (seed cutoff : ℤ) (extra : ℕ)
    (i : Fin (history.length + 1 + extra)) :
    (replayPhaseExtension history seed cutoff extra).get
        ⟨i, by
          rw [replayPhaseExtension_length]
          exact i.isLt⟩ =
      historyThenReplayUpperTail
        (history ++ [Sum.inl seed]) cutoff i := by
  rw [List.get_eq_getElem]
  by_cases hi : i.val < history.length
  · have hibase :
        i.val < (history ++ [Sum.inl seed]).length := by
      simp
      omega
    rw [historyThenReplayUpperTail_prefix
      (history ++ [Sum.inl seed]) cutoff hibase]
    rw [List.get_eq_getElem]
    simp only [replayPhaseExtension]
    rw [List.getElem_append_left hibase]
  · by_cases hieq : i.val = history.length
    · have hibase :
          i.val < (history ++ [Sum.inl seed]).length := by
        simp
        omega
      rw [historyThenReplayUpperTail_prefix
        (history ++ [Sum.inl seed]) cutoff hibase]
      rw [List.get_eq_getElem]
      simp only [replayPhaseExtension]
      rw [List.getElem_append_left
        (show i.val < (history ++ [Sum.inl seed]).length by
          simp [hieq])]
    · have hilower : history.length + 1 ≤ i.val := by
        omega
      let k := i.val - (history.length + 1)
      have hik : i.val = history.length + 1 + k := by
        dsimp only [k]
        omega
      have hkextra : k < extra := by
        dsimp only [k]
        omega
      have hitail :
          ¬i.val <
            (history ++ [Sum.inl seed]).length := by
        simp
        omega
      rw [historyThenReplayUpperTail]
      simp only [hitail, dite_false]
      simp only [replayPhaseExtension]
      rw [List.getElem_append_right
        (show
          (history ++ [Sum.inl seed]).length ≤ i.val by
          simp
          omega)]
      simp only [List.length_append, List.length_singleton]
      have hoffset :
          i.val - (history.length + 1) < extra := by
        simpa only [k] using hkextra
      have hoffsetList :
          i.val - (history.length + 1) <
            (replayUpperTailList cutoff extra).length := by
        simpa using hoffset
      change
        (replayUpperTailList cutoff extra)[
            i.val - (history.length + 1)]'hoffsetList =
          Sum.inl
            (cutoff +
              (i.val - (history.length + 1) : ℕ) + 1)
      simp [replayUpperTailList,
        replayUpperIntegerList]

/-- Finite data after `phase` completed adversarial phases. -/
structure ReplayLimitPhaseState (q phase : ℕ) where
  history : List LimitReplayPoint
  integerHistory : List ℤ
  history_shape :
    history =
      replayMarkerPrelude q ++ integerHistory.map Sum.inl
  cutoff : ℤ
  cutoff_lower : (q : ℤ) + 1 ≤ cutoff
  forbidden : Finset ℤ
  forbidden_above :
    ∀ z, z ∈ forbidden → (q : ℤ) + 1 < z
  forbidden_le_cutoff :
    ∀ z, z ∈ forbidden → z ≤ cutoff
  forbidden_avoided :
    ∀ z, z ∈ forbidden → Sum.inl z ∉ history
  base_avoided :
    Sum.inl ((q : ℤ) + 1) ∉ history
  phase_seeds :
    ∀ k, k < phase →
      Sum.inl (replayPhaseSeed q k) ∈ history

def initialReplayLimitPhaseState (q : ℕ) :
    ReplayLimitPhaseState q 0 where
  history := replayMarkerPrelude q
  integerHistory := []
  history_shape := by simp
  cutoff := (q : ℤ) + 1
  cutoff_lower := le_rfl
  forbidden := ∅
  forbidden_above := by simp
  forbidden_le_cutoff := by simp
  forbidden_avoided := by simp
  base_avoided := by
    intro h
    simp [replayMarkerPrelude] at h
  phase_seeds := by simp

theorem replayLimitPhaseState_history_length
    {q phase : ℕ} (state : ReplayLimitPhaseState q phase) :
    q + 1 ≤ state.history.length := by
  rw [state.history_shape]
  simp

theorem replayLimitPhaseState_marker_get
    {q phase : ℕ} (state : ReplayLimitPhaseState q phase)
    {i n : ℕ} (hi : i < state.history.length)
    (hvalue : state.history.get ⟨i, hi⟩ = Sum.inr n) :
    i = n ∧ n ≤ q := by
  have hiShape :
      i <
        (replayMarkerPrelude q ++
          state.integerHistory.map Sum.inl).length := by
    simpa [← state.history_shape] using hi
  have hvalueShape :
      (replayMarkerPrelude q ++
        state.integerHistory.map Sum.inl)[i] =
          Sum.inr n := by
    have hget :
        state.history[i] = Sum.inr n := by
      simpa [List.get_eq_getElem] using hvalue
    simpa [state.history_shape] using hget
  by_cases hiprelude : i < (replayMarkerPrelude q).length
  · have hget :
        (replayMarkerPrelude q)[i] =
          Sum.inr n := by
      simpa [List.getElem_append_left hiprelude] using
        hvalueShape
    have hget' :
        (Sum.inr i : LimitReplayPoint) = Sum.inr n := by
      simpa [replayMarkerPrelude] using hget
    have hin : i = n := Sum.inr.inj hget'
    have hiq : i ≤ q := by
      simpa only [replayMarkerPrelude_length,
        Nat.lt_succ_iff] using hiprelude
    exact
      ⟨hin, hin ▸ hiq⟩
  · have hsuffix := hvalueShape
    rw [List.getElem_append_right
      (show
        (replayMarkerPrelude q).length ≤ i by
        omega)] at hsuffix
    simp only [List.getElem_map] at hsuffix
    cases hsuffix

theorem replayLimitPhaseState_marker_mem
    {q phase : ℕ} (state : ReplayLimitPhaseState q phase)
    {n : ℕ} (hn : n ≤ q) :
    Sum.inr n ∈ state.history := by
  rw [state.history_shape]
  apply List.mem_append_left
  exact mem_replayMarkerPrelude_iff.mpr hn

theorem replayLimitPhaseState_get_marker
    {q phase : ℕ} (state : ReplayLimitPhaseState q phase)
    {i : ℕ} (hi : i ≤ q) :
    state.history.get
        ⟨i, by
          have hlen :=
            replayLimitPhaseState_history_length state
          omega⟩ =
      Sum.inr i := by
  have hoption :
      state.history[i]? =
        some (Sum.inr i) := by
    rw [state.history_shape]
    have hiprelude :
        i < (replayMarkerPrelude q).length := by
      simp
      omega
    rw [List.getElem?_append_left hiprelude]
    rw [List.getElem?_eq_getElem hiprelude]
    simp [replayMarkerPrelude]
  have hvalid : i < state.history.length := by
    have hlen :=
      replayLimitPhaseState_history_length state
    omega
  have hoption' := hoption
  rw [List.getElem?_eq_getElem hvalid] at hoption'
  have hgetElem :
      state.history[i] = Sum.inr i :=
    Option.some.inj hoption'
  rw [List.get_eq_getElem]
  exact hgetElem

theorem replayPhaseTarget_mem_class
    {q phase : ℕ} (state : ReplayLimitPhaseState q phase)
    (seed : ℤ) :
    replayPhaseTarget q state.history seed state.cutoff ∈
      replayLimitHardClass := by
  apply replayOneLanguage_mem
  have := state.cutoff_lower
  omega

theorem exists_upperTailIndex
    {cutoff z : ℤ} (hz : cutoff < z) :
    ∃ k : ℕ, z = cutoff + (k : ℤ) + 1 := by
  let k : ℕ := (z - cutoff - 1).toNat
  have hnonnegative :
      0 ≤ z - cutoff - 1 := by
    omega
  refine ⟨k, ?_⟩
  have hk :
      (k : ℤ) = z - cutoff - 1 := by
    dsimp only [k]
    rw [Int.toNat_of_nonneg hnonnegative]
  omega

theorem replayPhase_provisional_output_marker
    (gen : Generic.Generator LimitReplayPoint)
    {q phase tau : ℕ}
    (state : ReplayLimitPhaseState q phase)
    (seed : ℤ) (htauq : tau ≤ q) :
    Generic.output gen
        (historyThenReplayUpperTail
          (state.history ++ [Sum.inl seed]) state.cutoff)
        tau =
      Generic.output gen canonicalMarkerStream tau := by
  apply congrArg (gen tau)
  funext i
  have hiq : i.val ≤ q :=
    (Nat.le_of_lt i.isLt).trans htauq
  have hihistory :
      i.val < state.history.length := by
    have hlen :=
      replayLimitPhaseState_history_length state
    omega
  have hibase :
      i.val <
        (state.history ++ [Sum.inl seed]).length := by
    simp
    omega
  rw [historyThenReplayUpperTail_prefix
    (state.history ++ [Sum.inl seed])
      state.cutoff hibase]
  rw [List.get_eq_getElem]
  rw [List.getElem_append_left hihistory]
  change
    state.history.get ⟨i.val, hihistory⟩ =
      Sum.inr i.val
  exact replayLimitPhaseState_get_marker state hiq

/-- The provisional increasing-tail sequence for one phase is a genuine
enumeration with replay of its `H̃₁^q` target.  Its only possibly invalid
input is marker `q`, which is the output forced in the initial marker step. -/
theorem replayPhase_provisional_replayEnumeration
    (gen : Generic.Generator LimitReplayPoint)
    {q phase tau : ℕ}
    (state : ReplayLimitPhaseState q phase)
    (seed : ℤ)
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (hq :
      Sum.inl (q : ℤ) ∈ state.history ∨
        seed = (q : ℤ)) :
    IsReplayEnumeration gen
      (replayPhaseTarget q state.history seed state.cutoff)
      (historyThenReplayUpperTail
        (state.history ++ [Sum.inl seed]) state.cutoff) := by
  let base := state.history ++ [Sum.inl seed]
  let stream :=
    historyThenReplayUpperTail base state.cutoff
  change
    IsReplayEnumeration gen
      (replayPhaseTarget q state.history seed state.cutoff)
      stream
  have houtput :
      Generic.output gen stream tau = Sum.inr q := by
    exact
      (replayPhase_provisional_output_marker
        gen state seed htauq).trans hreplayed
  constructor
  · intro n
    by_cases hnbase : n < base.length
    · rw [show stream n = base.get ⟨n, hnbase⟩ by
        exact historyThenReplayUpperTail_prefix
          base state.cutoff hnbase]
      by_cases hnhistory : n < state.history.length
      · have hbaseGet :
            base.get ⟨n, hnbase⟩ =
              state.history.get ⟨n, hnhistory⟩ := by
          rw [List.get_eq_getElem, List.get_eq_getElem]
          exact List.getElem_append_left hnhistory
        rw [hbaseGet]
        cases hvalue :
            state.history.get ⟨n, hnhistory⟩ with
        | inl z =>
            left
            have hmem :=
              List.get_mem state.history
                ⟨n, hnhistory⟩
            rw [hvalue] at hmem
            exact Or.inr (Or.inl (Or.inl hmem))
        | inr m =>
            obtain ⟨hnm, hmq⟩ :=
              replayLimitPhaseState_marker_get
                state hnhistory hvalue
            subst m
            by_cases hnq : n < q
            · exact Or.inl hnq
            · have hnEq : n = q := by omega
              subst n
              right
              exact ⟨tau, htau, htauq, houtput⟩
      · have hnEq : n = state.history.length := by
          simp only [base, List.length_append,
            List.length_singleton] at hnbase
          omega
        subst n
        left
        have hget :
            base.get ⟨state.history.length, hnbase⟩ =
              Sum.inl seed := by
          simp [base]
        rw [hget]
        exact Or.inr (Or.inl (Or.inr rfl))
    · have htail :
          stream n =
            Sum.inl
              (state.cutoff +
                (n - base.length : ℕ) + 1) := by
        simp [stream, historyThenReplayUpperTail,
          hnbase]
      rw [htail]
      left
      exact Or.inr (Or.inr (by
        have hnonnegative :
            (0 : ℤ) ≤
              (n - base.length : ℕ) := by
          exact_mod_cast Nat.zero_le _
        omega))
  · intro x hx
    cases x with
    | inr n =>
        have hnq : n < q := by
          exact hx
        refine ⟨n, ?_⟩
        have hnhistory :
            n < state.history.length := by
          have hlen :=
            replayLimitPhaseState_history_length state
          omega
        have hnbase :
            n < base.length := by
          simp [base]
          omega
        rw [show stream n = base.get ⟨n, hnbase⟩ by
          exact historyThenReplayUpperTail_prefix
            base state.cutoff hnbase]
        rw [List.get_eq_getElem]
        rw [List.getElem_append_left hnhistory]
        change
          state.history.get ⟨n, hnhistory⟩ =
            Sum.inr n
        exact replayLimitPhaseState_get_marker state
          (Nat.le_of_lt hnq)
    | inl z =>
        change
          z = (q : ℤ) ∨
            z ∈ replayPhaseAuxiliarySet
              state.history seed ∨
            state.cutoff < z at hx
        rcases hx with hzq | haux | htail
        · rcases hq with hqHistory | hqSeed
          · rw [hzq]
            obtain ⟨i, hi⟩ :=
              List.mem_iff_get.mp hqHistory
            refine ⟨i, ?_⟩
            have hibase :
                i.val < base.length := by
              simp [base]
              omega
            rw [show stream i = base.get ⟨i, hibase⟩ by
              exact historyThenReplayUpperTail_prefix
                base state.cutoff hibase]
            rw [List.get_eq_getElem]
            rw [List.getElem_append_left i.isLt]
            exact hi
          · subst z
            refine ⟨state.history.length, ?_⟩
            have hibase :
                state.history.length < base.length := by
              simp [base]
            rw [show
              stream state.history.length =
                base.get
                  ⟨state.history.length, hibase⟩ by
              exact historyThenReplayUpperTail_prefix
                base state.cutoff hibase]
            simp [base, hqSeed]
        · rcases haux with hhistory | hseed
          · obtain ⟨i, hi⟩ :=
              List.mem_iff_get.mp hhistory
            refine ⟨i, ?_⟩
            have hibase :
                i.val < base.length := by
              simp [base]
              omega
            rw [show stream i = base.get ⟨i, hibase⟩ by
              exact historyThenReplayUpperTail_prefix
                base state.cutoff hibase]
            rw [List.get_eq_getElem]
            rw [List.getElem_append_left i.isLt]
            exact hi
          · subst z
            refine ⟨state.history.length, ?_⟩
            have hibase :
                state.history.length < base.length := by
              simp [base]
            rw [show
              stream state.history.length =
                base.get
                  ⟨state.history.length, hibase⟩ by
              exact historyThenReplayUpperTail_prefix
                base state.cutoff hibase]
            simp [base]
        · obtain ⟨k, hk⟩ :=
            exists_upperTailIndex htail
          refine ⟨base.length + k, ?_⟩
          have htailValue :=
            historyThenReplayUpperTail_tail
              base state.cutoff k
          change stream (base.length + k) =
            Sum.inl z
          rw [show stream =
            historyThenReplayUpperTail
              base state.cutoff from rfl]
          rw [htailValue]
          exact congrArg Sum.inl hk.symm

/-- The data produced by one terminating phase. -/
structure SuccessfulReplayLimitPhase
    (gen : Generic.Generator LimitReplayPoint)
    (q phase : ℕ)
    (state : ReplayLimitPhaseState q phase) where
  next : ReplayLimitPhaseState q (phase + 1)
  extends_history : state.history <+: next.history
  strict_growth : state.history.length < next.history.length
  forbidden_subset : state.forbidden ⊆ next.forbidden
  transitionTime : ℕ
  next_length : next.history.length = transitionTime
  base_length_le_transition :
    state.history.length + 1 ≤ transitionTime
  omittedOutput : ℤ
  cutoff_lt_omitted : state.cutoff < omittedOutput
  omitted_mem_next_forbidden :
    omittedOutput ∈ next.forbidden
  output_on_next :
    gen transitionTime
        (fun i =>
          next.history.get
            ⟨i, by
              rw [next_length]
              exact i.isLt⟩) =
      Sum.inl omittedOutput

private theorem exists_successfulReplayLimitPhase
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase : ℕ) (state : ReplayLimitPhaseState q phase) :
    Nonempty
      (SuccessfulReplayLimitPhase gen q phase state) := by
  classical
  let seed := replayPhaseSeed q phase
  let base := state.history ++ [Sum.inl seed]
  let stream :=
    historyThenReplayUpperTail base state.cutoff
  let target :=
    replayPhaseTarget q state.history seed state.cutoff
  have hq :
      Sum.inl (q : ℤ) ∈ state.history ∨
        seed = (q : ℤ) := by
    by_cases hphase : phase = 0
    · right
      simp [seed, replayPhaseSeed, hphase]
    · left
      exact state.phase_seeds 0
        (Nat.pos_of_ne_zero hphase)
  have htarget :
      target ∈ replayLimitHardClass := by
    exact replayPhaseTarget_mem_class state seed
  have hreplay :
      IsReplayEnumeration gen target stream := by
    exact replayPhase_provisional_replayEnumeration
      gen state seed htau htauq hreplayed hq
  obtain ⟨threshold, hcorrect⟩ :=
    hgen target htarget stream hreplay
  let transitionTime :=
    max threshold base.length
  have hthreshold :
      threshold ≤ transitionTime :=
    Nat.le_max_left _ _
  have hbaseTime :
      base.length ≤ transitionTime :=
    Nat.le_max_right _ _
  have hcorrectAt :
      Generic.CorrectAt gen target stream
        transitionTime :=
    hcorrect transitionTime hthreshold
  have hbaseSample :
      ∀ x, x ∈ base →
        x ∈ Generic.sample stream transitionTime := by
    intro x hx
    obtain ⟨i, hi⟩ :=
      List.mem_iff_get.mp hx
    apply Generic.mem_sample_iff.mpr
    refine ⟨i, lt_of_lt_of_le i.isLt hbaseTime, ?_⟩
    have hiprefix :
        i.val < base.length := i.isLt
    exact
      (historyThenReplayUpperTail_prefix
        base state.cutoff hiprefix).trans hi
  have hqBase : Sum.inl (q : ℤ) ∈ base := by
    rcases hq with hhistory | hseed
    · exact List.mem_append_left _ hhistory
    · exact List.mem_append_right _
        (by simp [hseed])
  obtain ⟨omitted, hcutoffOmitted, houtput⟩ :
      ∃ z : ℤ, state.cutoff < z ∧
        Generic.output gen stream transitionTime =
          Sum.inl z := by
    cases hout :
        Generic.output gen stream transitionTime with
    | inl z =>
        refine ⟨z, ?_, rfl⟩
        have hmem := hcorrectAt.1
        rw [hout] at hmem
        change
          z = (q : ℤ) ∨
            (Sum.inl z ∈ state.history ∨ z = seed) ∨
            state.cutoff < z at hmem
        rcases hmem with hzq | haux | htail
        · exfalso
          apply hcorrectAt.2
          rw [hout, hzq]
          exact hbaseSample _ hqBase
        · exfalso
          apply hcorrectAt.2
          rw [hout]
          apply hbaseSample
          rcases haux with hhistory | hseed
          · exact List.mem_append_left _ hhistory
          · exact List.mem_append_right _
              (by simp [hseed])
        · exact htail
    | inr n =>
        have hmem := hcorrectAt.1
        rw [hout] at hmem
        have hnq : n < q := by
          exact hmem
        exfalso
        apply hcorrectAt.2
        rw [hout]
        apply hbaseSample
        exact List.mem_append_left _
          (replayLimitPhaseState_marker_mem state
            (Nat.le_of_lt hnq))
  let extra := transitionTime - base.length
  have htime :
      base.length + extra = transitionTime := by
    dsimp only [extra]
    omega
  let nextHistory :=
    replayPhaseExtension state.history seed
      state.cutoff extra
  let nextIntegers :=
    state.integerHistory ++ [seed] ++
      replayUpperIntegerList state.cutoff extra
  have hnextLength :
      nextHistory.length = transitionTime := by
    dsimp only [nextHistory]
    rw [replayPhaseExtension_length]
    have hbaseLength :
        base.length = state.history.length + 1 := by
      simp [base]
    omega
  have hnextShape :
      nextHistory =
        replayMarkerPrelude q ++
          nextIntegers.map Sum.inl := by
    simp only [nextHistory, nextIntegers,
      replayPhaseExtension, replayUpperTailList,
      List.map_append, List.map_singleton]
    rw [state.history_shape]
    simp only [List.append_assoc]
  have hseedBelow :
      seed < (q : ℤ) + 1 := by
    dsimp only [seed, replayPhaseSeed]
    have hphaseNonnegative :
        (0 : ℤ) ≤ (phase : ℤ) :=
      Int.ofNat_zero_le phase
    omega
  have hnextSample :
      ∀ x, x ∈ nextHistory →
        x ∈ Generic.sample stream transitionTime := by
    intro x hx
    change
      x ∈
        state.history ++ [Sum.inl seed] ++
          replayUpperTailList state.cutoff extra
      at hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with (hhistory | hseed) | htail
    · exact hbaseSample x
        (List.mem_append_left _ hhistory)
    · exact hbaseSample x
        (List.mem_append_right _ (by simpa using hseed))
    · rw [replayUpperTailList] at htail
      obtain ⟨w, hw, hwx⟩ :=
        List.mem_map.mp htail
      rw [replayUpperIntegerList] at hw
      obtain ⟨k, hk⟩ := List.mem_ofFn.mp hw
      apply Generic.mem_sample_iff.mpr
      refine ⟨base.length + k.val, ?_, ?_⟩
      · have hkextra : k.val < extra := k.isLt
        have hbaseExtra :
            base.length + extra = transitionTime :=
          htime
        omega
      · have htailValue :=
          historyThenReplayUpperTail_tail
            base state.cutoff k.val
        change stream (base.length + k.val) = x
        rw [show stream =
          historyThenReplayUpperTail
            base state.cutoff from rfl]
        rw [htailValue]
        have hkw :
            state.cutoff + (k.val : ℤ) + 1 = w := by
          exact hk
        rw [hkw, hwx]
  have hnextOldForbidden :
      ∀ z, z ∈ state.forbidden →
        Sum.inl z ∉ nextHistory := by
    intro z hz hmem
    change
      Sum.inl z ∈
        state.history ++ [Sum.inl seed] ++
          replayUpperTailList state.cutoff extra
      at hmem
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with (hhistory | hseed) | htail
    · exact state.forbidden_avoided z hz hhistory
    · have hzs : z = seed :=
        Sum.inl.inj hseed
      have habove := state.forbidden_above z hz
      omega
    · rw [replayUpperTailList] at htail
      obtain ⟨w, hw, hwz⟩ :=
        List.mem_map.mp htail
      rw [replayUpperIntegerList] at hw
      obtain ⟨k, hk⟩ := List.mem_ofFn.mp hw
      have hwEq :
          state.cutoff + (k.val : ℤ) + 1 = w :=
        hk
      have hwzEq : w = z :=
        Sum.inl.inj hwz
      have hle := state.forbidden_le_cutoff _ hz
      omega
  have hnextBaseAvoided :
      Sum.inl ((q : ℤ) + 1) ∉ nextHistory := by
    intro hmem
    change
      Sum.inl ((q : ℤ) + 1) ∈
        state.history ++ [Sum.inl seed] ++
          replayUpperTailList state.cutoff extra
      at hmem
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with (hhistory | hseed) | htail
    · exact state.base_avoided hhistory
    · have hseedEq :
          (q : ℤ) + 1 = seed :=
        Sum.inl.inj hseed
      omega
    · rw [replayUpperTailList] at htail
      obtain ⟨w, hw, hwq⟩ :=
        List.mem_map.mp htail
      rw [replayUpperIntegerList] at hw
      obtain ⟨k, hk⟩ := List.mem_ofFn.mp hw
      have hwEq :
          state.cutoff + (k.val : ℤ) + 1 = w :=
        hk
      have hwqEq :
          w = (q : ℤ) + 1 :=
        Sum.inl.inj hwq
      have hcut := state.cutoff_lower
      omega
  have homittedNotNext :
      Sum.inl omitted ∉ nextHistory := by
    intro hmem
    apply hcorrectAt.2
    rw [houtput]
    exact hnextSample _ hmem
  have hnextSeeds :
      ∀ k, k < phase + 1 →
        Sum.inl (replayPhaseSeed q k) ∈
          nextHistory := by
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hkold | rfl
    · exact List.IsPrefix.mem
        (state.phase_seeds k hkold)
        (replayPhaseExtension_prefix state.history seed
          state.cutoff extra)
    · change Sum.inl seed ∈ nextHistory
      simp [nextHistory, replayPhaseExtension]
  let next :
      ReplayLimitPhaseState q (phase + 1) := {
    history := nextHistory
    integerHistory := nextIntegers
    history_shape := hnextShape
    cutoff := omitted
    cutoff_lower := by
      exact state.cutoff_lower.trans
        (Int.le_of_lt hcutoffOmitted)
    forbidden := insert omitted state.forbidden
    forbidden_above := by
      intro z hz
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact state.cutoff_lower.trans_lt hcutoffOmitted
      · exact state.forbidden_above z hz
    forbidden_le_cutoff := by
      intro z hz
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact le_rfl
      · exact
          (state.forbidden_le_cutoff z hz).trans
            (Int.le_of_lt hcutoffOmitted)
    forbidden_avoided := by
      intro z hz
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact homittedNotNext
      · exact hnextOldForbidden z hz
    base_avoided := hnextBaseAvoided
    phase_seeds := hnextSeeds
  }
  refine ⟨{
    next := next
    extends_history :=
      replayPhaseExtension_prefix state.history seed
        state.cutoff extra
    strict_growth := by
      have hbase :
          state.history.length + 1 ≤
            transitionTime := by
        simpa [base] using hbaseTime
      simpa [next, hnextLength] using
        (lt_of_lt_of_le
          (Nat.lt_succ_self state.history.length)
          hbase)
    forbidden_subset := by
      intro z hz
      exact Finset.mem_insert_of_mem hz
    transitionTime := transitionTime
    next_length := hnextLength
    base_length_le_transition := by
      simpa [base] using hbaseTime
    omittedOutput := omitted
    cutoff_lt_omitted := hcutoffOmitted
    omitted_mem_next_forbidden :=
      Finset.mem_insert_self _ _
    output_on_next := by
      rw [← houtput]
      apply congrArg (gen transitionTime)
      funext i
      change
        nextHistory.get
            ⟨i.val, by
              rw [hnextLength]
              exact i.isLt⟩ =
          stream i.val
      simpa [nextHistory, stream, base] using
        (replayPhaseExtension_get state.history seed
          state.cutoff extra
          ⟨i.val, by
            have hiNext : i.val < nextHistory.length := by
              rw [hnextLength]
              exact i.isLt
            simpa [nextHistory] using hiNext⟩)
  }⟩

/-! ### Iteration and the limiting replay presentation -/

private noncomputable def replayLimitPhase
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase : ℕ) (state : ReplayLimitPhaseState q phase) :
    SuccessfulReplayLimitPhase gen q phase state :=
  Classical.choice
    (exists_successfulReplayLimitPhase gen hgen
      htau htauq hreplayed phase state)

private noncomputable def replayLimitPhaseState
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q) :
    (phase : ℕ) → ReplayLimitPhaseState q phase
  | 0 => initialReplayLimitPhaseState q
  | phase + 1 =>
      (replayLimitPhase gen hgen htau htauq hreplayed
        phase
        (replayLimitPhaseState gen hgen
          htau htauq hreplayed phase)).next

private theorem replayLimitPhaseState_prefix_succ
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase : ℕ) :
    (replayLimitPhaseState gen hgen
        htau htauq hreplayed phase).history <+:
      (replayLimitPhaseState gen hgen
        htau htauq hreplayed (phase + 1)).history := by
  rw [replayLimitPhaseState]
  exact
    (replayLimitPhase gen hgen htau htauq hreplayed
      phase
      (replayLimitPhaseState gen hgen
        htau htauq hreplayed phase)).extends_history

private theorem replayLimitPhaseState_prefix
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    {n m : ℕ} (hnm : n ≤ m) :
    (replayLimitPhaseState gen hgen
        htau htauq hreplayed n).history <+:
      (replayLimitPhaseState gen hgen
        htau htauq hreplayed m).history := by
  induction m, hnm using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih =>
      exact ih.trans
        (replayLimitPhaseState_prefix_succ gen hgen
          htau htauq hreplayed m)

private theorem replayLimitPhaseState_length
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase : ℕ) :
    q + 1 + phase ≤
      (replayLimitPhaseState gen hgen
        htau htauq hreplayed phase).history.length := by
  induction phase with
  | zero =>
      simp [replayLimitPhaseState,
        initialReplayLimitPhaseState]
  | succ phase ih =>
      have hgrowth :=
        (replayLimitPhase gen hgen htau htauq hreplayed
          phase
          (replayLimitPhaseState gen hgen
            htau htauq hreplayed phase)).strict_growth
      rw [replayLimitPhaseState]
      omega

private theorem replayLimitPhaseState_forbidden_succ
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase : ℕ) :
    (replayLimitPhaseState gen hgen
        htau htauq hreplayed phase).forbidden ⊆
      (replayLimitPhaseState gen hgen
        htau htauq hreplayed (phase + 1)).forbidden := by
  rw [replayLimitPhaseState]
  exact
    (replayLimitPhase gen hgen htau htauq hreplayed
      phase
      (replayLimitPhaseState gen hgen
        htau htauq hreplayed phase)).forbidden_subset

private theorem replayLimitPhaseState_forbidden_mono
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    {n m : ℕ} (hnm : n ≤ m) :
    (replayLimitPhaseState gen hgen
        htau htauq hreplayed n).forbidden ⊆
      (replayLimitPhaseState gen hgen
        htau htauq hreplayed m).forbidden := by
  induction m, hnm using Nat.le_induction with
  | base => exact fun _ hz => hz
  | succ m _ ih =>
      exact fun z hz =>
        replayLimitPhaseState_forbidden_succ gen hgen
          htau htauq hreplayed m (ih hz)

/-- The time at which phase `phase` records the generator's next omitted
integer. -/
noncomputable def replayLimitTransitionTime
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase : ℕ) : ℕ :=
  (replayLimitPhase gen hgen htau htauq hreplayed
    phase
    (replayLimitPhaseState gen hgen
      htau htauq hreplayed phase)).transitionTime

/-- The integer output at the transition of phase `phase`, permanently
omitted from all later histories. -/
noncomputable def replayLimitOmittedOutput
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase : ℕ) : ℤ :=
  (replayLimitPhase gen hgen htau htauq hreplayed
    phase
    (replayLimitPhaseState gen hgen
      htau htauq hreplayed phase)).omittedOutput

theorem replayLimitTransitionTime_eq_next_length
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase : ℕ) :
    (replayLimitPhaseState gen hgen
        htau htauq hreplayed (phase + 1)).history.length =
      replayLimitTransitionTime gen hgen
        htau htauq hreplayed phase := by
  rw [replayLimitPhaseState]
  exact
    (replayLimitPhase gen hgen htau htauq hreplayed
      phase
      (replayLimitPhaseState gen hgen
        htau htauq hreplayed phase)).next_length

theorem replayLimitTransitionTime_phase_lower
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase : ℕ) :
    q + 2 + phase ≤
      replayLimitTransitionTime gen hgen
        htau htauq hreplayed phase := by
  have hlength :=
    replayLimitPhaseState_length gen hgen
      htau htauq hreplayed phase
  have hbase :=
    (replayLimitPhase gen hgen htau htauq hreplayed
      phase
      (replayLimitPhaseState gen hgen
        htau htauq hreplayed phase)).base_length_le_transition
  change
    q + 2 + phase ≤
      (replayLimitPhase gen hgen htau htauq hreplayed
        phase
        (replayLimitPhaseState gen hgen
          htau htauq hreplayed phase)).transitionTime
  omega

theorem replayLimitOmittedOutput_mem_next_forbidden
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase : ℕ) :
    replayLimitOmittedOutput gen hgen
        htau htauq hreplayed phase ∈
      (replayLimitPhaseState gen hgen
        htau htauq hreplayed (phase + 1)).forbidden := by
  rw [replayLimitPhaseState]
  exact
    (replayLimitPhase gen hgen htau htauq hreplayed
      phase
      (replayLimitPhaseState gen hgen
        htau htauq hreplayed phase)).omitted_mem_next_forbidden

theorem replayLimitOutput_on_next
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase : ℕ) :
    gen
        (replayLimitTransitionTime gen hgen
          htau htauq hreplayed phase)
        (fun i =>
          (replayLimitPhaseState gen hgen
            htau htauq hreplayed (phase + 1)).history.get
            ⟨i, by
              rw [replayLimitTransitionTime_eq_next_length
                gen hgen htau htauq hreplayed phase]
              exact i.isLt⟩) =
      Sum.inl
        (replayLimitOmittedOutput gen hgen
          htau htauq hreplayed phase) := by
  simpa only [replayLimitTransitionTime,
    replayLimitOmittedOutput, replayLimitPhaseState] using
      (replayLimitPhase gen hgen htau htauq hreplayed
        phase
        (replayLimitPhaseState gen hgen
          htau htauq hreplayed phase)).output_on_next

/-- The infinite presentation obtained as the limit of the nested completed
phase histories. -/
noncomputable def replayLimitAdversarialStream
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q) :
    Generic.Stream LimitReplayPoint :=
  fun k =>
    (replayLimitPhaseState gen hgen
      htau htauq hreplayed (k + 1)).history.get
      ⟨k, by
        have hlen :=
          replayLimitPhaseState_length gen hgen
            htau htauq hreplayed (k + 1)
        omega⟩

private theorem replayLimitAdversarialStream_eq_state_get
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase k : ℕ)
    (hk :
      k <
        (replayLimitPhaseState gen hgen
          htau htauq hreplayed phase).history.length) :
    replayLimitAdversarialStream gen hgen
        htau htauq hreplayed k =
      (replayLimitPhaseState gen hgen
        htau htauq hreplayed phase).history.get
        ⟨k, hk⟩ := by
  rw [replayLimitAdversarialStream]
  have hkShort :
      k <
        (replayLimitPhaseState gen hgen
          htau htauq hreplayed (k + 1)).history.length := by
    have hlen :=
      replayLimitPhaseState_length gen hgen
        htau htauq hreplayed (k + 1)
    omega
  rw [List.get_eq_getElem, List.get_eq_getElem]
  rcases le_total (k + 1) phase with hle | hge
  · exact
      (replayLimitPhaseState_prefix gen hgen
        htau htauq hreplayed hle).getElem hkShort
  · exact
      ((replayLimitPhaseState_prefix gen hgen
        htau htauq hreplayed hge).getElem hk).symm

private theorem replayLimitPhaseHistory_subset_limitRange
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase : ℕ) :
    (↑(replayLimitPhaseState gen hgen
        htau htauq hreplayed phase).history.toFinset :
        Set LimitReplayPoint) ⊆
      Set.range
        (replayLimitAdversarialStream gen hgen
          htau htauq hreplayed) := by
  intro x hx
  change
    x ∈ (replayLimitPhaseState gen hgen
      htau htauq hreplayed phase).history.toFinset at hx
  rw [List.mem_toFinset] at hx
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
  refine ⟨i, ?_⟩
  exact
    (replayLimitAdversarialStream_eq_state_get
      gen hgen htau htauq hreplayed
      phase i i.isLt).trans hi

private theorem replayLimitPhaseForbidden_disjoint_limitRange
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase : ℕ) :
    Disjoint
      (↑(replayLimitPhaseState gen hgen
        htau htauq hreplayed phase).forbidden : Set ℤ)
      {z : ℤ |
        Sum.inl z ∈
          Set.range
            (replayLimitAdversarialStream gen hgen
              htau htauq hreplayed)} := by
  rw [Set.disjoint_left]
  rintro z hzForbidden ⟨k, hk⟩
  let later := max phase (k + 1)
  have hphaseLater : phase ≤ later :=
    Nat.le_max_left _ _
  have hkLater : k + 1 ≤ later :=
    Nat.le_max_right _ _
  have hzForbiddenLater :
      z ∈ (replayLimitPhaseState gen hgen
        htau htauq hreplayed later).forbidden :=
    replayLimitPhaseState_forbidden_mono gen hgen
      htau htauq hreplayed hphaseLater hzForbidden
  have hkLength :
      k <
        (replayLimitPhaseState gen hgen
          htau htauq hreplayed later).history.length := by
    have hlen :=
      replayLimitPhaseState_length gen hgen
        htau htauq hreplayed later
    omega
  have hget :
      (replayLimitPhaseState gen hgen
        htau htauq hreplayed later).history.get
          ⟨k, hkLength⟩ =
        Sum.inl z := by
    exact
      (replayLimitAdversarialStream_eq_state_get
        gen hgen htau htauq hreplayed
        later k hkLength).symm.trans hk
  have hzHistory :
      Sum.inl z ∈
        (replayLimitPhaseState gen hgen
          htau htauq hreplayed later).history := by
    rw [← hget]
    exact
      List.get_mem
        (replayLimitPhaseState gen hgen
          htau htauq hreplayed later).history
        ⟨k, hkLength⟩
  exact
    (replayLimitPhaseState gen hgen
      htau htauq hreplayed later).forbidden_avoided
        z hzForbiddenLater hzHistory

theorem replayLimitOmittedOutput_omitted_forever
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase : ℕ) :
    Sum.inl
        (replayLimitOmittedOutput gen hgen
          htau htauq hreplayed phase) ∉
      Set.range
        (replayLimitAdversarialStream gen hgen
          htau htauq hreplayed) := by
  exact
    Set.disjoint_left.mp
      (replayLimitPhaseForbidden_disjoint_limitRange
        gen hgen htau htauq hreplayed (phase + 1))
      (replayLimitOmittedOutput_mem_next_forbidden
        gen hgen htau htauq hreplayed phase)

theorem replayPhaseSeed_mem_limitRange
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase : ℕ) :
    Sum.inl (replayPhaseSeed q phase) ∈
      Set.range
        (replayLimitAdversarialStream gen hgen
          htau htauq hreplayed) := by
  apply replayLimitPhaseHistory_subset_limitRange
    gen hgen htau htauq hreplayed (phase + 1)
  change
    Sum.inl (replayPhaseSeed q phase) ∈
      (replayLimitPhaseState gen hgen
        htau htauq hreplayed (phase + 1)).history.toFinset
  rw [List.mem_toFinset]
  exact
    (replayLimitPhaseState gen hgen
      htau htauq hreplayed (phase + 1)).phase_seeds
        phase (Nat.lt_succ_self phase)

private theorem replayLowerInteger_mem_limitRange
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    {z : ℤ} (hz : z < (q : ℤ) + 1) :
    Sum.inl z ∈
      Set.range
        (replayLimitAdversarialStream gen hgen
          htau htauq hreplayed) := by
  let phase : ℕ := ((q : ℤ) - z).toNat
  have hnonnegative :
      0 ≤ (q : ℤ) - z := by
    omega
  have hphase :
      (phase : ℤ) = (q : ℤ) - z := by
    dsimp only [phase]
    rw [Int.toNat_of_nonneg hnonnegative]
  have hseed :
      replayPhaseSeed q phase = z := by
    simp only [replayPhaseSeed]
    omega
  rw [← hseed]
  exact replayPhaseSeed_mem_limitRange
    gen hgen htau htauq hreplayed phase

theorem replayLimitBase_not_mem_limitRange
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q) :
    Sum.inl ((q : ℤ) + 1) ∉
      Set.range
        (replayLimitAdversarialStream gen hgen
          htau htauq hreplayed) := by
  rintro ⟨k, hk⟩
  have hkLength :
      k <
        (replayLimitPhaseState gen hgen
          htau htauq hreplayed (k + 1)).history.length := by
    have hlen :=
      replayLimitPhaseState_length gen hgen
        htau htauq hreplayed (k + 1)
    omega
  have hget :
      (replayLimitPhaseState gen hgen
        htau htauq hreplayed (k + 1)).history.get
          ⟨k, hkLength⟩ =
        Sum.inl ((q : ℤ) + 1) := by
    exact
      (replayLimitAdversarialStream_eq_state_get
        gen hgen htau htauq hreplayed
        (k + 1) k hkLength).symm.trans hk
  apply
    (replayLimitPhaseState gen hgen
      htau htauq hreplayed (k + 1)).base_avoided
  rw [← hget]
  exact
    List.get_mem
      (replayLimitPhaseState gen hgen
        htau htauq hreplayed (k + 1)).history
      ⟨k, hkLength⟩

theorem replayLimitMarker_mem_limitRange_iff
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (n : ℕ) :
    Sum.inr n ∈
        Set.range
          (replayLimitAdversarialStream gen hgen
            htau htauq hreplayed) ↔
      n ≤ q := by
  constructor
  · rintro ⟨k, hk⟩
    have hkLength :
        k <
          (replayLimitPhaseState gen hgen
            htau htauq hreplayed (k + 1)).history.length := by
      have hlen :=
        replayLimitPhaseState_length gen hgen
          htau htauq hreplayed (k + 1)
      omega
    have hget :
        (replayLimitPhaseState gen hgen
          htau htauq hreplayed (k + 1)).history.get
            ⟨k, hkLength⟩ =
          Sum.inr n := by
      exact
        (replayLimitAdversarialStream_eq_state_get
          gen hgen htau htauq hreplayed
          (k + 1) k hkLength).symm.trans hk
    exact
      (replayLimitPhaseState_marker_get
        (replayLimitPhaseState gen hgen
          htau htauq hreplayed (k + 1))
        hkLength hget).2
  · intro hn
    apply replayLimitPhaseHistory_subset_limitRange
      gen hgen htau htauq hreplayed 0
    change
      Sum.inr n ∈
        (replayLimitPhaseState gen hgen
          htau htauq hreplayed 0).history.toFinset
    rw [List.mem_toFinset]
    exact
      replayLimitPhaseState_marker_mem
        (replayLimitPhaseState gen hgen
          htau htauq hreplayed 0) hn

/-- The set of integer points that survive the limiting construction. -/
noncomputable def replayLimitAdversarialIntegerSet
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q) : Set ℤ :=
  {z |
    Sum.inl z ∈
      Set.range
        (replayLimitAdversarialStream gen hgen
          htau htauq hreplayed)}

/-- The final `H̃₂^(q+1)` language diagonalized against the proposed replay
generator. -/
noncomputable def replayLimitAdversarialTarget
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q) :
    Generic.Language LimitReplayPoint :=
  Set.range
    (replayLimitAdversarialStream gen hgen
      htau htauq hreplayed)

theorem replayLimitAdversarialIntegerSet_avoids_base
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q) :
    replayLimitAdversarialIntegerSet gen hgen
        htau htauq hreplayed ⊆
      {z : ℤ | z ≠ ((q + 1 : ℕ) : ℤ)} := by
  intro z hz
  change
    Sum.inl z ∈
      Set.range
        (replayLimitAdversarialStream gen hgen
          htau htauq hreplayed) at hz
  intro hzbase
  have hzbase' : z = (q : ℤ) + 1 := by
    simpa using hzbase
  rw [hzbase'] at hz
  exact replayLimitBase_not_mem_limitRange
    gen hgen htau htauq hreplayed hz

theorem replayLimitAdversarialTarget_eq_two
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q) :
    replayLimitAdversarialTarget gen hgen
        htau htauq hreplayed =
      replayTwoLanguage (q + 1)
        (replayLimitAdversarialIntegerSet gen hgen
          htau htauq hreplayed) := by
  ext x
  cases x with
  | inl z =>
      change
        Sum.inl z ∈
            Set.range
              (replayLimitAdversarialStream gen hgen
                htau htauq hreplayed) ↔
          z < ((q + 1 : ℕ) : ℤ) ∨
            z ∈
              replayLimitAdversarialIntegerSet gen hgen
                htau htauq hreplayed
      constructor
      · exact Or.inr
      · rintro (hz | hz)
        · have hz' : z < (q : ℤ) + 1 := by
            simpa using hz
          exact replayLowerInteger_mem_limitRange
            gen hgen htau htauq hreplayed hz'
        · exact hz
  | inr n =>
      change
        Sum.inr n ∈
            Set.range
              (replayLimitAdversarialStream gen hgen
                htau htauq hreplayed) ↔
          n < q + 1
      simpa only [Nat.lt_succ_iff] using
        (replayLimitMarker_mem_limitRange_iff
          gen hgen htau htauq hreplayed n)

theorem replayLimitAdversarialTarget_mem_class
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q) :
    replayLimitAdversarialTarget gen hgen
        htau htauq hreplayed ∈
      replayLimitHardClass := by
  rw [replayLimitAdversarialTarget_eq_two
    gen hgen htau htauq hreplayed]
  exact replayTwoLanguage_mem (q + 1)
    (replayLimitAdversarialIntegerSet gen hgen
      htau htauq hreplayed)
    (replayLimitAdversarialIntegerSet_avoids_base
      gen hgen htau htauq hreplayed)

theorem replayLimitAdversarialStream_replayEnumeration
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q) :
    IsReplayEnumeration gen
      (replayLimitAdversarialTarget gen hgen
        htau htauq hreplayed)
      (replayLimitAdversarialStream gen hgen
        htau htauq hreplayed) := by
  constructor
  · intro n
    left
    exact ⟨n, rfl⟩
  · intro x hx
    exact hx

theorem replayLimitOutput_on_limitStream
    (gen : Generic.Generator LimitReplayPoint)
    (hgen :
      IsLimitReplayGenerator gen replayLimitHardClass)
    {q tau : ℕ}
    (htau : 0 < tau) (htauq : tau ≤ q)
    (hreplayed :
      Generic.output gen canonicalMarkerStream tau =
        Sum.inr q)
    (phase : ℕ) :
    Generic.output gen
        (replayLimitAdversarialStream gen hgen
          htau htauq hreplayed)
        (replayLimitTransitionTime gen hgen
          htau htauq hreplayed phase) =
      Sum.inl
        (replayLimitOmittedOutput gen hgen
          htau htauq hreplayed phase) := by
  rw [Generic.output]
  rw [← replayLimitOutput_on_next
    gen hgen htau htauq hreplayed phase]
  apply congrArg
    (gen
      (replayLimitTransitionTime gen hgen
        htau htauq hreplayed phase))
  funext i
  apply replayLimitAdversarialStream_eq_state_get
    gen hgen htau htauq hreplayed (phase + 1)

/-- Lemma 6.8: no single generator succeeds in the limit on every
enumeration with replay of the literal hard class. -/
theorem lemma_6_8 :
    ¬GeneratableInLimitWithReplay replayLimitHardClass := by
  rintro ⟨gen, hgen⟩
  obtain ⟨threshold, hmarkerCorrect⟩ :=
    hgen allMarkerLanguage allMarkerLanguage_mem
      canonicalMarkerStream
      (canonicalMarkerStream_replayEnumeration gen)
  let tau := max threshold 1
  have htau : 0 < tau := by
    dsimp only [tau]
    omega
  have hthreshold : threshold ≤ tau := by
    exact Nat.le_max_left _ _
  have hcorrectAt :
      Generic.CorrectAt gen allMarkerLanguage
        canonicalMarkerStream tau :=
    hmarkerCorrect tau hthreshold
  cases hout :
      Generic.output gen canonicalMarkerStream tau with
  | inl z =>
      have hmem := hcorrectAt.1
      rw [hout] at hmem
      exact hmem
  | inr q =>
      have htauq : tau ≤ q := by
        by_contra hnot
        have hqtau : q < tau := Nat.lt_of_not_ge hnot
        apply hcorrectAt.2
        rw [hout]
        exact Generic.mem_sample_iff.mpr
          ⟨q, hqtau, rfl⟩
      have hreplayed :
          Generic.output gen canonicalMarkerStream tau =
            Sum.inr q :=
        hout
      let stream :=
        replayLimitAdversarialStream gen hgen
          htau htauq hreplayed
      let target :=
        replayLimitAdversarialTarget gen hgen
          htau htauq hreplayed
      have htarget :
          target ∈ replayLimitHardClass := by
        exact replayLimitAdversarialTarget_mem_class
          gen hgen htau htauq hreplayed
      have hstream :
          IsReplayEnumeration gen target stream := by
        exact replayLimitAdversarialStream_replayEnumeration
          gen hgen htau htauq hreplayed
      obtain ⟨finalThreshold, hfinalCorrect⟩ :=
        hgen target htarget stream hstream
      let phase := finalThreshold
      let transitionTime :=
        replayLimitTransitionTime gen hgen
          htau htauq hreplayed phase
      have hfinalThreshold :
          finalThreshold ≤ transitionTime := by
        have hlower :=
          replayLimitTransitionTime_phase_lower
            gen hgen htau htauq hreplayed phase
        dsimp only [phase, transitionTime] at hlower ⊢
        omega
      have hfinal :
          Generic.CorrectAt gen target stream
            transitionTime :=
        hfinalCorrect transitionTime hfinalThreshold
      have houtput :
          Generic.output gen stream transitionTime =
            Sum.inl
              (replayLimitOmittedOutput gen hgen
                htau htauq hreplayed phase) := by
        exact replayLimitOutput_on_limitStream
          gen hgen htau htauq hreplayed phase
      have homitted :
          Sum.inl
              (replayLimitOmittedOutput gen hgen
                htau htauq hreplayed phase) ∉
            target := by
        exact replayLimitOmittedOutput_omitted_forever
          gen hgen htau htauq hreplayed phase
      exact homitted (houtput ▸ hfinal.1)

/-- Theorem 6.6: an explicit uncountable UUS class that is generatable in
the ordinary limit model but not in the limit model with replay. -/
theorem theorem_6_6 :
    ¬replayLimitHardClass.Countable ∧
      UUS replayLimitHardClass ∧
      GeneratableInLimit replayLimitHardClass ∧
      ¬GeneratableInLimitWithReplay replayLimitHardClass :=
  ⟨replayLimitHardClass_uncountable,
    replayLimitHardClass_uus,
    lemma_6_7,
    lemma_6_8⟩

/-- Paper-shaped existential wrapper for Theorem 6.6. -/
theorem theorem_6_6_paper :
    ∃ H : Generic.LanguageClass LimitReplayPoint,
      ¬H.Countable ∧ UUS H ∧
        GeneratableInLimit H ∧
        ¬GeneratableInLimitWithReplay H :=
  ⟨replayLimitHardClass, theorem_6_6⟩

end Replay
end GenLimit
