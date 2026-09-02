import GenLimit.Paper17_InfiniteContamination.Definitions
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Bounded-displacement enumerations

Source: Mehrotra--Velegkas--Yu--Zhou,
*Language Generation with Infinite Contamination*,
arXiv:2511.07417v1, Definition 11, Proposition 7.4, and the finite
counting step in Lemma 7.5.

The source fixes one canonical ordering of the ambient domain and obtains the
canonical ordering of a language by deleting points outside that language.
Here `K : OrderedLanguage` supplies that ambient ordering.  Consequently,
`canonicalRank K L x` is the one-based rank of `x` in the ordering induced on
`L`, and is zero outside `L`, exactly as in Definition 11.

The theorems below prove the finite-prefix expansion inequality used in
Lemma 7.5, first for a positive natural displacement factor and then for an
arbitrary positive real factor via the exact ceiling prefix `⌈M n⌉`.
An explicit floor inverse fills the gaps between consecutive scaled
prefixes, proving that sampling at `⌈M n⌉` preserves both `liminf` and
`limsup`.  This completes both change-of-density inequalities of Lemma 7.5.
-/

namespace GenLimit.InfiniteContamination

open Filter
open GenLimit.KleinbergWei

/-! ## Definition 11: canonical rank and bounded displacement -/

/-- Zero-based position of a point in the fixed ambient canonical ordering.
Points outside the ambient carrier receive the harmless default value zero. -/
noncomputable def canonicalIndex (K : OrderedLanguage) (x : ℕ) : ℕ := by
  classical
  exact if hx : x ∈ K.carrier then
      Nat.find (by
        rw [← K.range_enumeration] at hx
        exact hx)
    else 0

theorem enumeration_canonicalIndex
    (K : OrderedLanguage) {x : ℕ} (hx : x ∈ K.carrier) :
    K.enumeration (canonicalIndex K x) = x := by
  rw [canonicalIndex, dif_pos hx]
  exact Nat.find_spec (by
    rw [← K.range_enumeration] at hx
    exact hx)

/-- Definition 11's rank `σ(x,L)`, using one-based ranks and rank zero outside
`L`.  When `L ⊆ K.carrier`, this is the rank in the canonical ordering of `L`
induced by deleting non-`L` elements from `K.enumeration`. -/
noncomputable def canonicalRank
    (K : OrderedLanguage) (L : Set ℕ) (x : ℕ) : ℕ := by
  classical
  exact if x ∈ L then K.prefixCount L (canonicalIndex K x + 1) else 0

@[simp] theorem canonicalRank_of_not_mem
    (K : OrderedLanguage) (L : Set ℕ) {x : ℕ} (hx : x ∉ L) :
    canonicalRank K L x = 0 := by
  simp [canonicalRank, hx]

theorem canonicalRank_carrier
    (K : OrderedLanguage) {x : ℕ} (hx : x ∈ K.carrier) :
    canonicalRank K K.carrier x = canonicalIndex K x + 1 := by
  simp [canonicalRank, hx]

/-- Monotonicity of finite prefix counts under language inclusion. -/
theorem canonicalPrefixCount_mono
    (K : OrderedLanguage) {A B : Set ℕ} (hAB : A ⊆ B) (n : ℕ) :
    K.prefixCount A n ≤ K.prefixCount B n := by
  classical
  unfold OrderedLanguage.prefixCount
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hi).1, hAB (Finset.mem_filter.mp hi).2⟩

/-- Deleting elements from a language can only decrease the induced
canonical rank of every point. -/
theorem canonicalRank_mono
    (K : OrderedLanguage) {A B : Set ℕ} (hAB : A ⊆ B) (x : ℕ) :
    canonicalRank K A x ≤ canonicalRank K B x := by
  by_cases hx : x ∈ A
  · rw [canonicalRank, if_pos hx, canonicalRank, if_pos (hAB hx)]
    exact canonicalPrefixCount_mono K hAB _
  · simp [canonicalRank, hx]

/-- Definition 11, with source time `n ≥ 1` represented by Lean time `n`
and hence the factor `n + 1`. -/
def BoundedDisplacement
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ)
    (L : Set ℕ) (M : ℝ) : Prop :=
  ∃ N, ∀ n, N ≤ n →
    (canonicalRank K L (stream n) : ℝ) ≤ M * (n + 1)

/-- Proposition 7.4: bounded displacement is closed under language subsets.

The shared ambient ordering is essential: the ordering of `L'` must be
obtained by deleting points from the ordering of `L`. -/
theorem proposition_7_4_boundedDisplacement_subset
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ)
    {L L' : Set ℕ} {M : ℝ}
    (hsub : L' ⊆ L)
    (hbounded : BoundedDisplacement K stream L M) :
    BoundedDisplacement K stream L' M := by
  obtain ⟨N, hN⟩ := hbounded
  refine ⟨N, fun n hn => ?_⟩
  calc
    (canonicalRank K L' (stream n) : ℝ)
        ≤ canonicalRank K L (stream n) := by
          exact_mod_cast canonicalRank_mono K hsub (stream n)
    _ ≤ M * (n + 1) := hN n hn

/-! ## The finite counting core of Lemma 7.5 -/

/-- Number of distinct elements of `L` appearing in the first `n` stream
positions.  This is the source quantity `|L ∩ {x₁, ..., xₙ}|`. -/
noncomputable def empiricalTargetCount
    (stream : GenLimit.Generic.Stream ℕ) (L : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact ((GenLimit.Generic.sample stream n).filter fun x => x ∈ L).card

/-- If every displayed point in a prefix has ambient canonical rank at most
`m`, then the distinct displayed target points fit inside the first `m`
canonical positions of the ambient language.

This is the finite set inclusion/cardinality argument at the heart of
Lemma 7.5.  Ranks are intentionally taken with respect to `K`, not merely
with respect to `L`: an `L`-rank bound alone does not imply containment in a
prefix of the canonical ordering of `K`. -/
theorem lemma_7_5_finite_prefix_core
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ)
    (L : Set ℕ) (hLK : L ⊆ K.carrier)
    (n m : ℕ)
    (hrank :
      ∀ i < n, canonicalRank K K.carrier (stream i) ≤ m) :
    empiricalTargetCount stream L n ≤ K.prefixCount L m := by
  classical
  unfold empiricalTargetCount OrderedLanguage.prefixCount
  apply Finset.card_le_card_of_injOn (canonicalIndex K)
  · intro x hx
    have hxSample : x ∈ GenLimit.Generic.sample stream n :=
      (Finset.mem_filter.mp hx).1
    have hxL : x ∈ L := (Finset.mem_filter.mp hx).2
    have hxK : x ∈ K.carrier := hLK hxL
    obtain ⟨i, hi, rfl⟩ :=
      GenLimit.Generic.mem_sample_iff.mp hxSample
    have hindex :
        canonicalIndex K (stream i) < m := by
      have hrank' := hrank i hi
      rw [canonicalRank_carrier K (hLK hxL)] at hrank'
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hindex,
        by simpa [enumeration_canonicalIndex K hxK] using hxL⟩
  · intro x hx y hy hxy
    have hxL : x ∈ L := (Finset.mem_filter.mp hx).2
    have hyL : y ∈ L := (Finset.mem_filter.mp hy).2
    have hxK : x ∈ K.carrier := hLK hxL
    have hyK : y ∈ K.carrier := hLK hyL
    calc
      x = K.enumeration (canonicalIndex K x) :=
        (enumeration_canonicalIndex K hxK).symm
      _ = K.enumeration (canonicalIndex K y) := by rw [hxy]
      _ = y := enumeration_canonicalIndex K hyK

/-- Lemma 7.5's eventual finite-prefix inequality for a positive natural
displacement factor.  It absorbs the finitely many pre-stabilization ranks
into a larger time threshold and then applies `lemma_7_5_finite_prefix_core`.

The source allows a real displacement factor.  This natural-factor theorem is
the exact discrete layer needed before ceilings and asymptotic density
transport enter. -/
theorem lemma_7_5_eventual_prefix_count_nat
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ)
    (L : Set ℕ) (hLK : L ⊆ K.carrier)
    (M : ℕ) (hM : 0 < M)
    (hbounded :
      BoundedDisplacement K stream K.carrier (M : ℝ)) :
    ∃ N, ∀ n, N ≤ n →
      empiricalTargetCount stream L n ≤ K.prefixCount L (M * n) := by
  obtain ⟨T, hT⟩ := hbounded
  let B : ℕ :=
    ∑ i ∈ Finset.range T, canonicalRank K K.carrier (stream i)
  refine ⟨max T B, fun n hn => ?_⟩
  apply lemma_7_5_finite_prefix_core K stream L hLK n (M * n)
  intro i hi
  by_cases hTi : T ≤ i
  · have hreal := hT i hTi
    have hnat :
        canonicalRank K K.carrier (stream i) ≤ M * (i + 1) := by
      exact_mod_cast hreal
    exact hnat.trans
      (Nat.mul_le_mul_left M (Nat.succ_le_iff.mpr hi))
  · have hiT : i < T := Nat.lt_of_not_ge hTi
    have hiB :
        canonicalRank K K.carrier (stream i) ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum
        (fun j hj => Nat.zero_le
          (canonicalRank K K.carrier (stream j)))
        (Finset.mem_range.mpr hiT)
    have hBn : B ≤ n := (le_max_right T B).trans hn
    have hnMn : n ≤ M * n := by
      have hOneM : 1 ≤ M := hM
      simpa using Nat.mul_le_mul_right n hOneM
    exact hiB.trans (hBn.trans hnMn)

/-! ## Arbitrary positive real displacement -/

/-- The real-scaled canonical prefix used in the statement of Lemma 7.5. -/
noncomputable def scaledPrefix (M : ℝ) (n : ℕ) : ℕ :=
  ⌈M * n⌉₊

/-- Lemma 7.5's finite-prefix inequality for an arbitrary positive real
displacement factor.  The ceiling is the exact integral prefix length needed
to contain every rank bounded by the real number `M * n`. -/
theorem lemma_7_5_eventual_prefix_count_real
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ)
    (L : Set ℕ) (hLK : L ⊆ K.carrier)
    (M : ℝ) (hM : 0 < M)
    (hbounded :
      BoundedDisplacement K stream K.carrier M) :
    ∃ N, ∀ n, N ≤ n →
      empiricalTargetCount stream L n ≤
        K.prefixCount L (scaledPrefix M n) := by
  obtain ⟨T, hT⟩ := hbounded
  let B : ℕ :=
    ∑ i ∈ Finset.range T, canonicalRank K K.carrier (stream i)
  let Nscale : ℕ := ⌈(B : ℝ) / M⌉₊
  refine ⟨max T Nscale, fun n hn => ?_⟩
  apply
    lemma_7_5_finite_prefix_core K stream L hLK n
      (scaledPrefix M n)
  intro i hi
  by_cases hTi : T ≤ i
  · have hreal := hT i hTi
    have htime : (i : ℝ) + 1 ≤ n := by
      exact_mod_cast Nat.succ_le_iff.mpr hi
    have hrank :
        (canonicalRank K K.carrier (stream i) : ℝ) ≤
          M * n :=
      hreal.trans
        (mul_le_mul_of_nonneg_left htime hM.le)
    have hceil :
        M * n ≤ (scaledPrefix M n : ℝ) := by
      exact Nat.le_ceil (M * n)
    exact_mod_cast hrank.trans hceil
  · have hiT : i < T := Nat.lt_of_not_ge hTi
    have hiB :
        canonicalRank K K.carrier (stream i) ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum
        (fun j hj => Nat.zero_le
          (canonicalRank K K.carrier (stream j)))
        (Finset.mem_range.mpr hiT)
    have hscale :
        (B : ℝ) ≤ M * Nscale := by
      have hdiv :
          (B : ℝ) / M ≤ (Nscale : ℝ) := by
        exact Nat.le_ceil ((B : ℝ) / M)
      simpa [mul_comm] using (div_le_iff₀ hM).mp hdiv
    have hNscale : Nscale ≤ n :=
      (Nat.le_max_right T Nscale).trans hn
    have htoN :
        M * Nscale ≤ M * n :=
      mul_le_mul_of_nonneg_left
        (by exact_mod_cast hNscale) hM.le
    have hceil :
        M * n ≤ (scaledPrefix M n : ℝ) := by
      exact Nat.le_ceil (M * n)
    have hBceil :
        (B : ℝ) ≤ (scaledPrefix M n : ℝ) :=
      hscale.trans (htoN.trans hceil)
    exact hiB.trans (by exact_mod_cast hBceil)

/-- The scaled prefixes tend to infinity for every positive displacement
factor. -/
theorem tendsto_scaledPrefix_atTop
    (M : ℝ) (hM : 0 < M) :
    Filter.Tendsto (scaledPrefix M) Filter.atTop Filter.atTop := by
  unfold scaledPrefix
  exact
    tendsto_nat_ceil_atTop.comp
      (Filter.Tendsto.const_mul_atTop hM
        tendsto_natCast_atTop_atTop)

/-- The ceiling factor in Lemma 7.5 converges to `M`. -/
theorem tendsto_scaledPrefix_div
    (M : ℝ) (hM : 0 ≤ M) :
    Filter.Tendsto
      (fun n : ℕ => (scaledPrefix M n : ℝ) / n)
      Filter.atTop (nhds M) := by
  simpa [scaledPrefix] using
    (tendsto_nat_ceil_mul_div_atTop (R := ℝ) hM).comp
      tendsto_natCast_atTop_atTop

/-! ## Gap filling between the scaled canonical prefixes -/

/-- The floor inverse of `scaledPrefix`.  For a canonical prefix length `k`,
`descaledPrefix M k` is the last source time whose real-scaled position is
at most `k`. -/
noncomputable def descaledPrefix (M : ℝ) (k : ℕ) : ℕ :=
  ⌊(k : ℝ) / M⌋₊

/-- The floor inverse tends to infinity for every positive scale. -/
theorem tendsto_descaledPrefix_atTop
    (M : ℝ) (hM : 0 < M) :
    Filter.Tendsto (descaledPrefix M) Filter.atTop Filter.atTop := by
  unfold descaledPrefix
  exact tendsto_nat_floor_atTop.comp
    (tendsto_natCast_atTop_atTop.atTop_div_const hM)

/-- The scaled floor inverse lies to the left of the original prefix. -/
theorem scaledPrefix_descaledPrefix_le
    (M : ℝ) (hM : 0 < M) (k : ℕ) :
    scaledPrefix M (descaledPrefix M k) ≤ k := by
  rw [scaledPrefix, Nat.ceil_le]
  have hfloor :
      (descaledPrefix M k : ℝ) ≤ (k : ℝ) / M := by
    exact Nat.floor_le (div_nonneg (Nat.cast_nonneg k) hM.le)
  calc
    M * (descaledPrefix M k : ℝ)
        = (descaledPrefix M k : ℝ) * M := by ring
    _ ≤ ((k : ℝ) / M) * M :=
      mul_le_mul_of_nonneg_right hfloor hM.le
    _ = k := by field_simp

/-- The next scaled prefix lies strictly to the right of the original
prefix. -/
theorem lt_scaledPrefix_descaledPrefix_succ
    (M : ℝ) (hM : 0 < M) (k : ℕ) :
    k < scaledPrefix M (descaledPrefix M k + 1) := by
  rw [scaledPrefix, Nat.lt_ceil]
  have hfloor :
      (k : ℝ) / M <
        (descaledPrefix M k : ℝ) + 1 := by
    exact Nat.lt_floor_add_one ((k : ℝ) / M)
  have hmul :
      (k : ℝ) <
        M * ((descaledPrefix M k : ℝ) + 1) := by
    calc
      (k : ℝ) = M * ((k : ℝ) / M) := by field_simp
      _ < M * ((descaledPrefix M k : ℝ) + 1) :=
        mul_lt_mul_of_pos_left hfloor hM
  simpa [Nat.cast_add, Nat.cast_one, mul_add] using hmul

/-- Consecutive scaled prefixes have a uniformly bounded additive gap. -/
theorem scaledPrefix_succ_le_add
    (M : ℝ) (n : ℕ) :
    scaledPrefix M (n + 1) ≤ scaledPrefix M n + ⌈M⌉₊ := by
  unfold scaledPrefix
  have hadd :
      M * (n + 1 : ℕ) = M * n + M := by
    push_cast
    ring
  rw [hadd]
  exact Nat.ceil_add_le (M * n) M

/-- Every canonical prefix lies within the fixed ceiling gap of the scaled
prefix immediately to its left. -/
theorem le_scaledPrefix_descaledPrefix_add
    (M : ℝ) (hM : 0 < M) (k : ℕ) :
    k ≤ scaledPrefix M (descaledPrefix M k) + ⌈M⌉₊ := by
  have hnext :=
    lt_scaledPrefix_descaledPrefix_succ M hM k
  have hgap :=
    scaledPrefix_succ_le_add M (descaledPrefix M k)
  omega

/-- The scaled prefix immediately to the right of `k` is at most the fixed
ceiling gap beyond `k`. -/
theorem scaledPrefix_descaledPrefix_succ_le_add
    (M : ℝ) (hM : 0 < M) (k : ℕ) :
    scaledPrefix M (descaledPrefix M k + 1) ≤ k + ⌈M⌉₊ := by
  exact
    (scaledPrefix_succ_le_add M (descaledPrefix M k)).trans
      (Nat.add_le_add_right
        (scaledPrefix_descaledPrefix_le M hM k) ⌈M⌉₊)

/-- Canonical prefix counts are monotone in the prefix length. -/
theorem canonicalPrefixCount_mono_index
    (K : OrderedLanguage) (L : Set ℕ) {a b : ℕ} (hab : a ≤ b) :
    K.prefixCount L a ≤ K.prefixCount L b := by
  classical
  unfold OrderedLanguage.prefixCount
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr
      ((Finset.mem_range.mp (Finset.mem_filter.mp hi).1).trans_le hab),
      (Finset.mem_filter.mp hi).2⟩

/-- A bounded additive change of canonical prefix length changes the prefix
ratio by at most `d / a` in the direction needed for both gap-filling
arguments. -/
theorem canonicalPrefixRatio_le_add_gap
    (K : OrderedLanguage) (L : Set ℕ)
    {a b d : ℕ} (ha : 0 < a) (hab : a ≤ b) (hgap : b ≤ a + d) :
    K.prefixRatio L a ≤ K.prefixRatio L b + (d : ℝ) / a := by
  have hb : b ≠ 0 := (ha.trans_le hab).ne'
  have ha0 : a ≠ 0 := ha.ne'
  have hcount :
      (K.prefixCount L a : ℝ) ≤ K.prefixCount L b := by
    exact_mod_cast canonicalPrefixCount_mono_index K L hab
  have hratio_nonneg := K.prefixRatio_nonneg L b
  have hratio_le := K.prefixRatio_le_one L b
  have hratio_mul :
      K.prefixRatio L b * (b : ℝ) = K.prefixCount L b := by
    simp [OrderedLanguage.prefixRatio, hb]
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hgap' : (b : ℝ) ≤ a + d := by exact_mod_cast hgap
  rw [OrderedLanguage.prefixRatio, if_neg ha0]
  apply (div_le_iff₀ (by exact_mod_cast ha)).2
  rw [add_mul, div_mul_cancel₀ _ (by exact_mod_cast ha0)]
  calc
    (K.prefixCount L a : ℝ)
        ≤ K.prefixCount L b := hcount
    _ = K.prefixRatio L b * (b : ℝ) := hratio_mul.symm
    _ ≤ K.prefixRatio L b * ((a : ℝ) + d) :=
      mul_le_mul_of_nonneg_left hgap' hratio_nonneg
    _ = K.prefixRatio L b * (a : ℝ) +
          K.prefixRatio L b * (d : ℝ) := by ring
    _ ≤ K.prefixRatio L b * (a : ℝ) + d := by
      exact add_le_add_left
        (mul_le_of_le_one_left (Nat.cast_nonneg d) hratio_le) _

/-- Taking a cofinal subsequence cannot decrease the liminf of the bounded
canonical prefix-ratio sequence. -/
theorem canonicalPrefixRatio_liminf_le_comp
    (K : OrderedLanguage) (L : Set ℕ)
    (v : ℕ → ℕ)
    (hv : Filter.Tendsto v Filter.atTop Filter.atTop) :
    Filter.liminf (K.prefixRatio L) Filter.atTop ≤
      Filter.liminf (fun n => K.prefixRatio L (v n)) Filter.atTop := by
  apply (le_liminf_iff
    (isCoboundedUnder_ge_of_le Filter.atTop
      (fun n => K.prefixRatio_le_one L (v n)))
    (isBoundedUnder_of
      ⟨0, fun n => K.prefixRatio_nonneg L (v n)⟩)).2
  intro y hy
  exact hv.eventually
    (eventually_lt_of_lt_liminf hy
      (isBoundedUnder_of
        ⟨0, fun n => K.prefixRatio_nonneg L n⟩))

/-- Taking a cofinal subsequence cannot increase the limsup of the bounded
canonical prefix-ratio sequence. -/
theorem canonicalPrefixRatio_comp_limsup_le
    (K : OrderedLanguage) (L : Set ℕ)
    (v : ℕ → ℕ)
    (hv : Filter.Tendsto v Filter.atTop Filter.atTop) :
    Filter.limsup (fun n => K.prefixRatio L (v n)) Filter.atTop ≤
      Filter.limsup (K.prefixRatio L) Filter.atTop := by
  apply (limsup_le_iff
    (isCoboundedUnder_le_of_le Filter.atTop
      (fun n => K.prefixRatio_nonneg L (v n)))
    (isBoundedUnder_of
      ⟨1, fun n => K.prefixRatio_le_one L (v n)⟩)).2
  intro y hy
  exact hv.eventually
    (eventually_lt_of_limsup_lt hy
      (isBoundedUnder_of
        ⟨1, fun n => K.prefixRatio_le_one L n⟩))

/-- The sampled canonical prefix immediately to the left of `k`. -/
noncomputable def leftScaledPrefix (M : ℝ) (k : ℕ) : ℕ :=
  scaledPrefix M (descaledPrefix M k)

/-- The sampled canonical prefix immediately to the right of `k`. -/
noncomputable def rightScaledPrefix (M : ℝ) (k : ℕ) : ℕ :=
  scaledPrefix M (descaledPrefix M k + 1)

theorem tendsto_leftScaledPrefix_atTop
    (M : ℝ) (hM : 0 < M) :
    Filter.Tendsto (leftScaledPrefix M) Filter.atTop Filter.atTop := by
  exact
    (tendsto_scaledPrefix_atTop M hM).comp
      (tendsto_descaledPrefix_atTop M hM)

theorem tendsto_rightScaledPrefix_atTop
    (M : ℝ) (hM : 0 < M) :
    Filter.Tendsto (rightScaledPrefix M) Filter.atTop Filter.atTop := by
  exact
    (tendsto_scaledPrefix_atTop M hM).comp
      (tendsto_atTop_mono
        (fun k => Nat.le_succ (descaledPrefix M k))
        (tendsto_descaledPrefix_atTop M hM))

/-- Filling the bounded gaps shows that sampling canonical prefix ratios at
`⌈M n⌉` preserves their liminf.  This is the analytic step that cofinality
alone does not provide. -/
theorem liminf_prefixRatio_scaledPrefix
    (K : OrderedLanguage) (L : Set ℕ)
    (M : ℝ) (hM : 0 < M) :
    Filter.liminf
        (fun n => K.prefixRatio L (scaledPrefix M n))
        Filter.atTop =
      K.lowerDensity L := by
  unfold OrderedLanguage.lowerDensity
  apply le_antisymm
  · calc
      Filter.liminf
          (fun n => K.prefixRatio L (scaledPrefix M n))
          Filter.atTop
          ≤ Filter.liminf
              (fun k => K.prefixRatio L
                (leftScaledPrefix M k))
              Filter.atTop := by
            apply (le_liminf_iff
              (isCoboundedUnder_ge_of_le Filter.atTop
                (fun k =>
                  K.prefixRatio_le_one L
                    (leftScaledPrefix M k)))
              (isBoundedUnder_of
                ⟨0, fun k =>
                  K.prefixRatio_nonneg L
                    (leftScaledPrefix M k)⟩)).2
            intro y hy
            exact
              (tendsto_descaledPrefix_atTop M hM).eventually
                (eventually_lt_of_lt_liminf hy
                  (isBoundedUnder_of
                    ⟨0, fun n =>
                      K.prefixRatio_nonneg L
                        (scaledPrefix M n)⟩))
      _ ≤ Filter.liminf (K.prefixRatio L) Filter.atTop := by
        apply (liminf_le_iff
          (isCoboundedUnder_ge_of_le Filter.atTop
            (fun k =>
              K.prefixRatio_le_one L
                (leftScaledPrefix M k)))
          (isBoundedUnder_of
            ⟨0, fun k =>
              K.prefixRatio_nonneg L
                (leftScaledPrefix M k)⟩)).2
        intro y hy
        obtain ⟨z, hzlower, hzy⟩ := exists_between hy
        have hfrequent :
            ∃ᶠ k : ℕ in Filter.atTop,
              K.prefixRatio L k < z :=
          (liminf_le_iff
            (isCoboundedUnder_ge_of_le Filter.atTop
              (fun k => K.prefixRatio_le_one L k))
            (isBoundedUnder_of
              ⟨0, fun k => K.prefixRatio_nonneg L k⟩)).1
            le_rfl z hzlower
        have hleftPositive :
            ∀ᶠ k : ℕ in Filter.atTop,
              0 < leftScaledPrefix M k :=
          (tendsto_leftScaledPrefix_atTop M hM).eventually
            (eventually_gt_atTop 0)
        have hcompare :
            ∀ᶠ k : ℕ in Filter.atTop,
              K.prefixRatio L (leftScaledPrefix M k) ≤
                K.prefixRatio L k +
                  (⌈M⌉₊ : ℝ) / leftScaledPrefix M k := by
          filter_upwards [hleftPositive] with k hk
          exact canonicalPrefixRatio_le_add_gap K L hk
            (scaledPrefix_descaledPrefix_le M hM k)
            (le_scaledPrefix_descaledPrefix_add M hM k)
        have herror :
            Filter.Tendsto
              (fun k : ℕ =>
                (⌈M⌉₊ : ℝ) / leftScaledPrefix M k)
              Filter.atTop (nhds 0) :=
          (tendsto_const_div_atTop_nhds_zero_nat
            (⌈M⌉₊ : ℝ)).comp
              (tendsto_leftScaledPrefix_atTop M hM)
        have herrorSmall :
            ∀ᶠ k : ℕ in Filter.atTop,
              (⌈M⌉₊ : ℝ) / leftScaledPrefix M k < y - z :=
          herror.eventually_lt_const (sub_pos.mpr hzy)
        exact
          (hfrequent.and_eventually
            (hcompare.and herrorSmall)).mono
              (fun k hk => by linarith)
  · exact canonicalPrefixRatio_liminf_le_comp K L
      (scaledPrefix M) (tendsto_scaledPrefix_atTop M hM)

/-- The same bounded-gap argument preserves the limsup at the scaled
canonical prefixes. -/
theorem limsup_prefixRatio_scaledPrefix
    (K : OrderedLanguage) (L : Set ℕ)
    (M : ℝ) (hM : 0 < M) :
    Filter.limsup
        (fun n => K.prefixRatio L (scaledPrefix M n))
        Filter.atTop =
      K.upperDensity L := by
  unfold OrderedLanguage.upperDensity
  apply le_antisymm
  · exact canonicalPrefixRatio_comp_limsup_le K L
      (scaledPrefix M) (tendsto_scaledPrefix_atTop M hM)
  · calc
      Filter.limsup (K.prefixRatio L) Filter.atTop
          ≤ Filter.limsup
              (fun k => K.prefixRatio L
                (rightScaledPrefix M k))
              Filter.atTop := by
        apply (le_limsup_iff
          (isCoboundedUnder_le_of_le Filter.atTop
            (fun k =>
              K.prefixRatio_nonneg L
                (rightScaledPrefix M k)))
          (isBoundedUnder_of
            ⟨1, fun k =>
              K.prefixRatio_le_one L
                (rightScaledPrefix M k)⟩)).2
        intro y hy
        obtain ⟨z, hyz, hzupper⟩ := exists_between hy
        have hfrequent :
            ∃ᶠ k : ℕ in Filter.atTop,
              z < K.prefixRatio L k :=
          (le_limsup_iff
            (isCoboundedUnder_le_of_le Filter.atTop
              (fun k => K.prefixRatio_nonneg L k))
            (isBoundedUnder_of
              ⟨1, fun k => K.prefixRatio_le_one L k⟩)).1
            le_rfl z hzupper
        have hkPositive :
            ∀ᶠ k : ℕ in Filter.atTop, 0 < k :=
          eventually_gt_atTop 0
        have hcompare :
            ∀ᶠ k : ℕ in Filter.atTop,
              K.prefixRatio L k ≤
                K.prefixRatio L (rightScaledPrefix M k) +
                  (⌈M⌉₊ : ℝ) / k := by
          filter_upwards [hkPositive] with k hk
          exact canonicalPrefixRatio_le_add_gap K L hk
            (Nat.le_of_lt
              (lt_scaledPrefix_descaledPrefix_succ M hM k))
            (scaledPrefix_descaledPrefix_succ_le_add M hM k)
        have herrorSmall :
            ∀ᶠ k : ℕ in Filter.atTop,
              (⌈M⌉₊ : ℝ) / k < z - y :=
          (tendsto_const_div_atTop_nhds_zero_nat
            (⌈M⌉₊ : ℝ)).eventually_lt_const
              (sub_pos.mpr hyz)
        exact
          (hfrequent.and_eventually
            (hcompare.and herrorSmall)).mono
              (fun k hk => by linarith)
      _ ≤ Filter.limsup
            (fun n => K.prefixRatio L (scaledPrefix M n))
            Filter.atTop := by
        apply (limsup_le_iff
          (isCoboundedUnder_le_of_le Filter.atTop
            (fun k =>
              K.prefixRatio_nonneg L
                (rightScaledPrefix M k)))
          (isBoundedUnder_of
            ⟨1, fun k =>
              K.prefixRatio_le_one L
                (rightScaledPrefix M k)⟩)).2
        intro y hy
        exact
          (tendsto_atTop_mono
            (fun k => Nat.le_succ (descaledPrefix M k))
            (tendsto_descaledPrefix_atTop M hM)).eventually
              (eventually_lt_of_limsup_lt hy
                (isBoundedUnder_of
                  ⟨1, fun n =>
                    K.prefixRatio_le_one L
                      (scaledPrefix M n)⟩))

/-! ## Lemma 7.5: final change-of-density inequalities -/

/-- Empirical fraction of distinct displayed points lying in `L`.  As for
canonical prefix ratios, the empty prefix receives value zero. -/
noncomputable def empiricalTargetRatio
    (stream : GenLimit.Generic.Stream ℕ)
    (L : Set ℕ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (empiricalTargetCount stream L n : ℝ) / n

theorem empiricalTargetCount_le
    (stream : GenLimit.Generic.Stream ℕ)
    (L : Set ℕ) (n : ℕ) :
    empiricalTargetCount stream L n ≤ n := by
  classical
  unfold empiricalTargetCount
  exact
    (Finset.card_filter_le
      (s := GenLimit.Generic.sample stream n)
      (p := fun x => x ∈ L)).trans
      (GenLimit.Generic.sample_card_le stream n)

theorem empiricalTargetRatio_nonneg
    (stream : GenLimit.Generic.Stream ℕ)
    (L : Set ℕ) (n : ℕ) :
    0 ≤ empiricalTargetRatio stream L n := by
  by_cases hn : n = 0
  · simp [empiricalTargetRatio, hn]
  · simp only [empiricalTargetRatio, hn, if_false]
    positivity

theorem empiricalTargetRatio_le_one
    (stream : GenLimit.Generic.Stream ℕ)
    (L : Set ℕ) (n : ℕ) :
    empiricalTargetRatio stream L n ≤ 1 := by
  by_cases hn : n = 0
  · simp [empiricalTargetRatio, hn]
  · simp only [empiricalTargetRatio, hn, if_false]
    apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)).2
    exact_mod_cast empiricalTargetCount_le stream L n

/-- The finite counting inequality in ratio form.  Its right-hand side is
the canonical prefix ratio sampled at `⌈M n⌉`, multiplied by the exact
ceiling scale `⌈M n⌉ / n`. -/
theorem lemma_7_5_eventual_ratio_comparison
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ)
    (L : Set ℕ) (hLK : L ⊆ K.carrier)
    (M : ℝ) (hM : 0 < M)
    (hbounded :
      BoundedDisplacement K stream K.carrier M) :
    ∀ᶠ n : ℕ in Filter.atTop,
      empiricalTargetRatio stream L n ≤
        ((scaledPrefix M n : ℝ) / n) *
          K.prefixRatio L (scaledPrefix M n) := by
  obtain ⟨N, hN⟩ :=
    lemma_7_5_eventual_prefix_count_real
      K stream L hLK M hM hbounded
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hnN : N ≤ n := (Nat.le_max_left N 1).trans hn
  have hnpos : 0 < n := by
    omega
  have hspos : 0 < scaledPrefix M n := by
    unfold scaledPrefix
    rw [Nat.ceil_pos]
    exact mul_pos hM (by exact_mod_cast hnpos)
  have hcount := hN n hnN
  simp only [empiricalTargetRatio, hnpos.ne', if_false,
    OrderedLanguage.prefixRatio, hspos.ne']
  calc
    (empiricalTargetCount stream L n : ℝ) / n
        ≤ (K.prefixCount L (scaledPrefix M n) : ℝ) / n :=
      div_le_div_of_nonneg_right
        (by exact_mod_cast hcount) (Nat.cast_nonneg n)
    _ = ((scaledPrefix M n : ℝ) / n) *
          ((K.prefixCount L (scaledPrefix M n) : ℝ) /
            scaledPrefix M n) := by
      field_simp

/-- Lemma 7.5, lower-density half, in the source's exact orientation. -/
theorem lemma_7_5_lowerDensity
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ)
    (L : Set ℕ) (hLK : L ⊆ K.carrier)
    (M : ℝ) (hM : 0 < M)
    (hbounded :
      BoundedDisplacement K stream K.carrier M) :
    (1 / M) *
        Filter.liminf
          (empiricalTargetRatio stream L) Filter.atTop ≤
      K.lowerDensity L := by
  let scale : ℕ → ℝ :=
    fun n => (scaledPrefix M n : ℝ) / n
  let canonical : ℕ → ℝ :=
    fun n => K.prefixRatio L (scaledPrefix M n)
  have hscale :
      Filter.Tendsto scale Filter.atTop (nhds M) := by
    exact tendsto_scaledPrefix_div M hM.le
  have hscaleNonneg :
      0 ≤ᶠ[Filter.atTop] scale :=
    Filter.Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hscaleBound :
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop scale :=
    hscale.isBoundedUnder_le
  have hcanonicalNonneg :
      0 ≤ᶠ[Filter.atTop] canonical :=
    Filter.Eventually.of_forall fun n =>
      K.prefixRatio_nonneg L (scaledPrefix M n)
  have hcanonicalCobounded :
      Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop canonical :=
    isCoboundedUnder_ge_of_le Filter.atTop fun n =>
      K.prefixRatio_le_one L (scaledPrefix M n)
  have hproductCobounded :
      Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
        (scale * canonical) :=
    isCoboundedUnder_ge_mul_of_nonneg
      hscaleNonneg hscaleBound
      hcanonicalNonneg hcanonicalCobounded
  have hcompare :
      empiricalTargetRatio stream L ≤ᶠ[Filter.atTop]
        scale * canonical := by
    filter_upwards [
      lemma_7_5_eventual_ratio_comparison
        K stream L hLK M hM hbounded] with n hn
    simpa [scale, canonical] using hn
  have hraw :
      Filter.liminf
          (empiricalTargetRatio stream L) Filter.atTop ≤
        M * K.lowerDensity L := by
    calc
      Filter.liminf
          (empiricalTargetRatio stream L) Filter.atTop
          ≤ Filter.liminf (scale * canonical) Filter.atTop :=
        Filter.liminf_le_liminf hcompare
          (isBoundedUnder_of
            ⟨0, fun n =>
              empiricalTargetRatio_nonneg stream L n⟩)
          hproductCobounded
      _ ≤ Filter.limsup scale Filter.atTop *
            Filter.liminf canonical Filter.atTop :=
        liminf_mul_le hscaleNonneg hscaleBound
          hcanonicalNonneg hcanonicalCobounded
      _ = M * K.lowerDensity L := by
        rw [hscale.limsup_eq]
        exact congrArg (M * ·)
          (liminf_prefixRatio_scaledPrefix K L M hM)
  have hdiv :
      Filter.liminf
          (empiricalTargetRatio stream L) Filter.atTop / M ≤
        K.lowerDensity L := by
    apply (div_le_iff₀ hM).2
    simpa [mul_comm] using hraw
  simpa [div_eq_mul_inv, one_div, mul_comm] using hdiv

/-- Lemma 7.5, upper-density half, again with the exact real displacement
factor rather than an integer relaxation. -/
theorem lemma_7_5_upperDensity
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ)
    (L : Set ℕ) (hLK : L ⊆ K.carrier)
    (M : ℝ) (hM : 0 < M)
    (hbounded :
      BoundedDisplacement K stream K.carrier M) :
    (1 / M) *
        Filter.limsup
          (empiricalTargetRatio stream L) Filter.atTop ≤
      K.upperDensity L := by
  let scale : ℕ → ℝ :=
    fun n => (scaledPrefix M n : ℝ) / n
  let canonical : ℕ → ℝ :=
    fun n => K.prefixRatio L (scaledPrefix M n)
  have hscale :
      Filter.Tendsto scale Filter.atTop (nhds M) := by
    exact tendsto_scaledPrefix_div M hM.le
  have hscaleNonneg :
      0 ≤ᶠ[Filter.atTop] scale :=
    Filter.Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hscaleFrequent :
      ∃ᶠ n : ℕ in Filter.atTop, 0 ≤ scale n :=
    hscaleNonneg.frequently
  have hscaleBound :
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop scale :=
    hscale.isBoundedUnder_le
  have hcanonicalNonneg :
      0 ≤ᶠ[Filter.atTop] canonical :=
    Filter.Eventually.of_forall fun n =>
      K.prefixRatio_nonneg L (scaledPrefix M n)
  have hcanonicalBound :
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop canonical :=
    isBoundedUnder_of
      ⟨1, fun n =>
        K.prefixRatio_le_one L (scaledPrefix M n)⟩
  have hproductBound :
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (scale * canonical) :=
    isBoundedUnder_le_mul_of_nonneg
      hscaleFrequent hscaleBound
      hcanonicalNonneg hcanonicalBound
  have hcompare :
      empiricalTargetRatio stream L ≤ᶠ[Filter.atTop]
        scale * canonical := by
    filter_upwards [
      lemma_7_5_eventual_ratio_comparison
        K stream L hLK M hM hbounded] with n hn
    simpa [scale, canonical] using hn
  have hraw :
      Filter.limsup
          (empiricalTargetRatio stream L) Filter.atTop ≤
        M * K.upperDensity L := by
    calc
      Filter.limsup
          (empiricalTargetRatio stream L) Filter.atTop
          ≤ Filter.limsup (scale * canonical) Filter.atTop :=
        Filter.limsup_le_limsup hcompare
          (isCoboundedUnder_le_of_le Filter.atTop
            (fun n =>
              empiricalTargetRatio_nonneg stream L n))
          hproductBound
      _ ≤ Filter.limsup scale Filter.atTop *
            Filter.limsup canonical Filter.atTop :=
        limsup_mul_le hscaleFrequent hscaleBound
          hcanonicalNonneg hcanonicalBound
      _ = M * K.upperDensity L := by
        rw [hscale.limsup_eq]
        exact congrArg (M * ·)
          (limsup_prefixRatio_scaledPrefix K L M hM)
  have hdiv :
      Filter.limsup
          (empiricalTargetRatio stream L) Filter.atTop / M ≤
        K.upperDensity L := by
    apply (div_le_iff₀ hM).2
    simpa [mul_comm] using hraw
  simpa [div_eq_mul_inv, one_div, mul_comm] using hdiv

/-- Lemma 7.5 (`Change of Density`), combining its lower- and upper-density
conclusions. -/
theorem lemma_7_5_change_of_density
    (K : OrderedLanguage)
    (stream : GenLimit.Generic.Stream ℕ)
    (L : Set ℕ) (hLK : L ⊆ K.carrier)
    (M : ℝ) (hM : 0 < M)
    (hbounded :
      BoundedDisplacement K stream K.carrier M) :
    ((1 / M) *
        Filter.liminf
          (empiricalTargetRatio stream L) Filter.atTop ≤
      K.lowerDensity L) ∧
    ((1 / M) *
        Filter.limsup
          (empiricalTargetRatio stream L) Filter.atTop ≤
      K.upperDensity L) :=
  ⟨lemma_7_5_lowerDensity K stream L hLK M hM hbounded,
    lemma_7_5_upperDensity K stream L hLK M hM hbounded⟩

/-!
## Exact next boundary

Lemma 7.5 is complete, including the non-generic gap filling required for
its lower-density direction.  The next source item is Algorithm 9 and
Theorem 7.8.  It requires a substantially larger stateful proof: the
time-varying priority order and stopping rule must maintain a dense
intersection while the empirical noise estimates stabilize.  That
priority/stopping/density invariant, rather than further ceiling or limit
algebra, is the first remaining boundary.
-/

end GenLimit.InfiniteContamination
