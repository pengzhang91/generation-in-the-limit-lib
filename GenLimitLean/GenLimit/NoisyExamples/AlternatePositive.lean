import GenLimit.NoisyExamples.NonuniformDefinitions
import Mathlib.Data.Set.Countable

/-!
# Raman--Raman Appendix C: counting only distinct positive examples

Source: Ananth Raman and Vinod Raman, *Generation from Noisy Examples*,
arXiv:2501.04179v2 / ICML 2025, Definition C.1, Lemma C.2, and
Theorem C.3.

The paper writes `sup_n (NC_n(H) - n) < ∞`.  Since the main development
deliberately does not assign an artificial natural value to a noisy closure
dimension with gaps, `BoundedNoisyClosureExcess` gives the exact
proposition-level meaning: one constant bounds `k - n` for every
`n`-noisy finite-core witness of cardinality `k`.
-/

namespace GenLimit.NoisyExamples

/-- Definition C.1 at a fixed generator and positive-example threshold. -/
def IsAlternateUniformNoiseIndependentGeneratorAt
    (gen : GenLimit.Generic.Generator α)
    (H : GenLimit.Generic.LanguageClass α) (d : ℕ) : Prop :=
  ∀ L, L ∈ H → ∀ stream : GenLimit.Generic.Stream α,
    HasFiniteNoise stream L →
    ∀ t, (positivePart (GenLimit.Generic.sample stream t) L).card = d →
      ∀ s, t ≤ s → GenLimit.Generic.CorrectAt gen L stream s

/-- Definition C.1: the threshold counts distinct positive observations,
not all distinct observations. -/
def AlternateUniformNoiseIndependentGeneratable
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α, ∃ d : ℕ,
    IsAlternateUniformNoiseIndependentGeneratorAt gen H d

/-- Proposition-level encoding of
`sup_n (NC_n(H) - n) < ∞`. -/
def BoundedNoisyClosureExcess
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ B : ℕ, ∀ n k : ℕ, NoisyClosureWitnessAt H n k → k ≤ n + B

theorem positivePart_mono
    {S T : Finset α} {L : GenLimit.Generic.Language α}
    (hST : S ⊆ T) :
    positivePart S L ⊆ positivePart T L := by
  classical
  intro x hx
  have hx' := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hST hx'.1, hx'.2⟩

private theorem positive_sample_card_step
    (stream : GenLimit.Generic.Stream α)
    (L : GenLimit.Generic.Language α) (t : ℕ) :
    (positivePart (GenLimit.Generic.sample stream (t + 1)) L).card ≤
      (positivePart (GenLimit.Generic.sample stream t) L).card + 1 := by
  classical
  have hsub :
      positivePart (GenLimit.Generic.sample stream (t + 1)) L ⊆
        insert (stream t)
          (positivePart (GenLimit.Generic.sample stream t) L) := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    obtain ⟨s, hs, hsx⟩ :=
      GenLimit.Generic.mem_sample_iff.mp hx'.1
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hst | rfl
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      exact ⟨GenLimit.Generic.mem_sample_iff.mpr ⟨s, hst, hsx⟩, hx'.2⟩
    · subst x
      exact Finset.mem_insert_self (stream s)
        (positivePart (GenLimit.Generic.sample stream s) L)
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- If a finite prefix contains at least `d` distinct positives, an earlier
prefix contains exactly `d`.  This supplies the crossing argument used
implicitly in the necessity proofs of Lemma C.2 and Theorem C.3. -/
theorem exists_earlier_positive_sample_card_eq
    {stream : GenLimit.Generic.Stream α}
    {L : GenLimit.Generic.Language α} {t d : ℕ}
    (hd : d ≤
      (positivePart (GenLimit.Generic.sample stream t) L).card) :
    ∃ r ≤ t,
      (positivePart (GenLimit.Generic.sample stream r) L).card = d := by
  classical
  let hex : ∃ r,
      d ≤ (positivePart (GenLimit.Generic.sample stream r) L).card :=
    ⟨t, hd⟩
  let r := Nat.find hex
  have hrLower :
      d ≤ (positivePart (GenLimit.Generic.sample stream r) L).card :=
    Nat.find_spec hex
  have hrt : r ≤ t := Nat.find_min' hex hd
  by_cases hr0 : r = 0
  · have hd0 : d = 0 := by
      rw [hr0] at hrLower
      simpa [GenLimit.Generic.sample, positivePart] using hrLower
    exact ⟨0, by simp, by simp [GenLimit.Generic.sample, positivePart, hd0]⟩
  · obtain ⟨q, hrq⟩ := Nat.exists_eq_succ_of_ne_zero hr0
    have hprevNot :
        ¬d ≤ (positivePart (GenLimit.Generic.sample stream q) L).card :=
      Nat.find_min hex (by
        change q < r
        rw [hrq]
        exact Nat.lt_succ_self q)
    have hprev :
        (positivePart (GenLimit.Generic.sample stream q) L).card < d :=
      Nat.lt_of_not_ge hprevNot
    have hupper :
        (positivePart (GenLimit.Generic.sample stream (q + 1)) L).card ≤ d :=
      (positive_sample_card_step stream L q).trans
        (Nat.succ_le_iff.mpr hprev)
    rw [hrq] at hrLower hrt
    exact ⟨q + 1, hrt, Nat.le_antisymm hupper hrLower⟩

/-! ## Sufficiency in Theorem C.3 -/

/-- The Appendix C generator: at a sample `S`, use noise level
`|S| - (B+1)` and play a fresh point from that noisy common core whenever it
is infinite. -/
noncomputable def excessNoisyClosureStrategyOutput [Nonempty α]
    (H : GenLimit.Generic.LanguageClass α) (B : ℕ)
    (S : Finset α) : α := by
  classical
  let n := S.card - (B + 1)
  if hcore : (noisyCommonCore H S n).Infinite then
    exact Classical.choose (hcore.diff S.finite_toSet).nonempty
  else
    exact Classical.choice inferInstance

theorem excessNoisyClosureStrategyOutput_spec [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α} {B : ℕ}
    {S : Finset α}
    (hcore :
      (noisyCommonCore H S (S.card - (B + 1))).Infinite) :
    excessNoisyClosureStrategyOutput H B S ∈
      noisyCommonCore H S (S.card - (B + 1)) \ (S : Set α) := by
  classical
  simpa [excessNoisyClosureStrategyOutput, hcore] using
    Classical.choose_spec (hcore.diff S.finite_toSet).nonempty

noncomputable def excessNoisyClosureStrategy [Nonempty α]
    (H : GenLimit.Generic.LanguageClass α) (B : ℕ) :
    GenLimit.Generic.Generator α :=
  fun _ history ↦
    excessNoisyClosureStrategyOutput H B
      (GenLimit.Generic.sequenceSample history)

theorem excessNoisyClosureStrategy_output [Nonempty α]
    (H : GenLimit.Generic.LanguageClass α) (B : ℕ)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    GenLimit.Generic.output (excessNoisyClosureStrategy H B) stream t =
      excessNoisyClosureStrategyOutput H B
        (GenLimit.Generic.sample stream t) := by
  simp [excessNoisyClosureStrategy, GenLimit.Generic.output,
    GenLimit.Generic.sequenceSample_prefix]

theorem boundedNoisyClosureExcess_implies_alternateUniform
    [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (hbound : BoundedNoisyClosureExcess H) :
    AlternateUniformNoiseIndependentGeneratable H := by
  classical
  obtain ⟨B, hB⟩ := hbound
  let d := B + 1
  let gen := excessNoisyClosureStrategy H B
  refine ⟨gen, d, ?_⟩
  intro L hLH stream _hnoise t ht s hts
  let S := GenLimit.Generic.sample stream s
  let n := S.card - d
  have hpositiveMono :
      positivePart (GenLimit.Generic.sample stream t) L ⊆
        positivePart S L :=
    positivePart_mono (GenLimit.Generic.sample_mono hts)
  have hdPositive : d ≤ (positivePart S L).card := by
    rw [← ht]
    exact Finset.card_le_card hpositiveMono
  have hdS : d ≤ S.card := by
    exact hdPositive.trans
      (Finset.card_le_card (by
        intro x hx
        exact (Finset.mem_filter.mp hx).1))
  have htarget : L ∈ noisyVersionSpace H S n := by
    constructor
    · exact hLH
    · change S.card ≤ (positivePart S L).card + n
      dsimp [n]
      omega
  have hcore :
      (noisyCommonCore H S n).Infinite := by
    by_contra hnot
    have hfinite : (noisyCommonCore H S n).Finite :=
      Set.not_infinite.mp hnot
    have hwit : NoisyClosureWitnessAt H n S.card :=
      ⟨S, rfl, ⟨L, htarget⟩, hfinite⟩
    have hboundWitness : S.card ≤ n + B := hB n S.card hwit
    dsimp [n, d] at hdS hboundWitness
    omega
  have hout :
      excessNoisyClosureStrategyOutput H B S ∈
        noisyCommonCore H S n \ (S : Set α) := by
    simpa [n] using excessNoisyClosureStrategyOutput_spec hcore
  have hrun :
      GenLimit.Generic.output gen stream s =
        excessNoisyClosureStrategyOutput H B S := by
    simpa [gen, S] using
      excessNoisyClosureStrategy_output H B stream s
  constructor
  · rw [hrun]
    exact noisyCommonCore_subset_of_mem_versionSpace htarget hout.1
  · rw [hrun]
    exact hout.2

/-! ## Necessity in Theorem C.3 -/

/-- A noisy-closure witness whose cardinality exceeds `n + d` defeats the
positive-example threshold `d`. -/
theorem noisyExcessWitness_defeats_alternate_threshold
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    {n k : ℕ} (hwit : NoisyClosureWitnessAt H n k)
    {d : ℕ} (hlarge : n + d < k)
    (gen : GenLimit.Generic.Generator α) :
    ∃ L, L ∈ H ∧ ∃ stream : GenLimit.Generic.Stream α,
      HasFiniteNoise stream L ∧
      ∃ t,
        (positivePart (GenLimit.Generic.sample stream t) L).card = d ∧
        ∃ s, t ≤ s ∧ ¬GenLimit.Generic.CorrectAt gen L stream s := by
  classical
  obtain ⟨S, hScard, hVS, hcoreFinite⟩ := hwit
  let C : Finset α := hcoreFinite.toFinset
  let P : Finset α := S ∪ C
  have hSP : S ⊆ P := fun x hx ↦ Finset.mem_union_left C hx
  have hcoreP : noisyCommonCore H S n ⊆ (P : Set α) := by
    intro x hx
    exact Finset.mem_union_right S (by simpa [C] using hx)
  let m := P.card
  have hkm : k ≤ m := by
    rw [← hScard]
    exact Finset.card_le_card hSP
  let xs : Fin m → α := fun i => (P.equivFin.symm i).1
  have hxs : Function.Injective xs := by
    intro i j hij
    apply P.equivFin.symm.injective
    exact Subtype.ext hij
  have hsample : GenLimit.Generic.sequenceSample xs = P := by
    simpa [m, xs] using sequenceSample_equivFin_symm P
  let y : α := gen m xs
  obtain ⟨L, hLVS, hybad⟩ :
      ∃ L, L ∈ noisyVersionSpace H S n ∧ (y ∉ L ∨ y ∈ P) := by
    by_cases hyP : y ∈ P
    · obtain ⟨L, hLVS⟩ := hVS
      exact ⟨L, hLVS, Or.inr hyP⟩
    · have hynotcore : y ∉ noisyCommonCore H S n := by
        intro hycore
        exact hyP (hcoreP hycore)
      simp only [noisyCommonCore, Set.mem_setOf_eq, not_forall] at hynotcore
      obtain ⟨L, hLVS, hyL⟩ := hynotcore
      exact ⟨L, hLVS, Or.inl hyL⟩
  have hnegativeSub : negativePart P L ⊆ negativePart S L := by
    intro x hx
    simp only [negativePart, Finset.mem_filter] at hx ⊢
    refine ⟨?_, hx.2⟩
    rcases Finset.mem_union.mp hx.1 with hxS | hxC
    · exact hxS
    · have hxcore : x ∈ noisyCommonCore H S n := by
        simpa [C] using hxC
      exact False.elim
        (hx.2 (noisyCommonCore_subset_of_mem_versionSpace hLVS hxcore))
  have hnegativeP : (negativePart P L).card ≤ n := by
    exact (Finset.card_le_card hnegativeSub).trans
      (negativePart_card_le_of_mem_noisyVersionSpace hLVS)
  have hsplit :
      (positivePart P L).card + (negativePart P L).card = P.card := by
    simpa [positivePart, negativePart] using
      P.filter_card_add_filter_neg_card_eq_card (fun x ↦ x ∈ L)
  have hpositiveP : d ≤ (positivePart P L).card := by
    omega
  have hLinf : L.Infinite := hUUS L hLVS.1
  let tail : α := Classical.choose hLinf.nonempty
  have htail : tail ∈ L := Classical.choose_spec hLinf.nonempty
  let stream : GenLimit.Generic.Stream α := prefixThen xs tail
  have hnoiseAtMost : HasNoiseAtMost stream L n := by
    apply hasNoiseAtMost_prefixThen hxs htail
    rw [hsample]
    exact hnegativeP
  have hnoise : HasFiniteNoise stream L :=
    hasFiniteNoise_of_hasNoiseAtMost hnoiseAtMost
  have hsampleM : GenLimit.Generic.sample stream m = P := by
    calc
      GenLimit.Generic.sample stream m =
          GenLimit.Generic.sequenceSample xs :=
        sample_prefixThen_full xs tail
      _ = P := hsample
  have hpositiveM :
      d ≤ (positivePart (GenLimit.Generic.sample stream m) L).card := by
    rwa [hsampleM]
  obtain ⟨t, htm, htcard⟩ :=
    exists_earlier_positive_sample_card_eq hpositiveM
  have hout : GenLimit.Generic.output gen stream m = y := by
    apply congrArg (fun f : Fin m → α => gen m f)
    funext i
    simp [stream, prefixThen, i.isLt]
  refine ⟨L, hLVS.1, stream, hnoise, t, htcard, m, htm, ?_⟩
  intro hcorrect
  rcases hybad with hyL | hyP
  · exact hyL (hout ▸ hcorrect.1)
  · exact hcorrect.2 (by simpa [hout, hsampleM] using hyP)

theorem alternateUniform_implies_boundedNoisyClosureExcess
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    (hgen : AlternateUniformNoiseIndependentGeneratable H) :
    BoundedNoisyClosureExcess H := by
  classical
  obtain ⟨gen, d, hgen⟩ := hgen
  refine ⟨d, ?_⟩
  intro n k hwit
  by_contra hnot
  have hlarge : n + d < k := Nat.lt_of_not_ge hnot
  obtain ⟨L, hLH, stream, hnoise, t, ht, s, hts, hfail⟩ :=
    noisyExcessWitness_defeats_alternate_threshold
      hUUS hwit hlarge gen
  exact hfail (hgen L hLH stream hnoise t ht s hts)

/-- Theorem C.3, with `BoundedNoisyClosureExcess` as the exact
proposition-level reading of the paper's extended-natural supremum. -/
theorem theorem_C_3 [Countable α] [Nonempty α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H) :
    AlternateUniformNoiseIndependentGeneratable H ↔
      BoundedNoisyClosureExcess H := by
  constructor
  · exact alternateUniform_implies_boundedNoisyClosureExcess hUUS
  · exact boundedNoisyClosureExcess_implies_alternateUniform

/-! ## Lemma C.2 -/

/-- Lemma C.2 (necessary condition for the alternate uniform notion).

If deleting one hypothesis changes a finite common intersection into an
infinite one, then the class cannot have a uniform threshold measured only
in distinct positive observations. -/
theorem lemma_C_2 [Countable α]
    {H F : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    (hFH : F ⊆ H)
    {f : GenLimit.Generic.Language α} (hfF : f ∈ F)
    (hcommonFinite : (commonIntersection F).Finite)
    (hwithoutInfinite : (commonIntersection (F \ {f})).Infinite) :
    ¬AlternateUniformNoiseIndependentGeneratable H := by
  classical
  intro hgen
  obtain ⟨B, hB⟩ :=
    alternateUniform_implies_boundedNoisyClosureExcess hUUS hgen
  let N := B + 1
  let Aset :=
    commonIntersection (F \ {f}) \ commonIntersection F
  let Bset := f \ commonIntersection F
  have hAInfinite : Aset.Infinite := by
    exact hwithoutInfinite.diff hcommonFinite
  have hBInfinite : Bset.Infinite := by
    exact (hUUS f (hFH hfF)).diff hcommonFinite
  obtain ⟨A, hA, hAcard⟩ := hAInfinite.exists_subset_card_eq N
  obtain ⟨D, hD, hDcard⟩ := hBInfinite.exists_subset_card_eq N
  have hAD : Disjoint A D := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxD
    have hxAset := hA hxA
    have hxDset := hD hxD
    exact hxAset.2 (by
      intro L hLF
      by_cases hLf : L = f
      · subst L
        exact hxDset.1
      · exact hxAset.1 L ⟨hLF, by simp [hLf]⟩)
  let S := A ∪ D
  have hScard : S.card = 2 * N := by
    dsimp [S]
    rw [Finset.card_union_of_disjoint hAD, hAcard, hDcard]
    omega
  have hFversion :
      F ⊆ noisyVersionSpace H S N := by
    intro L hLF
    constructor
    · exact hFH hLF
    · by_cases hLf : L = f
      · subst L
        have hDpositive : D ⊆ positivePart S f := by
          intro x hxD
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_union_right A hxD, (hD hxD).1⟩
        have hposCard :
            N ≤ (positivePart S f).card := by
          rw [← hDcard]
          exact Finset.card_le_card hDpositive
        change S.card ≤ (positivePart S f).card + N
        omega
      · have hApositive : A ⊆ positivePart S L := by
          intro x hxA
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_union_left D hxA,
            (hA hxA).1 L ⟨hLF, by simp [hLf]⟩⟩
        have hposCard :
            N ≤ (positivePart S L).card := by
          rw [← hAcard]
          exact Finset.card_le_card hApositive
        change S.card ≤ (positivePart S L).card + N
        omega
  have hVS : (noisyVersionSpace H S N).Nonempty :=
    ⟨f, hFversion hfF⟩
  have hcoreFinite : (noisyCommonCore H S N).Finite := by
    apply hcommonFinite.subset
    intro x hx
    exact fun L hLF ↦ hx L (hFversion hLF)
  have hwit : NoisyClosureWitnessAt H N (2 * N) :=
    ⟨S, hScard, hVS, hcoreFinite⟩
  have hbound := hB N (2 * N) hwit
  dsimp [N] at hbound
  omega

end GenLimit.NoisyExamples
