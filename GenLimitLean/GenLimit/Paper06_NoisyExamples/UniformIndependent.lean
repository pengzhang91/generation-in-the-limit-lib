import GenLimit.Paper06_NoisyExamples.Definitions
import GenLimit.Core.VersionSpace
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Fintype.EquivFin

/-!
# #06 Noisy Examples: uniform noise-independent generation

Source: Ananth Raman and Vinod Raman, *Generation from Noisy Examples*,
arXiv:2501.04179v2 / ICML 2025, Definitions 2.3--2.4 and Theorem 3.1.

The paper represents a hypothesis by its support.  We therefore use the
generic language API directly.  `HasFiniteNoise stream L` is the literal
condition that the stream contains only finitely many examples outside the
target language; it does not require the stream to enumerate the target.

The printed theorem says that the example space is countable.  Its proof also
uses an unbounded supply of distinct examples, and the equivalence is false
for an empty class over a finite example space.  We expose that implicit
convention as `[Infinite α]`; `[Countable α]` is retained on the paper-level
theorem.
-/

namespace GenLimit.NoisyExamples

theorem commonIntersection_subset_of_mem
    {H : GenLimit.Generic.LanguageClass α}
    {L : GenLimit.Generic.Language α} (hL : L ∈ H) :
    commonIntersection H ⊆ L := by
  intro x hx
  exact hx L hL

/-- The class-wide intersection in #06 is the ordinary positive-data common
core at the empty sample.  The paper-facing name remains local to #06, while
this theorem records its relationship with the neutral Core vocabulary. -/
theorem commonIntersection_eq_commonCore_empty
    (H : GenLimit.Generic.LanguageClass α) :
    commonIntersection H = GenLimit.Generic.commonCore H ∅ := by
  ext x
  constructor
  · intro hx L hL
    exact hx L hL.1
  · intro hx L hL
    exact hx L ⟨hL, by simp⟩

/-- The zero-sample generator used for the easy direction of Theorem 3.1. -/
noncomputable def commonIntersectionGenerator
    (H : GenLimit.Generic.LanguageClass α)
    (hcommon : (commonIntersection H).Infinite) :
    GenLimit.Generic.Generator α := by
  classical
  exact fun _ xs =>
    Classical.choose
      (hcommon.diff (GenLimit.Generic.sequenceSample xs).finite_toSet).nonempty

theorem commonIntersectionGenerator_spec
    {H : GenLimit.Generic.LanguageClass α}
    (hcommon : (commonIntersection H).Infinite)
    {t : ℕ} (xs : Fin t → α) :
    commonIntersectionGenerator H hcommon t xs ∈
      commonIntersection H \
        (↑(GenLimit.Generic.sequenceSample xs) : Set α) := by
  classical
  exact Classical.choose_spec
    (hcommon.diff (GenLimit.Generic.sequenceSample xs).finite_toSet).nonempty

/-- Sufficiency in Theorem 3.1: an infinite common intersection gives a
generator that succeeds from the empty history onward. -/
theorem infinite_commonIntersection_implies_uniform_noiseIndependent
    {H : GenLimit.Generic.LanguageClass α}
    (hcommon : (commonIntersection H).Infinite) :
    UniformNoiseIndependentGeneratable H := by
  let gen := commonIntersectionGenerator H hcommon
  refine ⟨gen, 0, ?_⟩
  intro L hLH stream _hnoise t _ht s _hts
  have hspec := commonIntersectionGenerator_spec hcommon
    (fun i : Fin s => stream i)
  rw [GenLimit.Generic.sequenceSample_prefix] at hspec
  exact ⟨commonIntersection_subset_of_mem hLH hspec.1, hspec.2⟩

/-- A stream formed from a finite prefix followed forever by `tail`. -/
def prefixThen {n : ℕ} (xs : Fin n → α) (tail : α) :
    GenLimit.Generic.Stream α :=
  fun i => if hi : i < n then xs ⟨i, hi⟩ else tail

theorem prefixThen_apply_lt {n : ℕ} (xs : Fin n → α) (tail : α)
    {i : ℕ} (hi : i < n) :
    prefixThen xs tail i = xs ⟨i, hi⟩ := by
  simp [prefixThen, hi]

theorem sample_prefixThen_full {n : ℕ} (xs : Fin n → α) (tail : α) :
    GenLimit.Generic.sample (prefixThen xs tail) n =
      GenLimit.Generic.sequenceSample xs := by
  classical
  ext x
  rw [GenLimit.Generic.mem_sample_iff,
    GenLimit.Generic.mem_sequenceSample_iff]
  constructor
  · rintro ⟨i, hi, hix⟩
    refine ⟨⟨i, hi⟩, ?_⟩
    simpa [prefixThen, hi] using hix
  · rintro ⟨i, hix⟩
    refine ⟨i, i.isLt, ?_⟩
    simpa [prefixThen, i.isLt] using hix

theorem sequenceSample_card_of_injective {n : ℕ} (xs : Fin n → α)
    (hxs : Function.Injective xs) :
    (GenLimit.Generic.sequenceSample xs).card = n :=
  GenLimit.Generic.sequenceSample_card_of_injective xs hxs

theorem sample_prefixThen_card_of_le {n d : ℕ} (xs : Fin n → α)
    (hxs : Function.Injective xs) (tail : α) (hdn : d ≤ n) :
    (GenLimit.Generic.sample (prefixThen xs tail) d).card = d := by
  let ys : Fin d → α := fun i => xs ⟨i, lt_of_lt_of_le i.isLt hdn⟩
  have hys : Function.Injective ys := by
    intro i j hij
    have hsub :
        (⟨(i : ℕ), lt_of_lt_of_le i.isLt hdn⟩ : Fin n) =
          ⟨(j : ℕ), lt_of_lt_of_le j.isLt hdn⟩ := hxs hij
    apply Fin.ext
    exact congrArg (fun z : Fin n => z.val) hsub
  have hsample : GenLimit.Generic.sample (prefixThen xs tail) d =
      GenLimit.Generic.sequenceSample ys := by
    classical
    ext x
    rw [GenLimit.Generic.mem_sample_iff,
      GenLimit.Generic.mem_sequenceSample_iff]
    constructor
    · rintro ⟨i, hi, hix⟩
      refine ⟨⟨i, hi⟩, ?_⟩
      have hin : i < n := lt_of_lt_of_le hi hdn
      have hprefix : prefixThen xs tail i = xs ⟨i, hin⟩ :=
        prefixThen_apply_lt xs tail hin
      rw [hprefix] at hix
      simpa [ys] using hix
    · rintro ⟨i, hix⟩
      refine ⟨i, i.isLt, ?_⟩
      have hin : (i : ℕ) < n := lt_of_lt_of_le i.isLt hdn
      calc
        prefixThen xs tail i = xs ⟨i, hin⟩ :=
          prefixThen_apply_lt xs tail hin
        _ = ys i := by rfl
        _ = x := hix
  rw [hsample]
  exact sequenceSample_card_of_injective ys hys

theorem sequenceSample_equivFin_symm (S : Finset α) :
    GenLimit.Generic.sequenceSample
      (fun i : Fin S.card => (S.equivFin.symm i).1) = S :=
  GenLimit.Generic.sequenceSample_equivFin_symm S

theorem equivFin_symm_value_injective (S : Finset α) :
    Function.Injective (fun i : Fin S.card => (S.equivFin.symm i).1) :=
  GenLimit.Generic.equivFin_symm_value_injective S

theorem sequenceSample_equivFinOfCardEq_symm
    (S : Finset α) {n : ℕ} (hcard : S.card = n) :
    GenLimit.Generic.sequenceSample
      (fun i : Fin n => ((S.equivFinOfCardEq hcard).symm i).1) = S := by
  classical
  ext x
  rw [GenLimit.Generic.mem_sequenceSample_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact (S.equivFinOfCardEq hcard).symm i |>.2
  · intro hx
    let z : S := ⟨x, hx⟩
    refine ⟨S.equivFinOfCardEq hcard z, ?_⟩
    change ((S.equivFinOfCardEq hcard).symm
      (S.equivFinOfCardEq hcard z)).1 = x
    simp [z]

theorem finiteNoise_prefixThen
    {n : ℕ} {xs : Fin n → α} {tail : α}
    {L : GenLimit.Generic.Language α}
    (htail : tail ∈ L) :
    HasFiniteNoise (prefixThen xs tail) L := by
  apply (Finset.range n).finite_toSet.subset
  intro i hi
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hin
  have hni : n ≤ i := Nat.le_of_not_gt hin
  have hstream : prefixThen xs tail i = tail := by
    simp [prefixThen, Nat.not_lt.mpr hni]
  exact hi (hstream.symm ▸ htail)

/-- The adversarial finite-prefix construction in the necessity proof of
Theorem 3.1.  It is stated separately to keep the paper's proof structure
visible. -/
theorem finite_commonIntersection_defeats_threshold [Infinite α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    (hfinite : (commonIntersection H).Finite)
    (gen : GenLimit.Generic.Generator α) (d : ℕ) :
    ∃ L, L ∈ H ∧ ∃ stream : GenLimit.Generic.Stream α,
      HasFiniteNoise stream L ∧
      ∃ t, (GenLimit.Generic.sample stream t).card = d ∧
        ∃ s, t ≤ s ∧ ¬GenLimit.Generic.CorrectAt gen L stream s := by
  classical
  have hH : H.Nonempty := by
    by_contra hne
    have hHempty : H = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hcommonUniv : commonIntersection H = Set.univ := by
      ext x
      simp [commonIntersection, hHempty]
    have hunivFinite : (Set.univ : Set α).Finite := by
      simpa [hcommonUniv] using hfinite
    exact Set.infinite_univ hunivFinite
  let C : Finset α := hfinite.toFinset
  let m : ℕ := max d C.card
  have hCm : C.card ≤ m := Nat.le_max_right _ _
  obtain ⟨S, hCS, hScard⟩ := Infinite.exists_superset_card_eq C m hCm
  let xs : Fin m → α := fun i => (S.equivFinOfCardEq hScard).symm i
  have hxs : Function.Injective xs := by
    intro i j hij
    exact (S.equivFinOfCardEq hScard).symm.injective (Subtype.ext hij)
  let y : α := gen m xs
  have hcommonS : commonIntersection H ⊆ (↑S : Set α) := by
    intro x hx
    have hxC : x ∈ C := by
      simpa [C] using hx
    exact hCS hxC
  obtain ⟨L, hLH, hybad⟩ : ∃ L, L ∈ H ∧ (y ∉ L ∨ y ∈ S) := by
    by_cases hyS : y ∈ S
    · obtain ⟨L, hLH⟩ := hH
      exact ⟨L, hLH, Or.inr hyS⟩
    · have hycommon : y ∉ commonIntersection H := by
        intro hy
        exact hyS (hcommonS hy)
      simp only [commonIntersection, Set.mem_setOf_eq, not_forall] at hycommon
      obtain ⟨L, hLH, hyL⟩ := hycommon
      exact ⟨L, hLH, Or.inl hyL⟩
  have hLinf : L.Infinite := hUUS L hLH
  let tail : α := Classical.choose hLinf.nonempty
  have htail : tail ∈ L := Classical.choose_spec hLinf.nonempty
  let stream : GenLimit.Generic.Stream α := prefixThen xs tail
  have hnoise : HasFiniteNoise stream L := by
    exact finiteNoise_prefixThen htail
  have hdm : d ≤ m := Nat.le_max_left _ _
  have hsampleD : (GenLimit.Generic.sample stream d).card = d := by
    exact sample_prefixThen_card_of_le xs hxs tail hdm
  have hsampleM : GenLimit.Generic.sample stream m = S := by
    calc
      GenLimit.Generic.sample stream m =
          GenLimit.Generic.sequenceSample xs :=
        sample_prefixThen_full xs tail
      _ = S := by
        simpa [xs] using
          sequenceSample_equivFinOfCardEq_symm S hScard
  have hout : GenLimit.Generic.output gen stream m = y := by
    apply congrArg (fun f : Fin m → α => gen m f)
    funext i
    simp [stream, prefixThen, i.isLt, xs]
  refine ⟨L, hLH, stream, hnoise, d, hsampleD, m, hdm, ?_⟩
  intro hcorrect
  rcases hybad with hyL | hyS
  · exact hyL (hout ▸ hcorrect.1)
  · exact hcorrect.2 (by simpa [hout, hsampleM] using hyS)

/-- Necessity in Theorem 3.1. -/
theorem uniform_noiseIndependent_implies_infinite_commonIntersection
    [Infinite α] {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H)
    (hgen : UniformNoiseIndependentGeneratable H) :
    (commonIntersection H).Infinite := by
  classical
  by_contra hnot
  have hfinite : (commonIntersection H).Finite := Set.not_infinite.mp hnot
  obtain ⟨gen, d, hgen⟩ := hgen
  obtain ⟨L, hLH, stream, hnoise, t, ht, s, hts, hfail⟩ :=
    finite_commonIntersection_defeats_threshold hUUS hfinite gen d
  exact hfail (hgen L hLH stream hnoise t ht s hts)

/-- Theorem 3.1 (Characterization of Uniform Noise-independent
Generatability). -/
theorem theorem_3_1 [Countable α] [Infinite α]
    {H : GenLimit.Generic.LanguageClass α}
    (hUUS : GenLimit.Generic.UUS H) :
    UniformNoiseIndependentGeneratable H ↔
      (commonIntersection H).Infinite := by
  constructor
  · exact uniform_noiseIndependent_implies_infinite_commonIntersection hUUS
  · exact infinite_commonIntersection_implies_uniform_noiseIndependent

end GenLimit.NoisyExamples
