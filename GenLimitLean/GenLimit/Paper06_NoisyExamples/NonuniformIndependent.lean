import GenLimit.Paper06_NoisyExamples.AlternatePositive
import Mathlib.Algebra.Ring.Parity

/-!
# #06 Noisy Examples: Appendix D non-uniform noise-independent generation

Source: Ananth Raman and Vinod Raman, *Generation from Noisy Examples*,
arXiv:2501.04179v2 / ICML 2025, Definition D.1 and Lemma D.2.

The displayed formula in Definition D.1 counts distinct *positive* examples,
as Definition C.1 does, but permits the threshold to depend on the target.
This is what is formalized below.  A sentence immediately before Lemma C.2
instead says that D.1 counts all distinct examples; that sentence conflicts
with the displayed definition and with the proof of Lemma D.2.
-/

namespace GenLimit.NoisyExamples

/-- Definition D.1 at a fixed generator.  The target-dependent threshold is
still independent of the amount and placement of finite noise. -/
def IsNonuniformNoiseIndependentGenerator
    (gen : GenLimit.Generic.Generator α)
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ∃ d : ℕ,
    ∀ stream : GenLimit.Generic.Stream α, HasFiniteNoise stream L →
      ∀ t, (positivePart (GenLimit.Generic.sample stream t) L).card = d →
        ∀ s, t ≤ s → GenLimit.Generic.CorrectAt gen L stream s

/-- Non-uniform noise-independent generatability, Definition D.1. -/
def NonuniformNoiseIndependentGeneratable
    (H : GenLimit.Generic.LanguageClass α) : Prop :=
  ∃ gen : GenLimit.Generic.Generator α,
    IsNonuniformNoiseIndependentGenerator gen H

/-! ## The even/odd counterexample -/

def evenLanguage : GenLimit.Generic.Language ℕ := {x | Even x}

def oddLanguage : GenLimit.Generic.Language ℕ := {x | Odd x}

def parityClass : GenLimit.Generic.LanguageClass ℕ :=
  {evenLanguage, oddLanguage}

theorem evenLanguage_infinite : evenLanguage.Infinite := by
  let values : ℕ → ℕ := fun n ↦ 2 * n
  have hrange : (Set.range values).Infinite := by
    apply Set.infinite_range_of_injective
    intro m n hmn
    dsimp [values] at hmn
    omega
  apply hrange.mono
  rintro _ ⟨n, rfl⟩
  exact (even_iff_exists_two_mul.mpr ⟨n, rfl⟩)

theorem oddLanguage_infinite : oddLanguage.Infinite := by
  let values : ℕ → ℕ := fun n ↦ 2 * n + 1
  have hrange : (Set.range values).Infinite := by
    apply Set.infinite_range_of_injective
    intro m n hmn
    dsimp [values] at hmn
    omega
  apply hrange.mono
  rintro _ ⟨n, rfl⟩
  exact (odd_iff_exists_bit1.mpr ⟨n, rfl⟩)

theorem parityClass_finite : parityClass.Finite := by
  simp [parityClass]

theorem parityClass_uus :
    GenLimit.Generic.UUS parityClass := by
  intro L hL
  rcases hL with (rfl | hL)
  · exact evenLanguage_infinite
  · have : L = oddLanguage := by simpa using hL
    subst L
    exact oddLanguage_infinite

/-- A stream agreeing with the natural-number enumeration before `p`, and
following `tail` afterwards. -/
def identityPrefixStream (p : ℕ) (tail : ℕ → ℕ) :
    GenLimit.Generic.Stream ℕ :=
  fun i ↦ if i < p then i else tail i

theorem sample_identityPrefixStream_of_le
    (p q : ℕ) (tail : ℕ → ℕ) (hqp : q ≤ p) :
    GenLimit.Generic.sample (identityPrefixStream p tail) q =
      Finset.range q := by
  ext x
  rw [GenLimit.Generic.mem_sample_iff, Finset.mem_range]
  constructor
  · rintro ⟨i, hiq, hix⟩
    have hip : i < p := lt_of_lt_of_le hiq hqp
    have : i = x := by
      simpa [identityPrefixStream, hip] using hix
    omega
  · intro hxq
    refine ⟨x, hxq, ?_⟩
    have hxp : x < p := lt_of_lt_of_le hxq hqp
    simp [identityPrefixStream, hxp]

theorem output_identityPrefixStream_boundary
    (gen : GenLimit.Generic.Generator ℕ)
    (p : ℕ) (tail : ℕ → ℕ) :
    GenLimit.Generic.output gen (identityPrefixStream p tail) p =
      gen p (fun i : Fin p ↦ i) := by
  unfold GenLimit.Generic.output
  apply congrArg (gen p)
  funext i
  simp [identityPrefixStream, i.isLt]

theorem finiteNoise_identityPrefixStream
    {p : ℕ} {tail : ℕ → ℕ}
    {L : GenLimit.Generic.Language ℕ}
    (htail : ∀ i, tail i ∈ L) :
    HasFiniteNoise (identityPrefixStream p tail) L := by
  apply (Finset.range p).finite_toSet.subset
  intro i hi
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra hip
  have hpi : p ≤ i := Nat.le_of_not_gt hip
  apply hi
  simp [identityPrefixStream, Nat.not_lt.mpr hpi, htail i]

theorem positivePart_range_even_card (d : ℕ) :
    (positivePart (Finset.range (2 * d)) evenLanguage).card = d := by
  classical
  let E : Finset ℕ := (Finset.range d).image (fun k ↦ 2 * k)
  have heq : positivePart (Finset.range (2 * d)) evenLanguage = E := by
    ext x
    simp only [positivePart, Finset.mem_filter, Finset.mem_range,
      evenLanguage, Set.mem_setOf_eq, E, Finset.mem_image]
    constructor
    · rintro ⟨hx, heven⟩
      obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp heven
      exact ⟨k, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨by omega, even_iff_exists_two_mul.mpr ⟨k, rfl⟩⟩
  rw [heq]
  change E.card = d
  dsimp [E]
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a _ b _ hab
    change 2 * a = 2 * b at hab
    omega

theorem positivePart_range_odd_card (d : ℕ) :
    (positivePart (Finset.range (2 * d)) oddLanguage).card = d := by
  classical
  let O : Finset ℕ := (Finset.range d).image (fun k ↦ 2 * k + 1)
  have heq : positivePart (Finset.range (2 * d)) oddLanguage = O := by
    ext x
    simp only [positivePart, Finset.mem_filter, Finset.mem_range,
      oddLanguage, Set.mem_setOf_eq, O, Finset.mem_image]
    constructor
    · rintro ⟨hx, hodd⟩
      obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp hodd
      exact ⟨k, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨by omega, odd_iff_exists_bit1.mpr ⟨k, rfl⟩⟩
  rw [heq]
  change O.card = d
  dsimp [O]
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a _ b _ hab
    change 2 * a + 1 = 2 * b + 1 at hab
    omega

private def naturalPrefixOutput
    (gen : GenLimit.Generic.Generator ℕ) (p : ℕ) : ℕ :=
  gen p (fun i : Fin p ↦ i)

/-- The paper's even/odd class is the required finite counterexample. -/
theorem parityClass_not_nonuniform_noiseIndependent :
    parityClass.Finite ∧
      GenLimit.Generic.UUS parityClass ∧
      ¬NonuniformNoiseIndependentGeneratable parityClass := by
  classical
  refine ⟨parityClass_finite, parityClass_uus, ?_⟩
  rintro ⟨gen, hgen⟩
  by_cases hOddUnbounded :
      ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ Odd (naturalPrefixOutput gen p)
  · obtain ⟨d, hd⟩ := hgen evenLanguage
      (by simp [parityClass])
    obtain ⟨p, hdp, hpOdd⟩ := hOddUnbounded (2 * d)
    let tail : ℕ → ℕ := fun i ↦ 2 * i
    let stream := identityPrefixStream p tail
    have hnoise : HasFiniteNoise stream evenLanguage := by
      apply finiteNoise_identityPrefixStream
      intro i
      exact even_iff_exists_two_mul.mpr ⟨i, rfl⟩
    have hsample :
        GenLimit.Generic.sample stream (2 * d) =
          Finset.range (2 * d) := by
      exact sample_identityPrefixStream_of_le p (2 * d) tail hdp
    have htrigger :
        (positivePart (GenLimit.Generic.sample stream (2 * d))
          evenLanguage).card = d := by
      rw [hsample]
      exact positivePart_range_even_card d
    have hcorrect := hd stream hnoise (2 * d) htrigger p hdp
    have hout :
        GenLimit.Generic.output gen stream p =
          naturalPrefixOutput gen p := by
      exact output_identityPrefixStream_boundary gen p tail
    have hpEven : Even (naturalPrefixOutput gen p) := by
      simpa [evenLanguage, hout] using hcorrect.1
    exact (Nat.not_odd_iff_even.mpr hpEven) hpOdd
  · push_neg at hOddUnbounded
    obtain ⟨N, hN⟩ := hOddUnbounded
    obtain ⟨d, hd⟩ := hgen oddLanguage
      (by simp [parityClass])
    let p := max N (2 * d)
    have hNp : N ≤ p := Nat.le_max_left _ _
    have hdp : 2 * d ≤ p := Nat.le_max_right _ _
    have hpEven : Even (naturalPrefixOutput gen p) :=
      Nat.not_odd_iff_even.mp (hN p hNp)
    let tail : ℕ → ℕ := fun i ↦ 2 * i + 1
    let stream := identityPrefixStream p tail
    have hnoise : HasFiniteNoise stream oddLanguage := by
      apply finiteNoise_identityPrefixStream
      intro i
      exact odd_iff_exists_bit1.mpr ⟨i, rfl⟩
    have hsample :
        GenLimit.Generic.sample stream (2 * d) =
          Finset.range (2 * d) := by
      exact sample_identityPrefixStream_of_le p (2 * d) tail hdp
    have htrigger :
        (positivePart (GenLimit.Generic.sample stream (2 * d))
          oddLanguage).card = d := by
      rw [hsample]
      exact positivePart_range_odd_card d
    have hcorrect := hd stream hnoise (2 * d) htrigger p hdp
    have hout :
        GenLimit.Generic.output gen stream p =
          naturalPrefixOutput gen p := by
      exact output_identityPrefixStream_boundary gen p tail
    have hpOdd : Odd (naturalPrefixOutput gen p) := by
      simpa [oddLanguage, hout] using hcorrect.1
    exact (Nat.not_odd_iff_even.mpr hpEven) hpOdd

/-- Lemma D.2, corrected to the concrete countably infinite universe `ℕ`
used by its proof. -/
theorem lemma_D_2 :
    ∃ H : GenLimit.Generic.LanguageClass ℕ,
      H.Finite ∧
      GenLimit.Generic.UUS H ∧
      ¬NonuniformNoiseIndependentGeneratable H :=
  ⟨parityClass, parityClass_not_nonuniform_noiseIndependent⟩

end GenLimit.NoisyExamples
