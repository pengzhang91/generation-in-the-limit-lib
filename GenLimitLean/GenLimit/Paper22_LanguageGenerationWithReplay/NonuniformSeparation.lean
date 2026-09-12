import GenLimit.Paper22_LanguageGenerationWithReplay.Uniform
import GenLimit.Paper02_LearningTheory.NonuniformCharacterization
import Mathlib.Data.Set.Countable
import Mathlib.Data.Vector.Basic

/-!
# Replay separates non-uniform generation

Source: Giorgio Racca, Michal Valko, and Amartya Sanyal,
*Language Generation with Replay: A Learning-Theoretic View of Model
Collapse*, arXiv:2603.11784v2, Definition 3.3 and Theorem 5.1.

The paper uses the integers, with one language supported on the positive
integers and the `d`-th competing language supported on the first `d`
positive integers together with every negative integer.  We use the
support-isomorphic universe `Sum ℕ ℕ`: the left copy plays the role of the
positive integers and the right copy the role of the negative integers.

Unlike a merely abstract diagonal lemma, the proof below constructs the
paper's online replay stream.  Its first `d` values are distinct left
points; every later input is the immediately preceding generator output.
-/

namespace GenLimit
namespace Replay

open GenLimit.LiRamanTewari

abbrev HardPoint := Sum ℕ ℕ

/-- The paper's `h∞`: the entire left copy. -/
def upperLanguage : Generic.Language HardPoint :=
  {x | match x with
    | Sum.inl _ => True
    | Sum.inr _ => False}

/-- The paper's `h_d`: the first `d` left points and the entire right copy. -/
def cutoffLanguage (d : ℕ) : Generic.Language HardPoint :=
  {x | match x with
    | Sum.inl n => n < d
    | Sum.inr _ => True}

/-- The countable hard class from Theorem 5.1. -/
def nonuniformHardClass : Generic.LanguageClass HardPoint :=
  {upperLanguage} ∪ Set.range cutoffLanguage

theorem upperLanguage_in_class :
    upperLanguage ∈ nonuniformHardClass := by
  simp [nonuniformHardClass]

theorem cutoffLanguage_in_class (d : ℕ) :
    cutoffLanguage d ∈ nonuniformHardClass := by
  exact Set.mem_union_right _ ⟨d, rfl⟩

theorem nonuniformHardClass_countable :
    (nonuniformHardClass).Countable := by
  exact Set.countable_singleton upperLanguage |>.union
    (Set.countable_range cutoffLanguage)

theorem upperLanguage_infinite : upperLanguage.Infinite := by
  have hinj : Function.Injective (Sum.inl : ℕ → HardPoint) :=
    Sum.inl_injective
  have hrange : (Set.range (Sum.inl : ℕ → HardPoint)).Infinite :=
    Set.infinite_range_of_injective hinj
  apply hrange.mono
  rintro _ ⟨n, rfl⟩
  simp [upperLanguage]

theorem cutoffLanguage_infinite (d : ℕ) :
    (cutoffLanguage d).Infinite := by
  have hinj : Function.Injective (Sum.inr : ℕ → HardPoint) :=
    Sum.inr_injective
  have hrange : (Set.range (Sum.inr : ℕ → HardPoint)).Infinite :=
    Set.infinite_range_of_injective hinj
  apply hrange.mono
  rintro _ ⟨n, rfl⟩
  simp [cutoffLanguage]

theorem nonuniformHardClass_uus :
    UUS nonuniformHardClass := by
  intro L hL
  change L ∈ ({upperLanguage} : Set (Generic.Language HardPoint)) ∪
    Set.range cutoffLanguage at hL
  rcases hL with hL | ⟨d, rfl⟩
  · simp only [Set.mem_singleton_iff] at hL
    subst L
    exact upperLanguage_infinite
  · exact cutoffLanguage_infinite d

/-- Definition 3.3, with the paper's positive sample-complexity convention
made explicit. -/
def IsNonuniformReplayGenerator
    (gen : Generic.Generator α) (H : Generic.LanguageClass α) : Prop :=
  ∀ L, L ∈ H → ∃ d, 0 < d ∧
    ∀ stream : Generic.Stream α, IsReplaySequence gen L stream →
      ∀ t, 0 < t → (Generic.sample stream t).card = d →
        ∀ s, t ≤ s → Generic.CorrectAt gen L stream s

def NonuniformlyGeneratableWithReplay
    (H : Generic.LanguageClass α) : Prop :=
  ∃ gen : Generic.Generator α, IsNonuniformReplayGenerator gen H

/-- Finite histories of the paper's online adversary. -/
noncomputable def adversarialPrefixes
    (gen : Generic.Generator HardPoint) (d : ℕ) :
    (n : ℕ) → Vector HardPoint n
  | 0 => #v[]
  | n + 1 =>
      let prior := adversarialPrefixes gen d n
      prior.push
        (if n < d then Sum.inl n
        else gen n (fun i => prior[i.val]))

/-- The input revealed at round `n`, namely the last value of the history
of length `n + 1`. -/
noncomputable def adversarialStream
    (gen : Generic.Generator HardPoint) (d : ℕ) :
    Generic.Stream HardPoint :=
  fun n => (adversarialPrefixes gen d (n + 1))[n]

theorem adversarialPrefixes_get_eq_stream
    (gen : Generic.Generator HardPoint) (d : ℕ)
    (n : ℕ) (i : Fin n) :
    (adversarialPrefixes gen d n)[i.val] =
      adversarialStream gen d i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      by_cases hi : i.val < n
      · rw [adversarialPrefixes]
        simp only [Vector.getElem_push_lt hi]
        exact ih ⟨i.val, hi⟩
      · have hin : i.val = n := by omega
        have hiFin : i = Fin.last n := Fin.ext hin
        subst i
        rfl

theorem adversarialStream_eq_seed
    (gen : Generic.Generator HardPoint) (d : ℕ)
    {n : ℕ} (hn : n < d) :
    adversarialStream gen d n = Sum.inl n := by
  rw [adversarialStream, adversarialPrefixes]
  simp [hn]

theorem adversarialStream_eq_output
    (gen : Generic.Generator HardPoint) (d : ℕ)
    {n : ℕ} (hn : d ≤ n) :
    adversarialStream gen d n =
      Generic.output gen (adversarialStream gen d) n := by
  rw [adversarialStream, adversarialPrefixes]
  simp only [if_neg (Nat.not_lt.mpr hn), Vector.getElem_push_eq]
  rw [Generic.output]
  apply congrArg (gen n)
  funext i
  exact adversarialPrefixes_get_eq_stream gen d n i

theorem adversarialStream_replay_upper
    (gen : Generic.Generator HardPoint) {d : ℕ} (hd : 0 < d) :
    IsReplaySequence gen upperLanguage (adversarialStream gen d) := by
  intro n
  by_cases hn : n < d
  · left
    rw [adversarialStream_eq_seed gen d hn]
    simp [upperLanguage]
  · right
    have hdn : d ≤ n := Nat.le_of_not_gt hn
    refine ⟨n, hd.trans_le hdn, le_rfl, ?_⟩
    exact (adversarialStream_eq_output gen d hdn).symm

theorem adversarialStream_replay_cutoff
    (gen : Generic.Generator HardPoint) {d : ℕ} (hd : 0 < d) :
    IsReplaySequence gen (cutoffLanguage d)
      (adversarialStream gen d) := by
  intro n
  by_cases hn : n < d
  · left
    rw [adversarialStream_eq_seed gen d hn]
    simpa [cutoffLanguage]
  · right
    have hdn : d ≤ n := Nat.le_of_not_gt hn
    refine ⟨n, hd.trans_le hdn, le_rfl, ?_⟩
    exact (adversarialStream_eq_output gen d hdn).symm

theorem sequenceSample_card_of_injective
    {n : ℕ} (xs : Fin n → α) (hxs : Function.Injective xs) :
    (Generic.sequenceSample xs).card = n := by
  classical
  rw [Generic.sequenceSample, Finset.card_image_iff.mpr]
  · simp
  · intro i _ j _ hij
    exact hxs hij

theorem adversarialStream_sample_seed_card
    (gen : Generic.Generator HardPoint) (d : ℕ) :
    (Generic.sample (adversarialStream gen d) d).card = d := by
  rw [← Generic.sequenceSample_prefix]
  apply sequenceSample_card_of_injective
  intro i j hij
  change adversarialStream gen d i.val =
    adversarialStream gen d j.val at hij
  rw [adversarialStream_eq_seed gen d i.isLt,
    adversarialStream_eq_seed gen d j.isLt] at hij
  exact Fin.ext (Sum.inl.inj hij)

/-- Once the upper-language guarantee applies, the replay tail has no
repeated values, so its range is infinite. -/
theorem adversarialStream_range_infinite
    {gen : Generic.Generator HardPoint} {d : ℕ} (_hd : 0 < d)
    (hcorrect :
      ∀ s, d ≤ s →
        Generic.CorrectAt gen upperLanguage
          (adversarialStream gen d) s) :
    (Set.range (adversarialStream gen d)).Infinite := by
  let tail : ℕ → HardPoint :=
    fun k => adversarialStream gen d (d + k)
  have htailInjective : Function.Injective tail := by
    intro i j
    intro htailEq
    by_contra hij
    have htailEq' :
        adversarialStream gen d (d + i) =
          adversarialStream gen d (d + j) := by
      simpa [tail] using htailEq
    have hij' : i < j ∨ j < i := Nat.lt_or_gt_of_ne hij
    rcases hij' with hij' | hij'
    · have hearlier :
          adversarialStream gen d (d + i) ∈
            Generic.sample (adversarialStream gen d) (d + j) := by
        exact Generic.mem_sample_iff.mpr
          ⟨d + i, Nat.add_lt_add_left hij' d, rfl⟩
      have hlate := (hcorrect (d + j) (Nat.le_add_right d j)).2
      have hout :=
        adversarialStream_eq_output gen d (Nat.le_add_right d j)
      rw [htailEq', hout] at hearlier
      exact hlate hearlier
    · have hearlier :
          adversarialStream gen d (d + j) ∈
            Generic.sample (adversarialStream gen d) (d + i) := by
        exact Generic.mem_sample_iff.mpr
          ⟨d + j, Nat.add_lt_add_left hij' d, rfl⟩
      have hlate := (hcorrect (d + i) (Nat.le_add_right d i)).2
      have hout :=
        adversarialStream_eq_output gen d (Nat.le_add_right d i)
      rw [← htailEq', hout] at hearlier
      exact hlate hearlier
  have htailRange : (Set.range tail).Infinite :=
    Set.infinite_range_of_injective htailInjective
  apply htailRange.mono
  rintro x ⟨k, rfl⟩
  exact ⟨d + k, rfl⟩

theorem output_mem_finite_intersection
    {gen : Generic.Generator HardPoint} {d t M s : ℕ}
    (hM : M = max d t) (hMs : M ≤ s)
    (hupper :
      ∀ q, d ≤ q →
        Generic.CorrectAt gen upperLanguage
          (adversarialStream gen d) q)
    (hcutoff :
      ∀ q, t ≤ q →
        Generic.CorrectAt gen (cutoffLanguage d)
          (adversarialStream gen d) q) :
    ∃ n, n < d ∧
      Generic.output gen (adversarialStream gen d) s = Sum.inl n := by
  have hds : d ≤ s := by
    exact (hM ▸ Nat.le_max_left d t).trans hMs
  have hts : t ≤ s := by
    exact (hM ▸ Nat.le_max_right d t).trans hMs
  have hu := (hupper s hds).1
  have hc := (hcutoff s hts).1
  cases hout : Generic.output gen (adversarialStream gen d) s with
  | inl n =>
      refine ⟨n, ?_, rfl⟩
      simpa [cutoffLanguage, hout] using hc
  | inr n =>
      simp [upperLanguage, hout] at hu

/-- Theorem 5.1: a countable UUS class that is non-uniformly generatable
in the standard model (by the standard countable-class theorem) but not
non-uniformly generatable with replay.  This declaration proves the replay
impossibility, which is the new content of the source theorem. -/
theorem theorem_5_1_not_nonuniformlyGeneratableWithReplay :
    ¬NonuniformlyGeneratableWithReplay nonuniformHardClass := by
  rintro ⟨gen, hgen⟩
  obtain ⟨d, hd, hupperGuarantee⟩ :=
    hgen upperLanguage upperLanguage_in_class
  let stream := adversarialStream gen d
  have hreplayUpper : IsReplaySequence gen upperLanguage stream := by
    exact adversarialStream_replay_upper gen hd
  have hsampleD : (Generic.sample stream d).card = d := by
    exact adversarialStream_sample_seed_card gen d
  have hupperCorrect :
      ∀ s, d ≤ s → Generic.CorrectAt gen upperLanguage stream s := by
    intro s hds
    exact hupperGuarantee stream hreplayUpper d hd hsampleD s hds
  have hrange : (Set.range stream).Infinite := by
    exact adversarialStream_range_infinite hd hupperCorrect
  obtain ⟨e, he, hcutoffGuarantee⟩ :=
    hgen (cutoffLanguage d) (cutoffLanguage_in_class d)
  have hpresents : Generic.Presents stream (Set.range stream) := rfl
  obtain ⟨t, hsampleT⟩ :=
    Generic.exists_sample_card_eq_of_presents_infinite
      hpresents hrange e
  have ht : 0 < t := by
    by_contra hnot
    have ht0 : t = 0 := Nat.eq_zero_of_not_pos hnot
    subst ht0
    have he0 : e = 0 := by
      simpa [Generic.sample] using hsampleT.symm
    exact he.ne' he0
  have hreplayCutoff :
      IsReplaySequence gen (cutoffLanguage d) stream := by
    exact adversarialStream_replay_cutoff gen hd
  have hcutoffCorrect :
      ∀ s, t ≤ s →
        Generic.CorrectAt gen (cutoffLanguage d) stream s := by
    intro s hts
    exact hcutoffGuarantee stream hreplayCutoff t ht
      hsampleT s hts
  let M := max d t
  let code : Fin (d + 1) → Fin d := fun i =>
    ⟨Classical.choose
        (output_mem_finite_intersection
          (gen := gen) (d := d) (t := t) (M := M)
          (s := M + i.val) rfl (Nat.le_add_right M i.val)
          hupperCorrect hcutoffCorrect),
      (Classical.choose_spec
        (output_mem_finite_intersection
          (gen := gen) (d := d) (t := t) (M := M)
          (s := M + i.val) rfl (Nat.le_add_right M i.val)
          hupperCorrect hcutoffCorrect)).1⟩
  have hcodeOutput :
      ∀ i : Fin (d + 1),
        Generic.output gen stream (M + i.val) =
          Sum.inl (code i).val := by
    intro i
    exact (Classical.choose_spec
      (output_mem_finite_intersection
        (gen := gen) (d := d) (t := t) (M := M)
        (s := M + i.val) rfl (Nat.le_add_right M i.val)
        hupperCorrect hcutoffCorrect)).2
  have hcodeInjective : Function.Injective code := by
    intro i j hcode
    apply Fin.ext
    by_contra hij
    have horder : i.val < j.val ∨ j.val < i.val :=
      Nat.lt_or_gt_of_ne hij
    have houtputs :
        Generic.output gen stream (M + i.val) =
          Generic.output gen stream (M + j.val) := by
      rw [hcodeOutput i, hcodeOutput j, hcode]
    rcases horder with hijlt | hjilt
    · have hMjd : d ≤ M + j.val :=
        (Nat.le_max_left d t).trans
          (Nat.le_add_right M j.val)
      have hinputOutput :
          stream (M + i.val) =
            Generic.output gen stream (M + i.val) := by
        exact adversarialStream_eq_output gen d
          ((Nat.le_max_left d t).trans
            (Nat.le_add_right M i.val))
      have hearlier :
          stream (M + i.val) ∈
            Generic.sample stream (M + j.val) := by
        exact Generic.mem_sample_iff.mpr
          ⟨M + i.val, Nat.add_lt_add_left hijlt M, rfl⟩
      have hfresh := (hupperCorrect (M + j.val) hMjd).2
      rw [hinputOutput, houtputs] at hearlier
      exact hfresh hearlier
    · have hMid : d ≤ M + i.val :=
        (Nat.le_max_left d t).trans
          (Nat.le_add_right M i.val)
      have hinputOutput :
          stream (M + j.val) =
            Generic.output gen stream (M + j.val) := by
        exact adversarialStream_eq_output gen d
          ((Nat.le_max_left d t).trans
            (Nat.le_add_right M j.val))
      have hearlier :
          stream (M + j.val) ∈
            Generic.sample stream (M + i.val) := by
        exact Generic.mem_sample_iff.mpr
          ⟨M + j.val, Nat.add_lt_add_left hjilt M, rfl⟩
      have hfresh := (hupperCorrect (M + i.val) hMid).2
      rw [hinputOutput, ← houtputs] at hearlier
      exact hfresh hearlier
  have hcard := Fintype.card_le_of_injective code hcodeInjective
  simp only [Fintype.card_fin] at hcard
  omega

/-- The full separation claimed by Theorem 5.1, reusing the checked
countable-class upper bound for the ordinary model. -/
theorem theorem_5_1 :
    NonuniformlyGeneratable nonuniformHardClass ∧
      ¬NonuniformlyGeneratableWithReplay nonuniformHardClass := by
  constructor
  · exact countable_classes_are_nonuniformly_generatable
      nonuniformHardClass_uus nonuniformHardClass_countable
  · exact theorem_5_1_not_nonuniformlyGeneratableWithReplay

end Replay
end GenLimit
