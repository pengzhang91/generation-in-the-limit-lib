import GenLimit.Paper30_TimeSensitiveLanguageGeneration.Definitions
import GenLimit.Support.Asymptotics.Liminf
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Deterministic density reductions

This file formalizes the finite, pathwise bookkeeping in Lemma 2
(Appendix-D Lemma 5) and Appendix-C Lemma 4 of
Ganju--McVoy--Dughmi--Teng, arXiv:2605.11302v2.

The analytic construction of the slowed deadline and the randomized
black-box generator are outside this module.  The results here are the exact
inequalities to which those asymptotic and probabilistic arguments reduce.
-/

namespace GenLimit.TimeSensitive

open Filter

/-- Element-wise credit is contained in prefix-wise credit at the current
deadline whenever deadlines are monotone.  This is the inequality
`μ_i ≤ μ_i^pfx` used at the end of Appendix-C Lemma 4. -/
theorem timelyElements_subset_prefixWiseElements
    (S R : ℕ → α) (D : Deadline) (i : ℕ) :
    timelyElements S R D i ⊆ prefixWiseElements S R D i := by
  classical
  intro x hx
  simp only [timelyElements, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range] at hx
  obtain ⟨j, ⟨hji, hjout⟩, rfl⟩ := hx
  have htarget : R j ∈ targetPrefix R i :=
    (mem_sequencePrefix_iff R (R j) i).mpr ⟨j, hji, rfl⟩
  have hdeadline : D j ≤ D i :=
    D.monotone' (Nat.le_of_lt hji)
  have hout : R j ∈ sequencePrefix S (D i) :=
    sequencePrefix_mono S hdeadline hjout
  exact Finset.mem_inter.mpr ⟨htarget, hout⟩

theorem timelyElements_card_le_prefixWiseElements_card
    (S R : ℕ → α) (D : Deadline) (i : ℕ) :
    (timelyElements S R D i).card ≤
      (prefixWiseElements S R D i).card := by
  classical
  exact Finset.card_le_card
    (timelyElements_subset_prefixWiseElements S R D i)

theorem timelyDensity_le_prefixWiseDensity
    (S R : ℕ → α) (D : Deadline) (i : ℕ) :
    timelyDensity S R D i ≤ prefixWiseDensity S R D i := by
  by_cases hi : i = 0
  · simp [timelyDensity, prefixWiseDensity, hi]
  · simp only [timelyDensity, prefixWiseDensity, hi, if_false]
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast
        timelyElements_card_le_prefixWiseElements_card S R D i)
      (Nat.cast_nonneg i)

theorem timelyDensity_nonneg
    (S R : ℕ → α) (D : ℕ → ℕ) (i : ℕ) :
    0 ≤ timelyDensity S R D i := by
  unfold timelyDensity
  split <;> positivity

theorem timelyDensity_le_one
    (S R : ℕ → α) (D : ℕ → ℕ) (i : ℕ) :
    timelyDensity S R D i ≤ 1 := by
  by_cases hi : i = 0
  · simp [timelyDensity, hi]
  · simp only [timelyDensity, hi, if_false]
    have hiReal : (0 : ℝ) < i := by
      exact_mod_cast Nat.pos_of_ne_zero hi
    rw [div_le_one hiReal]
    have hcard :
        (timelyElements S R D i).card ≤ i := by
      classical
      unfold timelyElements
      exact
        (Finset.card_image_le.trans
          (Finset.card_filter_le _ _)).trans_eq
            (Finset.card_range i)
    exact_mod_cast hcard

theorem prefixWiseDensity_nonneg
    (S R : ℕ → α) (F : ℕ → ℕ) (i : ℕ) :
    0 ≤ prefixWiseDensity S R F i := by
  unfold prefixWiseDensity
  split <;> positivity

theorem prefixWiseDensity_le_one
    (S R : ℕ → α) (F : ℕ → ℕ) (i : ℕ) :
    prefixWiseDensity S R F i ≤ 1 := by
  by_cases hi : i = 0
  · simp [prefixWiseDensity, hi]
  · simp only [prefixWiseDensity, hi, if_false]
    have hiReal : (0 : ℝ) < i := by
      exact_mod_cast Nat.pos_of_ne_zero hi
    rw [div_le_one hiReal]
    have hcard : (prefixWiseElements S R F i).card ≤ i := by
      classical
      unfold prefixWiseElements targetPrefix sequencePrefix
      exact (Finset.card_le_card Finset.inter_subset_left).trans
        (Finset.card_image_le.trans_eq (Finset.card_range i))
    exact_mod_cast hcard

/-- Exact finite-prefix core of Appendix-D Lemma 5.

If at most the first `r` target positions have a deadline earlier than the
common prefix cutoff `F i`, then every prefix-wise credited string except
possibly those `r` strings is element-wise timely. -/
theorem prefixWiseElements_subset_timely_union_early
    (S R : ℕ → α)
    (D F : ℕ → ℕ) (i r : ℕ)
    (hcutoff :
      ∀ j, j < i → r ≤ j → F i ≤ D j) :
    ∀ x, x ∈ prefixWiseElements S R F i →
      x ∈ timelyElements S R D i ∨ x ∈ targetPrefix R r := by
  classical
  intro x hx
  by_cases hearly : x ∈ targetPrefix R r
  · exact Or.inr hearly
  · apply Or.inl
    have htarget := (Finset.mem_inter.mp hx).1
    have hout := (Finset.mem_inter.mp hx).2
    obtain ⟨j, hji, hjx⟩ :=
      (mem_sequencePrefix_iff R x i).mp htarget
    have hrj : r ≤ j := by
      by_contra hnot
      have hjr : j < r := Nat.lt_of_not_ge hnot
      exact hearly
        ((mem_sequencePrefix_iff R x r).mpr ⟨j, hjr, hjx⟩)
    have hout' : x ∈ sequencePrefix S (D j) :=
      sequencePrefix_mono S (hcutoff j hji hrj) hout
    simp only [timelyElements, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨j, ⟨hji, hjx ▸ hout'⟩, hjx⟩

/-- Cardinal form of the finite-prefix reduction:
`prefix-credit ≤ element-credit + r`. -/
theorem prefixWise_card_le_timely_card_add
    (S R : ℕ → α) (hR : Function.Injective R)
    (D F : ℕ → ℕ) (i r : ℕ)
    (hcutoff :
      ∀ j, j < i → r ≤ j → F i ≤ D j) :
    (prefixWiseElements S R F i).card ≤
      (timelyElements S R D i).card + r := by
  classical
  have hsubset :
      prefixWiseElements S R F i ⊆
        timelyElements S R D i ∪ targetPrefix R r := by
    intro x hx
    exact Finset.mem_union.mpr
      (prefixWiseElements_subset_timely_union_early
        S R D F i r hcutoff x hx)
  calc
    (prefixWiseElements S R F i).card
        ≤ (timelyElements S R D i ∪ targetPrefix R r).card :=
      Finset.card_le_card hsubset
    _ ≤ (timelyElements S R D i).card +
          (targetPrefix R r).card :=
      Finset.card_union_le _ _
    _ = (timelyElements S R D i).card + r := by
      rw [targetPrefix, sequencePrefix]
      rw [Finset.card_image_iff.mpr]
      · simp
      · intro a _ b _ hab
        exact hR hab

/-- Ratio form printed in Appendix D.1:
`μ_i ≥ μ_i^pfx - r(i)/i`. -/
theorem prefixWiseDensity_sub_exception_le_timelyDensity
    (S R : ℕ → α) (hR : Function.Injective R)
    (D F : ℕ → ℕ) {i r : ℕ} (hi : 0 < i)
    (hcutoff :
      ∀ j, j < i → r ≤ j → F i ≤ D j) :
    prefixWiseDensity S R F i - (r : ℝ) / i ≤
      timelyDensity S R D i := by
  have hi0 : i ≠ 0 := Nat.ne_of_gt hi
  simp only [prefixWiseDensity, timelyDensity, hi0, if_false]
  have hcard :=
    prefixWise_card_le_timely_card_add S R hR D F i r hcutoff
  have hcardReal :
      ((prefixWiseElements S R F i).card : ℝ) ≤
        (((timelyElements S R D i).card + r : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hiReal : (0 : ℝ) < i := by exact_mod_cast hi
  rw [sub_le_iff_le_add]
  calc
    ((prefixWiseElements S R F i).card : ℝ) / i
        ≤ ((timelyElements S R D i).card + r : ℕ) / (i : ℝ) := by
      exact div_le_div_of_nonneg_right hcardReal hiReal.le
    _ = ((timelyElements S R D i).card : ℝ) / i +
          (r : ℝ) / i := by
      push_cast
      ring

/-! ## Appendix-D's deadline-exception index -/

/-- The zero-based version of Appendix D's
`r(i) = max {j ≤ i : Dₑₗ(j) < Dₚ𝒻ₓ(i)}`.

Because target positions are zero-based in Lean, the number of exceptional
positions is the cardinality of the corresponding filtered prefix.  For a
monotone element-wise deadline those positions form an initial segment, so
this cardinality is also the cutoff used in the paper's density loss
`r(i) / i`. -/
def deadlineExceptionCount
    (D : Deadline) (F : ℕ → ℕ) (i : ℕ) : ℕ :=
  ((Finset.range i).filter fun j => D j < F i).card

theorem deadlineExceptionCount_le
    (D : Deadline) (F : ℕ → ℕ) (i : ℕ) :
    deadlineExceptionCount D F i ≤ i := by
  unfold deadlineExceptionCount
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range i)

/-- Monotonicity makes the early-deadline exceptions an initial segment:
every position at or beyond their count meets the common prefix cutoff. -/
theorem deadlineExceptionCount_cutoff
    (D : Deadline) (F : ℕ → ℕ) (i : ℕ) :
    ∀ j, j < i → deadlineExceptionCount D F i ≤ j →
      F i ≤ D j := by
  intro j hji hrj
  by_contra hnot
  have hjEarly : D j < F i := Nat.lt_of_not_ge hnot
  have hsubset :
      Finset.range (j + 1) ⊆
        (Finset.range i).filter (fun k => D k < F i) := by
    intro k hk
    have hkj : k ≤ j := by
      have hklt : k < j + 1 := Finset.mem_range.mp hk
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (lt_of_le_of_lt hkj hji),
        (D.monotone' hkj).trans_lt hjEarly⟩
  have hcard :
      j + 1 ≤ deadlineExceptionCount D F i := by
    simpa [deadlineExceptionCount] using Finset.card_le_card hsubset
  omega

/-- Appendix-D Lemma 5 with the source-defined exception count rather than
an abstract cutoff hypothesis. -/
theorem prefixWiseDensity_sub_deadlineException_le_timelyDensity
    (S R : ℕ → α) (hR : Function.Injective R)
    (D : Deadline) (F : ℕ → ℕ) {i : ℕ} (hi : 0 < i) :
    prefixWiseDensity S R F i -
        (deadlineExceptionCount D F i : ℝ) / i ≤
      timelyDensity S R D i := by
  exact prefixWiseDensity_sub_exception_le_timelyDensity
    S R hR D F hi (deadlineExceptionCount_cutoff D F i)

/-- The normalized exceptional-prefix loss used in Appendix D. -/
noncomputable def deadlineExceptionRatio
    (D : Deadline) (F : ℕ → ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else (deadlineExceptionCount D F i : ℝ) / i

theorem deadlineExceptionRatio_nonneg
    (D : Deadline) (F : ℕ → ℕ) (i : ℕ) :
    0 ≤ deadlineExceptionRatio D F i := by
  by_cases hi : i = 0
  · simp [deadlineExceptionRatio, hi]
  · simp only [deadlineExceptionRatio, hi, if_false]
    positivity

theorem deadlineExceptionRatio_le_one
    (D : Deadline) (F : ℕ → ℕ) (i : ℕ) :
    deadlineExceptionRatio D F i ≤ 1 := by
  by_cases hi : i = 0
  · simp [deadlineExceptionRatio, hi]
  · simp only [deadlineExceptionRatio, hi, if_false]
    have hiReal : (0 : ℝ) < i := by
      exact_mod_cast Nat.pos_of_ne_zero hi
    rw [div_le_one hiReal]
    exact_mod_cast deadlineExceptionCount_le D F i

/-- Pointwise Appendix-D comparison, totalized at the empty prefix. -/
theorem prefixWiseDensity_le_timelyDensity_add_deadlineExceptionRatio
    (S R : ℕ → α) (hR : Function.Injective R)
    (D : Deadline) (F : ℕ → ℕ) (i : ℕ) :
    prefixWiseDensity S R F i ≤
      timelyDensity S R D i + deadlineExceptionRatio D F i := by
  by_cases hi : i = 0
  · simp [prefixWiseDensity, timelyDensity, deadlineExceptionRatio, hi]
  · have h :=
      prefixWiseDensity_sub_deadlineException_le_timelyDensity
        S R hR D F (Nat.pos_of_ne_zero hi)
    simpa [deadlineExceptionRatio, hi, sub_le_iff_le_add] using h

/-- The deterministic liminf endgame of Appendix-D Lemma 5.

Once the deadline construction supplies `r(i) / i → 0`, the prefix-wise
lower density cannot exceed the original element-wise lower density.  This
theorem isolates exactly the analytic conclusion; constructing the slowed
deadline and proving its exception ratio vanishes remain the paper's
countable-diagonal step. -/
theorem lowerPrefixWiseDensity_le_lowerTimelyDensity_of_exceptionRatio
    (S R : ℕ → α) (hR : Function.Injective R)
    (D : Deadline) (F : ℕ → ℕ)
    (hvanishing :
      Tendsto (deadlineExceptionRatio D F) atTop (nhds 0)) :
    lowerPrefixWiseDensity S R F ≤ lowerTimelyDensity S R D := by
  unfold lowerPrefixWiseDensity lowerTimelyDensity
  exact GenLimit.liminf_le_liminf_of_eventually_le_add_tendsto_zero
    (prefixWiseDensity_nonneg S R F)
    (prefixWiseDensity_le_one S R F)
    (timelyDensity_le_one S R D)
    (Eventually.of_forall
      (prefixWiseDensity_le_timelyDensity_add_deadlineExceptionRatio
        S R hR D F))
    hvanishing

/-- Pathwise finite decomposition in Appendix-C Lemma 4.

Every credited string in the first `i` target positions is either already in
the intermediate language `L`, or is a distinct output outside `L`. -/
theorem prefix_credit_le_target_intersection_add_hallucinations
    (S R : ℕ → α) (L : Set α) (i t : ℕ) :
    (prefixWiseElements S R (fun _ => t) i).card ≤
      targetIntersectionCount R L i + hallucinationCount S L t := by
  classical
  let inside :=
    (targetPrefix R i).filter fun x => x ∈ L
  let outside :=
    (sequencePrefix S t).filter fun x => x ∉ L
  have hsubset :
      prefixWiseElements S R (fun _ => t) i ⊆ inside ∪ outside := by
    intro x hx
    have hx' :
        x ∈ targetPrefix R i ∩ sequencePrefix S t := by
      simpa [prefixWiseElements] using hx
    rcases Finset.mem_inter.mp hx' with ⟨hxR, hxS⟩
    by_cases hxL : x ∈ L
    · exact Finset.mem_union_left _
        (by simpa [inside] using ⟨hxR, hxL⟩)
    · exact Finset.mem_union_right _
        (by simpa [outside] using ⟨hxS, hxL⟩)
  calc
    (prefixWiseElements S R (fun _ => t) i).card
        ≤ (inside ∪ outside).card :=
      Finset.card_le_card hsubset
    _ ≤ inside.card + outside.card :=
      Finset.card_union_le _ _
    _ = targetIntersectionCount R L i +
          hallucinationCount S L t := by
      rfl

/-- Eventual consistency gives a uniform finite bound on the number of
distinct hallucinated outputs.  This is the deterministic implication used
to derive Theorem 1 from the Hallucination Barrier. -/
theorem hallucinationCount_le_burnIn
    (S : ℕ → α) (L : Set α) {T t : ℕ}
    (hvalid : ∀ k, T ≤ k → S k ∈ L) :
    hallucinationCount S L t ≤ T := by
  classical
  have hsubset :
      (sequencePrefix S t).filter (fun x => x ∉ L) ⊆
        sequencePrefix S T := by
    intro x hx
    have hxparts := Finset.mem_filter.mp hx
    obtain ⟨k, hkt, hkx⟩ :=
      (mem_sequencePrefix_iff S x t).mp hxparts.1
    have hkT : k < T := by
      by_contra hnot
      exact hxparts.2 (hkx ▸ hvalid k (Nat.le_of_not_gt hnot))
    exact (mem_sequencePrefix_iff S x T).mpr ⟨k, hkT, hkx⟩
  calc
    hallucinationCount S L t
        ≤ (sequencePrefix S T).card := by
      exact Finset.card_le_card hsubset
    _ ≤ T := by
      unfold sequencePrefix
      simpa only [Finset.card_range] using
        (Finset.card_image_le (s := Finset.range T) (f := S))

/-- Appendix-C's pathwise inequality specialized to an eventually
consistent output sequence. -/
theorem prefix_credit_le_target_intersection_add_burnIn
    (S R : ℕ → α) (L : Set α) {T i t : ℕ}
    (hvalid : ∀ k, T ≤ k → S k ∈ L) :
    (prefixWiseElements S R (fun _ => t) i).card ≤
      targetIntersectionCount R L i + T := by
  exact
    (prefix_credit_le_target_intersection_add_hallucinations
      S R L i t).trans
      (Nat.add_le_add_left
        (hallucinationCount_le_burnIn S L hvalid) _)

end GenLimit.TimeSensitive
