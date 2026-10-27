import GenLimit.Paper03_HallucinationAndModeCollapse.LabeledIdentificationModel
import GenLimit.Paper03_HallucinationAndModeCollapse.IdentificationLowerBound

/-!
# The labeled exponential lower bound (Lemma 8.2)

Push a full-support domain law through the correct labeling map. Two distinct
targets sharing a positive point then have valid labeled laws with at least
half their mass at the same labeled atom. The all-common-atom sample and
infinite pigeonhole argument give a fixed hard law for every randomized
learner. Unlike a positive-only distribution, the marginal covers the whole
domain, including every negative point.
-/

namespace GenLimit.HallucinationModeCollapse

open GenLimit.Generic GenLimit.DiscreteIID Filter

noncomputable def correctlyLabel (C : Generic.LanguageFamily ℕ) (i x : ℕ) : LabeledDatum := by
  classical
  exact (x, decide (x ∈ C i))

theorem correctlyLabel_correct (C : Generic.LanguageFamily ℕ) (i x : ℕ) :
    CorrectLabel C i (correctlyLabel C i x) := by
  classical
  simp [CorrectLabel, correctlyLabel]

theorem correctlyLabel_pos (C : Generic.LanguageFamily ℕ) (i x : ℕ) (hx : x ∈ C i) :
    correctlyLabel C i x = (x, true) := by
  classical
  simp [correctlyLabel, hx]

theorem correctlyLabeledLaw_valid (C : Generic.LanguageFamily ℕ) (i : ℕ)
    (p : PMF ℕ) (hp : p.support = Set.univ) :
    ValidLabeledDistribution C i (p.map (correctlyLabel C i)) := by
  classical
  apply Set.ext
  intro z
  change z ∈ (p.map (correctlyLabel C i)).support ↔ CorrectLabel C i z
  rw [PMF.mem_support_map_iff]
  constructor
  · rintro ⟨x, _, rfl⟩
    exact correctlyLabel_correct C i x
  · intro hz
    refine ⟨z.1, ?_, ?_⟩
    · rw [hp]; trivial
    · apply Prod.ext
      · rfl
      · apply Bool.eq_iff_iff.mpr
        simpa [correctlyLabel] using hz.symm

theorem labeledLaw_atom_ge (C : Generic.LanguageFamily ℕ) (i : ℕ) (p : PMF ℕ) (x : ℕ) :
    (p x).toReal ≤ ((p.map (correctlyLabel C i)) (correctlyLabel C i x)).toReal := by
  classical
  apply ENNReal.toReal_mono (PMF.apply_ne_top _ _)
  rw [PMF.map_apply]
  calc
    p x = _ := (if_pos rfl).symm
    _ ≤ _ := ENNReal.le_tsum x

theorem labeledIdentificationError_heavyAtom (C : Generic.LanguageFamily ℕ) (A : LabeledIdentifier)
    (p : PMF LabeledDatum) (i : ℕ) (z : LabeledDatum) (n : ℕ)
    (hp : (1 / 2 : ℝ) ≤ (p z).toReal)
    (hA : (1 / 2 : ℝ) ≤ probability (A (List.replicate n z)) {k | C k ≠ C i}) :
    (1 / 2 : ℝ) ^ (n + 1) ≤ labeledIdentificationError C A p i n := by
  have hmass : (1 / 2 : ℝ) ^ n ≤ (samples p n (List.replicate n z)).toReal := by
    rw [samples_replicate, ENNReal.toReal_pow]
    exact pow_le_pow_left₀ (by norm_num) hp n
  calc
    _ = (1 / 2 : ℝ) ^ n * (1 / 2) := pow_succ _ _
    _ ≤ (samples p n (List.replicate n z)).toReal *
        probability (A (List.replicate n z)) {k | C k ≠ C i} :=
      mul_le_mul hmass hA (by norm_num) ENNReal.toReal_nonneg
    _ ≤ _ := probability_bind_ge (samples p n) A {k | C k ≠ C i} (List.replicate n z)

/-- Lemma 8.2: one fixed valid labeled law has exponential error infinitely
often, even for a randomized learner. The source's identification
nontriviality assumption is retained. -/
theorem lemma_8_2 (C : Generic.LanguageFamily ℕ) (hC : NontrivialCollection C)
    (A : LabeledIdentifier) :
    ∃ i p, ValidLabeledDistribution C i p ∧
      ∃ᶠ n : ℕ in atTop, Real.exp (-2 * (n : ℝ)) ≤ labeledIdentificationError C A p i n := by
  obtain ⟨i, j, x, hij, hxi, hxj⟩ := hC
  obtain ⟨r, hr, hrx⟩ := exists_fullSupport_heavyAtom Set.univ x (Set.mem_univ x)
  let p := r.map (correctlyLabel C i)
  let q := r.map (correctlyLabel C j)
  have hp : ValidLabeledDistribution C i p := correctlyLabeledLaw_valid C i r hr
  have hq : ValidLabeledDistribution C j q := correctlyLabeledLaw_valid C j r hr
  have hpx : (1 / 2 : ℝ) ≤ (p (x, true)).toReal := by
    simpa [p, correctlyLabel_pos C i x hxi] using hrx.trans (labeledLaw_atom_ge C i r x)
  have hqx : (1 / 2 : ℝ) ≤ (q (x, true)).toReal := by
    simpa [q, correctlyLabel_pos C j x hxj] using hrx.trans (labeledLaw_atom_ge C j r x)
  have hf : ∃ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) ^ (n + 1) ≤ labeledIdentificationError C A p i n ∨
      (1 / 2 : ℝ) ^ (n + 1) ≤ labeledIdentificationError C A q j n := by
    apply Frequently.of_forall
    intro n
    rcases twoTarget_conditional_error C (fun _ => A (List.replicate n (x, true))) i j hij [] with hi | hj
    · exact Or.inl (labeledIdentificationError_heavyAtom C A p i (x, true) n hpx hi)
    · exact Or.inr (labeledIdentificationError_heavyAtom C A q j (x, true) n hqx hj)
  rcases frequently_or_distrib.mp hf with hi | hj
  · refine ⟨i, p, hp, ?_⟩
    exact (hi.and_eventually (eventually_atTop.mpr ⟨1, fun _ h => h⟩)).mono
      (fun n h => (exp_neg_two_le_half_pow n h.2).trans h.1)
  · refine ⟨j, q, hq, ?_⟩
    exact (hj.and_eventually (eventually_atTop.mpr ⟨1, fun _ h => h⟩)).mono
      (fun n h => (exp_neg_two_le_half_pow n h.2).trans h.1)

end GenLimit.HallucinationModeCollapse
