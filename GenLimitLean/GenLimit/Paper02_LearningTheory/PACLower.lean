import GenLimit.Paper02_LearningTheory.PACModel

/-! # Distribution-free lower bound on a shattered finite set -/

namespace GenLimit.LiRamanTewari

open GenLimit.DiscreteIID

private theorem uniform_probability [Fintype α] [Nonempty α] (E : Set α) [Fintype E] :
    probability (PMF.uniformOfFintype α) E = (Fintype.card E : ℝ) / Fintype.card α := by
  rw [probability, PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]

private theorem bind_probability_le (p : PMF α) (q : α → PMF β) (E : Set β) {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ x ∈ p.support, probability (q x) E ≤ r) :
    probability (p.bind q) E ≤ r := by
  have hu (x) (hx : x ∈ p.support) : (q x).toOuterMeasure E ≤ ENNReal.ofReal r := by
    rw [← ENNReal.toReal_le_toReal (event_ne_top _ _) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hr]
    exact h x hx
  have hb : (p.bind q).toOuterMeasure E ≤ ENNReal.ofReal r := by
    rw [PMF.toOuterMeasure_bind_apply]
    calc
      _ ≤ ∑' x, p x * ENNReal.ofReal r := by
        apply ENNReal.tsum_le_tsum
        intro x
        by_cases hx : p x = 0
        · simp [hx]
        · exact mul_le_mul_left' (hu x hx) _
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  simpa [probability, ENNReal.toReal_ofReal hr] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

/-- Flip exactly the labels that the sample did not reveal. -/
private def flipUnseen {d : ℕ} (xs : List (Fin d)) (b : Fin d → Bool) (i : Fin d) :=
  if i ∈ xs then b i else !(b i)

private theorem flip_involutive {d : ℕ} (xs : List (Fin d)) :
    Function.Involutive (flipUnseen xs) := by
  intro b
  funext i
  by_cases h : i ∈ xs <;> simp [flipUnseen,h]

private theorem flip_sample {d : ℕ} (xs : List (Fin d)) (b : Fin d → Bool) :
    labeledSample (flipUnseen xs b) xs = labeledSample b xs := by
  apply List.map_congr_left
  intro i hi
  simp [flipUnseen,hi]

private theorem small_good_fraction (n : ℕ) (A : PACPredictor (Fin (4*n+1)))
    (xs : List (Fin (4*n+1))) (hx : xs.length = n) :
    let u := PMF.uniformOfFintype (Fin (4*n+1))
    let v := PMF.uniformOfFintype (Fin (4*n+1) → Bool)
    probability v {b | predictionRisk u (A (labeledSample b xs)) b ≤ 1/8} ≤ 1/2 := by
  classical
  let d := 4*n+1
  let u := PMF.uniformOfFintype (Fin (4*n+1))
  let Good : Set (Fin d → Bool) := {b | predictionRisk u (A (labeledSample b xs)) b ≤ 1/8}
  have flip_bad (b) (hb : b ∈ Good) : flipUnseen xs b ∉ Good := by
    intro hbad
    let f := A (labeledSample b xs)
    let err (g : Fin d → Bool) := {i | f i ≠ g i}
    change probability u (err b) ≤ 1/8 at hb
    change predictionRisk u (A (labeledSample (flipUnseen xs b) xs)) (flipUnseen xs b) ≤ 1/8 at hbad
    rw [flip_sample] at hbad
    change probability u (err (flipUnseen xs b)) ≤ 1/8 at hbad
    have hu : {i : Fin d | i ∈ xs}ᶜ ⊆ err b ∪ err (flipUnseen xs b) := by
      intro i hi
      change i ∉ xs at hi
      change f i ≠ b i ∨ f i ≠ flipUnseen xs b i
      simp only [flipUnseen, if_neg hi]
      cases f i <;> cases b i <;> decide
    have h := (probability_mono u hu).trans (probability_union_le _ _ _)
    rw [probability_compl] at h
    have seen : probability u {i : Fin d | i ∈ xs} ≤ (n : ℝ) / d := by
      rw [uniform_probability,Fintype.card_fin]
      apply div_le_div_of_nonneg_right _ (by positivity)
      let intoSeen : ↥({i : Fin d | i ∈ xs} : Set _) → ↥xs.toFinset :=
        fun i => ⟨i.1,List.mem_toFinset.mpr i.2⟩
      have hcard := Fintype.card_le_of_injective intoSeen (fun _ _ h => Subtype.ext (congrArg (fun z : ↥xs.toFinset => z.val) h))
      rw [Fintype.card_coe] at hcard
      exact_mod_cast (hcard.trans (xs.toFinset_card_le.trans_eq hx))
    have hratio : (n : ℝ) / d ≤ 1/4 := by
      dsimp [d]
      rw [div_le_iff₀ (by positivity)]
      push_cast
      linarith
    linarith
  let emb : Good → ↥Goodᶜ := fun b => ⟨flipUnseen xs b.1,flip_bad b.1 b.2⟩
  have hle := Fintype.card_le_of_injective emb (fun a b h =>
    Subtype.ext ((flip_involutive xs).injective (congrArg Subtype.val h)))
  rw [Fintype.card_compl_set] at hle
  have hc : 2 * Fintype.card Good ≤ Fintype.card (Fin d → Bool) := by
    have := Fintype.card_le_of_injective (Subtype.val : Good → _) Subtype.val_injective
    omega
  change probability (PMF.uniformOfFintype (Fin d → Bool)) Good ≤ 1/2
  rw [uniform_probability, div_le_iff₀ (by exact_mod_cast Fintype.card_pos)]
  have hr : (2 : ℝ) * Fintype.card Good ≤ Fintype.card (Fin d → Bool) := by exact_mod_cast hc
  linarith

private theorem finite_hard_distribution (n : ℕ) (A : PACPredictor (Fin (4*n+1))) :
    let u := PMF.uniformOfFintype (Fin (4*n+1))
    ∃ b : Fin (4*n+1) → Bool, (1/8 : ℝ) < probability (samples u n)
      {xs | 1/8 < predictionRisk u (A (labeledSample b xs)) b} := by
  classical
  let u := PMF.uniformOfFintype (Fin (4*n+1))
  let v := PMF.uniformOfFintype (Fin (4*n+1) → Bool)
  let draws := samples u n
  let bad (b : Fin (4*n+1) → Bool) (xs : List (Fin (4*n+1))) : Bool :=
    decide ((1/8 : ℝ) < predictionRisk u (A (labeledSample b xs)) b)
  let law := v.bind (fun b => draws.map (bad b))
  have swap : law = draws.bind (fun xs => v.map (fun b => bad b xs)) :=
    PMF.bind_comm v draws (fun b xs => PMF.pure (bad b xs))
  change ∃ b, (1/8 : ℝ) < probability draws {xs | 1/8 < predictionRisk u (A (labeledSample b xs)) b}
  by_contra! hn
  have hbad : probability law {true} ≤ 1/8 := by
    apply bind_probability_le v _ _ (by norm_num)
    intro b _
    rw [probability_map_preimage]
    simpa [bad,Set.preimage] using hn b
  have hgood : probability law ({true} : Set Bool)ᶜ ≤ 1/2 := by
    rw [swap]
    apply bind_probability_le draws _ _ (by norm_num)
    intro xs hs
    rw [probability_map_preimage]
    have he : (fun b => bad b xs) ⁻¹' ({true} : Set Bool)ᶜ =
        {b | predictionRisk u (A (labeledSample b xs)) b ≤ 1/8} := by
      ext b
      simp [bad]
    rw [he]
    exact small_good_fraction n A xs ((samples_support u n xs).mp hs).1
  rw [probability_compl] at hgood
  linarith

/-- Arbitrarily large shattered finite samples rule out Definition 2.8
even for improper learners. The marginal is uniform on a shattered set. -/
theorem not_pacLearnable_of_infiniteVC {H : Generic.LanguageClass α}
    (hv : HasInfiniteVCDimension H) : ¬PACLearnable H := by
  classical
  rintro ⟨A,hA⟩
  obtain ⟨n,hn⟩ := hA (1/8) (by norm_num) (by norm_num) (1/8) (by norm_num) (by norm_num)
  obtain ⟨feature,shat⟩ := hv (4*n+1)
  let u := PMF.uniformOfFintype (Fin (4*n+1))
  let B : PACPredictor (Fin (4*n+1)) := fun pairs i =>
    A (pairs.map fun q => (feature q.1,q.2)) (feature i)
  obtain ⟨b,hb⟩ := finite_hard_distribution n B
  obtain ⟨K,hK,hagree⟩ := shat b
  have eq (i) : languageLabel K (feature i) = b i := by
    cases e : b i <;> simp_all [languageLabel]
  have h := hn n le_rfl (u.map feature) K hK
  rw [samples_map, probability_map_preimage] at h
  apply (not_lt_of_ge h) (lt_of_lt_of_eq hb ?_)
  congr 1
  ext xs
  change (1/8 : ℝ) < predictionRisk u (B (labeledSample b xs)) b ↔
    (1/8 : ℝ) < predictionRisk (u.map feature) (A (labeledSample (languageLabel K) (xs.map feature))) (languageLabel K)
  have lab : labeledSample (languageLabel K) (xs.map feature) =
      (labeledSample b xs).map (fun q => (feature q.1,q.2)) := by
    simp [labeledSample,List.map_map,Function.comp_def,eq]
  rw [lab, predictionRisk, predictionRisk, probability_map_preimage]
  simp [Set.preimage, B,eq]

end GenLimit.LiRamanTewari
