import GenLimit.Paper02_LearningTheory.PACModel

/-! # PAC upper bounds for the threshold and block witnesses of Theorem 4.1 -/

namespace GenLimit.LiRamanTewari

open GenLimit.DiscreteIID Filter
open scoped Topology

/-- Predict the union of the regions forced by observed positive labels. -/
noncomputable def positiveClosurePredictor (region : α → Set α) : PACPredictor α := fun pairs =>
  languageLabel {y | ∃ x, (x,true) ∈ pairs ∧ y ∈ region x}

private def learned (region : α → Set α) (K : Set α) (xs : List α) : Set α :=
  {y | ∃ x ∈ xs, x ∈ K ∧ y ∈ region x}

private theorem trained_predicts (region : α → Set α) (K : Set α) (xs : List α) :
    positiveClosurePredictor region (labeledSample (languageLabel K) xs) =
      languageLabel (learned region K xs) := by
  classical
  ext y
  simp [positiveClosurePredictor,languageLabel,labeledSample,learned, and_assoc]

/-- A low-rank positive example certifies that the missing mass in one
ordered piece is at most η. If every finite initial segment has mass at
most η, any example from this piece supplies the certificate. -/
private theorem piece_error_bound (region : α → Set α) (K P : Set α) (rank : α → ℕ)
    (hPK : P ⊆ K) (hcover : ∀ x ∈ P, ∀ y ∈ P, rank x ≤ rank y → y ∈ region x)
    (p : PMF α) (n : ℕ) {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    probability (samples p n) {xs | η < probability p (P \ learned region K xs)} ≤ (1-η)^n := by
  classical
  by_cases hP : probability p P ≤ η
  · have he : {xs : List α | η < probability p (P \ learned region K xs)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro xs
      exact not_lt_of_ge ((probability_mono p Set.diff_subset).trans hP)
    rw [he]
    have hz : probability (samples p n) ∅ = 0 := by simp [probability]
    rw [hz]
    exact pow_nonneg (sub_nonneg.mpr hη1) n
  have witness : ∃ E : Set α, η < probability p E ∧ E ⊆ P ∧
      ∀ x ∈ E, probability p {y | y ∈ P ∧ rank y < rank x} ≤ η := by
    let seg := fun k => {y | y ∈ P ∧ rank y ≤ k}
    by_cases hex : ∃ k, η < probability p (seg k)
    · let k := Nat.find hex
      refine ⟨seg k,Nat.find_spec hex,fun y hy => hy.1,fun x hx => ?_⟩
      by_cases h0 : rank x = 0
      · simp [h0,probability,hη]
      · have hm : rank x - 1 < k := by have := hx.2; omega
        apply (probability_mono p (F := seg (rank x - 1)) (fun y hy => ⟨hy.1,by have : rank y < rank x := hy.2; omega⟩)).trans
        exact le_of_not_gt (Nat.find_min hex hm)
    · refine ⟨P,lt_of_not_ge hP,Set.Subset.rfl,fun x _ => ?_⟩
      exact (probability_mono p (F := seg (rank x)) (fun y hy => ⟨hy.1,hy.2.le⟩)).trans
        (le_of_not_gt (fun h => hex ⟨_,h⟩))
  obtain ⟨E,hE,hEP,hcert⟩ := witness
  have hsub : {xs | η < probability p (P \ learned region K xs)} ⊆
      {xs : List α | ∀ x ∈ xs, x ∈ Eᶜ} := by
    intro xs hfail x hxs hx
    apply (not_lt_of_ge ((probability_mono p (F := {y | y ∈ P ∧ rank y < rank x}) ?_).trans (hcert x hx))) hfail
    rintro y ⟨hy,hn⟩
    refine ⟨hy,lt_of_not_ge (fun h => hn ⟨x,hxs,hPK (hEP hx),hcover x (hEP hx) y hy h⟩)⟩
  apply (probability_mono (samples p n) hsub).trans
  change ((samples p n).toOuterMeasure _).toReal ≤ _
  rw [samples_all,ENNReal.toReal_pow]
  change (probability p Eᶜ)^n ≤ _
  rw [probability_compl]
  exact pow_le_pow_left₀ (sub_nonneg.mpr (probability_le_one _ _)) (by linarith) _

/-- A class learned by positive closures is PAC learnable if each target
splits into at most two such ordered pieces. The sample guarantee is uniform
over the target and the distribution. -/
theorem pacLearnable_of_two_pieces (H : Generic.LanguageClass α) (region : α → Set α)
    (sound : ∀ K ∈ H, ∀ x ∈ K, region x ⊆ K)
    (pieces : ∀ K ∈ H, ∃ P Q : Set α, ∃ r s : α → ℕ, K = P ∪ Q ∧
      (∀ x ∈ P, ∀ y ∈ P, r x ≤ r y → y ∈ region x) ∧
      (∀ x ∈ Q, ∀ y ∈ Q, s x ≤ s y → y ∈ region x)) : PACLearnable H := by
  classical
  refine ⟨positiveClosurePredictor region,fun ε hε hε1 δ hδ _ => ?_⟩
  let η := ε/2
  have hη : 0 ≤ η := by dsimp [η]; linarith
  have hη1 : η ≤ 1 := by dsimp [η]; linarith
  have lim : Tendsto (fun n : ℕ => (1-η)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by dsimp [η]; linarith)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (lim.eventually_lt_const (show 0 < δ/2 by linarith))
  refine ⟨N,fun n hn p K hK => ?_⟩
  obtain ⟨P,Q,r,s,eq,hP,hQ⟩ := pieces K hK
  let LP := fun xs => learned region K xs
  have hs (xs) : LP xs ⊆ K := by
    rintro y ⟨x,_,hx,hy⟩
    exact sound K hK x hx hy
  have loss (xs) : predictionRisk p (positiveClosurePredictor region (labeledSample (languageLabel K) xs))
      (languageLabel K) = probability p (K \ LP xs) := by
    rw [trained_predicts, predictionRisk]
    congr 1
    ext x
    have := @hs xs x
    simp [languageLabel,LP] at *
    tauto
  let miss := fun (T : Set α) => {xs : List α | η < probability p (T \ LP xs)}
  have split : {xs | ε < predictionRisk p (positiveClosurePredictor region (labeledSample (languageLabel K) xs))
        (languageLabel K)} ⊆ miss P ∪ miss Q := by
    intro xs h
    rw [Set.mem_setOf_eq,loss,eq,Set.union_diff_distrib] at h
    have hlarge := h.trans_le (probability_union_le _ _ _)
    change η < _ ∨ η < _
    dsimp [η]
    by_contra! hsmall
    linarith [hsmall.1,hsmall.2]
  have h₁ := piece_error_bound region K P r (eq ▸ Set.subset_union_left) hP p n hη hη1
  have h₂ := piece_error_bound region K Q s (eq ▸ Set.subset_union_right) hQ p n hη hη1
  calc
    _ ≤ _ := probability_mono (samples p n) split
    _ ≤ _ := probability_union_le _ _ _
    _ ≤ δ := by
      change probability (samples p n) {xs | η < probability p (P \ learned region K xs)} +
        probability (samples p n) {xs | η < probability p (Q \ learned region K xs)} ≤ δ
      linarith [hN n hn]

theorem thresholdClass_pacLearnable : PACLearnable thresholdClass := by
  apply pacLearnable_of_two_pieces _ (fun x => Set.Ici x)
  · rintro _ ⟨a,rfl⟩ x hx y hy
    exact Nat.le_trans hx hy
  · rintro _ ⟨a,rfl⟩
    exact ⟨thresholdLanguage a,∅,id,id,by simp,fun _ _ _ _ h => h,by simp⟩

private def blockRegion : BlockUniverse → Set BlockUniverse
  | Sum.inl (d,_) => blockSet d
  | Sum.inr (b,_) => blockTail b

private theorem blockRegion_from_block {d : ℕ} {x : BlockUniverse} (h : x ∈ blockSet d) :
    blockRegion x = blockSet d := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
  rfl

private theorem blockRegion_from_tail {b : Bool} {x : BlockUniverse} (h : x ∈ blockTail b) :
    blockRegion x = blockTail b := by
  obtain ⟨j,rfl⟩ := h
  rfl

private def mixedRegion : ThresholdBlockUniverse → Set ThresholdBlockUniverse
  | Sum.inl x => liftLeftLanguage (Set.Ici x)
  | Sum.inr x => liftRightLanguage (blockRegion x)

private def leftRank : ThresholdBlockUniverse → ℕ
  | Sum.inl x => x
  | Sum.inr _ => 0

private theorem piece_valid_left {a : ℕ} {x y : ThresholdBlockUniverse}
    (hx : x ∈ liftLeftLanguage (thresholdLanguage a)) (hxy : y ∈ mixedRegion x) :
    y ∈ liftLeftLanguage (thresholdLanguage a) := by
  cases x with
  | inr _ => exact False.elim hx
  | inl x =>
    cases y with
    | inr _ => exact False.elim hxy
    | inl y => exact Nat.le_trans hx hxy

private theorem same_right_region (P : Set BlockUniverse)
    (h : ∀ x ∈ P, blockRegion x = P) (x : ThresholdBlockUniverse) (hx : x ∈ liftRightLanguage P) :
    mixedRegion x = liftRightLanguage P := by
  cases x with
  | inl _ => exact False.elim hx
  | inr x => exact congrArg liftRightLanguage (h x hx)

theorem thresholdBlockClass_pacLearnable : PACLearnable thresholdBlockClass := by
  apply pacLearnable_of_two_pieces _ mixedRegion
  · rintro K (⟨_,⟨a,rfl⟩,rfl⟩ | ⟨_,⟨⟨b,d⟩,rfl⟩,rfl⟩) x hx y hy
    · exact piece_valid_left hx hy
    · cases x with
      | inl _ => exact False.elim hx
      | inr x =>
        change x ∈ blockSet d ∪ blockTail b at hx
        cases y with
        | inl _ => exact False.elim hy
        | inr y =>
          change y ∈ blockRegion x at hy
          rcases hx with h | h
          · exact Or.inl (blockRegion_from_block h ▸ hy)
          · exact Or.inr (blockRegion_from_tail h ▸ hy)
  · rintro K (⟨_,⟨a,rfl⟩,rfl⟩ | ⟨_,⟨⟨b,d⟩,rfl⟩,rfl⟩)
    · refine ⟨_,∅,leftRank,leftRank,(Set.union_empty _).symm,?_,by simp⟩
      intro x hx y hy hxy
      cases x <;> cases y <;> first | exact False.elim hx | exact False.elim hy | exact hxy
    · refine ⟨liftRightLanguage (blockSet d),liftRightLanguage (blockTail b),fun _ => 0,fun _ => 0,?_,?_,?_⟩
      · ext x
        cases x <;> simp [blockLanguage,liftRightLanguage]
      · intro x hx y hy _
        rwa [same_right_region _ (fun _ h => blockRegion_from_block h) x hx]
      · intro x hx y hy _
        rwa [same_right_region _ (fun _ h => blockRegion_from_tail h) x hx]

end GenLimit.LiRamanTewari
