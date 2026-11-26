import GenLimit.Paper24_PriceOfPrivacy.CommonAtom
import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.FiniteExperiments
import GenLimit.Support.EnumerationProgress

/-! The intersecting infinite-difference pair lower bound, Theorem 5.4. -/

namespace GenLimit.PriceOfPrivacy

open AgnosticLanguage DiscreteIID Set
open scoped ENNReal Classical
noncomputable section

/-- Definition 5.3. The two differences may contain words shared with other
languages in the collection. -/
def IntersectingInfiniteDifferencePair (C : Generic.LanguageFamily X) : Prop :=
  ∃ i j, (C i ∩ C j).Nonempty ∧ (C i \ C j).Infinite ∧ (C j \ C i).Infinite

theorem joint_output_event (A : StatisticalGenerator X) (p : PMF X) (n : ℕ)
    (F : Set X) : probability (joint A p n) (Prod.snd ⁻¹' F) =
      probability ((samples p n).bind A) F := by
  unfold probability
  rw [← PMF.toOuterMeasure_map_apply]
  have he : (joint A p n).map Prod.snd = (samples p n).bind A := by
    simp only [joint,PMF.map_bind,PMF.map_comp]
    congr 1
    funext xs
    exact (A xs).map_id
  rw [he]

private theorem failure_off_tail (A : StatisticalGenerator X) (p : PMF X)
    (a : X) (F : Set X) (support : p.support = insert a F) (n : ℕ) :
    probability ((samples p n).bind A) Fᶜ ≤
      genErr A p n + (1 - (p a).toReal)^n := by
  let bad : Set (List X × X) := {z | z.2 ∉ p.support ∨ z.2 ∈ z.1}
  let missing : Set (List X) := {xs | a ∉ xs}
  have sub : Prod.snd ⁻¹' Fᶜ ⊆ bad ∪ Prod.fst ⁻¹' missing := by
    rintro ⟨xs,y⟩ (off : y ∉ F)
    by_cases absent : a ∉ xs
    · exact Or.inr absent
    · apply Or.inl
      by_cases hs : y ∈ p.support
      · rw [support] at hs
        exact Or.inr ((Set.mem_insert_iff.mp hs).resolve_right off ▸ not_not.mp absent)
      · exact Or.inl hs
  rw [←joint_output_event]
  have h := (probability_mono (joint A p n) sub).trans (probability_union_le ..)
  rw [joint_sample_event] at h
  exact (missing_probability p a n) ▸ h

theorem failure_on_foreign (A : StatisticalGenerator X) (p : PMF X)
    (F : Set X) (dis : Disjoint F p.support) (n : ℕ) :
    probability ((samples p n).bind A) F ≤ genErr A p n := by
  rw [←joint_output_event]
  exact probability_mono (joint A p n) (fun xy hx => Or.inl (Set.disjoint_left.mp dis hx))

private theorem geometric_support (a : X) (f : ℕ → X) :
    (spiked positiveGeometric a f).support = insert a (range f) := by
  rw [spiked_support]
  have h : positiveGeometric.support = univ := Set.eq_univ_of_forall positiveGeometric_support
  rw [h,Set.image_univ]

private theorem quarter_power (ε : ℝ≥0∞) {n : ℕ} (hn : 0 < n) :
    3*(1/4 : ℝ)^n ≤ commonRate ε ^ n := by
  have lo : (3/4 : ℝ) ≤ commonRate ε := by unfold commonRate; linarith [(retention_mem ε).1]
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ,pow_succ]
  calc 3 * ((1/4 : ℝ)^k * (1/4)) = (1/4 : ℝ)^k * (3/4) := by ring
       _ ≤ _ := mul_le_mul (pow_le_pow_left₀ (by norm_num) (by linarith : (1/4:ℝ) ≤ commonRate ε) k)
         lo (by norm_num) (pow_nonneg (by linarith) _)

theorem generation_lower [Countable X] (C : Generic.LanguageFamily X)
    (pair : IntersectingInfiniteDifferencePair C) :
    ∃ p₀ p₁ : PMF X, p₀.support.Infinite ∧ p₁.support.Infinite ∧
      ∀ (ε : ℝ≥0∞) (A : StatisticalGenerator X), IsPrivate ε A →
      ∀ n : ℕ, 0 < n → commonRate ε ^ n / 3 ≤ max (genErr A p₀ n) (genErr A p₁ n) := by
  obtain ⟨i,j,⟨a,hai,haj⟩,h₀,h₁⟩ := pair
  let F := C i \ C j
  let F' := C j \ C i
  let f := Support.infiniteEnumeration F h₀
  let g := Support.infiniteEnumeration F' h₁
  let p₀ := spiked positiveGeometric a f
  let p₁ := spiked positiveGeometric a g
  have support₀ : p₀.support = insert a F := by
    change (spiked positiveGeometric a f).support = _
    rw [geometric_support,show range f = F from Support.infiniteEnumeration_presents F h₀]
  have support₁ : p₁.support = insert a F' := by
    change (spiked positiveGeometric a g).support = _
    rw [geometric_support,show range g = F' from Support.infiniteEnumeration_presents F' h₁]
  have mass : (3/4 : ℝ) ≤ (p₀ a).toReal := by
    have h := spiked_event positiveGeometric a f {a}
    simp only [Set.mem_singleton_iff,if_true,probability,PMF.toOuterMeasure_apply_singleton] at h
    change (p₀ a).toReal = _ at h
    linarith [ENNReal.toReal_nonneg (a := ((positiveGeometric.map f) a))]
  have dis : Disjoint F p₁.support := by
    rw [support₁]
    apply Set.disjoint_left.mpr
    rintro y (hy : y ∈ C i \ C j) (rfl | hy')
    · exact hy.2 haj
    · exact hy.2 hy'.1
  refine ⟨p₀,p₁,support₀ ▸ h₀.mono (Set.subset_insert ..),support₁ ▸ h₁.mono (Set.subset_insert ..),?_⟩
  intro ε A dp n hn
  have test := spiked_testing dp positiveGeometric a f g F n
  change commonRate ε ^ n ≤ probability ((samples p₀ n).bind A) Fᶜ +
    probability ((samples p₁ n).bind A) F at test
  have missing : (1 - (p₀ a).toReal)^n ≤ (1/4 : ℝ)^n := by
    apply pow_le_pow_left₀ _ (by linarith)
    exact sub_nonneg.mpr ((ENNReal.toReal_le_toReal (p₀.apply_ne_top a) ENNReal.one_ne_top).mpr
      (p₀.coe_le_one a) |>.trans_eq ENNReal.toReal_one)
  linarith [failure_off_tail A p₀ a F support₀ n, failure_on_foreign A p₁ F dis n,
    quarter_power ε hn, le_max_left (genErr A p₀ n) (genErr A p₁ n),
    le_max_right (genErr A p₀ n) (genErr A p₁ n)]

end
end GenLimit.PriceOfPrivacy
