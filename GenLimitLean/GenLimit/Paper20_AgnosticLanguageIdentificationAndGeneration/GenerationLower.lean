import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.Model
import GenLimit.Support.DiscreteSampleAtoms
import GenLimit.Support.FullSupportDistribution
import GenLimit.Paper03_HallucinationAndModeCollapse.IdentificationLowerBound

/-! # A fixed hard distribution for exponentially many indistinguishable samples -/
namespace GenLimit.AgnosticLanguage
open DiscreteIID Filter
open scoped Classical Topology
noncomputable section

theorem genErr_ge_atom (G : StatisticalGenerator α) (p : PMF α) (xs : List α) (n : ℕ) :
    ((samples p n) xs).toReal * probability (G xs) {y | y ∉ p.support ∨ y ∈ xs} ≤ genErr G p n := by
  unfold genErr
  have h := probability_bind_ge (samples p n) (fun z ↦ (G z).map (Prod.mk z))
    {z | z.2 ∉ p.support ∨ z.2 ∈ z.1} xs
  simpa only [probability,PMF.toOuterMeasure_map_apply] using h

private theorem samples_prefixed_atom (p : PMF α) (xs ys : List α) :
    (samples p (xs++ys).length (xs++ys)).toReal =
      (samples p xs.length xs).toReal * (samples p ys.length ys).toReal := by
  induction xs with
  | nil => simp [samples]
  | cons x xs ih =>
    simp only [List.cons_append,List.length_cons,samples_cons,ENNReal.toReal_mul, ih,mul_assoc]

/-- A finite common prefix has a positive constant probability cost.
All subsequent observations can be the common atom, of mass at least 1/2. -/
private theorem hard_sample_lower (p : PMF α) (G : StatisticalGenerator α) (xs : List α) (x : α)
    (hp : ∀ y ∈ xs, y ∈ p.support) (hx : (1/2 : ℝ) ≤ (p x).toReal)
    (hf : ∃ᶠ n : ℕ in atTop,
      (1/2 : ℝ) ≤ probability (G (xs ++ List.replicate n x)) {y | y ∉ p.support ∨ y ∈ xs ++ List.replicate n x}) :
    ∃ᶠ n : ℕ in atTop, Real.exp (-2*(n:ℝ))/4 ≤ genErr G p n := by
  let a := ((samples p xs.length) xs).toReal
  have ha : 0 < a := ENNReal.toReal_pos ((samples_support ..).mpr ⟨rfl,hp⟩) ((samples p xs.length).apply_ne_top xs)
  have small : ∀ᶠ n : ℕ in atTop, (1/2 : ℝ)^n ≤ a :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).eventually_le_const ha
  have he : Real.exp (-1 : ℝ) ≤ 1/2 := by
    rw [Real.exp_neg, inv_eq_one_div]; apply one_div_le_one_div_of_le (by norm_num)
    linarith [Real.add_one_le_exp (1:ℝ)]
  have hex (n : ℕ) : Real.exp (-2 * (n:ℝ)) ≤ ((1/2:ℝ)^n)^2 := by
    calc
      _ = (Real.exp (-1)^n)^2 := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
      _ ≤ _ := by gcongr
  apply frequently_atTop.mpr
  intro N
  obtain ⟨n,hn,hh,hsmall⟩ := frequently_atTop.mp (hf.and_eventually small) N
  let ys := xs ++ List.replicate n x
  refine ⟨ys.length,by simp [ys]; omega,?_⟩
  have hmass : a * (1/2 : ℝ)^n ≤ ((samples p ys.length) ys).toReal := by
    rw [show ys = _ from rfl, samples_prefixed_atom,List.length_replicate,samples_replicate,ENNReal.toReal_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hx n) ha.le
  apply le_trans _ ((mul_le_mul hmass hh (by norm_num) ENNReal.toReal_nonneg).trans (genErr_ge_atom G p ys _))
  have hlen : (n:ℝ) ≤ ys.length := by exact_mod_cast (show n ≤ ys.length by simp [ys])
  have hh' := Real.exp_le_exp.mpr (show -2*(ys.length:ℝ) ≤ -2*n by linarith)
  nlinarith [hex n, mul_le_mul_of_nonneg_right hsmall (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n)]

/-- Theorem 3.5. Both candidate laws give positive mass to the finite
intersection and have a common heavy atom outside the union. -/
theorem generation_exponential_lower [Countable α] (C : Generic.LanguageFamily α)
    (i j : ℕ) (hfin : (C i ∩ C j).Finite) (x : α) (hx : x ∉ C i ∪ C j)
    (G : StatisticalGenerator α) :
    ∃ p : PMF α, (∃ k, C k ⊆ p.support) ∧ ∃ᶠ n : ℕ in atTop,
      Real.exp (-2*(n:ℝ))/4 ≤ genErr G p n := by
  obtain ⟨p,hp,hm⟩ := exists_fullSupport_heavyAtom (insert x (C i)) x (Set.mem_insert ..)
  obtain ⟨q,hq,hm'⟩ := exists_fullSupport_heavyAtom (insert x (C j)) x (Set.mem_insert ..)
  let xs := x :: hfin.toFinset.toList
  have hboth (y : α) (hy : y ∈ xs) : y ∈ p.support ∧ y ∈ q.support := by
    rw [hp,hq]
    rcases List.mem_cons.mp hy with rfl | h
    · exact ⟨Set.mem_insert .., Set.mem_insert ..⟩
    · obtain ⟨hi,hj⟩ := hfin.mem_toFinset.mp (Finset.mem_toList.mp h)
      exact ⟨Or.inr hi,Or.inr hj⟩
  let bad := fun (r : PMF α) (n : ℕ) ↦ {y | y ∉ r.support ∨ y ∈ xs ++ List.replicate n x}
  have either (n) : (1/2 : ℝ) ≤ probability (G (xs ++ List.replicate n x)) (bad p n) ∨
      (1/2 : ℝ) ≤ probability (G (xs ++ List.replicate n x)) (bad q n) := by
    have cover : bad p n ∪ bad q n = Set.univ := by
      apply Set.eq_univ_of_forall
      intro y
      by_cases hs : y ∈ p.support ∧ y ∈ q.support
      · apply Or.inl ∘ Or.inr
        apply List.mem_append_left
        change y ∈ x :: _
        rw [hp,hq] at hs
        rcases hs.1 with h | hi
        · exact List.mem_cons.mpr (Or.inl h)
        rcases hs.2 with h | hj
        · exact List.mem_cons.mpr (Or.inl h)
        exact List.mem_cons.mpr (Or.inr (Finset.mem_toList.mpr (hfin.mem_toFinset.mpr ⟨hi,hj⟩)))
      · by_cases ht : y ∈ p.support
        · exact Or.inr (Or.inl (fun h ↦ hs ⟨ht,h⟩))
        · exact Or.inl (Or.inl ht)
    have h := probability_union_le (G (xs ++ List.replicate n x)) (bad p n) (bad q n)
    rw [cover,probability_univ] at h
    by_contra! hbad; linarith [hbad.1,hbad.2]
  rcases frequently_or_distrib.mp (Frequently.of_forall either : ∃ᶠ n : ℕ in atTop, _) with h | h
  · exact ⟨p,⟨i,hp ▸ Set.subset_insert ..⟩,hard_sample_lower p G xs x (fun y hy ↦ (hboth y hy).1) hm h⟩
  · exact ⟨q,⟨j,hq ▸ Set.subset_insert ..⟩,hard_sample_lower q G xs x (fun y hy ↦ (hboth y hy).2) hm' h⟩

end
end GenLimit.AgnosticLanguage
