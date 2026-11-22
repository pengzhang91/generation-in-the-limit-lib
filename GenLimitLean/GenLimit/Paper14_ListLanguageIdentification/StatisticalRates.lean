import GenLimit.Paper14_ListLanguageIdentification.StatisticalNecessity

/-! # Sharp rates for list identification on independent samples -/

namespace GenLimit.ListIdentification.Statistical
open DiscreteIID Filter
open scoped Topology

/-- The source's nontriviality hypothesis for the lower bound is a common
word shared by one more distinct language than the list can hold. -/
def NontrivialFor (F : Generic.LanguageFamily α) (k : ℕ) : Prop :=
  ∃ (S : Finset (Generic.Language α)) (x : α), S.card = k+1 ∧
    ∀ K ∈ S, K ∈ Set.range F ∧ x ∈ K

private theorem often_missed (F : Generic.LanguageFamily α) (A : Kernel α k)
    (S : Finset (Generic.Language α)) (hc : S.card = k+1) (x : α) :
    ∃ K ∈ S, ∃ᶠ n : ℕ in atTop, 1 / ((k : ℝ)+1) ≤
      probability (A (List.replicate n x)) (misses F K) := by
  classical
  by_contra h
  have bad (K) (hK : K ∈ S) : ∀ᶠ n : ℕ in atTop,
      probability (A (List.replicate n x)) (misses F K) < 1 / ((k : ℝ)+1) :=
    (not_frequently.mp (fun hf ↦ h ⟨K,hK,hf⟩)).mono (fun _ ↦ lt_of_not_ge)
  obtain ⟨n,hn⟩ := ((S.eventually_all).2 bad).exists
  have ne := Finset.card_pos.mp (show 0 < S.card by omega)
  have hi := Finset.sum_lt_sum_of_nonempty ne hn
  have lo := miss_sum F (A (List.replicate n x)) S (by omega)
  have contra := lo.trans_lt hi
  simp [hc,show (k : ℝ)+1 ≠ 0 by positivity] at contra

/-- Theorem 13. The same target and distribution witness the lower bound
at infinitely many sample sizes, including for randomized identifiers. -/
theorem theorem_13 [Countable α] (F : Generic.LanguageFamily α) (h : NontrivialFor F k)
    (A : Kernel α k) :
    ∃ (i : ℕ) (p : PMF α), p.support = F i ∧
      ∃ᶠ n : ℕ in atTop, Real.exp (-2 * (n : ℝ)) ≤ error F A p (F i) n := by
  classical
  obtain ⟨S,x,hc,hS⟩ := h
  obtain ⟨K,hK,hf⟩ := often_missed F A S hc x
  obtain ⟨⟨i,rfl⟩,hx⟩ := hS K hK
  obtain ⟨p,hp,hpx⟩ := exists_fullSupport_heavyAtom (F i) x hx
  refine ⟨i,p,hp,?_⟩
  have ε : 0 < 1 / ((k : ℝ)+1) := by positivity
  have hev := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2 : ℝ))
    (by norm_num) (by norm_num)).eventually_lt_const ε
  apply (hf.and_eventually hev).mono
  intro n ⟨hmiss,hsmall⟩
  have hexp : Real.exp (-1) ≤ (1/2 : ℝ) := by
    have h1 := Real.add_one_le_exp 1
    have hm : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-1)]
  have hm : (1/2 : ℝ)^n ≤ (samples p n (List.replicate n x)).toReal := by
    rw [samples_replicate,ENNReal.toReal_pow]
    exact pow_le_pow_left₀ (by norm_num) hpx n
  calc
    _ = Real.exp (-1)^(2*n) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    _ ≤ (1/2 : ℝ)^(2*n) := pow_le_pow_left₀ (Real.exp_nonneg _) hexp _
    _ = (1/2 : ℝ)^n * (1/2 : ℝ)^n := by rw [two_mul,pow_add]
    _ ≤ (samples p n (List.replicate n x)).toReal *
        probability (A (List.replicate n x)) (misses F (F i)) :=
      mul_le_mul hm (hsmall.le.trans hmiss) (by positivity) ENNReal.toReal_nonneg
    _ ≤ _ := probability_bind_ge (samples p n) A (misses F (F i)) _

/-- Overview Theorem 3. Nonempty targets on a countable universe have exact
texts. The upper bound is instance-dependent, the nontriviality assumption
qualifies optimality, and failure of list identification forces frequent
positive error on one fixed full-support law. -/
theorem theorem_3 [Countable α] [DecidableEq α] (F : Generic.LanguageFamily α) (k : ℕ)
    (hne : ∀ i, (F i).Nonempty) :
    (ListIdentifiable F k → ∃ A : Kernel α k, Exponential F A) ∧
    (NontrivialFor F k → ∀ A : Kernel α k, ∃ (i : ℕ) (p : PMF α), p.support = F i ∧
      ∃ᶠ n : ℕ in atTop, Real.exp (-2*(n : ℝ)) ≤ error F A p (F i) n) ∧
    (¬ ListIdentifiable F k → ∀ A : Kernel α k, ∃ (i : ℕ) (p : PMF α), p.support = F i ∧
      ∃ᶠ n : ℕ in atTop, 1 / ((k : ℝ)+2) < error F A p (F i) n) := by
  have present (i : ℕ) : ∃ s : Generic.Stream α, Generic.Presents s (F i) := by
    letI : Nonempty (F i) := (hne i).to_subtype
    obtain ⟨e,he⟩ := exists_surjective_nat (F i)
    refine ⟨fun n ↦ (e n).val,Set.ext (fun x ↦ ⟨?_,?_⟩)⟩
    · rintro ⟨n,rfl⟩; exact (e n).property
    · intro hx
      obtain ⟨n,hn⟩ := he ⟨x,hx⟩
      exact ⟨n,congrArg Subtype.val hn⟩
  have eqv := listIdentifiable_iff_kAngluin present k
  exact ⟨fun h ↦ theorem_12 (eqv.mp h),theorem_13 F,fun h ↦ theorem_8 F hne (h ∘ eqv.mpr)⟩

end GenLimit.ListIdentification.Statistical
