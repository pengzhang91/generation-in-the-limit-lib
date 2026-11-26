import GenLimit.Paper24_PriceOfPrivacy.Resampling
import GenLimit.Paper24_PriceOfPrivacy.WitnessModel
import GenLimit.Paper24_PriceOfPrivacy.GenerationLower

/-! The unknown-witness obstruction of Theorem 4.7. A nearby distribution
keeps the mass of a large finite head and redirects its tail onto the other
language. Under consistency the output must eventually escape the original
support with high probability in the new experiment. -/

namespace GenLimit.PriceOfPrivacy

open AgnosticLanguage DiscreteIID Set Filter
open scoped ENNReal Topology Classical
noncomputable section

/-- Small error on every distribution satisfying Assumption 4.1. -/
def ConsistentGenerator (u : ℕ ≃ X) (C : Generic.LanguageFamily X)
    (A : StatisticalGenerator X) : Prop :=
  ∀ q : PMF X, GenerationAssumptions u C q →
    Tendsto (genErr A q) atTop (𝓝 0)

private theorem eventually_foreign (A : StatisticalGenerator X) (q : PMF X) (L : Set X)
    (finite : (q.support ∩ L).Finite) (consistent : Tendsto (genErr A q) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, 3/4 ≤ sampleEvent q A Lᶜ n := by
  classical
  let T := finite.toFinset
  let missed : Set (List X) := {xs | ¬∀ x ∈ T, x ∈ xs}
  have covered := finite_coverage q T
    (fun _ hx => (finite.mem_toFinset.mp hx).1) (1/8) (by norm_num)
  filter_upwards [covered,consistent.eventually_lt_const (by norm_num : (0:ℝ) < 1/8)] with n small low
  let bad : Set (List X × X) := {z | z.2 ∉ q.support ∨ z.2 ∈ z.1}
  have sub : Prod.snd ⁻¹' L ⊆ bad ∪ Prod.fst ⁻¹' missed := by
    rintro ⟨xs,y⟩ (hy : y ∈ L)
    by_cases good : ∀ x ∈ T, x ∈ xs
    · apply Or.inl
      by_cases hs : y ∈ q.support
      · exact Or.inr (good y (finite.mem_toFinset.mpr ⟨hs,hy⟩))
      · exact Or.inl hs
    · exact Or.inr good
  have h := (probability_mono (joint A q n) sub).trans (probability_union_le ..)
  rw [joint_output_event,joint_sample_event] at h
  change sampleEvent q A L n ≤ genErr A q n + probability (samples q n) missed at h
  change probability (samples q n) missed < 1/8 at small
  unfold sampleEvent at h ⊢
  rw [probability_compl]
  linarith

private theorem eventual_slack {s r : ℝ} (hr : r < s) :
    ∀ᶠ n : ℕ in atTop, (n:ℝ) * Real.exp (-(s-r)*n) ≤ 1/4 := by
  have bpos := sub_pos.mpr hr
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop bpos)
  have small := h.eventually_lt_const (show (0:ℝ) < (s-r)/4 by positivity)
  filter_upwards [small] with n hn
  change ((s-r)*(n:ℝ))^1 * Real.exp (-((s-r)*n)) < (s-r)/4 at hn
  rw [pow_one, mul_assoc,← neg_mul] at hn
  apply le_of_lt
  apply (mul_lt_mul_iff_right₀ bpos).mp
  simpa only [div_eq_mul_inv,one_mul] using hn

theorem unknown_witness_lower [Countable X] (u : ℕ ≃ X) (C : Generic.LanguageFamily X)
    (finite : (range C).Finite) (i j : ℕ) (hi : (C i).Infinite) (hj : (C j).Infinite)
    (inter : (C i ∩ C j).Finite) (A : StatisticalGenerator X) (ok : ConsistentGenerator u C A)
    {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (dp : ∀ n, PrivateAt ε (δ n) n A)
    (decay : ∀ᶠ n : ℕ in atTop, δ n ≤ Real.exp (-s*n))
    (p : PMF X) (support : p.support = C i) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (1/2 : ℝ)*Real.exp (-c*n) ≤ genErr A p n := by
  classical
  let r := min c s / 2
  have hr : 0 < r := half_pos (lt_min hc hs)
  have rc : r ≤ c := (half_le_self (le_of_lt (lt_min hc hs))).trans (min_le_left ..)
  have rs : r < s := (half_lt_self (lt_min hc hs)).trans_le (min_le_right ..)
  let b := Real.exp ε - 1
  have hb : 0 < b := sub_pos.mpr (Real.one_lt_exp_iff.mpr hε)
  obtain ⟨T,small⟩ := finite_head p (div_pos hr hb)
  obtain ⟨g,agree,image⟩ := redirect_tail (C i) (C j) hi hj T
  let D : Set X := (T : Set X)ᶜ
  let q := p.map g
  have qsup : q.support = (C i ∩ (↑T : Set X)) ∪ C j := by
    change (p.map g).support = _
    rw [PMF.support_map,support,image]
  have hq : GenerationAssumptions u C q :=
    ⟨finite_witness u C q finite, j, fun x hx => qsup ▸ Or.inr hx⟩
  have finiteQ : (q.support ∩ C i).Finite := by
    apply (T.finite_toSet.union inter).subset
    rintro x ⟨h,hi'⟩
    rw [qsup] at h
    exact h.elim (fun ht => Or.inl ht.2) (fun hj' => Or.inr ⟨hi',hj'⟩)
  let k := 1+probability p D*b
  have kpos : 0 ≤ k := add_nonneg zero_le_one (mul_nonneg (probability_nonneg p D) hb.le)
  have kexp : k ≤ Real.exp r := by
    have h := (lt_div_iff₀ hb).mp small
    change probability p D * b < r at h
    dsimp [k]; linarith [Real.add_one_le_exp r]
  filter_upwards [eventually_foreign A q (C i) finiteQ (ok q hq),decay,eventual_slack rs] with n high slack smallSlack
  have transfer := private_resample p g D (fun x hx => agree x (by simpa [D] using hx))
    hε.le (hδ n) (C i)ᶜ n A (dp n)
  have foreign := failure_on_foreign A p (C i)ᶜ (support ▸ disjoint_compl_left) n
  have expn : k^n ≤ Real.exp (r*n) := by
    rw [mul_comm r,Real.exp_nat_mul]; exact pow_le_pow_left₀ kpos kexp _
  have start : 3/4 ≤ Real.exp (r*n)*(genErr A p n + n*δ n) := by
    apply high.trans (transfer.trans ?_)
    apply mul_le_mul expn (add_le_add_right foreign _) _ (Real.exp_pos _).le
    exact add_nonneg (probability_nonneg ..) (mul_nonneg (Nat.cast_nonneg _) (hδ _))
  have smallTerm : Real.exp (r*n) * (n*δ n) ≤ 1/4 := by
    calc
      _ ≤ Real.exp (r*n) * (n*Real.exp (-s*n)) := by gcongr
      _ = n * Real.exp (-(s-r)*n) := by
        rw [mul_left_comm,←Real.exp_add]; congr 2; ring
      _ ≤ _ := smallSlack
  have half : (1/2:ℝ) ≤ Real.exp (r*n) * genErr A p n := by linarith
  have undo := mul_le_mul_of_nonneg_right half (Real.exp_pos (-r*n)).le
  rw [mul_right_comm (Real.exp (r*n)),← Real.exp_add,show r*(n:ℝ)+ -r*n = 0 by ring,
    Real.exp_zero,one_mul] at undo
  apply le_trans _ undo
  gcongr

end
end GenLimit.PriceOfPrivacy
