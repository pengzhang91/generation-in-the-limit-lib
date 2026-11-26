import GenLimit.Paper24_PriceOfPrivacy.FiniteMinimum
import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.Concentration

/-! The signed-margin score of Definition 3.2 on a finite prefix of the
language family, its replacement sensitivity, and the separation event in Lemma 3.3. -/

namespace GenLimit.PriceOfPrivacy.Identification

open AgnosticLanguage DiscreteIID Set FiniteMinimum
open scoped Classical
noncomputable section

/-- Every empirical risk difference is at most one. Including one in the minimum
also gives the paper's first-index convention on the empty prefix. -/
def margin {w : ℕ} (v : Fin w → ℝ) (i : Fin w) : ℝ :=
  lower 1 (Finset.Iio i) fun j => v j-v i

def signedScore {w : ℕ} (v : Fin w → ℝ) (i : Fin w) : ℝ :=
  lower (margin v i-2/w) (Finset.Ioi i) fun j => 2/w-margin v j

def empiricalScore (C : Generic.LanguageFamily X) (w : ℕ) (xs : List X) : Fin w → ℝ :=
  signedScore fun i => empirical (C i.val)ᶜ xs

private theorem margin_shift {w : ℕ} {u v : Fin w → ℝ} {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ i, |u i-v i| ≤ d) (i : Fin w) : margin u i-margin v i ≤ 2*d := by
  apply lower_shift (by linarith)
  intro j _
  linarith [(abs_le.mp (h j)).2,(abs_le.mp (h i)).1]

private theorem signed_shift {w : ℕ} {u v : Fin w → ℝ} {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ i, |u i-v i| ≤ d) (i : Fin w) : signedScore u i-signedScore v i ≤ 2*d := by
  apply lower_shift (by linarith [margin_shift hd h i])
  intro j _
  have rev (k : Fin w) : |v k-u k| ≤ d := (abs_sub_comm ..).trans_le (h k)
  linarith [margin_shift hd rev j]

private theorem empirical_replace (E : Set X) (pre : List X) (x y : X) (post : List X)
    {n : ℕ} (hn : 0 < n) (len : pre.length+post.length+1 = n) :
    |empirical E (pre ++ x::post)-empirical E (pre ++ y::post)| ≤ 1/(n:ℝ) := by
  have length_eq (z : X) : (pre ++ z::post).length = n := by simp; omega
  simp only [empirical,length_eq,List.map_append,List.map_cons,List.sum_append,List.sum_cons,←sub_div,abs_div,
    abs_of_nonneg (show 0 ≤ (n : ℝ) by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  by_cases hx : x ∈ E <;> by_cases hy : y ∈ E <;> simp [hx,hy]

theorem sensitivity (C : Generic.LanguageFamily X) (w : ℕ) (pre : List X) (x y : X)
    (post : List X) {n : ℕ} (hn : 0 < n) (len : pre.length+post.length+1 = n) (i : Fin w) :
    |empiricalScore C w (pre ++ x::post) i-empiricalScore C w (pre ++ y::post) i| ≤ 2/(n:ℝ) := by
  have h (a b : X) := signed_shift (d := 1/(n:ℝ)) (by positivity)
    (fun j : Fin w => empirical_replace (C j.val)ᶜ pre a b post hn len) i
  have hy := h y x
  have hx := h x y
  rw [mul_one_div] at hy hx
  exact abs_le.mpr ⟨by unfold empiricalScore; linarith only [hy], hx⟩

def accurate (C : Generic.LanguageFamily X) (p : PMF X) (w : ℕ) (xs : List X) : Prop :=
  ∀ i : Fin w, |empirical (C i.val)ᶜ xs - risk p (C i.val)| ≤ 1/(4*w)

theorem inaccurate_probability [Countable X] (C : Generic.LanguageFamily X) (p : PMF X)
    {n w : ℕ} (hn : 0 < n) (hw : 0 < w) :
    probability (samples p n) {xs | ¬accurate C p w xs} ≤ 2*w*Real.exp (-(n:ℝ)/(8*w^2)) := by
  let bad (i : Fin w) := {xs | 1/(4*(w:ℝ)) ≤ |empirical (C i.val)ᶜ xs - risk p (C i.val)|}
  have sub : {xs | ¬accurate C p w xs} ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin w)), bad i := by
    intro xs h
    change ¬∀ i : Fin w, _ at h
    obtain ⟨i,hi⟩ := Classical.not_forall.mp h
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨Finset.mem_univ _,(lt_of_not_ge hi).le⟩⟩
  apply (probability_mono _ sub).trans ((probability_biUnion_le _ _ _).trans ?_)
  have hw' : (0:ℝ) < w := by exact_mod_cast hw
  calc
    _ ≤ ∑ _i : Fin w, 2*Real.exp (-(n:ℝ)/(8*w^2)) := by
      apply Finset.sum_le_sum
      intro i _
      apply (empirical_deviation p (C i.val)ᶜ n hn (1/(4*w)) (by positivity)).trans_eq
      congr 2
      field_simp
      norm_num
    _ = _ := by simp; ring

/-- On the simultaneous concentration event, the first optimal index beats
each competing score by the full paper margin, including tied later optima. -/
theorem score_gap (C : Generic.LanguageFamily X) (p : PMF X) {w : ℕ} (hw : 3 ≤ w)
    (target : Fin w) (optimal : Optimal C p target.val)
    (earlier : ∀ j < target, 3/(w:ℝ) ≤ risk p (C j.val)-risk p (C target.val))
    {xs : List X} (good : accurate C p w xs) (j : Fin w) (ne : j ≠ target) :
    1/(w:ℝ) ≤ empiricalScore C w xs target - empiricalScore C w xs j := by
  let v (i : Fin w) := empirical (C i.val)ᶜ xs
  let a : ℝ := (w:ℝ)⁻¹
  have wa : (0:ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have ha : 0 ≤ a := inv_nonneg.mpr wa.le
  have h3 : 3*a ≤ 1 := by
    dsimp [a]; rw [←div_eq_mul_inv,div_le_iff₀ wa,one_mul]; exact_mod_cast hw
  have close (i : Fin w) : -a/4 ≤ v i-risk p (C i.val) ∧ v i-risk p (C i.val) ≤ a/4 := by
    convert abs_le.mp (good i) using 2 <;> dsimp [a] <;> ring
  have top : 5*a/2 ≤ margin v target := by
    apply le_lower (by linarith)
    intro k hk
    have e := earlier k (Finset.mem_Iio.mp hk)
    rw [div_eq_mul_inv] at e
    change 3*a ≤ _ at e
    linarith [(close k).1,(close target).2]
  have later (k : Fin w) (hk : target < k) : margin v k ≤ a/2 := by
    have h : margin v k ≤ v target-v k := lower_entry 1 _ (Finset.mem_Iio.mpr hk)
    linarith [(optimal_iff ..).mp optimal k.val,(close k).1,(close target).2]
  have two : 2/(w:ℝ) = 2*a := div_eq_mul_inv ..
  have pos : a/2 ≤ signedScore v target := by
    apply le_lower (by rw [two]; linarith)
    intro k hk
    rw [two]; linarith [later k (Finset.mem_Ioi.mp hk)]
  have neg : signedScore v j ≤ -a/2 := by
    rcases lt_or_gt_of_ne ne with hj | hj
    · have h : signedScore v j ≤ 2/(w:ℝ)-margin v target :=
        lower_entry _ _ (Finset.mem_Ioi.mpr hj)
      rw [two] at h; linarith
    · have h : signedScore v j ≤ margin v j-2/(w:ℝ) := lower_anchor ..
      rw [two] at h; linarith [later j hj]
  change 1/(w:ℝ) ≤ signedScore v target-signedScore v j
  rw [one_div]; change a ≤ _; linarith

end
end GenLimit.PriceOfPrivacy.Identification
