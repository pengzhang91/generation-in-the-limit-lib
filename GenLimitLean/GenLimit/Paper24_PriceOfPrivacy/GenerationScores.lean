import GenLimit.Paper24_PriceOfPrivacy.CountConcentration
import GenLimit.Paper24_PriceOfPrivacy.FiniteMinimum
import GenLimit.Paper24_PriceOfPrivacy.WitnessModel

/-! The target mass floor, public prefix count and bounded-depth score of
Section 4. The unknown-witness mechanism maximizes over every level. -/
namespace GenLimit.PriceOfPrivacy.Generation

open FiniteMinimum DiscreteIID Set
open scoped Classical
noncomputable section

def prefixIndices (u : ℕ ≃ X) (L : Set X) (W : ℕ) := (Finset.range W).filter fun j => u j ∈ L

def massFloor (u : ℕ ≃ X) (L : Set X) (p : PMF X) (W : ℕ) :=
  lower 1 (prefixIndices u L W) fun j => (p (u j)).toReal

def prefixCount (u : ℕ ≃ X) (L : Set X) (xs : List X) (W : ℕ) :=
  lower xs.length (prefixIndices u L W) fun j => (xs.count (u j) : ℝ)

def profile (g : ℝ) (l : ℕ) : ℝ := g*l/(l+1)

def depthScore (u : ℕ ≃ X) (L : Set X) (xs : List X) (g : ℝ) :=
  ⨆ l : ℕ, min (prefixCount u L xs l) (profile g l)

theorem massFloor_pos (u : ℕ ≃ X) (L : Set X) (p : PMF X) (W : ℕ) (good : L ⊆ p.support) :
    0 < massFloor u L p W := by
  unfold massFloor lower
  have h := Finset.min'_mem (insert 1 ((prefixIndices u L W).image fun j => (p (u j)).toReal)) (by simp)
  rcases Finset.mem_insert.mp h with eq | mem
  · rw [eq]; norm_num
  · obtain ⟨j,hj,eq⟩ := Finset.mem_image.mp mem
    rw [←eq]
    exact ENNReal.toReal_pos (good (Finset.mem_filter.mp hj).2) (p.apply_ne_top _)

def covered (u : ℕ ≃ X) (L : Set X) (p : PMF X) (W n : ℕ) (xs : List X) : Prop :=
  ∀ j ∈ prefixIndices u L W, n*massFloor u L p W/2 ≤ (xs.count (u j) : ℝ)

theorem cover_failure (u : ℕ ≃ X) (L : Set X) (p : PMF X) (W n : ℕ) (good : L ⊆ p.support) :
    probability (samples p n) {xs | ¬covered u L p W n xs} ≤ W*Real.exp (-(n:ℝ)*massFloor u L p W/8) := by
  let m := massFloor u L p W
  let bad (j : ℕ) := {xs : List X | (xs.count (u j) : ℝ) < n*m/2}
  have eq : {xs | ¬covered u L p W n xs} = ⋃ j ∈ prefixIndices u L W, bad j := by
    ext xs; simp [covered,bad,m]
  rw [eq]
  apply (probability_biUnion_le _ _ _).trans
  calc
    _ ≤ ∑ _j ∈ prefixIndices u L W, Real.exp (-(n:ℝ)*m/8) := Finset.sum_le_sum fun j hj =>
      count_lower_tail p (u j) n m (massFloor_pos u L p W good).le (lower_entry 1 _ hj)
    _ ≤ _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast (Finset.card_le_card (Finset.filter_subset (fun j => u j ∈ L) (Finset.range W))).trans_eq (Finset.card_range W)

theorem target_count (u : ℕ ≃ X) (L : Set X) (p : PMF X) (W n : ℕ)
    {xs : List X} (len : xs.length = n) (ok : covered u L p W n xs) :
    n*massFloor u L p W/2 ≤ prefixCount u L xs W := by
  apply le_lower _ ok
  rw [len]
  have h : massFloor u L p W ≤ 1 := lower_anchor ..
  have := mul_le_mul_of_nonneg_left h (show 0 ≤ (n:ℝ) by positivity)
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem prefix_nonneg (u : ℕ ≃ X) (L : Set X) (xs : List X) (W : ℕ) :
    0 ≤ prefixCount u L xs W := le_lower (by positivity) (fun _ _ => by positivity)

private theorem prefix_shift (u : ℕ ≃ X) (L : Set X) (pre : List X) (x y : X)
    (post : List X) (W : ℕ) :
    prefixCount u L (pre ++ x::post) W-prefixCount u L (pre ++ y::post) W ≤ 1 := by
  apply lower_shift (by simp)
  intro j _
  simp only [List.count_append,List.count_cons]
  split <;> split <;> push_cast <;> linarith

theorem prefix_sensitive (u : ℕ ≃ X) (L : Set X) (pre : List X) (x y : X)
    (post : List X) (W : ℕ) :
    |prefixCount u L (pre ++ x::post) W-prefixCount u L (pre ++ y::post) W| ≤ 1 :=
  abs_le.mpr ⟨by linarith [prefix_shift u L pre y x post W],prefix_shift u L pre x y post W⟩

theorem bad_count (u : ℕ ≃ X) (C : Generic.LanguageFamily X) (p : PMF X) {W : ℕ}
    (hw : WitnessBy u C p W) {i : ℕ} (bad : ¬C i ⊆ p.support)
    {xs : List X} (supported : ∀ x ∈ xs, x ∈ p.support) {l : ℕ} (hl : W ≤ l) :
    prefixCount u (C i) xs l ≤ 0 := by
  obtain ⟨t,ht,mem,out⟩ := hw i bad
  have ht' : t ∈ prefixIndices u (C i) l := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ht.trans_le hl),mem⟩
  have le : prefixCount u (C i) xs l ≤ (xs.count (u t) : ℝ) := lower_entry _ _ ht'
  simpa [List.count_eq_zero_of_not_mem (fun h => out (supported _ h))] using le

private theorem bounded (u : ℕ ≃ X) (L : Set X) (xs : List X) (g : ℝ) :
    BddAbove (range (fun l => min (prefixCount u L xs l) (profile g l))) :=
  ⟨(xs.length:ℝ), fun _ ⟨_,eq⟩ => eq ▸ (min_le_left ..).trans (lower_anchor ..)⟩

theorem depth_le (u : ℕ ≃ X) (L : Set X) (xs : List X) (g : ℝ) {b : ℝ}
    (all : ∀ l, min (prefixCount u L xs l) (profile g l) ≤ b) :
    depthScore u L xs g ≤ b := ciSup_le all

theorem le_depth (u : ℕ ≃ X) (L : Set X) (xs : List X) (g : ℝ) (l : ℕ) :
    min (prefixCount u L xs l) (profile g l) ≤ depthScore u L xs g := le_ciSup (bounded ..) l

private theorem depth_shift (u : ℕ ≃ X) (L : Set X) (pre : List X) (x y : X)
    (post : List X) (g : ℝ) :
    depthScore u L (pre ++ x::post) g ≤ depthScore u L (pre ++ y::post) g+1 := by
  apply depth_le
  intro l
  have h := le_depth u L (pre ++ y::post) g l
  have d := prefix_shift u L pre x y post l
  rcases le_total (prefixCount u L (pre ++ y::post) l) (profile g l) with le | le
  · rw [min_eq_left le] at h
    linarith only [h,d,min_le_left (prefixCount u L (pre ++ x::post) l) (profile g l)]
  · rw [min_eq_right le] at h
    linarith only [h,min_le_right (prefixCount u L (pre ++ x::post) l) (profile g l)]

theorem depth_sensitive (u : ℕ ≃ X) (L : Set X) (pre : List X) (x y : X)
    (post : List X) (g : ℝ) :
    |depthScore u L (pre ++ x::post) g-depthScore u L (pre ++ y::post) g| ≤ 1 :=
  abs_le.mpr ⟨by linarith [depth_shift u L pre y x post g],by linarith [depth_shift u L pre x y post g]⟩

theorem private_depth_gap (u : ℕ ≃ X) (C : Generic.LanguageFamily X) (p : PMF X)
    {W n target i : ℕ} (witness : WitnessBy u C p (W+1)) (bad : ¬C i ⊆ p.support)
    {xs : List X} (len : xs.length = n) (supported : ∀ x ∈ xs, x ∈ p.support)
    (ok : covered u (C target) p (W+1) n xs) {g : ℝ} (pos : 0 < g)
    (cap : g ≤ n*massFloor u (C target) p (W+1)/2) :
    g/((W+1:ℕ)*((W+1:ℕ)+1):ℝ) ≤ depthScore u (C target) xs g-depthScore u (C i) xs g := by
  have mono : Monotone (profile g) := by
    intro a b le
    unfold profile
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have ab : (a:ℝ) ≤ b := by exact_mod_cast le
    nlinarith [mul_le_mul_of_nonneg_left ab pos.le]
  have prof : profile g (W+1) ≤ g := by
    unfold profile; rw [div_le_iff₀ (by positivity)]; nlinarith
  have low := le_depth u (C target) xs g (W+1)
  rw [min_eq_right (prof.trans (cap.trans (target_count u (C target) p (W+1) n len ok)))] at low
  have high : depthScore u (C i) xs g ≤ profile g W := by
    apply depth_le
    intro l
    rcases le_or_gt l W with h | h
    · exact (min_le_right ..).trans (mono h)
    · apply (min_le_left ..).trans ((bad_count u C p witness bad supported h).trans ?_)
      unfold profile; positivity
  have diff : profile g (W+1)-profile g W = g/((W+1:ℕ)*((W+1:ℕ)+1):ℝ) := by
    unfold profile; push_cast; field_simp; ring
  rw [←diff]; linarith

end
end GenLimit.PriceOfPrivacy.Generation
