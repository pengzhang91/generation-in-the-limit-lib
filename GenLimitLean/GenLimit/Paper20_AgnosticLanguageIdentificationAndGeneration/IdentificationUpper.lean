import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.Concentration

/-! # Identification by empirical comparisons on a growing finite window -/
namespace GenLimit.AgnosticLanguage
open DiscreteIID Generic Filter
open scoped Classical Topology
noncomputable section

private def score (C : Generic.LanguageFamily α) (xs : List α) (i : ℕ) := empirical (C i)ᶜ xs

private def withinWindow (C : Generic.LanguageFamily α) (p : PMF α) (w : ℕ) (xs : List α) :=
  ∀ i < w, |score C xs i - risk p (C i)| < 1/(2*w)

private theorem window_failure [Countable α] (C : Generic.LanguageFamily α) (p : PMF α)
    {n w : ℕ} (hn : 0 < n) (hw : 0 < w) :
    probability (samples p n) {xs | ¬withinWindow C p w xs} ≤
      2*w * Real.exp (-(n:ℝ)/(2*w^2)) := by
  let bad := fun i ↦ {xs | 1/(2*(w:ℝ)) ≤ |score C xs i - risk p (C i)|}
  have he : {xs | ¬withinWindow C p w xs} = ⋃ i ∈ Finset.range w, bad i := by
    ext xs; simp [withinWindow,bad]
  rw [he]
  apply (probability_biUnion_le (samples p n) _ _).trans
  have hw' : (0:ℝ) < w := by exact_mod_cast hw
  have h (i) : probability (samples p n) (bad i) ≤ 2*Real.exp (-(n:ℝ)/(2*w^2)) := by
    apply (empirical_deviation p (C i)ᶜ n hn (1/(2*w)) (by positivity)).trans_eq
    congr 2
    field_simp
  calc
    _ ≤ ∑ _i ∈ Finset.range w, (2*Real.exp (-(n:ℝ)/(2*w^2))) := Finset.sum_le_sum fun i _ ↦ h i
    _ = _ := by simp; ring

/-- Algorithm 1 uses zero-based indices strictly below the window size. -/
def algorithmOne (C : Generic.LanguageFamily α) (f : ℕ → ℕ) (xs : List α) : ℕ :=
  let w := f xs.length
  Nat.findGreatest (fun i ↦ ∀ j < i, 2/(w:ℝ) < score C xs j - score C xs i) (w-1)

private theorem earlier_gaps (C : Generic.LanguageFamily α) (p : PMF α) (f : ℕ → ℕ)
    (hf : Tendsto f atTop atTop) (z : ℕ) (P : ℕ → Prop)
    (h : ∀ j < z, P j → risk p (C z) < risk p (C j)) :
    ∀ᶠ n : ℕ in atTop, ∀ j < z, P j → 3/(f n : ℝ) < risk p (C j) - risk p (C z) := by
  simp_rw [← Finset.mem_range]
  apply (Finset.range z).eventually_all.mpr
  intro j hj
  by_cases hp : P j
  · exact (((tendsto_const_div_atTop_nhds_zero_nat (3:ℝ)).comp hf).eventually_lt_const
      (sub_pos.mpr (h j (Finset.mem_range.mp hj) hp))).mono fun _ ht _ ↦ ht
  · exact Eventually.of_forall fun _ ht ↦ False.elim (hp ht)

private theorem diff_error (C : Generic.LanguageFamily α) (p : PMF α) {w : ℕ} {xs : List α}
    (hg : withinWindow C p w xs) {j i : ℕ} (hj : j < w) (hi : i < w) :
    |(score C xs j - score C xs i) - (risk p (C j) - risk p (C i))| < 1/(w:ℝ) := by
  have h₁ := abs_lt.mp (hg j hj)
  have h₂ := abs_lt.mp (hg i hi)
  have hhalf : (1:ℝ)/(2*w) = (1/(w:ℝ))/2 := by ring
  rw [hhalf] at h₁ h₂
  exact abs_lt.mpr ⟨by linarith [h₁.1,h₂.2],by linarith [h₁.2,h₂.1]⟩

theorem weak_near_exponential [Countable α] (C : Generic.LanguageFamily α)
    (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (p : PMF α) (ho : ∃ i, Optimal C p i) :
    ∀ᶠ n : ℕ in atTop,
      probability (samples p n) {xs | ¬ Optimal C p (algorithmOne C f xs)} ≤
        2*f n * Real.exp (-(n:ℝ)/(2*(f n)^2)) ∧
      idErr C (deterministic (algorithmOne C f)) p n ≤
        2*f n * Real.exp (-(n:ℝ)/(2*(f n)^2)) := by
  let z := Nat.find ho
  have hz : Optimal C p z := Nat.find_spec ho
  have prior (j) (hj : j < z) (_ : True) : risk p (C z) < risk p (C j) := by
    apply lt_of_le_of_ne ((optimal_iff ..).mp hz j)
    exact fun he ↦ Nat.find_min ho hj (he.symm.trans hz)
  filter_upwards [earlier_gaps C p f hf z _ prior, hf.eventually (eventually_ge_atTop (z+1)),
    eventually_ge_atTop 1] with n hgap hwindow hn
  have hfpos : 0 < f n := by omega
  have hwin := window_failure C p hn hfpos
  have hfail : probability (samples p n) {xs | ¬ Optimal C p (algorithmOne C f xs)} ≤ 2*(f n:ℝ)*Real.exp (-(n:ℝ)/(2*(f n : ℝ)^2)) := by
    rw [← probability_inter_support]
    apply le_trans (probability_mono _ ?_) hwin
    rintro xs ⟨hbad,hxs⟩ hgood
    have hlen := ((samples_support ..).mp hxs).1
    let P := fun i ↦ ∀ j < i, 2/(f n:ℝ) < score C xs j - score C xs i
    have hzwin : z < f n := by omega
    have hP : P z := by
      intro j hj
      have hg := hgap j hj trivial
      have hd := (abs_lt.mp (diff_error C p hgood (hj.trans hzwin) hzwin)).1
      simp only [div_eq_mul_inv] at hg hd ⊢
      linarith
    let k := Nat.findGreatest P (f n - 1)
    have hzk : z ≤ k := Nat.le_findGreatest (by omega) hP
    have hk : k < f n := by have := Nat.findGreatest_le (P := P) (f n-1); dsimp [k]; omega
    have he : k = z := by
      by_contra! hne
      have hPk : P k := Nat.findGreatest_spec (P := P) (by omega : z ≤ f n-1) hP
      have hbeat := hPk z (by omega)
      have hr := (optimal_iff ..).mp hz k
      have hd := (abs_lt.mp (diff_error C p hgood hzwin hk)).2
      have hp : (0:ℝ) < (f n:ℝ) := by exact_mod_cast hfpos
      simp only [div_eq_mul_inv] at hbeat hd
      linarith [inv_pos.mpr hp]
    apply hbad
    have houtput : algorithmOne C f xs = k := by simp only [algorithmOne,hlen,k,P]
    rwa [houtput,he]
  refine ⟨hfail,(idErr_le_failure ..).trans ?_⟩
  exact (probability_deterministic (samples p n) (algorithmOne C f) {j | ¬ Optimal C p j}).le.trans hfail

private def visible (C : Generic.LanguageFamily α) (i : ℕ) (S : Set α) : Prop :=
  ∃ T : Finset α, IsFiniteTellTale (Set.range C) (C i) T ∧ (T : Set α) ⊆ S

/-- If a tell-tale is supported at an optimum, every strictly smaller
language misses positive mass there. -/
private theorem minimal_of_visible (C : Generic.LanguageFamily α) (p : PMF α) (i : ℕ)
    (hi : Optimal C p i) (hv : visible C i p.support) : MinimalOptimal C p i := by
  obtain ⟨T,hT,hTs⟩ := hv
  refine ⟨hi,fun k hk hki ↦ ?_⟩
  have hmiss : ¬ (T : Set α) ⊆ C k := fun h ↦ hki.ne (hT.2 _ ⟨k,rfl⟩ h hki.le)
  obtain ⟨x,hx,hout⟩ := Set.not_subset.mp hmiss
  letI : MeasurableSpace α := ⊤
  letI : DiscreteMeasurableSpace α := ⟨fun _ ↦ trivial⟩
  have he (S : Set α) : p.toMeasure.real S = probability p S := by
    rw [MeasureTheory.Measure.real_def,PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (DiscreteMeasurableSpace.forall_measurableSet _)]
    rfl
  have hd : Disjoint ((C i)ᶜ) ({x} : Set α) := Set.disjoint_singleton_right.mpr (by simpa using hT.1 hx)
  have hs : (C i)ᶜ ∪ {x} ⊆ (C k)ᶜ := Set.union_subset (Set.compl_subset_compl.mpr hki.le) (Set.singleton_subset_iff.mpr hout)
  have hle := probability_mono p hs
  rw [← he, MeasureTheory.measureReal_union hd (measurableSet_singleton _),he,he] at hle
  have hp : 0 < probability p {x} := by
    unfold probability; rw [PMF.toOuterMeasure_apply_singleton]
    exact ENNReal.toReal_pos (hTs hx) (p.apply_ne_top x)
  change risk p (C i) + _ ≤ risk p (C k) at hle
  rw [show risk p (C i) = _ from hi,show risk p (C k) = _ from hk] at hle
  linarith

private def eligible (C : Generic.LanguageFamily α) (w : ℕ) (xs : List α) (i : ℕ) :=
  i < w ∧ ∀ j < w, -(2/(w:ℝ)) < score C xs j - score C xs i

/-- Algorithm 2. Among near-minimizers prefer the first with a tell-tale
already observed. The final default only applies to an empty window. -/
def algorithmTwo (C : Generic.LanguageFamily α) (f : ℕ → ℕ) (xs : List α) : ℕ :=
  let E := eligible C (f xs.length) xs
  if h : ∃ i, E i ∧ visible C i {x | x ∈ xs} then Nat.find h
  else if h : ∃ i, E i then Nat.find h else 0

theorem minimal_near_exponential [Countable α] (C : Generic.LanguageFamily α)
    (f : ℕ → ℕ) (hf : Tendsto f atTop atTop) (p : PMF α) (htell : HasSupportedTellTale C p) :
    ∃ c > (0:ℝ), ∃ d > (0:ℝ), ∀ᶠ n : ℕ in atTop,
      idP C (deterministic (algorithmTwo C f)) p n ≤ c*f n * Real.exp (-d*n/(f n)^2) := by
  have hex : ∃ i, Optimal C p i ∧ visible C i p.support := htell
  let z := Nat.find hex
  obtain ⟨hz,hv⟩ := Nat.find_spec hex
  change Optimal C p z at hz
  change visible C z p.support at hv
  have hminimal := minimal_of_visible C p z hz hv
  obtain ⟨T,hT,hS⟩ := hv
  obtain ⟨b,hb,hmiss⟩ := finite_missing_exponential p T (fun x h ↦ hS h)
  let d := min b (1/2 : ℝ)
  refine ⟨2+T.card,by positivity,d,lt_min hb (by norm_num),?_⟩
  have prior (j) (hj : j < z) (hvj : visible C j p.support) : risk p (C z) < risk p (C j) := by
    apply lt_of_le_of_ne ((optimal_iff ..).mp hz j)
    exact fun he ↦ Nat.find_min hex hj ⟨he.symm.trans hz,hvj⟩
  filter_upwards [earlier_gaps C p f hf z _ prior, hf.eventually (eventually_ge_atTop (z+1)),
    eventually_ge_atTop 1] with n hgap hwindow hn
  have hw : 0 < f n := by omega
  let bad := {xs | ¬withinWindow C p (f n) xs}
  let missing := {xs : List α | ¬∀ x ∈ T, x ∈ xs}
  apply (probability_deterministic (samples p n) (algorithmTwo C f) {j | ¬ MinimalOptimal C p j}).le.trans
  rw [← probability_inter_support]
  apply le_trans (probability_mono _ (F := bad ∪ missing) ?_) ((probability_union_le _ _ _).trans ?_)
  · rintro xs ⟨hbad,hs⟩
    by_contra! hout
    have hg : withinWindow C p (f n) xs := by by_contra h; exact hout (Or.inl h)
    have hcov : ∀ x ∈ T, x ∈ xs := by by_contra h; exact hout (Or.inr h)
    obtain ⟨hlen,hs'⟩ := (samples_support p n xs).mp hs
    have hzwin : z < f n := by omega
    let E := fun i ↦ eligible C (f n) xs i ∧ visible C i {x | x ∈ xs}
    have hpos : (0:ℝ) < f n := by exact_mod_cast hw
    have hez : E z := by
      refine ⟨⟨hzwin,fun j hj ↦ ?_⟩,T,hT,hcov⟩
      have h := (abs_lt.mp (diff_error C p hg hj hzwin)).1
      have := (optimal_iff ..).mp hz j
      simp only [div_eq_mul_inv] at h ⊢
      linarith [inv_pos.mpr hpos]
    have hexs : ∃ i, E i := ⟨z,hez⟩
    let k := Nat.find hexs
    have hek : E k := Nat.find_spec hexs
    have hkz : k ≤ z := Nat.find_min' hexs hez
    have he : k = z := by
      by_contra! hne
      have hklt : k < z := by omega
      obtain ⟨U,hu,hu'⟩ := hek.2
      have hd := hgap k hklt ⟨U,hu,fun x hx ↦ hs' x (hu' hx)⟩
      have he₁ := hek.1.2 z hzwin
      have he₂ := (abs_lt.mp (diff_error C p hg hzwin hek.1.1)).2
      simp only [div_eq_mul_inv] at hd he₁ he₂
      linarith
    apply hbad
    have hout' : algorithmTwo C f xs = k := by
      simp only [algorithmTwo,hlen]
      exact dif_pos hexs
    rwa [hout',he]
  · have hg := window_failure C p hn hw
    have hm := hmiss n
    have hw' : (1:ℝ) ≤ f n := by exact_mod_cast hw
    have hs : 1 ≤ (f n:ℝ)^2 := by nlinarith
    have ed : Real.exp (-b*n) ≤ Real.exp (-d*n/(f n)^2) := by
      apply Real.exp_le_exp.mpr
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [mul_nonneg (show 0 ≤ b*(n:ℝ) by positivity) (sub_nonneg.mpr hs),
        mul_nonneg (sub_nonneg.mpr (min_le_left b (1/2:ℝ))) (Nat.cast_nonneg n)]
    have eg : Real.exp (-(n:ℝ)/(2*(f n)^2)) ≤ Real.exp (-d*n/(f n)^2) := by
      apply Real.exp_le_exp.mpr
      rw [show -(n:ℝ)/(2*(f n)^2) = (-(1/2 : ℝ)*n)/(f n)^2 by ring]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right b (1/2:ℝ))) (Nat.cast_nonneg n)) (sq_nonneg _)
    apply (add_le_add hg hm).trans
    calc
      _ ≤ 2*(f n:ℝ)*Real.exp (-d*n/(f n)^2) + T.card*Real.exp (-d*n/(f n)^2) := by gcongr
      _ ≤ _ := by
        have hcoef := mul_le_mul_of_nonneg_left hw' (Nat.cast_nonneg T.card)
        nlinarith [mul_nonneg (sub_nonneg.mpr hcoef) (Real.exp_nonneg (-d*n/(f n)^2))]

end
end GenLimit.AgnosticLanguage
