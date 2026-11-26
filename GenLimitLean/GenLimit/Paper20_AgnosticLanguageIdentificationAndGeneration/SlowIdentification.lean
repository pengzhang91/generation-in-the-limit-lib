import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.UnseenLabels

/-! # Arbitrarily slow excess risk under an unattained optimum

The marginal gives block k fixed positive mass, and its number of labels
exceeds four times the chosen sample size. Each finite-sample block loss is
continuous in the full labeling. The finite-block lower bound is dense in
every cylinder that fixes earlier labels. Baire's theorem supplies one
labeling witnessing the lower bound infinitely often. -/
namespace GenLimit.AgnosticLanguage.Slow
open DiscreteIID Filter
open scoped Classical Topology
noncomputable section

private theorem continuous_trial (A : Identifier Word) (k n : ℕ) (xs : List ℕ) :
    Continuous (fun s ↦ probability (trial (uniformBlock k n) s (A (xs.map (tag s)))) {true}) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  let coord := fun j : Fin (4*n+1) ↦ Nat.pair k j.val
  let B := max (xs.toFinset.sup id) (Finset.univ.sup coord) + 1
  have hlocal : ∀ᶠ t in 𝓝 s,
      probability (trial (uniformBlock k n) t (A (xs.map (tag t)))) {true} =
      probability (trial (uniformBlock k n) s (A (xs.map (tag s)))) {true} := by
    filter_upwards [(PiNat.isOpen_cylinder _ s B).mem_nhds (PiNat.self_mem_cylinder s B)] with t ht
    have same (x) (hx : x < B) : tag t x = tag s x := by simp [tag,PiNat.mem_cylinder_iff.mp ht x hx]
    have hs : xs.map (tag t) = xs.map (tag s) := List.map_congr_left fun x hx ↦
      same x (Nat.lt_succ_of_le ((Finset.le_sup (f := id) (List.mem_toFinset.mpr hx)).trans (le_max_left ..)))
    have hu (i) : (uniformBlock k n).map (misses i t) = (uniformBlock k n).map (misses i s) := by
      simp only [uniformBlock,PMF.map_comp]
      congr 1
      funext j
      have hj := same (coord j) (Nat.lt_succ_of_le ((Finset.le_sup (f := coord) (Finset.mem_univ j)).trans (le_max_right ..)))
      change decide (tag t (coord j) ∉ family i) = decide (tag s (coord j) ∉ family i)
      rw [hj]
    simp only [trial,hs,hu]
  apply continuousAt_const.congr
  exact hlocal.mono fun _ ht ↦ ht.symm

private theorem continuous_experiment (A : Identifier Word) (μ : PMF ℕ) (k n : ℕ) :
    Continuous (experiment A μ (uniformBlock k n) n) := by
  change Continuous (fun s ↦ probability ((samples μ n).bind fun xs ↦ trial (uniformBlock k n) s (A (xs.map (tag s)))) {true})
  simp_rw [probability_bind_eq_tsum (samples μ n)]
  apply continuous_tsum
  · intro xs; exact continuous_const.mul (continuous_trial A k n xs)
  · exact ENNReal.summable_toReal (samples μ n).tsum_coe_ne_top
  · intro xs s
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (probability_nonneg ..))]
    exact mul_le_mul_of_nonneg_left (probability_le_one ..) ENNReal.toReal_nonneg |>.trans_eq (mul_one _)

theorem arbitrary_slow_identification (A : Identifier Word) (R : ℕ → ℝ) (hR : Tendsto R atTop (𝓝 0)) :
    ∃ p : PMF Word, (¬∃ i, Optimal family p i) ∧ ∃ᶠ n : ℕ in atTop, R n / 8 ≤ idErr family A p n := by
  have ht (k) : ∃ n ≥ k, R n < weight k := ((eventually_ge_atTop k).and (hR.eventually_lt_const (weight_pos k))).exists
  choose N hN hR' using ht
  let μ := marginal N
  let H (m : ℕ) := ⋃ k ≥ m, {s : ℕ → ℕ | 1/8 < experiment A μ (uniformBlock k (N k)) (N k) s}
  have hopen (m) : IsOpen (H m) :=
    isOpen_iUnion fun k ↦ isOpen_iUnion fun _ ↦ isOpen_lt continuous_const (continuous_experiment ..)
  have hdense (m) : Dense (H m) := by
    apply dense_iff_inter_open.mpr
    rintro U hU ⟨s,hs⟩
    obtain ⟨_,⟨t,c,rfl⟩,_,hsub⟩ :=
      (PiNat.isTopologicalBasis_cylinders (fun _ ↦ ℕ)).exists_subset_of_mem_open hs hU
    let k := max m c
    obtain ⟨b,hb⟩ := exists_hard_patch A μ t k (N k)
    refine ⟨patch t k (N k) b,hsub (PiNat.mem_cylinder_iff.mpr fun x hx ↦ patch_below t k (N k) b x (hx.trans_le (le_max_right ..))),?_⟩
    exact Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨le_max_left ..,hb⟩⟩
  letI := baire_natSequences
  obtain ⟨s,hs⟩ := (dense_iInter_of_isOpen hopen hdense).nonempty
  refine ⟨μ.map (tag s),no_optimum N s,frequently_atTop.mpr fun m ↦ ?_⟩
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hs m)
  obtain ⟨hm,hb⟩ := Set.mem_iUnion.mp hk
  refine ⟨N k,hm.trans (hN k),?_⟩
  apply le_trans _ (block_lower A N s (N k) k)
  have := mul_le_mul_of_nonneg_left (le_of_lt hb) (weight_pos k).le
  linarith [hR' k]

end
end GenLimit.AgnosticLanguage.Slow
