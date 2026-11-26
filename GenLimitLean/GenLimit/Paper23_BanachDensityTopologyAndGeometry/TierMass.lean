import GenLimit.Paper23_BanachDensityTopologyAndGeometry.TierWeights

/-! Summing all overlapping trace events in the multi-level local lemma. -/
namespace GenLimit.KleinbergWei.Banach.TierWeights
open Finset Real
open scoped Classical
noncomputable section
variable {I V : Type*}

theorem point_mass (S : Finset I) (size tier : I → ℕ) {p η : ℝ}
    (hp : 0 ≤ p) (hη : 0 ≤ η) (positive : ∀ i ∈ S, 0 < size i)
    (cap : ∀ k j, ((S.filter (fun i => (size i,tier i) = (k,j))).card : ℝ) ≤ η*capacityFactor p k j) :
    ∑ i ∈ S, weight p (size i) (tier i) ≤ η*π^2/6 := by
  let K := S.image size
  let J := S.image tier
  let ij (i : I) := (size i,tier i)
  have mem (i) (hi : i ∈ S) : ij i ∈ K ×ˢ J :=
    Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hi,Finset.mem_image_of_mem _ hi⟩
  have hk (k) (h : k ∈ K) : 0 < k := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    exact positive i hi
  have geom : ∑ j ∈ J, (1/2:ℝ)^j ≤ 2 := by
    have h := sum_le_hasSum J (fun j _ => by positivity : ∀ j ∉ J, 0 ≤ (1/2:ℝ)^j)
      (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num))
    norm_num at h
    exact h
  have basel : ∑ k ∈ K, 1/(k:ℝ)^2 ≤ π^2/6 :=
    sum_le_hasSum K (fun _ _ => by positivity) hasSum_zeta_two
  calc
    _ = ∑ t ∈ K ×ˢ J, ((S.filter (fun i => ij i = t)).card : ℝ) * weight p t.1 t.2 := by
      simpa [nsmul_eq_mul,ij] using
        (Finset.sum_fiberwise_of_maps_to' mem (fun t => weight p t.1 t.2)).symm
    _ ≤ ∑ t ∈ K ×ˢ J, η * ((1/2:ℝ)*(1/(t.1:ℝ)^2)*(1/2:ℝ)^t.2) := by
      apply Finset.sum_le_sum
      rintro ⟨k,j⟩ h
      have pos := hk k (Finset.mem_product.mp h).1
      calc
        _ ≤ (η*capacityFactor p k j)*weight p k j :=
          mul_le_mul_of_nonneg_right (cap k j) (weight_bounds hp pos j).1
        _ = _ := by rw [mul_assoc,cancel_capacity p pos]
    _ = η/2*(∑ k ∈ K, 1/(k:ℝ)^2)*(∑ j ∈ J, (1/2:ℝ)^j) := by
      rw [Finset.sum_product,mul_assoc (η/2),Finset.sum_mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    _ ≤ η*π^2/6 := by
      have h₁ := mul_le_mul_of_nonneg_left geom
        (show 0 ≤ η/2 * ∑ k ∈ K, 1/(k:ℝ)^2 by positivity)
      have h₂ := mul_le_mul_of_nonneg_left basel hη
      linarith

/-- An event intersecting a trace is counted at least once when summing
over its points. The overlap is harmless for nonnegative weights. -/
theorem neighbors_mass [DecidableEq V] [Fintype I] (T : Finset V) (trace : I → Finset V)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) {b : ℝ}
    (perPoint : ∀ v, ∑ i ∈ Finset.univ.filter (fun i => v ∈ trace i), w i ≤ b) :
    ∑ i ∈ Finset.univ.filter (fun i => ¬Disjoint T (trace i)), w i ≤ T.card*b := by
  classical
  calc
    _ ≤ ∑ i : I, ∑ v ∈ T, if v ∈ trace i then w i else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro i _
      by_cases apart : Disjoint T (trace i)
      · rw [if_neg (not_not_intro apart)]
        apply Finset.sum_nonneg; intro v _; split <;> simp [hw]
      · rw [if_pos apart]
        obtain ⟨v,mem,inI⟩ := Finset.not_disjoint_iff.mp apart
        have h := Finset.single_le_sum (s := T) (f := fun u => if u ∈ trace i then w i else 0)
          (fun u _ => by dsimp only; split <;> simp [hw]) mem
        simpa only [if_pos inI] using h
    _ = ∑ v ∈ T, ∑ i ∈ Finset.univ.filter (fun i => v ∈ trace i), w i := by
      rw [Finset.sum_comm]; simp only [Finset.sum_filter]
    _ ≤ ∑ _ ∈ T, b := Finset.sum_le_sum (fun v _ => perPoint v)
    _ = _ := by simp

theorem product_lower (S : Finset I) (w : I → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i ∧ w i ≤ 1/2) :
    exp (-2 * ∑ i ∈ S, w i) ≤ ∏ i ∈ S, (1-w i) := by
  rw [Finset.mul_sum,Real.exp_sum]
  apply Finset.prod_le_prod (fun _ _ => (exp_pos _).le)
  intro i hi
  have ⟨lo,up⟩ := hw i hi
  rw [neg_mul,exp_neg,inv_le_iff_one_le_mul₀ (exp_pos _)]
  have linear := Real.add_one_le_exp (2*w i)
  nlinarith [mul_nonneg lo (show 0 ≤ 1-2*w i by linarith),
    mul_le_mul_of_nonneg_right linear (show 0 ≤ 1-w i by linarith)]

end
end GenLimit.KleinbergWei.Banach.TierWeights
