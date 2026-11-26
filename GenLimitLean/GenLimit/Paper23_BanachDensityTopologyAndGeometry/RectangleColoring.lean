import GenLimit.Paper23_BanachDensityTopologyAndGeometry.TierMass
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.TierGeometry
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RandomSigns

/-! The global simultaneous discrepancy bound of Theorem 5.9 with dense
overflow in tier zero and side length counted in lattice sites. -/
namespace GenLimit.KleinbergWei.Banach
open Real Finset TierWeights TierGeometry
open scoped Classical
noncomputable section

private theorem finite_rectangle_coloring {d : ℕ} (hd : 0 < d) (P : Set (Lattice d))
    (ε α : ℝ) (he : 0 < ε) (ha : 0 < α) (F : Finset (Index P)) :
    ∃ color : Lattice d → Bool, ∀ r ∈ F,
      |∑ v ∈ trace r, RandomSigns.sign (color v)| ≤
        threshold ε (scale d α) (trace r).card (boxTier ε α r) := by
  let p := scale d α
  let T (i : F) := trace i.val
  let m (i : F) := (T i).card
  let j (i : F) := boxTier ε α i.val
  let w (i : F) := weight p (m i) (j i)
  let limit (i : F) := threshold ε p (m i) (j i)
  have mp (i : F) : 0 < m i := i.val.property.card_pos
  have dp : (0:ℝ) < d := by exact_mod_cast hd
  have pp : 0 ≤ p := by unfold p scale; positivity
  have et : 0 ≤ eta ε := by unfold eta; positivity
  have weights (i : F) : 0 ≤ w i ∧ w i ≤ 1/2 := weight_bounds pp (mp i) (j i)
  have mass (v : Lattice d) :
      ∑ i ∈ Finset.univ.filter (fun i : F => v ∈ T i), w i ≤ eta ε*π^2/6 := by
    let S := Finset.univ.filter (fun i : F => v ∈ T i)
    apply point_mass S m j pp et (fun i _ => mp i)
    intro k n
    let D := S.filter fun i => (m i,j i) = (k,n)
    have geo := local_count hd he ha (D.image Subtype.val) v k n (by
      intro r hr
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨hs,eq⟩ := Finset.mem_filter.mp hi
      exact ⟨(Finset.mem_filter.mp hs).2,congrArg Prod.fst eq,congrArg Prod.snd eq⟩)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using geo
  have per (i : F) := neighbors_mass (b := eta ε*π^2/6) (T i) T w (fun a => (weights a).1)
    (fun v => by simpa only [Finset.sum_filter] using mass v)
  have expfit (i : F) : exp (-ε^2*m i/2) ≤
      ∏ a ∈ Finset.univ.filter (fun a => ¬Disjoint (T i) (T a)), (1-w a) := by
    apply le_trans _ (product_lower _ w (fun a _ => weights a))
    apply Real.exp_le_exp.mpr
    have factor : eta ε * π^2 / 6 = ε^2/4 := by
      unfold eta; field_simp [Real.pi_ne_zero]; ring
    have h := per i
    rw [factor] at h
    change _ ≤ (m i:ℝ)*(ε^2/4) at h
    linarith
  obtain ⟨c,hc⟩ := RandomSigns.finite_coloring T limit w (fun i => threshold_nonneg he.le ..)
    (fun i => ⟨(weights i).1,lt_of_le_of_lt (weights i).2 (by norm_num)⟩)
    (fun i => (tail_fits he.le pp (mp i) (j i)).trans (mul_le_mul_of_nonneg_left (expfit i) (weights i).1))
  exact ⟨c,fun r hr => hc ⟨r,hr⟩⟩

/-- One coloring controls every integer rectangle simultaneously, even
when P is infinite. A side with endpoints a and b spans b−a+1 sites. -/
theorem rectangle_coloring {d : ℕ} (hd : 0 < d) (P : Set (Lattice d))
    (ε α : ℝ) (he : 0 < ε) (ha : 0 < α) :
    ∃ color : Lattice d → Bool, ∀ l u, ∀ h : (Rectangles.box P l u).Nonempty,
      let m := (Rectangles.box P l u).card
      let j := tier (baseline ε α d * (span l u : ℝ)^α) m h.card_pos
      |∑ v ∈ Rectangles.box P l u, RandomSigns.sign (color v)| ≤ threshold ε (scale d α) m j := by
  let ok (r : Index P) (c : trace r → Bool) :=
    |∑ v, RandomSigns.sign (c v)| ≤ threshold ε (scale d α) (trace r).card (boxTier ε α r)
  obtain ⟨c,spec⟩ := DiscrepancyBoxes.global_coloring (@trace d P) ok (by
    intro F
    obtain ⟨c,good⟩ := finite_rectangle_coloring hd P ε α he ha F
    refine ⟨c,fun r hr => ?_⟩
    change |∑ v ∈ (trace r).attach, RandomSigns.sign (c v.val)| ≤ _
    rw [Finset.sum_attach (trace r) (fun v => RandomSigns.sign (c v))]
    exact good r hr)
  refine ⟨c,fun l u h => ?_⟩
  let r : Index P := ⟨(l,u),h⟩
  have hit := spec r
  change |∑ v ∈ (trace r).attach, RandomSigns.sign (c v.val)| ≤ _ at hit
  rw [Finset.sum_attach (trace r) (fun v => RandomSigns.sign (c v))] at hit
  exact hit

end
end GenLimit.KleinbergWei.Banach
