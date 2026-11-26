import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.SlowModel

/-! # Random labels on one finite block

Flip every label that the training sample missed. The training words and
hence the randomized output law agree under the two labelings. On each
unseen coordinate at least one of their predictions is wrong. -/
namespace GenLimit.AgnosticLanguage.Slow
open DiscreteIID LiRamanTewari Filter
open scoped Classical
noncomputable section

abbrev Bits (n : ℕ) := Fin (4*n+1) → Bool

def patch (s : ℕ → ℕ) (k n : ℕ) (b : Bits n) (x : ℕ) : ℕ :=
  if h : x.unpair.1 = k ∧ x.unpair.2 < 4*n+1 then if b ⟨x.unpair.2,h.2⟩ then 1 else 0 else s x

theorem patch_below (s : ℕ → ℕ) (k n : ℕ) (b : Bits n) (x : ℕ) (hx : x < k) :
    patch s k n b x = s x := by
  have hn : x.unpair.1 ≠ k := by have := Nat.unpair_left_le x; omega
  simp [patch,hn]

private theorem tag_patch (s : ℕ → ℕ) (k n : ℕ) (b : Bits n) (j : Fin (4*n+1)) :
    tag (patch s k n b) (Nat.pair k j.val) = (Nat.pair k j.val,some (b j)) := by
  cases h : b j <;> simp [tag,patch,Nat.unpair_pair,j.isLt,h]

private def flip (xs : List ℕ) (k n : ℕ) (b : Bits n) (j : Fin (4*n+1)) :=
  if Nat.pair k j.val ∈ xs then b j else !(b j)

private theorem flip_involution (xs : List ℕ) (k n) : Function.Involutive (flip xs k n) := by
  intro b; funext j; by_cases h : Nat.pair k j.val ∈ xs <;> simp [flip,h]

private theorem flip_sample (s : ℕ → ℕ) (k n : ℕ) (b : Bits n) (xs : List ℕ) :
    xs.map (tag (patch s k n (flip xs k n b))) = xs.map (tag (patch s k n b)) := by
  apply List.map_congr_left
  intro x hx
  by_cases hh : x.unpair.1 = k ∧ x.unpair.2 < 4*n+1
  · have he : Nat.pair k x.unpair.2 = x := by rw [←hh.1,Nat.pair_unpair]
    simp [tag,patch,hh,flip,he,hx]
  · simp [tag,patch,hh]

private theorem uniform_seen (k n) (xs : List ℕ) (hlen : xs.length = n) :
    probability (PMF.uniformOfFintype (Fin (4*n+1))) {j | Nat.pair k j.val ∈ xs} ≤ 1/4 := by
  let S := {j : Fin (4*n+1) | Nat.pair k j.val ∈ xs}
  let f : S → ↥xs.toFinset := fun j ↦ ⟨Nat.pair k j.1.val,List.mem_toFinset.mpr j.2⟩
  have inj : Function.Injective f := fun a b h ↦ Subtype.ext (Fin.ext
    ((Nat.pair_eq_pair.mp (congrArg (fun z : ↥xs.toFinset ↦ z.val) h)).2))
  have hc := Fintype.card_le_of_injective f inj
  rw [Fintype.card_coe] at hc
  have hcard : (Fintype.card S : ℝ) ≤ n := by exact_mod_cast hc.trans (xs.toFinset_card_le.trans_eq hlen)
  change probability _ S ≤ _
  rw [probability,PMF.toOuterMeasure_uniformOfFintype_apply,ENNReal.toReal_div]
  rw [ENNReal.toReal_natCast,ENNReal.toReal_natCast,Fintype.card_fin]
  push_cast
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

private theorem pair_error (s : ℕ → ℕ) (k n) (b : Bits n) (xs : List ℕ) (hlen : xs.length = n) (i : ℕ) :
    3/4 ≤ probability ((uniformBlock k n).map (misses i (patch s k n b))) {true} +
      probability ((uniformBlock k n).map (misses i (patch s k n (flip xs k n b)))) {true} := by
  let U := PMF.uniformOfFintype (Fin (4*n+1))
  let bad (v : Bits n) := {j : Fin (4*n+1) | tag (patch s k n v) (Nat.pair k j.val) ∉ family i}
  have he (v : Bits n) : probability ((uniformBlock k n).map (misses i (patch s k n v))) {true} = probability U (bad v) := by
    rw [trial_each,uniformBlock,probability_map_preimage]; rfl
  rw [he,he]
  have hsub : {j : Fin (4*n+1) | Nat.pair k j.val ∈ xs}ᶜ ⊆ bad b ∪ bad (flip xs k n b) := by
    intro j hj
    change Nat.pair k j.val ∉ xs at hj
    change _ ∉ family i ∨ _ ∉ family i
    rw [tag_patch,tag_patch]
    have h := unique_label i (Nat.pair k j.val)
    cases hb : b j <;> simp [flip,hj,hb] <;> tauto
  have h := (probability_mono U hsub).trans (probability_union_le U _ _)
  rw [probability_compl] at h
  have hs := uniform_seen k n xs hlen
  change probability U _ ≤ 1/4 at hs
  linarith

private theorem sum_weights (p : PMF α) (r : ℝ) : ∑' a, (p a).toReal * r = r := by
  rw [tsum_mul_right,←ENNReal.tsum_toReal_eq p.apply_ne_top,p.tsum_coe,ENNReal.toReal_one,one_mul]

private theorem integrate_pair (o : PMF ℕ) (f g : ℕ → PMF Bool)
    (h : ∀ i, 3/4 ≤ probability (f i) {true} + probability (g i) {true}) :
    3/4 ≤ probability (o.bind f) {true} + probability (o.bind g) {true} := by
  have summ (v : ℕ → PMF Bool) := weighted_summable o (v := fun i ↦ probability (v i) {true})
    (fun _ ↦ ⟨probability_nonneg ..,probability_le_one ..⟩)
  rw [probability_bind_eq_tsum,probability_bind_eq_tsum,←(summ f).tsum_add (summ g)]
  rw [←sum_weights o (3/4)]
  apply Summable.tsum_le_tsum _ ((ENNReal.summable_toReal o.tsum_coe_ne_top).mul_right _) ((summ f).add (summ g))
  intro i
  rw [←mul_add]
  exact mul_le_mul_of_nonneg_left (h i) ENNReal.toReal_nonneg

private theorem uniform_kernel (v : α → PMF Bool) [Fintype α] [Nonempty α] :
    probability ((PMF.uniformOfFintype α).bind v) {true} =
      (Fintype.card α : ℝ)⁻¹ * ∑ b, probability (v b) {true} := by
  simp [probability_bind_eq_tsum,tsum_fintype,PMF.uniformOfFintype_apply,Finset.mul_sum]

private theorem mean_lower (p : PMF α) (f : α → PMF Bool) (r : ℝ)
    (h : ∀ a ∈ p.support, r ≤ probability (f a) {true}) : r ≤ probability (p.bind f) {true} := by
  rw [←sum_weights p r,probability_bind_eq_tsum]
  apply Summable.tsum_le_tsum _ ((ENNReal.summable_toReal p.tsum_coe_ne_top).mul_right _)
    (weighted_summable _ (fun _ ↦ ⟨probability_nonneg ..,probability_le_one ..⟩))
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg

theorem exists_hard_patch (A : Identifier Word) (μ : PMF ℕ) (s : ℕ → ℕ) (k n : ℕ) :
    ∃ b : Bits n, 1/8 < experiment A μ (uniformBlock k n) n (patch s k n b) := by
  let v := PMF.uniformOfFintype (Bits n)
  let draws := samples μ n
  let L := fun (b : Bits n) (xs : List ℕ) ↦
    trial (uniformBlock k n) (patch s k n b) (A (xs.map (tag (patch s k n b))))
  have lower : 1/4 ≤ probability (draws.bind fun xs ↦ v.bind fun b ↦ L b xs) {true} := by
    apply mean_lower
    intro xs hxs
    have hlen := ((samples_support μ n xs).mp hxs).1
    let e := (flip_involution xs k n).toPerm
    let f := fun b ↦ probability (L b xs) {true}
    have hh (b : Bits n) : 3/4 ≤ f b + f (e b) := by
      change 3/4 ≤ probability (trial _ _ (A (xs.map (tag (patch s k n b))))) {true} + probability (trial _ _ (A (xs.map (tag (patch s k n (flip xs k n b)))))) {true}
      rw [flip_sample]
      exact integrate_pair _ _ _ (pair_error s k n b xs hlen)
    have hs := Finset.sum_le_sum (s := Finset.univ) fun b _ ↦ hh b
    rw [Finset.sum_add_distrib,Equiv.sum_comp e f] at hs
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
    rw [uniform_kernel]
    change 1/4 ≤ (Fintype.card (Bits n) : ℝ)⁻¹ * ∑ b, f b
    rw [←div_eq_inv_mul,le_div_iff₀ (by exact_mod_cast Fintype.card_pos)]
    linarith
  rw [←PMF.bind_comm v draws L] at lower
  by_contra! h
  have upper : probability (v.bind fun b ↦ draws.bind (L b)) {true} ≤ 1/8 := by
    rw [uniform_kernel]
    rw [←div_eq_inv_mul,div_le_iff₀ (by exact_mod_cast Fintype.card_pos)]
    have hs := Finset.sum_le_sum (s := Finset.univ) fun b _ ↦ h b
    simpa [experiment,L,draws,mul_comm] using hs
  linarith

end
end GenLimit.AgnosticLanguage.Slow
