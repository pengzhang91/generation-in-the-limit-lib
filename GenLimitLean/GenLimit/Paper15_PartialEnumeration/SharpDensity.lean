import GenLimit.Paper15_PartialEnumeration.Sharpness
import GenLimit.Bridges.Paper39ToPaper15

/-! # The sharp α/2 upper-density bound
The adversary enumerates an increasing copy of the natural numbers of
density exactly α in a larger target. Validity on the smaller target forces
all but finitely many outputs into that copy. The sharp prefix count on its
ranks then bounds the upper density in the larger target. -/
namespace GenLimit.KleinbergWei.PartialEnumeration.Sharpness
open Filter Set
open scoped Topology Classical

def natural : OrderedLanguage := ⟨univ,id,Function.injective_id,range_id⟩
noncomputable def thin (α : ℝ) (j : ℕ) := ⌊(j : ℝ)/α⌋₊

theorem thin_strict {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1) : StrictMono (thin α) := by
  apply strictMono_nat_of_lt_succ
  intro n
  change ⌊(n : ℝ)/α⌋₊ + 1 ≤ ⌊((n+1 : ℕ) : ℝ)/α⌋₊
  apply Nat.le_floor
  push_cast
  have h := Nat.floor_le (by positivity : 0 ≤ (n : ℝ)/α)
  have : (n : ℝ)/α + 1 ≤ (n+1)/α := by
    rw [le_div_iff₀ ha,add_mul,div_mul_cancel₀ _ ha.ne']; linarith
  linarith

private theorem thin_lt {α : ℝ} (ha : 0 < α) (n j : ℕ) :
    thin α j < n ↔ j < ⌈(n : ℝ)*α⌉₊ := by
  rw [thin,Nat.floor_lt (by positivity),div_lt_iff₀ ha,Nat.lt_ceil]

private theorem prefix_image {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1) (A : Set ℕ) (n : ℕ) :
    natural.prefixCount (thin α '' A) n =
      ((Finset.range ⌈(n : ℝ)*α⌉₊).filter (fun j ↦ j ∈ A)).card := by
  let F := (Finset.range ⌈(n : ℝ)*α⌉₊).filter (fun j ↦ j ∈ A)
  have he : ((Finset.range n).filter (fun x ↦ x ∈ thin α '' A)) = F.image (thin α) := by
    ext x
    constructor
    · rintro hx
      obtain ⟨hn,j,hj,rfl⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr ((thin_lt ha n j).mp (Finset.mem_range.mp hn)),hj⟩,rfl⟩
    · intro hx
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hn,h⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((thin_lt ha n j).mpr (Finset.mem_range.mp hn)),⟨j,h,rfl⟩⟩
  change ((Finset.range n).filter (fun x ↦ x ∈ thin α '' A)).card = F.card
  rw [he,Finset.card_image_of_injective _ (thin_strict ha ha1).injective]

theorem thin_density_ge {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1) :
    α ≤ natural.lowerDensity (range (thin α)) := by
  unfold OrderedLanguage.lowerDensity
  apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (fun n ↦ natural.prefixRatio_le_one _ n))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [OrderedLanguage.prefixRatio,if_neg (by omega),← image_univ,prefix_image ha ha1]
  simp only [mem_univ,Finset.filter_true,Finset.card_range]
  exact (le_div_iff₀ hpos).mpr (by simpa [mul_comm] using Nat.le_ceil ((n : ℝ)*α))

private theorem small_error (T : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (T : ℝ)+n.sqrt+2 ≤ 2*δ*n := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max (((T : ℝ)+2)/δ) (1/δ^2))
  filter_upwards [eventually_ge_atTop N] with n hn
  have b : max (((T : ℝ)+2)/δ) (1/δ^2) ≤ (n : ℝ) := hN.le.trans (by exact_mod_cast hn)
  have hT := (div_le_iff₀ hδ).mp ((le_max_left _ _).trans b)
  have h1 := (div_le_iff₀ (sq_pos_of_pos hδ)).mp ((le_max_right _ _).trans b)
  have hs : (n.sqrt : ℝ)^2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
  have hsq : (n.sqrt : ℝ)^2 ≤ (δ*n)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (Nat.cast_nonneg (α := ℝ) n)]
  have h := (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  linarith

theorem diluted_upper {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1) (G : List ℕ → ℕ)
    (T : ℕ) (hf : FreshAfter G T) :
    natural.upperDensity (thin α '' range (output G)) ≤ α/2 := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun n ↦ natural.prefixRatio_nonneg _ n))
  filter_upwards [small_error T hδ,eventually_ge_atTop 1] with n he hn
  let m := ⌈(n : ℝ)*α⌉₊
  have hm : m ≤ n := Nat.ceil_le.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hceil : (m : ℝ) < (n : ℝ)*α+1 := Nat.ceil_lt_add_one (by positivity)
  have hsq : (m.sqrt : ℝ) ≤ n.sqrt := by exact_mod_cast Nat.sqrt_le_sqrt hm
  rw [OrderedLanguage.prefixRatio,if_neg (by omega),prefix_image ha ha1]
  apply (div_le_iff₀ hpos).mpr
  have hcount := prefix_bound G T hf m
  have hc : 2 * (((Finset.range m).filter (fun x ↦ x ∈ range (output G))).card : ℝ) ≤
      m + T + m.sqrt + 1 := by exact_mod_cast hcount
  change (((Finset.range m).filter _).card : ℝ) ≤ _
  nlinarith

private noncomputable def inverse (f : ℕ → ℕ) (x : ℕ) := if h : x ∈ range f then h.choose else 0

private theorem right_inverse (f : ℕ → ℕ) {x : ℕ} (hx : x ∈ range f) : f (inverse f x) = x := by
  simpa [inverse,hx] using hx.choose_spec

/-- The lower bound adversary against *any* causal element generator valid
on the smaller language. The same complete text is an α-dense partial text
of the larger language ℕ. -/
theorem theorem_3_3_sharp {α : ℝ} (ha : 0 < α) (ha1 : α ≤ 1) (A : List ℕ → ℕ)
    (valid : ∀ s : ℕ → ℕ, range s = range (thin α) →
      ∃ T, ∀ t ≥ T, A (textPrefix s (t+1)) ∈ range (thin α) ∧
        ∀ i ≤ t, s i ≠ A (textPrefix s (t+1))) :
    ∃ s : ℕ → ℕ, Function.Injective s ∧ range s = range (thin α) ∧
      α ≤ natural.lowerDensity (range s) ∧
      natural.upperDensity (range (fun t ↦ A (textPrefix s (t+1)))) ≤ α/2 := by
  let f := thin α
  let G (h : List ℕ) := inverse f (A (h.map f))
  let s := f ∘ stream G
  have hs : range s = range f := by rw [show s = f ∘ stream G from rfl,range_comp,presents,image_univ]
  have hf := (thin_strict ha ha1).injective
  refine ⟨s,hf.comp (stream_injective G),hs,hs ▸ thin_density_ge ha ha1,?_⟩
  obtain ⟨T,hT⟩ := valid s hs
  let gen (t : ℕ) := A (textPrefix s (t+1))
  have heq (t : ℕ) : output G t = inverse f (gen t) := by
    simp only [output,history_eq,G,gen,textPrefix,List.map_map,s]
  have correct (t : ℕ) (ht : T ≤ t) : f (output G t) = gen t := by
    rw [heq]; exact right_inverse _ (hT t ht).1
  have fresh : FreshAfter G T := by
    intro t ht i hi hh
    apply (hT t ht).2 i hi
    exact (congrArg f hh).trans (correct t ht)
  have small := diluted_upper ha ha1 G T fresh
  let early := (Finset.range T).image gen
  have sub : range gen ⊆ (f '' range (output G)) ∪ (↑early : Set ℕ) := by
    rintro _ ⟨t,rfl⟩
    by_cases ht : t < T
    · exact Or.inr (Finset.mem_image.mpr ⟨_,Finset.mem_range.mpr ht,rfl⟩)
    · exact Or.inl ⟨_,⟨t,rfl⟩,correct t (by omega)⟩
  have hb := (natural.upperDensity_mono sub).trans (natural.upperDensity_union_le _ _)
  simpa [natural.upperDensity_eq_zero_of_finite early.finite_toSet] using
    hb.trans (add_le_add_right small (natural.upperDensity early))

end GenLimit.KleinbergWei.PartialEnumeration.Sharpness
