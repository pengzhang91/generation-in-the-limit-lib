import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRankGeneration
import GenLimit.Paper15_PartialEnumeration.Sharpness

/-! The sharp speed-one upper bound for all positive window bounds on the
known target ℕ. The same P15 adversarial presentation works for all of them. -/
namespace GenLimit.KleinbergWei.Banach
open Set Filter DensityMeasures PartialEnumeration.Sharpness
open scoped Classical ENNReal

theorem singleton_rank_one :
    TowerTopology.FiniteRankAtMost (range fun _ : ℕ => (univ : Set ℕ)) 1 := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ⟨_,i,rfl⟩ ⟨_,limit⟩
  obtain ⟨⟨_,j,rfl⟩,_,ne,_⟩ := limit ∅ (by simp)
  exact ne (Subtype.ext rfl)

private theorem upper_windows (G : List ℕ → ℕ) {T} (fresh : FreshAfter G T)
    {f : ℕ → WithTop ℕ} (hf : AdmissibleWindowBound f) :
    lowerWindowDensity f (range (output G)) ≤ ENNReal.ofReal (1/2) := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  rcases eq_or_ne r ⊤ with rfl | finite
  · exact le_top
  have lt : (1/2 : ℝ) < r.toReal := by
    exact (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top finite).mpr hr |>.trans_eq'
      (by rw [ENNReal.toReal_ofReal (by norm_num)])
  let δ := 2*r.toReal-1
  have pos : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨b,hb⟩ := exists_nat_gt (2/δ)
  apply liminf_le_of_frequently_le' (frequently_atTop.mpr ?_)
  intro N
  let q := max b (max N (T+3))
  have qb : b ≤ q := le_max_left ..
  have qN : N ≤ q := (le_max_left ..).trans (le_max_right ..)
  have qT : T+3 ≤ q := (le_max_right ..).trans (le_max_right ..)
  have qpos : 0 < q := by omega
  let k := q*q
  have large : q ≤ k := by simpa [k] using Nat.mul_le_mul_left q qpos
  refine ⟨k,qN.trans large,iInf_le_of_le 1 ?_⟩
  rw [if_pos ⟨le_rfl,hf.2 k⟩]
  have count : windowCount (range (output G)) 1 k ≤
      ((Finset.range (k+1)).filter (· ∈ range (output G))).card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hx,mem⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := (Finset.mem_Ico.mp hx).2; omega),mem⟩
  have sq : (k+1).sqrt ≤ q+1 := by
    apply Nat.lt_succ_iff.mp
    apply Nat.sqrt_lt'.mpr
    dsimp [k]; nlinarith
  have bound := prefix_bound G T fresh (k+1)
  have natBound : 2*windowCount (range (output G)) 1 k ≤ k+2*q := by omega
  have realBound : 2*(windowCount (range (output G)) 1 k : ℝ) ≤ (k:ℝ)+2*q := by exact_mod_cast natBound
  have bq : (b:ℝ) ≤ q := by exact_mod_cast qb
  have bd := (div_lt_iff₀ pos).mp (hb.trans_le bq)
  have err := mul_le_mul_of_nonneg_right bd.le (Nat.cast_nonneg (α := ℝ) q)
  have keq : (k:ℝ) = (q:ℝ)*(q:ℝ) := by simp [k]
  have kp : (0:ℝ) < k := by exact_mod_cast qpos.trans_le large
  have rat : (windowCount (range (output G)) 1 k : ℝ)/k ≤ r.toReal := by
    apply (div_le_iff₀ kp).mpr
    dsimp only [δ] at err
    rw [keq] at realBound ⊢
    nlinarith
  simpa only [windowRatio,if_neg (qpos.trans_le large).ne',ENNReal.ofReal_div_of_pos kp,
    ENNReal.ofReal_natCast,ENNReal.ofReal_toReal finite] using ENNReal.ofReal_le_ofReal rat

theorem singleton_window_upper (A : List ℕ → ℕ)
    (valid : ∀ s, Presents s univ → OrderedFocus.ElementValid s (OrderedFocus.play A s) univ) :
    ∃ s, Function.Injective s ∧ Presents s univ ∧ ∀ f, AdmissibleWindowBound f →
      lowerWindowDensity f (range (OrderedFocus.play A s)) ≤ ENNReal.ofReal (1/2) := by
  have play : OrderedFocus.play A (stream A) = output A := by
    funext t; simp [OrderedFocus.play,output,history_eq]
  obtain ⟨T,good⟩ := valid _ (presents A)
  rw [play] at good
  refine ⟨stream A,stream_injective A,presents A,fun f hf => ?_⟩
  rw [play]
  exact upper_windows A (fun t ht => (good t ht).2.1) hf

end GenLimit.KleinbergWei.Banach
