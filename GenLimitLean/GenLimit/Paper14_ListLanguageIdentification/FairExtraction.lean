import GenLimit.Paper14_ListLanguageIdentification.DrawSimulation

/-! # Extracting a fair bit from independent draws

A column supplies independent ordered pairs. At the first unequal pair,
the order of its entries gives an unbiased bit, for every nonsingleton
discrete distribution. -/
namespace GenLimit.ListIdentification.InfiniteDraws
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

def two {α : Type*} (x : ℕ → α) := (x 0,x 1)

theorem two_law {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    MeasurePreserving (two (α := α)) (iid μ) (μ.prod μ) := by
  have ev (i : ℕ) : MeasurePreserving (fun x : ℕ → α ↦ x i) (iid μ) μ :=
    measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) i
  have ind : iIndepFun (fun (i : ℕ) (x : ℕ → α) ↦ x i) (iid μ) :=
    iIndepFun_infinitePi (μ := fun _ : ℕ ↦ μ) (X := fun _ ↦ id) (fun _ ↦ measurable_id)
  refine ⟨(ev 0).measurable.prodMk (ev 1).measurable,?_⟩
  have q := (indepFun_iff_map_prod_eq_prod_map_map (ev 0).measurable.aemeasurable
    (ev 1).measurable.aemeasurable).mp (ind.indepFun (by decide : (0 : ℕ) ≠ 1))
  simpa only [(ev 0).map_eq,(ev 1).map_eq] using q

def pairs {α : Type*} (s : ℕ → α) (j : ℕ) : α × α := two (rows s j)

theorem pairs_law {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    MeasurePreserving (pairs (α := α)) (iid μ) (iid (μ.prod μ)) :=
  (iid_map (two_law μ)).comp (rows_iid μ)

def different {α : Type*} (w : ℕ → α × α) (j : ℕ) : Prop := (w j).1 ≠ (w j).2

noncomputable def orientation (code : α → ℕ) (w : ℕ → α × α) : Bool :=
  let z := w (first (different w))
  decide (code z.1 < code z.2)

theorem measurable_orientation [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (code : α → ℕ) : Measurable (orientation code) := by
  have h (j : ℕ) : MeasurableSet {w : ℕ → α × α | different w j} :=
    (measurable_pi_apply j : Measurable (fun w : ℕ → α × α ↦ w j))
      (Set.to_countable {v : α × α | v.1 ≠ v.2}).measurableSet
  have hm := measurable_first h
  have hev : Measurable (fun v : (ℕ → α × α) × ℕ ↦ v.1 v.2) :=
    measurable_from_prod_countable_left (fun j ↦ measurable_pi_apply j)
  have hp : Measurable (fun w : ℕ → α × α ↦ w (first (different w))) :=
    hev.comp (measurable_id.prodMk hm)
  exact (measurable_of_countable (fun v : α × α ↦ decide (code v.1 < code v.2))).comp hp

theorem ae_different [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] {a b : α} (hab : a ≠ b)
    (ha : 0 < μ {a}) (hb : 0 < μ {b}) :
    ∀ᵐ w ∂iid (μ.prod μ), ∃ j, different w j := by
  let H : Set (α × α) := {z | z.1 ≠ z.2}
  have pos : 0 < (μ.prod μ) (({a} : Set α) ×ˢ {b}) := by
    rw [Measure.prod_prod]; exact ENNReal.mul_pos ha.ne' hb.ne'
  exact ae_some (μ.prod μ) (H := H) (Set.to_countable _).measurableSet
    (pos.trans_le (measure_mono (by rintro _ ⟨rfl,rfl⟩; exact hab)))

private theorem swap_orientation (code : α → ℕ) (hc : Function.Injective code)
    (w : ℕ → α × α) (hw : ∃ j, different w j) :
    orientation code (fun i ↦ (w i).swap) = !(orientation code w) := by
  have h : different (fun i ↦ (w i).swap) = different w := by
    funext i
    exact propext ne_comm
  simp only [orientation,h,Prod.fst_swap,Prod.snd_swap]
  have hn : code (w (first (different w))).1 ≠ code (w (first (different w))).2 :=
    fun e ↦ first_spec hw (hc e)
  rcases lt_or_gt_of_ne hn with hlt | hgt <;> simp_all [not_lt_of_gt]

private theorem fair_of_flip (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hinv : MeasurePreserving Bool.not ν ν) : ν = coin := by
  have flip := hinv.measureReal_preimage (s := {true}) (measurableSet_singleton _).nullMeasurableSet
  have hset : Bool.not ⁻¹' {true} = {false} := by ext b; cases b <;> simp
  rw [hset] at flip
  have hs := sum_measureReal_singleton (μ := ν) (Finset.univ : Finset Bool)
  rw [Finset.coe_univ,measureReal_univ_eq_one,Fintype.sum_bool] at hs
  apply ext_iff_measureReal_singleton.mpr
  intro b
  have hcoin : coin.real {b} = (1 : ℝ)/2 := by
    rw [measureReal_def,PMF.toMeasure_apply_singleton _ b (measurableSet_singleton _),
      PMF.uniformOfFintype_apply]
    norm_num
  rw [hcoin]
  cases b <;> linarith

theorem orientation_law [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (code : α → ℕ) (hc : Function.Injective code) (μ : Measure α) [IsProbabilityMeasure μ]
    {a b : α} (hab : a ≠ b) (ha : 0 < μ {a}) (hb : 0 < μ {b}) :
    MeasurePreserving (orientation code) (iid (μ.prod μ)) coin := by
  let pairLaw := iid (μ.prod μ)
  let ν := pairLaw.map (orientation code)
  have hm := measurable_orientation code
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hm.aemeasurable
  have swapLaw : MeasurePreserving (fun (w : ℕ → α × α) i ↦ (w i).swap) pairLaw pairLaw :=
    iid_map (Measure.measurePreserving_swap (μ := μ) (ν := μ))
  refine ⟨hm,fair_of_flip ν ⟨measurable_of_countable _,?_⟩⟩
  change (pairLaw.map (orientation code)).map Bool.not = pairLaw.map (orientation code)
  have hn : Measurable Bool.not := measurable_of_countable _
  rw [Measure.map_map hn hm]
  calc
    _ = pairLaw.map (orientation code ∘ (fun w i ↦ (w i).swap)) := by
      apply Measure.map_congr
      filter_upwards [ae_different μ hab ha hb] with w hw
      exact (swap_orientation code hc w hw).symm
    _ = _ := by rw [← Measure.map_map hm swapLaw.measurable,swapLaw.map_eq]

end GenLimit.ListIdentification.InfiniteDraws
