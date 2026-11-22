import GenLimit.Paper14_ListLanguageIdentification.FirstSuccess
import GenLimit.Paper14_ListLanguageIdentification.PrefixSimulation

namespace GenLimit.ListIdentification.InfiniteDraws
open MeasureTheory Filter Set
open scoped Topology ENNReal
open PrefixSimulation

def success (F : Generic.LanguageFamily α) (D : ListIdentifier α k) (z : ℕ) : Set (ℕ → α) :=
  {s | IdentifiesFrom D F z s}

theorem measurable_success [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (F : Generic.LanguageFamily α) (D : ListIdentifier α k) (z : ℕ) :
    MeasurableSet (success F D z) := by
  let H (n : ℕ) := {xs : Fin n → α | TargetInGuess F z (D n xs)}
  have hm (n : ℕ) : Measurable (fun s : ℕ → α ↦ fun i : Fin n ↦ s i) :=
    measurable_pi_lambda _ (fun _ ↦ measurable_pi_apply _)
  have hs : success F D z = ⋃ N : ℕ, ⋂ n : ℕ, ⋂ (_ : N ≤ n),
      (fun s : ℕ → α ↦ fun i : Fin n ↦ s i) ⁻¹' H n := by
    ext s
    simp only [Set.mem_iUnion,Set.mem_iInter,Set.mem_preimage]
    rfl
  rw [hs]
  exact .iUnion fun N ↦ .iInter fun n ↦ .iInter fun _ ↦ hm n (Set.to_countable _).measurableSet

/-- Definition 10 with one deterministic finite-history identifier, evaluated
on the entire draw from each law having exactly the target as support. -/
def Identifies [MeasurableSpace α] (F : Generic.LanguageFamily α) (k : ℕ) (p : ℝ) :=
  ∃ D : ListIdentifier α k, ∀ z (q : PMF α), q.support = F z →
    p ≤ (iid q.toMeasure).real (success F D z)

theorem iid_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → β} (hf : MeasurePreserving f μ ν) :
    MeasurePreserving (fun (s : ℕ → α) j ↦ f (s j)) (iid μ) (iid ν) := by
  refine ⟨measurable_pi_lambda _ (fun j ↦ hf.measurable.comp (measurable_pi_apply j)), ?_⟩
  unfold iid
  rw [Measure.infinitePi_map_pi _ (fun _ ↦ hf.measurable)]
  simp only [hf.map_eq]

theorem first_congr {Q R : ℕ → Prop} (hq : ∃ j, Q j)
    (he : ∀ i ≤ first Q, Q i ↔ R i) : first R = first Q :=
  first_eq ((he _ le_rfl).mp (first_spec hq))
    (fun i hi hr ↦ hi.not_ge (first_le ((he i hi.le).mpr hr)))

noncomputable def draw (x : ℕ → α × Bool) (j : ℕ) : α :=
  (x (bitIndex (rows (fun i ↦ (x i).2) j))).1

private theorem draw_local (s : ℕ → α) (r : ℕ → Bool)
    (hr : ∀ j, ∃ l, rows r j l = true) : LocalAt draw (fun i ↦ (s i,r i)) := by
  intro j
  let m := bitIndex (rows r j)
  refine ⟨Nat.pair j m + 1,fun t ht ↦ ?_⟩
  have hi : bitIndex (rows (fun i ↦ (t i).2) j) = m := by
    apply first_congr (hr j)
    intro i hi
    change r (Nat.pair j i) = true ↔ (t (Nat.pair j i)).2 = true
    rw [ht _ (Nat.lt_succ_of_le ((strictMono_nat_of_lt_succ
      (fun i ↦ Nat.pair_lt_pair_right j (Nat.lt_succ_self i))).monotone hi))]
  change (t (bitIndex _)).1 = s m
  rw [hi,ht _ (Nat.lt_succ_of_le (Nat.right_le_pair ..))]

theorem ae_rows_true : ∀ᵐ r ∂Probabilistic.fair, ∀ j, ∃ l, rows r j l = true := by
  apply ae_all_iff.mpr
  intro j
  have h := (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ iid coin) j).comp (rows_iid coin)
  exact h.quasiMeasurePreserving.ae (p := fun b : ℕ → Bool ↦ ∃ l : ℕ, b l = true) ae_true

/-- An infinite-draw learner can be run on a fixed text and a fair tape.
Each simulated word is drawn from the same full-support law. -/
theorem probabilistic_of_draws [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {F : Generic.LanguageFamily α} {k : ℕ} {p : ℝ} (h : Identifies F k p) :
    Probabilistic.Identifies F k p := by
  classical
  obtain ⟨D,hD⟩ := h
  let A : Probabilistic.Identifier α k := fun n xs bits ↦
    simulate draw D n (fun i ↦ (xs i,bits i))
  refine ⟨A,fun z s hs ↦ ?_⟩
  let f (b : ℕ → Bool) := s (bitIndex b)
  have hf : Measurable f := (measurable_of_countable s).comp measurable_bitIndex
  let μ := (iid coin).map f
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hf.aemeasurable
  let q := μ.toPMF
  have hq : q.toMeasure = μ := Measure.toPMF_toMeasure _
  have supp : q.support = F z := by
    rw [← hs]
    ext a
    change μ {a} ≠ 0 ↔ ∃ j, s j = a
    rw [show μ {a} = iid coin (f ⁻¹' {a}) from Measure.map_apply hf (measurableSet_singleton _)]
    constructor
    · intro ha
      by_contra hn
      have he : f ⁻¹' {a} = ∅ := eq_empty_iff_forall_notMem.mpr
        (fun b hb ↦ hn ⟨bitIndex b,hb⟩)
      simp [he] at ha
    · rintro ⟨j,rfl⟩
      exact ((index_pos j).trans_le (measure_mono (show {b | bitIndex b = j} ⊆ f ⁻¹' {s j} from
        fun b hb ↦ congrArg s hb))).ne'
  let transform (r : ℕ → Bool) := fun j ↦ f (rows r j)
  have hf' : MeasurePreserving f (iid coin) q.toMeasure := ⟨hf,hq.symm⟩
  have law : MeasurePreserving transform Probabilistic.fair (iid q.toMeasure) :=
    (iid_map hf').comp (rows_iid coin)
  apply (hD z q supp).trans
  rw [← law.measureReal_preimage (measurable_success F D z).nullMeasurableSet]
  apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae _)
  filter_upwards [ae_rows_true] with r hr
  intro hd
  exact mem_iUnion.mpr (eventual_simulation (draw_local s r hr) hd)

end GenLimit.ListIdentification.InfiniteDraws
