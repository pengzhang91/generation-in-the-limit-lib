import GenLimit.Paper14_ListLanguageIdentification.IndependentText

/-! # Theorem 10: probabilistic list identification and infinite draws -/
namespace GenLimit.ListIdentification.InfiniteDraws
open MeasureTheory Set
open scoped ENNReal
open PrefixSimulation

private def jointSuccess (F : Generic.LanguageFamily α) (A : Probabilistic.Identifier α k)
    (z : ℕ) : Set ((ℕ → α) × Probabilistic.Tape) :=
  {v | v.2 ∈ Probabilistic.stableEvent F A v.1 z}

private theorem measurable_joint [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (F : Generic.LanguageFamily α) (A : Probabilistic.Identifier α k) (z : ℕ) :
    MeasurableSet (jointSuccess F A z) := by
  let H (n : ℕ) := {h : Fin n → α × Bool | TargetInGuess F z
    (A n (fun i ↦ (h i).1) (fun i ↦ (h i).2))}
  let history (n : ℕ) (v : (ℕ → α) × Probabilistic.Tape) (i : Fin n) := (v.1 i,v.2 i)
  have hm (n : ℕ) : Measurable (history n) := measurable_pi_lambda _ fun i ↦
    ((measurable_pi_apply _).comp measurable_fst).prodMk ((measurable_pi_apply _).comp measurable_snd)
  have he : jointSuccess F A z = ⋃ T : ℕ, ⋂ n : ℕ, ⋂ (_ : T ≤ n), history n ⁻¹' H n := by
    ext v
    simp only [jointSuccess,Probabilistic.stableEvent,mem_setOf_eq,mem_iUnion,mem_iInter,mem_preimage]
    rfl
  rw [he]
  exact .iUnion fun T ↦ .iInter fun n ↦ .iInter fun _ ↦ hm n (Set.to_countable _).measurableSet

private theorem joint_bound [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {F : Generic.LanguageFamily α} {A : Probabilistic.Identifier α k} {p : ℝ}
    (hA : ∀ z s, Generic.Presents s (F z) → p ≤ Probabilistic.fair.real (Probabilistic.stableEvent F A s z))
    (z : ℕ) (q : PMF α) (hq : q.support = F z) :
    p ≤ ((iid q.toMeasure).prod Probabilistic.fair).real (jointSuccess F A z) := by
  have hb : ENNReal.ofReal p ≤ ((iid q.toMeasure).prod Probabilistic.fair) (jointSuccess F A z) := by
    rw [Measure.prod_apply (measurable_joint ..)]
    calc
      _ = ∫⁻ _ : ℕ → α, ENNReal.ofReal p ∂iid q.toMeasure := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [ae_presents q] with s hs
        have h := ENNReal.ofReal_le_ofReal (hA z s (hq ▸ hs))
        rwa [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hb

private noncomputable def singleIndex (F : Generic.LanguageFamily α) (a : α) : ℕ := by
  classical
  exact if h : ∃ j, F j = {a} then Nat.find h else 0

private def paired (A : Probabilistic.Identifier α k) : ListIdentifier (α × Bool) k :=
  fun n h ↦ A n (fun i ↦ (h i).1) (fun i ↦ (h i).2)

private noncomputable def learner (code : α → ℕ) (F : Generic.LanguageFamily α)
    (A : Probabilistic.Identifier α k) : ListIdentifier α k := by
  classical
  exact fun n xs ↦
    if hn : 0 < n then
      if ∀ i, xs i = xs ⟨0,hn⟩ then fun _ ↦ singleIndex F (xs ⟨0,hn⟩)
      else simulate (observations code) (paired A) n xs
    else fun _ ↦ 0

private theorem singleton_success {F : Generic.LanguageFamily α} {k : ℕ} {A : Probabilistic.Identifier α k}
    {z : ℕ} {a : α} {s : ℕ → α} (code : α → ℕ) (hz : F z = {a}) (hs : Generic.Presents s (F z))
    (j : Fin k) : s ∈ success F (learner code F A) z := by
  classical
  have hall (i : ℕ) : s i = a := by
    have h : s i ∈ F z := hs ▸ mem_range_self i
    simpa [hz] using h
  refine ⟨1,fun n hn ↦ ⟨j,?_⟩⟩
  have he : ∃ l, F l = {a} := ⟨z,hz⟩
  simp [listOutput,learner,show 0 < n by omega,hall,singleIndex,he,Nat.find_spec he,hz]

private theorem transfer {F : Generic.LanguageFamily α} {A : Probabilistic.Identifier α k}
    {s : ℕ → α} {z : ℕ} (code : α → ℕ) (hs : LocalAt (observations code) s)
    (hab : ∃ u v, s u ≠ s v) (h : split code s ∈ jointSuccess F A z) :
    s ∈ success F (learner code F A) z := by
  classical
  obtain ⟨T,hT⟩ := Set.mem_iUnion.mp h
  have hd : ∃ T, ∀ n ≥ T, TargetInGuess F z (paired A n (fun j ↦ observations code s j)) :=
    ⟨T,fun n hn ↦ hT n hn⟩
  obtain ⟨N,hN⟩ := eventual_simulation hs hd
  obtain ⟨u,v,huv⟩ := hab
  refine ⟨max N (max u v + 1),fun n hn ↦ ?_⟩
  have hm : max u v < n := (le_max_right ..).trans hn
  have hu : u < n := (le_max_left ..).trans_lt hm
  have hv : v < n := (le_max_right ..).trans_lt hm
  have hpos : 0 < n := by omega
  have hvar : ¬∀ i : Fin n, s i = s 0 := fun he ↦ huv ((he ⟨u,hu⟩).trans (he ⟨v,hv⟩).symm)
  simpa [listOutput,learner,hpos,hvar] using hN n ((le_max_left ..).trans hn)

theorem draws_of_probabilistic [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {F : Generic.LanguageFamily α} {k : ℕ} {p : ℝ} (hp : p ≤ 1) (h : Probabilistic.Identifies F k p) :
    Identifies F k p := by
  classical
  obtain ⟨A,hA⟩ := h
  letI := Encodable.ofCountable α
  let code := @Encodable.encode α _
  let D := learner code F A
  refine ⟨D,fun z q hq ↦ ?_⟩
  rcases le_or_gt p 0 with hn | hpos
  · exact hn.trans measureReal_nonneg
  rcases q.support.subsingleton_or_nontrivial with hsingle | htwo
  · obtain ⟨a,ha⟩ := q.support_nonempty
    have hz : F z = {a} := hq.symm.trans (hsingle.eq_singleton_of_mem ha)
    have hall := ae_presents q
    obtain ⟨s,hs⟩ := hall.exists
    have mass := hpos.trans_le (hA z s (hq ▸ hs))
    have he : (Probabilistic.stableEvent F A s z).Nonempty := by
      by_contra! hn
      simp [hn] at mass
    obtain ⟨r,hr⟩ := he
    obtain ⟨T,hT⟩ := mem_iUnion.mp hr
    obtain ⟨j,_⟩ := hT T le_rfl
    have hae : ∀ᵐ t ∂iid q.toMeasure, t ∈ success F D z :=
      hall.mono (fun t ht ↦ singleton_success code hz (hq ▸ ht) j)
    have hone := (mem_ae_iff_prob_eq_one (μ := iid q.toMeasure) (measurable_success F D z)).mp hae
    simpa [measureReal_def,hone] using hp
  · obtain ⟨a,ha,b,hb,hab⟩ := htwo
    have pos (x : α) (hx : x ∈ q.support) : 0 < q.toMeasure {x} := by
      rw [q.toMeasure_apply_singleton _ (measurableSet_singleton _)]
      exact pos_iff_ne_zero.mpr hx
    have law := split_law code Encodable.encode_injective q.toMeasure hab (pos _ ha) (pos _ hb)
    apply (joint_bound hA z q hq).trans
    rw [← law.measureReal_preimage (measurable_joint ..).nullMeasurableSet]
    apply ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae _)
    filter_upwards [ae_local code q.toMeasure hab (pos _ ha) (pos _ hb), ae_presents q] with s hs he
    intro hgood
    obtain ⟨u,hu⟩ := (show a ∈ Set.range s from he.symm ▸ ha)
    obtain ⟨v,hv⟩ := (show b ∈ Set.range s from he.symm ▸ hb)
    exact transfer code hs ⟨u,v,fun eq ↦ hab (hu.symm.trans (eq.trans hv))⟩ hgood

/-- Theorem 10, including zero-width lists and singleton languages. -/
theorem theorem_10 [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (F : Generic.LanguageFamily α) (k : ℕ) (p : ℝ) (hp : p ≤ 1) :
    Identifies F k p ↔ Probabilistic.Identifies F k p :=
  ⟨probabilistic_of_draws,draws_of_probabilistic hp⟩

end GenLimit.ListIdentification.InfiniteDraws
