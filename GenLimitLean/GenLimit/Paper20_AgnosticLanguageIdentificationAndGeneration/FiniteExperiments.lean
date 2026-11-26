import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.Model
import GenLimit.Support.DiscreteLawContinuity

/-! # Finite experiments along an increasing sequence of prefixes

A fixed sample experiment varies continuously when the observation stream
is given geometrically decreasing masses. A strict probability inequality
can therefore be preserved while adding new atoms later. -/
namespace GenLimit.AgnosticLanguage
open DiscreteIID Filter
open scoped Classical Topology
noncomputable section

def joint (G : StatisticalGenerator X) (p : PMF X) (n : ℕ) : PMF (List X × X) :=
  (samples p n).bind (fun xs ↦ (G xs).map (Prod.mk xs))

theorem experiment_freeze (G : StatisticalGenerator ℕ) (s : ℕ → ℕ) (n : ℕ)
    (E : Set (List ℕ × ℕ)) (b : ℝ) (h : b < probability (joint G (sequenceLaw s) n) E) :
    ∃ k : ℕ, ∀ t : ℕ → ℕ, (∀ j < k, t j = s j) → b < probability (joint G (sequenceLaw t) n) E := by
  have ho : IsOpen {t : ℕ → ℕ | b < probability (joint G (sequenceLaw t) n) E} := isOpen_lt continuous_const (continuous_sequence_experiment n
    (fun xs ↦ (G xs).map (Prod.mk xs)) E)
  obtain ⟨_,⟨v,k,rfl⟩,hv,hsub⟩ := (PiNat.isTopologicalBasis_cylinders (fun _ ↦ ℕ)).exists_subset_of_mem_open h ho
  exact ⟨k,fun t ht ↦ hsub (PiNat.mem_cylinder_iff.mpr fun j hj ↦ (ht j hj).trans (PiNat.mem_cylinder_iff.mp hv j hj))⟩

theorem joint_sample_event (G : StatisticalGenerator X) (p : PMF X) (n : ℕ) (E : Set (List X)) :
    probability (joint G p n) (Prod.fst ⁻¹' E) = probability (samples p n) E := by
  have he : (joint G p n).map Prod.fst = samples p n := by
    simp only [joint, PMF.map_bind,PMF.map_comp]
    have h (xs : List X) : (G xs).map (Prod.fst ∘ Prod.mk xs) = PMF.pure xs := by
      exact (G xs).map_const xs
    simp_rw [h]; exact PMF.bind_pure _
  change ((joint G p n).toOuterMeasure _).toReal = _
  rw [← PMF.toOuterMeasure_map_apply,he]; rfl

theorem pmf_tight (p : PMF α) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Finset α, 1-ε < probability p (T : Set α) := by
  have hlim : Filter.Tendsto (fun T : Finset α ↦ ∑ x ∈ T, (p x).toReal) atTop (𝓝 1) := by
    have h := (ENNReal.summable_toReal p.tsum_coe_ne_top).hasSum
    rwa [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe, ENNReal.toReal_one] at h
  obtain ⟨T,hT⟩ := (hlim.eventually_const_lt (by linarith : 1-ε < 1)).exists
  refine ⟨T,?_⟩
  simpa [probability, PMF.toOuterMeasure_apply_finset, ENNReal.toReal_sum (fun x _ ↦ p.apply_ne_top x)] using hT

theorem finite_coverage (p : PMF X) (S : Finset X) (hS : (S : Set X) ⊆ p.support)
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop,
      probability (samples p n) {xs | ¬∀ x ∈ S, x ∈ xs} < ε := by
  classical
  obtain ⟨b,hb,h⟩ := finite_missing_exponential p S (fun x hx ↦ hS hx)
  have ht : Tendsto (fun n : ℕ ↦ (S.card : ℝ) * Real.exp (-b*n)) atTop (𝓝 0) := by
    have hd := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hb)
    simpa [Function.comp_def,neg_mul] using hd.const_mul (S.card : ℝ)
  exact (ht.eventually_lt_const hε).mono fun n hn ↦ (h n).trans_lt hn

/-- A finite prefix represented by an infinite stream padded with zeros. -/
structure Stage where
  stream : ℕ → ℕ
  length : ℕ
  tail_zero : ∀ j ≥ length, stream j = 0

def Stage.initial : Stage := ⟨fun _ ↦ 0,1,fun _ _ ↦ rfl⟩

theorem Stage.finite_range (q : Stage) : (Set.range q.stream).Finite := by
  apply (insert 0 ((Finset.range q.length).image q.stream)).finite_toSet.subset
  rintro _ ⟨j,rfl⟩
  by_cases hj : j < q.length
  · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hj,rfl⟩)
  · simp [q.tail_zero j (Nat.le_of_not_gt hj)]

def Stage.append (q : Stage) (k value : ℕ) : Stage where
  stream := Function.update q.stream (max q.length k) value
  length := max q.length k + 1
  tail_zero j hj := by
    rw [Function.update_of_ne (by omega : j ≠ max q.length k)]
    exact q.tail_zero j (by omega)

theorem Stage.append_range (q : Stage) (k value : ℕ) :
    Set.range (q.append k value).stream = insert value (Set.range q.stream) := by
  ext y
  constructor
  · rintro ⟨j,rfl⟩
    by_cases h : j = max q.length k
    · simp [Stage.append,h]
    · exact Or.inr ⟨j,by simp [Stage.append,h]⟩
  · rintro (rfl | ⟨j,rfl⟩)
    · exact ⟨_,Function.update_self ..⟩
    · by_cases h : j = max q.length k
      · refine ⟨max q.length k+1,?_⟩
        exact ((q.append k value).tail_zero _ (Nat.le_refl _)).trans (q.tail_zero _ (by omega)).symm
      · exact ⟨j,by simp [Stage.append,h]⟩

theorem Stage.append_agrees (q : Stage) (k x j : ℕ) (hj : j < max q.length k) :
    (q.append k x).stream j = q.stream j := Function.update_of_ne (Nat.ne_of_lt hj) ..

/-- The diagonal limit of successive zero-padded prefixes. -/
def stageLimit (q : ℕ → Stage) (j : ℕ) := (q (j+1)).stream j

theorem stageLimit_agrees (q : ℕ → Stage) (growth : ∀ k, (q k).length < (q (k+1)).length)
    (agree : ∀ k j, j < (q k).length → (q (k+1)).stream j = (q k).stream j)
    (k j : ℕ) (hj : j < (q k).length) : stageLimit q j = (q k).stream j := by
  have monot := strictMono_nat_of_lt_succ growth
  have stable (a b : ℕ) (hab : a ≤ b) (ha : j < (q a).length) : (q b).stream j = (q a).stream j := by
    induction b, hab using Nat.le_induction with
    | base => rfl
    | succ b hb ih => exact (agree b j (ha.trans_le (monot.monotone hb))).trans ih
  change (q (j+1)).stream j = _
  rcases le_total k (j+1) with h | h
  · exact stable _ _ h hj
  · exact (stable _ _ h ((Nat.lt_succ_self j).trans_le (monot.id_le _))).symm

theorem stageLimit_range (q : ℕ → Stage) (growth : ∀ k, (q k).length < (q (k+1)).length)
    (agree : ∀ k j, j < (q k).length → (q (k+1)).stream j = (q k).stream j)
    (hzero : 0 ∈ Set.range (stageLimit q)) :
    Set.range (stageLimit q) = ⋃ k, Set.range (q k).stream := by
  ext x
  constructor
  · rintro ⟨j,rfl⟩
    exact Set.mem_iUnion.mpr ⟨j+1,j,rfl⟩
  · intro hx
    obtain ⟨k,j,rfl⟩ := Set.mem_iUnion.mp hx
    by_cases hj : j < (q k).length
    · exact ⟨j,stageLimit_agrees q growth agree _ _ hj⟩
    · simpa [Stage.tail_zero _ j (Nat.le_of_not_gt hj)] using hzero

end
end GenLimit.AgnosticLanguage
