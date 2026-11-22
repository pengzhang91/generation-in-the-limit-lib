import GenLimit.Paper14_ListLanguageIdentification.Algorithm
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.Real

/-! # Theorem 9: probabilistic and deterministic list identification

A randomized identifier sees one fair bit per example. Its success
probability measures permanent eventual membership along the entire random
tape. Above the sharp threshold, its one-stage acceptance probabilities
determine a bounded set of distinct language guesses. -/
namespace GenLimit.ListIdentification.Probabilistic
open MeasureTheory Filter Set
open scoped Topology

abbrev Tape := ℕ → Bool
abbrev Identifier (α : Type*) (k : ℕ) := (n : ℕ) → (Fin n → α) → (Fin n → Bool) → Fin k → ℕ

noncomputable def fair : Measure Tape := Measure.infinitePi (fun _ : ℕ ↦ (PMF.uniformOfFintype Bool).toMeasure)

instance : IsProbabilityMeasure fair := by unfold fair; infer_instance

def hit (F : Generic.LanguageFamily α) (A : Identifier α k) (n : ℕ) (xs : Fin n → α)
    (K : Set α) : Set Tape := {r | ∃ j, F (A n xs (fun i ↦ r i) j) = K}

theorem measurable_hit (F : Generic.LanguageFamily α) (A : Identifier α k) (n : ℕ)
    (xs : Fin n → α) (K : Set α) : MeasurableSet (hit F A n xs K) := by
  let E : Set (Fin n → Bool) := {b | ∃ j, F (A n xs b j) = K}
  have hp : Measurable (fun r : Tape ↦ fun i : Fin n ↦ r i) :=
    measurable_pi_lambda _ (fun i ↦ measurable_pi_apply _)
  exact hp (Set.to_countable E).measurableSet

def stableEvent (F : Generic.LanguageFamily α) (A : Identifier α k) (s : ℕ → α) (z : ℕ) :
    Set Tape := ⋃ N : ℕ, {r | ∀ n ≥ N, r ∈ hit F A n (fun i ↦ s i) (F z)}

def Identifies (F : Generic.LanguageFamily α) (k : ℕ) (p : ℝ) :=
  ∃ A : Identifier α k, ∀ z s, Generic.Presents s (F z) → p ≤ fair.real (stableEvent F A s z)

private theorem eventual_hit (F : Generic.LanguageFamily α) (A : Identifier α k)
    (s : ℕ → α) (z : ℕ) {a : ℝ} (ha : a < fair.real (stableEvent F A s z)) :
    ∃ N, ∀ n ≥ N, a < fair.real (hit F A n (fun i ↦ s i) (F z)) := by
  let E (N : ℕ) : Set Tape := {r | ∀ n ≥ N, r ∈ hit F A n (fun i ↦ s i) (F z)}
  have hm : Monotone E := fun _ _ h _ hr n hn ↦ hr n (h.trans hn)
  have ht : Tendsto (fun n ↦ fair.real (E n)) atTop (𝓝 (fair.real (⋃ n, E n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_measure_iUnion_atTop hm)
  obtain ⟨N,hN⟩ := eventually_atTop.1 (ht.eventually (Ioi_mem_nhds ha))
  exact ⟨N,fun n hn ↦ (hN n hn).trans_le (measureReal_mono (fun _ hr ↦ hr n le_rfl))⟩

private noncomputable def candidates (F : Generic.LanguageFamily α) (A : Identifier α k)
    (n : ℕ) (xs : Fin n → α) : Finset (Set α) := by
  classical
  exact Finset.univ.biUnion (fun b : Fin n → Bool ↦ Finset.univ.image (F ∘ A n xs b))

private noncomputable def heavy (F : Generic.LanguageFamily α) (A : Identifier α k)
    (n : ℕ) (xs : Fin n → α) : Finset (Set α) := by
  classical
  exact (candidates F A n xs).filter (fun K ↦ (k : ℝ) / (k+1) < fair.real (hit F A n xs K))

private theorem heavy_card (F : Generic.LanguageFamily α) (A : Identifier α k) (n : ℕ)
    (xs : Fin n → α) : (heavy F A n xs).card ≤ k := by
  classical
  by_contra! hlt
  obtain ⟨S,hsub,hcard⟩ := Finset.exists_subset_card_eq (show k+1 ≤ _ from hlt)
  have cover : (⋃ K ∈ S, (hit F A n xs K)ᶜ) = univ := by
    apply eq_univ_of_forall
    intro r
    by_contra! hn
    have all : S ⊆ Finset.univ.image (F ∘ A n xs (fun i ↦ r i)) := by
      intro K hK
      have h : r ∈ hit F A n xs K := by
        by_contra h
        exact hn (mem_iUnion.mpr ⟨K,mem_iUnion.mpr ⟨hK,h⟩⟩)
      obtain ⟨j,hj⟩ := h
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩
    have := (Finset.card_le_card all).trans Finset.card_image_le
    simpa [hcard] using this
  have bound := measureReal_biUnion_finset_le (μ := fair) S (fun K ↦ (hit F A n xs K)ᶜ)
  rw [cover,measureReal_univ_eq_one] at bound
  have strict : ∑ K ∈ S, fair.real (hit F A n xs K)ᶜ < ∑ _K ∈ S, (1 : ℝ)/(k+1) := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (by omega))
    intro K hK
    have h := (Finset.mem_filter.mp (hsub hK)).2
    rw [measureReal_compl (measurable_hit ..),measureReal_univ_eq_one]
    have eq : (k : ℝ)/(k+1) + 1/(k+1) = 1 := by field_simp
    linarith
  have eq : (∑ _K ∈ S, (1 : ℝ)/(k+1)) = 1 := by
    simp [hcard,nsmul_eq_mul,add_ne_zero.mpr]; field_simp
  linarith

private noncomputable def indexOf (F : Generic.LanguageFamily α) (K : Set α) : ℕ := by
  classical
  exact if h : ∃ i, F i = K then Nat.find h else 0

private noncomputable def derandomize (F : Generic.LanguageFamily α) (A : Identifier α k) :
    ListIdentifier α k := fun n xs ↦ padIndexList ((heavy F A n xs).toList.map (indexOf F)) k

theorem theorem_9 (F : Generic.LanguageFamily α) (k : ℕ) (p : ℝ) (hp : p ≤ 1) :
    (ListIdentifiable F k → Identifies F k p) ∧
      ((k : ℝ)/(k+1) < p → Identifies F k p → ListIdentifiable F k) := by
  classical
  constructor
  · rintro ⟨D,hD⟩
    refine ⟨fun n xs _ ↦ D n xs,fun z s hs ↦ ?_⟩
    obtain ⟨N,hN⟩ := hD z s hs
    have he : stableEvent F (fun n xs _ ↦ D n xs) s z = univ :=
      eq_univ_of_forall (fun _ ↦ mem_iUnion.mpr ⟨N,fun n hn ↦ hN n hn⟩)
    simpa [he] using hp
  · rintro hth ⟨A,hA⟩
    refine ⟨derandomize F A,fun z s hs ↦ ?_⟩
    obtain ⟨N,hN⟩ := eventual_hit F A s z (hth.trans_le (hA z s hs))
    refine ⟨N,fun n hn ↦ ?_⟩
    let xs : Fin n → α := fun i ↦ s i
    have hpos : 0 < fair.real (hit F A n xs (F z)) := (by positivity : 0 ≤ (k : ℝ)/(k+1)).trans_lt (hN n hn)
    have hex : (hit F A n xs (F z)).Nonempty := by
      by_contra! h
      simp [h] at hpos
    obtain ⟨r,j,hj⟩ := hex
    have hK : F z ∈ heavy F A n xs := Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨(fun i ↦ r i),Finset.mem_univ _,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩⟩,hN n hn⟩
    obtain ⟨slot,hslot⟩ := mem_padIndexList (List.mem_map.mpr ⟨_,Finset.mem_toList.mpr hK,rfl⟩ :
      indexOf F (F z) ∈ (heavy F A n xs).toList.map (indexOf F)) (by simpa using heavy_card F A n xs)
    have he : ∃ j, F j = F z := ⟨z,rfl⟩
    refine ⟨slot,?_⟩
    change F (padIndexList _ k slot) = F z
    rw [hslot]
    simp [indexOf,he,Nat.find_spec he]

end GenLimit.ListIdentification.Probabilistic
