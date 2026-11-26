import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.Model
import GenLimit.Core.CanonicalDensity
import GenLimit.Support.FiniteCandidateRace

/-! # Bounded witness index and Algorithm 3 -/
namespace GenLimit.AgnosticLanguage
open Generic DiscreteIID Filter
open scoped Classical
noncomputable section

/-- The order on each language is inherited from the same enumeration of the universe. -/
def orderedWord (u : ℕ ≃ α) (L : Set α) (k : ℕ) : α :=
  u (Nat.nth (fun t ↦ u t ∈ L) k)

private theorem preimage_infinite (u : ℕ ≃ α) {L : Set α} (h : L.Infinite) :
    (u ⁻¹' L).Infinite := h.preimage (by rw [u.surjective.range_eq]; exact Set.subset_univ _)

theorem range_orderedWord (u : ℕ ≃ α) {L : Set α} (h : L.Infinite) :
    Set.range (orderedWord u L) = L := by
  have hr := Nat.range_nth_of_infinite (preimage_infinite u h)
  change Set.range (u ∘ Nat.nth (fun t ↦ u t ∈ L)) = L
  rw [Set.range_comp, hr]
  exact Set.image_preimage_eq _ u.surjective

/-- Finiteness of the witness index in equation (9), using zero-based positions. -/
def FiniteWitnessIndex (u : ℕ ≃ α) (C : Generic.LanguageFamily α) (p : PMF α) : Prop :=
  ∃ M : ℕ, ∀ i, (∀ r < M, orderedWord u (C i) r ∈ p.support) → C i ⊆ p.support

private theorem exists_unseen (u : ℕ ≃ α) (L : Set α) (hL : L.Infinite) (xs : List α) :
    ∃ r, orderedWord u L r ∉ xs := by
  by_contra! h
  apply hL
  apply xs.finite_toSet.subset
  rw [← range_orderedWord u hL]
  rintro _ ⟨r,rfl⟩
  exact h r

private def counter (u : ℕ ≃ α) (L : Set α) (hL : L.Infinite) (xs : List α) : ℕ :=
  Nat.find (exists_unseen u L hL xs)

/-- Select a language among the first sample-length many with the longest
observed initial segment, then output its first unobserved word. -/
def algorithmThree (u : ℕ ≃ α) (C : Generic.LanguageFamily α) (hC : ∀ i, (C i).Infinite)
    (xs : List α) : α :=
  let score := fun i ↦ counter u (C i) (hC i) xs
  let winner := (Support.winningIndexBy (Finset.range xs.length) score).getD 0
  orderedWord u (C winner) (score winner)

private theorem algorithmThree_correct (u : ℕ ≃ α) (C : Generic.LanguageFamily α)
    (hC : ∀ i, (C i).Infinite) (p : PMF α) (M z : ℕ)
    (hM : ∀ i, (∀ r < M, orderedWord u (C i) r ∈ p.support) → C i ⊆ p.support)
    (xs : List α) (hz : z < xs.length) (hs : ∀ x ∈ xs, x ∈ p.support)
    (hseen : ∀ r < M, orderedWord u (C z) r ∈ xs) :
    algorithmThree u C hC xs ∈ p.support ∧ algorithmThree u C hC xs ∉ xs := by
  let score := fun i ↦ counter u (C i) (hC i) xs
  obtain ⟨w,hw,_,hmax⟩ := Support.winningIndexBy_spec (Finset.range xs.length) score
    ⟨z,Finset.mem_range.mpr hz⟩
  have hzw := hmax z (Finset.mem_range.mpr hz)
  have hm : M ≤ score z := by
    by_contra! h
    exact Nat.find_spec (exists_unseen u (C z) (hC z) xs) (hseen (score z) h)
  have hall : C w ⊆ p.support := hM w (fun r hr ↦ hs _ (by
    by_contra hn
    have hle : score w ≤ r := Nat.find_min' (exists_unseen u (C w) (hC w) xs) hn
    omega))
  have he : algorithmThree u C hC xs = orderedWord u (C w) (score w) := by
    change orderedWord u (C ((Support.winningIndexBy _ score).getD 0)) (score _) = _
    rw [hw]; rfl
  rw [he]
  exact ⟨hall (Set.mem_of_mem_of_subset (Set.mem_range_self (f := orderedWord u (C w)) (score w)) (range_orderedWord u (hC w)).le), Nat.find_spec (exists_unseen u (C w) (hC w) xs)⟩

/-- Theorem 3.2. The positive constants may depend on the distribution and family. -/
theorem generation_exponential (u : ℕ ≃ α) (C : Generic.LanguageFamily α)
    (hC : ∀ i, (C i).Infinite) (p : PMF α) (hidx : FiniteWitnessIndex u C p)
    (hsub : ∃ z, C z ⊆ p.support) :
    ∃ c > (0:ℝ), ∃ d > (0:ℝ), ∀ n : ℕ,
      genErr (deterministic (algorithmThree u C hC)) p n ≤ c * Real.exp (-d * n) := by
  obtain ⟨M,hM⟩ := hidx
  obtain ⟨z,hz⟩ := hsub
  let T := (Finset.range M).image (orderedWord u (C z))
  obtain ⟨d,hd,ht⟩ := finite_missing_exponential p T (by
    rintro x hx
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hx
    exact hz ((range_orderedWord u (hC z)).le (Set.mem_range_self r)))
  let c := max (T.card : ℝ) (Real.exp (d * z))
  refine ⟨c,(Real.exp_pos _).trans_le (le_max_right ..),d,hd,fun n ↦ ?_⟩
  rw [genErr_deterministic]
  by_cases hn : z < n
  · rw [← probability_inter_support]
    apply le_trans (probability_mono _ ?_) ((ht n).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (Real.exp_nonneg _)))
    rintro xs ⟨hbad,hxs⟩ hcov
    obtain ⟨hlen,hs⟩ := (samples_support p n xs).mp hxs
    have hh := algorithmThree_correct u C hC p M z hM xs (hlen ▸ hn) hs
      (fun r hr ↦ hcov _ (Finset.mem_image.mpr ⟨r,Finset.mem_range.mpr hr,rfl⟩))
    exact hbad.elim (fun h ↦ h hh.1) hh.2
  · apply (probability_le_one ..).trans
    apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right ..) (Real.exp_nonneg _))
    rw [← Real.exp_add, Real.one_le_exp_iff]
    nlinarith [mul_nonneg hd.le (sub_nonneg.mpr (show (n:ℝ) ≤ z by exact_mod_cast Nat.le_of_not_gt hn))]

theorem finite_witness_index_of_finite (u : ℕ ≃ α) (C : Generic.LanguageFamily α)
    (hC : ∀ i, (C i).Infinite) (hf : (Set.range C).Finite) (p : PMF α) :
    FiniteWitnessIndex u C p := by
  classical
  have each (L : Set α) (hL : L ∈ hf.toFinset) :
      ∃ M : ℕ, (∀ r < M, orderedWord u L r ∈ p.support) → L ⊆ p.support := by
    by_cases hs : L ⊆ p.support
    · exact ⟨0,fun _ ↦ hs⟩
    obtain ⟨x,hx,hout⟩ := Set.not_subset.mp hs
    obtain ⟨i,rfl⟩ := hf.mem_toFinset.mp hL
    obtain ⟨r,rfl⟩ := (show x ∈ Set.range (orderedWord u (C i)) from (range_orderedWord u (hC i)).ge hx)
    exact ⟨r+1,fun h ↦ False.elim (hout (h r (Nat.lt_succ_self _)))⟩
  choose m hm using each
  refine ⟨hf.toFinset.sup' ⟨C 0,hf.mem_toFinset.mpr ⟨0,rfl⟩⟩ (fun L ↦ if h : L ∈ hf.toFinset then m L h else 0), ?_⟩
  intro i hi
  have hmem := hf.mem_toFinset.mpr (Set.mem_range_self i)
  apply hm _ hmem
  intro r hr
  apply hi
  apply hr.trans_le
  simpa only [dif_pos hmem] using (Finset.le_sup' (f := fun L ↦ if h : L ∈ hf.toFinset then m L h else 0) hmem)

end
end GenLimit.AgnosticLanguage
