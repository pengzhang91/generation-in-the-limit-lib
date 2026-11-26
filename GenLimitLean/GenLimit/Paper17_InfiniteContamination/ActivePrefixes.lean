import GenLimit.Paper17_InfiniteContamination.AlgorithmFour
import GenLimit.Paper17_InfiniteContamination.AlgorithmFive

/-! # Priority-free generation and finite collections (Appendix B) -/

namespace GenLimit.InfiniteContamination
open Filter
open scoped Topology

private noncomputable def freshAbove (L : Set ℕ) (b : ℕ) : ℕ := by
  classical
  exact if h : ∃ x ∈ L, b < x then h.choose else b+1

private theorem freshAbove_gt (L : Set ℕ) (b : ℕ) : b < freshAbove L b := by
  unfold freshAbove
  split
  next h => exact h.choose_spec.2
  next => omega

private theorem freshAbove_mem {L : Set ℕ} (h : L.Infinite) (b : ℕ) :
    freshAbove L b ∈ L := by
  have he := h.exists_gt b
  rw [freshAbove, dif_pos he]
  exact he.choose_spec.1

/-- Choose a member of the current infinite core above all earlier observations
and outputs. The initial empty history precedes the first source round. -/
noncomputable def activeCoreGenerator (core : Generic.SetGenerator ℕ) : Generic.Generator ℕ
  | 0, _ => 0
  | t+1, xs => freshAbove (core (t+1) xs) (max ((Generic.sequenceSample xs).sup id)
      (activeCoreGenerator core t (fun j ↦ xs j.castSucc)))

private theorem activeCore_succ (core : Generic.SetGenerator ℕ) (s : Generic.Stream ℕ) (t : ℕ) :
    Generic.output (activeCoreGenerator core) s (t+1) = freshAbove (setOutput core s (t+1))
      (max ((Generic.sample s (t+1)).sup id) (Generic.output (activeCoreGenerator core) s t)) := by
  rw [← Generic.sequenceSample_prefix]
  rfl

private theorem activeCore_increasing (core : Generic.SetGenerator ℕ) (s : Generic.Stream ℕ) :
    StrictMono (Generic.output (activeCoreGenerator core) s) := by
  apply strictMono_nat_of_lt_succ
  intro t
  rw [activeCore_succ]
  exact (le_max_right ..).trans_lt (freshAbove_gt _ _)

private theorem activeCore_correct (core : Generic.SetGenerator ℕ) (s : Generic.Stream ℕ)
    (L : Set ℕ) (h : ∀ᶠ t in atTop, (setOutput core s t).Infinite ∧ setOutput core s t ⊆ L) :
    GeneratesElementInLimitOn (activeCoreGenerator core) L s := by
  apply eventually_atTop.mp
  filter_upwards [h, eventually_ge_atTop 1] with t ht hpos
  cases t with
  | zero => omega
  | succ t =>
    unfold FreshElementCorrectAt
    refine ⟨?_, ?_, ?_⟩
    · rw [activeCore_succ]
      exact ht.2 (freshAbove_mem ht.1 _)
    · intro hx
      have hle := Finset.le_sup (f := id) hx
      change Generic.output _ _ _ ≤ _ at hle
      rw [activeCore_succ] at hle
      exact (not_lt_of_ge hle) ((le_max_left ..).trans_lt (freshAbove_gt _ _))
    · rintro hx
      obtain ⟨j,hj,he⟩ := mem_generatedBefore_iff.mp hx
      exact (activeCore_increasing core s hj).ne he

private abbrev common (family : ℕ → Set ℕ) (S : Finset ℕ) :=
  finiteCommonCore (indexedLanguages family S)

/-- Eventually every finite intersection in a fixed finite list whose current
noise fraction is bounded away from one is infinite. -/
private theorem eventually_infinite_intersections (family : ℕ → Set ℕ) (F : Finset ℕ)
    (s : Generic.Stream ℕ) (hinj : Function.Injective s) {q : ℝ} (hq : q < 1) :
    ∀ᶠ n in atTop, ∀ S ∈ F.powerset, empiricalNoiseRate s (common family S) n ≤ q →
      (common family S).Infinite := by
  rw [Filter.eventually_all_finset]
  intro S _
  by_cases hi : (common family S).Infinite
  · exact Eventually.of_forall fun _ _ ↦ hi
  have hf := Set.not_infinite.mp hi
  obtain ⟨N,hN⟩ := exists_nat_gt ((hf.toFinset.card : ℝ)/(1-q))
  filter_upwards [eventually_ge_atTop (N+1)] with n hn
  intro hrate
  have hnpos : 0 < n := by omega
  rw [empiricalNoiseRate, if_neg hnpos.ne'] at hrate
  have hfrac := (div_le_iff₀ (show (0:ℝ) < n by exact_mod_cast hnpos)).mp hrate
  have hcard := trueCount_le_finite_card hinj hf n
  have htotal := trueCount_add_noiseCount s (common family S) n
  have htotal' : (trueCount s (common family S) n : ℝ) + noiseCount s (common family S) n = n := by exact_mod_cast htotal
  have hc : (trueCount s (common family S) n : ℝ) ≤ hf.toFinset.card := by exact_mod_cast hcard
  have hn' : (N:ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
  have hlarge := ((div_lt_iff₀ (sub_pos.mpr hq)).mp hN).trans_le (mul_le_mul_of_nonneg_right hn' (sub_nonneg.mpr hq.le))
  exfalso
  linarith

private noncomputable def active (family : ℕ → Set ℕ) (s : Generic.Stream ℕ)
    (t k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range k).filter fun i ↦ empiricalNoiseRate s (family i) t ≤ geometricThreshold i

/-- Algorithm 10 chooses the longest initial segment of the active indices
with infinite intersection, without reordering the indices by priority. -/
noncomputable def algorithmTenCore (family : ℕ → Set ℕ) : Generic.SetGenerator ℕ :=
  fun t xs ↦ by
    classical
    let pref := fun k ↦ active family (prefixCompletion 0 xs) t k
    exact common family (pref (Nat.findGreatest (fun k ↦ (common family (pref k)).Infinite) t))

/-- Theorem B.2. The priority-free active-prefix algorithm tolerates vanishing
noise, using the summable geometric thresholds. -/
theorem algorithmTen_generates (family : ℕ → Set ℕ) (z : ℕ) (s : Generic.Stream ℕ)
    (hinj : Function.Injective s) (hnoise : VanishingNoise s (family z)) :
    GeneratesElementInLimitOn (activeCoreGenerator (algorithmTenCore family)) (family z) s := by
  classical
  apply activeCore_correct
  have htarget := hnoise.eventually_le_const (geometricThreshold_pos z)
  filter_upwards [htarget, eventually_ge_atTop (z+1),
    eventually_infinite_intersections family (Finset.range (z+1)) s hinj (by norm_num : (1/2:ℝ)<1)] with t ht hzt hgood
  let d := prefixCompletion 0 (fun j : Fin t ↦ s j)
  have hrate (i) : empiricalNoiseRate d (family i) t = empiricalNoiseRate s (family i) t :=
    empiricalNoiseRate_eq_of_eq_on_prefix _ (fun k hk ↦ prefixCompletion_eq _ _ hk)
  let pref := fun k ↦ active family d t k
  have hsub (k) : pref k ⊆ Finset.range k := Finset.filter_subset _ _
  have hinf : (common family (pref (z+1))).Infinite := by
    apply hgood _ (Finset.mem_powerset.mpr (hsub _))
    apply (empiricalNoiseRate_indexedCommonCore_le_sum s family _ t).trans
    apply le_trans (Finset.sum_le_sum (g := geometricThreshold) ?_)
    · exact sum_geometricThreshold_le_half (hsub _)
    · intro i hi
      rw [← hrate]
      exact (Finset.mem_filter.mp hi).2
  let k := Nat.findGreatest (fun k ↦ (common family (pref k)).Infinite) t
  have hge : z+1 ≤ k := Nat.le_findGreatest hzt hinf
  change (common family (pref k)).Infinite ∧ common family (pref k) ⊆ family z
  refine ⟨Nat.findGreatest_spec (P := fun k ↦ (common family (pref k)).Infinite) hzt hinf, finiteCommonCore_subset_of_index family _ ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hge, (hrate z).le.trans ht⟩


private noncomputable def countPrefix (k : ℕ) (family : ℕ → Set ℕ)
    (s : Generic.Stream ℕ) (n d : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range k).filter fun j ↦ noiseCount s (family j) n ≤ d

/-- A rule using only the size of the family. Raise the allowed error count
as long as the resulting common intersection remains infinite. -/
noncomputable def finiteClassCore (k : ℕ) (family : ℕ → Set ℕ) : Generic.SetGenerator ℕ :=
  fun t xs ↦ by
    classical
    let pref := countPrefix k family (prefixCompletion 0 xs) t
    exact common family (pref (Nat.findGreatest (fun d ↦ (common family (pref d)).Infinite) t))

/-- Theorem B.4 and the positive half of B.3. The generator is independent
of the unknown noise rate, and tolerates arbitrary omissions. -/
theorem finiteClass_below_reciprocal (k : ℕ) (hk : 0 < k) (family : ℕ → Set ℕ) :
    ∃ gen : Generic.Generator ℕ, ∀ c : ℝ, c < 1/k → ∀ z < k, ∀ s : Generic.Stream ℕ,
      Function.Injective s → ConstantNoise s (family z) c →
      GeneratesElementInLimitOn gen (family z) s := by
  classical
  refine ⟨activeCoreGenerator (finiteClassCore k family), ?_⟩
  intro c hc z hz s hinj hnoise
  obtain ⟨T,hT⟩ := hnoise
  have hc0 := (empiricalNoiseRate_nonneg s (family z) T).trans (hT T le_rfl)
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have hkc : (k:ℝ)*c < 1 := by linarith [(lt_div_iff₀ hk').mp hc]
  apply activeCore_correct
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop 1,
    eventually_infinite_intersections family (Finset.range k) s hinj hkc] with n hn hn1 hall
  let s' := prefixCompletion 0 (fun j : Fin n ↦ s j)
  let pref := countPrefix k family s' n
  let d := noiseCount s (family z) n
  have hcount (j) : noiseCount s' (family j) n = noiseCount s (family j) n :=
    noiseCount_eq_of_eq_on_prefix _ (fun i hi ↦ prefixCompletion_eq _ _ hi)
  have hsub : pref d ⊆ Finset.range k := Finset.filter_subset _ _
  have hcore : (common family (pref d)).Infinite := by
    apply hall _ (Finset.mem_powerset.mpr hsub)
    apply (empiricalNoiseRate_indexedCommonCore_le_sum s family (pref d) n).trans
    calc
      ∑ j ∈ pref d, empiricalNoiseRate s (family j) n ≤ ∑ _j ∈ pref d, c := by
        apply Finset.sum_le_sum
        intro j hj
        apply le_trans ?_ (hT n hn)
        have hle : noiseCount s (family j) n ≤ noiseCount s (family z) n :=
          (hcount j).symm.le.trans (Finset.mem_filter.mp hj).2
        simp only [empiricalNoiseRate, if_neg (show n ≠ 0 by omega)]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (Nat.cast_nonneg _)
      _ ≤ (k:ℝ)*c := by
        have hcard : (pref d).card ≤ k := by simpa using Finset.card_le_card hsub
        simpa using mul_le_mul_of_nonneg_right (show ((pref d).card : ℝ) ≤ k by exact_mod_cast hcard) hc0
  let cut := Nat.findGreatest (fun d ↦ (common family (pref d)).Infinite) n
  have hd : d ≤ n := noiseCount_le s (family z) n
  have hcut : d ≤ cut := Nat.le_findGreatest hd hcore
  change (common family (pref cut)).Infinite ∧ common family (pref cut) ⊆ family z
  refine ⟨Nat.findGreatest_spec (P := fun d ↦ (common family (pref d)).Infinite) hd hcore,
    finiteCommonCore_subset_of_index family _ ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hz, (hcount z).le.trans hcut⟩

end GenLimit.InfiniteContamination
