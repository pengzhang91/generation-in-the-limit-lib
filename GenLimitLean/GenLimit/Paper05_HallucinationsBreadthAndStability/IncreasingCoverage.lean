import GenLimit.Paper05_HallucinationsBreadthAndStability.StabilityGap
import GenLimit.Paper05_HallucinationsBreadthAndStability.CorrectedStability
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Set.Finite.Lattice

/-! # Proposition 8.14 under the two source conventions -/

namespace GenLimit.BreadthCharacterizations

/-- Definition 8.13, including its full-target stopping condition. -/
def IncreasingCoverage (G : SupportAlgorithm α) (F : Generic.LanguageFamily α) : Prop :=
  ∀ i s, Generic.Presents s (F i) → ∃ T, ∀ t ≥ T,
    supportAt G s t ⊆ supportAt G s (t+1) ∧
      (supportAt G s t = F i ∨ ∃ u > t, supportAt G s t ⊂ supportAt G s u)

/-- Footnote 17 allows previously seen words in an infinite valid support. -/
def SampleAllowingInfiniteCoverage (G : SupportAlgorithm α) (F : Generic.LanguageFamily α) : Prop :=
  ∀ i s, Generic.Presents s (F i) → ∃ T, ∀ t ≥ T,
    supportAt G s t ⊆ F i ∧ (supportAt G s t).Infinite

def integerRayFamily : Generic.LanguageFamily ℤ
  | 0 => Set.univ
  | n+1 => Set.Ici (Equiv.intEquivNat.symm n)

/-- After a nonempty prefix this is precisely the ray starting at the
smallest observed integer. -/
def observedRays (xs : List ℤ) : Set ℤ := {y | ∃ x ∈ xs, x ≤ y}

private theorem rays_mono (s : ℕ → ℤ) {n m : ℕ} (hn : n ≤ m) :
    supportAt observedRays s n ⊆ supportAt observedRays s m := by
  rintro y ⟨x,hx,hxy⟩
  obtain ⟨k,hk,eq⟩ := mem_textPrefix_iff.mp hx
  exact ⟨x,mem_textPrefix_iff.mpr ⟨k,hk.trans_le hn,eq⟩,hxy⟩

private theorem rays_valid {i : ℕ} {s : ℕ → ℤ} (hp : Generic.Presents s (integerRayFamily i)) (t : ℕ) :
    supportAt observedRays s t ⊆ integerRayFamily i := by
  rintro y ⟨x,hx,hxy⟩
  obtain ⟨k,_,rfl⟩ := mem_textPrefix_iff.mp hx
  have h : s k ∈ integerRayFamily i := hp ▸ Set.mem_range_self k
  cases i with
  | zero => trivial
  | succ _ => exact le_trans h hxy

private theorem rays_no_weak : ¬WeakAngluinCondition integerRayFamily := by
  intro hw
  obtain ⟨T,_,h⟩ := hw 0
  obtain ⟨a,ha⟩ := T.finite_toSet.bddBelow
  let j := Equiv.intEquivNat a + 1
  have hj : integerRayFamily j = Set.Ici a := by simp [j, integerRayFamily]
  have hproper : Set.Ici a ⊂ (Set.univ : Set ℤ) := by
    refine ⟨Set.subset_univ _, fun h => ?_⟩
    have bad : a ≤ a-1 := h (Set.mem_univ (a-1))
    omega
  have hf := h j (by rw [hj]; exact ha) (by rw [hj]; exact hproper)
  rw [hj] at hf
  apply Set.Iio_infinite a
  apply hf.subset
  intro x hx
  change x < a at hx
  exact ⟨Set.mem_univ _, fun hax => (not_le.mpr hx) (show a ≤ x from hax)⟩

/-- Example 8.12 and Proposition 8.14 with exactly the convention of
footnote 17. A point outside today's support appears in a later prefix. -/
theorem proposition_8_14_sampleAllowing :
    ¬WeakAngluinCondition integerRayFamily ∧
      SampleAllowingInfiniteCoverage observedRays integerRayFamily ∧
      IncreasingCoverage observedRays integerRayFamily := by
  refine ⟨rays_no_weak, ?_, ?_⟩
  · intro i s hp
    refine ⟨1,fun t ht => ⟨rays_valid hp t,?_⟩⟩
    exact (Set.Ici_infinite (s 0)).mono (fun y hy =>
      ⟨s 0, mem_textPrefix_iff.mpr ⟨0,ht,rfl⟩,hy⟩)
  · intro i s hp
    refine ⟨1,fun t _ => ⟨rays_mono s (by omega),?_⟩⟩
    by_cases eq : supportAt observedRays s t = integerRayFamily i
    · exact Or.inl eq
    · right
      have hn : ¬integerRayFamily i ⊆ supportAt observedRays s t :=
        fun h => eq (Set.Subset.antisymm (rays_valid hp t) h)
      obtain ⟨y,hy,hn⟩ := Set.not_subset.mp hn
      obtain ⟨k,rfl⟩ := hp.symm ▸ hy
      let u := max t k + 1
      have hu : t < u := by dsimp [u]; omega
      refine ⟨u,hu,rays_mono s hu.le,fun h => hn (h ?_)⟩
      exact ⟨s k,mem_textPrefix_iff.mpr ⟨k,by dsimp [u]; omega,rfl⟩,le_rfl⟩

/-- In the literal Definition 8.3 every support must avoid the cumulative
sample. Even eventual monotone inclusion would preserve some element past
the stage at which a complete presentation observes it. -/
theorem increasing_literal_incompatible {F : Generic.LanguageFamily α} {G : SupportAlgorithm α}
    {s : ℕ → α} {i : ℕ} (hp : Generic.Presents s (F i)) (hm : IncreasingCoverage G F)
    (hc : IsInfiniteCoverageGenerator G F) : False := by
  obtain ⟨A,hA⟩ := hm i s hp
  obtain ⟨B,hB⟩ := hc i s hp
  let n := max A B
  obtain ⟨x,hx⟩ := (hB n (Nat.le_max_right _ _)).2.2.nonempty
  obtain ⟨k,hk⟩ := Generic.eventually_mem_sample_of_presents hp ((hB n (Nat.le_max_right _ _)).1 hx)
  let m := max n k
  have hm' : ∀ u ≥ n, x ∈ supportAt G s u := by
    intro u hu
    induction u, hu using Nat.le_induction with
    | base => exact hx
    | succ u hu ih => exact (hA u ((Nat.le_max_left A B).trans hu)).1 ih
  exact Set.disjoint_left.mp (hB m ((Nat.le_max_right A B).trans (Nat.le_max_left n k))).2.1
    (hm' m (Nat.le_max_left n k)) (hk m (Nat.le_max_right n k))

/-- Section 8.3. Choose a late stage minimizing the finite number of
missing words. Any later strict growth would decrease that number. -/
theorem increasing_approximate_wholeTarget {G : SupportAlgorithm α} {F : Generic.LanguageFamily α}
    (hm : IncreasingCoverage G F) (ha : IsApproximateBreadthGenerator G F) :
    IsWholeTargetGenerator G F := by
  classical
  intro i s hp
  obtain ⟨A,hA⟩ := hm i s hp
  obtain ⟨B,hB⟩ := ha i s hp
  let N := max A B
  let missing (t : ℕ) := F i \ supportAt G s t
  have existsCount : ∃ k, ∃ t ≥ N, (missing t).ncard = k := ⟨_,N,le_rfl,rfl⟩
  obtain ⟨t,ht,hcard⟩ := Nat.find_spec existsCount
  have whole : supportAt G s t = F i := by
    rcases (hA t ((Nat.le_max_left ..).trans ht)).2 with eq | ⟨u,hu,strict⟩
    · exact eq
    · exfalso
      have valid := (hB u ((Nat.le_max_right ..).trans (ht.trans hu.le))).1
      have decrease : missing u ⊂ missing t := by
        refine ⟨Set.diff_subset_diff_right strict.1,fun rev ↦ strict.2 ?_⟩
        intro x hx
        by_contra absent
        exact (rev (show x ∈ missing t from ⟨valid hx,absent⟩)).2 hx
      have smaller := Set.ncard_lt_ncard decrease (hB t ((Nat.le_max_right ..).trans ht)).2
      exact (Nat.not_lt_of_ge (Nat.find_min' existsCount ⟨u,ht.trans hu.le,rfl⟩))
        (hcard ▸ smaller)
  refine ⟨t,fun u htu ↦ ?_⟩
  have incl : supportAt G s t ⊆ supportAt G s u := by
    induction u, htu using Nat.le_induction with
    | base => exact Set.Subset.rfl
    | succ u hu ih => exact ih.trans (hA u ((Nat.le_max_left ..).trans (ht.trans hu))).1
  exact Set.Subset.antisymm (hB u ((Nat.le_max_right ..).trans (ht.trans htu))).1 (whole ▸ incl)

theorem increasing_approximate_requires_conditionTwo [Nonempty α] [Countable α]
    {G : SupportAlgorithm α} {F : Generic.LanguageFamily α}
    (hm : IncreasingCoverage G F) (ha : IsApproximateBreadthGenerator G F) : Angluin.ConditionTwo F :=
  literalExact_implies_conditionTwo ⟨_,wholeTarget_implies_literalExact (increasing_approximate_wholeTarget hm ha)⟩

end GenLimit.BreadthCharacterizations
