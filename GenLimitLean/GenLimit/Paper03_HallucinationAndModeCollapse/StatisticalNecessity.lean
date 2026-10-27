import GenLimit.Paper03_HallucinationAndModeCollapse.StatisticalModel
import GenLimit.Paper00A_PositiveDataInference.Semantic.Definitions
import GenLimit.Support.DiscreteLawContinuity

/-!
# Statistical necessity of finite tell-tales

An independent Baire-category proof of the no-rate ingredient of P03
Theorem 3.1. It works for all randomized PMF kernels and uses finite-sample
laws only, without taking Angluin (1988) or an infinite-IID theorem as an
unproved premise. If a learner eventually has error below one half for every valid
distribution, closed error constraints cover the dense G-delta set of
surjective sequences. Baire category supplies one finite cylinder on which
the target has error at most one half. Its finite content is a tell-tale:
otherwise extend that prefix to a proper target sublanguage and contradict
the two-target error inequality.
-/

namespace GenLimit.HallucinationModeCollapse

noncomputable section

open GenLimit.Generic GenLimit.DiscreteIID Filter
open scoped Topology

theorem conditionTwo_of_eventual_small_error
    (C : Generic.LanguageFamily ℕ) (A : StatisticalIdentifier)
    (hA : ∀ i p, ValidDistribution C i p →
      ∀ᶠ n : ℕ in atTop, identificationError C A p i n < (1 / 2 : ℝ)) :
    GenLimit.Angluin.ConditionTwo C := by
  classical
  letI := baire_natSequences
  intro i
  by_cases hfinite : (C i).Finite
  · refine ⟨hfinite.toFinset, ?_, ?_⟩
    · intro x hx; simpa using hx
    · intro j hj _ x hx; exact hj (by simpa using hx)
  have hK : (C i).Nonempty := Set.Infinite.nonempty hfinite
  letI : Nonempty (C i) := hK.to_subtype
  obtain ⟨enum, henum⟩ := exists_surjective_nat (C i)
  let e : ℕ → ℕ := fun k => (enum k).1
  have he (x : ℕ) : x ∈ C i ↔ ∃ k, e k = x := by
    constructor
    · intro hx; obtain ⟨k, hk⟩ := henum ⟨x, hx⟩; exact ⟨k, congrArg Subtype.val hk⟩
    · rintro ⟨k, rfl⟩; exact (enum k).2
  let law := fun s : ℕ → ℕ => sequenceLaw (e ∘ s)
  have hvalid (s : ℕ → ℕ) (hs : Function.Surjective s) : ValidDistribution C i (law s) := by
    rw [ValidDistribution, sequenceLaw_support]
    ext x
    constructor
    · rintro ⟨k, rfl⟩; exact (enum (s k)).2
    · intro hx
      obtain ⟨k, hk⟩ := (he x).mp hx
      obtain ⟨l, rfl⟩ := hs k
      exact ⟨l, hk⟩
  have hcont (n : ℕ) : Continuous (fun s : ℕ → ℕ => identificationError C A (law s) i n) := by
    apply (continuous_sequence_experiment n A {j | C j ≠ C i}).comp
    exact continuous_pi (fun k => continuous_of_discreteTopology.comp (continuous_apply k))
  let F (N : ℕ) : Set (ℕ → ℕ) := {s | ∀ n ≥ N, identificationError C A (law s) i n ≤ (1 / 2 : ℝ)}
  have hclosed (N : ℕ) : IsClosed (F N) := by
    have heq : F N = ⋂ n : ℕ, ⋂ _hn : N ≤ n,
        {s | identificationError C A (law s) i n ≤ (1 / 2 : ℝ)} := by ext s; simp [F]
    rw [heq]
    exact isClosed_iInter (fun n => isClosed_iInter (fun _ => isClosed_le (hcont n) continuous_const))
  have hcover : {s : ℕ → ℕ | Function.Surjective s} ⊆ ⋃ N, F N := by
    intro s hs
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hA i (law s) (hvalid s hs))
    exact Set.mem_iUnion.mpr ⟨N, fun n hn => (hN n hn).le⟩
  have hd := surjective_sequences_dense_gdelta.1.dense_iUnion_interior_of_closed
    surjective_sequences_dense_gdelta.2 hclosed hcover
  obtain ⟨s, hs⟩ := hd.nonempty
  obtain ⟨N, hsN⟩ := Set.mem_iUnion.mp hs
  obtain ⟨V, ⟨t, n, rfl⟩, _hsV, hVF⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ => ℕ)).exists_subset_of_mem_open hsN isOpen_interior
  let m := n + 1
  let T := (Finset.range m).image (e ∘ t)
  have hTK : (↑T : Set ℕ) ⊆ C i := by
    intro x hx; obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx; exact (enum (t k)).2
  refine ⟨T, hTK, ?_⟩
  intro j hTj hjK
  by_contra hKj
  have hJ : (C j).Nonempty := ⟨e (t 0), hTj (Finset.mem_image.mpr
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _), rfl⟩)⟩
  letI : Nonempty (C j) := hJ.to_subtype
  obtain ⟨enJ, henJ⟩ := exists_surjective_nat (C j)
  have hex (k : ℕ) : ∃ l, e l = (enJ k).1 := (he _).mp (hjK (enJ k).2)
  let f := fun k => Classical.choose (hex k)
  let u : ℕ → ℕ := fun k => if k < m then t k else f (k - m)
  have hu : u ∈ PiNat.cylinder t n := by
    apply PiNat.mem_cylinder_iff.mpr
    intro k hk
    simp [u, show k < m from Nat.lt_succ_of_lt hk]
  have huF : u ∈ F N := interior_subset (hVF hu)
  have hvalidJ : ValidDistribution C j (law u) := by
    rw [ValidDistribution, sequenceLaw_support]
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      by_cases hk : k < m
      · change e (u k) ∈ C j
        simpa [u, hk] using hTj (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩)
      · change e (u k) ∈ C j
        simp only [u, if_neg hk]
        rw [Classical.choose_spec (hex (k - m))]
        exact (enJ (k - m)).2
    · intro hx
      obtain ⟨k, hk⟩ := henJ ⟨x, hx⟩
      refine ⟨m + k, ?_⟩
      change e (u (m + k)) = x
      simp only [u, show ¬m + k < m by omega, if_false, Nat.add_sub_cancel_left]
      exact (Classical.choose_spec (hex k)).trans (congrArg Subtype.val hk)
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hA j (law u) hvalidJ)
  have hlow := huF (max N M) (le_max_left _ _)
  have hupp := hM (max N M) (le_max_right _ _)
  have hsum := identificationError_add_ge_one C A (law u) i j (max N M)
    (fun h => hKj h.subset)
  linarith

/-- Strong finite-sample form of Lemma 5.8: one valid distribution has error
at least one half infinitely often. In particular its limsup is positive. -/
theorem lemma_5_8_frequently
    (C : Generic.LanguageFamily ℕ) (hC : ¬GenLimit.Angluin.ConditionTwo C)
    (A : StatisticalIdentifier) :
    ∃ i p, ValidDistribution C i p ∧
      ∃ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ≤ identificationError C A p i n := by
  classical
  by_contra h
  apply hC
  apply conditionTwo_of_eventual_small_error C A
  intro i p hp
  have hn : ¬∃ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ≤ identificationError C A p i n :=
    fun hf => h ⟨i, p, hp, hf⟩
  simpa only [not_le] using not_frequently.mp hn

end
end GenLimit.HallucinationModeCollapse
