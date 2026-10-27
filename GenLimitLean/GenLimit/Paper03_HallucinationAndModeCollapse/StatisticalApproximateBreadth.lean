import GenLimit.Paper03_HallucinationAndModeCollapse.ApproximateBreadthModel
import GenLimit.Paper00A_PositiveDataInference.Semantic.Characterization
import GenLimit.Support.Locking
import GenLimit.Support.FullSupportDistribution
import GenLimit.Support.DiscreteSamplePrefix

/-!
# Theorem 3.8: stable approximate breadth has no statistical rate

This alternative finite-sample proof uses the generic locking-sequence
theorem. Stability on every exact presentation gives a target-contained
prefix after which every target-contained continuation has one fixed support.
Every full-support IID law assigns that prefix a fixed positive mass. Thus a
bad locked support forces positive limsup error, independently of sample size.

If all valid distributions had nonpositive limsup error, the locked support
would approximate the target. The prefix contents together with the finitely
many missing target points give a finite tell-tale: any intermediate target
sublanguage inherits the same lock and therefore must contain that support
as well as all the missing points. Angluin's semantic characterization then
gives the no-rate contradiction.

Stability is used essentially in obtaining the lock. The stronger semantic
result needs no MOP; the source-facing theorem retains pointwise decidable
MOP. No infinite-IID/statistical-to-online construction, randomized online
derandomization, or effective construction of the tell-tale is asserted.
-/

namespace GenLimit.HallucinationModeCollapse

noncomputable section

open GenLimit.Generic GenLimit.DiscreteIID GenLimit.Angluin Filter

/-- The existing generic locking theorem applies to the entire support set,
not just to a natural-number hypothesis index. -/
theorem statisticalStable_has_support_lock (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator)
    (hstable : StatisticalStable G C) (i : ℕ) (hK : (C i).Nonempty) :
    ∃ xs S, IsLockingSequence (fun ys => (G ys).support) (C i) xs S := by
  let base := GenLimit.Support.exactPresentation (C i) hK
  have hb : Generic.Presents base (C i) := GenLimit.Support.exactPresentation_presents (C i) hK
  apply exists_lockingSequence_of_converges_with_base hb
  intro stream hstream
  obtain ⟨N, hN⟩ := (statisticalStable_iff G C).mp hstable i stream hstream
  exact ⟨(G (GenLimit.textPrefix stream N)).support, N, fun n hn => hN n N hn le_rfl⟩

/-- A locked support which fails approximate breadth contributes at least
the positive mass of the locking prefix at every sufficiently large size. -/
theorem locked_approximate_failure_limsup_pos (C : Generic.LanguageFamily ℕ)
    (G : StatisticalGenerator) (p : PMF ℕ) (i : ℕ) (xs : List ℕ) (S : Set ℕ)
    (hxs : ListWithin xs p.support)
    (hlock : ∀ tail, ListWithin tail p.support → (G (xs ++ tail)).support = S)
    (hbad : ¬ApproximateBreadthAt S (C i)) :
    0 < limsup (fun n => approximateBreadthError C G p i n) atTop := by
  let δ := (samples p xs.length xs).toReal
  have hδ : 0 < δ := samples_atom_pos p xs hxs
  have hb (n : ℕ) : δ ≤ approximateBreadthError C G p i (xs.length + n) := by
    apply probability_samples_append_ge
    intro tail ht
    change ¬ApproximateBreadthAt (G (xs ++ tail)).support (C i)
    rw [hlock tail ((samples_support p n tail).mp ht).2]
    exact hbad
  have he : ∀ᶠ n : ℕ in atTop, δ ≤ approximateBreadthError C G p i n := by
    apply eventually_atTop.mpr
    refine ⟨xs.length, ?_⟩
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact hb k
  exact hδ.trans_le (le_limsup_of_frequently_le he.frequently
    (isBoundedUnder_of ⟨1, approximateBreadthError_le_one C G p i⟩))

theorem approximate_of_locked_nonpositive_limsup (C : Generic.LanguageFamily ℕ)
    (G : StatisticalGenerator) (p : PMF ℕ) (i : ℕ) (xs : List ℕ) (S : Set ℕ)
    (hxs : ListWithin xs p.support)
    (hlock : ∀ tail, ListWithin tail p.support → (G (xs ++ tail)).support = S)
    (hz : limsup (fun n => approximateBreadthError C G p i n) atTop ≤ 0) :
    ApproximateBreadthAt S (C i) := by
  by_contra hbad
  exact not_lt_of_ge hz (locked_approximate_failure_limsup_pos C G p i xs S hxs hlock hbad)

/-- A stable generator with no positive approximate-breadth limsup on any
valid distribution forces Angluin's semantic finite-tell-tale condition. -/
theorem conditionTwo_of_stable_approximate_nonpositive_limsup
    (C : Generic.LanguageFamily ℕ) (G : StatisticalGenerator) (hstable : StatisticalStable G C)
    (hz : ∀ i p, ValidDistribution C i p →
      limsup (fun n => approximateBreadthError C G p i n) atTop ≤ 0) : ConditionTwo C := by
  classical
  intro i
  by_cases hfinite : (C i).Finite
  · refine ⟨hfinite.toFinset, ?_, ?_⟩
    · intro y hy; simpa using hy
    · intro j hTj _ y hy; exact hTj (by simpa using hy)
  obtain ⟨x, hx⟩ := Set.Infinite.nonempty hfinite
  obtain ⟨xs, S, hxs, hlock⟩ := statisticalStable_has_support_lock C G hstable i ⟨x, hx⟩
  obtain ⟨p, hp, _⟩ := exists_fullSupport_heavyAtom (C i) x hx
  have hS : ApproximateBreadthAt S (C i) :=
    approximate_of_locked_nonpositive_limsup C G p i xs S
      (fun y hy => hp.symm ▸ hxs y hy)
      (fun tail ht => hlock tail (fun y hy => hp ▸ ht y hy)) (hz i p hp)
  let T : Finset ℕ := xs.toFinset ∪ hS.2.toFinset ∪ {x}
  have hxsT (y : ℕ) (hy : y ∈ xs) : y ∈ T :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr hy))
  have hmissingT (y : ℕ) (hy : y ∈ C i \ S) : y ∈ T :=
    Finset.mem_union_left _ (Finset.mem_union_right _ (hS.2.mem_toFinset.mpr hy))
  have hxT : x ∈ T := by simp [T]
  refine ⟨T, ?_, ?_⟩
  · intro y hy
    have hy' : y ∈ T := hy
    rcases (Finset.mem_union.mp hy') with hy | hy
    · rcases Finset.mem_union.mp hy with hy | hy
      · exact hxs y (List.mem_toFinset.mp hy)
      · exact (hS.2.mem_toFinset.mp hy).1
    · have he : y = x := Finset.mem_singleton.mp hy
      exact he ▸ hx
  · intro j hTj hjK
    obtain ⟨q, hq, _⟩ := exists_fullSupport_heavyAtom (C j) x (hTj hxT)
    have hSj : ApproximateBreadthAt S (C j) :=
      approximate_of_locked_nonpositive_limsup C G q j xs S
        (fun y hy => hq.symm ▸ hTj (hxsT y hy))
        (fun tail ht => hlock tail (fun y hy => hjK (hq ▸ ht y hy))) (hz j q hq)
    intro y hy
    by_cases hyS : y ∈ S
    · exact hSj.1 hyS
    · exact hTj (hmissingT y ⟨hy, hyS⟩)

/-- Semantic strengthening of Theorem 3.8: support stability suffices for
the fixed-distribution positive-limsup obstruction, without assuming MOP. -/
theorem noApproximateBreadthRate_of_stable_not_identifiable
    (C : Generic.LanguageFamily ℕ) (hC : ¬IdentifiableInLimit C)
    (G : StatisticalGenerator) (hstable : StatisticalStable G C) : NoApproximateBreadthRate C G := by
  classical
  by_contra hno
  apply hC
  apply (semanticallyInferrable_iff_conditionTwo C).mpr
  apply conditionTwo_of_stable_approximate_nonpositive_limsup C G hstable
  intro i p hp
  by_contra hnot
  exact hno ⟨i, p, hp, lt_of_not_ge hnot⟩

/-- Theorem 3.8 in the explicit semantic/Condition-2 identifiability model,
retaining the source's stability and pointwise decidable-MOP hypotheses. -/
theorem theorem_3_8 (C : Generic.LanguageFamily ℕ) (hC : ¬IdentifiableInLimit C)
    (G : StatisticalGenerator) (hstable : StatisticalStable G C) (_hMOP : DecidableMOP G) :
    NoApproximateBreadthRate C G :=
  noApproximateBreadthRate_of_stable_not_identifiable C hC G hstable

end
end GenLimit.HallucinationModeCollapse
