import GenLimit.Paper13_ParetoOptimalNonuniformGeneration.VariantExactPareto
import GenLimit.Paper09_RepresentativeLanguageGeneration.FinitePartitionCorollaries

/-! # Representative generation times

Feasibility on a finite history asks for one distribution with the empirical
group profile to tolerance and with fresh support in every selected language.
For a finite partition this is exactly the negation of group scarcity. A
target's maximal obstructing sample can be found from the finalized times
of earlier indices. This gives a direct computation of the threshold,
including the zero convention when no such sample exists. -/
namespace GenLimit.ParetoGeneration.Representative
open RepresentativeGeneration
open scoped ENNReal
variable {α : Type*} [DecidableEq α]

def Feasible (F : ℕ → Set α) (groups : ℕ → Set α) (ε : ℝ) (S : Finset α)
    (W : Finset ℕ) : Prop :=
  ∃ μ : DiscreteDistribution α, groupSupDistance μ S groups ≤ ENNReal.ofReal ε ∧
    ∀ j ∈ W, SupportedOn μ (F j \ (↑S : Set α))

private theorem from_closure {F : ℕ → Set α} {groups : ℕ → Set α} {ε : ℝ}
    {S : Finset α} {W : Finset ℕ} {H : Set (Set α)}
    (h : ClosureFeasibleAt H groups ε S)
    (hw : ∀ j ∈ W, F j ∈ consistentHypotheses H S) : Feasible F groups ε S W := by
  obtain ⟨μ,hs,hr⟩ := h
  exact ⟨μ,hr,fun j hj x hx ↦ ⟨(hs x hx).1 _ (hw j hj),(hs x hx).2⟩⟩

/-- Definition 7. The two conditions bound each scarce group's lost mass
and the total capacity of the non-scarce groups, respectively. -/
theorem scarcity_iff {F : ℕ → Set α} {groups : ℕ → Set α} {ε : ℝ} {S : Finset α}
    {W : Finset ℕ} (hp : IsCountablePartition groups) (hε : 0 < ε)
    (hs : S.Nonempty) (hw : W.Nonempty) (hc : ∀ j ∈ W, (↑S : Set α) ⊆ F j) :
    ¬ Feasible F groups ε S W ↔
      groupClosureConditionOne (F '' (↑W : Set ℕ)) groups ε S ∨
      groupClosureConditionTwo (F '' (↑W : Set ℕ)) groups ε S := by
  classical
  let H := F '' (↑W : Set ℕ)
  have eqv : Feasible F groups ε S W ↔ ClosureFeasibleAt H groups ε S := by
    constructor
    · rintro ⟨μ,hr,hμ⟩
      refine ⟨μ,fun x hx ↦ ⟨?_,?_⟩,hr⟩
      · rintro L ⟨⟨j,hj,rfl⟩,_⟩
        exact (hμ j hj x hx).1
      · obtain ⟨j,hj⟩ := hw
        exact (hμ j hj x hx).2
    · exact fun h ↦ from_closure h (fun j hj ↦ ⟨⟨j,hj,rfl⟩,hc j hj⟩)
  constructor
  · intro h
    by_contra! hno
    exact h (eqv.mpr (closureFeasible_of_not_groupClosureConditions hp hε hs hno.1 hno.2))
  · intro h hf
    exact h.elim (closureFeasible_not_groupClosureConditionOne (eqv.mp hf))
      (closureFeasible_not_groupClosureConditionTwo hp hε hs (eqv.mp hf))

/-- A single causal distribution-valued learner on arbitrary histories.
Repetitions count once for both the empirical profile and the time budget. -/
def Realizable (F : ℕ → Set α) (groups : ℕ → Set α) (ε : ℝ) : Set TimeVector :=
  {t | PositiveTimeVector t ∧ ∃ G : List α → DiscreteDistribution α,
    ∀ xs, xs.toFinset.Nonempty →
      groupSupDistance (G xs) xs.toFinset groups ≤ ENNReal.ofReal ε ∧
      ∀ i, t i ≤ xs.toFinset.card → (↑xs.toFinset : Set α) ⊆ F i →
        SupportedOn (G xs) (F i \ (↑xs.toFinset : Set α))}

/-- A finite subcollection prevents a joint output, and every older
coordinate in it already requires correctness at this history size. -/
def Obstruction (F : ℕ → Set α) (groups : ℕ → Set α) (ε : ℝ)
    (i : ℕ) (earlier : ∀ j, j < i → ℕ) (n : ℕ) : Prop :=
  ∃ (S : Finset α) (W : Finset ℕ), S.card = n ∧ S.Nonempty ∧ i ∈ W ∧
    (∀ j ∈ W, j ≤ i ∧ (↑S : Set α) ⊆ F j ∧ ∀ h : j < i, earlier j h < n) ∧
    ¬ Feasible F groups ε S W

theorem obstruction_sizes_bounded {k : ℕ} (F : ℕ → Set α) (groups : Fin k → Set α)
    (hp : IsFinitePartition groups) (ε : ℝ) (hε : 0 < ε) (i : ℕ)
    (earlier : ∀ j, j < i → ℕ) :
    BddAbove (insert 0 {n | Obstruction F (extendFinitePartition groups) ε i earlier n}) := by
  classical
  let H := F '' (↑(Finset.range (i+1)) : Set ℕ)
  obtain ⟨d,hd⟩ := finite_languageClass_has_finite_groupClosureDimension
    (show H.Finite from (Finset.range _).finite_toSet.image F) groups hp hε
  refine ⟨d,fun n hn ↦ ?_⟩
  rcases hn with rfl | ⟨S,W,rfl,hS,hi,hW,hbad⟩
  · omega
  · by_contra! hlarge
    have members (j) (hj : j ∈ W) : F j ∈ consistentHypotheses H S :=
      ⟨⟨j,Finset.mem_range.mpr (Nat.lt_succ_of_le (hW j hj).1),rfl⟩,(hW j hj).2.1⟩
    exact hbad (from_closure (closureFeasible_of_card_gt_dimensionBound hp hε hd
      hS ⟨F i,members i hi⟩ hlarge) members)

/-- The maximal obstructing size, including 0 as the default for empty
candidate sets. The recursive calls use only earlier family indices. -/
noncomputable def complexity (F : ℕ → Set α) (groups : ℕ → Set α) (ε : ℝ) (i : ℕ) : ℕ :=
  sSup (insert 0 {n | Obstruction F groups ε i (fun j _ ↦ complexity F groups ε j) n})
termination_by i

/-- Each maximization reached in the insertion has a bounded set of sizes.
This condition is automatic at positive tolerance. At zero tolerance it
makes explicit when a numerical complexity can be assigned. -/
def BoundedObstructions (F : ℕ → Set α) (groups : ℕ → Set α) (ε : ℝ) :=
  ∀ i, BddAbove (insert 0 {n | Obstruction F groups ε i
    (fun j _ ↦ complexity F groups ε j) n})

private theorem bound_score (F : ℕ → Set α) (groups : ℕ → Set α)
    (ε : ℝ) (hbounds : BoundedObstructions F groups ε) {i n : ℕ}
    (h : Obstruction F groups ε i
      (fun j _ ↦ complexity F groups ε j) n) :
    n ≤ complexity F groups ε i := by
  rw [complexity]
  exact le_csSup (hbounds i) (Set.mem_insert_of_mem _ h)

private theorem score_attained (F : ℕ → Set α) (groups : ℕ → Set α)
    (ε : ℝ) (hbounds : BoundedObstructions F groups ε) (i : ℕ)
    (hpos : 0 < complexity F groups ε i) :
    Obstruction F groups ε i
      (fun j _ ↦ complexity F groups ε j)
      (complexity F groups ε i) := by
  let g := groups
  let d := complexity F g ε
  let B := insert 0 {n | Obstruction F g ε i (fun j _ ↦ d j) n}
  have h : d i ∈ B := by
    change complexity F g ε i ∈ B
    rw [complexity]
    exact Nat.sSup_mem ⟨0,Set.mem_insert _ _⟩ (hbounds i)
  exact h.resolve_left (Nat.ne_of_gt hpos)

/-- All consistent coordinates that have passed their deadlines share a common
fresh distribution. A finite obstruction would contradict the score of its
largest index. -/
theorem feasible_due (F : ℕ → Set α) (g : ℕ → Set α) (ε : ℝ)
    (hb : BoundedObstructions F g ε) (S : Finset α) (hs : S.Nonempty)
    (W : Finset ℕ) (hW : ∀ j ∈ W, complexity F g ε j < S.card ∧ (↑S : Set α) ⊆ F j) :
    Feasible F g ε S W := by
  classical
  by_cases hw : W.Nonempty
  · by_contra h
    let i := W.max' hw
    have hi : i ∈ W := Finset.max'_mem _ _
    have ho : Obstruction F g ε i (fun j _ ↦ complexity F g ε j) S.card :=
      ⟨S,W,rfl,hs,hi,fun j hj ↦ ⟨Finset.le_max' _ j hj,(hW j hj).2,fun _ ↦ (hW j hj).1⟩,h⟩
    exact (Nat.not_lt_of_ge (bound_score F g ε hb ho)) (hW i hi).1
  · exact ⟨empiricalPointDistribution S hs,by rw [empiricalPointDistribution_distance_zero]; exact bot_le,
      fun j hj ↦ (hw ⟨j,hj⟩).elim⟩

private theorem scheduler [Nonempty α] (F : ℕ → Set α) (groups : ℕ → Set α)
    (ε : ℝ) (hbounds : BoundedObstructions F groups ε)
    (f : ℕ → ℕ) (hf : IsUnboundedScheduler f) :
    (fun i ↦ max (schedulerEntryTime f hf i) (complexity F groups ε i + 1))
      ∈ Realizable F groups ε := by
  classical
  let g := groups
  let d := complexity F g ε
  let active (S : Finset α) := (Finset.range (f S.card)).filter
    (fun i ↦ d i < S.card ∧ (↑S : Set α) ⊆ F i)
  have feas (S : Finset α) (hS : S.Nonempty) : Feasible F g ε S (active S) := by
    exact feasible_due F g ε hbounds S hS (active S) (fun _ hj ↦ (Finset.mem_filter.mp hj).2)
  let G (xs : List α) := if hs : xs.toFinset.Nonempty then (feas xs.toFinset hs).choose
    else DiscreteDistribution.ofPMF (PMF.pure (Classical.choice (inferInstance : Nonempty α)))
  refine ⟨fun i ↦ (Nat.succ_le_succ (Nat.zero_le _)).trans (le_max_right _ _),G,fun xs hs ↦ ?_⟩
  dsimp only [G]
  rw [dif_pos hs]
  have hm := (feas xs.toFinset hs).choose_spec
  refine ⟨hm.1,fun i ht hc ↦ hm.2 i (Finset.mem_filter.mpr ⟨?_,?_,hc⟩)⟩
  · exact Finset.mem_range.mpr ((schedulerEntryTime_le_iff f hf).mp ((le_max_left _ _).trans ht))
  · exact (le_max_right _ _).trans ht

private theorem tradeoff (F : ℕ → Set α) (groups : ℕ → Set α)
    (ε : ℝ) (hbounds : BoundedObstructions F groups ε) :
    EarlierTradeoff (variantCanonicalTime (complexity F groups ε))
      (Realizable F groups ε) := by
  intro t ⟨ht,G,hG⟩ i hi
  let g := groups
  let d := complexity F g ε
  change t i < d i+1 at hi
  have pos : 0 < d i := by have := ht i; omega
  obtain ⟨S,W,hs,hS,hI,hW,hb⟩ := score_attained F groups ε hbounds i pos
  by_contra! hn
  obtain ⟨hr,hμ⟩ := hG S.toList (by simpa using hS)
  apply hb
  refine ⟨G S.toList,by simpa using hr,fun j hj ↦ ?_⟩
  have hm := hW j hj
  have htime : t j ≤ S.card := by
    rcases hm.1.lt_or_eq with hlt | rfl
    · exact (hn j hlt).trans (by simpa [variantCanonicalTime,hs] using hm.2.2 hlt)
    · change S.card = d j at hs
      omega
  simpa using hμ j (by simpa using htime) (by simpa using hm.2.1)

/-- The substantive representative scheduler and earlier-coordinate tradeoff
are witnessed by a concrete probability-distribution model. -/
theorem certificate {k : ℕ} [Nonempty α] (F : ℕ → Set α) (groups : Fin k → Set α)
    (hp : IsFinitePartition groups) (ε : ℝ) (hε : 0 < ε) :
    VariantSchedulerCertificate (Realizable F (extendFinitePartition groups) ε)
      (complexity F (extendFinitePartition groups) ε) :=
  ⟨scheduler F _ ε (fun i ↦ obstruction_sizes_bounded F groups hp ε hε i _),
    tradeoff F _ ε (fun i ↦ obstruction_sizes_bounded F groups hp ε hε i _)⟩

/-- The positive-tolerance generation time bound, with arbitrary schedules. -/
theorem theorem_7 {k : ℕ} [Nonempty α] (F : ℕ → Set α) (groups : Fin k → Set α)
    (hp : IsFinitePartition groups) (ε : ℝ) (hε : 0 < ε) (f : ℕ → ℕ)
    (hf : IsUnboundedScheduler f) :
    (fun i ↦ max (schedulerEntryTime f hf i) (complexity F (extendFinitePartition groups) ε i + 1))
      ∈ Realizable F (extendFinitePartition groups) ε :=
  (certificate F groups hp ε hε).scheduler_realizable f hf

/-- Exact Pareto optimality under the finite-sublevel condition of Theorem 9. -/
theorem theorem_9 {k : ℕ} [Nonempty α] (F : ℕ → Set α) (groups : Fin k → Set α)
    (hp : IsFinitePartition groups) (ε : ℝ) (hε : 0 < ε)
    (hf : FiniteSublevels (complexity F (extendFinitePartition groups) ε)) :
    variantCanonicalTime (complexity F (extendFinitePartition groups) ε) ∈
      Realizable F (extendFinitePartition groups) ε ∧
    ParetoOptimal (Realizable F (extendFinitePartition groups) ε)
      (variantCanonicalTime (complexity F (extendFinitePartition groups) ε)) :=
  variant_exactPareto_of_finiteSublevels (certificate F groups hp ε hε) hf

/-- Includes zero tolerance whenever the scarcity maxima in Procedure 3
exist. The unbounded singleton-group example falls outside this domain. -/
theorem of_bounded_scarcity [Nonempty α] (F : ℕ → Set α) (groups : ℕ → Set α)
    (ε : ℝ) (hb : BoundedObstructions F groups ε) :
    VariantSchedulerCertificate (Realizable F groups ε) (complexity F groups ε) :=
  ⟨scheduler F groups ε hb,tradeoff F groups ε hb⟩

end GenLimit.ParetoGeneration.Representative
