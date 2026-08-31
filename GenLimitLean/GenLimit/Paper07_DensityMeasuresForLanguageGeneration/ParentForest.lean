import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.Levels
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.StrictCritical
import Mathlib.Data.Nat.Nth

/-!
# Kleinberg--Wei finite-rank parent forest

This module formalizes the parent-selection layer and Property 6.5 of
*Density Measures for Language Generation*.

The paper numbers rounds from one.  Lean exposes a zero-based `round`, so
the remaining languages and strict-critical candidates use the first
`round + 1` observations, while the infinite-chain branch selects
`Nat.nth ... round`.  Thus Lean round `s` is literally paper round `s + 1`.

The graph relation is defined on the subtype of languages that remain
consistent with the observed sample.  Its eligible parents are the strictly
critical strict supersets at a strictly higher Cantor--Bendixson level.
Finite nonempty candidate sets use their largest family index, which is the
inclusion-minimum language because strict-critical languages form a
reverse-inclusion chain.  Infinite candidate sets use the paper's ranked
descending-chain choice.
-/

namespace GenLimit
namespace KleinbergWei
namespace DensityMeasures

open TowerTopology

namespace FiniteRankParent

/-- The topological language collection underlying an indexed family. -/
abbrev FamilySpace (C : LanguageFamily) : Set Language :=
  Set.range C

/-- A language in the range of an indexed family. -/
abbrev FamilyPoint (C : LanguageFamily) :=
  Point (FamilySpace C)

/-- The point represented by a particular family index. -/
def familyPoint (C : LanguageFamily) (n : ℕ) : FamilyPoint C :=
  ⟨C n, Set.mem_range_self n⟩

@[simp] theorem familyPoint_val (C : LanguageFamily) (n : ℕ) :
    (familyPoint C n).1 = C n :=
  rfl

/-- A language remains at zero-based round `round` exactly when it contains
the first `round + 1` observed values. -/
def RemainingAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (round : ℕ)
    (L : FamilyPoint C) : Prop :=
  (↑(sample stream (round + 1)) : Set ℕ) ⊆ L.1

/-- The vertices of the paper's forest at zero-based round `round`. -/
abbrev RemainingPoint
    (C : LanguageFamily) (stream : ℕ → ℕ) (round : ℕ) :=
  {L : FamilyPoint C // RemainingAt C stream round L}

/-- A nonempty finite-rank space cannot have rank bound zero. -/
theorem finiteRankAtMost_ne_zero
    {X : Set Language} {r : ℕ}
    (hr : FiniteRankAtMost X r) (L : Point X) :
    r ≠ 0 := by
  intro hr0
  subst r
  have hL : L ∈ cbDerivative X 0 := by simp
  unfold FiniteRankAtMost at hr
  rw [hr] at hL
  simp at hL

/-- Every point of a finite-rank space lies at a level strictly below the
rank bound. -/
theorem exists_level_lt_of_finiteRankAtMost
    {X : Set Language} {r : ℕ}
    (hr : FiniteRankAtMost X r) (L : Point X) :
    ∃ i, i < r ∧ L ∈ cbLevel X i := by
  classical
  have hrne : r ≠ 0 := finiteRankAtMost_ne_zero hr L
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hrne
  let S : Finset ℕ :=
    (Finset.range (q + 1)).filter fun i =>
      L ∉ cbDerivative X (i + 1)
  have hqS : q ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_succ_self q, ?_⟩
    intro hq
    unfold FiniteRankAtMost at hr
    rw [hr] at hq
    simp at hq
  have hSne : S.Nonempty := ⟨q, hqS⟩
  let i := S.min' hSne
  have hiS : i ∈ S := Finset.min'_mem S hSne
  have hiParts :
      i < q + 1 ∧ L ∉ cbDerivative X (i + 1) := by
    simpa only [S, Finset.mem_filter, Finset.mem_range] using hiS
  have hiMem : L ∈ cbDerivative X i := by
    by_cases hi0 : i = 0
    · simp [hi0]
    · obtain ⟨k, hik⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      by_contra hiNot
      have hkNot : L ∉ cbDerivative X (k + 1) := by
        simpa [hik] using hiNot
      have hkS : k ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hkNot⟩
      have hmin : i ≤ k := by
        dsimp only [i]
        exact Finset.min'_le S k hkS
      omega
  exact ⟨i, hiParts.1, hiMem, hiParts.2⟩

/-- Cantor--Bendixson levels are unique. -/
theorem cbLevel_index_unique
    {X : Set Language} {L : Point X} {i j : ℕ}
    (hi : L ∈ cbLevel X i) (hj : L ∈ cbLevel X j) :
    i = j := by
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact
      (Set.disjoint_left.mp (cbLevel_disjoint_of_lt hij))
        hi hj
  · exact
      (Set.disjoint_left.mp (cbLevel_disjoint_of_lt hji))
        hj hi

/-- The unique finite Cantor--Bendixson level of a point. -/
noncomputable def levelOf
    {X : Set Language} {r : ℕ}
    (hr : FiniteRankAtMost X r) (L : Point X) : ℕ :=
  Classical.choose (exists_level_lt_of_finiteRankAtMost hr L)

theorem levelOf_lt
    {X : Set Language} {r : ℕ}
    (hr : FiniteRankAtMost X r) (L : Point X) :
    levelOf hr L < r :=
  (Classical.choose_spec
    (exists_level_lt_of_finiteRankAtMost hr L)).1

theorem mem_cbLevel_levelOf
    {X : Set Language} {r : ℕ}
    (hr : FiniteRankAtMost X r) (L : Point X) :
    L ∈ cbLevel X (levelOf hr L) :=
  (Classical.choose_spec
    (exists_level_lt_of_finiteRankAtMost hr L)).2

theorem levelOf_eq_of_mem_cbLevel
    {X : Set Language} {r i : ℕ}
    (hr : FiniteRankAtMost X r) (L : Point X)
    (hi : L ∈ cbLevel X i) :
    levelOf hr L = i :=
  cbLevel_index_unique (mem_cbLevel_levelOf hr L) hi

/-- An eligible parent is a strictly critical strict superset of the child
at a strictly higher finite Cantor--Bendixson level. -/
def ParentCandidate
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ) (child : RemainingPoint C stream round) (n : ℕ) : Prop :=
  StrictCritical C stream (round + 1) n ∧
    child.1.1 ⊂ C n ∧
      levelOf hr child.1 < levelOf hr (familyPoint C n)

def parentCandidateSet
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ) (child : RemainingPoint C stream round) : Set ℕ :=
  {n | ParentCandidate C stream r hr round child n}

/-- The paper's three-case parent-index selection, with paper round `t`
represented as Lean round `t - 1`. -/
noncomputable def parentIndexAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ) (child : RemainingPoint C stream round) : Option ℕ := by
  classical
  let S := parentCandidateSet C stream r hr round child
  exact if hfin : S.Finite then
    if hne : hfin.toFinset.Nonempty then
      some (hfin.toFinset.max' hne)
    else
      none
  else
    some (Nat.nth
      (ParentCandidate C stream r hr round child) round)

theorem parentIndexAt_of_finite
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ) (child : RemainingPoint C stream round)
    (hfin :
      (parentCandidateSet C stream r hr round child).Finite)
    (hne : hfin.toFinset.Nonempty) :
    parentIndexAt C stream r hr round child =
      some (hfin.toFinset.max' hne) := by
  classical
  simp [parentIndexAt, hfin, hne]

theorem parentIndexAt_of_infinite
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ) (child : RemainingPoint C stream round)
    (hinf :
      (parentCandidateSet C stream r hr round child).Infinite) :
    parentIndexAt C stream r hr round child =
      some (Nat.nth
        (ParentCandidate C stream r hr round child) round) := by
  classical
  unfold parentIndexAt
  dsimp only
  split
  next hfin =>
    exact (hinf hfin).elim
  next =>
    rfl

/-- Every selected parent index really is eligible. -/
theorem parentIndexAt_spec
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round n : ℕ} {child : RemainingPoint C stream round}
    (hn : parentIndexAt C stream r hr round child = some n) :
    ParentCandidate C stream r hr round child n := by
  classical
  unfold parentIndexAt at hn
  dsimp only at hn
  split at hn
  next hfin =>
    split at hn
    next hne =>
      have heq : hfin.toFinset.max' hne = n :=
        Option.some.inj hn
      rw [← heq]
      have hmem :=
        Finset.max'_mem hfin.toFinset hne
      simpa [parentCandidateSet] using hmem
    next hne =>
      simp at hn
  next hfin =>
    have heq :
        Nat.nth
          (ParentCandidate C stream r hr round child) round = n :=
      Option.some.inj hn
    rw [← heq]
    have hinf :
        (parentCandidateSet C stream r hr round child).Infinite :=
      hfin
    exact Nat.nth_mem_of_infinite
      (by simpa only [parentCandidateSet] using hinf) round

/-- In the finite branch, the selected language is inclusion-minimal among
all eligible parents. -/
theorem finite_parent_is_inclusion_minimum
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round n m : ℕ} {child : RemainingPoint C stream round}
    (hfin :
      (parentCandidateSet C stream r hr round child).Finite)
    (hne : hfin.toFinset.Nonempty)
    (hn : parentIndexAt C stream r hr round child = some n)
    (hm : ParentCandidate C stream r hr round child m) :
    C n ⊆ C m := by
  classical
  have hchoice :=
    parentIndexAt_of_finite C stream r hr round child hfin hne
  have hnmax : n = hfin.toFinset.max' hne :=
    Option.some.inj (hn.symm.trans hchoice)
  have hmMem : m ∈ hfin.toFinset := by
    simpa [parentCandidateSet] using hm
  have hmle : m ≤ hfin.toFinset.max' hne :=
    Finset.le_max' hfin.toFinset m hmMem
  have hselected := parentIndexAt_spec hn
  rw [hnmax] at hselected ⊢
  rcases eq_or_lt_of_le hmle with heq | hlt
  · simp [heq]
  · exact
      (strictCritical_ssubset_of_lt
        hlt hm.1 hselected.1).le

/-- Consecutive ranks in one fixed infinite candidate set form a strictly
descending inclusion chain.  This is a rank lemma, not a comparison between
candidate sets at two different temporal rounds. -/
theorem nth_candidate_languages_descend
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round rank : ℕ} {child : RemainingPoint C stream round}
    (hinf :
      (parentCandidateSet C stream r hr round child).Infinite) :
    C (Nat.nth
        (ParentCandidate C stream r hr round child) (rank + 1)) ⊂
      C (Nat.nth
        (ParentCandidate C stream r hr round child) rank) := by
  have hinf' :
      Set.Infinite
        {n | ParentCandidate C stream r hr round child n} := by
    simpa only [parentCandidateSet] using hinf
  have hlt :
      Nat.nth (ParentCandidate C stream r hr round child) rank <
        Nat.nth
          (ParentCandidate C stream r hr round child) (rank + 1) :=
    (Nat.nth_strictMono hinf') (Nat.lt_succ_self rank)
  have hrank :=
    Nat.nth_mem_of_infinite hinf' rank
  have hrank1 :=
    Nat.nth_mem_of_infinite hinf' (rank + 1)
  exact strictCritical_ssubset_of_lt hlt hrank.1 hrank1.1

/-- An infinite candidate set has no inclusion-minimum language.  Together
with `finite_parent_is_inclusion_minimum`, this justifies the source's
minimum/no-minimum case split by the implementation's finite/infinite split. -/
theorem infinite_candidates_have_no_inclusion_minimum
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} {child : RemainingPoint C stream round}
    (hinf :
      (parentCandidateSet C stream r hr round child).Infinite) :
    ¬ ∃ n,
        ParentCandidate C stream r hr round child n ∧
          ∀ m, ParentCandidate C stream r hr round child m →
            C n ⊆ C m := by
  rintro ⟨n, hn, hminimum⟩
  have hinf' :
      Set.Infinite
        {m | ParentCandidate C stream r hr round child m} := by
    simpa only [parentCandidateSet] using hinf
  let m :=
    Nat.nth (ParentCandidate C stream r hr round child) (n + 1)
  have hm : ParentCandidate C stream r hr round child m := by
    exact Nat.nth_mem_of_infinite hinf' (n + 1)
  have hnm : n < m := by
    have hle : n + 1 ≤ m := by
      exact Nat.le_nth (fun hfin => (hinf' hfin).elim)
    omega
  have hstrict : C m ⊂ C n :=
    strictCritical_ssubset_of_lt hnm hn.1 hm.1
  exact hstrict.ne
    (Set.Subset.antisymm hstrict.le (hminimum m hm))

/-- The optional ambient family point selected as parent. -/
noncomputable def parentAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ) (child : RemainingPoint C stream round) :
    Option (FamilyPoint C) :=
  (parentIndexAt C stream r hr round child).map (familyPoint C)

/-- Every selected parent is itself among the remaining languages. -/
theorem parentAt_remaining
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} {child : RemainingPoint C stream round}
    {parent : FamilyPoint C}
    (hparent : parentAt C stream r hr round child = some parent) :
    RemainingAt C stream round parent := by
  unfold parentAt at hparent
  rcases Option.map_eq_some_iff.mp hparent with
    ⟨n, hn, hpoint⟩
  have hcand := parentIndexAt_spec hn
  rw [← hpoint]
  exact hcand.1.1

/-- A directed edge on the remaining-vertex subtype points from a child to
its selected parent. -/
def EdgeAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ)
    (child parent : RemainingPoint C stream round) : Prop :=
  parentAt C stream r hr round child = some parent.1

/-- The edge invariant underlying Property 6.5. -/
theorem edge_strict_level_and_inclusion
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ}
    {child parent : RemainingPoint C stream round}
    (hEdge : EdgeAt C stream r hr round child parent) :
    levelOf hr child.1 < levelOf hr parent.1 ∧
      child.1.1 ⊂ parent.1.1 := by
  unfold EdgeAt parentAt at hEdge
  rcases Option.map_eq_some_iff.mp hEdge with
    ⟨n, hn, hpoint⟩
  have hcand := parentIndexAt_spec hn
  rw [← hpoint]
  exact ⟨hcand.2.2, hcand.2.1⟩

/-- Every remaining vertex has outdegree at most one. -/
theorem edge_outdegree_at_most_one
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ}
    {child parent₁ parent₂ : RemainingPoint C stream round}
    (h₁ : EdgeAt C stream r hr round child parent₁)
    (h₂ : EdgeAt C stream r hr round child parent₂) :
    parent₁ = parent₂ := by
  apply Subtype.ext
  exact Option.some.inj (h₁.symm.trans h₂)

/-- Levels strictly increase along every nonempty directed path. -/
theorem transGen_edge_level_lt
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ}
    {child ancestor : RemainingPoint C stream round}
    (hpath :
      Relation.TransGen (EdgeAt C stream r hr round)
        child ancestor) :
    levelOf hr child.1 < levelOf hr ancestor.1 := by
  induction hpath using Relation.TransGen.trans_induction_on with
  | single h =>
      exact (edge_strict_level_and_inclusion h).1
  | trans h₁ h₂ ih₁ ih₂ =>
      exact ih₁.trans ih₂

/-- The directed parent relation on remaining vertices is acyclic. -/
theorem edge_acyclic
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} :
    ∀ vertex : RemainingPoint C stream round,
      ¬ Relation.TransGen (EdgeAt C stream r hr round)
        vertex vertex := by
  intro vertex hcycle
  exact (Nat.lt_irrefl (levelOf hr vertex.1))
    (transGen_edge_level_lt hcycle)

end FiniteRankParent

/-- Property 6.5: every parent-forest edge goes from a strict sublanguage at
a lower level to a strict superlanguage at a higher level. -/
theorem property_6_5
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr :
      FiniteRankAtMost
        (FiniteRankParent.FamilySpace C) r}
    {round : ℕ}
    {child parent :
      FiniteRankParent.RemainingPoint C stream round}
    (hEdge :
      FiniteRankParent.EdgeAt C stream r hr round child parent) :
    FiniteRankParent.levelOf hr child.1 <
        FiniteRankParent.levelOf hr parent.1 ∧
      child.1.1 ⊂ parent.1.1 :=
  FiniteRankParent.edge_strict_level_and_inclusion hEdge

end DensityMeasures
end KleinbergWei
end GenLimit
