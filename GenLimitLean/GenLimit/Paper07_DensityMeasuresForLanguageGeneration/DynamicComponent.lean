import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.ParentForest
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.InfinitelyOften
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Finite-rank dynamic parent-forest components

This file gives a typed account of the paper's time-dependent forest
component `D_t^*`.  Edges point from child to parent; directed ancestry is
their reflexive-transitive closure, while weak connectivity is the
equivalence closure.

It also proves the fixed-round structural facts needed by the fallback
construction: parent paths are linearly ordered, finite rank makes every
ancestor set finite, connected vertices have an inclusion-minimum common
ancestor, purging persists through time, and the accurate selector
eventually names a remaining vertex.
-/

namespace GenLimit
namespace KleinbergWei
namespace DensityMeasures
namespace FiniteRankParent
open TowerTopology

/-- `ancestor` is an ancestor of `child`, allowing equality. -/
abbrev AncestorAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ)
    (child ancestor : RemainingPoint C stream round) : Prop :=
  Relation.ReflTransGen (EdgeAt C stream r hr round) child ancestor

/-- A nontrivial directed parent path. -/
abbrev ProperAncestorAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ)
    (child ancestor : RemainingPoint C stream round) : Prop :=
  Relation.TransGen (EdgeAt C stream r hr round) child ancestor

/-- `child` is a descendant of `ancestor`, allowing equality. -/
abbrev DescendantAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ)
    (ancestor child : RemainingPoint C stream round) : Prop :=
  AncestorAt C stream r hr round child ancestor

/-- Weak connectivity in the directed parent forest. -/
abbrev ConnectedAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ)
    (x y : RemainingPoint C stream round) : Prop :=
  Relation.EqvGen (EdgeAt C stream r hr round) x y

/-- The source's `D_t*`, centered at a chosen remaining language. -/
def ComponentAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ)
    (center : RemainingPoint C stream round) :
    Set (RemainingPoint C stream round) :=
  {vertex | ConnectedAt C stream r hr round center vertex}

theorem ancestorAt_refl
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} (vertex : RemainingPoint C stream round) :
    AncestorAt C stream r hr round vertex vertex :=
  Relation.ReflTransGen.refl

theorem edge_ancestorAt
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} {child parent : RemainingPoint C stream round}
    (hEdge : EdgeAt C stream r hr round child parent) :
    AncestorAt C stream r hr round child parent :=
  Relation.ReflTransGen.single hEdge

theorem ancestorAt_trans
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} {child middle ancestor : RemainingPoint C stream round}
    (h₁ : AncestorAt C stream r hr round child middle)
    (h₂ : AncestorAt C stream r hr round middle ancestor) :
    AncestorAt C stream r hr round child ancestor :=
  h₁.trans h₂

/-- Languages grow by inclusion along every directed parent path. -/
theorem ancestorAt_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} {child ancestor : RemainingPoint C stream round}
    (h : AncestorAt C stream r hr round child ancestor) :
    child.1.1 ⊆ ancestor.1.1 := by
  induction h with
  | refl =>
      exact Set.Subset.rfl
  | tail hpath hEdge ih =>
      exact ih.trans (edge_strict_level_and_inclusion hEdge).2.le

/-- A proper ancestor has both a strictly higher level and a strict
superlanguage. -/
theorem properAncestorAt_strict
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} {child ancestor : RemainingPoint C stream round}
    (h : ProperAncestorAt C stream r hr round child ancestor) :
    levelOf hr child.1 < levelOf hr ancestor.1 ∧
      child.1.1 ⊂ ancestor.1.1 := by
  refine ⟨transGen_edge_level_lt h, ?_⟩
  have hsub : child.1.1 ⊆ ancestor.1.1 :=
    ancestorAt_subset h.to_reflTransGen
  refine Set.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
  intro heq
  have hpoints : child.1 = ancestor.1 := Subtype.ext heq
  have hlevels :
      levelOf hr child.1 = levelOf hr ancestor.1 :=
    congrArg (levelOf hr) hpoints
  exact (Nat.ne_of_lt (transGen_edge_level_lt h)) hlevels

theorem ancestorAt_level_le
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} {child ancestor : RemainingPoint C stream round}
    (h : AncestorAt C stream r hr round child ancestor) :
    levelOf hr child.1 ≤ levelOf hr ancestor.1 := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h with hEq | hProper
  · subst ancestor
    exact le_rfl
  · exact (transGen_edge_level_lt hProper).le

/-- Ambient ancestry hides the proofs that both endpoints remain at this
round.  This is convenient for statements comparing languages across rounds. -/
def IsAncestorAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ) (child ancestor : FamilyPoint C) : Prop :=
  ∃ (hchild : RemainingAt C stream round child)
      (hancestor : RemainingAt C stream round ancestor),
    AncestorAt C stream r hr round
      ⟨child, hchild⟩ ⟨ancestor, hancestor⟩

/-- Ambient descendant relation, with the source's argument order. -/
def IsDescendantAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ) (ancestor child : FamilyPoint C) : Prop :=
  IsAncestorAt C stream r hr round child ancestor

theorem isAncestorAt_endpoints_remaining
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} {child ancestor : FamilyPoint C}
    (h : IsAncestorAt C stream r hr round child ancestor) :
    RemainingAt C stream round child ∧
      RemainingAt C stream round ancestor := by
  rcases h with ⟨hchild, hancestor, _⟩
  exact ⟨hchild, hancestor⟩

theorem isAncestorAt_subset
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} {child ancestor : FamilyPoint C}
    (h : IsAncestorAt C stream r hr round child ancestor) :
    child.1 ⊆ ancestor.1 := by
  rcases h with ⟨hchild, hancestor, hpath⟩
  exact ancestorAt_subset
    (child := ⟨child, hchild⟩)
    (ancestor := ⟨ancestor, hancestor⟩) hpath

/-- A parent forest is locally confluent because every vertex has at most one
outgoing edge. -/
theorem edge_local_confluent
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ}
    {a b c : RemainingPoint C stream round}
    (hab : EdgeAt C stream r hr round a b)
    (hac : EdgeAt C stream r hr round a c) :
    ∃ d,
      Relation.ReflGen (EdgeAt C stream r hr round) b d ∧
        Relation.ReflTransGen (EdgeAt C stream r hr round) c d := by
  have hbc : b = c := edge_outdegree_at_most_one hab hac
  subst c
  exact ⟨b, Relation.ReflGen.refl, Relation.ReflTransGen.refl⟩

/-- Two vertices are in one tree exactly when their parent paths meet. -/
theorem connectedAt_iff_exists_commonAncestor
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} {x y : RemainingPoint C stream round} :
    ConnectedAt C stream r hr round x y ↔
      ∃ common,
        AncestorAt C stream r hr round x common ∧
          AncestorAt C stream r hr round y common := by
  let E := EdgeAt C stream r hr round
  let J := Relation.Join (Relation.ReflTransGen E)
  have hJE : Equivalence J :=
    Relation.equivalence_join_reflTransGen
      (r := E) (fun _ _ _ hab hac =>
        edge_local_confluent hab hac)
  constructor
  · intro hxy
    apply hJE.eqvGen_iff.mp
    exact Relation.EqvGen.mono
      (fun a b hab =>
        ⟨b, Relation.ReflTransGen.single hab,
          Relation.ReflTransGen.refl⟩) hxy
  · rintro ⟨common, hxc, hyc⟩
    have hEqv :
        Equivalence (Relation.EqvGen E) :=
      Relation.EqvGen.is_equivalence E
    have liftPath :
        ∀ {a b}, Relation.ReflTransGen E a b →
          Relation.EqvGen E a b := by
      intro a b hab
      exact Relation.reflTransGen_of_equivalence hEqv
        (fun u v huv => Relation.EqvGen.rel u v huv) hab
    exact hEqv.trans (liftPath hxc) (hEqv.symm (liftPath hyc))

theorem mem_componentAt_iff_exists_commonAncestor
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} {center vertex : RemainingPoint C stream round} :
    vertex ∈ ComponentAt C stream r hr round center ↔
      ∃ common,
        AncestorAt C stream r hr round center common ∧
          AncestorAt C stream r hr round vertex common :=
  connectedAt_iff_exists_commonAncestor

/-- Parent paths from one child are linearly ordered because the parent
relation has functional outdegree. -/
theorem ancestors_comparable
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} {child a b : RemainingPoint C stream round}
    (ha : AncestorAt C stream r hr round child a)
    (hb : AncestorAt C stream r hr round child b) :
    AncestorAt C stream r hr round a b ∨
      AncestorAt C stream r hr round b a := by
  exact Relation.ReflTransGen.total_of_right_unique
    (fun _ _ _ h₁ h₂ => edge_outdegree_at_most_one h₁ h₂)
    ha hb

/-- The ancestors of one remaining language at a fixed round. -/
def ancestorSet
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ) (child : RemainingPoint C stream round) :
    Set (RemainingPoint C stream round) :=
  {ancestor | AncestorAt C stream r hr round child ancestor}

theorem ancestor_level_injective
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} {child : RemainingPoint C stream round} :
    Set.InjOn (fun a => levelOf hr a.1)
      (ancestorSet C stream r hr round child) := by
  intro a ha b hb hlevel
  rcases ancestors_comparable ha hb with hab | hba
  · rcases Relation.reflTransGen_iff_eq_or_transGen.mp hab with
      heq | hpath
    · exact heq.symm
    · exact False.elim
        ((transGen_edge_level_lt hpath).ne hlevel)
  · rcases Relation.reflTransGen_iff_eq_or_transGen.mp hba with
      heq | hpath
    · exact heq
    · exact False.elim
        ((transGen_edge_level_lt hpath).ne hlevel.symm)

/-- A finite-rank parent path has only finitely many ancestors. -/
theorem ancestorSet_finite
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} (child : RemainingPoint C stream round) :
    (ancestorSet C stream r hr round child).Finite := by
  apply Set.Finite.of_finite_image
  · apply (Set.finite_Iio r).subset
    rintro n ⟨ancestor, -, rfl⟩
    exact levelOf_lt hr ancestor.1
  · exact ancestor_level_injective

/-- Common ancestors of two remaining languages. -/
def commonAncestorSet
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ) (a b : RemainingPoint C stream round) :
    Set (RemainingPoint C stream round) :=
  ancestorSet C stream r hr round a ∩
    ancestorSet C stream r hr round b

theorem commonAncestorSet_finite
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} (a b : RemainingPoint C stream round) :
    (commonAncestorSet C stream r hr round a b).Finite :=
  (ancestorSet_finite a).inter_of_left _

/-- Whenever a common ancestor exists, there is an inclusion-minimum common
ancestor.  This is the finite-rank existence assertion used by the source's
fallback algorithm. -/
theorem exists_inclusion_minimum_commonAncestor
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} {a b : RemainingPoint C stream round}
    (hne :
      (commonAncestorSet C stream r hr round a b).Nonempty) :
    ∃ z,
      z ∈ commonAncestorSet C stream r hr round a b ∧
        ∀ w,
          w ∈ commonAncestorSet C stream r hr round a b →
            z.1.1 ⊆ w.1.1 := by
  obtain ⟨z, hz, hzmin⟩ :=
    Set.exists_min_image
      (commonAncestorSet C stream r hr round a b)
      (fun x => levelOf hr x.1)
      (commonAncestorSet_finite a b) hne
  refine ⟨z, hz, ?_⟩
  intro w hw
  rcases ancestors_comparable hz.1 hw.1 with hzw | hwz
  · exact ancestorAt_subset hzw
  · have hle := ancestorAt_level_le hwz
    have heqLevel :
        levelOf hr z.1 = levelOf hr w.1 :=
      Nat.le_antisymm (hzmin w hw) hle
    have heq : z = w :=
      ancestor_level_injective hz.1 hw.1 heqLevel
    simp [heq]

theorem exists_inclusion_minimum_commonAncestor_of_connected
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ} {a b : RemainingPoint C stream round}
    (hconnected : ConnectedAt C stream r hr round a b) :
    ∃ z,
      z ∈ commonAncestorSet C stream r hr round a b ∧
        ∀ w,
          w ∈ commonAncestorSet C stream r hr round a b →
            z.1.1 ⊆ w.1.1 := by
  obtain ⟨common, ha, hb⟩ :=
    connectedAt_iff_exists_commonAncestor.mp hconnected
  exact exists_inclusion_minimum_commonAncestor
    ⟨common, ha, hb⟩

/-- One eligible candidate is enough to ensure that the optional parent
selector returns an index. -/
theorem parentIndexAt_exists_of_candidate
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round m : ℕ} {child : RemainingPoint C stream round}
    (hm : ParentCandidate C stream r hr round child m) :
    ∃ n, parentIndexAt C stream r hr round child = some n := by
  classical
  let S := parentCandidateSet C stream r hr round child
  by_cases hfin : S.Finite
  · have hmMem : m ∈ hfin.toFinset := by
      simpa [S, parentCandidateSet] using hm
    have hne : hfin.toFinset.Nonempty := ⟨m, hmMem⟩
    exact
      ⟨hfin.toFinset.max' hne,
        parentIndexAt_of_finite
          C stream r hr round child hfin hne⟩
  · have hinf : S.Infinite := hfin
    exact
      ⟨Nat.nth
          (ParentCandidate C stream r hr round child) round,
        parentIndexAt_of_infinite
          C stream r hr round child hinf⟩

/-- If candidate `m` occurs no later than the current paper round, every
selected parent language is contained in candidate `m`.

In the finite branch this is inclusion-minimality.  In the infinite branch,
the selected `round`-th candidate has family index at least `round`, while
strictly critical languages descend as their family indices increase. -/
theorem selected_parent_subset_candidate
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round m n : ℕ} {child : RemainingPoint C stream round}
    (hmround : m ≤ round)
    (hm : ParentCandidate C stream r hr round child m)
    (hn : parentIndexAt C stream r hr round child = some n) :
    C n ⊆ C m := by
  classical
  let S := parentCandidateSet C stream r hr round child
  by_cases hfin : S.Finite
  · have hmMem : m ∈ hfin.toFinset := by
      simpa [S, parentCandidateSet] using hm
    have hne : hfin.toFinset.Nonempty := ⟨m, hmMem⟩
    exact
      finite_parent_is_inclusion_minimum
        hfin hne hn hm
  · have hinf : S.Infinite := hfin
    have hchoice :=
      parentIndexAt_of_infinite
        C stream r hr round child hinf
    have hnNth :
        n =
          Nat.nth
            (ParentCandidate C stream r hr round child) round :=
      Option.some.inj (hn.symm.trans hchoice)
    have hinf' :
        Set.Infinite
          {k | ParentCandidate C stream r hr round child k} := by
      simpa [S, parentCandidateSet] using hinf
    have hroundNth :
        round ≤
      Nat.nth
            (ParentCandidate C stream r hr round child) round :=
      Nat.le_nth (fun hfinite => (hinf' hfinite).elim)
    have hmn : m ≤ n := by
      rw [hnNth]
      exact hmround.trans hroundNth
    have hselected := parentIndexAt_spec hn
    rcases eq_or_lt_of_le hmn with hEq | hlt
    · simp [hEq]
    · exact
        (strictCritical_ssubset_of_lt
          hlt hm.1 hselected.1).le

/-- An eligible candidate at an index already reached by the paper round
produces an actual parent edge whose language is contained in that candidate. -/
theorem exists_parent_edge_subset_candidate
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round m : ℕ} {child : RemainingPoint C stream round}
    (hmround : m ≤ round)
    (hm : ParentCandidate C stream r hr round child m) :
    ∃ parent : RemainingPoint C stream round,
      EdgeAt C stream r hr round child parent ∧
        parent.1.1 ⊆ C m := by
  obtain ⟨n, hn⟩ := parentIndexAt_exists_of_candidate hm
  have hparent :
      parentAt C stream r hr round child =
        some (familyPoint C n) := by
    simp [parentAt, hn]
  have hremaining :
      RemainingAt C stream round (familyPoint C n) :=
    parentAt_remaining hparent
  let parent : RemainingPoint C stream round :=
    ⟨familyPoint C n, hremaining⟩
  refine ⟨parent, ?_, ?_⟩
  · exact hparent
  · simpa [parent] using
      selected_parent_subset_candidate hmround hm hn

/-- A language is purged once it fails consistency with the observations at
this round. -/
def PurgedAt
    (C : LanguageFamily) (stream : ℕ → ℕ)
    (round : ℕ) (L : FamilyPoint C) : Prop :=
  ¬ RemainingAt C stream round L

theorem remainingAt_of_later
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {s t : ℕ} {L : FamilyPoint C}
    (hst : s ≤ t) (hL : RemainingAt C stream t L) :
    RemainingAt C stream s L := by
  intro u hu
  exact hL (sample_mono (Nat.succ_le_succ hst) hu)

theorem purgedAt_mono
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {s t : ℕ} {L : FamilyPoint C}
    (hst : s ≤ t) (hL : PurgedAt C stream s L) :
    PurgedAt C stream t L := by
  intro hremain
  exact hL (remainingAt_of_later hst hremain)

theorem purgedAt_iff_exists_missing
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {round : ℕ} {L : FamilyPoint C} :
    PurgedAt C stream round L ↔
      ∃ u, u ∈ sample stream (round + 1) ∧ u ∉ L.1 := by
  rw [PurgedAt, RemainingAt]
  exact Set.not_subset

/-- Purging a language purges every fixed sublanguage at the same round. -/
theorem purgedAt_of_subset
    {C : LanguageFamily} {stream : ℕ → ℕ}
    {round : ℕ} {child parent : FamilyPoint C}
    (hsub : child.1 ⊆ parent.1)
    (hparent : PurgedAt C stream round parent) :
    PurgedAt C stream round child := by
  intro hchild
  exact hparent (hchild.trans hsub)

/-- Purging an ambient language at any round also purges every fixed
sublanguage that occurs below it along a parent path at any forest round. -/
theorem descendant_purged_with_ancestor
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {oldRound newRound : ℕ} {ancestor child : FamilyPoint C}
    (hdesc :
      IsDescendantAt C stream r hr oldRound ancestor child)
    (hpurged : PurgedAt C stream newRound ancestor) :
    PurgedAt C stream newRound child :=
  purgedAt_of_subset (isAncestorAt_subset hdesc) hpurged

/-- The language identified by the Section 3 semantic selector after the
`round + 1`-st observation. -/
def identifiedPointAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (round : ℕ) :
    FamilyPoint C :=
  familyPoint C (guessIndex C stream (round + 1))

/-- In the stable-target regime, the Section 3 selector contains the newly
observed value.  This fact is implicit in `selectIndex_spec` but is needed to
put the selector's output into the post-observation forest. -/
theorem selectIndex_mem_of_stable_target
    {C : LanguageFamily} {stream : ℕ → ℕ} {t w z : ℕ}
    (hzt : z ≤ t)
    (hz : StrictCritical C stream t z)
    (hw : w ∈ C z) :
    w ∈ C (selectIndex C stream t w) := by
  classical
  by_cases hall : ∀ n, StrictCritical C stream t n → w ∈ C n
  · have hfocus := scopedFocus_spec hzt hz
    have hselect :
        selectIndex C stream t w = scopedFocus C stream t := by
      rw [selectIndex]
      simp only [dif_pos hall]
    rw [hselect]
    exact hall _ hfocus.2.1
  · have hbad : ∃ n, BadStrictCritical C stream t w n := by
      simpa [BadStrictCritical] using hall
    let b := firstBadStrictCritical C stream t w
    have hb := firstBadStrictCritical_spec hbad
    have hzb : z < b := by
      have hle : z ≤ b := by
        by_contra hnot
        have hbz : b < z := Nat.lt_of_not_ge hnot
        have hsub : C z ⊆ C b :=
          (strictCritical_ssubset_of_lt hbz hb.1 hz).le
        exact hb.2 (hsub hw)
      exact lt_of_le_of_ne hle
        (fun heq => hb.2 (by simpa [heq] using hw))
    let S := boundaryCandidates C stream t w
    have hzS : z ∈ S := by
      simpa [S, b] using
        mem_boundaryCandidates.mpr ⟨hzb, hz, hw⟩
    have hne : S.Nonempty := ⟨z, hzS⟩
    have hselect : selectIndex C stream t w = S.max' hne := by
      rw [selectIndex]
      simp only [dif_neg hall]
      simp [S, hne]
    rw [hselect]
    have hmax : S.max' hne ∈ S := Finset.max'_mem S hne
    exact
      (mem_boundaryCandidates.mp (by simpa [S] using hmax)).2.2

/-- Under the stable-target hypotheses, the identified language is a vertex
of the post-observation forest. -/
theorem identifiedPointAt_remaining_of_stable_target
    {C : LanguageFamily} {stream : ℕ → ℕ} {round z : ℕ}
    (hzround : z ≤ round)
    (hz : StrictCritical C stream round z)
    (hw : stream round ∈ C z) :
    RemainingAt C stream round
      (identifiedPointAt C stream round) := by
  let selected := selectIndex C stream round (stream round)
  have hselected :=
    selectIndex_spec hzround hz hw
  have hnew :
      stream round ∈ C selected :=
    selectIndex_mem_of_stable_target hzround hz hw
  have hconsistent :
      Consistent C stream (round + 1) selected := by
    intro u hu
    change u ∈ sample stream (round + 1) at hu
    rw [mem_sample_iff] at hu
    obtain ⟨q, hq, rfl⟩ := hu
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hlt | rfl
    · exact hselected.1.1 (value_mem_sample hlt)
    · exact hnew
  simpa [RemainingAt, identifiedPointAt, guessIndex, selected] using
    hconsistent

/-- Along an exact target presentation, the identified language eventually
is a vertex of every post-observation forest. -/
theorem identifiedPointAt_eventually_remaining
    {C : LanguageFamily} {stream : ℕ → ℕ} {z : ℕ}
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    ∃ T, ∀ round, T ≤ round →
      RemainingAt C stream round
        (identifiedPointAt C stream round) := by
  obtain ⟨Tcrit, hcrit⟩ := lemma_3_3 hP hfirst
  refine ⟨max Tcrit z, ?_⟩
  intro round hround
  have hTcrit : Tcrit ≤ round :=
    le_trans (Nat.le_max_left _ _) hround
  have hzround : z ≤ round :=
    le_trans (Nat.le_max_right _ _) hround
  have hw : stream round ∈ C z := by
    rw [← hP]
    exact ⟨round, rfl⟩
  exact identifiedPointAt_remaining_of_stable_target
    hzround (hcrit round hTcrit) hw

/-- An exact ambient version of the source's dynamic component `D_t*`.
It is empty at an early round where the semantic focus is not remaining; in
the stable source regime the center proof exists and this is exactly
`ComponentAt` transported out of the remaining-language subtype. -/
def IdentifiedComponentAt
    (C : LanguageFamily) (stream : ℕ → ℕ) (r : ℕ)
    (hr : FiniteRankAtMost (FamilySpace C) r)
    (round : ℕ) : Set (FamilyPoint C) :=
  {vertex |
    ∃ (hcenter :
          RemainingAt C stream round
            (identifiedPointAt C stream round))
      (hvertex : RemainingAt C stream round vertex),
      ConnectedAt C stream r hr round
        ⟨identifiedPointAt C stream round, hcenter⟩
        ⟨vertex, hvertex⟩}

theorem identifiedPoint_mem_identifiedComponentAt
    {C : LanguageFamily} {stream : ℕ → ℕ} {r : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    {round : ℕ}
    (hremaining :
      RemainingAt C stream round
        (identifiedPointAt C stream round)) :
    identifiedPointAt C stream round ∈
      IdentifiedComponentAt C stream r hr round :=
  ⟨hremaining, hremaining, Relation.EqvGen.refl _⟩

/-- The source component `D_t*` is eventually nonempty. -/
theorem identifiedComponentAt_eventually_nonempty
    {C : LanguageFamily} {stream : ℕ → ℕ} {r z : ℕ}
    {hr : FiniteRankAtMost (FamilySpace C) r}
    (hP : Presents stream (C z))
    (hfirst : FirstOccurrence C z) :
    ∃ T, ∀ round, T ≤ round →
      (IdentifiedComponentAt C stream r hr round).Nonempty := by
  obtain ⟨T, hT⟩ :=
    identifiedPointAt_eventually_remaining hP hfirst
  refine ⟨T, ?_⟩
  intro round hround
  exact
    ⟨identifiedPointAt C stream round,
      identifiedPoint_mem_identifiedComponentAt (hT round hround)⟩

end FiniteRankParent
end DensityMeasures
end KleinbergWei
end GenLimit
