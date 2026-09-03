import GenLimit.Paper27_FeedbackQueriesAndMistakes.SourceQuery
import GenLimit.Support.Fresh
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Source Theorem 3.3: element/set separation under query feedback

This file formalizes Appendix A.2.2 of Hanneke--Karbasi--Mehrotra--
Velegkas, *Language Generation with Feedback: Queries and Mistakes*.

The paper partitions the positive natural numbers into consecutive triples
`{3j - 2, 3j - 1, 3j}`.  Lean uses the equivalent zero-based partition
encoded by `Nat.divModEquiv 3`: a point has a block index in `ℕ` and a
position in `Fin 3`.  In each block a bit chooses either positions zero and
one (the pair) or position two (the singleton).

The positive direction gives a source-timed element generator one membership
query per round.  It queries position zero in a block beyond every observed
block and emits position one after a positive answer or position two after a
negative answer.  The negative direction diagonalizes against every proposed
countable inner cover, then invokes the already formalized Theorem 3.4.
-/

namespace GenLimit.FeedbackQueries

open GenLimit.Generic

/-! ## Definition 2 for element-valued query generation -/

/-- Definition 2's source-timed element-valued query strategy.  At Lean round
`t` it sees `t + 1` positive examples, receives `t` previous answers, asks one
membership query, and emits after the current answer has been appended. -/
structure SourceElementQueryStrategy (α : Type*) where
  query : SourceQueryPolicy α
  output : ∀ t, (Fin (t + 1) → α) → List Bool → α

/-- Truthful query feedback before paper round `t + 1`. -/
noncomputable def sourceElementQueryFeedback
    (strategy : SourceElementQueryStrategy α)
    (target : Set α) (stream : Stream α) : ℕ → List Bool :=
  sourceQueryFeedback strategy.query target stream

@[simp] theorem sourceElementQueryFeedback_zero
    (strategy : SourceElementQueryStrategy α)
    (target : Set α) (stream : Stream α) :
    sourceElementQueryFeedback strategy target stream 0 = [] :=
  sourceQueryFeedback_zero strategy.query target stream

@[simp] theorem sourceElementQueryFeedback_succ
    (strategy : SourceElementQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    sourceElementQueryFeedback strategy target stream (t + 1) =
      sourceElementQueryFeedback strategy target stream t ++
        [membershipAnswer target
          (strategy.query t (fun i => stream i)
            (sourceElementQueryFeedback strategy target stream t))] :=
  sourceQueryFeedback_succ strategy.query target stream t

@[simp] theorem sourceElementQueryFeedback_length
    (strategy : SourceElementQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) :
    (sourceElementQueryFeedback strategy target stream t).length = t := by
  exact sourceQueryFeedback_length strategy.query target stream t

/-- The element emitted in paper round `t + 1`, after the current query
answer is available. -/
noncomputable def sourceElementQueryOutput
    (strategy : SourceElementQueryStrategy α)
    (target : Set α) (stream : Stream α) (t : ℕ) : α :=
  strategy.output t (fun i => stream i)
    (sourceElementQueryFeedback strategy target stream (t + 1))

/-- Definition 2 success for an element-valued query generator. -/
def SourceElementQuerySucceedsOn
    (strategy : SourceElementQueryStrategy α)
    (target : Set α) : Prop :=
  ∀ stream : Stream α, Generic.Presents stream target →
    ∃ T, ∀ t, T ≤ t →
      sourceElementQueryOutput strategy target stream t ∈
        target \ (Generic.sample stream (t + 1) : Set α)

def SourceElementQueryGenerates
    (strategy : SourceElementQueryStrategy α)
    (targets : LanguageClass α) : Prop :=
  ∀ target, target ∈ targets → SourceElementQuerySucceedsOn strategy target

def SourceElementQueryGeneratable
    (targets : LanguageClass α) : Prop :=
  ∃ strategy : SourceElementQueryStrategy α,
    SourceElementQueryGenerates strategy targets

/-! ## The paper's three-point block class on `ℕ` -/

/-- The canonical zero-based decomposition of `ℕ` into triples. -/
def threePointEquiv : ℕ ≃ ℕ × Fin 3 :=
  Nat.divModEquiv 3

/-- The zero-based block containing a natural number. -/
def threePointBlockIndex (x : ℕ) : ℕ :=
  (threePointEquiv x).1

/-- The position of a natural number inside its three-point block. -/
def threePointBlockPosition (x : ℕ) : Fin 3 :=
  (threePointEquiv x).2

/-- Encode a block index and one of its three positions as a natural number. -/
def threePointBlockPoint (j : ℕ) (k : Fin 3) : ℕ :=
  threePointEquiv.symm (j, k)

@[simp] theorem threePointBlockIndex_point (j : ℕ) (k : Fin 3) :
    threePointBlockIndex (threePointBlockPoint j k) = j := by
  change (threePointEquiv (threePointEquiv.symm (j, k))).1 = j
  rw [threePointEquiv.apply_symm_apply]

@[simp] theorem threePointBlockPosition_point (j : ℕ) (k : Fin 3) :
    threePointBlockPosition (threePointBlockPoint j k) = k := by
  change (threePointEquiv (threePointEquiv.symm (j, k))).2 = k
  rw [threePointEquiv.apply_symm_apply]

@[simp] theorem threePointBlockPoint_index_position (x : ℕ) :
    threePointBlockPoint (threePointBlockIndex x)
      (threePointBlockPosition x) = x := by
  exact threePointEquiv.symm_apply_apply x

/-- The language selected by a bit sequence.  A true bit contributes the
first two points of its block; a false bit contributes only the last point. -/
def threePointLanguage (σ : ℕ → Bool) : Set ℕ :=
  {x | if σ (threePointBlockIndex x) = true then
      threePointBlockPosition x ≠ (2 : Fin 3)
    else
      threePointBlockPosition x = (2 : Fin 3)}

/-- The explicit class used in source Theorem 3.3. -/
def threePointLanguageClass : LanguageClass ℕ :=
  Set.range threePointLanguage

@[simp] theorem threePoint_indicator_mem_iff
    (σ : ℕ → Bool) (j : ℕ) :
    threePointBlockPoint j 0 ∈ threePointLanguage σ ↔ σ j = true := by
  cases hσ : σ j <;> simp [threePointLanguage, hσ]

@[simp] theorem threePoint_pairOutput_mem_iff
    (σ : ℕ → Bool) (j : ℕ) :
    threePointBlockPoint j 1 ∈ threePointLanguage σ ↔ σ j = true := by
  cases hσ : σ j <;> simp [threePointLanguage, hσ]

@[simp] theorem threePoint_singletonOutput_mem_iff
    (σ : ℕ → Bool) (j : ℕ) :
    threePointBlockPoint j 2 ∈ threePointLanguage σ ↔ σ j = false := by
  cases hσ : σ j <;> simp [threePointLanguage, hσ]

/-- One canonical member from every block. -/
def threePointRepresentative (σ : ℕ → Bool) (j : ℕ) : ℕ :=
  if σ j = true then threePointBlockPoint j 0
  else threePointBlockPoint j 2

theorem threePointRepresentative_mem
    (σ : ℕ → Bool) (j : ℕ) :
    threePointRepresentative σ j ∈ threePointLanguage σ := by
  cases hσ : σ j <;>
    simp [threePointRepresentative, hσ]

theorem threePointRepresentative_injective
    (σ : ℕ → Bool) :
    Function.Injective (threePointRepresentative σ) := by
  intro i j hij
  have hblocks := congrArg threePointBlockIndex hij
  cases hσi : σ i <;> cases hσj : σ j <;>
    simpa [threePointRepresentative, hσi, hσj] using hblocks

theorem threePointLanguage_infinite (σ : ℕ → Bool) :
    (threePointLanguage σ).Infinite := by
  apply (Set.infinite_range_of_injective
    (threePointRepresentative_injective σ)).mono
  rintro x ⟨j, rfl⟩
  exact threePointRepresentative_mem σ j

theorem threePointLanguageClass_all_infinite :
    ∀ L, L ∈ threePointLanguageClass → L.Infinite := by
  rintro L ⟨σ, rfl⟩
  exact threePointLanguage_infinite σ

/-! ## Step 1: one query certifies one fresh element -/

/-- A block strictly beyond every block represented in the current positive
history.  This proof-equivalent choice is simpler than storing the largest
previously queried block; Definition 2 does not require queries to be fresh. -/
noncomputable def threePointFreshBlock
    {t : ℕ} (samples : Fin (t + 1) → ℕ) : ℕ :=
  Nat.succ (Finset.univ.sup (fun i => threePointBlockIndex (samples i)))

theorem sample_block_lt_threePointFreshBlock
    {t : ℕ} (samples : Fin (t + 1) → ℕ) (i : Fin (t + 1)) :
    threePointBlockIndex (samples i) < threePointFreshBlock samples := by
  exact Nat.lt_succ_of_le
    (Finset.le_sup (f := fun k => threePointBlockIndex (samples k))
      (Finset.mem_univ i))

/-- The source construction: query the indicator of a wholly unseen block,
then emit the other pair member or the singleton member according to the
current answer. -/
noncomputable def threePointElementQueryStrategy :
    SourceElementQueryStrategy ℕ where
  query := fun _ samples _ =>
    threePointBlockPoint (threePointFreshBlock samples) 0
  output := fun _ samples answers =>
    if answers.getLast? = some true then
      threePointBlockPoint (threePointFreshBlock samples) 1
    else
      threePointBlockPoint (threePointFreshBlock samples) 2

theorem membershipAnswer_threePoint_indicator
    (σ : ℕ → Bool) (j : ℕ) :
    membershipAnswer (threePointLanguage σ)
      (threePointBlockPoint j 0) = σ j := by
  classical
  cases hσ : σ j <;>
    simp [membershipAnswer, threePointLanguage, hσ]

theorem threePointElementQueryOutput_eq
    (σ : ℕ → Bool) (stream : Stream ℕ) (t : ℕ) :
    sourceElementQueryOutput threePointElementQueryStrategy
        (threePointLanguage σ) stream t =
      if σ (threePointFreshBlock (fun i : Fin (t + 1) => stream i)) = true then
        threePointBlockPoint
          (threePointFreshBlock (fun i : Fin (t + 1) => stream i)) 1
      else
        threePointBlockPoint
          (threePointFreshBlock (fun i : Fin (t + 1) => stream i)) 2 := by
  simp only [sourceElementQueryOutput, sourceElementQueryFeedback_succ]
  rw [show membershipAnswer (threePointLanguage σ)
      (threePointElementQueryStrategy.query t (fun i => stream i)
        (sourceElementQueryFeedback threePointElementQueryStrategy
          (threePointLanguage σ) stream t)) =
      σ (threePointFreshBlock (fun i : Fin (t + 1) => stream i)) by
    exact membershipAnswer_threePoint_indicator _ _]
  cases hσ : σ (threePointFreshBlock
      (fun i : Fin (t + 1) => stream i)) <;>
    simp [threePointElementQueryStrategy]

theorem threePointBlockPoint_fresh
    (stream : Stream ℕ) (t : ℕ) (k : Fin 3) :
    threePointBlockPoint
        (threePointFreshBlock (fun i : Fin (t + 1) => stream i)) k ∉
      Generic.sample stream (t + 1) := by
  intro hmem
  obtain ⟨s, hs, hvalue⟩ := Generic.mem_sample_iff.mp hmem
  let i : Fin (t + 1) := ⟨s, hs⟩
  have hlt : threePointBlockIndex (stream s) <
      threePointFreshBlock (fun q : Fin (t + 1) => stream q) := by
    simpa [i] using sample_block_lt_threePointFreshBlock
      (fun q : Fin (t + 1) => stream q) i
  have hblocks : threePointBlockIndex (stream s) =
      threePointFreshBlock (fun q : Fin (t + 1) => stream q) := by
    calc
      threePointBlockIndex (stream s) =
          threePointBlockIndex
            (threePointBlockPoint
              (threePointFreshBlock (fun q : Fin (t + 1) => stream q)) k) :=
        congrArg threePointBlockIndex hvalue
      _ = threePointFreshBlock (fun q : Fin (t + 1) => stream q) := by
        simp
  omega

theorem threePointElementQueryStrategy_generates :
    SourceElementQueryGenerates threePointElementQueryStrategy
      threePointLanguageClass := by
  rintro L ⟨σ, rfl⟩ stream _hpresents
  refine ⟨0, ?_⟩
  intro t _ht
  rw [threePointElementQueryOutput_eq]
  constructor
  · cases hσ : σ (threePointFreshBlock
        (fun i : Fin (t + 1) => stream i)) <;>
      simp [hσ]
  · split_ifs
    · exact threePointBlockPoint_fresh stream t 1
    · exact threePointBlockPoint_fresh stream t 2

theorem threePointLanguageClass_sourceElementQueryGeneratable :
    SourceElementQueryGeneratable threePointLanguageClass :=
  ⟨threePointElementQueryStrategy,
    threePointElementQueryStrategy_generates⟩

/-! ## Step 2: no countable inner cover -/

/-- All points in the finitely many block indices already used by the
diagonal construction. -/
def threePointForbiddenBlocks (used : Finset ℕ) : Finset ℕ :=
  (used.product (Finset.univ : Finset (Fin 3))).map
    threePointEquiv.symm.toEmbedding

theorem mem_threePointForbiddenBlocks_iff
    {used : Finset ℕ} {x : ℕ} :
    x ∈ threePointForbiddenBlocks used ↔
      threePointBlockIndex x ∈ used := by
  classical
  constructor
  · intro hx
    obtain ⟨p, hp, hpx⟩ := Finset.mem_map.mp hx
    have hpused := (Finset.mem_product.mp hp).1
    rw [← hpx]
    have hindex : threePointBlockIndex (threePointEquiv.symm p) = p.1 := by
      change (threePointEquiv (threePointEquiv.symm p)).1 = p.1
      rw [threePointEquiv.apply_symm_apply]
    change threePointBlockIndex (threePointEquiv.symm p) ∈ used
    rw [hindex]
    exact hpused
  · intro hx
    apply Finset.mem_map.mpr
    refine ⟨threePointEquiv x, ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨hx, Finset.mem_univ _⟩
    · exact threePointEquiv.symm_apply_apply x

/-- The finite set of block indices already assigned before diagonal stage
`n`. -/
noncomputable def threePointDiagonalUsedBlocks
    {targets : LanguageClass ℕ}
    (inner : CountableInnerCover targets) : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 =>
      let point := GenLimit.Support.freshFromInfinite
        (inner.cover n) (inner.infinite_cover n)
        (threePointForbiddenBlocks (threePointDiagonalUsedBlocks inner n))
      insert (threePointBlockIndex point)
        (threePointDiagonalUsedBlocks inner n)

/-- The point chosen from cover member `n` outside all previously assigned
blocks. -/
noncomputable def threePointDiagonalPoint
    {targets : LanguageClass ℕ}
    (inner : CountableInnerCover targets) (n : ℕ) : ℕ :=
  GenLimit.Support.freshFromInfinite
    (inner.cover n) (inner.infinite_cover n)
    (threePointForbiddenBlocks (threePointDiagonalUsedBlocks inner n))

@[simp] theorem threePointDiagonalUsedBlocks_succ
    {targets : LanguageClass ℕ}
    (inner : CountableInnerCover targets) (n : ℕ) :
    threePointDiagonalUsedBlocks inner (n + 1) =
      insert (threePointBlockIndex (threePointDiagonalPoint inner n))
        (threePointDiagonalUsedBlocks inner n) := by
  simp [threePointDiagonalUsedBlocks, threePointDiagonalPoint]

theorem threePointDiagonalPoint_mem
    {targets : LanguageClass ℕ}
    (inner : CountableInnerCover targets) (n : ℕ) :
    threePointDiagonalPoint inner n ∈ inner.cover n :=
  GenLimit.Support.freshFromInfinite_mem _ _ _

theorem threePointDiagonalPoint_block_not_used
    {targets : LanguageClass ℕ}
    (inner : CountableInnerCover targets) (n : ℕ) :
    threePointBlockIndex (threePointDiagonalPoint inner n) ∉
      threePointDiagonalUsedBlocks inner n := by
  intro hused
  exact GenLimit.Support.freshFromInfinite_not_mem _ _ _
    (mem_threePointForbiddenBlocks_iff.mpr hused)

theorem threePointDiagonalUsedBlocks_step
    {targets : LanguageClass ℕ}
    (inner : CountableInnerCover targets) (n : ℕ) :
    threePointDiagonalUsedBlocks inner n ⊆
      threePointDiagonalUsedBlocks inner (n + 1) := by
  rw [threePointDiagonalUsedBlocks_succ]
  exact Finset.subset_insert _ _

theorem threePointDiagonalUsedBlocks_mono
    {targets : LanguageClass ℕ}
    (inner : CountableInnerCover targets) :
    Monotone (threePointDiagonalUsedBlocks inner) :=
  monotone_nat_of_le_succ (threePointDiagonalUsedBlocks_step inner)

theorem threePointDiagonalBlockIndex_injective
    {targets : LanguageClass ℕ}
    (inner : CountableInnerCover targets) :
    Function.Injective
      (fun n => threePointBlockIndex (threePointDiagonalPoint inner n)) := by
  intro i j hij
  change threePointBlockIndex (threePointDiagonalPoint inner i) =
    threePointBlockIndex (threePointDiagonalPoint inner j) at hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hiStep :
        threePointBlockIndex (threePointDiagonalPoint inner i) ∈
          threePointDiagonalUsedBlocks inner (i + 1) := by
      simp
    have hiLater :
        threePointBlockIndex (threePointDiagonalPoint inner i) ∈
          threePointDiagonalUsedBlocks inner j :=
      (threePointDiagonalUsedBlocks_mono inner
        (Nat.succ_le_iff.mpr hlt)) hiStep
    exact threePointDiagonalPoint_block_not_used inner j
      (hij ▸ hiLater)
  · have hjStep :
        threePointBlockIndex (threePointDiagonalPoint inner j) ∈
          threePointDiagonalUsedBlocks inner (j + 1) := by
      simp
    have hjLater :
        threePointBlockIndex (threePointDiagonalPoint inner j) ∈
          threePointDiagonalUsedBlocks inner i :=
      (threePointDiagonalUsedBlocks_mono inner
        (Nat.succ_le_iff.mpr hgt)) hjStep
    exact threePointDiagonalPoint_block_not_used inner i
      (hij.symm ▸ hjLater)

/-- Choose the pair pattern exactly when the selected diagonal point in a
block is its singleton position.  Injectivity of selected block indices makes
this assignment consistent. -/
noncomputable def threePointDiagonalPattern
    {targets : LanguageClass ℕ}
    (inner : CountableInnerCover targets) (j : ℕ) : Bool :=
  by
    classical
    exact if ∃ i,
        threePointBlockIndex (threePointDiagonalPoint inner i) = j ∧
        threePointBlockPosition (threePointDiagonalPoint inner i) =
          (2 : Fin 3)
      then true
      else false

theorem threePointDiagonalPoint_not_mem_language
    {targets : LanguageClass ℕ}
    (inner : CountableInnerCover targets) (i : ℕ) :
    threePointDiagonalPoint inner i ∉
      threePointLanguage (threePointDiagonalPattern inner) := by
  classical
  let point := threePointDiagonalPoint inner i
  by_cases hlast : threePointBlockPosition point = (2 : Fin 3)
  · have hpattern :
        threePointDiagonalPattern inner (threePointBlockIndex point) = true := by
      have hex : ∃ k,
          threePointBlockIndex (threePointDiagonalPoint inner k) =
              threePointBlockIndex point ∧
            threePointBlockPosition (threePointDiagonalPoint inner k) =
              (2 : Fin 3) := by
        refine ⟨i, ?_, ?_⟩
        · simp [point]
        · simpa [point] using hlast
      simp [threePointDiagonalPattern, hex]
    simp [threePointLanguage, hpattern, point, hlast]
  · have hnone : ¬ ∃ k,
        threePointBlockIndex (threePointDiagonalPoint inner k) =
            threePointBlockIndex point ∧
          threePointBlockPosition (threePointDiagonalPoint inner k) =
            (2 : Fin 3) := by
      rintro ⟨k, hkblock, hkpos⟩
      have hki : k = i :=
        threePointDiagonalBlockIndex_injective inner hkblock
      subst k
      exact hlast hkpos
    have hpattern :
        threePointDiagonalPattern inner (threePointBlockIndex point) = false := by
      simp [threePointDiagonalPattern, hnone]
    simp [threePointLanguage, hpattern, point, hlast]

theorem no_countableInnerCover_threePointLanguageClass :
    ¬ HasCountableInnerCover threePointLanguageClass := by
  rintro ⟨inner⟩
  let σ := threePointDiagonalPattern inner
  let target := threePointLanguage σ
  have htarget : target ∈ threePointLanguageClass :=
    ⟨σ, rfl⟩
  obtain ⟨i, hi⟩ := inner.contained target htarget
  exact threePointDiagonalPoint_not_mem_language inner i
    (hi (threePointDiagonalPoint_mem inner i))

theorem threePointLanguageClass_not_sourceSetQueryGeneratable :
    ¬ SourceSetQueryGeneratable threePointLanguageClass := by
  intro hgeneratable
  exact no_countableInnerCover_threePointLanguageClass
    (sourceSetQuery_implies_countableInnerCover
      threePointLanguageClass_all_infinite hgeneratable)

/-! ## Source Theorem 3.3 -/

/-- The paper's concrete witness: the three-point block class is generatable
by a source-timed element-valued one-query strategy but not by any
source-timed set-valued one-query strategy. -/
theorem theorem_3_3_threePointBlock_separation :
    SourceElementQueryGeneratable threePointLanguageClass ∧
      ¬ SourceSetQueryGeneratable threePointLanguageClass :=
  ⟨threePointLanguageClass_sourceElementQueryGeneratable,
    threePointLanguageClass_not_sourceSetQueryGeneratable⟩

/-- Literal existential form of source Theorem 3.3. -/
theorem theorem_3_3 :
    ∃ targets : LanguageClass ℕ,
      SourceElementQueryGeneratable targets ∧
        ¬ SourceSetQueryGeneratable targets :=
  ⟨threePointLanguageClass, theorem_3_3_threePointBlock_separation⟩

end GenLimit.FeedbackQueries
