import GenLimit.Core.FiniteContamination
import GenLimit.Core.OrderedDensity
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Paper 32: approximate generation definitions

Source: Irene Strauss, Alexandra Butoi, and Ryan Cotterell,
*Generating in the Limit with Infinitely Many Hallucinations*,
arXiv:2606.28354v1.

The paper works over the Kleene closure of a finite nonempty alphabet.  This
module uses `ℕ`, an explicit canonical coding of that countably infinite
universe.  Unlike the element-at-a-time Core generator, the source generator
observes and emits finite sets, so its exhaustion and batch-generator
interface remains paper-local.

Target recall in the main generation theorems is measured along a fixed
duplicate-free enumeration.  We therefore reuse `KleinbergWei.OrderedLanguage`
and its checked `lowerDensity`/`upperDensity` API rather than introduce a
second ordered-density definition.
-/

namespace GenLimit.InfinitelyManyHallucinations

open Filter
open GenLimit.Generic
open GenLimit.KleinbergWei

noncomputable local instance : DecidableEq α := Classical.decEq α
noncomputable local instance (p : Prop) : Decidable p :=
  Classical.propDecidable p

abbrev Language := GenLimit.Generic.Language ℕ

/-- Definition 2.1's increasing finite-set presentation, without yet naming
its union. -/
structure Exhaustion where
  stage : ℕ → Finset ℕ
  stage_zero : stage 0 = ∅
  monotone_stage : Monotone stage

@[ext] theorem Exhaustion.ext {E F : Exhaustion}
    (hstage : E.stage = F.stage) : E = F := by
  cases E
  cases F
  cases hstage
  rfl

namespace Exhaustion

/-- The language exhausted by an increasing finite-set presentation. -/
def limit (E : Exhaustion) : Language :=
  {x | ∃ n, x ∈ E.stage n}

theorem mem_limit_iff (E : Exhaustion) {x : ℕ} :
    x ∈ E.limit ↔ ∃ n, x ∈ E.stage n :=
  Iff.rfl

theorem stage_subset_limit (E : Exhaustion) (n : ℕ) :
    (E.stage n : Set ℕ) ⊆ E.limit := by
  intro x hx
  exact ⟨n, hx⟩

/-- The strings first added at a positive round.  Round zero has no
increment, matching the source convention `L₀ = ∅`. -/
def increment (E : Exhaustion) : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => E.stage (n + 1) \ E.stage n

@[simp] theorem increment_zero (E : Exhaustion) : E.increment 0 = ∅ :=
  rfl

theorem stage_succ_eq_stage_union_increment (E : Exhaustion) (n : ℕ) :
    E.stage (n + 1) = E.stage n ∪ E.increment (n + 1) := by
  rw [increment]
  exact (Finset.union_sdiff_of_subset
    (E.monotone_stage (Nat.le_succ n))).symm

theorem increment_subset_stage (E : Exhaustion) (n : ℕ) :
    E.increment n ⊆ E.stage n := by
  cases n with
  | zero => simp
  | succ n => exact Finset.sdiff_subset

theorem increment_disjoint_previous (E : Exhaustion) (n : ℕ) :
    Disjoint (E.increment (n + 1)) (E.stage n) := by
  simp [increment, Finset.disjoint_left]

theorem finset_eventually_subset_stage
    (E : Exhaustion) (S : Finset ℕ) (hS : (S : Set ℕ) ⊆ E.limit) :
    ∃ N, S ⊆ E.stage N := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | @insert x S hx ih =>
      obtain ⟨Nx, hxStage⟩ :=
        hS (show x ∈ insert x S by exact Finset.mem_insert_self x S)
      obtain ⟨NS, hSStage⟩ := ih
        (fun y hy => hS (Finset.mem_insert_of_mem hy))
      refine ⟨max Nx NS, ?_⟩
      rw [Finset.insert_subset_iff]
      exact ⟨E.monotone_stage (Nat.le_max_left _ _) hxStage,
        fun y hy => E.monotone_stage (Nat.le_max_right _ _) (hSStage hy)⟩

/-- Finite stages exhausting an infinite limit grow without bound. -/
theorem card_tendsto_atTop_of_limit_infinite
    (E : Exhaustion) (hinfinite : E.limit.Infinite) :
    Tendsto (fun n => (E.stage n).card) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  obtain ⟨S, hS, hcard⟩ := hinfinite.exists_subset_card_eq b
  obtain ⟨N, hSN⟩ := E.finset_eventually_subset_stage S hS
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [← hcard]
  exact Finset.card_le_card
    (hSN.trans (E.monotone_stage hn))

/-- The source notation `E_n ↑ L`. -/
def Exhausts (E : Exhaustion) (L : Language) : Prop :=
  E.limit = L

/-- An enumeration adds exactly one new string at every positive round. -/
def IsEnumeration (E : Exhaustion) : Prop :=
  ∀ n, (E.increment (n + 1)).card = 1

/-- An `f`-bounded exhaustion adds at most `f(n)` strings at positive round
`n`. -/
def BoundedBy (f : ℕ → ℕ) (E : Exhaustion) : Prop :=
  ∀ n, (E.increment (n + 1)).card ≤ f (n + 1)

/-- The paper's single-step exhaustion permits an empty increment. -/
def IsSingleStep (E : Exhaustion) : Prop :=
  BoundedBy (fun _ => 1) E

end Exhaustion

/-- Number of members of `S` belonging to `L`. -/
noncomputable def countIn (L : Language) (S : Finset ℕ) : ℕ := by
  exact GenLimit.Generic.acceptedCount (fun x => x ∈ L) S

theorem countIn_eq_filter_card (L : Language) (S : Finset ℕ) :
    countIn L S = (S.filter fun x => x ∈ L).card := by
  classical
  rfl

theorem countIn_le (L : Language) (S : Finset ℕ) :
    countIn L S ≤ S.card := by
  exact GenLimit.Generic.acceptedCount_le (fun x => x ∈ L) S

/-- A finite membership fraction.  The empty denominator is assigned zero;
all source asymptotics used below have eventually positive denominators, so
this initial-value convention is immaterial. -/
noncomputable def membershipFraction (L : Language) (S : Finset ℕ) : ℝ :=
  GenLimit.Generic.acceptedFraction (fun x => x ∈ L) S

theorem membershipFraction_eq (L : Language) (S : Finset ℕ) :
    membershipFraction L S =
      if S.card = 0 then 0 else (countIn L S : ℝ) / S.card := by
  rfl

theorem membershipFraction_nonneg (L : Language) (S : Finset ℕ) :
    0 ≤ membershipFraction L S := by
  exact GenLimit.Generic.acceptedFraction_nonneg (fun x => x ∈ L) S

theorem membershipFraction_le_one (L : Language) (S : Finset ℕ) :
    membershipFraction L S ≤ 1 := by
  exact GenLimit.Generic.acceptedFraction_le_one (fun x => x ∈ L) S

/-- Theorem 2.1's membership-side lower precision. -/
noncomputable def lowerMembershipPrecision
    (L : Language) (guess : Exhaustion) : ℝ :=
  liminf (fun n => membershipFraction L (guess.stage n)) atTop

/-- The corresponding membership-side upper precision. -/
noncomputable def upperMembershipPrecision
    (L : Language) (guess : Exhaustion) : ℝ :=
  limsup (fun n => membershipFraction L (guess.stage n)) atTop

/-- Coverage-based lower recall from Lemma 2.2, specialized to the fixed
target enumeration used by the main generation results. -/
noncomputable def lowerRecall (target : OrderedLanguage) (guess : Language) : ℝ :=
  target.lowerDensity guess

/-- Coverage-based upper recall. -/
noncomputable def upperRecall (target : OrderedLanguage) (guess : Language) : ℝ :=
  target.upperDensity guess

/-- The step-wise tail precision `t_n`; empty increments receive precision
one exactly as in Definition 2.3. -/
noncomputable def stepTailPrecision
    (L : Language) (guess : Exhaustion) (n : ℕ) : ℝ :=
  if (guess.increment n).card = 0 then 1
  else (countIn L (guess.increment n) : ℝ) / (guess.increment n).card

noncomputable def lowerTailPrecision
    (L : Language) (guess : Exhaustion) : ℝ :=
  liminf (stepTailPrecision L guess) atTop

noncomputable def upperTailPrecision
    (L : Language) (guess : Exhaustion) : ℝ :=
  limsup (stepTailPrecision L guess) atTop

/-- Definition 3.2: every sufficiently late generated increment is valid. -/
def EventuallyValid (L : Language) (guess : Exhaustion) : Prop :=
  ∃ N, ∀ n, N ≤ n → (guess.increment n : Set ℕ) ⊆ L

/-- Tail precision one is attained in finite time when every later step has
step-wise precision exactly one. -/
def TailPrecisionOneFromFiniteTime
    (L : Language) (guess : Exhaustion) : Prop :=
  ∃ N, ∀ n, N ≤ n → stepTailPrecision L guess n = 1

/-- A history-sensitive batch generator.  At round `n` it receives the
adversary's stages `0,...,n` and its own previous cumulative stage, then
returns the next finite batch.

The displayed source type mentions only the current adversarial and previous
generated sets, while its algorithms also maintain counters, previous input,
pods, and intersection chains.  Supplying the finite histories is the
standard total functional encoding of that state: a deterministic routine
can replay its internal counters and pods from the adversarial history. -/
abbrev BatchGenerator :=
  ∀ n : ℕ,
    (Fin (n + 1) → Finset ℕ) →
    Finset ℕ → Finset ℕ

/-- Equation (3.1): the cumulative generated exhaustion induced by a batch
generator and an adversarial exhaustion. -/
def generatedStages (G : BatchGenerator) (adversary : Exhaustion) : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 =>
      generatedStages G adversary n ∪
        G (n + 1)
          (fun i => adversary.stage i)
          (generatedStages G adversary n)

theorem generatedStages_mono
    (G : BatchGenerator) (adversary : Exhaustion) :
    Monotone (generatedStages G adversary) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ n _ ih =>
      exact ih.trans (Finset.subset_union_left)

/-- The generated stages packaged as a source exhaustion. -/
def generatedExhaustion
    (G : BatchGenerator) (adversary : Exhaustion) : Exhaustion where
  stage := generatedStages G adversary
  stage_zero := rfl
  monotone_stage := generatedStages_mono G adversary

/-- Definition 3.4 at the literal generator-output level.  Every returned
batch must avoid both the current adversarial stage and the previous
cumulative guess. -/
def GeneratorNovel (G : BatchGenerator) (adversary : Exhaustion) : Prop :=
  ∀ n,
    Disjoint
      (G (n + 1) (fun i => adversary.stage i)
        (generatedStages G adversary n))
      (adversary.stage (n + 1) ∪ generatedStages G adversary n)

/-- The extensional trace consequence of strict generator novelty: every
new distinct output avoids everything revealed by the current round.  This
predicate deliberately cannot detect a generator that returns an already
generated value, because cumulative set traces quotient away such attempts. -/
def Novel (adversary guess : Exhaustion) : Prop :=
  ∀ n, Disjoint (guess.increment n) (adversary.stage n)

theorem GeneratorNovel.traceNovel
    {G : BatchGenerator} {adversary : Exhaustion}
    (hnovel : GeneratorNovel G adversary) :
    Novel adversary (generatedExhaustion G adversary) := by
  intro n
  cases n with
  | zero => simp [Exhaustion.increment]
  | succ n =>
      let previous := generatedStages G adversary n
      let batch := G (n + 1) (fun i => adversary.stage i) previous
      have hraw : Disjoint batch
          (adversary.stage (n + 1) ∪ previous) := by
        simpa [batch, previous] using hnovel n
      have hprevious : Disjoint previous batch := by
        rw [Finset.disjoint_left]
        intro x hxPrevious hxBatch
        exact (Finset.disjoint_left.mp hraw) hxBatch
          (Finset.mem_union_right _ hxPrevious)
      have hadversary : Disjoint batch (adversary.stage (n + 1)) := by
        rw [Finset.disjoint_left]
        intro x hxBatch hxAdversary
        exact (Finset.disjoint_left.mp hraw) hxBatch
          (Finset.mem_union_left _ hxAdversary)
      change Disjoint ((previous ∪ batch) \ previous)
        (adversary.stage (n + 1))
      rw [Finset.union_sdiff_cancel_left hprevious]
      exact hadversary

/-- Definition 3.7's recursively accumulated set of outputs that were novel
at the round when they first appeared. -/
def novelHistory (adversary guess : Exhaustion) : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 =>
      novelHistory adversary guess n ∪
        (guess.increment (n + 1) \ adversary.stage (n + 1))

/-- Definition 3.7: at every nonempty stage, at least a `γ` fraction of all
distinct generated values were novel when first produced. -/
def GammaNovel (γ : ℝ) (adversary guess : Exhaustion) : Prop :=
  ∀ n, 0 < (guess.stage n).card →
    γ ≤ (novelHistory adversary guess n).card / (guess.stage n).card

/-- Number of exploration rounds through time `m`. -/
noncomputable def explorationCount (E : Set ℕ) (m : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc 1 m).filter fun n => n ∈ E).card

/-- Definition 4.1's sparse exploration times, expressed by their finite
prefix count and its zero-density limit. -/
structure ExplorationSet where
  carrier : Set ℕ
  infinite' : carrier.Infinite
  one_not_mem : 1 ∉ carrier
  nonconsecutive : ∀ n, n ∈ carrier → n + 1 ∉ carrier
  prefixRatio_tendsto_zero :
    Tendsto
      (fun m =>
        ((explorationCount carrier m : ℝ) / (m : ℝ)))
      atTop (nhds 0)

/-- Definition 4.2's finite-prefix strengthening. -/
def ExplorationSet.GammaAdmissible
    (E : ExplorationSet) (γ : ℝ) : Prop :=
  ∀ m,
    ((explorationCount E.carrier m : ℝ) ≤
      (1 - γ) * (m : ℝ))

end GenLimit.InfinitelyManyHallucinations
