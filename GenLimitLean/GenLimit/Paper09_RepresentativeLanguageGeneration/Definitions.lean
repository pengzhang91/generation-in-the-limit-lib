import GenLimit.Paper09_RepresentativeLanguageGeneration.Distribution
import GenLimit.Core.ClassGeneration
import GenLimit.Core.VersionSpace

/-!
# Representative language generation: semantic definitions

Source: Peale--Raman--Reingold, *Representative Language Generation*, ICML
2025 / PMLR 267, Definitions 2.2--2.12.

Histories have length `t` and contain `x₀,...,x_{t-1}`.  This is the
zero-indexed form of the paper's `x₁,...,x_t`.  Representativeness is required
only for `0 < t`, since Definition 2.6's empirical distribution divides by the
number of unique observed examples.
-/

namespace GenLimit.RepresentativeGeneration

/-- Published Definition 2.2. -/
def IsCountablePartition (groups : ℕ → Set α) : Prop :=
  (∀ i j, i ≠ j → Disjoint (groups i) (groups j)) ∧
    (⋃ i, groups i) = Set.univ

/-- Published Definition 2.3, on the finset of distinct observed examples.  This is the
paper-facing name for Core's positive version space. -/
abbrev consistentHypotheses
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) :
    Set (GenLimit.Generic.Language α) :=
  GenLimit.Generic.versionSpace H S

/-- The common support of a nonempty version space, reusing Core's canonical
closure intersection. -/
abbrev commonCore
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) :
    GenLimit.Generic.Language α :=
  GenLimit.Generic.commonCore H S

/-- Published Definition 2.4, with `none` representing the paper's bottom value.  This is
the same positive closure already shared by Core and Paper02. -/
noncomputable abbrev closure
    (H : GenLimit.Generic.LanguageClass α) (S : Finset α) :
    Option (GenLimit.Generic.Language α) :=
  GenLimit.Generic.closure H S

theorem commonCore_subset_of_consistent
    {H : GenLimit.Generic.LanguageClass α} {S : Finset α}
    {L : GenLimit.Generic.Language α}
    (hL : L ∈ consistentHypotheses H S) :
    commonCore H S ⊆ L :=
  GenLimit.Generic.commonCore_subset_of_mem_versionSpace hL

/-- Run a randomized generator after a history of length `t`. -/
def distributionAt
    (gen : RandomizedGenerator α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) :
    DiscreteDistribution α :=
  gen t (fun k => stream k)

/-- Published Definition 2.8.  The repaired `iSup` distance is in `ENNReal`, so the real
tolerance is embedded with `ofReal`. -/
def IsAlphaRepresentative
    (gen : RandomizedGenerator α) (groups : ℕ → Set α) (alpha : ℝ) : Prop :=
  ∀ stream : GenLimit.Generic.Stream α, ∀ t : ℕ, 0 < t →
    groupSupDistance (distributionAt gen stream t)
        (GenLimit.Generic.sample stream t) groups ≤
      ENNReal.ofReal alpha

/-- Probability one on the target's unseen examples. -/
def IsConsistentAt
    (gen : RandomizedGenerator α)
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (t : ℕ) : Prop :=
  groupMass (distributionAt gen stream t)
    (L \ (↑(GenLimit.Generic.sample stream t) : Set α)) = 1

def IsConsistentFrom
    (gen : RandomizedGenerator α)
    (L : GenLimit.Generic.Language α)
    (stream : GenLimit.Generic.Stream α) (T : ℕ) : Prop :=
  ∀ t, T ≤ t → IsConsistentAt gen L stream t

theorem isConsistentAt_iff_supportedOn
    {gen : RandomizedGenerator α}
    {L : GenLimit.Generic.Language α}
    {stream : GenLimit.Generic.Stream α} {t : ℕ} :
    IsConsistentAt gen L stream t ↔
      SupportedOn (distributionAt gen stream t)
        (L \ (↑(GenLimit.Generic.sample stream t) : Set α)) := by
  exact supportedOn_iff_groupMass_eq_one.symm

/-- Published Definition 2.9 at a fixed tolerance. -/
def AlphaRepresentativeUniformlyGeneratable
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) (alpha : ℝ) : Prop :=
  ∃ gen : RandomizedGenerator α,
    IsAlphaRepresentative gen groups alpha ∧
    ∃ d : ℕ, ∀ L, L ∈ H →
      ∀ stream : GenLimit.Generic.Stream α,
        GenLimit.Generic.StreamIn stream L →
        ∀ t, (GenLimit.Generic.sample stream t).card = d →
          IsConsistentFrom gen L stream t

/-- Published Definition 2.10. -/
def RepresentativelyUniformlyGeneratable
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) : Prop :=
  ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 →
    AlphaRepresentativeUniformlyGeneratable H groups alpha

/-- Published Definition 2.11.  The threshold may depend on the target but not on the
stream. -/
def RepresentativelyNonuniformlyGeneratable
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) : Prop :=
  ∀ alpha : ℝ, 0 < alpha →
    ∃ gen : RandomizedGenerator α,
      IsAlphaRepresentative gen groups alpha ∧
      ∀ L, L ∈ H → ∃ d : ℕ,
        ∀ stream : GenLimit.Generic.Stream α,
          GenLimit.Generic.StreamIn stream L →
          ∀ t, (GenLimit.Generic.sample stream t).card = d →
            IsConsistentFrom gen L stream t

/-- Published Definition 2.12.  The time may depend on both target and exact
enumeration. -/
def RepresentativelyGeneratableInLimit
    (H : GenLimit.Generic.LanguageClass α)
    (groups : ℕ → Set α) : Prop :=
  ∀ alpha : ℝ, 0 < alpha →
    ∃ gen : RandomizedGenerator α,
      IsAlphaRepresentative gen groups alpha ∧
      ∀ L, L ∈ H → ∀ stream : GenLimit.Generic.Stream α,
        GenLimit.Generic.Presents stream L →
          ∃ T : ℕ, IsConsistentFrom gen L stream T

end GenLimit.RepresentativeGeneration
