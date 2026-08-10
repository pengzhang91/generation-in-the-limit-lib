import GenLimit.Paper28_ContrastiveGeneration.IdentificationGeometry
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Finite.Range

/-!
# Safe and eventual cores for contrastive generation

Source: Li--Han--Jiang--Gao,
*Contrastive Identification and Generation in the Limit*,
arXiv:2605.06211v1, Definitions 5.1--5.2 and Propositions 5.8 and 5.11.

This module uses the paper's prefix model literally: a contrastive generator
sees the first `t` crossing edges and returns one point.  Eventual correctness
requires that point to lie in the target support and outside the vertices
seen in the prefix.  As in the source, outputs need not be fresh relative to
earlier generated outputs.
-/

namespace GenLimit
namespace ContrastiveGeneration

/-- The vertices appearing in a finite contrastive history. -/
def seenPrefix {t : ℕ} (history : Fin t → Edge α) : Set α :=
  {x | ∃ i, Incident x (history i)}

theorem seenPrefix_finite {t : ℕ} (history : Fin t → Edge α) :
    (seenPrefix history).Finite := by
  apply
    ((Set.finite_range fun i : Fin t => (history i).left).union
      (Set.finite_range fun i : Fin t => (history i).right)).subset
  intro x hx
  obtain ⟨i, hi⟩ := hx
  rcases hi with rfl | rfl
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr ⟨i, rfl⟩

/-- The first `t` edges of a stream, in the source's finite-prefix form. -/
def streamPrefix (stream : ℕ → Edge α) (t : ℕ) : Fin t → Edge α :=
  fun i => stream i

/-- A contrastive generator on finite edge prefixes. -/
abbrev ContrastiveGenerator (α : Type*) :=
  ∀ t : ℕ, (Fin t → Edge α) → α

/-- Output of a contrastive generator on the first `t` edges of a stream. -/
def generatorOutput
    (G : ContrastiveGenerator α) (stream : ℕ → Edge α) (t : ℕ) : α :=
  G t (streamPrefix stream t)

/-- Definition 3.4's eventual generation condition for one target. -/
def GeneratesFrom
    (G : ContrastiveGenerator α) (h : Set α) : Prop :=
  ∀ stream : ℕ → Edge α,
    IsContrastivePresentation stream h →
      ∃ T, ∀ t, T ≤ t →
        generatorOutput G stream t ∈ h ∧
          generatorOutput G stream t ∉
            seenPrefix (streamPrefix stream t)

/-- Definition 5.2's non-uniform contrastive generatability. -/
def ContrastivelyGeneratable (𝓗 : Set (Set α)) : Prop :=
  ∃ G : ContrastiveGenerator α,
    ∀ h, h ∈ 𝓗 → GeneratesFrom G h

/-- Definition 5.1: hypotheses consistent with all observed crossing edges. -/
def edgeVersionSpace
    (𝓗 : Set (Set α)) {t : ℕ} (history : Fin t → Edge α) :
    Set (Set α) :=
  {h | h ∈ 𝓗 ∧ ∀ i, Crosses h (history i)}

/-- Definition 5.1: edge-induced closure, with the source's empty-version
space convention. -/
noncomputable def edgeClosure
    (𝓗 : Set (Set α)) {t : ℕ} (history : Fin t → Edge α) : Set α :=
  by
    classical
    exact
      if (edgeVersionSpace 𝓗 history).Nonempty then
        {x | ∀ h, h ∈ edgeVersionSpace 𝓗 history → x ∈ h}
      else
        ∅

theorem target_mem_edgeVersionSpace
    {𝓗 : Set (Set α)} {h : Set α} (hh : h ∈ 𝓗)
    {stream : ℕ → Edge α}
    (hstream : IsContrastivePresentation stream h) (t : ℕ) :
    h ∈ edgeVersionSpace 𝓗 (streamPrefix stream t) := by
  exact ⟨hh, fun i => hstream.1 i⟩

theorem edgeClosure_subset_target
    {𝓗 : Set (Set α)} {h : Set α} (hh : h ∈ 𝓗)
    {stream : ℕ → Edge α}
    (hstream : IsContrastivePresentation stream h) (t : ℕ) :
    edgeClosure 𝓗 (streamPrefix stream t) ⊆ h := by
  have hmem :
      h ∈ edgeVersionSpace 𝓗 (streamPrefix stream t) :=
    target_mem_edgeVersionSpace hh hstream t
  have hnonempty :
      (edgeVersionSpace 𝓗 (streamPrefix stream t)).Nonempty :=
    ⟨h, hmem⟩
  simp only [edgeClosure, if_pos hnonempty]
  intro x hx
  exact hx h hmem

/-- The hypothesis of Proposition 5.8: every valid prefix has an infinite
safe edge-induced closure. -/
def InfiniteSafeCores (𝓗 : Set (Set α)) : Prop :=
  ∀ h, h ∈ 𝓗 → ∀ stream : ℕ → Edge α,
    IsContrastivePresentation stream h →
      ∀ t, (edgeClosure 𝓗 (streamPrefix stream t)).Infinite

theorem exists_safe_fresh
    {𝓗 : Set (Set α)} {t : ℕ} {history : Fin t → Edge α}
    (hinfinite : (edgeClosure 𝓗 history).Infinite) :
    ∃ x, x ∈ edgeClosure 𝓗 history ∧ x ∉ seenPrefix history :=
  hinfinite.exists_notMem_finite (seenPrefix_finite history)

/-- The information-theoretic safe-core generator from Proposition 5.8. -/
noncomputable def safeCoreGenerator [Nonempty α]
    (𝓗 : Set (Set α)) : ContrastiveGenerator α :=
  by
    classical
    exact fun _t history =>
      if hex :
          ∃ x, x ∈ edgeClosure 𝓗 history ∧
            x ∉ seenPrefix history then
        Classical.choose hex
      else
        Classical.choice inferInstance

theorem safeCoreGenerator_spec [Nonempty α]
    {𝓗 : Set (Set α)} {t : ℕ} {history : Fin t → Edge α}
    (hinfinite : (edgeClosure 𝓗 history).Infinite) :
    safeCoreGenerator 𝓗 t history ∈ edgeClosure 𝓗 history ∧
      safeCoreGenerator 𝓗 t history ∉ seenPrefix history := by
  have hex := exists_safe_fresh hinfinite
  simpa [safeCoreGenerator, hex] using Classical.choose_spec hex

/-- Proposition 5.8: uniformly infinite safe cores suffice for ordinary
contrastive generation. -/
theorem proposition_5_8 [Nonempty α]
    (𝓗 : Set (Set α)) (hsafe : InfiniteSafeCores 𝓗) :
    ContrastivelyGeneratable 𝓗 := by
  refine ⟨safeCoreGenerator 𝓗, ?_⟩
  intro h hh stream hstream
  refine ⟨0, ?_⟩
  intro t _ht
  have hspec :=
    safeCoreGenerator_spec (hsafe h hh stream hstream t)
  exact
    ⟨edgeClosure_subset_target hh hstream t hspec.1,
      hspec.2⟩

/-- Definition 5.10: one injective sequence is eventually contained in
every target support. -/
def IsEventualCore (𝓗 : Set (Set α)) (core : ℕ → α) : Prop :=
  Function.Injective core ∧
    ∀ h, h ∈ 𝓗 → {m : ℕ | core m ∉ h}.Finite

theorem pairFiber_injective
    (core : ℕ → α) (hcore : Function.Injective core) (t : ℕ) :
    Function.Injective (fun k => core (Nat.pair t k)) := by
  intro k l hkl
  exact (Nat.pair_eq_pair.mp (hcore hkl)).2

theorem exists_pairFiber_fresh
    (core : ℕ → α) (hcore : Function.Injective core)
    {t : ℕ} (history : Fin t → Edge α) :
    ∃ k, core (Nat.pair t k) ∉ seenPrefix history := by
  have hinfinite :
      (Set.range fun k => core (Nat.pair t k)).Infinite :=
    Set.infinite_range_of_injective (pairFiber_injective core hcore t)
  obtain ⟨x, ⟨k, rfl⟩, hk⟩ :=
    hinfinite.exists_notMem_finite (seenPrefix_finite history)
  exact ⟨k, hk⟩

/-- A selected index in the infinite pairing-function fiber assigned to one
history length. -/
noncomputable def eventualCoreChoice
    (core : ℕ → α) (hcore : Function.Injective core)
    {t : ℕ} (history : Fin t → Edge α) : ℕ :=
  Classical.choose (exists_pairFiber_fresh core hcore history)

theorem eventualCoreChoice_spec
    (core : ℕ → α) (hcore : Function.Injective core)
    {t : ℕ} (history : Fin t → Edge α) :
    core (Nat.pair t (eventualCoreChoice core hcore history)) ∉
      seenPrefix history :=
  Classical.choose_spec (exists_pairFiber_fresh core hcore history)

/-- The prefix-based generator used for Proposition 5.11.  Pairing the time
with an auxiliary search coordinate makes its core index at least the
current time while leaving infinitely many candidates outside a finite
observed prefix. -/
noncomputable def eventualCoreGenerator
    (core : ℕ → α) (hcore : Function.Injective core) :
    ContrastiveGenerator α :=
  fun t history =>
    core (Nat.pair t (eventualCoreChoice core hcore history))

theorem eventualCoreGenerator_fresh
    (core : ℕ → α) (hcore : Function.Injective core)
    {t : ℕ} (history : Fin t → Edge α) :
    eventualCoreGenerator core hcore t history ∉ seenPrefix history :=
  eventualCoreChoice_spec core hcore history

theorem eventualCoreGenerator_index_ge
    (core : ℕ → α) (hcore : Function.Injective core)
    {t : ℕ} (history : Fin t → Edge α) :
    t ≤ Nat.pair t (eventualCoreChoice core hcore history) :=
  Nat.left_le_pair _ _

/-- Proposition 5.11.  The source assumes a countable class of infinite
proper nontrivial hypotheses; the proof only needs the displayed eventual
core and is therefore stated in its stronger semantic form. -/
theorem proposition_5_11
    (𝓗 : Set (Set α)) (core : ℕ → α)
    (hcore : IsEventualCore 𝓗 core) :
    ContrastivelyGeneratable 𝓗 := by
  classical
  refine ⟨eventualCoreGenerator core hcore.1, ?_⟩
  intro h hh stream _hstream
  let bad : Set ℕ := {m | core m ∉ h}
  have hbad : bad.Finite := hcore.2 h hh
  obtain ⟨T, hT⟩ := hbad.toFinset.exists_nat_subset_range
  refine ⟨T, ?_⟩
  intro t ht
  let history := streamPrefix stream t
  let k := eventualCoreChoice core hcore.1 history
  have hindex_ge : T ≤ Nat.pair t k :=
    ht.trans (Nat.left_le_pair t k)
  constructor
  · by_contra hnot
    have hmem_bad : Nat.pair t k ∈ bad := hnot
    have hmem_fin : Nat.pair t k ∈ hbad.toFinset := by
      simpa only [Set.Finite.mem_toFinset] using hmem_bad
    have hlt : Nat.pair t k < T :=
      Finset.mem_range.mp (hT hmem_fin)
    exact (Nat.not_lt_of_ge hindex_ge) hlt
  · exact eventualCoreGenerator_fresh core hcore.1
      (history := history)

end ContrastiveGeneration
end GenLimit
