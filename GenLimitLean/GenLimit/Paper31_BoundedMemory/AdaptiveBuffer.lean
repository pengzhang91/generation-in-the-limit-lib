import GenLimit.Paper31_BoundedMemory.MinimaxClosure
import Mathlib.Data.List.FinRange
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Adaptive-buffer density lower bound

Source: Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas,
*On Language Generation in the Limit with Bounded Memory*,
arXiv:2605.30324v1, Definition 12 and Theorem 4.15.

This module gives the exact bounded-buffer transition semantics, including
output infinitude and the source's no-synthesis constraint.  It constructs the
greedy no-eviction buffer generator and proves Theorem 4.15 using the actual
outer run `limsup` and minimax supremum.

The source numbers rounds from one.  Here state zero is empty, output `t` uses
the state before processing `stream t`, and state `t + 1` is the update; this
is the same run after shifting the paper's indices by one.
-/

namespace GenLimit.BoundedMemory

open Filter
open scoped Topology
open GenLimit.KleinbergWei

/-! ## Definition 12 -/

/-- Ordered buffers of at most `b` examples. -/
abbrev BufferState (α : Type*) (b : ℕ) :=
  {xs : List α // xs.length ≤ b}

def emptyBufferState (α : Type*) (b : ℕ) :
    BufferState α b :=
  ⟨[], by simp⟩

/-- Definition 12.  Output infinitude is part of the codomain, and
`update_supported` is the source's no-synthesis transition constraint. -/
structure BufferSetGenerator (α : Type*) (b : ℕ) where
  output : BufferState α b → α → Set α
  output_infinite : ∀ M x, (output M x).Infinite
  update : BufferState α b → α → BufferState α b
  update_supported :
    ∀ M x y, y ∈ (update M x).1 → y ∈ M.1 ∨ y = x

def bufferState
    {α : Type*} {b : ℕ}
    (G : BufferSetGenerator α b) (stream : ℕ → α) :
    ℕ → BufferState α b
  | 0 => emptyBufferState α b
  | t + 1 => G.update (bufferState G stream t) (stream t)

def bufferOutputAt
    {α : Type*} {b : ℕ}
    (G : BufferSetGenerator α b) (stream : ℕ → α)
    (t : ℕ) : Set α :=
  G.output (bufferState G stream t) (stream t)

def IsRepetitionFreeBufferGeneratorOn
    {α : Type*} {b : ℕ}
    (G : BufferSetGenerator α b) (L : Set α) : Prop :=
  ∀ stream : ℕ → α, ∀ _hstream : Function.Injective stream,
    GenLimit.Generic.Presents stream L →
      ∃ T, ∀ t, T ≤ t → bufferOutputAt G stream t ⊆ L

noncomputable def bufferRunUpperDensity
    (K : OrderedLanguage) {b : ℕ}
    (G : BufferSetGenerator ℕ b) (stream : ℕ → ℕ) : ℝ :=
  limsup
    (fun t => K.upperDensity (bufferOutputAt G stream t))
    atTop

/-- The exact outer-`limsup` adaptive-buffer analogue of Definition 9,
restricted as in Section 4.3 to repetition-free exact presentations. -/
def BufferUpperDensityGuarantee
    (k b : ℕ) (σ : ℝ) : Prop :=
  ∀ (langs : Fin k → Set ℕ),
    Function.Injective langs →
    (∀ a, (langs a).Infinite) →
    ∃ G : BufferSetGenerator ℕ b,
      (∀ a, IsRepetitionFreeBufferGeneratorOn G (langs a)) ∧
      ∀ (target : Fin k) (K : OrderedLanguage),
        K.carrier = langs target →
        ∀ (stream : ℕ → ℕ),
          Function.Injective stream →
          GenLimit.Generic.Presents stream K.carrier →
          σ ≤ bufferRunUpperDensity K G stream

def bufferAdmissibleUpperDensities
    (k b : ℕ) : Set ℝ :=
  Set.Icc (0 : ℝ) 1 ∩
    {σ | BufferUpperDensityGuarantee k b σ}

noncomputable def bufferMinimaxUpperDensity
    (k b : ℕ) : ℝ :=
  sSup (bufferAdmissibleUpperDensities k b)

theorem bufferRunUpperDensity_ge_of_frequently
    (K : OrderedLanguage) {b : ℕ}
    (G : BufferSetGenerator ℕ b) (stream : ℕ → ℕ)
    {σ : ℝ}
    (hσ : ∃ᶠ t : ℕ in atTop,
      σ ≤ K.upperDensity (bufferOutputAt G stream t)) :
    σ ≤ bufferRunUpperDensity K G stream := by
  unfold bufferRunUpperDensity
  exact le_limsup_of_frequently_le hσ
    (isBoundedUnder_of
      ⟨1, fun t =>
        orderedUpperDensity_le_one K
          (bufferOutputAt G stream t)⟩)

/-! ## Greedy no-eviction construction -/

noncomputable def bufferResidual
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (M : BufferState ℕ b) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun i =>
    ∀ x ∈ M.1, x ∈ langs i

noncomputable def bufferResidualAfter
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (M : BufferState ℕ b) (x : ℕ) : Finset (Fin k) := by
  classical
  exact (bufferResidual langs M).filter
    (fun i => x ∈ langs i)

theorem bufferResidualAfter_subset
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (M : BufferState ℕ b) (x : ℕ) :
    bufferResidualAfter langs M x ⊆
      bufferResidual langs M := by
  classical
  exact Finset.filter_subset _ _

theorem mem_bufferResidual_iff
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (M : BufferState ℕ b) (i : Fin k) :
    i ∈ bufferResidual langs M ↔
      ∀ x ∈ M.1, x ∈ langs i := by
  classical
  simp [bufferResidual]

theorem bufferResidual_empty
    {k b : ℕ} (langs : Fin k → Set ℕ) :
    bufferResidual langs (emptyBufferState ℕ b) =
      Finset.univ := by
  classical
  ext i
  simp [bufferResidual, emptyBufferState]

def bufferResidualCore
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (M : BufferState ℕ b) (x : ℕ) : Set ℕ :=
  {y | ∀ i, i ∈ bufferResidual langs M →
    x ∈ langs i → y ∈ langs i}

noncomputable def bufferCanonicalOutput
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (M : BufferState ℕ b) (x : ℕ) : Set ℕ := by
  classical
  exact
    if (bufferResidualCore langs M x).Infinite then
      bufferResidualCore langs M x
    else
      Set.univ

theorem bufferCanonicalOutput_infinite
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (M : BufferState ℕ b) (x : ℕ) :
    (bufferCanonicalOutput langs M x).Infinite := by
  classical
  unfold bufferCanonicalOutput
  split_ifs with h
  · exact h
  · exact Set.infinite_univ

noncomputable def ShouldStore
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (M : BufferState ℕ b) (x : ℕ) : Prop := by
  classical
  exact
    M.1.length < b ∧
      bufferResidualAfter langs M x ⊂
        bufferResidual langs M

noncomputable def greedyBufferUpdate
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (M : BufferState ℕ b) (x : ℕ) :
    BufferState ℕ b := by
  classical
  by_cases h : ShouldStore langs M x
  · exact ⟨M.1 ++ [x], by simpa using h.1⟩
  · exact M

theorem greedyBufferUpdate_of_shouldStore
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (M : BufferState ℕ b) (x : ℕ)
    (h : ShouldStore langs M x) :
    (greedyBufferUpdate langs M x).1 = M.1 ++ [x] := by
  classical
  simp [greedyBufferUpdate, h]

theorem greedyBufferUpdate_of_not_shouldStore
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (M : BufferState ℕ b) (x : ℕ)
    (h : ¬ShouldStore langs M x) :
    greedyBufferUpdate langs M x = M := by
  classical
  simp [greedyBufferUpdate, h]

noncomputable def greedyBufferGenerator
    {k : ℕ} (b : ℕ) (langs : Fin k → Set ℕ) :
    BufferSetGenerator ℕ b where
  output := bufferCanonicalOutput langs
  output_infinite := bufferCanonicalOutput_infinite langs
  update := greedyBufferUpdate langs
  update_supported := by
    classical
    intro M x y hy
    by_cases h : ShouldStore langs M x
    · rw [greedyBufferUpdate_of_shouldStore langs M x h] at hy
      simp only [List.mem_append, List.mem_singleton] at hy
      exact hy
    · rw [greedyBufferUpdate_of_not_shouldStore langs M x h] at hy
      exact Or.inl hy

noncomputable def greedyBufferState
    {k : ℕ} (b : ℕ) (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) (t : ℕ) : BufferState ℕ b :=
  bufferState (greedyBufferGenerator b langs) stream t

theorem greedyBufferState_zero
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) :
    greedyBufferState b langs stream 0 =
      emptyBufferState ℕ b := rfl

theorem greedyBufferState_succ
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) (t : ℕ) :
    greedyBufferState b langs stream (t + 1) =
      greedyBufferUpdate langs
        (greedyBufferState b langs stream t) (stream t) := rfl

theorem greedyBufferState_succ_of_shouldStore
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) (t : ℕ)
    (h : ShouldStore langs
      (greedyBufferState b langs stream t) (stream t)) :
    (greedyBufferState b langs stream (t + 1)).1 =
      (greedyBufferState b langs stream t).1 ++ [stream t] := by
  rw [greedyBufferState_succ,
    greedyBufferUpdate_of_shouldStore langs _ _ h]

theorem greedyBufferState_succ_of_not_shouldStore
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) (t : ℕ)
    (h : ¬ShouldStore langs
      (greedyBufferState b langs stream t) (stream t)) :
    greedyBufferState b langs stream (t + 1) =
      greedyBufferState b langs stream t := by
  rw [greedyBufferState_succ,
    greedyBufferUpdate_of_not_shouldStore langs _ _ h]

theorem greedyBufferState_length_step_le
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) (t : ℕ) :
    (greedyBufferState b langs stream t).1.length ≤
      (greedyBufferState b langs stream (t + 1)).1.length := by
  classical
  by_cases h : ShouldStore langs
      (greedyBufferState b langs stream t) (stream t)
  · rw [greedyBufferState_succ_of_shouldStore langs stream t h]
    simp
  · rw [greedyBufferState_succ_of_not_shouldStore
      langs stream t h]

theorem greedyBufferState_length_mono
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) :
    Monotone fun t =>
      (greedyBufferState b langs stream t).1.length :=
  monotone_nat_of_le_succ
    (greedyBufferState_length_step_le langs stream)

theorem greedyBufferState_length_strict_of_shouldStore
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) (t : ℕ)
    (h : ShouldStore langs
      (greedyBufferState b langs stream t) (stream t)) :
    (greedyBufferState b langs stream t).1.length <
      (greedyBufferState b langs stream (t + 1)).1.length := by
  rw [greedyBufferState_succ_of_shouldStore langs stream t h]
  simp

noncomputable def greedyStoreTimes
    {k : ℕ} (b : ℕ) (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) : Set ℕ :=
  {t | ShouldStore langs
    (greedyBufferState b langs stream t) (stream t)}

theorem greedyStoreTimes_finite
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) :
    (greedyStoreTimes b langs stream).Finite := by
  classical
  let len : ℕ → ℕ := fun t =>
    (greedyBufferState b langs stream t).1.length
  have himage :
      len '' greedyStoreTimes b langs stream ⊆
        (Finset.range b : Set ℕ) := by
    rintro _ ⟨t, ht, rfl⟩
    exact Finset.mem_range.mpr ht.1
  have himageFinite :
      (len '' greedyStoreTimes b langs stream).Finite :=
    (Finset.finite_toSet (Finset.range b)).subset himage
  apply Set.Finite.of_finite_image himageFinite
  intro t ht u hu hlen
  by_contra htu
  rcases lt_or_gt_of_ne htu with hlt | hgt
  · have hstrict :
        len t < len (t + 1) := by
      exact
        greedyBufferState_length_strict_of_shouldStore
          langs stream t ht
    have hmono :
        len (t + 1) ≤ len u :=
      greedyBufferState_length_mono langs stream
        (by omega)
    omega
  · have hstrict :
        len u < len (u + 1) := by
      exact
        greedyBufferState_length_strict_of_shouldStore
          langs stream u hu
    have hmono :
        len (u + 1) ≤ len t :=
      greedyBufferState_length_mono langs stream
        (by omega)
    omega

theorem greedyBufferState_eventually_constant
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) :
    ∃ T, ∀ t, T ≤ t →
      greedyBufferState b langs stream t =
        greedyBufferState b langs stream T := by
  classical
  obtain ⟨B, hB⟩ :=
    (greedyStoreTimes_finite (b := b) langs stream).bddAbove
  let T := B + 1
  have hNoStore :
      ∀ t, T ≤ t →
        ¬ShouldStore langs
          (greedyBufferState b langs stream t) (stream t) := by
    intro t ht hstore
    have htB : t ≤ B := hB hstore
    omega
  refine ⟨T, ?_⟩
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
      rw [greedyBufferState_succ_of_not_shouldStore
        langs stream t (hNoStore t ht), ih]

theorem bufferResidual_eq_of_val_eq
    {k b : ℕ} (langs : Fin k → Set ℕ)
    {M N : BufferState ℕ b} (hMN : M.1 = N.1) :
    bufferResidual langs M = bufferResidual langs N := by
  classical
  ext i
  simp [bufferResidual, hMN]

theorem bufferResidual_append
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (M N : BufferState ℕ b) (x : ℕ)
    (hN : N.1 = M.1 ++ [x]) :
    bufferResidual langs N =
      bufferResidualAfter langs M x := by
  classical
  ext i
  rw [show i ∈ bufferResidualAfter langs M x ↔
      i ∈ bufferResidual langs M ∧ x ∈ langs i by
        simp [bufferResidualAfter],
    mem_bufferResidual_iff,
    mem_bufferResidual_iff]
  constructor
  · intro hi
    constructor
    · intro y hy
      exact hi y (by simp [hN, hy])
    · exact hi x (by simp [hN])
  · rintro ⟨hiM, hix⟩ y hy
    rw [hN] at hy
    rcases List.mem_append.mp hy with hyM | hyx
    · exact hiM y hyM
    · simp only [List.mem_singleton] at hyx
      subst y
      exact hix

theorem greedyBuffer_residual_length_bound
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) (t : ℕ) :
    (bufferResidual langs
        (greedyBufferState b langs stream t)).card +
        (greedyBufferState b langs stream t).1.length ≤
      k := by
  classical
  induction t with
  | zero =>
      rw [greedyBufferState_zero,
        bufferResidual_empty]
      simp [emptyBufferState]
  | succ t ih =>
      by_cases h : ShouldStore langs
          (greedyBufferState b langs stream t) (stream t)
      · have hval :=
          greedyBufferState_succ_of_shouldStore
            langs stream t h
        have hres :=
          bufferResidual_append langs
            (greedyBufferState b langs stream t)
            (greedyBufferState b langs stream (t + 1))
            (stream t) hval
        have hcard :
            (bufferResidual langs
              (greedyBufferState b langs stream (t + 1))).card <
              (bufferResidual langs
                (greedyBufferState b langs stream t)).card := by
          rw [hres]
          exact Finset.card_lt_card h.2
        rw [hval]
        simp only [List.length_append, List.length_singleton]
        omega
      · rw [greedyBufferState_succ_of_not_shouldStore
          langs stream t h]
        exact ih

/-! ## Run invariants -/

theorem bufferState_entry_seen
    {α : Type*} {b : ℕ}
    (G : BufferSetGenerator α b) (stream : ℕ → α)
    {t : ℕ} {y : α}
    (hy : y ∈ (bufferState G stream t).1) :
    ∃ s < t, stream s = y := by
  induction t with
  | zero =>
      simp [bufferState, emptyBufferState] at hy
  | succ t ih =>
      have hsupport :=
        G.update_supported
          (bufferState G stream t) (stream t) y hy
      rcases hsupport with hold | hcurrent
      · obtain ⟨s, hst, hs⟩ := ih hold
        exact ⟨s, by omega, hs⟩
      · exact ⟨t, by omega, hcurrent.symm⟩

theorem bufferState_entries_mem_of_presents
    {α : Type*} {b : ℕ}
    (G : BufferSetGenerator α b) (stream : ℕ → α)
    (L : Set α)
    (hP : GenLimit.Generic.Presents stream L)
    (t : ℕ) :
    ∀ y ∈ (bufferState G stream t).1, y ∈ L := by
  intro y hy
  obtain ⟨s, _hst, hs⟩ :=
    bufferState_entry_seen G stream hy
  rw [← hP]
  exact ⟨s, hs⟩

theorem target_mem_greedyBufferResidual
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (target : Fin k) (stream : ℕ → ℕ)
    (hP : GenLimit.Generic.Presents stream (langs target))
    (t : ℕ) :
    target ∈ bufferResidual langs
      (greedyBufferState b langs stream t) := by
  rw [mem_bufferResidual_iff]
  exact bufferState_entries_mem_of_presents
    (greedyBufferGenerator b langs) stream
      (langs target) hP t

theorem greedyBufferResidual_succ_subset
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) (t : ℕ) :
    bufferResidual langs
        (greedyBufferState b langs stream (t + 1)) ⊆
      bufferResidual langs
        (greedyBufferState b langs stream t) := by
  classical
  by_cases h : ShouldStore langs
      (greedyBufferState b langs stream t) (stream t)
  · have hval :=
      greedyBufferState_succ_of_shouldStore
        langs stream t h
    rw [bufferResidual_append langs
      (greedyBufferState b langs stream t)
      (greedyBufferState b langs stream (t + 1))
      (stream t) hval]
    exact bufferResidualAfter_subset langs _ _
  · rw [greedyBufferState_succ_of_not_shouldStore
      langs stream t h]

theorem greedyBufferResidual_antitone
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) :
    Antitone fun t =>
      bufferResidual langs
        (greedyBufferState b langs stream t) :=
  antitone_nat_of_succ_le
    (greedyBufferResidual_succ_subset langs stream)

theorem residual_nonempty_on_presentation
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (target : Fin k) (stream : ℕ → ℕ)
    (hP : GenLimit.Generic.Presents stream (langs target))
    (t : ℕ) :
    (bufferResidual langs
      (greedyBufferState b langs stream t)).Nonempty :=
  ⟨target,
    target_mem_greedyBufferResidual
      langs target stream hP t⟩

/-! ## Reindexing and padding a stabilized residual family -/

def residualCoreFor
    {k : ℕ} (langs : Fin k → Set ℕ)
    (R : Finset (Fin k)) (x : ℕ) : Set ℕ :=
  {y | ∀ i, i ∈ R → x ∈ langs i → y ∈ langs i}

noncomputable def paddedResidualIndex
    {k q : ℕ} (R : Finset (Fin k))
    (fallback : Fin k) (j : Fin q) : Fin k := by
  classical
  by_cases hj : j.1 < R.card
  · exact (R.equivFin.symm ⟨j.1, hj⟩).1
  · exact fallback

noncomputable def paddedResidualFamily
    {k q : ℕ} (langs : Fin k → Set ℕ)
    (R : Finset (Fin k)) (fallback : Fin k) :
    Fin q → Set ℕ :=
  fun j => langs (paddedResidualIndex R fallback j)

theorem paddedResidualIndex_mem
    {k q : ℕ} {R : Finset (Fin k)}
    {fallback : Fin k}
    (hfallback : fallback ∈ R)
    (j : Fin q) :
    paddedResidualIndex R fallback j ∈ R := by
  classical
  unfold paddedResidualIndex
  split_ifs
  · exact (R.equivFin.symm _).2
  · exact hfallback

theorem paddedResidualIndex_surjective_on
    {k q : ℕ} {R : Finset (Fin k)}
    {fallback : Fin k}
    (hcard : R.card ≤ q)
    {i : Fin k} (hi : i ∈ R) :
    ∃ j : Fin q, paddedResidualIndex R fallback j = i := by
  classical
  let ri : Fin R.card := R.equivFin ⟨i, hi⟩
  let j : Fin q := ⟨ri.1, ri.isLt.trans_le hcard⟩
  refine ⟨j, ?_⟩
  have hj : j.1 < R.card := ri.isLt
  simp only [paddedResidualIndex, dif_pos hj]
  exact congrArg Subtype.val
    (R.equivFin.symm_apply_apply ⟨i, hi⟩)

theorem finiteFamilyCore_paddedResidualFamily
    {k m : ℕ} (langs : Fin k → Set ℕ)
    (R : Finset (Fin k)) (fallback : Fin k)
    (hfallback : fallback ∈ R)
    (hcard : R.card ≤ m + 1) (x : ℕ) :
    finiteFamilyCore
        (paddedResidualFamily
          (q := m + 1) langs R fallback) x =
      residualCoreFor langs R x := by
  ext y
  constructor
  · intro hy i hi hxi
    obtain ⟨j, hj⟩ :=
      paddedResidualIndex_surjective_on
        (fallback := fallback) hcard hi
    have hxj :
        x ∈ paddedResidualFamily
          (q := m + 1) langs R fallback j := by
      simpa [paddedResidualFamily, hj] using hxi
    have hyj := hy j hxj
    simpa [paddedResidualFamily, hj] using hyj
  · intro hy j hxj
    exact hy (paddedResidualIndex R fallback j)
      (paddedResidualIndex_mem hfallback j) hxj

theorem bufferResidualCore_eq_residualCoreFor
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (M : BufferState ℕ b) (x : ℕ) :
    bufferResidualCore langs M x =
      residualCoreFor langs (bufferResidual langs M) x :=
  rfl

theorem canonicalDensityGenerator_padded_eq_buffer
    {k b m : ℕ} (langs : Fin k → Set ℕ)
    (M : BufferState ℕ b) (fallback : Fin k)
    (hfallback : fallback ∈ bufferResidual langs M)
    (hcard : (bufferResidual langs M).card ≤ m + 1)
    (x : ℕ) :
    canonicalDensityGenerator
        (paddedResidualFamily (q := m + 1) langs
          (bufferResidual langs M) fallback) x =
      bufferCanonicalOutput langs M x := by
  classical
  unfold canonicalDensityGenerator bufferCanonicalOutput
  rw [finiteFamilyCore_paddedResidualFamily
    langs (bufferResidual langs M) fallback
      hfallback hcard x]
  rfl

@[simp] theorem bufferOutputAt_greedyBufferGenerator
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) (t : ℕ) :
    bufferOutputAt (greedyBufferGenerator b langs) stream t =
      bufferCanonicalOutput langs
        (greedyBufferState b langs stream t) (stream t) :=
  rfl

theorem greedyBufferGenerator_succeeds
    {k : ℕ} (b : ℕ) (langs : Fin k → Set ℕ) :
    ∀ a, IsRepetitionFreeBufferGeneratorOn
      (greedyBufferGenerator b langs) (langs a) := by
  intro target stream hstream hP
  obtain ⟨T, hstable⟩ :=
    greedyBufferState_eventually_constant
      (b := b) langs stream
  let M := greedyBufferState b langs stream T
  have htarget :
      target ∈ bufferResidual langs M := by
    exact target_mem_greedyBufferResidual
      langs target stream hP T
  have hcard :
      (bufferResidual langs M).card ≤ k := by
    simpa using Finset.card_le_card
      (show bufferResidual langs M ⊆
        (Finset.univ : Finset (Fin k)) from
          Finset.subset_univ _)
  cases k with
  | zero => exact Fin.elim0 target
  | succ m =>
      let residualLangs : Fin (m + 1) → Set ℕ :=
        paddedResidualFamily langs
          (bufferResidual langs M) target
      obtain ⟨target', htarget'⟩ :=
        paddedResidualIndex_surjective_on
          (fallback := target) hcard htarget
      have htargetLang :
          residualLangs target' = langs target := by
        simp [residualLangs, paddedResidualFamily, htarget']
      obtain ⟨TC, hCanonical⟩ :=
        canonicalDensityGenerator_succeeds residualLangs
          (langs target) ⟨target', htargetLang⟩
          stream hP
          (injective_finitelyRepeating hstream)
      refine ⟨max T TC, ?_⟩
      intro t ht
      have htT : T ≤ t :=
        (Nat.le_max_left T TC).trans ht
      have htC : TC ≤ t :=
        (Nat.le_max_right T TC).trans ht
      have hstate :
          greedyBufferState b langs stream t = M := by
        simpa [M] using hstable t htT
      rw [bufferOutputAt_greedyBufferGenerator,
        hstate,
        ← canonicalDensityGenerator_padded_eq_buffer
          langs M target htarget hcard]
      exact (hCanonical t htC).2

theorem greedyBuffer_frequently_sperner_dense_of_residual_card_le
    {k b n : ℕ} (langs : Fin k → Set ℕ)
    (target : Fin k) (K : OrderedLanguage)
    (hK : K.carrier = langs target)
    (stream : ℕ → ℕ)
    (hP : GenLimit.Generic.Presents stream K.carrier)
    (T : ℕ)
    (hstable : ∀ t, T ≤ t →
      greedyBufferState b langs stream t =
        greedyBufferState b langs stream T)
    (hcard :
      (bufferResidual langs
        (greedyBufferState b langs stream T)).card ≤ n + 1) :
    ∃ᶠ t : ℕ in atTop,
      1 / (Nat.choose n (n / 2) : ℝ) ≤
        K.upperDensity
          (bufferOutputAt
            (greedyBufferGenerator b langs) stream t) := by
  let M := greedyBufferState b langs stream T
  have hPtarget :
      GenLimit.Generic.Presents stream (langs target) := by
    simpa [hK] using hP
  have htarget :
      target ∈ bufferResidual langs M :=
    target_mem_greedyBufferResidual
      langs target stream hPtarget T
  let residualLangs : Fin (n + 1) → Set ℕ :=
    paddedResidualFamily langs
      (bufferResidual langs M) target
  obtain ⟨target', htarget'⟩ :=
    paddedResidualIndex_surjective_on
      (fallback := target) hcard htarget
  have htargetLang :
      residualLangs target' = langs target := by
    change
      langs
          (paddedResidualIndex
            (bufferResidual langs M) target target') =
        langs target
    rw [show paddedResidualIndex
          (bufferResidual langs M) target target' =
        target by simpa [M] using htarget']
  have hKresidual :
      K.carrier = residualLangs target' :=
    hK.trans htargetLang.symm
  have hFrequently :=
    canonicalDensityGenerator_frequently_sperner_dense
      residualLangs target' K hKresidual stream hP
  exact
    (hFrequently.and_eventually
      (eventually_ge_atTop T)).mono fun t ht => by
        have hstate :
            greedyBufferState b langs stream t = M := by
          simpa [M] using hstable t ht.2
        rw [bufferOutputAt_greedyBufferGenerator,
          hstate,
          ← canonicalDensityGenerator_padded_eq_buffer
            langs M target htarget hcard]
        exact ht.1

def residualIntersection
    {k : ℕ} (langs : Fin k → Set ℕ)
    (R : Finset (Fin k)) : Set ℕ :=
  {y | ∀ i, i ∈ R → y ∈ langs i}

theorem stabilized_nonfull_residualAfter_eq
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) (T t : ℕ)
    (hstable : ∀ u, T ≤ u →
      greedyBufferState b langs stream u =
        greedyBufferState b langs stream T)
    (hNonfull :
      (greedyBufferState b langs stream T).1.length < b)
    (ht : T ≤ t) :
    bufferResidualAfter langs
        (greedyBufferState b langs stream T) (stream t) =
      bufferResidual langs
        (greedyBufferState b langs stream T) := by
  classical
  let M := greedyBufferState b langs stream T
  have hstate :
      greedyBufferState b langs stream t = M := by
    simpa [M] using hstable t ht
  have hstateSucc :
      greedyBufferState b langs stream (t + 1) = M := by
    simpa [M] using hstable (t + 1) (by omega)
  have hNoStore :
      ¬ShouldStore langs M (stream t) := by
    intro hstore
    have hstoreAt :
        ShouldStore langs
          (greedyBufferState b langs stream t)
          (stream t) := by
      simpa [hstate] using hstore
    have hval :=
      greedyBufferState_succ_of_shouldStore
        langs stream t hstoreAt
    rw [hstate, hstateSucc] at hval
    have hlen := congrArg List.length hval
    simp at hlen
  have hNotStrict :
      ¬bufferResidualAfter langs M (stream t) ⊂
        bufferResidual langs M := by
    intro hstrict
    exact hNoStore ⟨by simpa [M] using hNonfull, hstrict⟩
  apply Finset.Subset.antisymm
  · exact bufferResidualAfter_subset langs M (stream t)
  · by_contra hnotSubset
    apply hNotStrict
    rw [Finset.ssubset_iff_subset_ne]
    refine
      ⟨bufferResidualAfter_subset langs M (stream t), ?_⟩
    intro heq
    apply hnotSubset
    intro i hi
    rw [heq]
    exact hi

theorem stabilized_nonfull_stream_mem_residual
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (stream : ℕ → ℕ) (T t : ℕ)
    (hstable : ∀ u, T ≤ u →
      greedyBufferState b langs stream u =
        greedyBufferState b langs stream T)
    (hNonfull :
      (greedyBufferState b langs stream T).1.length < b)
    (ht : T ≤ t) :
    ∀ i ∈ bufferResidual langs
        (greedyBufferState b langs stream T),
      stream t ∈ langs i := by
  intro i hi
  have hEq :=
    stabilized_nonfull_residualAfter_eq
      langs stream T t hstable hNonfull ht
  have hiAfter :
      i ∈ bufferResidualAfter langs
        (greedyBufferState b langs stream T) (stream t) := by
    rw [hEq]
    exact hi
  have hinfo :
      i ∈ bufferResidual langs
          (greedyBufferState b langs stream T) ∧
        stream t ∈ langs i := by
    simpa [bufferResidualAfter] using hiAfter
  exact hinfo.2

theorem bufferResidualCore_eq_intersection_of_all_mem
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (M : BufferState ℕ b) (x : ℕ)
    (hx : ∀ i ∈ bufferResidual langs M, x ∈ langs i) :
    bufferResidualCore langs M x =
      residualIntersection langs (bufferResidual langs M) := by
  ext y
  constructor
  · intro hy i hi
    exact hy i hi (hx i hi)
  · intro hy i hi _hxi
    exact hy i hi

theorem residualIntersection_upperDensity_eq_one_of_tail
    {k : ℕ} (langs : Fin k → Set ℕ)
    (R : Finset (Fin k)) (K : OrderedLanguage)
    (stream : ℕ → ℕ)
    (hP : GenLimit.Generic.Presents stream K.carrier)
    (T : ℕ)
    (hTail :
      ∀ t, T ≤ t → stream t ∈ residualIntersection langs R) :
    K.upperDensity (residualIntersection langs R) = 1 := by
  let finitePrefix : Set ℕ :=
    Set.range fun s : Fin T => stream s
  have hprefixFinite : finitePrefix.Finite :=
    Set.finite_range _
  have hcover :
      K.carrier ⊆
        residualIntersection langs R ∪ finitePrefix := by
    intro y hy
    rw [← hP] at hy
    obtain ⟨t, rfl⟩ := hy
    by_cases ht : T ≤ t
    · exact Or.inl (hTail t ht)
    · exact Or.inr
        ⟨⟨t, Nat.lt_of_not_ge ht⟩, rfl⟩
  have honeLe :
      (1 : ℝ) ≤ K.upperDensity
        (residualIntersection langs R) := by
    calc
      (1 : ℝ) =
          K.upperDensity K.carrier :=
        (orderedUpperDensity_carrier_eq_one K).symm
      _ ≤ K.upperDensity
          (residualIntersection langs R ∪ finitePrefix) :=
        orderedUpperDensity_mono K hcover
      _ ≤ K.upperDensity (residualIntersection langs R) +
          K.upperDensity finitePrefix :=
        orderedUpperDensity_union_le K _ _
      _ = K.upperDensity (residualIntersection langs R) := by
        rw [orderedUpperDensity_finite_eq_zero
          K hprefixFinite, add_zero]
  exact le_antisymm
    (orderedUpperDensity_le_one K _) honeLe

theorem greedyBuffer_eventually_density_one_of_stable_nonfull
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (K : OrderedLanguage) (stream : ℕ → ℕ)
    (hstream : Function.Injective stream)
    (hP : GenLimit.Generic.Presents stream K.carrier)
    (T : ℕ)
    (hstable : ∀ t, T ≤ t →
      greedyBufferState b langs stream t =
        greedyBufferState b langs stream T)
    (hNonfull :
      (greedyBufferState b langs stream T).1.length < b) :
    ∀ t, T ≤ t →
      K.upperDensity
          (bufferOutputAt
            (greedyBufferGenerator b langs) stream t) = 1 := by
  let M := greedyBufferState b langs stream T
  let R := bufferResidual langs M
  have hTail :
      ∀ t, T ≤ t →
        stream t ∈ residualIntersection langs R := by
    intro t ht i hi
    exact stabilized_nonfull_stream_mem_residual
      langs stream T t hstable hNonfull ht i hi
  have hIntersectionDensity :
      K.upperDensity (residualIntersection langs R) = 1 :=
    residualIntersection_upperDensity_eq_one_of_tail
      langs R K stream hP T hTail
  have hTailInfinite :
      (Set.range fun s : ℕ => stream (T + s)).Infinite := by
    apply Set.infinite_range_of_injective
    intro s u hsu
    apply Nat.add_left_cancel
    exact hstream hsu
  have hIntersectionInfinite :
      (residualIntersection langs R).Infinite := by
    apply hTailInfinite.mono
    rintro _ ⟨s, rfl⟩
    exact hTail (T + s) (by omega)
  intro t ht
  have hstate :
      greedyBufferState b langs stream t = M := by
    simpa [M] using hstable t ht
  have hCurrent :
      ∀ i ∈ bufferResidual langs M,
        stream t ∈ langs i := by
    simpa [M] using
      stabilized_nonfull_stream_mem_residual
        langs stream T t hstable hNonfull ht
  have hCore :
      bufferResidualCore langs M (stream t) =
        residualIntersection langs R := by
    simpa [R] using
      bufferResidualCore_eq_intersection_of_all_mem
        langs M (stream t) hCurrent
  have hCoreInfinite :
      (bufferResidualCore langs M (stream t)).Infinite := by
    rw [hCore]
    exact hIntersectionInfinite
  rw [bufferOutputAt_greedyBufferGenerator, hstate]
  unfold bufferCanonicalOutput
  rw [if_pos hCoreInfinite, hCore]
  exact hIntersectionDensity

/-! ## Theorem 4.15 -/

noncomputable def adaptiveBufferLowerValue
    (k b : ℕ) : ℝ :=
  if b ≤ k - 3 then
    1 /
      (Nat.choose (k - b - 1)
        ((k - b - 1) / 2) : ℝ)
  else
    1

theorem greedyBuffer_runDensity_one_of_stable_nonfull
    {k b : ℕ} (langs : Fin k → Set ℕ)
    (K : OrderedLanguage) (stream : ℕ → ℕ)
    (hstream : Function.Injective stream)
    (hP : GenLimit.Generic.Presents stream K.carrier)
    (T : ℕ)
    (hstable : ∀ t, T ≤ t →
      greedyBufferState b langs stream t =
        greedyBufferState b langs stream T)
    (hNonfull :
      (greedyBufferState b langs stream T).1.length < b) :
    1 ≤ bufferRunUpperDensity K
      (greedyBufferGenerator b langs) stream := by
  have hEventually :
      ∀ᶠ t : ℕ in atTop,
        K.upperDensity
            (bufferOutputAt
              (greedyBufferGenerator b langs) stream t) = 1 := by
    filter_upwards [eventually_ge_atTop T] with t ht
    exact greedyBuffer_eventually_density_one_of_stable_nonfull
      langs K stream hstream hP T hstable hNonfull t ht
  apply bufferRunUpperDensity_ge_of_frequently
  exact hEventually.frequently.mono fun _ ht => ht.ge

theorem adaptiveBuffer_low_regime_guaranteed
    (k b : ℕ) (hk : 1 ≤ k) (hb : b ≤ k - 3) :
    BufferUpperDensityGuarantee k b
      (1 /
        (Nat.choose (k - b - 1)
          ((k - b - 1) / 2) : ℝ)) := by
  intro langs _hInjective _hInfinite
  refine
    ⟨greedyBufferGenerator b langs,
      greedyBufferGenerator_succeeds b langs, ?_⟩
  intro target K hK stream hstream hP
  obtain ⟨T, hstable⟩ :=
    greedyBufferState_eventually_constant
      (b := b) langs stream
  let M := greedyBufferState b langs stream T
  by_cases hFull : M.1.length = b
  · have hBound :=
      greedyBuffer_residual_length_bound
        (b := b) langs stream T
    have hcard :
        (bufferResidual langs M).card ≤ k - b := by
      simpa [M, hFull] using
        (Nat.le_sub_of_add_le hBound)
    have hq : 1 ≤ k - b := by
      omega
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hq)
    have hFrequently :
        ∃ᶠ t : ℕ in atTop,
          1 / (Nat.choose n (n / 2) : ℝ) ≤
            K.upperDensity
              (bufferOutputAt
                (greedyBufferGenerator b langs) stream t) := by
      apply
        greedyBuffer_frequently_sperner_dense_of_residual_card_le
          langs target K hK stream hP T hstable
      simpa [M, hn] using hcard
    apply bufferRunUpperDensity_ge_of_frequently
    simpa [hn] using hFrequently
  · have hNonfull : M.1.length < b := by
      exact lt_of_le_of_ne M.2 hFull
    have hRunOne :
        1 ≤ bufferRunUpperDensity K
          (greedyBufferGenerator b langs) stream :=
      greedyBuffer_runDensity_one_of_stable_nonfull
        langs K stream hstream hP T hstable
          (by simpa [M] using hNonfull)
    have hValueLeOne :
        1 /
            (Nat.choose (k - b - 1)
              ((k - b - 1) / 2) : ℝ) ≤
          1 := by
      simpa [memorylessSpernerValue] using
        (memorylessSpernerValue_mem_Icc (k - b)).2
    exact hValueLeOne.trans hRunOne

theorem adaptiveBuffer_high_regime_guaranteed
    (k b : ℕ) (hk : 1 ≤ k) (hb : k - 2 ≤ b) :
    BufferUpperDensityGuarantee k b 1 := by
  intro langs _hInjective _hInfinite
  refine
    ⟨greedyBufferGenerator b langs,
      greedyBufferGenerator_succeeds b langs, ?_⟩
  intro target K hK stream hstream hP
  obtain ⟨T, hstable⟩ :=
    greedyBufferState_eventually_constant
      (b := b) langs stream
  let M := greedyBufferState b langs stream T
  by_cases hFull : M.1.length = b
  · have hBound :=
      greedyBuffer_residual_length_bound
        (b := b) langs stream T
    have hcard :
        (bufferResidual langs M).card ≤ 2 := by
      dsimp [M] at hFull ⊢
      omega
    have hFrequently :
        ∃ᶠ t : ℕ in atTop,
          1 ≤ K.upperDensity
            (bufferOutputAt
              (greedyBufferGenerator b langs) stream t) := by
      simpa using
        greedyBuffer_frequently_sperner_dense_of_residual_card_le
          (n := 1) langs target K hK stream hP
            T hstable (by simpa [M] using hcard)
    exact bufferRunUpperDensity_ge_of_frequently
      K (greedyBufferGenerator b langs) stream hFrequently
  · have hNonfull : M.1.length < b :=
      lt_of_le_of_ne M.2 hFull
    exact greedyBuffer_runDensity_one_of_stable_nonfull
      langs K stream hstream hP T hstable
        (by simpa [M] using hNonfull)

theorem adaptiveBufferLowerValue_guaranteed
    (k b : ℕ) (hk : 1 ≤ k) :
    BufferUpperDensityGuarantee k b
      (adaptiveBufferLowerValue k b) := by
  unfold adaptiveBufferLowerValue
  split_ifs with hb
  · exact adaptiveBuffer_low_regime_guaranteed
      k b hk hb
  · apply adaptiveBuffer_high_regime_guaranteed
      k b hk
    omega

theorem adaptiveBufferLowerValue_admissible
    (k b : ℕ) (hk : 1 ≤ k) :
    adaptiveBufferLowerValue k b ∈
      bufferAdmissibleUpperDensities k b := by
  refine ⟨?_, adaptiveBufferLowerValue_guaranteed k b hk⟩
  unfold adaptiveBufferLowerValue
  split_ifs
  · simpa [memorylessSpernerValue] using
      memorylessSpernerValue_mem_Icc (k - b)
  · exact ⟨by norm_num, le_rfl⟩

/-- Theorem 4.15 with its two source regimes, including the actual minimax
supremum and outer run `limsup`. -/
theorem theorem_4_15_adaptive_buffer_lower_bound
    (k b : ℕ) (hk : 1 ≤ k) :
    adaptiveBufferLowerValue k b ≤
      bufferMinimaxUpperDensity k b := by
  unfold bufferMinimaxUpperDensity
  exact le_csSup
    ⟨1, fun σ hσ => hσ.1.2⟩
    (adaptiveBufferLowerValue_admissible k b hk)

end GenLimit.BoundedMemory
