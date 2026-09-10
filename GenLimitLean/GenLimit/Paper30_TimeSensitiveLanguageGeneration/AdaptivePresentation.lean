import GenLimit.Paper30_TimeSensitiveLanguageGeneration.OnlineTotalizedGCG
import GenLimit.Paper30_TimeSensitiveLanguageGeneration.TurnTakingUpperBound
import GenLimit.Support.Asymptotics.NatLog
import Mathlib.Data.Nat.Log

/-!
# Sparse adaptive presentation for the half-density upper bound

This module implements the Kleinberg--Wei turn-taking adversary needed by
P30 Theorem 4.  Ordinary rounds announce the least target-ranked point not
previously used by either player.  At the sparse rounds `2^(n+1)`, the
adversary catches up with target-valued generator output number `n`.

The catch-up schedule makes the resulting stream an exact presentation while
using only logarithmically many exceptional rounds in each prefix.  The joint
run is defined from the finite-history GCG step, so the adversary never reads
the current or future generator output.
-/

namespace GenLimit.TimeSensitive

open Filter
open GenLimit.KleinbergWei

/-- The finite set already owned by either player before the next round. -/
def adaptiveUsed (state : OnlineTotalizedGCGState) : Finset ℕ :=
  state.observations.toFinset ∪ state.outputs.toFinset

def UnusedTargetRank
    (O : OrderedLanguage) (used : Finset ℕ) (r : ℕ) : Prop :=
  O.enumeration r ∉ used

theorem exists_unusedTargetRank
    (O : OrderedLanguage) (used : Finset ℕ) :
    ∃ r, UnusedTargetRank O used r := by
  classical
  by_contra h
  push_neg at h
  have hsubset :
      (Finset.range (used.card + 1)).image O.enumeration ⊆ used := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    exact not_not.mp (h r)
  have hcard :
      ((Finset.range (used.card + 1)).image O.enumeration).card =
        used.card + 1 := by
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro a _ b _ hab
      exact O.enumeration_injective hab
  have := Finset.card_le_card hsubset
  rw [hcard] at this
  omega

/-- Least target rank not yet used by either player. -/
noncomputable def leastUnusedTargetRank
    (O : OrderedLanguage) (used : Finset ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_unusedTargetRank O used)

noncomputable def leastUnusedTarget
    (O : OrderedLanguage) (used : Finset ℕ) : ℕ :=
  O.enumeration (leastUnusedTargetRank O used)

theorem leastUnusedTargetRank_spec
    (O : OrderedLanguage) (used : Finset ℕ) :
    UnusedTargetRank O used (leastUnusedTargetRank O used) := by
  classical
  exact Nat.find_spec (exists_unusedTargetRank O used)

theorem leastUnusedTargetRank_min
    (O : OrderedLanguage) (used : Finset ℕ) {r : ℕ}
    (hr : UnusedTargetRank O used r) :
    leastUnusedTargetRank O used ≤ r := by
  classical
  exact Nat.find_min' (exists_unusedTargetRank O used) hr

theorem leastUnusedTarget_mem
    (O : OrderedLanguage) (used : Finset ℕ) :
    leastUnusedTarget O used ∈ O.carrier := by
  rw [← O.range_enumeration]
  exact ⟨leastUnusedTargetRank O used, rfl⟩

theorem leastUnusedTarget_fresh
    (O : OrderedLanguage) (used : Finset ℕ) :
    leastUnusedTarget O used ∉ used :=
  leastUnusedTargetRank_spec O used

/-- Round `2^(n+1)` is reserved for catching up output number `n`. -/
def IsCatchupRound (t : ℕ) : Prop :=
  ∃ n, t = 2 ^ (n + 1)

noncomputable instance (t : ℕ) : Decidable (IsCatchupRound t) :=
  Classical.propDecidable _

noncomputable def catchupIndex (t : ℕ) : ℕ :=
  if h : IsCatchupRound t then Nat.find h else 0

theorem catchupIndex_spec {t : ℕ} (h : IsCatchupRound t) :
    t = 2 ^ (catchupIndex t + 1) := by
  simp only [catchupIndex, dif_pos h]
  exact Nat.find_spec h

theorem catchupIndex_scheduled (n : ℕ) :
    catchupIndex (2 ^ (n + 1)) = n := by
  have hcatch : IsCatchupRound (2 ^ (n + 1)) := ⟨n, rfl⟩
  have hspec := catchupIndex_spec hcatch
  apply Nat.succ.inj
  apply Nat.pow_right_injective (a := 2) (by omega)
  simpa using hspec.symm

theorem index_lt_scheduled_time (n : ℕ) :
    n < 2 ^ (n + 1) := by
  exact n.lt_two_pow_self.trans_le
    (Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.le_succ n))

/-- The target-valued output scheduled at a catch-up round, with the least
unused target point as a harmless fallback. -/
noncomputable def catchupCandidate
    (O : OrderedLanguage) (state : OnlineTotalizedGCGState) (t : ℕ) : ℕ :=
  state.outputs.getD (catchupIndex t)
    (leastUnusedTarget O (adaptiveUsed state))

/-- One adaptive adversary announcement. -/
noncomputable def adaptiveAnnouncement
    (O : OrderedLanguage) (state : OnlineTotalizedGCGState) (t : ℕ) : ℕ := by
  classical
  let fallback := leastUnusedTarget O (adaptiveUsed state)
  if hcatch : IsCatchupRound t then
    let candidate := catchupCandidate O state t
    exact if candidate ∈ O.carrier then candidate else fallback
  else
    exact fallback

/-- Joint adversary/GCG run after `t` complete rounds. -/
noncomputable def adaptiveGCGRun
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) :
    ℕ → OnlineTotalizedGCGState
  | 0 => OnlineTotalizedGCGState.initial
  | t + 1 =>
      let old := adaptiveGCGRun F O t
      let current := adaptiveAnnouncement O old t
      onlineTotalizedGCGStep F t old current

noncomputable def adaptivePresentation
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) : ℕ :=
  adaptiveAnnouncement O (adaptiveGCGRun F O t) t

noncomputable def adaptiveGCGOutput
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) : ℕ :=
  onlineTotalizedRoundOutput F t (adaptiveGCGRun F O t)
    (adaptivePresentation F O t)

@[simp] theorem adaptiveGCGRun_zero
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) :
    adaptiveGCGRun F O 0 = OnlineTotalizedGCGState.initial := rfl

@[simp] theorem adaptiveGCGRun_succ
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) :
    adaptiveGCGRun F O (t + 1) =
      onlineTotalizedGCGStep F t (adaptiveGCGRun F O t)
        (adaptivePresentation F O t) := rfl

theorem adaptiveGCGRun_observations_succ
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) :
    (adaptiveGCGRun F O (t + 1)).observations =
      (adaptiveGCGRun F O t).observations ++
        [adaptivePresentation F O t] := by
  rfl

theorem adaptiveGCGRun_outputs_succ
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) :
    (adaptiveGCGRun F O (t + 1)).outputs =
      (adaptiveGCGRun F O t).outputs ++ [adaptiveGCGOutput F O t] := by
  rfl

theorem adaptiveGCGRun_observations_eq
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) :
    (adaptiveGCGRun F O t).observations =
      (List.range t).map (adaptivePresentation F O) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [adaptiveGCGRun_observations_succ, ih]
      simp [List.range_succ]

theorem adaptiveGCGRun_outputs_eq
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) :
    (adaptiveGCGRun F O t).outputs =
      (List.range t).map (adaptiveGCGOutput F O) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [adaptiveGCGRun_outputs_succ, ih]
      simp [List.range_succ]

theorem adaptiveGCGRun_eq_onlineRun
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) :
    adaptiveGCGRun F O t =
      onlineTotalizedGCGRun F (adaptivePresentation F O) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [adaptiveGCGRun_succ, onlineTotalizedGCGRun_succ, ← ih]

/-- The jointly defined output is exactly the repaired GCG output on the
jointly defined adaptive presentation. -/
theorem adaptiveGCGOutput_eq_totalized
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) :
    adaptiveGCGOutput F O t =
      totalizedGCGOutput F (adaptivePresentation F O) t := by
  rw [← onlineTotalizedGCGOutput_eq]
  unfold adaptiveGCGOutput onlineTotalizedGCGOutput
  rw [← adaptiveGCGRun_eq_onlineRun]

theorem adaptivePresentation_mem_target
    (F : CanonicallyOrderedFamily) (O : OrderedLanguage) (t : ℕ) :
    adaptivePresentation F O t ∈ O.carrier := by
  classical
  unfold adaptivePresentation adaptiveAnnouncement
  by_cases hcatch : IsCatchupRound t
  · simp only [dif_pos hcatch]
    by_cases hcandidate :
        catchupCandidate O (adaptiveGCGRun F O t) t ∈ O.carrier
    · simp [hcandidate]
    · simp [hcandidate, leastUnusedTarget_mem]
  · simp [hcatch, leastUnusedTarget_mem]

end GenLimit.TimeSensitive
