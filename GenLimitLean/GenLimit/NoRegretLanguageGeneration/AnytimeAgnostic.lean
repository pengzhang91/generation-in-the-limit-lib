import GenLimit.NoRegretLanguageGeneration.Plays
import GenLimit.NoRegretLanguageGeneration.AnytimeRealizable
import GenLimit.NoRegretLanguageGeneration.Sublinear

namespace PredictionToGeneration

/-- Copy replies pad a virtual play without changing any comparator's regret. -/
def copyPadding (G : Generator X) : Nat → List X → List X
  | 0, xs => xs
  | n+1, xs => copyPadding G n (G.output xs :: xs)

theorem copyPadding_length (G : Generator X) (n : Nat) (xs : List X) :
    (copyPadding G n xs).length = xs.length + n := by
  induction n generalizing xs with
  | zero => simp [copyPadding]
  | succ n ih => simp [copyPadding, ih]; omega

theorem copyPadding_nodup (G : Generator X) (n : Nat) (xs : List X)
    (hn : xs.Nodup) : (copyPadding G n xs).Nodup := by
  induction n generalizing xs with
  | zero => exact hn
  | succ n ih => exact ih _ (List.nodup_cons.mpr ⟨G.fresh xs, hn⟩)

theorem copyPadding_regret (G : Generator X) (n : Nat) (xs : List X)
    (h : Hypothesis X) : regret h (G.play (copyPadding G n xs)) = regret h (G.play xs) := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    rw [copyPadding, ih]
    exact regret_copy h (G.output xs) (G.play xs)

/-- Unlike arbitrary extensions, copy padding transfers signed terminal bounds to prefixes. -/
theorem agnostic_prefix_of_horizon (G : Generator X) (H : HypothesisClass X)
    (N : Nat) (B : Int)
    (hb : ∀ xs, xs.Nodup → xs.length = N → ∀ h, H h → regret h (G.play xs) ≤ B)
    (xs : List X) (hn : xs.Nodup) (hlen : xs.length ≤ N) :
    ∀ h, H h → regret h (G.play xs) ≤ B := by
  intro h hh
  have hpad := hb (copyPadding G (N-xs.length) xs) (copyPadding_nodup G _ xs hn)
    (by rw [copyPadding_length]; omega) h hh
  simpa [copyPadding_regret] using hpad

private theorem nodup_subset_length {xs ys : List X} (hn : xs.Nodup) (hs : xs ⊆ ys) :
    xs.length ≤ ys.length := by
  classical
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
    have hmem : x ∈ ys := hs (by simp)
    have hsub : xs ⊆ ys.erase x := by
      intro z hz
      have hne : z ≠ x := by intro he; subst z; exact hnot hz
      exact (List.mem_erase_of_ne hne).mpr (hs (by simp [hz]))
    have hl := ih htail hsub
    rw [List.length_erase_of_mem hmem] at hl
    have hp : 0 < ys.length := List.length_pos_of_mem hmem
    simp only [List.length_cons]
    omega

/-- Flush illegal proposals as zero-regret copies. The final virtual history
remains a duplicate-free subset of the real history, proving the horizon count. -/
theorem virtual_flush_exists (G : Generator X) (real : List X) (xs : List X)
    (hn : xs.Nodup) (hs : xs ⊆ real) :
    ∃ ys, ys.Nodup ∧ ys ⊆ real ∧
      (∀ h, regret h (G.play ys) = regret h (G.play xs)) ∧ G.output ys ∉ real := by
  classical
  have aux : ∀ k, ∀ xs : List X, real.length-xs.length = k →
      xs.Nodup → xs ⊆ real →
      ∃ ys, ys.Nodup ∧ ys ⊆ real ∧
        (∀ h, regret h (G.play ys) = regret h (G.play xs)) ∧ G.output ys ∉ real := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro xs he hn hs
      by_cases hz : G.output xs ∈ real
      · have hn' : (G.output xs::xs).Nodup := List.nodup_cons.mpr ⟨G.fresh xs, hn⟩
        have hs' : G.output xs::xs ⊆ real := by
          intro z hm
          obtain rfl | hm := List.mem_cons.mp hm
          · exact hz
          · exact hs hm
        have hlen := nodup_subset_length hn' hs'
        have hlt : real.length-(G.output xs::xs).length < k := by
          simp only [List.length_cons] at hlen ⊢
          omega
        obtain ⟨ys, hy, hsub, hr, hout⟩ := ih _ hlt _ rfl hn' hs'
        refine ⟨ys, hy, hsub, fun h => ?_, hout⟩
        rw [hr h]
        exact regret_copy h (G.output xs) (G.play xs)
      · exact ⟨xs, hn, hs, fun _ => rfl, hz⟩
  exact aux _ xs rfl hn hs

/-- A chosen flush is mathematical (classical), not asserted to be efficient. -/
noncomputable def virtualFlush (G : Generator X) (real xs : List X)
    (hn : xs.Nodup) (hs : xs ⊆ real) : List X :=
  Classical.choose (virtual_flush_exists G real xs hn hs)

theorem virtualFlush_spec (G : Generator X) (real xs : List X)
    (hn : xs.Nodup) (hs : xs ⊆ real) :
    (virtualFlush G real xs hn hs).Nodup ∧ virtualFlush G real xs hn hs ⊆ real ∧
    (∀ h, regret h (G.play (virtualFlush G real xs hn hs)) = regret h (G.play xs)) ∧
    G.output (virtualFlush G real xs hn hs) ∉ real :=
  Classical.choose_spec (virtual_flush_exists G real xs hn hs)

theorem virtualFlush_length (G : Generator X) (real xs : List X)
    (hn : xs.Nodup) (hs : xs ⊆ real) :
    (virtualFlush G real xs hn hs).length ≤ real.length :=
  nodup_subset_length (virtualFlush_spec G real xs hn hs).1
    (virtualFlush_spec G real xs hn hs).2.1

/-- At the start of a real round, the active epoch's virtual observations are
all distinct and drawn from the actual observations so far. -/
private noncomputable def epochState (Gs : Nat → Generator X) (idx : Nat → Nat) :
    (xs : List X) → xs.Nodup → {ys : List X // ys.Nodup ∧ ys ⊆ xs}
  | [], _ => ⟨[], by simp⟩
  | x::xs, hn => by
    classical
    have hx := (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    let prev := epochState Gs idx xs ht
    let flushed := virtualFlush (Gs (idx xs.length)) xs prev.val prev.property.1 prev.property.2
    have spec := virtualFlush_spec (Gs (idx xs.length)) xs prev.val prev.property.1 prev.property.2
    by_cases he : idx (xs.length+1) = idx xs.length
    · refine ⟨x::flushed, List.nodup_cons.mpr ⟨?_, spec.1⟩, ?_⟩
      · intro hm
        exact hx (spec.2.1 hm)
      · intro y hy
        obtain rfl | hy := List.mem_cons.mp hy
        · simp
        · exact List.mem_cons.mpr (Or.inr (spec.2.1 hy))
    · exact ⟨[], by simp⟩

private noncomputable def epochFlushed (Gs : Nat → Generator X) (idx : Nat → Nat)
    (xs : List X) (hn : xs.Nodup) : List X :=
  let st := epochState Gs idx xs hn
  virtualFlush (Gs (idx xs.length)) xs st.val st.property.1 st.property.2

private theorem epochFlushed_spec (Gs : Nat → Generator X) (idx : Nat → Nat)
    (xs : List X) (hn : xs.Nodup) :
    (epochFlushed Gs idx xs hn).Nodup ∧ epochFlushed Gs idx xs hn ⊆ xs ∧
    (∀ h, regret h ((Gs (idx xs.length)).play (epochFlushed Gs idx xs hn)) =
      regret h ((Gs (idx xs.length)).play (epochState Gs idx xs hn).val)) ∧
    (Gs (idx xs.length)).output (epochFlushed Gs idx xs hn) ∉ xs := by
  exact virtualFlush_spec _ _ _ (epochState Gs idx xs hn).property.1
    (epochState Gs idx xs hn).property.2

/-- Restart each finite-horizon generator at its epoch, simulating illegal
proposals by zero-regret copies. No labels or validity bits are observed. -/
noncomputable def agnosticEpochGenerator (Gs : Nat → Generator X) (idx : Nat → Nat) :
    Generator X where
  output xs := by
    classical
    exact if hn : xs.Nodup then (Gs (idx xs.length)).output (epochFlushed Gs idx xs hn)
      else (Gs 0).output xs
  fresh xs := by
    classical
    split
    · exact (epochFlushed_spec Gs idx xs _).2.2.2
    · exact (Gs 0).fresh xs

private theorem agnosticEpochGenerator_output (Gs : Nat → Generator X) (idx : Nat → Nat)
    (xs : List X) (hn : xs.Nodup) :
    (agnosticEpochGenerator Gs idx).output xs =
      (Gs (idx xs.length)).output (epochFlushed Gs idx xs hn) := by
  classical
  simp [agnosticEpochGenerator, hn]

private theorem epochState_same (Gs : Nat → Generator X) (idx : Nat → Nat)
    (x : X) (xs : List X) (hn : (x::xs).Nodup)
    (he : idx (xs.length+1) = idx xs.length) :
    (epochState Gs idx (x::xs) hn).val =
      x::epochFlushed Gs idx xs (List.nodup_cons.mp hn).2 := by
  classical
  simp [epochState, he, epochFlushed]

private theorem epochState_new (Gs : Nat → Generator X) (idx : Nat → Nat)
    (x : X) (xs : List X) (hn : (x::xs).Nodup)
    (he : idx (xs.length+1) ≠ idx xs.length) :
    (epochState Gs idx (x::xs) hn).val = [] := by
  classical
  simp [epochState, he]

private theorem epoch_regret_invariant (Gs : Nat → Generator X) (idx N C : Nat → Nat)
    (H : HypothesisClass X) (hmono : ∀ t, idx t ≤ idx (t+1))
    (hdeadline : ∀ t, t+1 ≤ N (idx t))
    (hbound : ∀ j xs, xs.Nodup → xs.length = N j →
      ∀ h, H h → regret h ((Gs j).play xs) ≤ (C j : Int))
    (xs : List X) (hn : xs.Nodup) (h : Hypothesis X) (hh : H h) :
    regret h ((agnosticEpochGenerator Gs idx).play xs) ≤
      (epochBudget C (idx xs.length) : Int) +
        regret h ((Gs (idx xs.length)).play (epochState Gs idx xs hn).val) := by
  induction xs with
  | nil => simp [Generator.play, epochState, regret, mistakes, demonstrationLoss]
  | cons x xs ih =>
    have ht := (List.nodup_cons.mp hn).2
    have hx := (List.nodup_cons.mp hn).1
    have hi := ih ht
    let old := Gs (idx xs.length)
    let vs := epochFlushed Gs idx xs ht
    have spec := epochFlushed_spec Gs idx xs ht
    have hv : (x::vs).Nodup := List.nodup_cons.mpr ⟨fun hm => hx (spec.2.1 hm), spec.1⟩
    have hlen : (x::vs).length ≤ N (idx xs.length) := by
      have hl := nodup_subset_length spec.1 spec.2.1
      have hd := hdeadline xs.length
      dsimp [vs]
      omega
    have hb := agnostic_prefix_of_horizon old H (N (idx xs.length)) (C (idx xs.length))
      (hbound (idx xs.length)) (x::vs) hv hlen h hh
    have hcopy := spec.2.2.1 h
    have hreal := regret_cons h ((agnosticEpochGenerator Gs idx).output xs) x
      ((agnosticEpochGenerator Gs idx).play xs)
    have hvirt := regret_cons h (old.output vs) x (old.play vs)
    rw [agnosticEpochGenerator_output Gs idx xs ht] at hreal
    have hbalance : regret h ((agnosticEpochGenerator Gs idx).play (x::xs)) =
        regret h ((agnosticEpochGenerator Gs idx).play xs) +
        regret h (old.play (x::vs)) -
        regret h (old.play (epochState Gs idx xs ht).val) := by
      simp only [Generator.play, regret_cons]
      rw [agnosticEpochGenerator_output Gs idx xs ht]
      dsimp [old, vs]
      rw [hcopy]
      omega
    by_cases he : idx (xs.length+1) = idx xs.length
    · rw [epochState_same Gs idx x xs hn he]
      simp only [List.length_cons, he]
      dsimp [old, vs] at hbalance
      omega
    · rw [epochState_new Gs idx x xs hn he]
      simp only [List.length_cons]
      change regret h ((agnosticEpochGenerator Gs idx).play (x::xs)) ≤
        (epochBudget C (idx (xs.length+1)) : Int) + 0
      have hm := hmono xs.length
      have hlt : idx xs.length + 1 ≤ idx (xs.length+1) := by omega
      have hsum := epochBudget_mono C hlt
      change epochBudget C (idx xs.length) + C (idx xs.length) ≤ _ at hsum
      dsimp [old] at hbalance hb
      omega

/-- A schedule-independent agnostic anytime theorem. Virtual copies give a
legal generator and transfer each terminal guarantee to every epoch prefix. -/
theorem agnostic_epoch_regret_bound (Gs : Nat → Generator X) (idx N C : Nat → Nat)
    (H : HypothesisClass X) (hmono : ∀ t, idx t ≤ idx (t+1))
    (hdeadline : ∀ t, t+1 ≤ N (idx t))
    (hbound : ∀ j xs, xs.Nodup → xs.length = N j →
      ∀ h, H h → regret h ((Gs j).play xs) ≤ (C j : Int))
    (xs : List X) (hn : xs.Nodup) (h : Hypothesis X) (hh : H h) :
    regret h ((agnosticEpochGenerator Gs idx).play xs) ≤
      (epochBudget C (idx xs.length+1) : Int) := by
  have hi := epoch_regret_invariant Gs idx N C H hmono hdeadline hbound xs hn h hh
  let st := epochState Gs idx xs hn
  have hlen : st.val.length ≤ N (idx xs.length) := by
    have hl := nodup_subset_length st.property.1 st.property.2
    have hd := hdeadline xs.length
    omega
  have hb := agnostic_prefix_of_horizon (Gs (idx xs.length)) H _ _
    (hbound (idx xs.length)) st.val st.property.1 hlen h hh
  change _ ≤ ((epochBudget C (idx xs.length) + C (idx xs.length) : Nat) : Int)
  dsimp [st] at hb
  omega

/-- Sharper endpoint form: charge the epoch of the last played round, without
charging a new epoch that is about to start. -/
theorem agnostic_epoch_nonempty_bound (Gs : Nat → Generator X) (idx N C : Nat → Nat)
    (H : HypothesisClass X) (hmono : ∀ t, idx t ≤ idx (t+1))
    (hdeadline : ∀ t, t+1 ≤ N (idx t))
    (hbound : ∀ j xs, xs.Nodup → xs.length = N j →
      ∀ h, H h → regret h ((Gs j).play xs) ≤ (C j : Int))
    (x : X) (xs : List X) (hn : (x::xs).Nodup) (h : Hypothesis X) (hh : H h) :
    regret h ((agnosticEpochGenerator Gs idx).play (x::xs)) ≤
      (epochBudget C (idx xs.length+1) : Int) := by
  have ht := (List.nodup_cons.mp hn).2
  have hx := (List.nodup_cons.mp hn).1
  have hi := epoch_regret_invariant Gs idx N C H hmono hdeadline hbound xs ht h hh
  let vs := epochFlushed Gs idx xs ht
  have spec := epochFlushed_spec Gs idx xs ht
  have hv : (x::vs).Nodup := List.nodup_cons.mpr ⟨fun hm => hx (spec.2.1 hm), spec.1⟩
  have hlen : (x::vs).length ≤ N (idx xs.length) := by
    have hl := nodup_subset_length spec.1 spec.2.1
    have hd := hdeadline xs.length
    dsimp [vs]
    omega
  have hb := agnostic_prefix_of_horizon (Gs (idx xs.length)) H _ _
    (hbound (idx xs.length)) (x::vs) hv hlen h hh
  have hcopy := spec.2.2.1 h
  simp only [Generator.play, regret_cons] at hb ⊢
  rw [agnosticEpochGenerator_output Gs idx xs ht]
  dsimp [vs] at hb
  rw [hcopy] at hb
  change _ ≤ ((epochBudget C (idx xs.length) + C (idx xs.length) : Nat) : Int)
  omega

/-- Quantitative agnostic horizon-to-anytime theorem for integer envelopes.
The factor four includes illegal-proposal simulation and arbitrary epoch prefixes. -/
theorem agnostic_horizon_to_anytime_nat (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) (b : Nat → Nat)
    (hmono : ∀ i j, i ≤ j → b i ≤ b j)
    (hunbounded : ∀ c, ∃ t, c < b t)
    (hpositive : ∀ t, 1 ≤ t → 1 ≤ b t)
    (hbound : ∀ t, SMF H t ≤ b t) :
    ∃ G : Generator X, ∀ xs, xs.Nodup → 1 ≤ xs.length →
      ∀ h, H h → regret h (G.play xs) ≤ (4 * b xs.length : Nat) := by
  classical
  let cap : Nat → Nat := fun j => Classical.choose (hunbounded (2 ^ j))
  have hcap : ∀ j, 2 ^ j < b (cap j) := fun j => Classical.choose_spec (hunbounded (2 ^ j))
  let N : Nat → Nat := fun j => thresholdMax (fun t => t = 0 ∨ b t ≤ 2 ^ j) (cap j)
  have hNcost : ∀ j, SMF H (N j) ≤ 2 ^ j := by
    intro j
    have hs := (thresholdMax_spec (fun t => t = 0 ∨ b t ≤ 2 ^ j) (Or.inl rfl) (cap j)).1
    change N j = 0 ∨ b (N j) ≤ 2 ^ j at hs
    rcases hs with he | he
    · rw [he]
      exact Nat.le_trans (smf_le_horizon H 0) (Nat.zero_le _)
    · exact Nat.le_trans (hbound _) he
  have hNcovers : ∀ t j, b t ≤ 2 ^ j → t ≤ N j := by
    intro t j ht
    have hc : t ≤ cap j := by
      by_cases hh : t ≤ cap j
      · exact hh
      · have hm := hmono (cap j) t (by omega)
        have hb := hcap j
        omega
    exact (thresholdMax_spec (fun t => t = 0 ∨ b t ≤ 2 ^ j) (Or.inl rfl) (cap j)).2 t hc (Or.inr ht)
  let family : Nat → Generator X := fun j => Classical.choose (smf_generator_attained H hu hne (N j))
  have hfamily : ∀ j xs, xs.Nodup → xs.length = N j → ∀ h, H h →
      regret h ((family j).play xs) ≤ (2 ^ j : Nat) := by
    intro j xs hn hl h hh
    have hb := (Classical.choose_spec (smf_generator_attained H hu hne (N j))) xs hn hl h hh
    change regret h ((family j).play xs) ≤ (SMF H (N j) : Int) at hb
    have hc := hNcost j
    omega
  let index : Nat → Nat := fun t => dyadicLevel (b (t+1))
  have hi : ∀ t, index t ≤ index (t+1) :=
    fun t => dyadicLevel_mono (hmono (t+1) (t+1+1) (by omega))
  have hd : ∀ t, t+1 ≤ N (index t) :=
    fun t => hNcovers (t+1) (index t) (dyadicLevel_covers (b (t+1)))
  refine ⟨agnosticEpochGenerator family index, ?_⟩
  intro xs hn hl h hh
  cases xs with
  | nil => simp at hl
  | cons x xs =>
    have hb := agnostic_epoch_nonempty_bound family index N (fun j => 2^j) H hi hd hfamily x xs hn h hh
    have he := epochBudget_dyadic (index xs.length+1)
    have hc := dyadicLevel_cost (b (xs.length+1)) (hpositive _ (by omega))
    change 2 ^ index xs.length ≤ 2 * b (xs.length+1) at hc
    rw [Nat.pow_succ] at he
    simp only [List.length_cons]
    omega

/-- A single anytime generator with a sublinear uniform signed-regret envelope. -/
def AgnosticNoRegret (H : HypothesisClass X) : Prop :=
  ∃ G : Generator X, ∃ r : Nat → Nat, NatSublinear r ∧
    ∀ xs, xs.Nodup → ∀ h, H h → regret h (G.play xs) ≤ (r xs.length : Int)

/-- Complete agnostic no-regret characterization in arithmetic little-o form. -/
theorem agnostic_no_regret_iff (H : HypothesisClass X) (hu : UUS H)
    (hne : ∃ h, H h) : AgnosticNoRegret H ↔ NatSublinear (SMF H) := by
  constructor
  · rintro ⟨G, r, hr, hb⟩ k
    obtain ⟨N, hN⟩ := hr k
    refine ⟨N, fun t ht => ?_⟩
    have hv := smf_le_of_generator_bound H hu hne t (r t) G
      (fun xs hn hl h hh => by simpa [hl] using hb xs hn h hh)
    have hv' : SMF H t ≤ r t := by omega
    exact Nat.le_trans (Nat.mul_le_mul_left k hv') (hN t ht)
  · intro hp
    let b := sublinearEnvelope (SMF H)
    have hm : ∀ i j, i ≤ j → b i ≤ b j :=
      sublinearEnvelope_mono (nat_mono_of_succ _ (smf_mono_succ H hu hne))
    obtain ⟨G, hg⟩ := agnostic_horizon_to_anytime_nat H hu hne b hm
      (sublinearEnvelope_unbounded _) (fun t _ => sublinearEnvelope_positive _ t)
      (le_sublinearEnvelope _)
    refine ⟨G, fun t => 4*b t, ?_, ?_⟩
    · intro k
      obtain ⟨N, hN⟩ := sublinearEnvelope_sublinear hp (k*4)
      exact ⟨N, fun t ht => by simpa [Nat.mul_assoc] using hN t ht⟩
    · intro xs hn h hh
      cases xs with
      | nil => exact Int.natCast_nonneg _
      | cons x xs => exact hg _ hn (by simp) h hh

end PredictionToGeneration
