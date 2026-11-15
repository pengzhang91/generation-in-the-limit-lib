import GenLimit.NoRegretLanguageGeneration.VCCounterexample
import GenLimit.NoRegretLanguageGeneration.ArbitraryProfiles

namespace PredictionToGeneration
open Classical

/-- Ordinary finite-set VC shattering: every Boolean labeling of the set is
realized by one hypothesis from the class. -/
def FinsetShatters (H : HypothesisClass X) (S : Finset X) : Prop :=
  ∀ labels : X → Bool, ∃ h, H h ∧ ∀ x ∈ S, h x = labels x

theorem finsetShatters_singleton_iff (H : HypothesisClass X) (x : X) :
    FinsetShatters H {x} ↔ (∃ h, H h ∧ h x = true) ∧ (∃ h, H h ∧ h x = false) := by
  constructor
  · intro hs
    obtain ⟨h, hh, ht⟩ := hs (fun _ => true)
    obtain ⟨g, hg, hf⟩ := hs (fun _ => false)
    exact ⟨⟨h, hh, ht x (by simp)⟩, ⟨g, hg, hf x (by simp)⟩⟩
  · rintro ⟨⟨h, hh, ht⟩, ⟨g, hg, hf⟩⟩ labels
    cases he : labels x with
    | false => exact ⟨g, hg, by intro y hy; have := Finset.mem_singleton.mp hy; subst y; exact hf.trans he.symm⟩
    | true => exact ⟨h, hh, by intro y hy; have := Finset.mem_singleton.mp hy; subst y; exact ht.trans he.symm⟩

theorem finsetShatters_pair_iff (H : HypothesisClass X) (x y : X) (hxy : x ≠ y) :
    FinsetShatters H {x,y} ↔ ∀ a b : Bool, ∃ h, H h ∧ h x = a ∧ h y = b := by
  constructor
  · intro hs a b
    obtain ⟨h, hh, hl⟩ := hs (fun z => if z = x then a else b)
    exact ⟨h, hh, by simpa using hl x (by simp), by simpa [Ne.symm hxy] using hl y (by simp)⟩
  · intro hs labels
    obtain ⟨h, hh, hx, hy⟩ := hs (labels x) (labels y)
    refine ⟨h, hh, ?_⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy

theorem finsetShatters_mono (H : HypothesisClass X) {S T : Finset X}
    (hST : S ⊆ T) (ht : FinsetShatters H T) : FinsetShatters H S := by
  intro labels
  obtain ⟨h, hh, ht⟩ := ht labels
  exact ⟨h, hh, fun x hx => ht x (hST hx)⟩

theorem no_pair_iff_shattered_card_le_one (H : HypothesisClass X) :
    (∀ x y, x ≠ y → ¬ (∀ a b : Bool, ∃ h, H h ∧ h x = a ∧ h y = b)) ↔
      ∀ S : Finset X, FinsetShatters H S → S.card ≤ 1 := by
  constructor
  · intro hpair S hs
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hxy
    have hp : FinsetShatters H {x,y} := finsetShatters_mono H (by intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl; exact hx; exact hy) hs
    exact hpair x y hxy ((finsetShatters_pair_iff H x y hxy).mp hp)
  · intro hcard x y hxy hs
    have hc := hcard {x,y} ((finsetShatters_pair_iff H x y hxy).mpr hs)
    simp [hxy] at hc

/-- The earlier singleton/pair test is exactly the usual finite-set definition
of VC dimension one, not a weakened surrogate. -/
theorem vcOne_iff_finite_shattering (H : HypothesisClass VCCounterexample.String) :
    VCCounterexample.VCOne H ↔
      (∃ x, FinsetShatters H {x}) ∧ ∀ S : Finset VCCounterexample.String,
        FinsetShatters H S → S.card ≤ 1 := by
  unfold VCCounterexample.VCOne
  simp_rw [finsetShatters_singleton_iff]
  exact and_congr Iff.rfl (no_pair_iff_shattered_card_le_one H)

theorem vc_counterexample_dimension_one :
    (∃ x, FinsetShatters VCCounterexample.H {x}) ∧
      ∀ S : Finset VCCounterexample.String, FinsetShatters VCCounterexample.H S → S.card ≤ 1 :=
  (vcOne_iff_finite_shattering _).mp VCCounterexample.vc_one

theorem vc_counterexample_countable : Countable {h // VCCounterexample.H h} := by
  obtain ⟨code, hc⟩ := VCCounterexample.countable_class
  exact Function.Injective.countable (f := code) hc

/-- Zero-based round indices, with index zero denoting the newest stored round. -/
noncomputable def mistakeIndices (h : Hypothesis X) : Trajectory X → Finset Nat
  | [] => ∅
  | (z, _) :: τ =>
    let previous := (mistakeIndices h τ).image Nat.succ
    if h z then previous else insert 0 previous

theorem mistakeIndices_card (h : Hypothesis X) (τ : Trajectory X) :
    (mistakeIndices h τ).card = mistakes h τ := by
  induction τ with
  | nil => rfl
  | cons p τ ih =>
    have hzero : 0 ∉ (mistakeIndices h τ).image Nat.succ := by simp
    simp only [mistakeIndices, mistakes, loss]
    cases he : h p.1 <;> simp [Finset.card_image_of_injective _ Nat.succ_injective, ih, Nat.add_comm]

theorem mistakeIndices_mem_iff (h : Hypothesis X) (τ : Trajectory X) (i : Nat) :
    i ∈ mistakeIndices h τ ↔ ∃ z x, τ[i]? = some (z,x) ∧ h z = false := by
  induction τ generalizing i with
  | nil => simp [mistakeIndices]
  | cons p τ ih =>
    rcases p with ⟨z, x⟩
    cases i with
    | zero =>
      simp only [mistakeIndices]
      cases he : h z <;> simp [he]
    | succ i =>
      simp only [mistakeIndices]
      cases he : h z <;> simp [ih]

/-- An m-mistake threshold is equivalent to an explicit feasible set of m
round indices. Exact mistake sets are obtained by taking mistakeIndices itself. -/
theorem mistakes_threshold_iff_indices (h : Hypothesis X) (τ : Trajectory X) (m : Nat) :
    m ≤ mistakes h τ ↔ ∃ I : Finset Nat, I ⊆ mistakeIndices h τ ∧ I.card = m := by
  rw [← mistakeIndices_card]
  constructor
  · exact Finset.exists_subset_card_eq
  · rintro ⟨I, hI, hc⟩
    rw [← hc]
    exact Finset.card_le_card hI

end PredictionToGeneration


namespace PredictionToGeneration
open Classical

/-- Exact invalid-demonstration index set on the same trajectory. -/
noncomputable def demonstrationIndices (h : Hypothesis X) (τ : Trajectory X) : Finset Nat :=
  mistakeIndices h (τ.map Prod.swap)

theorem demonstrationIndices_card (h : Hypothesis X) (τ : Trajectory X) :
    (demonstrationIndices h τ).card = demonstrationLoss h τ := by
  unfold demonstrationIndices
  rw [mistakeIndices_card]
  induction τ with
  | nil => rfl
  | cons p τ ih => simp [mistakes, demonstrationLoss, ih]

theorem regret_eq_index_score (h : Hypothesis X) (τ : Trajectory X) :
    regret h τ = ((mistakeIndices h τ).card : Int) - ((demonstrationIndices h τ).card : Int) := by
  simp only [mistakeIndices_card, demonstrationIndices_card, regret]

theorem realizableBad_iff_index_pattern (H : HypothesisClass X) (m : Nat) (τ : Trajectory X) :
    RealizableBad H m τ ↔ ∃ h, ∃ I : Finset Nat,
      H h ∧ Realizes h τ ∧ I ⊆ mistakeIndices h τ ∧ I.card = m := by
  constructor
  · rintro ⟨h, hh, hr, hm⟩
    obtain ⟨I, hI, hc⟩ := (mistakes_threshold_iff_indices h τ m).mp hm
    exact ⟨h, I, hh, hr, hI, hc⟩
  · rintro ⟨h, I, hh, hr, hI, hc⟩
    exact ⟨h, hh, hr, (mistakes_threshold_iff_indices h τ m).mpr ⟨I, hI, hc⟩⟩

theorem signedBad_iff_index_pattern (H : HypothesisClass X) (m : Int) (τ : Trajectory X) :
    SignedBad H m τ ↔ ∃ h, ∃ I J : Finset Nat,
      H h ∧ I = mistakeIndices h τ ∧ J = demonstrationIndices h τ ∧
        m ≤ (I.card : Int) - (J.card : Int) := by
  constructor
  · rintro ⟨h, hh, hm⟩
    exact ⟨h, mistakeIndices h τ, demonstrationIndices h τ, hh, rfl, rfl,
      by simpa only [← regret_eq_index_score] using hm⟩
  · rintro ⟨h, I, J, hh, rfl, rfl, hm⟩
    exact ⟨h, hh, by simpa only [← regret_eq_index_score] using hm⟩

end PredictionToGeneration


namespace PredictionToGeneration
open Classical

theorem mistakeIndices_lt_length (h : Hypothesis X) (τ : Trajectory X) (i : Nat)
    (hi : i ∈ mistakeIndices h τ) : i < τ.length := by
  obtain ⟨z, x, hx, _⟩ := (mistakeIndices_mem_iff h τ i).mp hi
  exact (List.getElem?_eq_some_iff.mp hx).1

theorem demonstrationIndices_mem_iff (h : Hypothesis X) (τ : Trajectory X) (i : Nat) :
    i ∈ demonstrationIndices h τ ↔ ∃ z x, τ[i]? = some (z,x) ∧ h x = false := by
  unfold demonstrationIndices
  rw [mistakeIndices_mem_iff]
  cases he : τ[i]? with
  | none => simp [List.getElem?_map, he]
  | some p =>
    rcases p with ⟨z,x⟩
    simp [List.getElem?_map, he]

theorem demonstrationIndices_lt_length (h : Hypothesis X) (τ : Trajectory X) (i : Nat)
    (hi : i ∈ demonstrationIndices h τ) : i < τ.length := by
  obtain ⟨z, x, hx, _⟩ := (demonstrationIndices_mem_iff h τ i).mp hi
  exact (List.getElem?_eq_some_iff.mp hx).1

end PredictionToGeneration
