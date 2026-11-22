import GenLimit.Paper08_HallucinationDetection.AngluinCondition
import Mathlib.Data.Finset.Prod

/-! # Definition 4's enumeration primitive and Algorithm 2's consistency queries -/
namespace GenLimit.HallucinationDetection
open GenLimit.Generic GenLimit.Angluin

/-- An oracle emits successive items of the finite enumeration on request.
An empty list provides the empty tell-tale. -/
structure TellTaleOracle (C : Generic.LanguageFamily α) [DecidableEq α] where
  enumeration : ℕ → List α
  correct : ∀ i, IsTellTale C i (enumeration i).toFinset

theorem conditionTwo_iff_tellTaleOracle (C : Generic.LanguageFamily α) [DecidableEq α] :
    ConditionTwo C ↔ Nonempty (TellTaleOracle C) := by
  classical
  constructor
  · intro h
    exact ⟨⟨fun i ↦ (chosenTellTale C h i).toList,
      fun i ↦ by simpa using chosenTellTale_spec C h i⟩⟩
  · rintro ⟨O⟩ i
    exact ⟨_, O.correct i⟩

/-- Keys are pairs of a zero-based language index and an observation
position. The full table after round t answers every such pair below t. -/
def querySquare (t : ℕ) : Finset (ℕ × ℕ) := (Finset.range t) ×ˢ (Finset.range t)

/-- Evaluate just the previously uncached coordinates. Old answers are
retained even when the next observation repeats an earlier value. -/
def extendQueryCache (oracle : ℕ → α → Bool) (stream : Stream α) (t : ℕ)
    (old : Finset ((ℕ × ℕ) × Bool)) : Finset ((ℕ × ℕ) × Bool) :=
  old ∪ ((querySquare (t + 1) \ querySquare t).image
    (fun ij ↦ (ij, oracle ij.1 (stream ij.2))))

def queryCache (oracle : ℕ → α → Bool) (stream : Stream α) :
    ℕ → Finset ((ℕ × ℕ) × Bool)
  | 0 => ∅
  | t + 1 => extendQueryCache oracle stream t (queryCache oracle stream t)

private theorem querySquare_mono (t : ℕ) : querySquare t ⊆ querySquare (t+1) :=
  Finset.product_subset_product (Finset.range_mono (Nat.le_succ t)) (Finset.range_mono (Nat.le_succ t))

theorem queryCache_eq (oracle : ℕ → α → Bool) (stream : Stream α) (t : ℕ) :
    queryCache oracle stream t =
      (querySquare t).image (fun ij ↦ (ij, oracle ij.1 (stream ij.2))) := by
  induction t with
  | zero => simp [queryCache, querySquare]
  | succ t ih =>
    rw [queryCache, extendQueryCache, ih, ← Finset.image_union,
      Finset.union_sdiff_of_subset (querySquare_mono t)]

/-- Footnote 5: the transition from t to t+1 requests exactly 2t+1 new
table entries. This is 2s-1 in the paper's one-based round s. -/
theorem algorithmTwo_fresh_query_count (t : ℕ) :
    (querySquare (t + 1) \ querySquare t).card = 2 * (t + 1) - 1 := by
  rw [Finset.card_sdiff_of_subset (querySquare_mono t)]
  simp [querySquare, Nat.add_mul, Nat.mul_add]
  omega

/-- Reading a row of the cache computes exactly Algorithm 2's consistency
test on the observed sample, using its t visible languages. -/
theorem algorithmTwo_cached_consistency (C : Generic.LanguageFamily α)
    (oracle : ℕ → α → Bool) (hO : ∀ i x, oracle i x = true ↔ x ∈ C i)
    (stream : Stream α) {t i : ℕ} (hi : i < t) :
    (∀ j < t, ((i,j),true) ∈ queryCache oracle stream t) ↔
      (↑(Generic.sample stream t) : Set α) ⊆ C i := by
  rw [queryCache_eq]
  have cell (j : ℕ) (hj : j < t) :
      ((i,j),true) ∈ (querySquare t).image (fun ij ↦ (ij, oracle ij.1 (stream ij.2))) ↔
      stream j ∈ C i := by
    simp [querySquare, hi, hj, hO]
  constructor
  · intro h x hx
    obtain ⟨j,hj,rfl⟩ := Generic.mem_sample_iff.mp hx
    exact (cell j hj).mp (h j hj)
  · intro h j hj
    exact (cell j hj).mpr (h (Generic.mem_sample_iff.mpr ⟨j,hj,rfl⟩))

end GenLimit.HallucinationDetection
