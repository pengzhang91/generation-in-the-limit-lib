import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.GenerationUpper
import Mathlib.Combinatorics.Colex

/-! # The countable family for the infinite witness-index lower bound -/
namespace GenLimit.AgnosticLanguage.RowFamily
open DiscreteIID Filter
open scoped Classical
noncomputable section

def cell (i j : ℕ) := 2 * Nat.pair i j

theorem cell_inj {i j k l : ℕ} (h : cell i j = cell k l) : i = k ∧ j = l := by
  apply Nat.pair_eq_pair.mp
  unfold cell at h; omega

def row (i : ℕ) : Set ℕ := Set.range (cell i)
def spine : Set ℕ := Set.range (fun i ↦ cell i 0)
def beyond (i j : ℕ) : Set ℕ := {x | ∃ l > j, cell i l = x}

private def extra (T : Finset ℕ) : Set ℕ := (T : Set ℕ) ∪ {x | x % 2 = 1 ∧ T.sup id < x}

/-- The spine, all horizontal rows, and an infinite language extending each
finite subset by odd numbers above its maximum. -/
def family : Generic.LanguageFamily ℕ
  | 0 => spine
  | k+1 => if k % 2 = 0 then row (k/2) else extra (Finset.equivBitIndices (k/2))

theorem includes_row (i : ℕ) : family (2*i+1) = row i := by simp [family]

private theorem includes_extra (T : Finset ℕ) :
    family (2*Finset.equivBitIndices.symm T+1+1) = extra T := by
  simp [family,Nat.add_div]

theorem row_infinite (i : ℕ) : (row i).Infinite :=
  Set.infinite_range_of_injective (fun _ _ h ↦ (cell_inj h).2)

theorem spine_infinite : spine.Infinite :=
  Set.infinite_range_of_injective (fun _ _ h ↦ (cell_inj h).1)

private theorem extra_infinite (T : Finset ℕ) : (extra T).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro n
  refine ⟨2*(n+T.sup id)+1,Or.inr ⟨by omega,by omega⟩,by omega⟩

theorem infinite_languages : ∀ i, (family i).Infinite
  | 0 => spine_infinite
  | k+1 => by simp only [family]; split <;> first | apply row_infinite | apply extra_infinite

theorem unbounded_witness_index (p : PMF ℕ) (hinf : p.support.Infinite)
    (heven : ∀ x ∈ p.support, x % 2 = 0) : ¬ FiniteWitnessIndex (Equiv.refl ℕ) family p := by
  rintro ⟨M,hM⟩
  obtain ⟨T,hT,hcard⟩ := hinf.exists_subset_card_eq M
  let bound := T.sup id + 1
  have hfilter : (Finset.range bound).filter (fun x ↦ x ∈ extra T) = T := by
    ext x; simp only [Finset.mem_filter,Finset.mem_range]
    constructor
    · rintro ⟨hx, ht | ho⟩
      · exact ht
      · exact False.elim ((Nat.not_lt_of_ge (Nat.le_of_lt_succ hx)) ho.2)
    · intro hx
      exact ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id) hx),Or.inl hx⟩
  have hcount : Nat.count (fun x ↦ x ∈ extra T) bound = M := by
    rw [Nat.count_eq_card_filter_range,hfilter,hcard]
  have h := hM (2*Finset.equivBitIndices.symm T+1+1)
  rw [includes_extra] at h
  have hsub : extra T ⊆ p.support := h (by
    intro r hr
    let w := Nat.nth (fun x ↦ x ∈ extra T) r
    have hw : w < bound := Nat.nth_lt_of_lt_count (hcount.symm ▸ hr)
    have hm : w ∈ extra T := Nat.nth_mem_of_infinite (extra_infinite T) r
    have ht : w ∈ T := by rw [←hfilter]; exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw,hm⟩
    exact hT ht)
  have he := heven (2*T.sup id+1) (hsub (Or.inr ⟨by omega,by omega⟩))
  omega

end
end GenLimit.AgnosticLanguage.RowFamily
