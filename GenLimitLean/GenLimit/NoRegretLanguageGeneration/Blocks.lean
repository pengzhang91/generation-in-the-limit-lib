import GenLimit.NoRegretLanguageGeneration.FiniteMinimax
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Countable
import Mathlib.Tactic

namespace PredictionToGeneration.Blocks

abbrev Space (size : Nat → Nat) := (n : Nat) × Fin (size n)

def block {size : Nat → Nat} (x : Space size) : Nat := x.1

noncomputable def inBlock {size : Nat → Nat} (E : Finset (Space size)) (n : Nat) : Finset (Space size) :=
  E.filter (fun x => block x = n)

def Admissible {size : Nat → Nat} (capacity : Nat → Nat) (E : Finset (Space size)) : Prop :=
  ∀ n, (inBlock E n).card ≤ capacity n

noncomputable def cofiniteHypothesis {X : Type} (E : Finset X) : Hypothesis X :=
  fun x => @decide (x ∉ E) (Classical.propDecidable _)

noncomputable def Class (size capacity : Nat → Nat) : HypothesisClass (Space size) :=
  fun h => ∃ E : Finset (Space size), Admissible capacity E ∧ h = cofiniteHypothesis E

instance space_infinite (size : Nat → Nat) (hsize : ∀ n, 0 < size n) : Infinite (Space size) :=
  Infinite.of_injective (fun n => (⟨n, ⟨0, hsize n⟩⟩ : Space size)) (by intro a b he; exact congrArg Sigma.fst he)

theorem cofinite_uus {X : Type} [Infinite X] (E : Finset X) (seen : List X) :
    ∃ x, x ∉ seen ∧ cofiniteHypothesis E x = true := by
  classical
  obtain ⟨x, hx⟩ := Finset.exists_notMem (E ∪ seen.toFinset)
  simp only [Finset.mem_union, not_or, List.mem_toFinset] at hx
  exact ⟨x, hx.2, by simp [cofiniteHypothesis, hx.1]⟩

theorem uus (size capacity : Nat → Nat) (hsize : ∀ n, 0 < size n) : UUS (Class size capacity) := by
  letI := space_infinite size hsize
  intro h ⟨E, _, he⟩ seen
  subst h
  exact cofinite_uus E seen

theorem nonempty_class (size capacity : Nat → Nat) : ∃ h, Class size capacity h := by
  refine ⟨cofiniteHypothesis ∅, ∅, ?_, rfl⟩
  intro n
  simp [inBlock]

theorem countable_class (size capacity : Nat → Nat) : Countable {h // Class size capacity h} := by
  classical
  let encode : {h // Class size capacity h} → Finset (Space size) := fun h => Classical.choose h.2
  apply Function.Injective.countable (f := encode)
  intro a b he
  apply Subtype.ext
  have ha := (Classical.choose_spec a.2).2
  have hb := (Classical.choose_spec b.2).2
  exact ha.trans ((congrArg cofiniteHypothesis he).trans hb.symm)

end PredictionToGeneration.Blocks


namespace PredictionToGeneration.Blocks
open Classical

noncomputable def points (size : Nat → Nat) (n : Nat) : Finset (Space size) :=
  Finset.univ.map ⟨fun i => (⟨n, i⟩ : Space size), by intro a b he; cases he; rfl⟩

@[simp] theorem mem_points {size : Nat → Nat} {n : Nat} {x : Space size} :
    x ∈ points size n ↔ block x = n := by
  rcases x with ⟨m, i⟩
  simp only [points, Finset.mem_map, Finset.mem_univ, true_and, block]
  constructor
  · rintro ⟨j, he⟩; exact (congrArg Sigma.fst he).symm
  · intro he; subst m; exact ⟨i, rfl⟩

@[simp] theorem card_points (size : Nat → Nat) (n : Nat) : (points size n).card = size n := by
  simp [points]

abbrev outputs (τ : Trajectory X) : List X := τ.map Prod.fst

theorem mistakes_cofinite_eq_filter (E : Finset X) (τ : Trajectory X) :
    mistakes (cofiniteHypothesis E) τ = ((outputs τ).filter (fun z => decide (z ∈ E))).length := by
  induction τ with
  | nil => rfl
  | cons p τ ih =>
    simp only [mistakes, outputs, List.map_cons, List.filter_cons, cofiniteHypothesis, loss]
    simp only [outputs] at ih
    by_cases he : p.1 ∈ E <;> simp [he, ih, Nat.add_comm]

theorem block_mistakes_bound {size : Nat → Nat} (capacity : Nat → Nat)
    (E : Finset (Space size)) (he : Admissible capacity E)
    (n : Nat) (τ : Trajectory (Space size)) (hn : (outputs τ).Nodup)
    (hb : ∀ z ∈ outputs τ, block z = n) : mistakes (cofiniteHypothesis E) τ ≤ capacity n := by
  rw [mistakes_cofinite_eq_filter]
  let zs := (outputs τ).filter (fun z => decide (z ∈ E))
  have hz : zs.Nodup := List.Pairwise.filter _ hn
  have hs : zs.toFinset ⊆ inBlock E n := by
    intro z hz
    have hm := List.mem_filter.mp (List.mem_toFinset.mp hz)
    simp only [inBlock, Finset.mem_filter]
    exact ⟨of_decide_eq_true hm.2, hb z hm.1⟩
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup hz] at hc
  convert Nat.le_trans hc (he n) using 1; simp [zs]
  congr 2
  funext z
  by_cases hz : z ∈ E <;> simp [hz]

/-- A sufficiently large block supports pairwise distinct outputs through T. -/
theorem block_strategy (size capacity : Nat → Nat) (n T : Nat) (hsize : 2 * T ≤ size n)
    (k : Nat) (τ : Trajectory (Space size)) (hl : τ.length + k = T)
    (hn : (outputs τ).Nodup) (hb : ∀ z ∈ outputs τ, block z = n) :
    ∃ s : Strategy (Space size) k τ, Guarantees
      (fun leaf => ∀ h, Class size capacity h → mistakes h leaf ≤ capacity n) s := by
  induction k generalizing τ with
  | zero =>
    refine ⟨.done τ, ?_⟩
    rintro h ⟨E, he, rfl⟩
    exact block_mistakes_bound capacity E he n τ hn hb
  | succ k ih =>
    let forbidden := (demonstrations τ).toFinset ∪ (outputs τ).toFinset
    have hc : forbidden.card < (points size n).card := by
      have hd := List.toFinset_card_le (l := demonstrations τ)
      have ho := List.toFinset_card_le (l := outputs τ)
      have hu := Finset.card_union_le (demonstrations τ).toFinset (outputs τ).toFinset
      simp only [demonstrations, outputs, List.length_map] at hd ho
      rw [card_points]
      dsimp [forbidden]
      simp only [demonstrations, outputs] at hu ⊢
      omega
    obtain ⟨z, hz, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
    have hbz : block z = n := mem_points.mp hz
    have hzfresh : Fresh τ z := by
      have : z ∉ (demonstrations τ).toFinset := fun h => hnot (Finset.mem_union_left _ h)
      simpa [Fresh] using this
    have hzout : z ∉ outputs τ := by
      intro h
      exact hnot (Finset.mem_union_right _ (List.mem_toFinset.mpr h))
    have children : ∀ x, Fresh τ x → ∃ s : Strategy (Space size) k ((z, x) :: τ),
        Guarantees (fun leaf => ∀ h, Class size capacity h → mistakes h leaf ≤ capacity n) s := by
      intro x hx
      apply ih ((z, x) :: τ) (by simp only [List.length_cons]; omega)
      · exact List.nodup_cons.mpr ⟨hzout, hn⟩
      · intro y hy
        rcases List.mem_cons.mp hy with he | he
        · simpa [he] using hbz
        · exact hb y he
    refine ⟨.step z hzfresh (fun x hx => Classical.choose (children x hx)), ?_⟩
    intro x hx
    exact Classical.choose_spec (children x hx)

theorem mf_upper (size capacity : Nat → Nat) (hpositive : ∀ n, 0 < size n)
    (n T : Nat) (hsize : 2 * T ≤ size n) : MF (Class size capacity) T ≤ capacity n := by
  obtain ⟨s, hs⟩ := block_strategy size capacity n T hsize T [] (by simp) List.nodup_nil (by simp)
  have hr : Guarantees (fun τ => ∀ h, Class size capacity h → Realizes h τ → mistakes h τ ≤ capacity n) s :=
    guarantees_mono s (fun τ ht h hh _ => ht h hh) hs
  have hf := (realizable_finite_characterization (Class size capacity) T (capacity n)).mpr ⟨s, hr⟩
  by_contra hh
  have hforce := (mf_spec (Class size capacity) (uus size capacity hpositive) (nonempty_class size capacity) T).1
  apply hf
  apply forces_mono (n := T) (τ := []) (hf := hforce)
  rintro τ ⟨h, hh', hr, hm⟩
  exact ⟨h, hh', hr, by omega⟩

end PredictionToGeneration.Blocks





