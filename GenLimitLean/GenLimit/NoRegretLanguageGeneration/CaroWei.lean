import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace PredictionToGeneration.CaroWei
open scoped BigOperators
open Classical

noncomputable def neighbors {α : Type*} (G : SimpleGraph α) (V : Finset α) (v : α) : Finset α :=
  V.filter (G.Adj v)

noncomputable def weight {α : Type*} (G : SimpleGraph α) (V : Finset α) (v : α) : ℚ :=
  1 / ((neighbors G V v).card + 1 : ℚ)

theorem weighted_independent {α : Type*} (G : SimpleGraph α) (V : Finset α) :
    ∃ I : Finset α, I ⊆ V ∧ (∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b) ∧
      ∑ v ∈ V, weight G V v ≤ (I.card : ℚ) := by
  classical
  induction V using Finset.strongInductionOn with
  | _ V ih =>
    by_cases hV : V.Nonempty
    · obtain ⟨v,hv,hmin⟩ := Finset.exists_min_image V (fun v => (neighbors G V v).card) hV
      let W := V.filter (fun w => w ≠ v ∧ ¬ G.Adj v w)
      have hWV : W ⊆ V := Finset.filter_subset _ _
      have vnotW : v ∉ W := by simp [W]
      have hproper : W ⊂ V := Finset.ssubset_iff_subset_ne.mpr ⟨hWV,fun he => vnotW (he ▸ hv)⟩
      obtain ⟨I,hIW,hind,hbound⟩ := ih W hproper
      have vnotI : v ∉ I := fun hi => vnotW (hIW hi)
      have hind' : ∀ a ∈ insert v I, ∀ b ∈ insert v I, ¬ G.Adj a b := by
        intro a ha b hb
        rcases Finset.mem_insert.mp ha with he | ha
        · subst a
          rcases Finset.mem_insert.mp hb with he | hb
          · subst b
            exact G.loopless _
          · exact (Finset.mem_filter.mp (hIW hb)).2.2
        · rcases Finset.mem_insert.mp hb with he | hb
          · subst b
            exact fun hab => (Finset.mem_filter.mp (hIW ha)).2.2 (G.symm hab)
          · exact hind a ha b hb
      have hweight : ∀ w ∈ W, weight G V w ≤ weight G W w := by
        intro w _
        apply one_div_le_one_div_of_le (by positivity)
        have hs : neighbors G W w ⊆ neighbors G V w := by
          intro u hu
          obtain ⟨huW,hadj⟩ := Finset.mem_filter.mp hu
          exact Finset.mem_filter.mpr ⟨hWV huW,hadj⟩
        have hc := Finset.card_le_card hs
        exact_mod_cast Nat.add_le_add_right hc 1
      have hsumW : ∑ w ∈ W, weight G V w ≤ (I.card : ℚ) :=
        le_trans (Finset.sum_le_sum hweight) hbound
      have hcompl : V \ W = insert v (neighbors G V v) := by
        ext w
        simp only [Finset.mem_sdiff,Finset.mem_insert,neighbors,Finset.mem_filter,W]
        constructor
        · rintro ⟨hw,hn⟩
          by_cases he : w = v
          · exact Or.inl he
          · exact Or.inr ⟨hw,by tauto⟩
        · rintro (rfl | ⟨hw,ha⟩)
          · exact ⟨hv,by simp⟩
          · exact ⟨hw,by tauto⟩
      have vnotN : v ∉ neighbors G V v := by simp [neighbors]
      have hcard : (V \ W).card = (neighbors G V v).card + 1 := by
        rw [hcompl,Finset.card_insert_of_notMem vnotN]
      have hsumC : ∑ w ∈ V \ W, weight G V w ≤ 1 := by
        have point : ∀ w ∈ V \ W, weight G V w ≤ weight G V v := by
          intro w hw
          apply one_div_le_one_div_of_le (by positivity)
          have hc := hmin w (Finset.mem_sdiff.mp hw).1
          exact_mod_cast Nat.add_le_add_right hc 1
        have hs := Finset.sum_le_sum point
        calc
          ∑ w ∈ V \ W, weight G V w ≤ ∑ _w ∈ V \ W, weight G V v := hs
          _ = 1 := by
            simp only [Finset.sum_const,nsmul_eq_mul,hcard,weight]
            push_cast
            field_simp
      refine ⟨insert v I,Finset.insert_subset hv (hIW.trans hWV),hind',?_⟩
      have hsplit := Finset.sum_sdiff (f := weight G V) hWV
      rw [Finset.card_insert_of_notMem vnotI]
      push_cast
      linarith
    · have he := Finset.not_nonempty_iff_eq_empty.mp hV
      subst V
      exact ⟨∅,Finset.empty_subset _,by simp,by simp⟩




/-- The full finite-graph bound named Caro--Wei in the manuscript.
Rational arithmetic expresses the cardinality quotient exactly. -/
theorem caro_wei {α : Type*} [Fintype α] (G : SimpleGraph α) :
    ∃ I : Finset α, G.IsIndepSet (I : Set α) ∧
      (Fintype.card α : ℚ)^2 /
        (2 * (G.edgeFinset.card : ℚ) + Fintype.card α) ≤ (I.card : ℚ) := by
  classical
  obtain ⟨I,_,hind,hweight⟩ := weighted_independent G Finset.univ
  have hneighbor (v : α) : neighbors G Finset.univ v = G.neighborFinset v := by
    ext w
    simp [neighbors]
  have hw (v : α) : weight G Finset.univ v = 1 / ((G.degree v : ℚ)+1) := by
    simp [weight,hneighbor,G.card_neighborFinset_eq_degree]
  have hc := Finset.sq_sum_div_le_sum_sq_div (R := ℚ) (Finset.univ : Finset α)
    (fun _ => 1) (g := fun v => (G.degree v : ℚ)+1) (by intro v _; positivity)
  have hd : (∑ v : α, ((G.degree v : ℚ)+1)) =
      2 * (G.edgeFinset.card : ℚ) + Fintype.card α := by
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    have hsum := G.sum_degrees_eq_twice_card_edges
    exact_mod_cast congrArg (fun n : Nat => n + Fintype.card α) hsum
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,one_pow,hd] at hc
  simp_rw [hw] at hweight
  refine ⟨I,?_,le_trans hc hweight⟩
  rw [G.isIndepSet_iff]
  intro a ha b hb _
  exact hind a ha b hb

/-- The sparse-graph vertex cover conclusion, with an integral inequality. -/
theorem sparse_vertex_cover {α : Type*} [Fintype α] (G : SimpleGraph α)
    (he : G.edgeFinset.card ≤ Fintype.card α) :
    ∃ C : Finset α, (∀ a b, G.Adj a b → a ∈ C ∨ b ∈ C) ∧
      3 * C.card ≤ 2 * Fintype.card α := by
  classical
  obtain ⟨I,hind,hbound⟩ := caro_wei G
  have hsize : (Fintype.card α : ℚ) ≤ 3 * (I.card : ℚ) := by
    by_cases hz : Fintype.card α = 0
    · simp [hz]
    · have hn : (0 : ℚ) < Fintype.card α := by exact_mod_cast Nat.pos_of_ne_zero hz
      have hd : (0 : ℚ) < 2*(G.edgeFinset.card : ℚ) + Fintype.card α := by positivity
      have hb := (div_le_iff₀ hd).mp hbound
      have he' : (G.edgeFinset.card : ℚ) ≤ Fintype.card α := by exact_mod_cast he
      have hi : (0 : ℚ) ≤ I.card := by positivity
      nlinarith
  refine ⟨Finset.univ \ I,?_,?_⟩
  · intro a b hab
    by_cases ha : a ∈ I
    · have hb : b ∉ I := by
        intro hb
        exact (G.isIndepSet_iff.mp hind) ha hb (G.ne_of_adj hab) hab
      exact Or.inr (by simp [hb])
    · exact Or.inl (by simp [ha])
  · have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I)
    simp only [Finset.card_univ] at hcard
    have hi : Fintype.card α ≤ 3*I.card := by exact_mod_cast hsize
    omega

end PredictionToGeneration.CaroWei
