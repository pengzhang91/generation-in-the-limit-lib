import GenLimit.NoRegretLanguageGeneration.Comparisons
import GenLimit.NoRegretLanguageGeneration.IndependentFunction

namespace PredictionToGeneration.Rows
open Classical

noncomputable def hypothesis (S : Set Nat) (hole : Nat → Nat) : Hypothesis (Nat × Nat) :=
  fun x => decide (x.1 ∈ S ∧ x.2 ≠ hole x.1)

def H : HypothesisClass (Nat × Nat) :=
  fun h => ∃ S : Set Nat, S.Nonempty ∧ ∃ hole : Nat → Nat, h = hypothesis S hole

theorem uus : UUS H := by
  intro h ⟨S, ⟨i, hi⟩, hole, he⟩ seen
  subst h
  let q := Cofinite.freshAbove (hole i :: seen.map Prod.snd)
  refine ⟨(i,q), ?_, ?_⟩
  · intro hm
    have hq : q ∈ seen.map Prod.snd := List.mem_map.mpr ⟨(i,q), hm, rfl⟩
    have := Cofinite.lt_freshAbove (hole i :: seen.map Prod.snd) q (by simp [hq])
    omega
  · have hq := Cofinite.lt_freshAbove (hole i :: seen.map Prod.snd) (hole i) (by simp)
    simp [hypothesis, hi, q, ne_of_gt hq]

private def rowPrefix (i : Nat) : List (Nat × Nat) := (List.range i).map (fun j => (i,j))

private theorem rowPrefix_nodup (i : Nat) : (rowPrefix i).Nodup := by
  apply List.Nodup.map
  · intro a b he
    exact congrArg Prod.snd he
  · exact List.nodup_range

private theorem output_column_ge (G : Generator (Nat × Nat)) (i : Nat)
    (hr : (G.output (rowPrefix i)).1 = i) : i ≤ (G.output (rowPrefix i)).2 := by
  by_contra hn
  apply G.fresh (rowPrefix i)
  apply List.mem_map.mpr
  refine ⟨(G.output (rowPrefix i)).2, List.mem_range.mpr (by omega), ?_⟩
  apply Prod.ext
  · exact hr.symm
  · rfl

private theorem realizes_of_positive (G : Generator X) (h : Hypothesis X) (xs : List X)
    (hp : ∀ x ∈ xs, h x = true) : Realizes h (G.play xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨hp x (by simp), ih (fun y hy => hp y (by simp [hy]))⟩

/-- An infinite independent set of rows makes one fixed target defeat every
proposed target-dependent cutoff for the given generator. -/
theorem not_nonuniform : ¬ NonuniformGeneration H := by
  classical
  rintro ⟨G, hg⟩
  let row : Nat → Nat := fun i => (G.output (rowPrefix i)).1
  obtain ⟨S, hinf, hind⟩ := infinite_independent_for_function row
  let hole : Nat → Nat := fun i => if row i = i then (G.output (rowPrefix i)).2 else i
  let h := hypothesis S hole
  have hh : H h := ⟨S, hinf.nonempty, hole, rfl⟩
  obtain ⟨B, hb⟩ := hg h hh
  obtain ⟨i, hi, hBi⟩ := hinf.exists_gt B
  have hhole : i ≤ hole i := by
    dsimp [hole]
    split
    · exact output_column_ge G i ‹row i = i›
    · exact Nat.le_refl _
  have hr : Realizes h (G.play (rowPrefix i)) := by
    apply realizes_of_positive
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hj' := List.mem_range.mp hj
    simp [h, hypothesis, hi, show j ≠ hole i by omega]
  have hp := hb (rowPrefix i) (rowPrefix_nodup i) hr (by simpa [rowPrefix] using Nat.le_of_lt hBi)
  by_cases he : row i = i
  · have he' : (G.output (rowPrefix i)).1 = i := he
    simp [h, hypothesis, hole, he, he'] at hp
  · have hn : row i ∉ S := by
      intro hm
      exact hind i hi (row i) hm (Ne.symm he) rfl
    have hn' : (G.output (rowPrefix i)).1 ∉ S := hn
    simp [h, hypothesis, hn'] at hp

private def firstRow : List (Nat × Nat) → Nat
  | [] => 0
  | x::xs => match xs with
    | [] => x.1
    | _::_ => firstRow xs

noncomputable def generator : Generator (Nat × Nat) where
  output xs := (firstRow xs, (nonrepeatGenerator Nat).output (xs.map Prod.snd))
  fresh xs := by
    intro hm
    apply (nonrepeatGenerator Nat).fresh (xs.map Prod.snd)
    exact List.mem_map.mpr ⟨_, hm, rfl⟩

private theorem firstRow_positive (S : Set Nat) (hole : Nat → Nat) (xs : List (Nat × Nat))
    (hne : xs ≠ []) (hr : Realizes (hypothesis S hole) (generator.play xs)) : firstRow xs ∈ S := by
  induction xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs ih =>
    cases xs with
    | nil =>
      have hp : hypothesis S hole x = true := hr.1
      simp only [hypothesis, decide_eq_true_eq] at hp
      exact hp.1
    | cons y ys => exact ih (by simp) hr.2

private theorem row_loss (S : Set Nat) (hole : Nat → Nat) (i q : Nat) (hi : i ∈ S) :
    loss (hypothesis S hole) (i,q) = loss (Blocks.cofiniteHypothesis {hole i}) q := by
  by_cases he : q = hole i <;> simp [loss, hypothesis, Blocks.cofiniteHypothesis, hi, he]

private theorem row_mistakes_domination (S : Set Nat) (hole : Nat → Nat)
    (xs : List (Nat × Nat)) (hne : xs ≠ []) (hi : firstRow xs ∈ S) :
    mistakes (hypothesis S hole) (generator.play xs) ≤ 1 +
      mistakes (Blocks.cofiniteHypothesis {hole (firstRow xs)})
        ((nonrepeatGenerator Nat).play (xs.map Prod.snd)) := by
  induction xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs ih =>
    cases xs with
    | nil =>
      have hl := loss_le_one (hypothesis S hole) (generator.output [])
      simp only [Generator.play, mistakes]
      omega
    | cons y ys =>
      have ht : firstRow (y::ys) ∈ S := hi
      have hprev := ih (by simp) ht
      change loss (hypothesis S hole) (generator.output (y::ys)) +
          mistakes (hypothesis S hole) (generator.play (y::ys)) ≤ _
      have hl := row_loss S hole (firstRow (y::ys))
        ((nonrepeatGenerator Nat).output ((y::ys).map Prod.snd)) ht
      change loss (hypothesis S hole) (generator.output (y::ys)) = _ at hl
      rw [hl]
      change _ ≤ 1 + (loss (Blocks.cofiniteHypothesis {hole (firstRow (y::ys))})
        ((nonrepeatGenerator Nat).output ((y::ys).map Prod.snd)) +
        mistakes (Blocks.cofiniteHypothesis {hole (firstRow (y::ys))})
          ((nonrepeatGenerator Nat).play ((y::ys).map Prod.snd)))
      omega

/-- One possible initial error and one excluded point in the certified row. -/
theorem uniform_two_mistakes : UniformMistakeBound generator H 2 := by
  intro xs hn h ⟨S, _, hole, he⟩ hr
  subst h
  by_cases hnil : xs = []
  · simp [hnil, Generator.play, mistakes]
  · have hi := firstRow_positive S hole xs hnil hr
    have hm := row_mistakes_domination S hole xs hnil hi
    have hc := nonrepeatGenerator_cofinite_bound Nat {hole (firstRow xs)} (xs.map Prod.snd)
    simp only [Finset.card_singleton] at hc
    omega

theorem row_comparison_witness :
    UniformMistakeBounded H ∧ ¬ NonuniformGeneration H ∧
    RealizableNoRegret H ∧ GenerationInLimit H := by
  have hb : UniformMistakeBounded H := ⟨generator, 2, uniform_two_mistakes⟩
  exact ⟨hb, not_nonuniform, mistake_bounded_implies_no_regret H hb, mistake_bounded_implies_limit H hb⟩

end PredictionToGeneration.Rows
