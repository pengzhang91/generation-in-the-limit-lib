import GenLimit.NoRegretLanguageGeneration.Blocks
import GenLimit.NoRegretLanguageGeneration.Uniform

namespace PredictionToGeneration.Blocks
open Classical

/-- At most one invalid point is reserved in each finite block. -/
def Separated {size : Nat → Nat} (R : Finset (Space size)) : Prop :=
  ∀ x ∈ R, ∀ y ∈ R, block x = block y → x = y

theorem separated_empty (size : Nat → Nat) : Separated (∅ : Finset (Space size)) := by
  simp [Separated]

theorem separated_insert {size : Nat → Nat} (R : Finset (Space size)) (z : Space size)
    (hR : Separated R) (hz : ∀ r ∈ R, block r ≠ block z) : Separated (insert z R) := by
  classical
  intro x hx y hy he
  simp only [Finset.mem_insert] at hx hy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · rfl
  · exact False.elim (hz y hy he.symm)
  · exact False.elim (hz x hx he)
  · exact hR x hx y hy he

theorem separated_admissible {size : Nat → Nat} (R : Finset (Space size))
    (hR : Separated R) : Admissible (fun _ => 1) R := by
  classical
  intro n
  apply Finset.card_le_one.mpr
  intro x hx y hy
  simp only [inBlock, Finset.mem_filter] at hx hy
  exact hR x hx.1 y hy.1 (hx.2.trans hy.2.symm)

noncomputable def blockPoints (size : Nat → Nat) (n : Nat) : Finset (Space size) :=
  Finset.univ.map ⟨fun i => ⟨n,i⟩, by intro a b he; simpa using he⟩

theorem mem_blockPoints {size : Nat → Nat} (n : Nat) (x : Space size) :
    x ∈ blockPoints size n ↔ block x = n := by
  classical
  cases x with
  | mk k i =>
    simp only [blockPoints, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨j, he⟩
      exact (congrArg Sigma.fst he).symm
    · intro he
      change k = n at he
      subst k
      exact ⟨i, rfl⟩

noncomputable def visitedPoints {size : Nat → Nat} (R : Finset (Space size)) : Finset (Space size) :=
  R.biUnion (fun r => blockPoints size (block r))

theorem mem_visitedPoints {size : Nat → Nat} (R : Finset (Space size)) (x : Space size) :
    x ∈ visitedPoints R ↔ ∃ r ∈ R, block r = block x := by
  classical
  simp [visitedPoints, mem_blockPoints, eq_comm]

noncomputable def availableVisited {size : Nat → Nat} (R : Finset (Space size))
    (τ : Trajectory (Space size)) : Finset (Space size) :=
  (visitedPoints R).filter (Fresh τ)

theorem availableVisited_copy {size : Nat → Nat} (R : Finset (Space size))
    (τ : Trajectory (Space size)) (z : Space size) :
    availableVisited R ((z,z)::τ) = (availableVisited R τ).erase z := by
  classical
  ext x
  simp [availableVisited, Fresh, demonstrations, and_left_comm, and_comm]

theorem cofinite_mistakes_mono {X : Type} {R S : Finset X} (hRS : R ⊆ S)
    (τ : Trajectory X) : mistakes (cofiniteHypothesis R) τ ≤ mistakes (cofiniteHypothesis S) τ := by
  classical
  induction τ with
  | nil => exact Nat.le_refl _
  | cons p τ ih =>
    have hl : loss (cofiniteHypothesis R) p.1 ≤ loss (cofiniteHypothesis S) p.1 := by
      by_cases hr : p.1 ∈ R
      · have hs := hRS hr
        simp [loss, cofiniteHypothesis, hr, hs]
      · simp [loss, cofiniteHypothesis, hr]
    simp only [mistakes]
    omega

theorem cofinite_realizes_insert {size : Nat → Nat} (R : Finset (Space size))
    (τ : Trajectory (Space size)) (hr : Realizes (cofiniteHypothesis R) τ)
    (z : Space size) (hz : Fresh τ z) : Realizes (cofiniteHypothesis (insert z R)) τ := by
  classical
  induction τ with
  | nil => trivial
  | cons p τ ih =>
    obtain ⟨hp, ht⟩ := hr
    simp only [Fresh, demonstrations, List.map_cons, List.mem_cons, not_or] at hz
    refine ⟨?_, ih ht hz.2⟩
    have hp' : p.2 ∉ R := by simpa [cofiniteHypothesis] using hp
    simp [cofiniteHypothesis, hp', Ne.symm hz.1]

private theorem wf_step_of_exists {X : Type} (bad : Trajectory X → Prop) (τ : Trajectory X)
    (hc : ∀ z, Fresh τ z → ∃ x, Fresh τ x ∧ WellFoundedForces bad ((z,x)::τ)) :
    WellFoundedForces bad τ := by
  classical
  exact .step (fun z hz => Classical.choose (hc z hz))
    (fun z hz => (Classical.choose_spec (hc z hz)).1)
    (fun z hz => (Classical.choose_spec (hc z hz)).2)

/-- The reserve adversary is well-founded: a counted mistake decreases the
remaining budget; every other round consumes a point in finitely many visited blocks. -/
theorem reserve_wellFounded {size : Nat → Nat} [Infinite (Space size)]
    (H : HypothesisClass (Space size)) (m : Nat)
    (hin : ∀ R, Separated R → R.card ≤ m → H (cofiniteHypothesis R))
    (q : Nat) (R : Finset (Space size)) (τ : Trajectory (Space size))
    (hR : Separated R) (hcard : R.card + q ≤ m)
    (hr : Realizes (cofiniteHypothesis R) τ)
    (hm : m ≤ mistakes (cofiniteHypothesis R) τ + q) :
    WellFoundedForces (RealizableBad H m) τ := by
  classical
  induction q generalizing R τ with
  | zero => exact .leaf ⟨_, hin R hR (by omega), hr, by omega⟩
  | succ q ih =>
    have inner : ∀ a, ∀ τ : Trajectory (Space size),
        (availableVisited R τ).card = a → Realizes (cofiniteHypothesis R) τ →
        m ≤ mistakes (cofiniteHypothesis R) τ + (q+1) →
        WellFoundedForces (RealizableBad H m) τ := by
      intro a
      induction a using Nat.strongRecOn with
      | ind a rec =>
        intro τ ha hr hm
        apply wf_step_of_exists
        intro z hz
        by_cases hzR : z ∈ R
        · obtain ⟨x, hx, hp⟩ := cofinite_uus R (demonstrations τ)
          refine ⟨x, hx, ih R ((z,x)::τ) hR (by omega) ⟨hp, hr⟩ ?_⟩
          simp only [mistakes]
          have hl : loss (cofiniteHypothesis R) z = 1 := by simp [loss, cofiniteHypothesis, hzR]
          rw [hl]
          omega
        · by_cases hblock : ∃ r ∈ R, block r = block z
          · have hav : z ∈ availableVisited R τ := by
              simp only [availableVisited, Finset.mem_filter]
              exact ⟨(mem_visitedPoints R z).mpr hblock, hz⟩
            have hless : (availableVisited R ((z,z)::τ)).card < a := by
              rw [availableVisited_copy, ← ha]
              exact Finset.card_erase_lt_of_mem hav
            refine ⟨z, hz, rec _ hless ((z,z)::τ) rfl ?_ ?_⟩
            · exact ⟨by simp [cofiniteHypothesis, hzR], hr⟩
            · have hl : loss (cofiniteHypothesis R) z = 0 := by simp [loss, cofiniteHypothesis, hzR]
              simpa [mistakes, hl] using hm
          · let S := insert z R
            have hsep : Separated S := separated_insert R z hR (by
              intro r hmem he
              exact hblock ⟨r, hmem, he⟩)
            have hsize : S.card + q ≤ m := by
              simp only [S, Finset.card_insert_of_notMem hzR]
              omega
            have hrs : Realizes (cofiniteHypothesis S) τ := cofinite_realizes_insert R τ hr z hz
            obtain ⟨x, hx, hp⟩ := cofinite_uus S (demonstrations τ)
            refine ⟨x, hx, ih S ((z,x)::τ) hsep hsize ⟨hp, hrs⟩ ?_⟩
            have hmono := cofinite_mistakes_mono (Finset.subset_insert z R) τ
            have hl : loss (cofiniteHypothesis S) z = 1 := by simp [S, loss, cofiniteHypothesis]
            simp only [mistakes]
            rw [hl]
            dsimp [S] at *
            omega
    exact inner _ τ rfl hr hm

/-- Every finite requested mistake threshold is forceable when its separated
reserve targets are present. This includes bounded and unbounded compactness gaps. -/
theorem separated_reserve_forces {size : Nat → Nat} [Infinite (Space size)]
    (H : HypothesisClass (Space size)) (m : Nat)
    (hin : ∀ R, Separated R → R.card ≤ m → H (cofiniteHypothesis R)) :
    WellFoundedForces (RealizableBad H m) [] := by
  exact reserve_wellFounded H m hin m ∅ [] (separated_empty size)
    (by simp) trivial (by simp [mistakes])

end PredictionToGeneration.Blocks
