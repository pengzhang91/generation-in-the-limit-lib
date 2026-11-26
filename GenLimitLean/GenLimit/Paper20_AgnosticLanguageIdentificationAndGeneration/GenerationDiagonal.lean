import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.FiniteExperiments

/-! # An infinite-support obstruction to agnostic generation

At a finite-support law, sufficiently many draws cover its support. Almost
all generator outputs are bounded. Move to a new atom above this bound and
preserve the finite experiment on an initial segment of the law. Each later
atom is still larger, so the same error event holds at the limiting law. -/
namespace GenLimit.AgnosticLanguage
open DiscreteIID Filter
open scoped Classical
noncomputable section

private def covered (q : Stage) : Set (List ℕ) := {xs | ∀ x ∈ Set.range q.stream, x ∈ xs}

private def observedBelow (q : Stage) (v : ℕ) : Set (List ℕ × ℕ) :=
  {z | z.1 ∈ covered q ∧ z.2 < v}

private theorem finite_step (G : StatisticalGenerator ℕ) {ε : ℝ} (hε : 0 < ε)
    (q : Stage) (k : ℕ) :
    ∃ n ≥ k, ∃ v, (∀ x ∈ Set.range q.stream, x < v) ∧ ∃ cutoff,
      ∀ t : ℕ → ℕ, (∀ j < cutoff, t j = q.stream j) →
        1-ε < probability (joint G (sequenceLaw t) n) (observedBelow q v) := by
  let S := q.finite_range.toFinset
  have hs : (S : Set ℕ) = Set.range q.stream := q.finite_range.coe_toFinset
  have hc := finite_coverage (sequenceLaw q.stream) S (by rw [hs,sequenceLaw_support]) (ε/2) (by positivity)
  obtain ⟨n,hn,hcov⟩ := ((eventually_ge_atTop k).and hc).exists
  let law := joint G (sequenceLaw q.stream) n
  obtain ⟨F,hF⟩ := pmf_tight law (ε/2) (by positivity)
  let v := max (F.sup Prod.snd) (S.sup id) + 1
  have hS (x) (hx : x ∈ Set.range q.stream) : x < v := by
    have hm := Finset.le_sup (s := S) (f := id) (show x ∈ S by rwa [←hs] at hx)
    exact Nat.lt_succ_of_le (hm.trans (le_max_right ..))
  have hb (z) (hz : z ∈ F) : z.2 < v :=
    Nat.lt_succ_of_le ((Finset.le_sup (f := Prod.snd) hz).trans (le_max_left ..))
  refine ⟨n,hn,v,hS,experiment_freeze G q.stream n _ _ ?_⟩
  have hbad : (observedBelow q v)ᶜ ⊆ (F : Set (List ℕ × ℕ))ᶜ ∪ Prod.fst ⁻¹' (covered q)ᶜ := by
    intro z hz
    by_cases hf : z ∈ F
    · exact Or.inr (fun h ↦ hz ⟨h,hb z hf⟩)
    · exact Or.inl hf
  have h := (probability_mono law hbad).trans (probability_union_le law _ _)
  rw [probability_compl, probability_compl, joint_sample_event] at h
  have hw : (covered q)ᶜ = {xs | ¬∀ x ∈ S, x ∈ xs} := by
    ext xs; simp only [covered,Set.mem_compl_iff,Set.mem_setOf_eq]; rw [←hs]; rfl
  rw [hw] at h
  change 1-ε < probability law _
  linarith

/-- Theorem 3.1. A single infinite-support law gives infinitely many bad
sample sizes, including for a randomized generator. -/
theorem agnostic_generation_obstruction (G : StatisticalGenerator ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : PMF ℕ, p.support.Infinite ∧ ∃ᶠ n : ℕ in atTop, 1-ε ≤ genErr G p n := by
  choose n hn v hv cut hcut using finite_step G hε
  let q : ℕ → Stage := Nat.rec Stage.initial (fun k prev ↦ prev.append (cut prev k) (v prev k))
  let a := fun k ↦ v (q k) k
  have step (k) : q (k+1) = (q k).append (cut (q k) k) (a k) := rfl
  have growth (k) : (q k).length < (q (k+1)).length := by rw [step]; exact Nat.lt_succ_of_le (le_max_left ..)
  have agree (k j) (hj : j < (q k).length) : (q (k+1)).stream j = (q k).stream j := by
    rw [step]; exact Stage.append_agrees _ _ _ _ (hj.trans_le (le_max_left ..))
  let s := stageLimit q
  let p := sequenceLaw s
  have hs0 : 0 ∈ Set.range s := ⟨0,stageLimit_agrees q growth agree 0 0 (show 0 < 1 by decide)⟩
  have hr : p.support = ⋃ k, Set.range (q k).stream :=
    (sequenceLaw_support s).trans (stageLimit_range q growth agree hs0)
  have rangeStep (k) : Set.range (q (k+1)).stream = insert (a k) (Set.range (q k).stream) := by
    rw [step,Stage.append_range]
  have mem (k) : a k ∈ Set.range (q (k+1)).stream := by rw [rangeStep]; exact Set.mem_insert ..
  have mono : Monotone (fun k ↦ Set.range (q k).stream) := monotone_nat_of_le_succ fun k ↦ by
    rw [rangeStep]; exact Set.subset_insert ..
  have fresh : StrictMono a := strictMono_nat_of_lt_succ fun k ↦ hv (q (k+1)) (k+1) _ (mem k)
  have small (k x) (hx : x ∈ p.support) (hlt : x < a k) : x ∈ Set.range (q k).stream := by
    rw [hr] at hx
    obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hx
    rcases le_total m k with h | h
    · exact mono h hm
    · induction m,h using Nat.le_induction with
      | base => exact hm
      | succ m h ih =>
        rw [rangeStep] at hm
        rcases hm with he | he
        · exact False.elim ((Nat.not_lt_of_ge (fresh.monotone h)) (he ▸ hlt))
        · exact ih he
  refine ⟨p,(Set.infinite_range_of_injective fresh.injective).mono ?_,?_⟩
  · rintro _ ⟨k,rfl⟩; rw [hr]; exact Set.mem_iUnion.mpr ⟨k+1,mem k⟩
  · apply frequently_atTop.mpr
    intro k
    refine ⟨n (q k) k,hn _ _,?_⟩
    have freeze := hcut (q k) k s (fun j hj ↦
      (stageLimit_agrees q growth agree (k+1) j (by rw [step]; exact Nat.lt_succ_of_lt (hj.trans_le (le_max_right ..)))).trans
        (Stage.append_agrees (q k) _ _ _ (hj.trans_le (le_max_right ..))))
    apply freeze.le.trans (probability_mono _ ?_)
    rintro z ⟨hc,hv'⟩
    by_cases h : z.2 ∈ p.support
    · exact Or.inr (hc _ (small k _ h hv'))
    · exact Or.inl h

end
end GenLimit.AgnosticLanguage
