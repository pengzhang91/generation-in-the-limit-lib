import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.RowWalk
import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.FiniteExperiments

/-! # The infinite witness-index obstruction

At each finite law, test whether the generator is likely to continue along
the current row. In this case abandon the row. Otherwise, extend the row.
A path changing row infinitely often contains the spine. A path that
eventually stays contains its final row. -/
namespace GenLimit.AgnosticLanguage
open DiscreteIID RowFamily Filter
open scoped Classical Topology
noncomputable section

private def tolerance (k : ℕ) : ℝ := 1/((k:ℝ)+1)

private def rowEvent (q : Stage) (u : ℕ × ℕ) (b : Bool) : Set (List ℕ × ℕ) :=
  if b then {z | z.2 ∈ beyond u.1 u.2}
  else {z | z.2 ∉ beyond u.1 u.2 ∧ ∀ x ∈ Set.range q.stream, x ∈ z.1}

private theorem row_experiment (G : StatisticalGenerator ℕ) (k : ℕ) (q : Stage) (u : ℕ × ℕ) :
    ∃ n ≥ k, ∃ (b : Bool) (c : ℕ), ∀ t : ℕ → ℕ, (∀ j < c, t j = q.stream j) →
      1/2 - tolerance k < probability (joint G (sequenceLaw t) n) (rowEvent q u b) := by
  have he : 0 < tolerance k := by unfold tolerance; positivity
  let S := q.finite_range.toFinset
  have hS : (S : Set ℕ) = Set.range q.stream := q.finite_range.coe_toFinset
  obtain ⟨n,hn,hcov⟩ := ((eventually_ge_atTop k).and
    (finite_coverage (sequenceLaw q.stream) S (by rw [hS,sequenceLaw_support]) _ he)).exists
  let law := joint G (sequenceLaw q.stream) n
  let R := rowEvent q u true
  by_cases h : 1/2 ≤ probability law R
  · exact ⟨n,hn,true,experiment_freeze G q.stream n _ _ ((sub_lt_self _ he).trans_le h)⟩
  refine ⟨n,hn,false,experiment_freeze G q.stream n _ _ ?_⟩
  let missing := {xs : List ℕ | ¬∀ x ∈ S, x ∈ xs}
  have hsub : (rowEvent q u false)ᶜ ⊆ R ∪ Prod.fst ⁻¹' missing := by
    intro z hz
    by_cases hm : z.2 ∈ beyond u.1 u.2
    · exact Or.inl hm
    · exact Or.inr fun hv ↦ hz ⟨hm,fun x hx ↦ hv x (by rwa [←hS] at hx)⟩
  have hh := (probability_mono law hsub).trans (probability_union_le law _ _)
  rw [probability_compl,joint_sample_event] at hh
  change 1/2 - _ < probability law _
  change probability _ missing < _ at hcov
  linarith

/-- The witness family and its enumeration are independent of the generator.
The construction also applies to randomized kernels. -/
theorem infinite_index_obstruction (G : StatisticalGenerator ℕ) :
    ∃ p : PMF ℕ, (∃ i, family i ⊆ p.support) ∧ ¬ FiniteWitnessIndex (Equiv.refl ℕ) family p ∧
      1/2 ≤ limsup (genErr G p) atTop := by
  choose n hn b cut freeze using row_experiment G
  let states : ℕ → Stage × (ℕ × ℕ) := Nat.rec (Stage.initial,(0,0)) fun k z ↦
    let u := move (b k z.1 z.2) z.2
    (z.1.append (cut k z.1 z.2) (cell u.1 u.2),u)
  let q := fun k ↦ (states k).1
  let w : Walk := ⟨fun k ↦ (states k).2,fun k ↦ b k (q k) (states k).2,rfl,fun _ ↦ rfl⟩
  have step (k) : q (k+1) = (q k).append (cut k (q k) (w.pos k)) (w.word (k+1)) := rfl
  have growth (k) : (q k).length < (q (k+1)).length := by rw [step]; exact Nat.lt_succ_of_le (le_max_left ..)
  have agree (k j) (hj : j < (q k).length) : (q (k+1)).stream j = (q k).stream j := by
    rw [step]; exact Stage.append_agrees _ _ _ _ (hj.trans_le (le_max_left ..))
  let s := stageLimit q
  let p := sequenceLaw s
  have hs0 : 0 ∈ Set.range s := ⟨0,stageLimit_agrees q growth agree 0 0 (show 0 < 1 by decide)⟩
  have history (k) : Set.range (q k).stream = w.past k := by
    induction k with
    | zero =>
      ext x; change (∃ _j : ℕ, 0 = x) ↔ ∃ t ≤ 0, w.word t = x
      simp [Walk.word,w.first,cell,Nat.pair]
    | succ k ih =>
      rw [step,Stage.append_range,ih]
      ext x
      change (x = w.word (k+1) ∨ ∃ t ≤ k, w.word t = x) ↔ ∃ t ≤ k+1, w.word t = x
      constructor
      · rintro (rfl | ⟨t,ht,rfl⟩)
        · exact ⟨k+1,le_rfl,rfl⟩
        · exact ⟨t,by omega,rfl⟩
      · rintro ⟨t,ht,rfl⟩
        by_cases h : t = k+1
        · exact Or.inl (congrArg w.word h)
        · exact Or.inr ⟨t,by omega,rfl⟩
  have support : p.support = Set.range w.word := by
    rw [show p.support = _ from (sequenceLaw_support s).trans (stageLimit_range q growth agree hs0)]
    simp_rw [history]
    ext x
    exact ⟨fun hx ↦ by obtain ⟨k,t,_,h⟩ := Set.mem_iUnion.mp hx; exact ⟨t,h⟩,
      fun ⟨t,h⟩ ↦ Set.mem_iUnion.mpr ⟨t,t,le_rfl,h⟩⟩
  obtain ⟨i,hi⟩ := w.contains_language
  rw [←support] at hi
  refine ⟨p,⟨i,hi⟩,unbounded_witness_index p ((infinite_languages i).mono hi) ?_,?_⟩
  · rw [support]; rintro x ⟨t,rfl⟩; simp [Walk.word,cell]
  · let N := fun k ↦ n k (q k) (w.pos k)
    have bound (k) : 1/2-tolerance k < probability (joint G p (N k)) (rowEvent (q k) (w.pos k) (w.switch k)) :=
      freeze k (q k) (w.pos k) s (fun j hj ↦
        (stageLimit_agrees q growth agree (k+1) j (by rw [step]; exact Nat.lt_succ_of_lt (hj.trans_le (le_max_right ..)))).trans
          (Stage.append_agrees (q k) _ _ _ (hj.trans_le (le_max_right ..))))
    have often : ∃ᶠ k : ℕ in atTop, 1/2-tolerance k ≤ genErr G p (N k) := by
      by_cases h : ∃ᶠ k : ℕ in atTop, w.switch k = true
      · apply h.mono
        intro k hk
        apply (bound k).le.trans (probability_mono _ ?_)
        rw [hk]; intro z hz
        exact Or.inl fun hx ↦ Set.disjoint_left.mp (w.no_return hk) (support ▸ hx) hz
      · rw [Filter.not_frequently] at h
        obtain ⟨k0,h0⟩ := eventually_atTop.mp h
        apply ((eventually_ge_atTop k0).mono ?_).frequently
        intro k hk
        have stay (m) (hm : k ≤ m) : w.switch m = false := by simpa using h0 m (hk.trans hm)
        apply (bound k).le.trans (probability_mono _ ?_)
        rw [stay k le_rfl]
        intro z hz
        change z.2 ∉ beyond _ _ ∧ _ at hz
        by_cases hmem : z.2 ∈ p.support
        · exact Or.inr (hz.2 _ (history k ▸ ((w.stay_support stay (support ▸ hmem)).resolve_right hz.1)))
        · exact Or.inl hmem
    by_contra! h
    obtain ⟨r,hr₁,hr₂⟩ := exists_between h
    have he := tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const (sub_pos.mpr hr₂)
    have hits : ∃ᶠ n' : ℕ in atTop, r ≤ genErr G p n' := by
      apply frequently_atTop.mpr
      intro m
      obtain ⟨k,hk,hm,he'⟩ := (often.and_eventually ((eventually_ge_atTop m).and he)).exists
      exact ⟨N k,hm.trans (hn ..),by dsimp [tolerance] at hk; linarith⟩
    exact (not_le_of_gt hr₁) (le_limsup_of_frequently_le hits (isBoundedUnder_of ⟨1,fun _ ↦ probability_le_one ..⟩))

end
end GenLimit.AgnosticLanguage
