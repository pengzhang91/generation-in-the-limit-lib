import GenLimit.Paper23_BanachDensityTopologyAndGeometry.ForestMatching
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.SpatialBins
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.FiniteHistory

/-! A finite-history generator for the finite-rank theorem. The first word
seen in each bin fixes its matching for the rest of the play. On each
observation the generator outputs its mate if fresh, and otherwise uses
an unseen word from the current accurate-selector hypothesis. -/
namespace GenLimit.KleinbergWei.Banach.IntervalGenerator
open Set Filter TowerTopology DensityMeasures DensityMeasures.FiniteRankParent
open scoped Classical
noncomputable section
variable {C : LanguageFamily} {R : ℕ} (hr : FiniteRankAtMost (FamilySpace C) R)
  (B : SpatialBins C) (inf : ∀ z, (C z).Infinite)

private def visit (s : ℕ → ℕ) (j : ℕ) :=
  if h : ∃ t, B.number (s t)=j then Nat.find h else 0

private theorem first_visit {s : ℕ → ℕ} {j t} (hit : B.number (s t)=j) :
    B.number (s (visit B s j))=j ∧ visit B s j ≤ t ∧
      ∀ i < visit B s j, B.number (s i) ≠ j := by
  have ex : ∃ i, B.number (s i)=j := ⟨t,hit⟩
  rw [visit,dif_pos ex]
  exact ⟨Nat.find_spec ex,Nat.find_min' ex hit,fun _ hi => Nat.find_min ex hi⟩

def seed (s : ℕ → ℕ) (j : ℕ) :=
  familyPoint C (indexHistoryRule C (textPrefix s (visit B s j+1)))

def planned (s : ℕ → ℕ) (x : ℕ) :=
  ForestMatching.mate hr (B.cell (B.number x)) (seed B s (B.number x)) x

private theorem prefix_planned (s : ℕ → ℕ) (t : ℕ) :
    planned hr B (Generic.historyThenFallback (textPrefix s (t+1)) 0) (s t) =
      planned hr B s (s t) := by
  let r := Generic.historyThenFallback (textPrefix s (t+1)) 0
  let j := B.number (s t)
  have agree (a : ℕ) (h : a ≤ t) : r a = s a := by
    simp [r,Generic.historyThenFallback,textPrefix,show a < t+1 by omega]
  obtain ⟨a,al,am⟩ := first_visit B (s:=s) (j:=j) (t:=t) rfl
  obtain ⟨b,bl,bm⟩ := first_visit B (s:=r) (j:=j) (t:=t) (by rw [agree t le_rfl])
  have eq : visit B r j=visit B s j := by
    apply le_antisymm
    · exact le_of_not_gt fun lt => bm _ lt (by rwa [agree _ al])
    · exact le_of_not_gt fun lt => am _ lt (by rwa [←agree _ bl])
  have pre : textPrefix r (visit B s j+1)=textPrefix s (visit B s j+1) := by
    unfold textPrefix
    apply List.map_congr_left
    intro a ha; exact agree a ((Nat.le_of_lt_succ (List.mem_range.mp ha)).trans al)
  change ForestMatching.mate _ _ (familyPoint C (indexHistoryRule C (textPrefix r (visit B r j+1)))) _ = _
  rw [eq,pre]; rfl

private def emit (xs : List ℕ) (x : ℕ) (old : Finset ℕ) :=
  let used := xs.toFinset ∪ old
  let plan := planned hr B (Generic.historyThenFallback xs 0) x
  if h : ∃ y, plan=some y ∧ y ∉ used then h.choose
  else ((inf (indexHistoryRule C xs)).exists_notMem_finset used).choose

private structure State where
  inputs : List ℕ
  outputs : Finset ℕ
  last : ℕ

private def advance (q : State) (x : ℕ) : State :=
  let xs := q.inputs++[x]
  let y := emit hr B inf xs x q.outputs
  ⟨xs, insert y q.outputs,y⟩

private def run (xs : List ℕ) := xs.foldl (advance hr B inf) ⟨[],∅,0⟩

private theorem run_push (xs : List ℕ) (x : ℕ) :
    run hr B inf (xs++[x]) = advance hr B inf (run hr B inf xs) x := by simp [run]

private theorem inputs_eq (xs : List ℕ) : (run hr B inf xs).inputs=xs := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x ih => rw [run_push]; change _++[x]=_; rw [ih]

def rule (xs : List ℕ) := (run hr B inf xs).last

private def earned (s : ℕ → ℕ) (t : ℕ) := (run hr B inf (textPrefix s t)).outputs

private theorem play_eq (s : ℕ → ℕ) (t : ℕ) :
    OrderedFocus.play (rule hr B inf) s t =
      emit hr B inf (textPrefix s (t+1)) (s t) (earned hr B inf s t) := by
  change (run hr B inf (textPrefix s (t+1))).last=_
  rw [textPrefix_succ,run_push]; simp [advance,inputs_eq,earned]

private theorem mem_earned {s : ℕ → ℕ} {t x} :
    x ∈ earned hr B inf s t ↔ ∃ i < t, OrderedFocus.play (rule hr B inf) s i=x := by
  induction t with
  | zero => simp [earned,run]
  | succ t ih =>
    have step : earned hr B inf s (t+1) =
        insert (OrderedFocus.play (rule hr B inf) s t) (earned hr B inf s t) := by
      rw [play_eq]; unfold earned; rw [textPrefix_succ,run_push]; simp [advance,inputs_eq]
    rw [step,Finset.mem_insert,ih]
    constructor
    · rintro (e | ⟨i,hi,e⟩)
      · exact ⟨t,by omega,e.symm⟩
      · exact ⟨i,by omega,e⟩
    · rintro ⟨i,hi,e⟩; by_cases eq : i=t
      · exact Or.inl (eq ▸ e.symm)
      · exact Or.inr ⟨i,by omega,e⟩

private theorem decision (s : ℕ → ℕ) (t : ℕ) :
    let y := OrderedFocus.play (rule hr B inf) s t
    let used := (textPrefix s (t+1)).toFinset ∪ earned hr B inf s t
    y ∉ used ∧ (planned hr B s (s t)=some y ∨ y ∈ C (guessIndex C s (t+1))) ∧
    ∀ v, planned hr B s (s t)=some v → v ∉ used → y=v := by
  rw [play_eq]; dsimp only
  unfold emit
  dsimp only
  rw [prefix_planned]
  split
  next h =>
    obtain ⟨choice,fresh⟩ := h.choose_spec
    exact ⟨fresh,Or.inl choice,fun v eq _ => Option.some.inj (choice.symm.trans eq)⟩
  next no =>
    obtain ⟨inside,fresh⟩ := ((inf (indexHistoryRule C (textPrefix s (t+1)))).exists_notMem_finset
      ((textPrefix s (t+1)).toFinset ∪ earned hr B inf s t)).choose_spec
    exact ⟨fresh,Or.inr ((congrArg C (indexHistoryRule_prefix C s (t+1))) ▸ inside),
      fun v eq fresh => (no ⟨v,eq,fresh⟩).elim⟩

/-- Once a bin's first visit is after stabilization its entire protected
matching restricts to the true target. Only finitely many earlier bins
can ever produce errors. -/
theorem eventual_seed {s : ℕ → ℕ} {z : ℕ} (pres : Presents s (C z)) :
    ∃ J, ∀ j ≥ J, (∃ t, B.number (s t)=j) →
      StaticForest.Reaches hr (seed B s j) (familyPoint C z) := by
  obtain ⟨T,good⟩ := StaticForest.guesses_reach hr pres
  let n := (Finset.range T).sup fun t => B.number (s t)
  refine ⟨n+1,?_⟩
  rintro j hj ⟨t,hit⟩
  have here := (first_visit B hit).1
  have late : T ≤ visit B s j := by
    by_contra! early
    have h : B.number (s (visit B s j)) ≤ n := Finset.le_sup (f:=fun i => B.number (s i)) (Finset.mem_range.mpr early)
    omega
  simpa [seed,indexHistoryRule_prefix] using (good _ late).1

theorem validity {s : ℕ → ℕ} {z : ℕ} (pres : Presents s (C z)) :
    OrderedFocus.ElementValid s (OrderedFocus.play (rule hr B inf) s) (C z) := by
  let g := OrderedFocus.play (rule hr B inf) s
  obtain ⟨J,cert⟩ := eventual_seed hr B pres
  obtain ⟨T,good⟩ := StaticForest.guesses_reach hr pres
  have fresh (t i : ℕ) (hi : i<t) : g i ≠ g t := fun eq =>
    (decision hr B inf s t).1 (Finset.mem_union_right _ ((mem_earned hr B inf).mpr ⟨i,hi,eq⟩))
  have inject : Function.Injective g := by
    intro i j eq
    rcases lt_trichotomy i j with lt | same | gt
    · exact (fresh _ _ lt eq).elim
    · exact same
    · exact (fresh _ _ gt eq.symm).elim
  have esc : Tendsto g atTop atTop := by simpa [Nat.cofinite_eq_atTop] using inject.tendsto_cofinite
  obtain ⟨N,far⟩ := eventually_atTop.mp (esc.eventually (eventually_ge_atTop (B.edge J)))
  refine ⟨max T N,?_⟩
  intro t ht
  obtain ⟨avoid,whereFrom,_⟩ := decision hr B inf s t
  refine ⟨?_,fun i hi eq => avoid (Finset.mem_union_left _ (List.mem_toFinset.mpr (mem_textPrefix_iff.mpr ⟨i,by omega,eq⟩))),fresh t⟩
  rcases whereFrom with link | fallback
  · let j := B.number (s t)
    have bin : g t ∈ B.cell j := (ForestMatching.mate_spec hr _ _ link).2.1
    have validBin : J ≤ j := by
      by_contra! low
      have upper := (Finset.mem_Ico.mp bin).2.trans_le (B.strict.monotone (show j+1 ≤ J from low))
      exact upper.not_ge (far t (by omega))
    exact ForestMatching.target_closed hr _ _ (cert j validBin ⟨t,rfl⟩)
      (show s t ∈ C z by rw [←pres]; exact mem_range_self t) link
  · exact StaticForest.subset_of_reaches hr (good t (by omega)).1 fallback

/-- On an exact presentation, every mutual pair of target words has at
least one endpoint in the generated set, even if the inputs repeat. -/
theorem protects {s : ℕ → ℕ} {z x y} (pres : Presents s (C z)) (hx : x ∈ C z)
    (forward : planned hr B s x=some y) (back : planned hr B s y=some x) (distinct : x ≠ y) :
    x ∈ range (OrderedFocus.play (rule hr B inf) s) ∨ y ∈ range (OrderedFocus.play (rule hr B inf) s) := by
  by_contra! none
  have ex : ∃ t, s t=x ∨ s t=y := by
    obtain ⟨t,e⟩ := (show x ∈ range s from pres.symm ▸ hx); exact ⟨t,Or.inl e⟩
  let t := Nat.find ex
  have first := Nat.find_spec ex
  have must (a b : ℕ) (hit : s t=a) (neq : a ≠ b) (old : ∀ i < t, s i ≠ b)
      (plan : planned hr B s a=some b) (no : b ∉ range (OrderedFocus.play (rule hr B inf) s)) : False := by
    apply no; refine ⟨t,(decision hr B inf s t).2.2 b (hit ▸ plan) ?_⟩
    intro h; rcases Finset.mem_union.mp h with input | output
    · obtain ⟨i,hi,eq⟩ := mem_textPrefix_iff.mp (List.mem_toFinset.mp input)
      by_cases e : i=t
      · exact neq (hit.symm.trans (e ▸ eq))
      · exact old i (by omega) eq
    · obtain ⟨i,_,e⟩ := (mem_earned hr B inf).mp output; exact no ⟨i,e⟩
  rcases first with e | e
  · exact must x y e distinct (fun i hi eq => Nat.find_min ex hi (Or.inr eq)) forward none.2
  · exact must y x e distinct.symm (fun i hi eq => Nat.find_min ex hi (Or.inl eq)) back none.1

end
end GenLimit.KleinbergWei.Banach.IntervalGenerator
