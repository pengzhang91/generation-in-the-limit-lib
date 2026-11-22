import GenLimit.Paper39_DenseGeneration.Patient.Validity

/-! # Prefix and relabeling invariance of patient-scope focus selection -/
namespace GenLimit.PatientMachine

/-- Only these four fields affect the focus decision. -/
structure SameControl (a b : State) : Prop where
  scope : a.scope = b.scope
  tau : a.tau = b.tau
  age : a.age = b.age
  focus : a.focus = b.focus

private theorem critical_congr {C D : LanguageFamily} {s d : ℕ → ℕ} {t : ℕ}
    (hc : Consistent C s t = Consistent D d t)
    (hs : ∀ i j, C i ⊆ C j ↔ D i ⊆ D j) :
    RecursiveCritical C s t = RecursiveCritical D d t := by
  funext i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    cases i with
    | zero => simp [RecursiveCritical,hc]
    | succ i =>
      simp only [RecursiveCritical,hc]
      congr 1
      apply propext
      constructor <;> intro h j hj hjc
      · exact (hs _ _).1 (h j hj ((ih j (by omega)) ▸ hjc))
      · exact (hs _ _).2 (h j hj ((ih j (by omega)) ▸ hjc))

theorem decide_congr {C D : LanguageFamily} {s d : ℕ → ℕ} {t : ℕ} {a b : State}
    (h0 : Consistent C s t = Consistent D d t)
    (h1 : Consistent C s (t+1) = Consistent D d (t+1))
    (hs : ∀ i j, C i ⊆ C j ↔ D i ⊆ D j) (ha : SameControl a b) :
    decide C s t a = decide D d t b := by
  have c0 := critical_congr h0 hs
  have c1 := critical_congr h1 hs
  classical
  let update (consistent oldCrit newCrit : ℕ → Prop) (scope tau age focus : ℕ) : Decision :=
    let candidates := (Finset.range scope).filter consistent
    let guard := (Finset.range scope).filter (fun i ↦ oldCrit i ∧ newCrit i)
    if consistent focus then
      if 2 ^ tau ≤ age then
        let f := Support.greatestCandidateWithFallback ((Finset.range (scope+1)).filter newCrit) focus
        ⟨scope+1,if f = focus then tau else tau+1,f,.expand⟩
      else ⟨scope,tau,focus,.stay⟩
    else if candidates.Nonempty then
      let f := if guard.Nonempty then Support.greatestCandidateWithFallback guard focus
               else Support.leastCandidateWithFallback candidates focus
      ⟨f+1,tau+1,f,.backtrack⟩
    else
      let f := if h : ∃ i, consistent i then Nat.find h else focus
      if ∃ i, consistent i then ⟨f+1,tau+1,f,.backtrack⟩ else ⟨max scope 1,tau+1,focus,.backtrack⟩
  change update (Consistent C s (t+1)) (RecursiveCritical C s t) (RecursiveCritical C s (t+1))
      a.scope a.tau a.age a.focus = update (Consistent D d (t+1)) (RecursiveCritical D d t)
      (RecursiveCritical D d (t+1)) b.scope b.tau b.age b.focus
  rw [h1,c0,c1,ha.scope,ha.tau,ha.age,ha.focus]

theorem run_control_congr {O P : OracleFamily} {s d : ℕ → ℕ} (t : ℕ)
    (hc : ∀ u ≤ t, Consistent O.language s u = Consistent P.language d u)
    (hs : ∀ i j, O.language i ⊆ O.language j ↔ P.language i ⊆ P.language j) :
    SameControl (run O s t) (run P d t) := by
  induction t with
  | zero => exact ⟨rfl,rfl,rfl,rfl⟩
  | succ t ih =>
    have h := ih (fun u hu ↦ hc u (hu.trans (Nat.le_succ t)))
    have hd := decide_congr (hc t (Nat.le_succ t)) (hc _ le_rfl) hs h
    simp only [run_succ,processRound,hd,h.focus,h.age]
    exact ⟨rfl,rfl,rfl,rfl⟩

theorem run_focus_eventually_subset (O : OracleFamily) {s : ℕ → ℕ} {z : ℕ}
    (hp : Presents s (O.language z)) :
    ∃ T, ∀ t ≥ T, O.language (run O s (t+1)).focus ⊆ O.language z := by
  obtain ⟨Ts,hs⟩ := target_eventually_in_scope O s hp
  obtain ⟨Tc,hc⟩ := target_eventually_recursiveCritical hp
  exact ⟨max Ts Tc, fun t ht ↦ focus_subset_target (run_focus_isFocus O hp (t+1))
    (hs _ (by omega)) (hc _ (by omega))⟩

end GenLimit.PatientMachine
