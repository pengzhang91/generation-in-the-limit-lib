import GenLimit.Paper26_IdentificationWithComputationalTrace.FiniteControl

namespace GenLimit.ComputationalTrace.Control

variable {μ O A : Type} (D : Device μ O A) (M : Machine ℕ O A)

def trim (qs : List ℕ) : Machine (Option (Fin qs.length)) O A :=
  ⟨locateState qs M.initial, fun i => i.any fun j => M.final (qs.get j),
    fun i o => i.bind fun j => (M.table (qs.get j) o).map fun e => (locateState qs e.1,e.2)⟩

private theorem trim_final (qs : List ℕ) {q} (hq : q ∈ qs) :
    (trim M qs).final (locateState qs q) = M.final q := by
  simp [trim,locateState,hq,List.get_eq_getElem,List.getElem_idxOf]

private theorem trim_table (qs : List ℕ) {q} (hq : q ∈ qs) (o : O) :
    (trim M qs).table (locateState qs q) o =
    (M.table q o).map (fun e => (locateState qs e.1,e.2)) := by
  simp [trim,locateState,hq,List.get_eq_getElem,List.getElem_idxOf]

theorem Finish.trim (qs : List ℕ) {c ds} (hf : Finish D M c ds)
    (hc : ∀ e ∈ c :: ds, e.1 ∈ qs) :
    Finish D (Control.trim M qs) (locateState qs c.1,c.2)
      (ds.map fun e => (locateState qs e.1,e.2)) :=
  hf.relabel D M fun e he => ⟨trim_final M qs (hc e he),trim_table M qs (hc e he) _⟩

private theorem sink_rejects (qs : List ℕ) (m : μ) (n : ℕ) :
    acceptsWithin D (trim M qs) n (none,m) = false := by
  cases n <;> simp [acceptsWithin,isFinal,move,trim]

theorem trim_sound (qs : List ℕ) (n : ℕ) (q : ℕ) (m : μ)
    (hc : acceptsWithin D (trim M qs) n (locateState qs q,m) = true) :
    acceptsWithin D M n (q,m) = true := by
  induction n generalizing q m with
  | zero =>
    by_cases hq : q ∈ qs
    · simpa only [acceptsWithin,isFinal,trim_final M qs hq] using hc
    · simp [acceptsWithin,isFinal,trim,locateState,hq] at hc
  | succ n ih =>
    by_cases hq : q ∈ qs
    · simp only [acceptsWithin,isFinal,trim_final M qs hq,move,trim_table M qs hq,
        Bool.or_eq_true,Option.map_map] at hc ⊢
      rcases hc with h | h
      · exact Or.inl h
      · right
        cases he : M.table q (D.read m) with
        | none => simp [he] at h
        | some v =>
          simp only [he,Option.map_some,Function.comp_apply,Option.any_some] at h ⊢
          exact ih _ _ h
    · rw [show locateState qs q = none by simp [locateState,hq],sink_rejects] at hc
      contradiction

end GenLimit.ComputationalTrace.Control
