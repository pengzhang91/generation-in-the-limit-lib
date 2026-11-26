import GenLimit.Paper26_IdentificationWithComputationalTrace.FiniteControl

namespace GenLimit.ComputationalTrace.Control
variable {μ O A σ : Type} {D : Device μ O A} {M : Machine σ O A}

/-- The list contains each pre-transition configuration and excludes the endpoint. -/
inductive Path (D : Device μ O A) (M : Machine σ O A) :
    Frame σ μ → List (Frame σ μ) → Frame σ μ → Prop
  | refl (c) : Path D M c [] c
  | cons {c d z cs} (live : isFinal D M c = false) (edge : move D M c = some d)
      (tail : Path D M d cs z) : Path D M c (c :: cs) z

theorem Path.single {c d : Frame σ μ} (h : isFinal D M c = false) (e : move D M c = some d) :
    Path D M c [c] d := .cons h e (.refl d)

theorem Path.append {c d z l r} (p : Path D M c l d) (q : Path D M d r z) :
    Path D M c (l ++ r) z := by
  induction p with
  | refl => exact q
  | cons h e _ ih => exact .cons h e (ih q)

theorem Path.finish {c d l ds} (p : Path D M c l d) (f : Finish D M d ds) :
    ∃ xs, c :: xs = l ++ d :: ds ∧ Finish D M c xs := by
  induction p with
  | refl => exact ⟨ds,rfl,f⟩
  | cons h e _ ih =>
    obtain ⟨xs,hh,hf⟩ := ih f
    exact ⟨_ :: xs,congrArg (List.cons _) hh,.next h e hf⟩

theorem Path.finish_at_end {c d l xs} (p : Path D M c l d) (f : Finish D M c xs) :
    ∃ ys, Finish D M d ys := by
  induction p generalizing xs with
  | refl => exact ⟨_,f⟩
  | cons live edge _ ih =>
    cases f with
    | halt h => simp_all
    | next _ e tail =>
      obtain rfl := Option.some.inj (edge.symm.trans e)
      exact ih tail

end GenLimit.ComputationalTrace.Control
