import GenLimit.Support.DiscreteIID

/-!
# Fixed IID prefixes have sample-length-independent positive probability

The concatenation law splits an ordered IID sample into two independent
blocks. If every supported continuation after a fixed prefix satisfies an
event, the event has probability at least the mass of that prefix, regardless
of the continuation length. This is finite-sample infrastructure; no infinite
product probability space is needed.
-/

namespace GenLimit.DiscreteIID

noncomputable section

variable {α : Type*}

theorem samples_append (p : PMF α) (m n : ℕ) :
    samples p (m + n) = (samples p m).bind (fun xs => (samples p n).map (xs ++ ·)) := by
  induction m with
  | zero => simpa only [Nat.zero_add, samples, PMF.pure_bind, List.nil_append] using (PMF.map_id (samples p n)).symm
  | succ m ih =>
    rw [Nat.succ_add, samples, ih, samples, PMF.bind_bind]
    congr 1
    funext x
    simp only [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def, List.cons_append]

theorem probability_eq_one_of_support_subset (p : PMF α) (E : Set α) (hE : p.support ⊆ E) :
    probability p E = 1 := by
  rw [← probability_inter_support, Set.inter_eq_right.mpr hE]
  have h := probability_inter_support p Set.univ
  simpa using h

/-- A prefix cylinder contributes its full probability when all supported
continuations lie in the event. The bound is independent of `n`. -/
theorem probability_samples_append_ge (p : PMF α) (xs : List α) (n : ℕ) (E : Set (List α))
    (hE : ∀ tail ∈ (samples p n).support, xs ++ tail ∈ E) :
    (samples p xs.length xs).toReal ≤ probability (samples p (xs.length + n)) E := by
  rw [samples_append]
  have hprob : probability ((samples p n).map (xs ++ ·)) E = 1 := by
    apply probability_eq_one_of_support_subset
    intro ys hys
    obtain ⟨tail, ht, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hys
    exact hE tail ht
  have h := probability_bind_ge (samples p xs.length)
    (fun head => (samples p n).map (head ++ ·)) E xs
  simpa only [hprob, mul_one] using h

theorem samples_atom_pos (p : PMF α) (xs : List α) (hxs : ∀ x ∈ xs, x ∈ p.support) :
    0 < (samples p xs.length xs).toReal :=
  ENNReal.toReal_pos ((samples_support p xs.length xs).mpr ⟨rfl, hxs⟩)
    ((samples p xs.length).apply_ne_top xs)

end
end GenLimit.DiscreteIID
