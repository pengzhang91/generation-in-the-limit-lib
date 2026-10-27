import GenLimit.Support.DiscreteIID

/-! # Lower bounds on the probability of a specified ordered IID sample -/

namespace GenLimit.DiscreteIID

noncomputable section

variable {α : Type*}

theorem samples_cons (p : PMF α) (x : α) (xs : List α) :
    samples p (xs.length + 1) (x :: xs) = p x * samples p xs.length xs := by
  classical
  rw [samples, PMF.bind_apply]
  have hm (y : α) : ((samples p xs.length).map (List.cons y)) (x :: xs) =
      if x = y then samples p xs.length xs else 0 := by
    rw [PMF.map_apply]
    by_cases h : x = y
    · subst y
      simp only [List.cons.injEq, true_and, ite_true]
      rw [tsum_eq_single xs]
      · simp
      · intro a ha
        exact if_neg (Ne.symm ha)
    · simp [List.cons.injEq, h]
  simp_rw [hm]
  simp only [mul_ite, mul_zero]
  rw [tsum_eq_single x]
  · simp
  · intro a ha
    exact if_neg (Ne.symm ha)

/-- A uniform lower bound on the masses of the observed points multiplies. -/
theorem samples_atom_lower_bound (p : PMF α) (xs : List α) (d : ℝ) (hd : 0 ≤ d)
    (hxs : ∀ x ∈ xs, d ≤ (p x).toReal) :
    d ^ xs.length ≤ (samples p xs.length xs).toReal := by
  induction xs with
  | nil => simp [samples]
  | cons x xs ih =>
    rw [List.length_cons, samples_cons, ENNReal.toReal_mul, pow_succ']
    exact mul_le_mul (hxs x (by simp)) (ih (fun y hy => hxs y (by simp [hy])))
      (pow_nonneg hd _) ENNReal.toReal_nonneg

end
end GenLimit.DiscreteIID
