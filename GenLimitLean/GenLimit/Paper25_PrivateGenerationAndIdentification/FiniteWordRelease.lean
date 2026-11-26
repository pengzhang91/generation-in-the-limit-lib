import GenLimit.Paper25_PrivateGenerationAndIdentification.FinitePrivateCore
import GenLimit.Paper24_PriceOfPrivacy.GenerationRelease

/-! Appendix C.1. The set selection uses only the input sample. The
postprocessing also takes a public horizon: the word can be held throughout
an epoch while avoiding every input up to the end of that epoch. -/
namespace GenLimit.PrivateLimit.FiniteCore

open Set DiscreteIID PriceOfPrivacy
open scoped Classical ENNReal
noncomputable section

def errorTerm (k d n : ℕ) (ε : ℝ) := Real.exp (-ε*((n:ℝ)-d)/(2*k))

def poolSize (H : ℕ) (b : ℝ) := ⌈(H:ℝ)/b⌉₊+1

instance (H : ℕ) (b : ℝ) : NeZero (poolSize H b) := ⟨Nat.succ_ne_zero _⟩

private theorem pool_bound (H : ℕ) {b : ℝ} (hb : 0 < b) : (H:ℝ)/poolSize H b ≤ b := by
  have le := Nat.le_ceil ((H:ℝ)/b)
  have h : (H:ℝ)/b ≤ poolSize H b := by unfold poolSize; push_cast; linarith
  apply (div_le_iff₀ (by exact_mod_cast Nat.succ_pos _ : (0:ℝ) < poolSize H b)).mpr
  linarith [(div_le_iff₀ hb).mp h]

def wordRelease {k : ℕ} (C : Fin k → Set ℕ) (d n H : ℕ) (ε : ℝ) (xs : List ℕ) : PMF ℕ :=
  (select C d n ε xs).bind fun S =>
    (PMF.uniformOfFintype (Fin (poolSize H (errorTerm k d n ε)))).map
      fun j => Generation.word (Equiv.refl ℕ) (core C S) j.val

theorem word_private {k : ℕ} (C : Fin k → Set ℕ) (d n H : ℕ) {ε : ℝ} (he : 0 < ε) :
    PrivateAt ε 0 n (wordRelease C d n H ε) :=
  privateAt_random_map (privateAt C d n he) _ _

/-- The avoidance list may include the rest of a fixed input enumeration up
to a public horizon. Its contents never enter the mechanism. -/
theorem word_failure {k : ℕ} (C : Fin k → Set ℕ) {d : ℕ}
    (bound : SubcollectionClosureBound (range C) d) {ε : ℝ} (he : 0 < ε)
    (z : Fin k) (xs avoid : List ℕ) (nd : xs.Nodup) (inK : ∀ x ∈ xs, x ∈ C z) :
    probability (wordRelease C d xs.length avoid.length ε xs) {x | x ∉ C z ∨ x ∈ avoid} ≤
      5*errorTerm k d xs.length ε := by
  let b := errorTerm k d xs.length ε
  have hb : 0 < b := Real.exp_pos _
  let q := PMF.uniformOfFintype (Fin (poolSize avoid.length b))
  let F := {x | x ∉ C z ∨ x ∈ avoid}
  let draw (S : Finset (Fin k)) (j : Fin (poolSize avoid.length b)) :=
    Generation.word (Equiv.refl ℕ) (core C S) j.val
  have good (S : Finset (Fin k)) (_ : S ∈ (select C d xs.length ε xs).support)
      (h : S ∉ {S | ¬safe C z S}) : probability (q.map (draw S)) F ≤ b := by
    have hs : safe C z S := Classical.not_not.mp h
    have eq : draw S ⁻¹' F = {j | draw S j ∈ avoid} := by
      ext j
      have mem : draw S j ∈ C z := hs.2 (Nat.nth_mem_of_infinite hs.1 j.val)
      exact or_iff_right (not_not_intro mem)
    rw [probability,PMF.toOuterMeasure_map_apply,eq]
    exact (Generation.collision (Equiv.refl ℕ) hs.1 avoid).trans (pool_bound _ hb)
  have p := bind_event_off_exception (select C d xs.length ε xs) (fun S => q.map (draw S))
    F {S | ¬safe C z S} hb.le good
  change probability _ F ≤ 5*b
  exact p.trans ((add_le_add_right (failure C bound he z xs nd inK) b).trans_eq (by dsimp [b,errorTerm]; ring))

/-- The finite-sample assertion of Theorem C.1 with the paper's constant. -/
theorem finite_generation {k : ℕ} (C : Fin k → Set ℕ) {d : ℕ}
    (bound : SubcollectionClosureBound (range C) d) (n : ℕ) {ε : ℝ} (he : 0 < ε) :
    ∃ A : List ℕ → PMF ℕ, PrivateAt ε 0 n A ∧ ∀ z xs, xs.length = n → xs.Nodup →
      (∀ x ∈ xs, x ∈ C z) →
      probability (A xs) {x | x ∉ C z ∨ x ∈ xs} ≤ 5*Real.exp (-ε*((n:ℝ)-d)/(2*k)) := by
  refine ⟨wordRelease C d n n ε,word_private C d n n he,?_⟩
  rintro z xs rfl nd inK
  exact word_failure C bound he z xs xs nd inK

end
end GenLimit.PrivateLimit.FiniteCore
