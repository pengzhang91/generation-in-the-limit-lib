import GenLimit.Paper24_PriceOfPrivacy.PrivateSelection
import GenLimit.Paper24_PriceOfPrivacy.IdentificationScores

/-! The finite-sample pure and Gaussian identifiers of Theorem 3.4. -/
namespace GenLimit.PriceOfPrivacy.Identification

open AgnosticLanguage DiscreteIID Set Selection
open scoped Classical
noncomputable section

def pureIdentifier (C : Generic.LanguageFamily X) (w : ℕ) [NeZero w] (n : ℕ) (ε : ℝ) :
    Identifier X := pureLaw (empiricalScore C w) (2/n) ε

def gaussianIdentifier (C : Generic.LanguageFamily X) (w : ℕ) [NeZero w] (n : ℕ) (ε δ : ℝ) :
    Identifier X := gaussianLaw (empiricalScore C w) (2/n) ε δ

private theorem risk_bound [Countable X] (C : Generic.LanguageFamily X) (p : PMF X)
    {w n : ℕ} (hw : 3 ≤ w) (hn : 0 < n) (A : Identifier X) (target : Fin w)
    (optimal : Optimal C p target.val) {b : ℝ} (hb : 0 ≤ b)
    (utility : ∀ xs, accurate C p w xs → probability (A xs) {j | j ≠ target.val} ≤ b) :
    idErr C A p n ≤ 2*w*Real.exp (-(n:ℝ)/(8*w^2))+b := by
  calc
    _ ≤ _ := idErr_le_failure C A p n
    _ ≤ probability ((samples p n).bind A) {j | j ≠ target.val} :=
      probability_mono _ (fun _ hj heq => hj (heq ▸ optimal))
    _ ≤ probability (samples p n) {xs | ¬accurate C p w xs} + b :=
      bind_event_off_exception _ A _ _ hb (fun xs _ hx => utility xs (Classical.not_not.mp hx))
    _ ≤ _ := add_le_add_right (inaccurate_probability C p hn (by omega : 0 < w)) _

theorem private_identification [Countable X] (C : Generic.LanguageFamily X) (p : PMF X)
    {w n : ℕ} [NeZero w] (hw : 3 ≤ w) (hn : 0 < n) (target : Fin w)
    (optimal : Optimal C p target.val)
    (earlier : ∀ j < target, 3/(w:ℝ) ≤ risk p (C j.val)-risk p (C target.val)) :
    (∀ ε : ℝ, 0 < ε → PrivateAt ε 0 n (pureIdentifier C w n ε) ∧
      idErr C (pureIdentifier C w n ε) p n ≤
        2*w*Real.exp (-(n:ℝ)/(8*w^2)) + w*Real.exp (-ε*n/(4*w))) ∧
    (∀ ε δ : ℝ, ε ∈ Ioo 0 1 → δ ∈ Ioo 0 1 → PrivateAt ε δ n (gaussianIdentifier C w n ε δ) ∧
      idErr C (gaussianIdentifier C w n ε δ) p n ≤ 2*w*Real.exp (-(n:ℝ)/(8*w^2)) +
        2*w*Real.exp (-ε^2*n^2/(64*w^3*Real.log ((5/4)/δ)))) := by
  have nw : (0:ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have nn : (0:ℝ) < n := by exact_mod_cast hn
  have sens : SensitiveAt (empiricalScore C w) (2/n) n := fun pre x y post len i =>
    sensitivity C w pre x y post hn len i
  have gaps (xs : List X) (good : accurate C p w xs) (i : Fin w) (hi : i.val ≠ target.val) :=
    score_gap C p hw target optimal earlier good i (fun h => hi (congrArg Fin.val h))
  constructor
  · intro ε he
    refine ⟨pure_private (by positivity) he sens, risk_bound C p hw hn _ target optimal (by positivity) ?_⟩
    intro xs good
    apply (pure_gap (by positivity : 0 < 2/(n:ℝ)) he xs {j | j ≠ target.val} target (gaps xs good)).trans_eq
    congr 2
    field_simp
    ring
  · intro ε δ he hδ
    refine ⟨gaussian_private (by positivity) he hδ sens, risk_bound C p hw hn _ target optimal (by positivity) ?_⟩
    intro xs good
    apply (gaussian_gap (Δ := 2/n) (ε := ε) (δ := δ) (by positivity : 0 < 1/(w:ℝ))
      xs {j | j ≠ target.val} target (gaps xs good)).trans_eq
    rw [variance_value (by positivity) he.1 hδ]
    have hl : 0 < Real.log ((5/4)/δ) := Real.log_pos ((lt_div_iff₀ hδ.1).mpr (by linarith [hδ.2]))
    congr 2
    field_simp [he.1.ne',hl.ne']
    ring

end
end GenLimit.PriceOfPrivacy.Identification
