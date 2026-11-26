import GenLimit.Paper24_PriceOfPrivacy.GenerationRelease
import GenLimit.Paper24_PriceOfPrivacy.GenerationScores
import GenLimit.Paper24_PriceOfPrivacy.PrivateSelection

/-! Finite-sample generation under pure and approximate replacement privacy.
The public score reads one prefix. The unknown-witness score uses only the
public cap parameter and takes a supremum over levels. -/
namespace GenLimit.PriceOfPrivacy.Generation

open AgnosticLanguage DiscreteIID Selection Set
open scoped Classical
noncomputable section

def publicScores (u : ℕ ≃ X) (C : Generic.LanguageFamily X) (f W : ℕ) (xs : List X) (i : Fin f) :=
  prefixCount u (C i.val) xs W

def unknownScores (u : ℕ ≃ X) (C : Generic.LanguageFamily X) (f : ℕ) (g : ℝ) (xs : List X) (i : Fin f) :=
  depthScore u (C i.val) xs g

def pureGenerator (u : ℕ ≃ X) (C : Generic.LanguageFamily X) {f : ℕ} [NeZero f] (n : ℕ)
    (s : List X → Fin f → ℝ) (ε : ℝ) : StatisticalGenerator X := release u C n (pureLaw s 1 ε)

def gaussianGenerator (u : ℕ ≃ X) (C : Generic.LanguageFamily X) {f : ℕ} [NeZero f] (n : ℕ)
    (s : List X → Fin f → ℝ) (ε δ : ℝ) : StatisticalGenerator X := release u C n (gaussianLaw s 1 ε δ)

private theorem rates (u : ℕ ≃ X) (C : Generic.LanguageFamily X) (inf : ∀ i, (C i).Infinite)
    (p : PMF X) {f : ℕ} [NeZero f] (n W : ℕ) (target : Fin f) (safe : C target.val ⊆ p.support)
    (s : List X → Fin f → ℝ) (sens : SensitiveAt s 1 n) {Γ : ℝ} (hg : 0 < Γ)
    (gap : ∀ xs ∈ (samples p n).support, covered u (C target.val) p W n xs →
      ∀ i : Fin f, ¬C i.val ⊆ p.support → Γ ≤ s xs target - s xs i) :
    (∀ ε : ℝ, 0 < ε → PrivateAt ε 0 n (pureGenerator u C n s ε) ∧
      genErr (pureGenerator u C n s ε) p n ≤ W*Real.exp (-(n:ℝ)*massFloor u (C target.val) p W/8) +
        f*Real.exp (-ε*Γ/2) + n/(2:ℝ)^n) ∧
    (∀ ε δ : ℝ, ε ∈ Ioo 0 1 → δ ∈ Ioo 0 1 → PrivateAt ε δ n (gaussianGenerator u C n s ε δ) ∧
      genErr (gaussianGenerator u C n s ε δ) p n ≤ W*Real.exp (-(n:ℝ)*massFloor u (C target.val) p W/8) +
        2*f*Real.exp (-ε^2*Γ^2/(16*f*Real.log ((5/4)/δ))) + n/(2:ℝ)^n) := by
  let B := {xs | ¬covered u (C target.val) p W n xs}
  have failure := cover_failure u (C target.val) p W n safe
  have bound (A : Identifier X) (b : ℝ) (hb : 0 ≤ b)
      (cond : ∀ xs ∈ (samples p n).support, xs ∉ B → probability (A xs) {i | ¬C i ⊆ p.support} ≤ b) :=
    (generation_error u C inf p A n B hb cond).trans
      (add_le_add_right (add_le_add_right failure b) ((n:ℝ)/2^n))
  constructor
  · intro ε he
    refine ⟨release_private u C (pure_private zero_lt_one he sens),bound _ _ (by positivity) ?_⟩
    intro xs hx good
    apply (pure_gap zero_lt_one he xs {i | ¬ C i ⊆ p.support} target (gap xs hx (Classical.not_not.mp good))).trans_eq
    congr 2
    ring
  · intro ε δ he hd
    refine ⟨release_private u C (gaussian_private zero_lt_one he hd sens),bound _ _ (by positivity) ?_⟩
    intro xs hx good
    apply (gaussian_gap (Δ := 1) (ε := ε) (δ := δ) hg xs {i | ¬C i ⊆ p.support} target
      (gap xs hx (Classical.not_not.mp good))).trans_eq
    rw [variance_value zero_lt_one he.1 hd]
    have hl : 0 < Real.log ((5/4)/δ) := Real.log_pos ((lt_div_iff₀ hd.1).mpr (by linarith [hd.2]))
    have hf : (0:ℝ) < f := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne f)
    congr 2
    field_simp [he.1.ne',hl.ne']
    ring

theorem public_generation (u : ℕ ≃ X) (C : Generic.LanguageFamily X) (inf : ∀ i, (C i).Infinite)
    (p : PMF X) {f : ℕ} [NeZero f] (n W : ℕ) (hn : 0 < n)
    (witness : WitnessBy u C p W) (t : Fin f) (safe : C t.val ⊆ p.support) :
    (∀ ε : ℝ, 0 < ε → PrivateAt ε 0 n (pureGenerator u C n (publicScores u C f W) ε) ∧
      genErr (pureGenerator u C n (publicScores u C f W) ε) p n ≤
        W*Real.exp (-(n:ℝ)*massFloor u (C t.val) p W/8) +
        f*Real.exp (-ε*n*massFloor u (C t.val) p W/4) + n/(2:ℝ)^n) ∧
    (∀ ε δ : ℝ, ε ∈ Ioo 0 1 → δ ∈ Ioo 0 1 →
      PrivateAt ε δ n (gaussianGenerator u C n (publicScores u C f W) ε δ) ∧
      genErr (gaussianGenerator u C n (publicScores u C f W) ε δ) p n ≤
        W*Real.exp (-(n:ℝ)*massFloor u (C t.val) p W/8) +
        2*f*Real.exp (-ε^2*n^2*(massFloor u (C t.val) p W)^2/(64*f*Real.log ((5/4)/δ))) + n/(2:ℝ)^n) := by
  let m := massFloor u (C t.val) p W
  have mpos : 0 < m := massFloor_pos u (C t.val) p W safe
  have h := rates u C inf p n W t safe (publicScores u C f W)
    (fun pre x y post _ i => prefix_sensitive u (C i.val) pre x y post W)
    (by positivity : 0 < n*m/2) (fun xs hx ok i bad => by
      obtain ⟨len,sup⟩ := (samples_support p n xs).mp hx
      have high := target_count u (C t.val) p W n len ok
      have low := bad_count u C p witness bad sup (le_refl W)
      unfold publicScores; dsimp [m]; linarith)
  constructor
  · intro ε he
    convert h.1 ε he using 1
    dsimp [m]; ring_nf
  · intro ε δ he hd
    convert h.2 ε δ he hd using 1
    dsimp [m]; ring_nf

theorem unknown_generation (u : ℕ ≃ X) (C : Generic.LanguageFamily X) (inf : ∀ i, (C i).Infinite)
    (p : PMF X) {f : ℕ} [NeZero f] (n W : ℕ) (hw : 0 < W)
    (witness : WitnessBy u C p W) (t : Fin f) (safe : C t.val ⊆ p.support)
    (g : ℝ) (hg : 0 < g) (cap : g ≤ n*massFloor u (C t.val) p W/2) :
    (∀ ε : ℝ, 0 < ε → PrivateAt ε 0 n (pureGenerator u C n (unknownScores u C f g) ε) ∧
      genErr (pureGenerator u C n (unknownScores u C f g) ε) p n ≤
        W*Real.exp (-(n:ℝ)*massFloor u (C t.val) p W/8) +
        f*Real.exp (-ε*g/(2*W*(W+1))) + n/(2:ℝ)^n) ∧
    (∀ ε δ : ℝ, ε ∈ Ioo 0 1 → δ ∈ Ioo 0 1 →
      PrivateAt ε δ n (gaussianGenerator u C n (unknownScores u C f g) ε δ) ∧
      genErr (gaussianGenerator u C n (unknownScores u C f g) ε δ) p n ≤
        W*Real.exp (-(n:ℝ)*massFloor u (C t.val) p W/8) +
        2*f*Real.exp (-ε^2*g^2/(16*W^2*(W+1)^2*f*Real.log ((5/4)/δ))) + n/(2:ℝ)^n) := by
  have hp : (0:ℝ) < W := by exact_mod_cast hw
  have h := rates u C inf p n W t safe (unknownScores u C f g)
    (fun pre x y post _ i => depth_sensitive u (C i.val) pre x y post g)
    (by positivity : 0 < g/((W:ℝ)*(W+1))) (fun xs hx ok i bad => by
      obtain ⟨len,sup⟩ := (samples_support p n xs).mp hx
      cases W with
      | zero => omega
      | succ W => exact private_depth_gap u C p witness bad len sup ok hg cap)
  constructor
  · intro ε he
    have eq : -ε*(g/((W:ℝ)*(W+1)))/2 = -ε*g/(2*W*(W+1)) := by
      field_simp
    simpa only [eq] using h.1 ε he
  · intro ε δ he hd
    have hf : (0:ℝ) < f := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne f)
    have hl : 0 < Real.log ((5/4)/δ) := Real.log_pos ((lt_div_iff₀ hd.1).mpr (by linarith [hd.2]))
    have eq : -ε^2*(g/((W:ℝ)*(W+1)))^2/(16*f*Real.log ((5/4)/δ)) =
        -ε^2*g^2/(16*W^2*(W+1)^2*f*Real.log ((5/4)/δ)) := by
      field_simp [hl.ne']
    simpa only [eq] using h.2 ε δ he hd

end
end GenLimit.PriceOfPrivacy.Generation
