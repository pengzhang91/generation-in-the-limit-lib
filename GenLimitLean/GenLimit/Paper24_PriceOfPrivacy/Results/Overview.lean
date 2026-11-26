import GenLimit.Paper24_PriceOfPrivacy.IdentificationUpper
import GenLimit.Paper24_PriceOfPrivacy.IdentificationLower
import GenLimit.Paper24_PriceOfPrivacy.GenerationUpper
import GenLimit.Paper24_PriceOfPrivacy.GenerationLower
import GenLimit.Paper24_PriceOfPrivacy.UnknownWitnessLower

/-! Main results of Li, Han, Jiang and Gao on the statistical price of
privacy for language identification and generation (arXiv:2604.07238v2). -/

namespace GenLimit.PriceOfPrivacy.Results

open AgnosticLanguage Filter Generation
open scoped ENNReal Topology

/-- Theorem 3.4. For each qualifying sample size and public horizon, the
signed-margin identifiers satisfy replacement privacy and the stated excess-risk
bounds. The window uses zero-based indices. The earlier-index condition expands
the paper's minimum risk gap, including its first-index convention. -/
theorem theorem_3_4 [Countable X] (C : Generic.LanguageFamily X) (p : PMF X)
    {w n : ℕ} [NeZero w] (hw : 3 ≤ w) (hn : 0 < n) (target : Fin w)
    (optimal : Optimal C p target.val)
    (earlier : ∀ j < target, 3/(w:ℝ) ≤ risk p (C j.val)-risk p (C target.val)) :
    (∀ ε : ℝ, 0 < ε → PrivateAt ε 0 n (Identification.pureIdentifier C w n ε) ∧
      idErr C (Identification.pureIdentifier C w n ε) p n ≤
        2*w*Real.exp (-(n:ℝ)/(8*w^2)) + w*Real.exp (-ε*n/(4*w))) ∧
    (∀ ε δ : ℝ, ε ∈ Set.Ioo 0 1 → δ ∈ Set.Ioo 0 1 →
      PrivateAt ε δ n (Identification.gaussianIdentifier C w n ε δ) ∧
      idErr C (Identification.gaussianIdentifier C w n ε δ) p n ≤ 2*w*Real.exp (-(n:ℝ)/(8*w^2)) +
        2*w*Real.exp (-ε^2*n^2/(64*w^3*Real.log ((5/4)/δ)))) :=
  Identification.private_identification C p hw hn target optimal earlier

/-- Theorem 4.4. The public prefix level W witnesses every bad language.
Both mechanisms sample a candidate from the selected language and
meet the stated generation-error bound, including the collision term. -/
theorem theorem_4_4 (u : ℕ ≃ X) (C : Generic.LanguageFamily X) (inf : ∀ i, (C i).Infinite)
    (p : PMF X) {f : ℕ} [NeZero f] (n W : ℕ) (hn : 0 < n)
    (witness : WitnessBy u C p W) (t : Fin f) (safe : C t.val ⊆ p.support) :
    (∀ ε : ℝ, 0 < ε → PrivateAt ε 0 n (pureGenerator u C n (publicScores u C f W) ε) ∧
      genErr (pureGenerator u C n (publicScores u C f W) ε) p n ≤
        W*Real.exp (-(n:ℝ)*massFloor u (C t.val) p W/8) +
        f*Real.exp (-ε*n*massFloor u (C t.val) p W/4) + n/(2:ℝ)^n) ∧
    (∀ ε δ : ℝ, ε ∈ Set.Ioo 0 1 → δ ∈ Set.Ioo 0 1 →
      PrivateAt ε δ n (gaussianGenerator u C n (publicScores u C f W) ε δ) ∧
      genErr (gaussianGenerator u C n (publicScores u C f W) ε δ) p n ≤
        W*Real.exp (-(n:ℝ)*massFloor u (C t.val) p W/8) +
        2*f*Real.exp (-ε^2*n^2*(massFloor u (C t.val) p W)^2/(64*f*Real.log ((5/4)/δ))) + n/(2:ℝ)^n) :=
  Generation.public_generation u C inf p n W hn witness t safe

/-- Theorem 4.5. The cap profile uses only g and the level. The witness W
and the mass floor enter the guarantee for the two private generators. -/
theorem theorem_4_5 (u : ℕ ≃ X) (C : Generic.LanguageFamily X) (inf : ∀ i, (C i).Infinite)
    (p : PMF X) {f : ℕ} [NeZero f] (n W : ℕ) (hw : 0 < W)
    (witness : WitnessBy u C p W) (t : Fin f) (safe : C t.val ⊆ p.support)
    (g : ℝ) (hg : 0 < g) (cap : g ≤ n*massFloor u (C t.val) p W/2) :
    (∀ ε : ℝ, 0 < ε → PrivateAt ε 0 n (pureGenerator u C n (unknownScores u C f g) ε) ∧
      genErr (pureGenerator u C n (unknownScores u C f g) ε) p n ≤
        W*Real.exp (-(n:ℝ)*massFloor u (C t.val) p W/8) +
        f*Real.exp (-ε*g/(2*W*(W+1))) + n/(2:ℝ)^n) ∧
    (∀ ε δ : ℝ, ε ∈ Set.Ioo 0 1 → δ ∈ Set.Ioo 0 1 →
      PrivateAt ε δ n (gaussianGenerator u C n (unknownScores u C f g) ε δ) ∧
      genErr (gaussianGenerator u C n (unknownScores u C f g) ε δ) p n ≤
        W*Real.exp (-(n:ℝ)*massFloor u (C t.val) p W/8) +
        2*f*Real.exp (-ε^2*g^2/(16*W^2*(W+1)^2*f*Real.log ((5/4)/δ))) + n/(2:ℝ)^n) :=
  Generation.unknown_generation u C inf p n W hw witness t safe g hg cap

/-- Theorem 4.7. Without a public witness bound, every positive exponential
rate fails on every distribution with the given support. The second part
allows approximate privacy with exponentially small slack at each sample size. -/
theorem theorem_4_7 [Countable X] (u : ℕ ≃ X) (C : Generic.LanguageFamily X)
    (finite : (Set.range C).Finite) (i j : ℕ) (hi : (C i).Infinite) (hj : (C j).Infinite)
    (inter : (C i ∩ C j).Finite) (A : StatisticalGenerator X) (ok : ConsistentGenerator u C A)
    (ε : ℝ) (hε : 0 < ε) (p : PMF X) (support : p.support = C i) :
    (IsPrivate (ENNReal.ofReal ε) A → ∀ c : ℝ, 0 < c →
      ∀ᶠ n : ℕ in atTop, (1/2 : ℝ)*Real.exp (-c*n) ≤ genErr A p n) ∧
    (∀ δ : ℕ → ℝ, (∀ n, 0 ≤ δ n) → (∀ n, PrivateAt ε (δ n) n A) →
      (∃ s : ℝ, 0 < s ∧ ∀ n : ℕ, δ n ≤ Real.exp (-s*n)) →
      ∀ c : ℝ, 0 < c → ∀ᶠ n : ℕ in atTop, (1/2 : ℝ)*Real.exp (-c*n) ≤ genErr A p n) := by
  constructor
  · intro dp
    apply unknown_witness_lower u C finite i j hi hj inter A ok hε zero_lt_one
      (fun _ => 0) (fun _ => le_rfl) _ _ p support
    · intro n
      simpa only [ENNReal.toReal_ofReal hε.le] using privateAt_of_pure ENNReal.ofReal_ne_top dp n
    · exact Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)
  · rintro δ nonneg dp ⟨s,hs,decay⟩
    exact unknown_witness_lower u C finite i j hi hj inter A ok hε hs δ nonneg dp
      (Filter.Eventually.of_forall decay) p support

/-- Theorem 5.2. The two distributions have attained optima and are fixed
before choosing the identifier, privacy budget or sample size. The factor
retention(ε) is exp(−ε) for finite ε and zero at the nonprivate endpoint. -/
theorem theorem_5_2 (C : Generic.LanguageFamily X) (ipp : IntersectingPrivatePair C) :
    ∃ p₀ p₁ : PMF X, (∃ i, Optimal C p₀ i) ∧ (∃ j, Optimal C p₁ j) ∧
      ∀ (ε : ℝ≥0∞), 0 < ε → ∀ A : Identifier X, IsPrivate ε (languageOutput C A) →
      ∀ n : ℕ, 1 ≤ n →
        (1 - (1 - retention ε)/4)^n / 8 ≤ max (idErr C A p₀ n) (idErr C A p₁ n) ∧
        Real.exp (-((min 1 ε).toReal) * n / 3) / 8 ≤ (1 - (1 - retention ε)/4)^n / 8 := by
  obtain ⟨p₀,p₁,o₀,o₁,lower⟩ := identification_lower C ipp
  exact ⟨p₀,p₁,o₀,o₁,fun ε _ A dp n _ =>
    ⟨lower ε A dp n,div_le_div_of_nonneg_right (commonRate_ge_exponential ε n) (by norm_num)⟩⟩

/-- Theorem 5.4. Infinite differences in both directions supply two
infinite-support laws. Generation error counts previously observed outputs
as well as outputs outside the support. -/
theorem theorem_5_4 [Countable X] (C : Generic.LanguageFamily X)
    (pair : IntersectingInfiniteDifferencePair C) :
    ∃ p₀ p₁ : PMF X, p₀.support.Infinite ∧ p₁.support.Infinite ∧
      ∀ (ε : ℝ≥0∞), 0 < ε → ∀ A : StatisticalGenerator X, IsPrivate ε A →
      ∀ n : ℕ, 1 ≤ n →
        (1 - (1 - retention ε)/4)^n / 3 ≤ max (genErr A p₀ n) (genErr A p₁ n) ∧
        Real.exp (-((min 1 ε).toReal) * n / 3) / 3 ≤ (1 - (1 - retention ε)/4)^n / 3 := by
  obtain ⟨p₀,p₁,s₀,s₁,lower⟩ := generation_lower C pair
  exact ⟨p₀,p₁,s₀,s₁,fun ε _ A dp n hn =>
    ⟨lower ε A dp n hn,div_le_div_of_nonneg_right (commonRate_ge_exponential ε n) (by norm_num)⟩⟩

end GenLimit.PriceOfPrivacy.Results
