import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.SublinearRates
import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.WeakLower
import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.SlowIdentification
import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.GenerationDiagonal
import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.InfiniteIndex
import GenLimit.Paper20_AgnosticLanguageIdentificationAndGeneration.GenerationLower

/-! # Agnostic Language Identification and Generation

The nine numbered theorems and Corollary 3.3 from Sections 2 and 3 of
Høgsgaard and Pabbaraju, arXiv:2601.23258v4. The five informal statements
in Section 1 summarize these results. -/
namespace GenLimit.AgnosticLanguage.Results
open Generic DiscreteIID Filter
open scoped Topology

/-- Algorithm 1 identifies an attained optimum with near-exponential probability. -/
theorem theorem_2_1 [Countable α] (C : Generic.LanguageFamily α) (f : ℕ → ℕ)
    (hf : Tendsto f atTop atTop) (p : PMF α) (hopt : ∃ i, Optimal C p i) :
    ∀ᶠ n : ℕ in atTop,
      probability (samples p n) {xs | ¬ Optimal C p (algorithmOne C f xs)} ≤
        2 * f n * Real.exp (-(n:ℝ) / (2 * (f n)^2)) ∧
      idErr C (deterministic (algorithmOne C f)) p n ≤
        2 * f n * Real.exp (-(n:ℝ) / (2 * (f n)^2)) :=
  weak_near_exponential C f hf p hopt

/-- Two languages with private strings force exponential excess risk infinitely often. -/
theorem theorem_2_2 (C : Generic.LanguageFamily α) (i j : ℕ) (hne : C i ≠ C j)
    (x y : α) (hx : ∀ k, x ∈ C k ↔ C k = C i) (hy : ∀ k, y ∈ C k ↔ C k = C j)
    (A : Identifier α) :
    ∃ p : PMF α, (∃ k, Optimal C p k) ∧
      ∃ᶠ n : ℕ in atTop, Real.exp (-5 * (n:ℝ)) ≤ idErr C A p n :=
  weak_exponential_lower C i j hne x y hx hy A

/-- A fixed countable family has arbitrarily slow rates when the infimum is unattained. -/
theorem theorem_2_3 :
    ∃ C : Generic.LanguageFamily Slow.Word, (∀ i, (C i).Infinite) ∧
      ∀ (A : Identifier Slow.Word) (R : ℕ → ℝ), Tendsto R atTop (𝓝 0) →
        ∃ p : PMF Slow.Word, (¬∃ i, Optimal C p i) ∧
          ∃ᶠ n : ℕ in atTop, R n / 8 ≤ idErr C A p n :=
  ⟨Slow.family,Slow.infinite_languages,Slow.arbitrary_slow_identification⟩

/-- Algorithm 2 identifies a minimal optimum when an optimum has a supported tell-tale. -/
theorem theorem_2_4 [Countable α] (C : Generic.LanguageFamily α) (f : ℕ → ℕ)
    (hf : Tendsto f atTop atTop) (p : PMF α) (htell : HasSupportedTellTale C p) :
    ∃ c > (0:ℝ), ∃ d > (0:ℝ), ∀ᶠ n : ℕ in atTop,
      idP C (deterministic (algorithmTwo C f)) p n ≤ c * f n * Real.exp (-d*n / (f n)^2) :=
  minimal_near_exponential C f hf p htell

/-- Tell-tales in every language can coexist with persistent failure when
no optimum has a tell-tale contained in the sampling support. -/
theorem theorem_2_5 :
    ∃ C : Generic.LanguageFamily (Bool × ℕ),
      (∀ i, (C i).Infinite ∧ ∃ T, IsFiniteTellTale (Set.range C) (C i) T) ∧
      ∀ A : GenLimit.Learner (Bool × ℕ) ℕ, ∃ p : PMF (Bool × ℕ),
        (∃ i, Optimal C p i) ∧ ¬ HasSupportedTellTale C p ∧
        liminf (fun n ↦ probability (samples p n) {xs | MinimalOptimal C p (A xs)}) atTop ≤ 1/2 := by
  obtain ⟨C,p,hC,_,ho,ht,he⟩ := minimal_identification_obstruction
  refine ⟨C,hC,fun A ↦ ⟨p,ho,ht,?_⟩⟩
  have hz (n) : probability (samples p n) {xs | MinimalOptimal C p (A xs)} = 0 := by
    have h := he (deterministic A) n
    have hd := probability_deterministic (samples p n) A {i | ¬ MinimalOptimal C p i}
    change probability _ _ = 1 at h
    have hc : probability (samples p n) {xs | MinimalOptimal C p (A xs)}ᶜ = 1 := hd.symm.trans h
    rw [probability_compl] at hc
    linarith
  simp_rw [hz]
  norm_num [liminf_const]

/-- Any randomized generator fails with probability at least 1−ε
infinitely often for one infinite-support distribution. -/
theorem theorem_3_1 (ε : ℝ) (hε : 0 < ε) (G : StatisticalGenerator ℕ) :
    ∃ p : PMF ℕ, p.support.Infinite ∧ ∃ᶠ n : ℕ in atTop, 1-ε ≤ genErr G p n :=
  agnostic_generation_obstruction G hε

/-- Algorithm 3 has an exponential error bound under a finite witness
index when the sampling support contains a candidate language. -/
theorem theorem_3_2 (u : ℕ ≃ α) (C : Generic.LanguageFamily α) (hC : ∀ i, (C i).Infinite)
    (p : PMF α) (hidx : FiniteWitnessIndex u C p) (hsub : ∃ i, C i ⊆ p.support) :
    ∃ c > (0:ℝ), ∃ d > (0:ℝ), ∀ n : ℕ,
      genErr (deterministic (algorithmThree u C hC)) p n ≤ c * Real.exp (-d*n) :=
  generation_exponential u C hC p hidx hsub

/-- Every finite collection of infinite languages satisfies the witness-index condition. -/
theorem corollary_3_3 (u : ℕ ≃ α) (C : Generic.LanguageFamily α) (hC : ∀ i, (C i).Infinite)
    (hfin : (Set.range C).Finite) (p : PMF α) (hsub : ∃ i, C i ⊆ p.support) :
    ∃ c > (0:ℝ), ∃ d > (0:ℝ), ∀ n : ℕ,
      genErr (deterministic (algorithmThree u C hC)) p n ≤ c * Real.exp (-d*n) :=
  generation_exponential u C hC p (finite_witness_index_of_finite u C hC hfin p) hsub

/-- With infinite witness index even a supported language can coexist with
a limsup generation error of at least one half. -/
theorem theorem_3_4 :
    ∃ C : Generic.LanguageFamily ℕ, (∀ i, (C i).Infinite) ∧
      ∀ A : GenLimit.Learner ℕ ℕ, ∃ p : PMF ℕ, (∃ i, C i ⊆ p.support) ∧
        ¬ FiniteWitnessIndex (Equiv.refl ℕ) C p ∧ 1/2 ≤ limsup (genErr (deterministic A) p) atTop :=
  ⟨RowFamily.family,RowFamily.infinite_languages,fun A ↦ infinite_index_obstruction (deterministic A)⟩

/-- Finite intersection and a string outside the union give a matching
exponential lower bound, including against randomized generators. -/
theorem theorem_3_5 [Countable α] (C : Generic.LanguageFamily α) (i j : ℕ)
    (hfin : (C i ∩ C j).Finite) (x : α) (hout : x ∉ C i ∪ C j) (G : StatisticalGenerator α) :
    ∃ p : PMF α, (∃ k, C k ⊆ p.support) ∧ ∃ᶠ n : ℕ in atTop,
      Real.exp (-2*(n:ℝ))/4 ≤ genErr G p n :=
  generation_exponential_lower C i j hfin x hout G

end GenLimit.AgnosticLanguage.Results
