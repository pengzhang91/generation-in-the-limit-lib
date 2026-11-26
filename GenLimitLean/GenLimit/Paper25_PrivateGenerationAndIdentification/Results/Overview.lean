import GenLimit.Paper25_PrivateGenerationAndIdentification.StochasticIdentifier
import GenLimit.Paper25_PrivateGenerationAndIdentification.CountableGeneration
import GenLimit.Paper25_PrivateGenerationAndIdentification.FiniteGenerationRate
import GenLimit.Paper25_PrivateGenerationAndIdentification.PrivateGenerationLower
import GenLimit.Paper25_PrivateGenerationAndIdentification.OnlineIdentification

/-! Main results of Mehrotra, Velegkas, Yu and Zhou on private language
generation and identification in the limit (arXiv:2604.08504v1). -/

namespace GenLimit.PrivateLimit.Results

/-- Theorem 1.1. At every positive budget a single family-indexed
construction privately generates from each countable collection. A word
released at time t must belong to the target and avoid all inputs through t. -/
theorem theorem_1_1 (ε : ℝ) (he : 0 < ε) :
    ∃ G : LanguageFamily → Privacy.ContinualRelease ℕ ℕ, ∀ C,
      Privacy.DifferentiallyPrivate ε 0 (G C).law ∧ Epoch.GeneratesOnline (G C) C := by
  exact ⟨fun C => Epoch.generator (Epoch.countableScheme C) ε,
    fun C => ⟨Epoch.generator_private _ he,Epoch.countable_correct C he⟩⟩

/-- Theorem 1.2. The chance of any error after observing m examples
decays exponentially in ε(m−d)/(k log²(m−d)), uniformly in the target and
its injective enumeration. The integer dimension includes −1. -/
theorem theorem_1_2 {k : ℕ} (C : Fin k → Set ℕ) (d : ℤ) (hd : -1 ≤ d)
    (bound : ∀ V ⊆ Set.range C, (⋂₀ V).Finite → ((⋂₀ V).ncard : ℤ) ≤ d)
    (ε : ℝ) (he : 0 < ε) :
    ∃ M : Privacy.ContinualRelease ℕ ℕ, Privacy.DifferentiallyPrivate ε 0 M.law ∧
      ∀ (z : Fin k) (s : ℕ → ℕ), Function.Injective s → Set.range s ⊆ C z →
      ∀ m : ℕ, let u := ((m:ℤ)-d).toNat
        33 ≤ u → (M.law s).real (Epoch.failsAfter (C z) s (m-1)) ≤
          10*Real.exp (-ε*(u:ℝ)/(8*k*((Nat.log 2 u:ℝ)+2)^2)) := by
  exact Epoch.finite_generation_signed C d hd bound he

/-- Theorem 1.3 with the feasible size range k ≥ 2. The whole family
witnesses its exact dimension d. The positive constant in the private
bound is independent of k, d and ε. The same collection has a nonprivate
generator correct after d+1 observations. -/
theorem theorem_1_3_corrected (k d : ℕ) (hk : 2 ≤ k) :
    ∃ C : Set (Set ℕ), C.Finite ∧ C.ncard = k ∧ (∀ L ∈ C, L.Infinite) ∧
      SubcollectionClosureBound C d ∧ (⋂₀ C).Finite ∧ (⋂₀ C).ncard = d ∧
      (∀ (ε : ℝ), 0 < ε → ∀ M : Privacy.ContinualRelease ℕ ℕ,
        Privacy.DifferentiallyPrivate ε 0 M.law → ∀ m : ℕ, 0 < m →
        Packing.UniformFrom M C m → (d:ℝ)+(Packing.coefficient/3)*k/ε ≤ m) ∧
      (∃ G : Generic.Generator ℕ, ∀ K ∈ C, ∀ n, d < n → ∀ xs : Fin n → ℕ,
        Function.Injective xs → Set.range xs ⊆ K → G n xs ∈ K \ Set.range xs) := by
  obtain ⟨C,fin,size,inf,bd,inter,card,lo⟩ := Packing.corrected_lower k d hk
  exact ⟨C,fin,size,inf,bd,inter,card,lo,nonprivate_generation_after_closure_bound C bd⟩

/-- Theorem 1.5. Infinite overlap and a finite one-sided difference between
two distinct languages prevent pure-private identification in continual release.
The privacy guarantee covers the entire sequence of released indices. -/
theorem theorem_1_5 (C : LanguageFamily) (i j : ℕ)
    (distinct : C i ≠ C j) (overlap : (C i ∩ C j).Infinite)
    (difference : (C i \ C j).Finite) (ε : ℝ) (_positive : 0 < ε) :
    ¬∃ M : Privacy.ContinualRelease ℕ ℕ,
      Privacy.DifferentiallyPrivate ε 0 M.law ∧ IdentifiesOnline M C := by
  rintro ⟨M, privateLaw, identifies⟩
  exact identification_barrier distinct overlap difference M privateLaw identifies

/-- Theorem 1.6. At every positive privacy budget, a countable family
admits private stochastic identification exactly when it satisfies
Angluin's finite tell-tale condition. Privacy covers the joint trajectory.
Success stabilizes at one correct index, for every full-support IID law. -/
theorem theorem_1_6 (C : LanguageFamily) (ε : ℝ) (he : 0 < ε) :
    (∃ M : Privacy.ContinualRelease ℕ ℕ,
      Privacy.DifferentiallyPrivate ε 0 M.law ∧ IdentifiesStochastically M C) ↔
      Angluin.ConditionTwo C := by
  constructor
  · rintro ⟨M,_,ok⟩
    exact stochastic_condition_necessary C M ok
  · intro tell
    exact ⟨Voting.identifier C ε,Voting.identifier_private C he,Voting.identifier_correct C tell he⟩

/-- Appendix Theorem C.5. Algorithm 2 privately releases its complete
trajectory. On families with finite pairwise intersections it identifies
the target almost surely along each injective adversarial enumeration. -/
theorem theorem_C_5 (C : LanguageFamily) (ε : ℝ) (he : 0 < ε) :
    Privacy.DifferentiallyPrivate ε 0 (OnlineIdentification.identifier C ε).law ∧
      ((∀ i j, i ≠ j → (C i ∩ C j).Finite) →
        IdentifiesOnline (OnlineIdentification.identifier C ε) C) :=
  ⟨OnlineIdentification.identifier_private C he,OnlineIdentification.identifier_correct C he⟩

end GenLimit.PrivateLimit.Results
