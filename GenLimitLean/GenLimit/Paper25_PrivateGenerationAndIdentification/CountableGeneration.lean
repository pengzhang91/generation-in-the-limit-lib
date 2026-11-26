import GenLimit.Paper25_PrivateGenerationAndIdentification.EpochGeneration

/-! A second construction for the existence assertion of Theorem 1.1.
Use increasingly long prefixes of the public family. Each finite prefix
has a finite bound on its finite intersection sizes, regardless of the
dimension of the full family. The public sample schedule uses those
bounds to make the error for each fixed target summable. -/
namespace GenLimit.PrivateLimit.Epoch

open Set Filter MeasureTheory Privacy
open scoped Classical
noncomputable section

def finiteDimension {k : ℕ} (A : Fin k → Set ℕ) :=
  Finset.univ.sup (fun S : Finset (Fin k) => (FiniteCore.core A S).ncard)

theorem finiteDimension_bound {k : ℕ} (A : Fin k → Set ℕ) :
    SubcollectionClosureBound (range A) (finiteDimension A) := by
  intro V sub _
  let S := Finset.univ.filter (fun i => A i ∈ V)
  have eq : ⋂₀ V = FiniteCore.core A S := by
    ext x; change (∀ L ∈ V, x ∈ L) ↔ ∀ i ∈ S, x ∈ A i
    constructor
    · exact fun h i hi => h _ (Finset.mem_filter.mp hi).2
    · intro h L hL
      obtain ⟨i,rfl⟩ := sub hL
      exact h i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hL⟩)
  rw [eq]
  exact Finset.le_sup (f := fun T => (FiniteCore.core A T).ncard) (Finset.mem_univ S)

private def front (C : LanguageFamily) (r : ℕ) (i : Fin (r+1)) := C i.val

def countableFinish (C : LanguageFamily) : ℕ → ℕ
  | 0 => 0
  | r+1 => finiteDimension (front C (r+1))+2*((r+1)+1)^2*((r+1)+2)*(r+1)

def countableScheme (C : LanguageFamily) : Scheme where
  count j := j+1
  family := front C
  dim j := finiteDimension (front C j)
  bound _ := finiteDimension_bound _
  finish := countableFinish C
  initial := rfl

private theorem countable_error (C : LanguageFamily) {ε : ℝ} (he : 0 < ε) {r : ℕ} (hr : 0 < r) :
    errorAt (countableScheme C) ε r ≤ 5*(Real.exp (-ε))^r := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  rw [← Real.exp_nat_mul]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  change -(cost ε (j+1))*(((countableFinish C (j+1)+1:ℕ):ℝ)-
    (finiteDimension (front C (j+1)):ℝ))/(2*((j+1+1:ℕ):ℝ)) ≤ _
  simp only [countableFinish,cost,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_succ]
  field_simp
  nlinarith only [he]

/-- The probability-one requirement of Definition 1, counting time t from
zero: the generator has seen precisely the positions 0 through t. -/
def GeneratesOnline (M : ContinualRelease ℕ ℕ) (C : LanguageFamily) : Prop :=
  ∀ i (s : ℕ → ℕ), Function.Injective s → range s = C i →
    ∀ᵐ y ∂M.law s, ∃ T, ∀ t ≥ T, y t ∈ C i ∧ ∀ j ≤ t, y t ≠ s j

theorem countable_correct (C : LanguageFamily) {ε : ℝ} (he : 0 < ε) :
    GeneratesOnline (generator (countableScheme C) ε) C := by
  intro i s nd eq
  let P := countableScheme C
  let μ := productLaw (sample P ε) s
  have geom := summable_geometric_of_lt_one (Real.exp_pos (-ε)).le
    (show Real.exp (-ε) < 1 from Real.exp_lt_one_iff.mpr (by linarith))
  have b : ∀ᶠ r : ℕ in atTop, μ.real (badEpoch P (C i) s r) ≤ 5*(Real.exp (-ε))^r := by
    filter_upwards [eventually_ge_atTop (i+1)] with r hr
    exact (badEpoch_bound P he s nd r (⟨i,by change i < r+1; omega⟩ : Fin (P.count r)) eq.subset).trans
      (countable_error C he (by omega))
  have a := Voting.eventually_avoid μ (badEpoch P (C i) s) (geom.mul_left 5) b
  have nonfailure : ∀ᵐ y ∂(generator P ε).law s, ∃ T, y ∉ failsAfter (C i) s T := by
    change ∀ᵐ y ∂μ.map (playback P.finish), _
    apply (ae_map_iff (measurable_playback _).aemeasurable ?_).mpr
    · filter_upwards [a] with y hy
      obtain ⟨r,hr⟩ := eventually_atTop.mp hy
      refine ⟨max r (P.finish r),fun h => ?_⟩
      obtain ⟨l,hl⟩ := mem_iUnion.mp (late_failure P (C i) s le_rfl h)
      exact hr (r+l) (by omega) hl
    · simp only [setOf_exists]; exact MeasurableSet.iUnion (fun T => (measurable_failsAfter ..).compl)
  filter_upwards [nonfailure] with y hy
  obtain ⟨T,hT⟩ := hy
  refine ⟨T,fun t ht => ?_⟩
  have h : y t ∉ badWord (C i) s (t+1) := by
    intro bad; apply hT
    refine mem_iUnion.mpr ⟨t-T,?_⟩
    simpa only [Nat.add_sub_of_le ht,mem_preimage,Function.eval] using bad
  refine ⟨Classical.not_not.mp (fun fail => h (Or.inl fail)),?_⟩
  intro j hj e
  exact h (Or.inr (mem_observations.mpr ⟨j,by omega,e.symm⟩))

end
end GenLimit.PrivateLimit.Epoch
