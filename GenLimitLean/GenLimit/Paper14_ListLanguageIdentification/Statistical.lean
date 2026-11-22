import GenLimit.Paper14_ListLanguageIdentification.Stratification
import GenLimit.Support.DiscreteLawContinuity

/-! # Statistical list identification

A kernel outputs an ordered list of width k, and succeeds whenever one of
the named languages equals the target. Repeated names are permitted.
Sampling laws have exactly the target language as their support. -/
namespace GenLimit.ListIdentification.Statistical
open DiscreteIID Filter
open scoped Topology

abbrev Kernel (α : Type*) (k : ℕ) := List α → PMF (Fin k → ℕ)

def misses (F : Generic.LanguageFamily α) (K : Generic.Language α) {k : ℕ} :
    Set (Fin k → ℕ) := {v | ∀ r, F (v r) ≠ K}

noncomputable def error (F : Generic.LanguageFamily α) (A : Kernel α k)
    (p : PMF α) (K : Generic.Language α) (n : ℕ) : ℝ :=
  probability ((samples p n).bind A) (misses F K)

def Exponential (F : Generic.LanguageFamily α) (A : Kernel α k) : Prop :=
  ∀ i (p : PMF α), p.support = F i → ∃ c > (0 : ℝ), ∃ D > (0 : ℝ),
    ∀ n : ℕ, error F A p (F i) n ≤ D * Real.exp (-c * n)

/-- A finite set of positive examples forces the relative layer identifier
to name the target on every target-contained history displaying that set. -/
theorem layer_witness (F : Generic.LanguageFamily α) {I : Set ℕ}
    (hI : RelativeConditionTwo F I) {i : ℕ} (hi : i ∈ I) :
    ∃ W : Finset α, (↑W : Set α) ⊆ F i ∧ ∀ xs : List α,
      (∀ x ∈ xs, x ∈ F i) → (∀ x ∈ W, x ∈ xs) →
      F (relativeIdentifier F I xs) = F i := by
  classical
  let T := relativeTellTale F I
  let bad := (Finset.range (i+1)).filter (fun j ↦ ¬ F i ⊆ F j)
  have hex (j : {j // j ∈ bad}) : ∃ x, x ∈ F i ∧ x ∉ F j.1 :=
    Set.not_subset.mp (Finset.mem_filter.mp j.2).2
  let w := fun j ↦ (hex j).choose
  let W := T i ∪ bad.attach.image w
  refine ⟨W,?_,?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (relativeTellTale_spec hI hi).1 hx
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
      exact (hex j).choose_spec.1
  · intro xs hin hseen
    let S := Angluin.historySample xs
    have memS (x) : x ∈ S ↔ x ∈ xs := by simp [S, Angluin.historySample]
    have elig : LevelEligible F T I S i :=
      ⟨hi,fun x hx ↦ hin x ((memS _).1 hx),fun x hx ↦
        (memS _).2 (hseen x (Finset.mem_union_left _ hx))⟩
    let j := levelChoice F T I S
    have hj := levelChoice_eligible (h := ⟨i,elig⟩)
    have hji : j ≤ i := levelChoice_le_of_eligible elig
    have sub : F i ⊆ F j := by
      by_contra hn
      have hbad : j ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hn⟩
      let a : {j // j ∈ bad} := ⟨j,hbad⟩
      have hw : w a ∈ W := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,by simp,rfl⟩)
      exact (hex a).choose_spec.2 (hj.2.1 ((memS _).2 (hseen _ hw)))
    exact (relativeTellTale_spec hI hj.1).2 i hi
      (fun x hx ↦ elig.2.1 (hj.2.2 hx)) sub |>.antisymm sub

/-- Theorem 12. Combining the deterministic identifiers of the layers yields
an exponential upper bound, with constants depending on the sampling law. -/
theorem theorem_12 {F : Generic.LanguageFamily α} {k : ℕ}
    (h : KAngluinCondition F k) : ∃ A : Kernel α k, Exponential F A := by
  classical
  obtain ⟨L,hl,cover,conditions⟩ := kAngluin_implies_stratification h
  subst k
  let g (xs : List α) (r : Fin L.length) := relativeIdentifier F (L.get r) xs
  refine ⟨fun xs ↦ PMF.pure (g xs),?_⟩
  intro i p hp
  obtain ⟨I,hI,hi⟩ := cover i
  obtain ⟨r,hr⟩ := List.mem_iff_get.mp hI
  obtain ⟨W,hW,hw⟩ := layer_witness F (conditions _ hI) hi
  obtain ⟨c,hc,hmiss⟩ := finite_missing_exponential p W (fun x hx ↦ (show x ∈ p.support by rw [hp]; exact hW hx))
  refine ⟨c,hc,(W.card : ℝ)+1,by positivity,fun n ↦ ?_⟩
  have he : error F (fun xs ↦ PMF.pure (g xs)) p (F i) n =
      probability (samples p n) {xs | g xs ∈ misses F (F i)} := by
    unfold error probability
    change (((samples p n).map g).toOuterMeasure _).toReal = _
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  rw [he,← probability_inter_support]
  apply le_trans (probability_mono (samples p n) (F := {xs | ¬∀ x ∈ W, x ∈ xs}) ?_)
  · exact (hmiss n).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _))
  · intro xs ⟨hbad,hxs⟩ hseen
    have hin := (samples_support p n xs).mp hxs
    have correct := hw xs (fun x hx ↦ hp ▸ hin.2 x hx) hseen
    apply hbad r
    change F (relativeIdentifier F (L.get r) xs) = F i
    rwa [hr]

/-- A k-slot output must miss at least one of any k+1 distinct languages. -/
theorem miss_sum (F : Generic.LanguageFamily α) (p : PMF (Fin k → ℕ))
    (S : Finset (Generic.Language α)) (h : k < S.card) :
    1 ≤ ∑ K ∈ S, probability p (misses F K) := by
  classical
  have hu : (⋃ K ∈ S, misses (k := k) F K) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    have ex : ∃ K ∈ S, K ∉ Finset.univ.image (F ∘ v) := by
      by_contra! hn
      have hh := Finset.card_le_card hn
      exact h.not_ge (hh.trans ((Finset.card_image_le).trans_eq (by simp)))
    obtain ⟨K,hK,hm⟩ := ex
    exact Set.mem_iUnion.mpr ⟨K,Set.mem_iUnion.mpr ⟨hK,fun j hj ↦
      hm (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩)⟩⟩
  simpa only [hu,probability_univ] using probability_biUnion_le p S (fun K ↦ misses F K)

end GenLimit.ListIdentification.Statistical
