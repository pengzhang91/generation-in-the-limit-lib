import GenLimit.Bridges.Paper39ToPaper07
import GenLimit.Paper39_DenseGeneration.Partial.Main

/-! # Ordered density under partial enumeration

Each infinite finite intersection inherits an ordering from one of its factors.
Patient scope runs on these intersections. The code used to compare this
ordered run with a natural-order run is chosen only in the proof. -/

namespace GenLimit.Bridge.Paper39ToPaper15
open KleinbergWei KleinbergWei.DensityMeasures KleinbergWei.DensityMeasures.OrderedFocus
open GenLimit.PartialEnumeration PatientMachine

private theorem oracle_ext {O P : OracleFamily} (h : ∀ i, O.language i = P.language i) : O = P := by
  cases O with
  | mk C hi q hq =>
    cases P with
    | mk D hj r hr =>
      change ∀ i, C i = D i at h
      obtain rfl := funext h
      have e : q = r := by
        funext i x
        exact Bool.eq_iff_iff.mpr ((hq i x).trans (hr i x).symm)
      cases e
      rfl

private theorem support_nonempty {q : ℕ} (h : q ≠ 0) : (codeSupport q).Nonempty := by
  by_contra! he
  apply h
  apply Finset.equivBitIndices.injective
  simpa [codeSupport] using he

/-- An infinite subset in the relative order of an ordered language. -/
private noncomputable def restrict (L : OrderedLanguage) (A : Language) (hi : A.Infinite)
    (hs : A ⊆ L.carrier) : OrderedLanguage :=
  let p := fun n ↦ L.enumeration n ∈ A
  have hp : (setOf p).Infinite := hi.preimage (L.range_enumeration.symm ▸ hs)
  { carrier := A
    enumeration := L.enumeration ∘ Nat.nth p
    enumeration_injective := L.enumeration_injective.comp (Nat.nth_strictMono hp).injective
    range_enumeration := by
      rw [Set.range_comp,Nat.range_nth_of_infinite hp]
      exact Set.image_preimage_eq_of_subset (L.range_enumeration.symm ▸ hs) }

private noncomputable def factor (O : OracleFamily) (i : ℕ) : ℕ :=
  (support_nonempty (closureCode_good O i).1).choose

private theorem subset_factor (O : OracleFamily) (i : ℕ) :
    (closure O).language i ⊆ O.language (factor O i) :=
  codedIntersection_subset_original (support_nonempty (closureCode_good O i).1).choose_spec

noncomputable def orderedClosure (O : ℕ → OrderedLanguage) (i : ℕ) : OrderedLanguage :=
  restrict (O (factor (machine O) i)) ((closure (machine O)).language i)
    ((closure (machine O)).infinite' i) (subset_factor (machine O) i)

private theorem compatible_target (O : ℕ → OrderedLanguage) (hc : Compatible O) (z i a b c d : ℕ)
    (ha : (orderedClosure O i).enumeration a = (O z).enumeration c)
    (hb : (orderedClosure O i).enumeration b = (O z).enumeration d) (hab : a < b) : c < d := by
  let j := factor (machine O) i
  let A := (closure (machine O)).language i
  have hinf : (((O j).enumeration) ⁻¹' A).Infinite :=
    ((closure (machine O)).infinite' i).preimage ((O j).range_enumeration.symm ▸ subset_factor _ i)
  exact hc j z _ _ c d ha hb (Nat.nth_strictMono hinf hab)

private noncomputable def imageFamily (O : OracleFamily) (f : ℕ → ℕ) (hf : Function.Injective f) :
    OracleFamily := by
  classical
  let D (i : ℕ) := f '' O.language i
  exact ⟨D,fun i ↦ (O.infinite' i).image hf.injOn,
    fun i x ↦ if x ∈ D i then true else false,fun _ _ ↦ by simp⟩

private theorem image_intersection (O : OracleFamily) (f : ℕ → ℕ) (hf : Function.Injective f)
    {q : ℕ} (hq : q ≠ 0) :
    codedIntersection (imageFamily O f hf).language q = f '' codedIntersection O.language q := by
  ext y
  constructor
  · intro hy
    obtain ⟨i,hi⟩ := support_nonempty hq
    obtain ⟨x,_,rfl⟩ := hy i hi
    refine ⟨x,fun j hj ↦ ?_,rfl⟩
    obtain ⟨w,hw,hx⟩ := hy j hj
    exact hf hx ▸ hw
  · rintro ⟨x,hx,rfl⟩
    exact fun i hi ↦ ⟨x,hx i hi,rfl⟩

private theorem closure_image (O : OracleFamily) (f : ℕ → ℕ) (hf : Function.Injective f) (i : ℕ) :
    (closure (imageFamily O f hf)).language i = f '' (closure O).language i := by
  have good : GoodCode (imageFamily O f hf) = GoodCode O := by
    funext q
    apply propext
    by_cases hq : q = 0
    · simp [GoodCode,hq]
    · simp only [GoodCode,image_intersection O f hf hq,Set.infinite_image_iff hf.injOn]
  simp only [closure_language,closureCode,good]
  exact image_intersection O f hf (closureCode_good O i).1

/-- One online rule for all infinite partial presentations of all targets. -/
noncomputable def generate (O : ℕ → OrderedLanguage) := OrderedFocus.generate (orderedClosure O)

theorem generate_prefix (O : ℕ → OrderedLanguage) (s d : ℕ → ℕ) (t : ℕ)
    (h : ∀ i ≤ t, s i = d i) : generate O s t = generate O d t :=
  OrderedFocus.generate_prefix _ _ _ _ h

/-- Theorem 1.6 / 3.5. The relative lower density of the *whole output set*
is at least one half of the relative lower density of the presented subset. -/
theorem theorem_1_6 (O : ℕ → OrderedLanguage) (hc : Compatible O)
    {z : ℕ} {E : Language} {s : ℕ → ℕ} (hp : Presents s E) (hi : E.Infinite)
    (hs : E ⊆ (O z).carrier) {α : ℝ} (ha : α ≤ (O z).lowerDensity E) :
    ElementValid s (generate O s) (O z).carrier ∧
      α / 2 ≤ (O z).lowerDensity (Set.range (generate O s)) := by
  classical
  let C := machine O
  let D := orderedClosure O
  have hD : machine D = closure C := oracle_ext (fun _ ↦ rfl)
  obtain ⟨S⟩ := stableTargetRun_nonempty C hp hi hs
  have eventual (t : ℕ) (ht : S.threshold ≤ t) :
      (D (focus D s t)).carrier ⊆ (O z).carrier := by
    change (closure C).language (run (machine D) s (t+1)).focus ⊆ C.language z
    rw [hD]
    have h := ht.trans (Nat.le_succ _)
    exact (focus_subset_target (run_focus_isFocus_of_onModel _ S.onModel _) (S.inScope _ h)
      (S.critical _ h)).trans S.witness_subset_target
  obtain ⟨hv,f,P,hf,hP,sim,order⟩ :=
    exists_coded_run D (O z) (compatible_target O hc z) s S.threshold eventual
  refine ⟨hv,?_⟩
  let B := imageFamily C f hf
  have heq : P = closure B := oracle_ext (fun i ↦ (hP i).trans (closure_image C f hf i).symm)
  have hr : B.language z = Set.range (f ∘ (O z).enumeration) := by
    rw [Set.range_comp,(O z).range_enumeration]; rfl
  have hp' : Presents (f ∘ s) (f '' E) := by rw [Presents,Set.range_comp,hp]
  have hd := theorem_B_3_lowerDensity B (z := z) hp' (hi.image hf.injOn) (Set.image_mono hs)
  have monotone : partialPatientLowerDensity B (f ∘ s) z ≤
      (OrderedLanguage.increasing (B.language z) (B.infinite' z)).lowerDensity
        (Set.range (output P (f ∘ s))) := by
    rw [heq]
    exact (OrderedLanguage.increasing _ _).lowerDensity_mono
      (fun _ ⟨⟨t,h,_⟩,_⟩ ↦ ⟨t,h⟩)
  have density (A : Language) : (OrderedLanguage.increasing (B.language z) (B.infinite' z)).lowerDensity A =
      (O z).lowerDensity (f ⁻¹' A) := by
    simp only [hr]
    exact CommonOrder.lowerDensity_code _ _ hf order A
  have h := hd.trans monotone
  unfold PatientScope.relativeLowerDensity at h
  rw [density,density,Set.preimage_image_eq _ hf] at h
  have sub : f ⁻¹' Set.range (output P (f ∘ s)) ⊆ Set.range (generate O s) := by
    rintro x ⟨t,ht⟩
    exact ⟨t,hf ((sim t).symm.trans ht)⟩
  linarith [(O z).lowerDensity_mono sub]

/-- Theorem 3.1's one-third guarantee follows for the same rule. -/
theorem theorem_3_1 (O : ℕ → OrderedLanguage) (hc : Compatible O)
    {z : ℕ} {E : Language} {s : ℕ → ℕ} (hp : Presents s E) (hi : E.Infinite)
    (hs : E ⊆ (O z).carrier) {α : ℝ} (hpos : 0 ≤ α) (ha : α ≤ (O z).lowerDensity E) :
    ElementValid s (generate O s) (O z).carrier ∧
      α / 3 ≤ (O z).lowerDensity (Set.range (generate O s)) := by
  obtain ⟨hv,hd⟩ := theorem_1_6 O hc hp hi hs ha
  exact ⟨hv,by linarith⟩

/-- Theorem 1.3 is the ordered full-enumeration guarantee. -/
theorem theorem_1_3 (O : ℕ → OrderedLanguage) (hc : Compatible O)
    {z : ℕ} {s : ℕ → ℕ} (hp : Presents s (O z).carrier) :
    ElementValid s (OrderedFocus.generate O s) (O z).carrier ∧
      (1 / 2 : ℝ) ≤ (O z).lowerDensity (Set.range (OrderedFocus.generate O s)) :=
  generation_and_lowerDensity O hc hp

end GenLimit.Bridge.Paper39ToPaper15
