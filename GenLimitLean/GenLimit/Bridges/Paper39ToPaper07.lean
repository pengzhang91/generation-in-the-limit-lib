import GenLimit.Paper39_DenseGeneration.Patient.FocusCongruence
import GenLimit.Paper39_DenseGeneration.Patient.Main
import GenLimit.Paper07_DensityMeasuresForLanguageGeneration.OrderedCodingDensity
import GenLimit.Support.KleinbergWei.OrderedPositions

/-! # Patient-scope generation for compatible orders on overlaps

The live algorithm ranks a fresh word using only the current focus language.
The natural-number coding used to analyze a run can depend on its target and
its finitely many early outputs. This gives a comparison even when a global
linear extension of the language orders has not been supplied.
-/
namespace GenLimit.KleinbergWei.DensityMeasures.OrderedFocus
open PatientMachine FiniteRankFallback

/-- The two ranks of a pair agree in every language containing both words. -/
def Compatible (O : ℕ → OrderedLanguage) : Prop :=
  ∀ i j a b c d, (O i).enumeration a = (O j).enumeration c →
    (O i).enumeration b = (O j).enumeration d → a < b → c < d

private noncomputable def family (C : LanguageFamily) (hi : ∀ i, (C i).Infinite) : OracleFamily := by
  classical
  exact ⟨C,hi, fun i x ↦ if x ∈ C i then true else false, fun _ _ ↦ by simp⟩

private theorem infiniteCarrier (O : OrderedLanguage) : O.carrier.Infinite :=
  O.range_enumeration ▸ Set.infinite_range_of_injective O.enumeration_injective

noncomputable abbrev machine (O : ℕ → OrderedLanguage) :=
  family (fun i ↦ (O i).carrier) (fun i ↦ infiniteCarrier (O i))

noncomputable abbrev focus (O : ℕ → OrderedLanguage) (s : ℕ → ℕ) (t : ℕ) :=
  (run (machine O) s (t+1)).focus

private theorem exists_rank (L : OrderedLanguage) (S : Finset ℕ) : ∃ i, L.enumeration i ∉ S := by
  obtain ⟨x,hx,hf⟩ := (infiniteCarrier L).exists_notMem_finset S
  obtain ⟨i,rfl⟩ := L.range_enumeration.symm ▸ hx
  exact ⟨i,hf⟩

private noncomputable def choice (L : OrderedLanguage) (S : Finset ℕ) :=
  L.enumeration (Nat.find (exists_rank L S))

private noncomputable def used (O : ℕ → OrderedLanguage) (s : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | t+1 => let U := used O s t
           insert (choice (O (focus O s t)) (sample s (t+1) ∪ U)) U

noncomputable def generate (O : ℕ → OrderedLanguage) (s : ℕ → ℕ) (t : ℕ) :=
  choice (O (focus O s t)) (sample s (t+1) ∪ used O s t)

private theorem mem_used {O s t x} : x ∈ used O s t ↔ ∃ i < t, generate O s i = x := by
  induction t with
  | zero => simp [used]
  | succ t ih =>
    change x ∈ insert (generate O s t) (used O s t) ↔ _
    rw [Finset.mem_insert,ih]
    constructor
    · rintro (rfl | ⟨i,hi,hx⟩)
      · exact ⟨t,by omega,rfl⟩
      · exact ⟨i,by omega,hx⟩
    · rintro ⟨i,hi,hx⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
      · exact Or.inr ⟨i,hi,hx⟩
      · exact Or.inl hx.symm

private theorem fresh (O : ℕ → OrderedLanguage) (s : ℕ → ℕ) (t : ℕ) :
    generate O s t ∉ sample s (t+1) ∪ used O s t := Nat.find_spec (exists_rank ..)

private theorem injective (O : ℕ → OrderedLanguage) (s : ℕ → ℕ) : Function.Injective (generate O s) := by
  have h {i j : ℕ} (hi : i < j) : generate O s i ≠ generate O s j := fun he ↦
    fresh O s j (Finset.mem_union_right _ (mem_used.mpr ⟨i,hi,he⟩))
  intro i j he
  exact le_antisymm (le_of_not_gt (fun hj ↦ h hj he.symm)) (le_of_not_gt (fun hi ↦ h hi he))

private theorem focus_prefix {O : ℕ → OrderedLanguage} {s d : ℕ → ℕ} {t : ℕ}
    (he : ∀ k ≤ t, s k = d k) : focus O s t = focus O d t := by
  apply (run_control_congr _ ?_ (fun _ _ ↦ Iff.rfl)).focus
  intro u hu
  funext i
  unfold Consistent
  rw [sample_eq_of_eq_on_prefix (stream₂ := d) (fun k hk ↦ he k (by omega))]

/-- The rule uses exactly the observations through the current round. -/
theorem generate_prefix (O : ℕ → OrderedLanguage) (s d : ℕ → ℕ) (t : ℕ)
    (he : ∀ k ≤ t, s k = d k) : generate O s t = generate O d t := by
  have hu (n : ℕ) (hn : n ≤ t+1) : used O s n = used O d n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hpre (k) (hk : k ≤ n) := he k (by omega)
      simp only [used,ih (by omega),focus_prefix hpre,
        sample_eq_of_eq_on_prefix (stream₂ := d) (fun k (hk : k < n+1) ↦ hpre k (by omega))]
  unfold generate
  rw [focus_prefix he,hu t (by omega),
    sample_eq_of_eq_on_prefix (stream₂ := d) (fun k (hk : k < t+1) ↦ he k (by omega))]

/-- Code the early outputs in their emission order. Subsequent codes follow
target order on the target and use a disjoint odd branch off the target. -/
private noncomputable def wordCode (L : OrderedLanguage) (g : ℕ → ℕ) (T x : ℕ) : ℕ := by
  classical
  exact if early : ∃ i < T, g i = x then early.choose
    else if hx : x ∈ L.carrier then T + 2 * orderedPosition L x hx else T + 2*x + 1

private theorem code_early {L g T} (hg : Function.Injective g) {i} (hi : i < T) :
    wordCode L g T (g i) = i := by
  have h : ∃ j < T, g j = g i := ⟨i,hi,rfl⟩
  simpa only [wordCode,dif_pos h] using hg h.choose_spec.2

private theorem code_before {L g T x} (h : wordCode L g T x < T) :
    ∃ i < T, g i = x ∧ wordCode L g T x = i := by
  classical
  by_cases he : ∃ i < T, g i = x
  · exact ⟨he.choose,he.choose_spec.1,he.choose_spec.2,by simp [wordCode,he]⟩
  · simp only [wordCode,dif_neg he] at h
    split at h <;> omega

private theorem code_late {L g T x} (hx : x ∈ L.carrier) (he : ¬ ∃ i < T, g i = x) :
    wordCode L g T x = T + 2 * orderedPosition L x hx := by simp [wordCode,he,hx]

private theorem code_inj (L : OrderedLanguage) (g : ℕ → ℕ) (T : ℕ) :
    Function.Injective (wordCode L g T) := by
  classical
  intro x y h
  by_cases he : wordCode L g T x < T
  · obtain ⟨i,_,hx,hi⟩ := code_before he
    obtain ⟨j,_,hy,hj⟩ := code_before (h ▸ he)
    have : i = j := hi.symm.trans (h.trans hj)
    exact hx.symm.trans (this ▸ hy)
  · have hne {w : ℕ} (ha : ¬ wordCode L g T w < T) : ¬ ∃ i < T, g i = w := by
      intro h
      exact ha (by simpa only [wordCode,dif_pos h] using h.choose_spec.1)
    simp only [wordCode,dif_neg (hne he),dif_neg (hne (h ▸ he))] at h
    split at h <;> split at h
    · rename_i hx hy
      have heq : orderedPosition L x hx = orderedPosition L y hy := by omega
      exact (enumeration_orderedPosition L x hx).symm.trans
        ((congrArg L.enumeration heq).trans (enumeration_orderedPosition L y hy))
    all_goals omega

private theorem code_target_order (L : OrderedLanguage) (g : ℕ → ℕ) (T : ℕ) :
    ∃ N, ∀ j ≥ N, ∀ i < j, wordCode L g T (L.enumeration i) < wordCode L g T (L.enumeration j) := by
  classical
  let E := (Finset.range T).image g
  obtain ⟨b,hb⟩ := (E.finite_toSet.preimage L.enumeration_injective.injOn).bddAbove
  refine ⟨b+1,?_⟩
  intro j hj i hij
  have hlate : ¬ ∃ k < T, g k = L.enumeration j := by
    rintro ⟨k,hk,he⟩
    have := hb (show L.enumeration j ∈ E from Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr hk,he⟩)
    omega
  have hmem (i) : L.enumeration i ∈ L.carrier := L.range_enumeration ▸ Set.mem_range_self i
  have pos (i) : orderedPosition L (L.enumeration i) (hmem i) = i :=
    L.enumeration_injective (enumeration_orderedPosition L _ _)
  rw [code_late (hmem j) hlate,pos]
  by_cases he : ∃ k < T, g k = L.enumeration i
  · simp only [wordCode,dif_pos he]
    have := he.choose_spec.1
    omega
  · rw [code_late (hmem i) he,pos]
    omega


/-- Eventual target membership and freshness against both players' histories. -/
def ElementValid (s g : ℕ → ℕ) (K : Language) : Prop :=
  ∃ T, ∀ t ≥ T, g t ∈ K ∧ (∀ i ≤ t, s i ≠ g t) ∧ (∀ i < t, g i ≠ g t)

/-- When the focus eventually lies in the target, a run-dependent injection
transports the ordered outputs to an ordinary patient-scope run. On the
target, this coding preserves every sufficiently late initial segment. -/
theorem exists_coded_run (O : ℕ → OrderedLanguage) (K : OrderedLanguage)
    (compat : ∀ i a b c d, (O i).enumeration a = K.enumeration c →
      (O i).enumeration b = K.enumeration d → a < b → c < d)
    (s : ℕ → ℕ) (T : ℕ)
    (hT : ∀ t ≥ T, (O (focus O s t)).carrier ⊆ K.carrier) :
    ElementValid s (generate O s) K.carrier ∧
    ∃ (code : ℕ → ℕ) (P : OracleFamily), Function.Injective code ∧
      (∀ i, P.language i = code '' (O i).carrier) ∧
      (∀ t, output P (code ∘ s) t = code (generate O s t)) ∧
      ∃ N, ∀ j ≥ N, ∀ i < j, code (K.enumeration i) < code (K.enumeration j) := by
  classical
  let g := generate O s
  have localMem (t : ℕ) : g t ∈ (O (focus O s t)).carrier :=
    (O (focus O s t)).range_enumeration ▸ Set.mem_range_self _
  refine ⟨⟨T,fun t ht ↦ ⟨hT t ht (localMem t),fun i hi he ↦
    fresh O s t (Finset.mem_union_left _ (mem_sample_iff.mpr ⟨i,by omega,he⟩)),
    fun i hi he ↦ fresh O s t (Finset.mem_union_right _ (mem_used.mpr ⟨i,hi,he⟩))⟩⟩,?_⟩
  let code := wordCode K g T
  have hinj : Function.Injective code := code_inj ..
  let F (i : ℕ) := Set.range (code ∘ (O i).enumeration)
  have hi (i : ℕ) : (F i).Infinite := Set.infinite_range_of_injective (hinj.comp (O i).enumeration_injective)
  let P := family F hi
  let d := code ∘ s
  have hF (i) : F i = code '' (O i).carrier := by rw [← (O i).range_enumeration,← Set.range_comp]
  have member (i x) : code x ∈ P.language i ↔ x ∈ (O i).carrier := by
    change code x ∈ F i ↔ _
    rw [hF]
    exact ⟨fun ⟨y,hy,he⟩ ↦ hinj he ▸ hy,fun h ↦ ⟨x,h,rfl⟩⟩
  have hfocus (t) : focus O s t = (run P d (t+1)).focus := by
    apply (run_control_congr _ ?_ ?_).focus
    · intro u _
      funext i
      apply propext
      constructor <;> intro hs x hx
      · obtain ⟨r,hr,rfl⟩ := mem_sample_iff.mp hx
        exact (member _ _).2 (hs (value_mem_sample hr))
      · obtain ⟨r,hr,rfl⟩ := mem_sample_iff.mp hx
        exact (member _ _).1 (hs (value_mem_sample (stream := d) hr))
    · intro i j
      change (O i).carrier ⊆ (O j).carrier ↔ F i ⊆ F j
      rw [hF,hF]
      exact (Set.image_subset_image_iff hinj).symm
  have sim (t : ℕ) : output P d t = code (g t) := by
    induction t using Nat.strong_induction_on with
    | h t ih =>
      let L := O (focus O s t)
      let S := sample s (t+1) ∪ used O s t
      let k := Nat.find (exists_rank L S)
      have hgk : L.enumeration k = g t := rfl
      have pre (i : ℕ) (h : i < t) := ih i h
      have hm := output_mem_round_focus P d t
      rw [← hfocus] at hm
      change output P d t ∈ F _ at hm
      obtain ⟨y,hy,he⟩ := hF _ ▸ hm
      have yf : y ∉ S := by
        intro h
        rcases Finset.mem_union.mp h with h | h
        · obtain ⟨i,hi,hx⟩ := mem_sample_iff.mp h
          exact stream_ne_output P d t i (by omega) ((congrArg code hx).trans he)
        · obtain ⟨i,hi,hx⟩ := mem_used.mp h
          exact output_ne_of_lt P d hi ((pre i hi).trans ((congrArg code hx).trans he))
      apply le_antisymm
      · apply output_minimal_post_focus
        refine ⟨?_,?_,?_⟩
        · rw [← hfocus]
          exact (member _ _).2 (localMem t)
        · intro h
          obtain ⟨i,hi,hx⟩ := mem_sample_iff.mp h
          exact fresh O s t (Finset.mem_union_left _ (mem_sample_iff.mpr ⟨i,hi,hinj hx⟩))
        · intro h
          obtain ⟨i,hi,hx⟩ := (mem_run_used_iff P d).mp h
          exact fresh O s t (Finset.mem_union_right _ (mem_used.mpr ⟨i,hi,hinj ((pre i hi).symm.trans hx)⟩))
      · rw [← he]
        by_cases ht : t < T
        · rw [show code (g t) = t from code_early (injective O s) ht]
          by_contra! h
          obtain ⟨i,_,hiy,hci⟩ := code_before (lt_trans h ht)
          exact yf (Finset.mem_union_right _ (mem_used.mpr ⟨i,hci ▸ h,hiy⟩))
        · have late {x} (h : x ∉ S) : ¬ ∃ i < T, g i = x := by
            rintro ⟨i,hi,hx⟩
            exact h (Finset.mem_union_right _ (mem_used.mpr ⟨i,by omega,hx⟩))
          have htarget := hT t (Nat.le_of_not_gt ht)
          have hgy := htarget (localMem t)
          have hyy := htarget hy
          rw [show code (g t) = _ from code_late hgy (late (fresh O s t)),
            show code y = _ from code_late hyy (late yf)]
          obtain ⟨j,hj⟩ := (show y ∈ Set.range L.enumeration by rw [L.range_enumeration]; exact hy)
          have hkj : k ≤ j := Nat.find_min' (exists_rank L S) (hj ▸ yf)
          rcases hkj.eq_or_lt with h | h
          · have heq := hgk.symm.trans ((congrArg L.enumeration h).trans hj)
            simp only [heq, le_refl]
          · have hpos := compat (focus O s t) k j _ _
                (hgk.trans (enumeration_orderedPosition K _ hgy).symm)
                (hj.trans (enumeration_orderedPosition K _ hyy).symm) h
            omega
  exact ⟨code,P,hinj,hF,sim,code_target_order ..⟩

/-- A single prefix-dependent generator attains lower density one half on every target. -/
theorem generation_and_lowerDensity (O : ℕ → OrderedLanguage) (compat : Compatible O)
    {z : ℕ} {s : ℕ → ℕ} (hp : Presents s (O z).carrier) :
    ElementValid s (generate O s) (O z).carrier ∧
    (1 / 2 : ℝ) ≤ (O z).lowerDensity (Set.range (generate O s)) := by
  obtain ⟨T,hT⟩ := run_focus_eventually_subset (machine O) (z := z) hp
  obtain ⟨hv,code,P,hinj,hF,sim,horder⟩ :=
    exists_coded_run O (O z) (fun i ↦ compat i z) s T hT
  refine ⟨hv,?_⟩
  let d := code ∘ s
  have hpres : Presents d (P.language z) := by rw [Presents,Set.range_comp,hF,hp]
  have hr : P.language z = Set.range (code ∘ (O z).enumeration) := by
    rw [hF,Set.range_comp,(O z).range_enumeration]
  obtain ⟨_,hd⟩ := patientScope_generation_and_lowerDensity P d (z := z) hpres
  have bound : (1 / 2 : ℝ) ≤ (OrderedLanguage.increasing (P.language z) (P.infinite' z)).lowerDensity
      (Set.range (output P d)) := hd.trans ((OrderedLanguage.increasing _ _).lowerDensity_mono
        (fun _ ⟨⟨t,ht,_⟩,_⟩ ↦ ⟨t,ht⟩))
  have transport (A : Language) : (OrderedLanguage.increasing (P.language z) (P.infinite' z)).lowerDensity A =
      (O z).lowerDensity (code ⁻¹' A) := by
    simp only [hr]
    exact CommonOrder.lowerDensity_code _ _ hinj horder A
  rw [transport] at bound
  apply bound.trans ((O z).lowerDensity_mono ?_)
  rintro x ⟨t,ht⟩
  exact ⟨t,hinj ((sim t).symm.trans ht)⟩

/-- Theorems 2.5 and 5.1. The same generator works for all c < 1. -/
theorem theorem_5_1 (O : ℕ → OrderedLanguage) (compat : Compatible O)
    {z : ℕ} {s : ℕ → ℕ} (hp : Presents s (O z).carrier) :
    ElementValid s (generate O s) (O z).carrier ∧ ∀ c : ℝ, c < 1 →
      c / 2 ≤ (O z).upperDensity (Set.range (generate O s)) := by
  obtain ⟨hv,hd⟩ := generation_and_lowerDensity O compat hp
  refine ⟨hv,fun c hc ↦ (show c / 2 ≤ 1 / 2 by linarith).trans (hd.trans ?_)⟩
  exact Filter.liminf_le_limsup (Filter.isBoundedUnder_of ⟨1, (O z).prefixRatio_le_one _⟩)
    (Filter.isBoundedUnder_of ⟨0, (O z).prefixRatio_nonneg _⟩)

/-- Theorem 6.2's numerical conclusion, for every finite rank bound. -/
theorem theorem_6_2 (O : ℕ → OrderedLanguage) (compat : Compatible O)
    (r : ℕ) {z : ℕ} {s : ℕ → ℕ} (hp : Presents s (O z).carrier) :
    ElementValid s (generate O s) (O z).carrier ∧
    1 / (3 * ((r : ℝ) + 1)) ≤ (O z).lowerDensity (Set.range (generate O s)) := by
  obtain ⟨hv,hd⟩ := generation_and_lowerDensity O compat hp
  exact ⟨hv,(one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    (by linarith [Nat.cast_nonneg (α := ℝ) r] : (2 : ℝ) ≤ 3 * ((r : ℝ) + 1))).trans hd⟩

/-- Theorems 2.6 and 6.12, with the published lower bound. -/
theorem theorem_6_12 (O : ℕ → OrderedLanguage) (compat : Compatible O)
    {z : ℕ} {s : ℕ → ℕ} (hp : Presents s (O z).carrier) :
    ElementValid s (generate O s) (O z).carrier ∧
    (1 / 8 : ℝ) ≤ (O z).lowerDensity (Set.range (generate O s)) := by
  obtain ⟨hv,hd⟩ := generation_and_lowerDensity O compat hp
  exact ⟨hv,(by norm_num : (1 / 8 : ℝ) ≤ 1 / 2).trans hd⟩

end GenLimit.KleinbergWei.DensityMeasures.OrderedFocus
