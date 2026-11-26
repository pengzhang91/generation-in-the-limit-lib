import GenLimit.Core.CanonicalDensity
import GenLimit.Paper31_BoundedMemory.WindowHardInstance
import GenLimit.Paper31_BoundedMemory.AdaptiveBuffer

/-! # Density in the common ambient order (P31, Definition 8)

Words are represented by their ranks in the fixed ambient enumeration. The
target inherits the increasing order on these ranks. To transfer a hard
instance, rename the entire family, the input stream, and the generator by
the same permutation before measuring the output in the canonical order.
-/

namespace GenLimit.BoundedMemory

open GenLimit.KleinbergWei Filter Set Function

private noncomputable def enumerationEquiv (K : OrderedLanguage) : ℕ ≃ K.carrier :=
  Equiv.ofBijective (fun n => ⟨K.enumeration n, K.range_enumeration ▸ ⟨n, rfl⟩⟩)
    ⟨fun _ _ h => K.enumeration_injective (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨n, hn⟩ := K.range_enumeration.symm ▸ hx
      exact ⟨n, Subtype.ext hn⟩⟩

/-- Renumber the words of a hard target by their canonical ranks, leaving
every other word fixed. Thus all languages and all observations can be
renamed together, before a generator for the renamed family is selected. -/
private theorem alignTargetOrder (K : OrderedLanguage) (S : Set ℕ)
    (hS : S.Infinite) (hc : K.carrier = S) :
    ∃ e : Equiv.Perm ℕ, e '' S = S ∧
      ∀ n, e (K.enumeration n) = (OrderedLanguage.canonical S hS).enumeration n := by
  classical
  subst S
  let O := OrderedLanguage.canonical K.carrier hS
  let p : Equiv.Perm K.carrier := (enumerationEquiv K).symm.trans (enumerationEquiv O)
  let e := p.subtypeCongr (Equiv.refl {x : ℕ // x ∉ K.carrier})
  have he (n : ℕ) : e (K.enumeration n) = O.enumeration n := by
    change e ((enumerationEquiv K n).val) = _
    rw [show e ((enumerationEquiv K n).val) = (p (enumerationEquiv K n)).val from
      Equiv.Perm.subtypeCongr.left_apply_subtype _ _ _]
    simp [p, Equiv.trans_apply]
    rfl
  refine ⟨e, ?_, he⟩
  calc
    e '' K.carrier = Set.range (e ∘ K.enumeration) := by rw [Set.range_comp, K.range_enumeration]
    _ = Set.range O.enumeration := congrArg Set.range (funext he)
    _ = K.carrier := O.range_enumeration

private theorem alignedRatio (K O : OrderedLanguage) (e : Equiv.Perm ℕ)
    (h : ∀ n, e (K.enumeration n) = O.enumeration n) (A : Set ℕ) :
    K.prefixRatio (e ⁻¹' A) = O.prefixRatio A := by
  classical
  funext n
  simp [OrderedLanguage.prefixRatio, OrderedLanguage.prefixCount, Set.mem_preimage, h]

private theorem renamedPresents (e : Equiv.Perm ℕ) {s : ℕ → ℕ} {L : Set ℕ}
    (hs : Generic.Presents s L) : Generic.Presents (e ∘ s) (e '' L) :=
  (Set.range_comp e s).trans (congrArg _ hs)

private theorem renamedRepeat (e : Equiv.Perm ℕ) {s : ℕ → ℕ} (hs : FinitelyRepeating s) :
    FinitelyRepeating (e ∘ s) := by
  intro x
  simpa [Function.comp_def, Equiv.apply_eq_iff_eq_symm_apply] using hs (e.symm x)

private theorem renamedFamily_injective {ι : Type*} (e : Equiv.Perm ℕ)
    {langs : ι → Set ℕ} (h : Injective langs) : Injective (fun i => e '' langs i) :=
  (Set.image_injective.mpr e.injective).comp h

private theorem pullMemoryless (e : Equiv.Perm ℕ) {ι : Type*} {langs : ι → Set ℕ}
    {G : MemorylessSetGenerator ℕ}
    (hG : IsFinitelyRepeatingMemorylessGenerator G (Set.range (fun i => e '' langs i))) :
    IsFinitelyRepeatingMemorylessGenerator (fun x => e ⁻¹' G (e x)) (Set.range langs) := by
  rintro L ⟨i,rfl⟩ s hs hr
  obtain ⟨T,hT⟩ := hG _ ⟨i,rfl⟩ _ (renamedPresents e hs) (renamedRepeat e hr)
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨hi, hsub⟩ := hT t ht
  constructor
  · exact hi.preimage (fun y _ => e.surjective y)
  · intro y hy
    exact e.injective.mem_set_image.mp (hsub hy)

/-- The property in Definition 9 on ranks in the fixed ambient order. -/
def FixedMemorylessGuarantee (k : ℕ) (σ : ℝ) : Prop :=
  ∀ (langs : Fin k → Set ℕ), Injective langs → ∀ hi : ∀ i, (langs i).Infinite,
    ∃ G : MemorylessSetGenerator ℕ, (∀ x, (G x).Infinite) ∧
      IsFinitelyRepeatingMemorylessGenerator G (Set.range langs) ∧
      ∀ i s, Generic.Presents s (langs i) → FinitelyRepeating s →
        σ ≤ memorylessRunUpperDensity (OrderedLanguage.canonical (langs i) (hi i)) G s

private theorem fixedMemoryless_attains (k : ℕ) (hk : 1 ≤ k) :
    FixedMemorylessGuarantee k (memorylessSpernerValue k) := by
  cases k with
  | zero => omega
  | succ n =>
    intro langs _ hi
    refine ⟨canonicalDensityGenerator langs, ?_, canonicalDensityGenerator_succeeds langs, ?_⟩
    · exact canonicalDensityGenerator_infinite langs
    · intro i s hs _
      apply memorylessRunUpperDensity_ge_of_frequently
      simpa [memorylessSpernerValue] using canonicalDensityGenerator_frequently_sperner_dense
        langs i (OrderedLanguage.canonical (langs i) (hi i)) rfl s hs

private theorem fixedMemoryless_bound (k : ℕ) (hk : 2 ≤ k) {σ : ℝ}
    (hσ : FixedMemorylessGuarantee k σ) : σ ≤ memorylessSpernerValue k := by
  obtain ⟨K, langs, i, hinj, hi, htarget, hard⟩ := lemma_4_7_sperner_hard_instance k hk
  obtain ⟨e, himage, he⟩ := alignTargetOrder K (langs i) (hi i) htarget.symm
  let family := fun j => e '' langs j
  have inf (j) : (family j).Infinite := (hi j).image e.injective.injOn
  obtain ⟨G, _, hG, density⟩ := hσ family (renamedFamily_injective e hinj) inf
  let s := K.enumeration
  have hs : Generic.Presents s (langs i) := K.range_enumeration.trans htarget.symm
  have hp : Generic.Presents s K.carrier := K.range_enumeration
  obtain ⟨T,hT⟩ := hard _ (pullMemoryless e hG) s hp K.enumeration_injective
  let O := OrderedLanguage.canonical (family i) (inf i)
  have aligned (n) : e (K.enumeration n) = O.enumeration n := by
    simpa [O, family, himage] using he n
  apply (density i _ (renamedPresents e hs) (injective_finitelyRepeating
    (e.injective.comp K.enumeration_injective))).trans
  apply memorylessRunUpperDensity_le_of_eventually
  filter_upwards [eventually_ge_atTop T] with t ht
  simpa only [OrderedLanguage.upperDensity, alignedRatio K O e aligned,
    Function.comp_apply, memorylessSpernerValue] using hT t ht

/-- The fixed-order minimax value for memoryless generation (Theorem 4.1). -/
theorem fixedOrder_memoryless (k : ℕ) (hk : 1 ≤ k) :
    sSup {σ : ℝ | σ ∈ Icc 0 1 ∧ FixedMemorylessGuarantee k σ} =
      1 / (Nat.choose (k - 1) ((k - 1) / 2) : ℝ) := by
  change _ = memorylessSpernerValue k
  apply IsGreatest.csSup_eq
  refine ⟨⟨memorylessSpernerValue_mem_Icc k, fixedMemoryless_attains k hk⟩, ?_⟩
  intro σ hσ
  by_cases h : k = 1
  · subst k
    simpa [memorylessSpernerValue] using hσ.1.2
  · exact fixedMemoryless_bound k (by omega) hσ.2

/-- A finitely repeating presentation eventually avoids every finite prefix
of an injective enumeration. Thus eventual pointwise conclusions on one
complete enumeration transfer to every finitely repeating presentation. -/
private theorem eventually_on_presentation {S : Set ℕ} {a s : ℕ → ℕ} {P : ℕ → Prop}
    (ha : Generic.Presents a S) (hs : Generic.Presents s S) (hr : FinitelyRepeating s)
    (hp : ∃ T, ∀ t ≥ T, P (a t)) : ∃ T, ∀ t ≥ T, P (s t) := by
  obtain ⟨B,hB⟩ := hp
  obtain ⟨T,hT⟩ := finitelyRepeating_avoids_finite_set hr
    (Set.finite_range (fun i : Fin B => a i))
  refine ⟨T, fun t ht => ?_⟩
  have hx : s t ∈ Set.range a := ha.symm ▸ (hs ▸ Set.mem_range_self t)
  obtain ⟨n, hn⟩ := hx
  rw [← hn]
  apply hB
  by_contra! h
  exact hT t ht ⟨⟨n,h⟩,hn⟩

/-- Theorem 4.2. The same target defeats every successful generator on every
finitely repeating presentation in the order induced by the ambient ranks. -/
theorem fixedOrder_zero_lowerDensity (k : ℕ) (hk : 3 ≤ k) :
    ∃ (langs : Fin k → Set ℕ) (i : Fin k), Injective langs ∧
      ∃ hi : ∀ j, (langs j).Infinite, ∀ G : MemorylessSetGenerator ℕ,
        IsFinitelyRepeatingMemorylessGenerator G (Set.range langs) →
        ∀ s, Generic.Presents s (langs i) → FinitelyRepeating s →
          ∃ T, ∀ t ≥ T, (OrderedLanguage.canonical (langs i) (hi i)).lowerDensity
            (G (s t)) = 0 := by
  obtain ⟨K, langs, i, hinj, hi, hc, hard⟩ := theorem_4_2_no_uniform_positive_lower_density k hk
  obtain ⟨e, himage, he⟩ := alignTargetOrder K (langs i) (hi i) hc.symm
  let family := fun j => e '' langs j
  have inf (j) : (family j).Infinite := (hi j).image e.injective.injOn
  refine ⟨family, i, renamedFamily_injective e hinj, inf, ?_⟩
  intro G hG s hs hr
  let O := OrderedLanguage.canonical (family i) (inf i)
  have aligned (n) : e (K.enumeration n) = O.enumeration n := by
    simpa [O, family, himage] using he n
  have ha := renamedPresents e (K.range_enumeration.trans hc.symm)
  apply eventually_on_presentation (P := fun x => O.lowerDensity (G x) = 0) ha hs hr
  obtain ⟨T,hT⟩ := (hard _ (pullMemoryless e hG) _ K.range_enumeration K.enumeration_injective).1
  refine ⟨T,fun t ht => ?_⟩
  simpa only [OrderedLanguage.lowerDensity, alignedRatio K O e aligned,
    Function.comp_apply] using hT t ht

private def renameWindow {W : ℕ} (e : Equiv.Perm ℕ) (w : DistinctWindow ℕ W) :
    DistinctWindow ℕ W := ⟨e ∘ w.val, e.injective.comp w.property⟩

private def pullWindow {W : ℕ} (e : Equiv.Perm ℕ)
    (G : WindowSetGenerator ℕ W) : WindowSetGenerator ℕ W where
  output w := e ⁻¹' G (renameWindow e w)
  output_infinite w := (G.output_infinite (renameWindow e w)).preimage (fun y _ => e.surjective y)

private theorem pullWindow_succeeds {W : ℕ} (e : Equiv.Perm ℕ)
    {G : WindowSetGenerator ℕ W} {S : Set ℕ}
    (hG : IsRepetitionFreeWindowGeneratorOn G (e '' S)) :
    IsRepetitionFreeWindowGeneratorOn (pullWindow e G) S := by
  intro s hinj hs
  obtain ⟨T,hT⟩ := hG (e ∘ s) (e.injective.comp hinj) (renamedPresents e hs)
  exact ⟨T, fun t ht x hx => e.injective.mem_set_image.mp (hT t ht hx)⟩

/-- Width-`W` guarantee on repetition-free presentations, using the
inherited target order of Definition 8. -/
def FixedWindowGuarantee (k W : ℕ) (σ : ℝ) : Prop :=
  ∀ (langs : Fin k → Set ℕ), Injective langs → ∀ hi : ∀ i, (langs i).Infinite,
    ∃ G : WindowSetGenerator ℕ W, (∀ i, IsRepetitionFreeWindowGeneratorOn G (langs i)) ∧
      ∀ i s (hs : Injective s), Generic.Presents s (langs i) →
        σ ≤ windowRunUpperDensity (OrderedLanguage.canonical (langs i) (hi i)) G s hs

private theorem fixedWindow_bound {k W : ℕ} (hk : 2 ≤ k) (hW : 0 < W) {σ : ℝ}
    (hσ : FixedWindowGuarantee k W σ) : σ ≤ memorylessSpernerValue k := by
  obtain ⟨K, langs, i, s, hs, hinj, hi, hc, hp, hard⟩ := lemma_4_12_single_hard_instance k hk
  obtain ⟨e, himage, he⟩ := alignTargetOrder K (langs i) (hi i) hc.symm
  let family := fun j => e '' langs j
  have inf (j) : (family j).Infinite := (hi j).image e.injective.injOn
  obtain ⟨G,hG,density⟩ := hσ family (renamedFamily_injective e hinj) inf
  obtain ⟨T,hT⟩ := hard W hW _ (fun j => pullWindow_succeeds e (hG j))
  let O := OrderedLanguage.canonical (family i) (inf i)
  have aligned (n) : e (K.enumeration n) = O.enumeration n := by
    simpa [O, family, himage] using he n
  apply (density i _ (e.injective.comp hs) (renamedPresents e (hp.trans hc.symm))).trans
  apply windowRunUpperDensity_le_of_eventually
  filter_upwards [eventually_ge_atTop T] with t ht
  change O.upperDensity (G (renameWindow e (windowAt s hs t W))) ≤ _
  simpa only [pullWindow, OrderedLanguage.upperDensity, alignedRatio K O e aligned,
    memorylessSpernerValue] using hT t ht

/-- Theorem 4.10. Fixing one order on the alphabet before the family is
chosen leaves the sliding-window minimax value equal to the Sperner bound. -/
theorem fixedOrder_window (k W : ℕ) (hk : 1 ≤ k) (hW : 0 < W) :
    sSup {σ : ℝ | σ ∈ Icc 0 1 ∧ FixedWindowGuarantee k W σ} =
      1 / (Nat.choose (k - 1) ((k - 1) / 2) : ℝ) := by
  change _ = memorylessSpernerValue k
  apply IsGreatest.csSup_eq
  refine ⟨⟨memorylessSpernerValue_mem_Icc k, ?_⟩, ?_⟩
  · intro langs hinj hi
    obtain ⟨G,hG,hd⟩ := windowSpernerValue_guaranteed hk hW langs hinj hi
    exact ⟨G,hG, fun i s hs hp => hd i _ rfl s hs hp⟩
  · intro σ hσ
    by_cases h : k = 1
    · subst k
      simpa [memorylessSpernerValue] using hσ.1.2
    · exact fixedWindow_bound (by omega) hW hσ.2

/-- The adaptive-buffer analogue of the fixed-order guarantee. -/
def FixedBufferGuarantee (k b : ℕ) (σ : ℝ) : Prop :=
  ∀ (langs : Fin k → Set ℕ), Injective langs → ∀ hi : ∀ i, (langs i).Infinite,
    ∃ G : BufferSetGenerator ℕ b, (∀ i, IsRepetitionFreeBufferGeneratorOn G (langs i)) ∧
      ∀ i s, Injective s → Generic.Presents s (langs i) →
        σ ≤ bufferRunUpperDensity (OrderedLanguage.canonical (langs i) (hi i)) G s

private theorem fixedBuffer_attains (k b : ℕ) (hk : 1 ≤ k) :
    FixedBufferGuarantee k b (adaptiveBufferLowerValue k b) := by
  intro langs hinj hi
  obtain ⟨G,hG,hd⟩ := adaptiveBufferLowerValue_guaranteed k b hk langs hinj hi
  exact ⟨G,hG,fun i s hs hp => hd i _ rfl s hs hp⟩

/-- Theorem 4.15, including both buffer-size regimes in the inherited order. -/
theorem fixedOrder_buffer (k b : ℕ) (hk : 1 ≤ k) : adaptiveBufferLowerValue k b ≤
    sSup {σ : ℝ | σ ∈ Icc 0 1 ∧ FixedBufferGuarantee k b σ} := by
  apply le_csSup (show BddAbove {σ : ℝ | σ ∈ Icc 0 1 ∧ FixedBufferGuarantee k b σ}
    from ⟨1, fun _ h => h.1.2⟩)
  exact ⟨(adaptiveBufferLowerValue_admissible k b hk).1, fixedBuffer_attains k b hk⟩

private theorem emptyBuffer_window {k : ℕ} {σ : ℝ} (h : FixedBufferGuarantee k 0 σ) :
    FixedWindowGuarantee k 1 σ := by
  intro L distinct hi
  obtain ⟨G,success,density⟩ := h L distinct hi
  let W : WindowSetGenerator ℕ 1 :=
    ⟨fun w => G.output (emptyBufferState ℕ 0) (w.val 0),fun w => G.output_infinite _ _⟩
  have empty (s : ℕ → ℕ) (t : ℕ) : bufferState G s t = emptyBufferState ℕ 0 := by
    apply Subtype.ext
    exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (bufferState G s t).property)
  have same (s : ℕ → ℕ) (hs : Injective s) (t : ℕ) :
      W (windowAt s hs t 1) = bufferOutputAt G s t := by
    rw [bufferOutputAt,empty]
    rfl
  refine ⟨W,?_,?_⟩
  · intro i s hs hp
    obtain ⟨T,hT⟩ := success i s hs hp
    refine ⟨T,fun t ht => ?_⟩
    change W (windowAt s hs t 1) ⊆ L i
    rw [same]; exact hT t ht
  · intro i s hs hp
    simpa only [windowRunUpperDensity,bufferRunUpperDensity,same s hs] using density i s hs hp

theorem fixedOrder_empty_buffer (k : ℕ) (hk : 1 ≤ k) :
    sSup {σ : ℝ | σ ∈ Icc 0 1 ∧ FixedBufferGuarantee k 0 σ} =
      1 / (Nat.choose (k-1) ((k-1)/2) : ℝ) := by
  apply le_antisymm
  · rw [← fixedOrder_window k 1 hk (by decide)]
    apply csSup_le_csSup (s := {σ : ℝ | σ ∈ Icc 0 1 ∧ FixedBufferGuarantee k 0 σ}) (show BddAbove {σ : ℝ | σ ∈ Icc 0 1 ∧ FixedWindowGuarantee k 1 σ} from
      ⟨1, fun _ h => h.1.2⟩)
      ⟨_,(adaptiveBufferLowerValue_admissible k 0 hk).1,fixedBuffer_attains k 0 hk⟩
    exact fun _ h => ⟨h.1,emptyBuffer_window h.2⟩
  · simpa only [adaptiveBufferLowerValue,zero_le,if_true,Nat.sub_zero] using fixedOrder_buffer k 0 hk

/-- Remark 4.17, with the denominator expressed as the actual empty-buffer
minimax value on repetition-free streams. -/
theorem fixedOrder_buffer_comparison (k b : ℕ) (hk : 1 ≤ k) (hb : b ≤ k-3) :
    ((Nat.choose (k-1) ((k-1)/2) : ℝ) / Nat.choose (k-b-1) ((k-b-1)/2)) *
        sSup {σ : ℝ | σ ∈ Icc 0 1 ∧ FixedBufferGuarantee k 0 σ} ≤
      sSup {σ : ℝ | σ ∈ Icc 0 1 ∧ FixedBufferGuarantee k b σ} := by
  rw [fixedOrder_empty_buffer k hk]
  have pos : (0 : ℝ) < Nat.choose (k-1) ((k-1)/2) := by
    exact_mod_cast Nat.choose_pos (Nat.div_le_self _ _)
  have eq (a : ℝ) : ((Nat.choose (k-1) ((k-1)/2) : ℝ)/a) *
      (1/(Nat.choose (k-1) ((k-1)/2) : ℝ)) = 1/a := by
    field_simp [pos.ne']
  rw [eq]
  simpa only [adaptiveBufferLowerValue,if_pos hb] using fixedOrder_buffer k b hk

end GenLimit.BoundedMemory
