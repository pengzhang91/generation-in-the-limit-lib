import GenLimit.ContrastiveGeneration.CorruptedPresentations
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Countable
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Defect numbers as exact forced wrong-cut infima

Source: Xiaoyu Li, Andi Han, Jiaojiao Jiang, and Junbin Gao,
*Contrastive Identification and Generation in the Limit*,
arXiv:2605.06211v1, Definition 6.2 and Proposition 6.3.

The source cardinalities take values in `ℕ ∪ {∞}`.  We model them literally
with `Set.encard : Set α → ℕ∞`; no finite-cardinality fallback is used.
Likewise, the forced number is the literal infimum of the extended-natural
violation counts of all clean valid presentations.
-/

namespace GenLimit
namespace ContrastiveGeneration

/- `ENat` is definitionally `WithTop ℕ`, but its basic API intentionally
does not install infinitary lattice operations.  Definition 6.2 requires
the literal infimum, so locally transport the standard `WithTop ℕ`
conditionally-complete structure. -/
noncomputable local instance : InfSet ENat :=
  inferInstanceAs (InfSet (WithTop Nat))

noncomputable local instance : SupSet ENat :=
  inferInstanceAs (SupSet (WithTop Nat))

noncomputable local instance : ConditionallyCompleteLattice ENat :=
  inferInstanceAs (ConditionallyCompleteLattice (WithTop Nat))

/-! ## Literal defect and violation values -/

/-- Definition 6.2's positive-side defect set
`D⁺_{h→g} = supp(h) \ V(Γ(h,g))`. -/
def positiveDefectSet (h g : Set α) : Set α :=
  h \ commonVertices h g

/-- Definition 6.2's extended-natural defect number. -/
noncomputable def defectNumber (h g : Set α) : ℕ∞ :=
  (positiveDefectSet h g).encard

/-- Indices at which a presentation pair violates `g`'s cut. -/
def wrongCutViolationTimes
    (g : Set α) (stream : ℕ → Edge α) : Set ℕ :=
  {t | ¬Crosses g (stream t)}

/-- The source's `viol_g(P)`, with infinite index sets valued at `⊤`. -/
noncomputable def wrongCutViolationCount
    (g : Set α) (stream : ℕ → Edge α) : ℕ∞ :=
  (wrongCutViolationTimes g stream).encard

/-- All extended-natural wrong-cut counts attained by clean valid
presentations of `h`. -/
def cleanWrongCutViolationCounts
    (h g : Set α) : Set ℕ∞ :=
  {c | ∃ stream : ℕ → Edge α,
    IsContrastivePresentation stream h ∧
      wrongCutViolationCount g stream = c}

/-- The literal infimum in Proposition 6.3. -/
noncomputable def forcedWrongCutViolationInfimum
    (h g : Set α) : ℕ∞ :=
  sInf (cleanWrongCutViolationCounts h g)

/-- The paper's standing support assumption `∅ ⊊ h ⊊ X`. -/
def ProperNontrivialSupport (h : Set α) : Prop :=
  h.Nonempty ∧ hᶜ.Nonempty

/-- A clean presentation is exactly a zero-corrupted presentation under
Definition 6.1. -/
theorem isContrastivePresentation_iff_zeroCorrupted
    {stream : ℕ → Edge α} {h : Set α} :
    IsContrastivePresentation stream h ↔
      IsKCorruptedContrastivePresentation 0 stream h := by
  constructor
  · intro hP
    have hEmpty :
        {n : ℕ | ¬Crosses h (stream n)} = ∅ := by
      ext n
      simp [hP.1 n]
    refine ⟨?_, ?_, hP.2⟩
    · rw [hEmpty]
      exact Set.finite_empty
    · rw [hEmpty]
      simp
  · intro hP
    have hCardZero :
        {n : ℕ | ¬Crosses h (stream n)}.ncard = 0 :=
      Nat.eq_zero_of_le_zero hP.2.1
    have hEmpty :
        {n : ℕ | ¬Crosses h (stream n)} = ∅ :=
      (Set.ncard_eq_zero hP.1).1 hCardZero
    constructor
    · intro n
      have hn :
          n ∉ {t : ℕ | ¬Crosses h (stream t)} := by
        rw [hEmpty]
        exact Set.notMem_empty n
      simpa using hn
    · exact hP.2.2

/-! ## Every clean presentation pays for every defect -/

theorem incident_positive_unique
    {h : Set α} {e : Edge α} {x y : α}
    (he : Crosses h e)
    (hxInc : Incident x e) (hyInc : Incident y e)
    (hx : x ∈ h) (hy : y ∈ h) :
    x = y := by
  rcases hxInc with rfl | rfl <;>
    rcases hyInc with rfl | rfl
  · rfl
  · exact False.elim
      (right_not_mem_of_left_mem_of_crosses hx he hy)
  · exact False.elim
      (left_not_mem_of_right_mem_of_crosses hx he hy)
  · rfl

/-- Choose one presentation time incident to a positive defect. -/
noncomputable def defectIncidentTime
    {h g : Set α} {stream : ℕ → Edge α}
    (hP : IsContrastivePresentation stream h)
    (x : positiveDefectSet h g) : ℕ :=
  Classical.choose (hP.2 x.2.1)

theorem defectIncidentTime_spec
    {h g : Set α} {stream : ℕ → Edge α}
    (hP : IsContrastivePresentation stream h)
    (x : positiveDefectSet h g) :
    Incident x.1 (stream (defectIncidentTime hP x)) :=
  Classical.choose_spec (hP.2 x.2.1)

theorem defectIncidentTime_is_violation
    {h g : Set α} {stream : ℕ → Edge α}
    (hP : IsContrastivePresentation stream h)
    (x : positiveDefectSet h g) :
    defectIncidentTime hP x ∈
      wrongCutViolationTimes g stream := by
  intro hgCross
  exact x.2.2
    ⟨stream (defectIncidentTime hP x),
      ⟨hP.1 _, hgCross⟩,
      defectIncidentTime_spec hP x⟩

/-- The source's injection `x ↦ t(x)` from positive defects to
wrong-cut violation occurrences. -/
noncomputable def defectToViolationTime
    {h g : Set α} {stream : ℕ → Edge α}
    (hP : IsContrastivePresentation stream h) :
    positiveDefectSet h g →
      wrongCutViolationTimes g stream :=
  fun x =>
    ⟨defectIncidentTime hP x,
      defectIncidentTime_is_violation hP x⟩

theorem defectToViolationTime_injective
    {h g : Set α} {stream : ℕ → Edge α}
    (hP : IsContrastivePresentation stream h) :
    Function.Injective
      (defectToViolationTime (g := g) hP) := by
  intro x y hxy
  apply Subtype.ext
  have htime :
      defectIncidentTime hP x =
        defectIncidentTime hP y :=
    congrArg Subtype.val hxy
  apply incident_positive_unique
    (hP.1 (defectIncidentTime hP x))
    (defectIncidentTime_spec hP x)
  · rw [htime]
    exact defectIncidentTime_spec hP y
  · exact x.2.1
  · exact y.2.1

/-- The exact extended-cardinal lower bound in Proposition 6.3. -/
theorem defectNumber_le_wrongCutViolationCount
    {h g : Set α} {stream : ℕ → Edge α}
    (hP : IsContrastivePresentation stream h) :
    defectNumber h g ≤ wrongCutViolationCount g stream := by
  unfold defectNumber wrongCutViolationCount Set.encard
  exact ENat.card_le_card_of_injective
    (defectToViolationTime_injective (g := g) hP)

theorem defectNumber_le_forcedWrongCutViolationInfimum
    (h g : Set α)
    (hCounts : (cleanWrongCutViolationCounts h g).Nonempty) :
    defectNumber h g ≤
      forcedWrongCutViolationInfimum h g := by
  unfold forcedWrongCutViolationInfimum
  apply le_csInf hCounts
  intro c hc
  obtain ⟨stream, hP, rfl⟩ := hc
  exact defectNumber_le_wrongCutViolationCount hP

/-! ## A clean presentation with exactly one violation per finite defect -/

/-- Any two proper nontrivial cuts have a common crossing edge. -/
theorem exists_commonCrossing_of_proper
    {h g : Set α}
    (hh : ProperNontrivialSupport h)
    (hg : ProperNontrivialSupport g) :
    ∃ e : Edge α, CommonCrossing h g e := by
  obtain ⟨x, hxh⟩ := hh.1
  obtain ⟨y, hyhCompl⟩ := hh.2
  have hyh : y ∉ h := hyhCompl
  have hxy : x ≠ y := by
    intro hEq
    exact hyh (hEq ▸ hxh)
  by_cases hxg : x ∈ g
  · by_cases hyg : y ∈ g
    · obtain ⟨z, hzgCompl⟩ := hg.2
      have hzg : z ∉ g := hzgCompl
      by_cases hzh : z ∈ h
      · have hzy : z ≠ y := by
          intro hEq
          exact hyh (hEq ▸ hzh)
        exact
          ⟨⟨z, y, hzy⟩,
            Or.inl ⟨hzh, hyh⟩,
            Or.inr ⟨hyg, hzg⟩⟩
      · have hxz : x ≠ z := by
          intro hEq
          exact hzh (hEq ▸ hxh)
        exact
          ⟨⟨x, z, hxz⟩,
            Or.inl ⟨hxh, hzh⟩,
            Or.inl ⟨hxg, hzg⟩⟩
    · exact
        ⟨⟨x, y, hxy⟩,
          Or.inl ⟨hxh, hyh⟩,
          Or.inl ⟨hxg, hyg⟩⟩
  · by_cases hyg : y ∈ g
    · exact
        ⟨⟨x, y, hxy⟩,
          Or.inl ⟨hxh, hyh⟩,
          Or.inr ⟨hyg, hxg⟩⟩
    · obtain ⟨z, hzg⟩ := hg.1
      by_cases hzh : z ∈ h
      · have hzy : z ≠ y := by
          intro hEq
          exact hyh (hEq ▸ hzh)
        exact
          ⟨⟨z, y, hzy⟩,
            Or.inl ⟨hzh, hyh⟩,
            Or.inl ⟨hzg, hyg⟩⟩
      · have hxz : x ≠ z := by
          intro hEq
          exact hxg (hEq ▸ hzg)
        exact
          ⟨⟨x, z, hxz⟩,
            Or.inl ⟨hxh, hzh⟩,
            Or.inr ⟨hzg, hxg⟩⟩

/-- The non-defect positive set used for common-crossing filler pairs. -/
def positiveNondefectSet (h g : Set α) : Set α :=
  h ∩ commonVertices h g

theorem positiveNondefectSet_nonempty
    {h g : Set α}
    (hh : ProperNontrivialSupport h)
    (hg : ProperNontrivialSupport g) :
    (positiveNondefectSet h g).Nonempty := by
  obtain ⟨e, he⟩ := exists_commonCrossing_of_proper hh hg
  rcases he.1 with heh | heh
  · exact
      ⟨e.left, heh.1,
        ⟨e, he, Or.inl rfl⟩⟩
  · exact
      ⟨e.right, heh.1,
        ⟨e, he, Or.inr rfl⟩⟩

/-- A chosen common-crossing pair incident to a non-defect positive. -/
noncomputable def commonEdgeForNondefect
    {h g : Set α} (x : positiveNondefectSet h g) :
    Edge α :=
  Classical.choose x.2.2

theorem commonEdgeForNondefect_spec
    {h g : Set α} (x : positiveNondefectSet h g) :
    CommonCrossing h g (commonEdgeForNondefect x) ∧
      Incident x.1 (commonEdgeForNondefect x) :=
  Classical.choose_spec x.2.2

/-- Pair a defect positive with a fixed `h`-negative point. -/
def edgeForDefect
    {h g : Set α} (z : ↥(hᶜ : Set α))
    (x : positiveDefectSet h g) : Edge α :=
  ⟨x.1, z.1, fun hEq => z.2 (hEq ▸ x.2.1)⟩

theorem edgeForDefect_crosses
    {h g : Set α} (z : ↥(hᶜ : Set α))
    (x : positiveDefectSet h g) :
    Crosses h (edgeForDefect z x) := by
  exact Or.inl ⟨x.2.1, z.2⟩

theorem edgeForDefect_not_crosses
    {h g : Set α} (z : ↥(hᶜ : Set α))
    (x : positiveDefectSet h g) :
    ¬Crosses g (edgeForDefect z x) := by
  intro hgCross
  exact x.2.2
    ⟨edgeForDefect z x,
      ⟨edgeForDefect_crosses z x, hgCross⟩,
      Or.inl rfl⟩

/-! ## Clean presentation existence -/

/-- Pair an arbitrary `h`-positive with a fixed `h`-negative. -/
def edgeForPositive
    {h : Set α} (z : ↥(hᶜ : Set α)) (x : h) :
    Edge α :=
  ⟨x.1, z.1, fun hEq => z.2 (hEq ▸ x.2)⟩

theorem edgeForPositive_crosses
    {h : Set α} (z : ↥(hᶜ : Set α)) (x : h) :
    Crosses h (edgeForPositive z x) :=
  Or.inl ⟨x.2, z.2⟩

theorem exists_clean_contrastive_presentation
    [Countable α] {h : Set α}
    (hh : ProperNontrivialSupport h) :
    ∃ stream : ℕ → Edge α,
      IsContrastivePresentation stream h := by
  classical
  let z : ↥(hᶜ : Set α) :=
    ⟨Classical.choose hh.2, Classical.choose_spec hh.2⟩
  obtain ⟨enumeration, hSurjective⟩ :=
    (Set.to_countable h).exists_surjective hh.1
  let stream : ℕ → Edge α :=
    fun n => edgeForPositive z (enumeration n)
  refine ⟨stream, ?_, ?_⟩
  · intro n
    exact edgeForPositive_crosses z (enumeration n)
  · intro x hx
    obtain ⟨n, hn⟩ := hSurjective ⟨x, hx⟩
    refine ⟨n, ?_⟩
    have hvalue :
        (enumeration n).1 = x :=
      congrArg Subtype.val hn
    exact Or.inl hvalue.symm

theorem cleanWrongCutViolationCounts_nonempty
    [Countable α] {h g : Set α}
    (hh : ProperNontrivialSupport h) :
    (cleanWrongCutViolationCounts h g).Nonempty := by
  obtain ⟨stream, hP⟩ :=
    exists_clean_contrastive_presentation hh
  exact
    ⟨wrongCutViolationCount g stream,
      stream, hP, rfl⟩

/-! ## Exact finite-defect upper construction -/

/-- If the positive defect set is finite, there is a clean presentation
with exactly one wrong-cut occurrence per defect and no other violations. -/
theorem exists_clean_presentation_wrongCutCount_eq_defect
    [Countable α] {h g : Set α}
    (hh : ProperNontrivialSupport h)
    (hg : ProperNontrivialSupport g)
    (hDefectFinite : (positiveDefectSet h g).Finite) :
    ∃ stream : ℕ → Edge α,
      IsContrastivePresentation stream h ∧
      wrongCutViolationCount g stream =
        defectNumber h g := by
  classical
  let D := positiveDefectSet h g
  let N := positiveNondefectSet h g
  have hN : N.Nonempty := by
    simpa [N] using positiveNondefectSet_nonempty hh hg
  letI : Fintype D := by
    dsimp [D]
    exact hDefectFinite.fintype
  let d := Fintype.card D
  let defectEnumeration : Fin d ≃ D :=
    (Fintype.equivFin D).symm
  obtain ⟨nondefectEnumeration, hNondefectSurjective⟩ :=
    (Set.to_countable N).exists_surjective hN
  let z : ↥(hᶜ : Set α) :=
    ⟨Classical.choose hh.2, Classical.choose_spec hh.2⟩
  let stream : ℕ → Edge α :=
    fun n =>
      if hn : n < d then
        edgeForDefect z
          (defectEnumeration ⟨n, hn⟩)
      else
        commonEdgeForNondefect
          (nondefectEnumeration (n - d))
  have hCrosses (n : ℕ) :
      Crosses h (stream n) := by
    by_cases hn : n < d
    · simp only [stream, dif_pos hn]
      exact edgeForDefect_crosses z
        (defectEnumeration ⟨n, hn⟩)
    · simp only [stream, dif_neg hn]
      exact (commonEdgeForNondefect_spec
        (nondefectEnumeration (n - d))).1.1
  have hCovers :
      h ⊆ {x | ∃ n, Incident x (stream n)} := by
    intro x hx
    by_cases hxCommon : x ∈ commonVertices h g
    · let xn : N := ⟨x, hx, hxCommon⟩
      obtain ⟨r, hr⟩ := hNondefectSurjective xn
      refine ⟨d + r, ?_⟩
      have hnotlt : ¬d + r < d := by omega
      have hIncident :=
        (commonEdgeForNondefect_spec
          (nondefectEnumeration r)).2
      have hvalue :
          (nondefectEnumeration r).1 = x :=
        congrArg Subtype.val hr
      simpa [stream, hnotlt, hvalue] using hIncident
    · let xd : D := ⟨x, hx, hxCommon⟩
      let i : Fin d := defectEnumeration.symm xd
      refine ⟨i.1, ?_⟩
      have hi : i.1 < d := i.2
      have hFin :
          (⟨i.1, hi⟩ : Fin d) = i :=
        Fin.ext rfl
      have hEnum :
          defectEnumeration ⟨i.1, hi⟩ = xd := by
        rw [hFin]
        exact defectEnumeration.apply_symm_apply xd
      simp only [stream, dif_pos hi, hEnum]
      exact Or.inl rfl
  have hPresentation :
      IsContrastivePresentation stream h :=
    ⟨hCrosses, hCovers⟩
  have hViolation (n : ℕ) :
      n ∈ wrongCutViolationTimes g stream ↔ n < d := by
    change (¬Crosses g (stream n)) ↔ n < d
    by_cases hn : n < d
    · simp only [stream, dif_pos hn, hn, iff_true]
      exact edgeForDefect_not_crosses z
        (defectEnumeration ⟨n, hn⟩)
    · simp only [stream, dif_neg hn, hn, iff_false,
        not_not]
      exact (commonEdgeForNondefect_spec
        (nondefectEnumeration (n - d))).1.2
  have hViolationTimes :
      wrongCutViolationTimes g stream =
        {n : ℕ | n < d} := by
    ext n
    exact hViolation n
  have hCount :
      wrongCutViolationCount g stream = (d : ℕ∞) := by
    unfold wrongCutViolationCount
    rw [hViolationTimes]
    exact Set.Nat.encard_range d
  have hDefectCard :
      defectNumber h g = (d : ℕ∞) := by
    unfold defectNumber
    change D.encard = (d : ℕ∞)
    simp [d]
  exact
    ⟨stream, hPresentation,
      hCount.trans hDefectCard.symm⟩

/-! ## Proposition 6.3 -/

/-- Proposition 6.3: the extended-natural defect number is exactly the
infimum of the extended-natural wrong-cut violation counts over all clean
valid contrastive presentations. -/
theorem proposition_6_3_defect_eq_forced_wrong_cut_infimum
    [Countable α] {h g : Set α}
    (_hDistinct : h ≠ g)
    (hh : ProperNontrivialSupport h)
    (hg : ProperNontrivialSupport g) :
    forcedWrongCutViolationInfimum h g =
      defectNumber h g := by
  have hCounts :
      (cleanWrongCutViolationCounts h g).Nonempty :=
    cleanWrongCutViolationCounts_nonempty hh
  have hLower :
      defectNumber h g ≤
        forcedWrongCutViolationInfimum h g :=
    defectNumber_le_forcedWrongCutViolationInfimum
      h g hCounts
  apply le_antisymm
  · by_cases hFinite :
      (positiveDefectSet h g).Finite
    · obtain ⟨stream, hP, hCount⟩ :=
        exists_clean_presentation_wrongCutCount_eq_defect
          hh hg hFinite
      unfold forcedWrongCutViolationInfimum
      apply csInf_le
      · exact ⟨0, fun _ _ => bot_le⟩
      · exact ⟨stream, hP, hCount⟩
    · have hInfinite :
          (positiveDefectSet h g).Infinite :=
        hFinite
      rw [defectNumber, hInfinite.encard_eq]
      exact le_top
  · exact hLower

/-- The final “in particular” clause of Proposition 6.3. -/
theorem proposition_6_3_notEliminable_iff_defectNumber_zero
    [Countable α] {h g : Set α}
    (_hDistinct : h ≠ g)
    (hh : ProperNontrivialSupport h)
    (_hg : ProperNontrivialSupport g) :
    NotEliminableFrom g h ↔ defectNumber h g = 0 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hh.1
  let enumeration :=
    Set.enumerateCountable (Set.to_countable h) x₀
  have hEnumeration :
      h ⊆ Set.range enumeration :=
    Set.subset_range_enumerate
      (Set.to_countable h) x₀
  rw [proposition_4_2 x₀ hx₀ enumeration hEnumeration]
  unfold defectNumber positiveDefectSet
  rw [Set.encard_eq_zero]
  exact Set.diff_eq_empty.symm

end ContrastiveGeneration
end GenLimit
