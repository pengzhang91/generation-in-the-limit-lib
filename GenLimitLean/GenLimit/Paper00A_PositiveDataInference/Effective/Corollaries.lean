import GenLimit.Paper00A_PositiveDataInference.Effective.Necessity

/-!
# Effective corollaries of Angluin's characterization

This module formalizes Corollaries 2 and 3 of Angluin (1980). Both proofs
construct a uniform total stage emitter satisfying Condition 1 and then use
the already formalized effective Theorem 1.
-/

namespace GenLimit.Angluin

open GenLimit.Generic

/-! ## Executable least-witness tests -/

@[simp] theorem membership_eq_false_iff
    (F : EffectiveIndexedFamily) (i x : ℕ) :
    F.membership i x = false ↔ x ∉ F.language i := by
  rw [Bool.eq_false_iff]
  exact not_congr (F.membership_spec i x)

/-- No number below `x` belongs to language `i`. -/
def noEarlierMemberCheck (F : EffectiveIndexedFamily)
    (i x : ℕ) : Bool :=
  boundedAll (fun i y => !(F.membership i y)) i x

/-- `x` is the least member of language `i`. -/
def leastMemberCheck (F : EffectiveIndexedFamily)
    (i x : ℕ) : Bool :=
  F.membership i x && noEarlierMemberCheck F i x

/-- Below `m`, every member of language `j` belongs to language `i`. -/
def prefixSubsetCheck (F : EffectiveIndexedFamily)
    (p : ℕ × ℕ) (m : ℕ) : Bool :=
  boundedAll
    (fun p y => (!(F.membership p.1 y)) || F.membership p.2 y)
    p m

/-- `x` is the least member of language `i` missing from language `j`. -/
def leastDifferenceCheck (F : EffectiveIndexedFamily)
    (p : ℕ × ℕ) (x : ℕ) : Bool :=
  F.membership p.1 x && !(F.membership p.2 x) &&
    boundedAll
      (fun p y => !((F.membership p.1 y) && !(F.membership p.2 y)))
      p x

theorem noEarlierMemberCheck_eq_true_iff
    (F : EffectiveIndexedFamily) (i x : ℕ) :
    noEarlierMemberCheck F i x = true ↔
      ∀ y < x, y ∉ F.language i := by
  rw [noEarlierMemberCheck, boundedAll_eq_true_iff]
  constructor
  · intro h y hy hmem
    have := h y hy
    rw [Bool.not_eq_true', membership_eq_false_iff] at this
    exact this hmem
  · intro h y hy
    rw [Bool.not_eq_true', membership_eq_false_iff]
    exact h y hy

theorem leastMemberCheck_eq_true_iff
    (F : EffectiveIndexedFamily) (i x : ℕ) :
    leastMemberCheck F i x = true ↔
      x ∈ F.language i ∧ ∀ y < x, y ∉ F.language i := by
  rw [leastMemberCheck, Bool.and_eq_true, F.membership_spec,
    noEarlierMemberCheck_eq_true_iff]

theorem prefixSubsetCheck_eq_true_iff
    (F : EffectiveIndexedFamily) (j i m : ℕ) :
    prefixSubsetCheck F (j, i) m = true ↔
      ∀ y < m, y ∈ F.language j → y ∈ F.language i := by
  rw [prefixSubsetCheck, boundedAll_eq_true_iff]
  constructor
  · intro h y hy hj
    have hcheck := h y hy
    rw [Bool.or_eq_true, Bool.not_eq_true', membership_eq_false_iff,
      F.membership_spec] at hcheck
    exact hcheck.resolve_left (not_not.mpr hj)
  · intro h y hy
    rw [Bool.or_eq_true, Bool.not_eq_true', membership_eq_false_iff,
      F.membership_spec]
    exact Classical.em (y ∈ F.language j) |>.elim
      (fun hj => Or.inr (h y hy hj)) Or.inl

theorem leastDifferenceCheck_eq_true_iff
    (F : EffectiveIndexedFamily) (i j x : ℕ) :
    leastDifferenceCheck F (i, j) x = true ↔
      x ∈ F.language i ∧ x ∉ F.language j ∧
        ∀ y < x, y ∈ F.language i → y ∈ F.language j := by
  rw [leastDifferenceCheck, Bool.and_eq_true, Bool.and_eq_true,
    F.membership_spec, Bool.not_eq_true', membership_eq_false_iff,
    boundedAll_eq_true_iff]
  constructor
  · rintro ⟨⟨hxi, hxj⟩, hleast⟩
    refine ⟨hxi, hxj, ?_⟩
    intro y hy hyi
    have hcheck := hleast y hy
    rw [Bool.not_eq_true'] at hcheck
    by_contra hyj
    have hiTrue : F.membership i y = true :=
      (F.membership_spec i y).mpr hyi
    have hjFalse : F.membership j y = false :=
      (membership_eq_false_iff F j y).mpr hyj
    simp [hiTrue, hjFalse] at hcheck
  · rintro ⟨hxi, hxj, hleast⟩
    refine ⟨⟨hxi, hxj⟩, ?_⟩
    intro y hy
    rw [Bool.not_eq_true']
    by_cases hyi : y ∈ F.language i
    · have hiTrue : F.membership i y = true :=
        (F.membership_spec i y).mpr hyi
      have hjTrue : F.membership j y = true :=
        (F.membership_spec j y).mpr (hleast y hy hyi)
      simp [hiTrue, hjTrue]
    · have hiFalse : F.membership i y = false :=
        (membership_eq_false_iff F i y).mpr hyi
      simp [hiFalse]

theorem noEarlierMemberCheck_computable (F : EffectiveIndexedFamily) :
    Computable₂ (noEarlierMemberCheck F) := by
  have hnotMembership : Computable₂ (fun i y => !(F.membership i y)) := by
    exact Computable.to₂ <|
      Primrec.not.to_comp.comp
        (F.membership_computable.comp Computable.fst Computable.snd)
  exact boundedAll_computable hnotMembership

theorem leastMemberCheck_computable (F : EffectiveIndexedFamily) :
    Computable₂ (leastMemberCheck F) := by
  exact Primrec.and.to_comp.comp₂ F.membership_computable
    (noEarlierMemberCheck_computable F)

theorem prefixSubsetCheck_computable (F : EffectiveIndexedFamily) :
    Computable₂ (prefixSubsetCheck F) := by
  have hleft : Computable₂ (fun p : ℕ × ℕ => fun y =>
      !(F.membership p.1 y)) := by
    exact Computable.to₂ <|
      Primrec.not.to_comp.comp <|
        F.membership_computable.comp
          (Computable.fst.comp Computable.fst) Computable.snd
  have hright : Computable₂ (fun p : ℕ × ℕ => fun y =>
      F.membership p.2 y) :=
    F.membership_computable.comp₂
      (Primrec.snd.comp₂ Primrec₂.left).to_comp
      Primrec₂.right.to_comp
  exact boundedAll_computable
    (Primrec.or.to_comp.comp₂ hleft hright)

theorem leastDifferenceCheck_computable (F : EffectiveIndexedFamily) :
    Computable₂ (leastDifferenceCheck F) := by
  have hi : Computable₂ (fun p : ℕ × ℕ => fun x =>
      F.membership p.1 x) :=
    F.membership_computable.comp₂
      (Primrec.fst.comp₂ Primrec₂.left).to_comp
      Primrec₂.right.to_comp
  have hnotj : Computable₂ (fun p : ℕ × ℕ => fun x =>
      !(F.membership p.2 x)) := by
    exact Computable.to₂ <|
      Primrec.not.to_comp.comp <|
        F.membership_computable.comp
          (Computable.snd.comp Computable.fst) Computable.snd
  have hpoint : Computable₂ (fun p : ℕ × ℕ => fun x =>
      !((F.membership p.1 x) && !(F.membership p.2 x))) := by
    exact Computable.to₂ <|
      Primrec.not.to_comp.comp <|
        Primrec.and.to_comp.comp
          (hi.comp Computable.fst Computable.snd)
          (hnotj.comp Computable.fst Computable.snd)
  exact Primrec.and.to_comp.comp₂
    (Primrec.and.to_comp.comp₂ hi hnotj)
    (boundedAll_computable hpoint)

/-! ## Corollary 3: Condition 2 plus computable inclusion -/

/-- The direct Corollary 3 emitter enumerates the least target element missing
from each indexed proper sublanguage. -/
def conditionFourEmitter (F : EffectiveIndexedFamily)
    (inclusion : ℕ → ℕ → Bool) (i stage : ℕ) : Option ℕ :=
  let jx := stage.unpair
  if inclusion jx.1 i && !(inclusion i jx.1) &&
      leastDifferenceCheck F (i, jx.1) jx.2 then
    some jx.2
  else
    none

theorem conditionFourEmitter_computable
    (F : EffectiveIndexedFamily) {inclusion : ℕ → ℕ → Bool}
    (hinclusion : Computable₂ inclusion) :
    Computable₂ (conditionFourEmitter F inclusion) := by
  let Input := ℕ × ℕ
  have hi : Computable (fun z : Input => z.1) := Computable.fst
  have hj : Computable (fun z : Input => z.2.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd
  have hx : Computable (fun z : Input => z.2.unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.snd
  have hji : Computable (fun z : Input => inclusion z.2.unpair.1 z.1) :=
    hinclusion.comp hj hi
  have hnotij : Computable (fun z : Input => !(inclusion z.1 z.2.unpair.1)) :=
    Primrec.not.to_comp.comp (hinclusion.comp hi hj)
  have hdiff : Computable (fun z : Input =>
      leastDifferenceCheck F (z.1, z.2.unpair.1) z.2.unpair.2) :=
    (leastDifferenceCheck_computable F).comp
      (Computable.pair hi hj) hx
  have hcheck : Computable (fun z : Input =>
      inclusion z.2.unpair.1 z.1 && !(inclusion z.1 z.2.unpair.1) &&
        leastDifferenceCheck F (z.1, z.2.unpair.1) z.2.unpair.2) :=
    Primrec.and.to_comp.comp
      (Primrec.and.to_comp.comp hji hnotij) hdiff
  exact (Computable.to₂ <|
    Computable.cond hcheck
      (Computable.option_some.comp hx)
      (Computable.const none)).of_eq fun z => by
        rcases z with ⟨i, stage⟩
        simp only [conditionFourEmitter]
        cases hcheckValue :
          (inclusion stage.unpair.1 i && !(inclusion i stage.unpair.1) &&
            leastDifferenceCheck F (i, stage.unpair.1) stage.unpair.2) <;>
          rfl

theorem conditionFourEmitter_mem_target
    (F : EffectiveIndexedFamily) (inclusion : ℕ → ℕ → Bool)
    {i stage x : ℕ}
    (h : conditionFourEmitter F inclusion i stage = some x) :
    x ∈ F.language i := by
  rw [conditionFourEmitter] at h
  split at h
  next hcheck =>
    injection h with hx
    subst x
    rw [Bool.and_eq_true] at hcheck
    have hdiff := hcheck.2
    exact (leastDifferenceCheck_eq_true_iff F i
      stage.unpair.1 stage.unpair.2).mp hdiff |>.1
  next => contradiction

theorem conditionFourEmitter_finite
    (F : EffectiveIndexedFamily) (inclusion : ℕ → ℕ → Bool)
    (hinclusion : ∀ i j, inclusion i j = true ↔
      F.language i ⊆ F.language j)
    (hTwo : ConditionTwo F.language) (i : ℕ) :
    (enumeratedSet (conditionFourEmitter F inclusion) i).Finite := by
  classical
  obtain ⟨T, hT⟩ := hTwo i
  apply (Finset.range (T.sup id + 1)).finite_toSet.subset
  intro x hx
  obtain ⟨stage, hstage⟩ := hx
  rw [conditionFourEmitter] at hstage
  split at hstage
  next hcheck =>
    injection hstage with hxValue
    subst x
    rw [Bool.and_eq_true, Bool.and_eq_true] at hcheck
    obtain ⟨⟨hjiCheck, hijCheck⟩, hleastCheck⟩ := hcheck
    have hji : F.language stage.unpair.1 ⊆ F.language i :=
      (hinclusion stage.unpair.1 i).mp hjiCheck
    have hnotij : ¬F.language i ⊆ F.language stage.unpair.1 := by
      intro hij
      have hijTrue := (hinclusion i stage.unpair.1).mpr hij
      rw [hijTrue] at hijCheck
      contradiction
    have hTnot : ¬(↑T : Set ℕ) ⊆ F.language stage.unpair.1 := by
      intro hTj
      exact hnotij (hT.2 stage.unpair.1 hTj hji)
    obtain ⟨r, hrT, hrnot⟩ := Set.not_subset.mp hTnot
    have hrTarget : r ∈ F.language i := hT.1 hrT
    have hleast :=
      (leastDifferenceCheck_eq_true_iff F i
        stage.unpair.1 stage.unpair.2).mp hleastCheck
    have hxr : stage.unpair.2 ≤ r := by
      by_contra hnot
      have hrlt : r < stage.unpair.2 := Nat.lt_of_not_ge hnot
      exact hrnot (hleast.2.2 r hrlt hrTarget)
    have hrSup : r ≤ T.sup id := Finset.le_sup (f := id) hrT
    exact Finset.mem_range.mpr <|
      lt_of_le_of_lt (hxr.trans hrSup) (Nat.lt_succ_self _)
  next => contradiction

theorem conditionFourEmitter_isEnumeratedTellTale
    (F : EffectiveIndexedFamily) (inclusion : ℕ → ℕ → Bool)
    (hinclusion : ∀ i j, inclusion i j = true ↔
      F.language i ⊆ F.language j)
    (hTwo : ConditionTwo F.language) (i : ℕ) :
    IsEnumeratedTellTale F.language i
      (enumeratedSet (conditionFourEmitter F inclusion) i) := by
  classical
  refine ⟨conditionFourEmitter_finite F inclusion hinclusion hTwo i,
    ?_, ?_⟩
  · intro x hx
    obtain ⟨stage, hstage⟩ := hx
    exact conditionFourEmitter_mem_target F inclusion hstage
  · intro j hEmitJ hji
    by_contra hnotij
    have hmissing : ∃ x, x ∈ F.language i ∧ x ∉ F.language j :=
      Set.not_subset.mp hnotij
    let x := Nat.find hmissing
    have hx : x ∈ F.language i ∧ x ∉ F.language j := by
      dsimp [x]
      exact Nat.find_spec hmissing
    have hleast : ∀ y < x, y ∈ F.language i → y ∈ F.language j := by
      intro y hy hyi
      by_contra hyj
      exact Nat.find_min hmissing (by simpa [x] using hy) ⟨hyi, hyj⟩
    have hdiff : leastDifferenceCheck F (i, j) x = true :=
      (leastDifferenceCheck_eq_true_iff F i j x).mpr
        ⟨hx.1, hx.2, hleast⟩
    have hjiCheck : inclusion j i = true := (hinclusion j i).mpr hji
    have hijCheck : inclusion i j = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      exact hnotij ((hinclusion i j).mp htrue)
    have hemits : conditionFourEmitter F inclusion i (Nat.pair j x) = some x := by
      simp [conditionFourEmitter, hjiCheck, hijCheck, hdiff]
    exact hx.2 (hEmitJ ⟨Nat.pair j x, hemits⟩)

/-- Conditions 2 and 4 construct Condition 1. -/
theorem conditionTwo_conditionFour_conditionOne
    {F : EffectiveIndexedFamily}
    (hTwo : ConditionTwo F.language) (hFour : ConditionFour F) :
    ConditionOne F := by
  obtain ⟨inclusion, hcomputable, hinclusion⟩ := hFour
  exact ⟨conditionFourEmitter F inclusion,
    conditionFourEmitter_computable F hcomputable,
    conditionFourEmitter_isEnumeratedTellTale
      F inclusion hinclusion hTwo⟩

/-- Angluin's Corollary 3. -/
theorem corollaryThree (F : EffectiveIndexedFamily) :
    CorollaryThreeStatement F := by
  intro hTwo hFour
  exact ConditionOne.effective_sufficiency
    (conditionTwo_conditionFour_conditionOne hTwo hFour)

/-! ## Corollary 2: finite thickness -/

/-- The least element of `target \ candidate`, with an irrelevant default
when the difference is empty. This function is used only in the finiteness
proof; the stage emitter below remains fully computable. -/
noncomputable def firstDifference
    (target candidate : Set ℕ) : ℕ := by
  classical
  exact if h : ∃ x, x ∈ target ∧ x ∉ candidate then Nat.find h else 0

theorem firstDifference_eq_of_least
    {target candidate : Set ℕ} {x : ℕ}
    (hxTarget : x ∈ target) (hxCandidate : x ∉ candidate)
    (hleast : ∀ y < x, y ∈ target → y ∈ candidate) :
    firstDifference target candidate = x := by
  classical
  rw [firstDifference]
  split
  next h =>
    apply Nat.le_antisymm
    · exact Nat.find_min' h ⟨hxTarget, hxCandidate⟩
    · by_contra hnot
      have hfound := Nat.find_spec h
      exact hfound.2 (hleast _ (Nat.lt_of_not_ge hnot) hfound.1)
  next h =>
    exact False.elim (h ⟨x, hxTarget, hxCandidate⟩)

/-- A dovetailed form of the finite-thickness construction. A stage decodes
as `(t,j,m,x)`. It always emits the least target member, and additionally
emits the least target-versus-candidate disagreement `x` when the finite
prefix through `m` contains no disagreement in the other direction. -/
def conditionThreeEmitter (F : EffectiveIndexedFamily)
    (i stage : ℕ) : Option ℕ :=
  let t := stage.unpair.1
  let j := stage.unpair.2.unpair.1
  let m := stage.unpair.2.unpair.2.unpair.1
  let x := stage.unpair.2.unpair.2.unpair.2
  if leastMemberCheck F i x ||
      (leastMemberCheck F i t && F.membership j t &&
        prefixSubsetCheck F (j, i) m && decide (x < m) &&
        leastDifferenceCheck F (i, j) x) then
    some x
  else
    none

theorem conditionThreeEmitter_computable (F : EffectiveIndexedFamily) :
    Computable₂ (conditionThreeEmitter F) := by
  let Input := ℕ × ℕ
  have hi : Computable (fun z : Input => z.1) := Computable.fst
  have ht : Computable (fun z : Input => z.2.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.snd
  have hj : Computable (fun z : Input => z.2.unpair.2.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).to_comp.comp <|
      (Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.snd
  have hm : Computable (fun z : Input =>
      z.2.unpair.2.unpair.2.unpair.1) :=
    (Primrec.fst.comp Primrec.unpair).to_comp.comp <|
      (Primrec.snd.comp Primrec.unpair).to_comp.comp <|
        (Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.snd
  have hx : Computable (fun z : Input =>
      z.2.unpair.2.unpair.2.unpair.2) :=
    (Primrec.snd.comp Primrec.unpair).to_comp.comp <|
      (Primrec.snd.comp Primrec.unpair).to_comp.comp <|
        (Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.snd
  have hseed : Computable (fun z : Input =>
      leastMemberCheck F z.1 z.2.unpair.2.unpair.2.unpair.2) :=
    (leastMemberCheck_computable F).comp hi hx
  have htLeast : Computable (fun z : Input =>
      leastMemberCheck F z.1 z.2.unpair.1) :=
    (leastMemberCheck_computable F).comp hi ht
  have hjt : Computable (fun z : Input =>
      F.membership z.2.unpair.2.unpair.1 z.2.unpair.1) :=
    F.membership_computable.comp hj ht
  have hprefix : Computable (fun z : Input =>
      prefixSubsetCheck F
        (z.2.unpair.2.unpair.1, z.1)
        z.2.unpair.2.unpair.2.unpair.1) :=
    (prefixSubsetCheck_computable F).comp
      (Computable.pair hj hi) hm
  have hlt : Computable (fun z : Input => decide
      (z.2.unpair.2.unpair.2.unpair.2 <
        z.2.unpair.2.unpair.2.unpair.1)) :=
    Primrec.nat_lt.decide.to_comp.comp hx hm
  have hdiff : Computable (fun z : Input =>
      leastDifferenceCheck F
        (z.1, z.2.unpair.2.unpair.1)
        z.2.unpair.2.unpair.2.unpair.2) :=
    (leastDifferenceCheck_computable F).comp
      (Computable.pair hi hj) hx
  have hwitness : Computable (fun z : Input =>
      leastMemberCheck F z.1 z.2.unpair.1 &&
        F.membership z.2.unpair.2.unpair.1 z.2.unpair.1 &&
        prefixSubsetCheck F
          (z.2.unpair.2.unpair.1, z.1)
          z.2.unpair.2.unpair.2.unpair.1 &&
        decide (z.2.unpair.2.unpair.2.unpair.2 <
          z.2.unpair.2.unpair.2.unpair.1) &&
        leastDifferenceCheck F
          (z.1, z.2.unpair.2.unpair.1)
          z.2.unpair.2.unpair.2.unpair.2) :=
    Primrec.and.to_comp.comp
      (Primrec.and.to_comp.comp
        (Primrec.and.to_comp.comp
          (Primrec.and.to_comp.comp htLeast hjt) hprefix) hlt) hdiff
  have hcheck : Computable (fun z : Input =>
      leastMemberCheck F z.1 z.2.unpair.2.unpair.2.unpair.2 ||
        (leastMemberCheck F z.1 z.2.unpair.1 &&
          F.membership z.2.unpair.2.unpair.1 z.2.unpair.1 &&
          prefixSubsetCheck F
            (z.2.unpair.2.unpair.1, z.1)
            z.2.unpair.2.unpair.2.unpair.1 &&
          decide (z.2.unpair.2.unpair.2.unpair.2 <
            z.2.unpair.2.unpair.2.unpair.1) &&
          leastDifferenceCheck F
            (z.1, z.2.unpair.2.unpair.1)
            z.2.unpair.2.unpair.2.unpair.2)) :=
    Primrec.or.to_comp.comp hseed hwitness
  exact (Computable.to₂ <|
    Computable.cond hcheck
      (Computable.option_some.comp hx)
      (Computable.const none)).of_eq fun z => by
        rcases z with ⟨i, stage⟩
        simp only [conditionThreeEmitter]
        cases hcheckValue :
          (leastMemberCheck F i stage.unpair.2.unpair.2.unpair.2 ||
            (leastMemberCheck F i stage.unpair.1 &&
              F.membership stage.unpair.2.unpair.1 stage.unpair.1 &&
              prefixSubsetCheck F
                (stage.unpair.2.unpair.1, i)
                stage.unpair.2.unpair.2.unpair.1 &&
              decide (stage.unpair.2.unpair.2.unpair.2 <
                stage.unpair.2.unpair.2.unpair.1) &&
              leastDifferenceCheck F
                (i, stage.unpair.2.unpair.1)
                stage.unpair.2.unpair.2.unpair.2)) <;>
          rfl

private theorem leastMember_unique
    (F : EffectiveIndexedFamily) {i x y : ℕ}
    (hx : leastMemberCheck F i x = true)
    (hy : leastMemberCheck F i y = true) : x = y := by
  obtain ⟨hxi, hxleast⟩ := (leastMemberCheck_eq_true_iff F i x).mp hx
  obtain ⟨hyi, hyleast⟩ := (leastMemberCheck_eq_true_iff F i y).mp hy
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact False.elim (hyleast x hxy hxi)
  · exact hxy
  · exact False.elim (hxleast y hyx hyi)

theorem conditionThreeEmitter_mem_target
    (F : EffectiveIndexedFamily) {i stage x : ℕ}
    (h : conditionThreeEmitter F i stage = some x) :
    x ∈ F.language i := by
  rw [conditionThreeEmitter] at h
  split at h
  next hcheck =>
    injection h with hx
    subst x
    rw [Bool.or_eq_true] at hcheck
    rcases hcheck with hseed | hwitness
    · exact (leastMemberCheck_eq_true_iff F i _).mp hseed |>.1
    · rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
        Bool.and_eq_true] at hwitness
      exact (leastDifferenceCheck_eq_true_iff F i
        stage.unpair.2.unpair.1
        stage.unpair.2.unpair.2.unpair.2).mp hwitness.2 |>.1
  next => contradiction

theorem conditionThreeEmitter_finite
    (F : EffectiveIndexedFamily) (hThree : ConditionThree F.language)
    (i : ℕ) :
    (enumeratedSet (conditionThreeEmitter F) i).Finite := by
  classical
  let t := Nat.find (F.nonempty i)
  have htTarget : t ∈ F.language i := by
    dsimp [t]
    exact Nat.find_spec (F.nonempty i)
  have htLeast : leastMemberCheck F i t = true := by
    apply (leastMemberCheck_eq_true_iff F i t).mpr
    refine ⟨htTarget, ?_⟩
    intro y hy
    exact Nat.find_min (F.nonempty i) (by simpa [t] using hy)
  let candidates : Set (Set ℕ) :=
    {L | L ∈ Set.range F.language ∧ t ∈ L}
  have hcandidates : candidates.Finite := by
    have h := hThree {t} (by simp)
    simpa only [candidates, Finset.coe_singleton, Set.singleton_subset_iff]
      using h
  let possible : Set ℕ :=
    firstDifference (F.language i) '' candidates
  have hpossible : possible.Finite := hcandidates.image _
  apply (Set.finite_singleton t).union hpossible |>.subset
  intro x hx
  obtain ⟨stage, hstage⟩ := hx
  rw [conditionThreeEmitter] at hstage
  split at hstage
  next hcheck =>
    injection hstage with hxValue
    subst x
    rw [Bool.or_eq_true] at hcheck
    rcases hcheck with hseed | hwitness
    · exact Or.inl (leastMember_unique F hseed htLeast)
    · rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
        Bool.and_eq_true] at hwitness
      let j := stage.unpair.2.unpair.1
      let x := stage.unpair.2.unpair.2.unpair.2
      have htParam : stage.unpair.1 = t :=
        leastMember_unique F hwitness.1.1.1.1 htLeast
      have hjt : t ∈ F.language j := by
        have hmem := (F.membership_spec j stage.unpair.1).mp
          hwitness.1.1.1.2
        simpa [j, htParam] using hmem
      have hjCandidate : F.language j ∈ candidates :=
        ⟨⟨j, rfl⟩, hjt⟩
      have hdiff :=
        (leastDifferenceCheck_eq_true_iff F i j x).mp hwitness.2
      have hfirst : firstDifference (F.language i) (F.language j) = x :=
        firstDifference_eq_of_least hdiff.1 hdiff.2.1 hdiff.2.2
      exact Or.inr ⟨F.language j, hjCandidate, by simpa [x] using hfirst⟩
  next => contradiction

theorem conditionThreeEmitter_isEnumeratedTellTale
    (F : EffectiveIndexedFamily) (hThree : ConditionThree F.language)
    (i : ℕ) :
    IsEnumeratedTellTale F.language i
      (enumeratedSet (conditionThreeEmitter F) i) := by
  classical
  refine ⟨conditionThreeEmitter_finite F hThree i, ?_, ?_⟩
  · intro x hx
    obtain ⟨stage, hstage⟩ := hx
    exact conditionThreeEmitter_mem_target F hstage
  · intro j hEmitJ hji
    let t := Nat.find (F.nonempty i)
    have htTarget : t ∈ F.language i := by
      dsimp [t]
      exact Nat.find_spec (F.nonempty i)
    have htLeast : leastMemberCheck F i t = true := by
      apply (leastMemberCheck_eq_true_iff F i t).mpr
      refine ⟨htTarget, ?_⟩
      intro y hy
      exact Nat.find_min (F.nonempty i) (by simpa [t] using hy)
    have htEmitted : t ∈ enumeratedSet (conditionThreeEmitter F) i := by
      let stage := Nat.pair 0 (Nat.pair 0 (Nat.pair 0 t))
      refine ⟨stage, ?_⟩
      simp [stage, conditionThreeEmitter, htLeast]
    have htJ : t ∈ F.language j := hEmitJ htEmitted
    by_contra hnotij
    have hmissing : ∃ x, x ∈ F.language i ∧ x ∉ F.language j :=
      Set.not_subset.mp hnotij
    let x := Nat.find hmissing
    have hx : x ∈ F.language i ∧ x ∉ F.language j := by
      dsimp [x]
      exact Nat.find_spec hmissing
    have hxLeast : ∀ y < x, y ∈ F.language i → y ∈ F.language j := by
      intro y hy hyi
      by_contra hyj
      exact Nat.find_min hmissing (by simpa [x] using hy) ⟨hyi, hyj⟩
    have hdiff : leastDifferenceCheck F (i, j) x = true :=
      (leastDifferenceCheck_eq_true_iff F i j x).mpr
        ⟨hx.1, hx.2, hxLeast⟩
    have hprefix : prefixSubsetCheck F (j, i) (x + 1) = true :=
      (prefixSubsetCheck_eq_true_iff F j i (x + 1)).mpr
        fun y _hy hyj => hji hyj
    have hjt : F.membership j t = true := (F.membership_spec j t).mpr htJ
    let stage := Nat.pair t (Nat.pair j (Nat.pair (x + 1) x))
    have hxEmitted : conditionThreeEmitter F i stage = some x := by
      simp [stage, conditionThreeEmitter, htLeast, hjt, hprefix, hdiff]
    exact hx.2 (hEmitJ ⟨stage, hxEmitted⟩)

/-- Condition 3 constructs Condition 1. -/
theorem conditionThree_conditionOne
    {F : EffectiveIndexedFamily} (hThree : ConditionThree F.language) :
    ConditionOne F :=
  ⟨conditionThreeEmitter F, conditionThreeEmitter_computable F,
    conditionThreeEmitter_isEnumeratedTellTale F hThree⟩

/-- Angluin's Corollary 2. -/
theorem corollaryTwo (F : EffectiveIndexedFamily) :
    CorollaryTwoStatement F := by
  intro hThree
  exact ConditionOne.effective_sufficiency
    (conditionThree_conditionOne hThree)

end GenLimit.Angluin
