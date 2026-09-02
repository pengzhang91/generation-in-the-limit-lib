import GenLimit.Paper14_ListLanguageIdentification.GeneralNecessity

/-!
# Stratification of list-identifiable language families

Source: Charikar--Pabbaraju--Tewari,
*A Characterization of List Language Identification in the Limit*,
arXiv:2511.04103v1, Section 7.

This file formalizes the paper's peeling construction from the `k`-Angluin
condition to a cover by exactly `k` indexed subcollections, each satisfying
Angluin's tell-tale condition relative to that subcollection.  It also
constructs the paper's alternative list identifier by running one relative
Angluin learner per layer.

The converse from arbitrary `k`-list identification to the `k`-Angluin
condition is Theorem 7's adaptive lower bound and is deliberately not assumed
here.
-/

namespace GenLimit.ListIdentification

/-- A tell-tale for `F i` relative to an active set of indices `I`. -/
def IsRelativeTellTale
    (F : GenLimit.Generic.LanguageFamily α)
    (I : Set ℕ) (i : ℕ) (T : Finset α) : Prop :=
  (↑T : Set α) ⊆ F i ∧
    ∀ j, j ∈ I →
      (↑T : Set α) ⊆ F j →
      F j ⊆ F i →
      F i ⊆ F j

/-- Angluin's condition restricted to an indexed subcollection. -/
def RelativeConditionTwo
    (F : GenLimit.Generic.LanguageFamily α)
    (I : Set ℕ) : Prop :=
  ∀ i, i ∈ I → ∃ T : Finset α, IsRelativeTellTale F I i T

/-- A list of indexed subcollections covers all language indices. -/
def CoversAllIndices (layers : List (Set ℕ)) : Prop :=
  ∀ i, ∃ I ∈ layers, i ∈ I

/-- The source's stratification property: exactly `k` subcollections cover
the family and each subcollection satisfies Angluin's condition.  The source
does not require the displayed union to be disjoint. -/
def HasAngluinStratification
    (F : GenLimit.Generic.LanguageFamily α) (k : ℕ) : Prop :=
  ∃ layers : List (Set ℕ),
    layers.length = k ∧
      CoversAllIndices layers ∧
      ∀ I, I ∈ layers → RelativeConditionTwo F I

/-! ## The paper's peeling construction -/

/-- The top layer selected from an active set at recursive level `k + 1`.
An index is kept exactly when it has no incoming edge in the relation of
Section 7. -/
def peelLayer
    (F : GenLimit.Generic.LanguageFamily α)
    (k : ℕ) (I : Set ℕ) : Set ℕ :=
  {j |
    j ∈ I ∧
      ∀ i, i ∈ I →
        ¬(F j ⊂ F i ∧
          (↑(psiTellTale F i k) : Set α) ⊆ F j)}

/-- Every peeled layer satisfies Angluin's condition relative to itself. -/
theorem peelLayer_relativeConditionTwo
    {F : GenLimit.Generic.LanguageFamily α}
    {k : ℕ} {I : Set ℕ}
    (hPsi : ∀ i, i ∈ I → Psi F i (k + 1)) :
    RelativeConditionTwo F (peelLayer F k I) := by
  classical
  intro i hi
  refine ⟨psiTellTale F i k, (psiTellTale_spec (hPsi i hi.1)).1, ?_⟩
  intro j hj hTj hji
  by_contra hnot
  have hproper : F j ⊂ F i := ⟨hji, hnot⟩
  exact (hj.2 i hi.1) ⟨hproper, hTj⟩

/-- Every index not selected in the top layer satisfies the next lower
recursive predicate. -/
theorem psi_of_mem_residual
    {F : GenLimit.Generic.LanguageFamily α}
    {k : ℕ} {I : Set ℕ}
    (hPsi : ∀ i, i ∈ I → Psi F i (k + 1))
    {j : ℕ} (hj : j ∈ I \ peelLayer F k I) :
    Psi F j k := by
  classical
  have hIncoming :
      ∃ i, i ∈ I ∧
        F j ⊂ F i ∧
        (↑(psiTellTale F i k) : Set α) ⊆ F j := by
    by_contra hnone
    push_neg at hnone
    exact hj.2 ⟨hj.1, fun i hi hpair =>
      hnone i hi hpair.1 hpair.2⟩
  obtain ⟨i, hi, hproper, hTj⟩ := hIncoming
  exact (psiTellTale_spec (hPsi i hi)).2 j hTj hproper

/-- Recursive peeling produces exactly `k` relative-Angluin layers covering
any active set whose members all satisfy `Psi` at level `k`. -/
theorem exists_relative_stratification
    (F : GenLimit.Generic.LanguageFamily α) :
    ∀ k : ℕ, ∀ I : Set ℕ,
      (∀ i, i ∈ I → Psi F i k) →
      ∃ layers : List (Set ℕ),
        layers.length = k ∧
          (∀ i, i ∈ I ↔ ∃ J ∈ layers, i ∈ J) ∧
          ∀ J, J ∈ layers → RelativeConditionTwo F J := by
  intro k
  induction k with
  | zero =>
      intro I hPsi
      have hI : I = ∅ := by
        ext i
        constructor
        · intro hi
          exact (psi_zero F i (hPsi i hi)).elim
        · simp
      refine ⟨[], rfl, ?_, ?_⟩
      · simp [hI]
      · simp
  | succ k ih =>
      intro I hPsi
      let J := peelLayer F k I
      let R := I \ J
      have hResidual : ∀ i, i ∈ R → Psi F i k := by
        intro i hi
        exact psi_of_mem_residual hPsi hi
      obtain ⟨layers, hlength, hcover, hconditions⟩ :=
        ih R hResidual
      refine ⟨J :: layers, by simp [hlength], ?_, ?_⟩
      · intro i
        constructor
        · intro hi
          by_cases hiJ : i ∈ J
          · exact ⟨J, by simp, hiJ⟩
          · have hiR : i ∈ R := ⟨hi, hiJ⟩
            obtain ⟨K, hKmem, hiK⟩ := (hcover i).mp hiR
            exact ⟨K, by simp [hKmem], hiK⟩
        · rintro ⟨K, hKmem, hiK⟩
          simp only [List.mem_cons] at hKmem
          rcases hKmem with rfl | hKmem
          · exact hiK.1
          · exact (hcover i).mpr ⟨K, hKmem, hiK⟩ |>.1
      · intro K hKmem
        simp only [List.mem_cons] at hKmem
        rcases hKmem with rfl | hKmem
        · exact peelLayer_relativeConditionTwo hPsi
        · exact hconditions K hKmem

/-- The `k`-Angluin condition yields the `k`-layer stratification constructed
in Section 7. -/
theorem kAngluin_implies_stratification
    {F : GenLimit.Generic.LanguageFamily α} {k : ℕ}
    (h : KAngluinCondition F k) :
    HasAngluinStratification F k := by
  obtain ⟨layers, hlength, hcover, hconditions⟩ :=
    exists_relative_stratification F k Set.univ
      (fun i _ => h i)
  refine ⟨layers, hlength, ?_, hconditions⟩
  intro i
  exact (hcover i).mp (Set.mem_univ i)

/-! ## The alternative identifier induced by a stratification -/

/-- Choose one relative tell-tale for each index in `I`. -/
noncomputable def relativeTellTale
    (F : GenLimit.Generic.LanguageFamily α)
    (I : Set ℕ) (i : ℕ) : Finset α := by
  classical
  exact
    if h : ∃ T : Finset α, IsRelativeTellTale F I i T then
      Classical.choose h
    else
      ∅

theorem relativeTellTale_spec
    {F : GenLimit.Generic.LanguageFamily α}
    {I : Set ℕ} (hI : RelativeConditionTwo F I)
    {i : ℕ} (hi : i ∈ I) :
    IsRelativeTellTale F I i (relativeTellTale F I i) := by
  classical
  have hex : ∃ T : Finset α, IsRelativeTellTale F I i T :=
    hI i hi
  rw [relativeTellTale, dif_pos hex]
  exact Classical.choose_spec hex

/-- One relative Angluin learner, expressed using the stable least eligible
index already used in Claim 5.1. -/
noncomputable def relativeIdentifier
    (F : GenLimit.Generic.LanguageFamily α)
    (I : Set ℕ) : GenLimit.Angluin.SemanticIdentifier α :=
  fun history =>
    levelChoice F (relativeTellTale F I) I
      (GenLimit.Angluin.historySample history)

theorem relativeIdentifier_identifies_member
    {F : GenLimit.Generic.LanguageFamily α}
    {I : Set ℕ} (hI : RelativeConditionTwo F I)
    {z : ℕ} (hzI : z ∈ I)
    {stream : GenLimit.Generic.Stream α}
    (hP : GenLimit.Generic.Presents stream (F z)) :
    ∃ N, ∀ t, N ≤ t →
      F (relativeIdentifier F I (GenLimit.textPrefix stream t)) = F z := by
  classical
  let T : ℕ → Finset α := relativeTellTale F I
  have hT : ∀ i, i ∈ I → (↑(T i) : Set α) ⊆ F i := by
    intro i hi
    exact (relativeTellTale_spec hI hi).1
  obtain ⟨N, hstable⟩ :=
    levelChoice_stabilizes
      (F := F) (T := T) (I := I) (z := z)
      hP hzI hT
  let q := limitChoice F T I z
  have hzCandidate : LimitCandidate F T I z z :=
    ⟨hzI, le_rfl, Set.Subset.rfl, hT z hzI⟩
  have hq : LimitCandidate F T I z q := by
    simpa [q] using
      limitChoice_spec (F := F) (T := T) (I := I)
        (z := z) ⟨z, hzCandidate⟩
  have hqz : F q = F z := by
    apply Set.Subset.antisymm
    · exact
        (relativeTellTale_spec hI hq.1).2
          z hzI hq.2.2.2 hq.2.2.1
    · exact hq.2.2.1
  refine ⟨N, ?_⟩
  intro t ht
  have hchoice :
      levelChoice F T I (GenLimit.Generic.sample stream t) = q :=
    hstable t ht
  change
    F (levelChoice F (relativeTellTale F I) I
      (GenLimit.Angluin.historySample (GenLimit.textPrefix stream t))) =
      F z
  rw [GenLimit.Angluin.historySample_textPrefix]
  simpa [T, q, hchoice] using hqz

/-- Run one relative identifier for each layer. -/
noncomputable def stratifiedIdentifier
    (F : GenLimit.Generic.LanguageFamily α)
    (layers : List (Set ℕ)) :
    ListIdentifier α layers.length :=
  fun _t xs r =>
    relativeIdentifier F (layers.get r) (List.ofFn xs)

/-- A cover by `k` relative Angluin classes is `k`-list identifiable, matching
the straightforward direction of the paper's stratification theorem. -/
theorem stratification_implies_listIdentifiable
    {F : GenLimit.Generic.LanguageFamily α} {k : ℕ}
    (h : HasAngluinStratification F k) :
    ListIdentifiable F k := by
  classical
  obtain ⟨layers, hlength, hcover, hconditions⟩ := h
  have hidentifies :
      ListIdentifies (stratifiedIdentifier F layers) F := by
    intro z stream hP
    obtain ⟨I, hImem, hzI⟩ := hcover z
    obtain ⟨r, hr⟩ := List.mem_iff_get.mp hImem
    have hIr : layers.get r = I := hr
    obtain ⟨N, hN⟩ :=
      relativeIdentifier_identifies_member
        (hconditions I hImem) hzI hP
    refine ⟨N, ?_⟩
    intro t ht
    refine ⟨r, ?_⟩
    change
      F (relativeIdentifier F (layers.get r)
        (List.ofFn (fun i : Fin t => stream i))) = F z
    rw [hIr]
    rw [← GenLimit.textPrefix_eq_ofFn]
    exact hN t ht
  subst k
  exact ⟨stratifiedIdentifier F layers, hidentifies⟩

/-- Section 7's full stratification theorem: under the paper's standing
presentability assumption, `k`-list identifiability is equivalent to a cover
by exactly `k` relative-Angluin layers. -/
theorem listIdentifiable_iff_stratification
    [DecidableEq α]
    {F : GenLimit.Generic.LanguageFamily α}
    (hPresentable : ∀ i, ∃ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (F i))
    (k : ℕ) :
    ListIdentifiable F k ↔ HasAngluinStratification F k := by
  constructor
  · intro h
    exact kAngluin_implies_stratification
      (theorem7_kAngluin_necessity hPresentable h)
  · exact stratification_implies_listIdentifiable

/-- The paper's stratification equivalence at list size one.  The forward
direction uses the completed one-list case of Theorem 7; the reverse
direction is the layerwise identifier above. -/
theorem one_list_identifiable_iff_stratification
    [DecidableEq α]
    {F : GenLimit.Generic.LanguageFamily α}
    (hPresentable : ∀ i, ∃ stream : GenLimit.Generic.Stream α,
      GenLimit.Generic.Presents stream (F i)) :
    ListIdentifiable F 1 ↔ HasAngluinStratification F 1 :=
  listIdentifiable_iff_stratification hPresentable 1

end GenLimit.ListIdentification
