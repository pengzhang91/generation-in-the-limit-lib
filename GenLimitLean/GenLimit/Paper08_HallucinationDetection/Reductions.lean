import GenLimit.Paper08_HallucinationDetection.Definitions
import GenLimit.Angluin.SemanticSufficiency

/-!
# Identification and hallucination detection are equivalent

This module follows Lemmas 3.1 and 3.2 and Theorem 2.1 of Karbasi,
Montasser, Sous, and Velegkas.  The two reductions use the source algorithms:

* an identifier is followed by a growing finite subset test for its current
  language conjecture;
* an identifier is recovered from a detector by choosing the least bounded
  language which is both positive-data consistent and declared contained in
  the target.
-/

namespace GenLimit.HallucinationDetection

open GenLimit.Generic

noncomputable local instance reductionsPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The first `t` points of a fixed enumeration of the countable domain. -/
def domainPrefix (enumerate : ℕ → α) (t : ℕ) : List α :=
  List.ofFn (fun i : Fin t => enumerate i)

theorem mem_domainPrefix_iff
    {enumerate : ℕ → α} {t : ℕ} {x : α} :
    x ∈ domainPrefix enumerate t ↔ ∃ i < t, enumerate i = x := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hx
    exact ⟨i, i.isLt, hi⟩
  · rintro ⟨i, hi, hix⟩
    exact List.mem_ofFn.mpr ⟨⟨i, hi⟩, hix⟩

/-- A finite membership-query tree checking whether every queried member of
`G` belongs to `L`.  Points already known to lie in `L` require no query. -/
noncomputable def subsetTestTree (L : Set α) : List α → OracleTree α
  | [] => .answer true
  | x :: xs => if x ∈ L then subsetTestTree L xs
      else .query x (.answer false) (subsetTestTree L xs)

theorem eval_subsetTestTree_eq_true_iff
    (G L : Set α) (xs : List α) :
    OracleTree.eval G (subsetTestTree L xs) = true ↔
      ∀ x, x ∈ xs → x ∈ G → x ∈ L := by
  classical
  induction xs with
  | nil => simp [subsetTestTree, OracleTree.eval]
  | cons x xs ih =>
      by_cases hxL : x ∈ L
      · simp [subsetTestTree, hxL, ih]
      · by_cases hxG : x ∈ G
        · simp [subsetTestTree, OracleTree.eval, hxL, hxG]
        · simp [subsetTestTree, OracleTree.eval, hxL, hxG, ih]

/-- Algorithm 1: use the identifier's current conjecture and test it on a
growing prefix of the domain. -/
noncomputable def detectorFromIdentifier
    (C : GenLimit.Generic.LanguageFamily α)
    (enumerate : ℕ → α)
    (M : GenLimit.Angluin.SemanticIdentifier α) : Detector α :=
  fun t xs => subsetTestTree (C (M t xs)) (domainPrefix enumerate t)

/-- Lemma 3.1. -/
theorem lemma_3_1_identification_implies_detection
    (C : GenLimit.Generic.LanguageFamily α)
    (enumerate : ℕ → α) (henumerate : Function.Surjective enumerate)
    (hID : IdentifiableInLimit C) :
    HallucinationDetectable C := by
  classical
  obtain ⟨M, hM⟩ := hID
  refine ⟨detectorFromIdentifier C enumerate M, ?_⟩
  intro z stream hP G
  obtain ⟨j, hj, T, hT⟩ := hM z stream hP
  by_cases hGK : G ⊆ C z
  · refine ⟨T, ?_⟩
    intro t ht
    have hMt : M t (fun i => stream i) = j := by
      simpa [GenLimit.Angluin.identifierOutput] using hT t ht
    rw [DetectorCorrectAt, detectorOutput, detectorFromIdentifier,
      eval_subsetTestTree_eq_true_iff]
    rw [hMt, hj]
    constructor
    · intro _
      exact hGK
    · intro _ x _hxList hxG
      exact hGK hxG
  · obtain ⟨x, hxG, hxK⟩ := Set.not_subset.mp hGK
    obtain ⟨i, hi⟩ := henumerate x
    refine ⟨max T (i + 1), ?_⟩
    intro t ht
    have htT : T ≤ t := le_trans (Nat.le_max_left _ _) ht
    have hit : i < t :=
      lt_of_lt_of_le (Nat.lt_succ_self i)
        (le_trans (Nat.le_max_right _ _) ht)
    have hMt : M t (fun i => stream i) = j := by
      simpa [GenLimit.Angluin.identifierOutput] using hT t htT
    rw [DetectorCorrectAt, detectorOutput, detectorFromIdentifier,
      eval_subsetTestTree_eq_true_iff]
    rw [hMt, hj]
    constructor
    · intro hout
      have hxList : x ∈ domainPrefix enumerate t :=
        mem_domainPrefix_iff.mpr ⟨i, hit, hi⟩
      exact False.elim (hxK (hout x hxList hxG))
    · intro hsubset
      exact False.elim (hGK hsubset)

/-! ## From a detector to an identifier -/

/-- The two tests in Algorithm 2, together with the bounded index scope. -/
def DetectorCandidate
    (C : GenLimit.Generic.LanguageFamily α) (D : Detector α)
    {t : ℕ} (xs : Fin t → α) (i : ℕ) : Prop :=
  i ≤ t ∧
    (↑(GenLimit.Generic.sequenceSample xs) : Set α) ⊆ C i ∧
    OracleTree.eval (C i) (D t xs) = true

/-- Algorithm 2: choose the least candidate, with `0` as the paper's
arbitrary default when no candidate exists. -/
noncomputable def identifierFromDetector
    (C : GenLimit.Generic.LanguageFamily α) (D : Detector α) :
    GenLimit.Angluin.SemanticIdentifier α := by
  classical
  exact fun t xs =>
    if h : ∃ i, DetectorCandidate C D xs i then Nat.find h else 0

theorem identifierFromDetector_candidate
    {C : GenLimit.Generic.LanguageFamily α} {D : Detector α}
    {t : ℕ} {xs : Fin t → α}
    (h : ∃ i, DetectorCandidate C D xs i) :
    DetectorCandidate C D xs (identifierFromDetector C D t xs) := by
  classical
  rw [identifierFromDetector, dif_pos h]
  exact Nat.find_spec h

theorem identifierFromDetector_le_of_candidate
    {C : GenLimit.Generic.LanguageFamily α} {D : Detector α}
    {t : ℕ} {xs : Fin t → α} {i : ℕ}
    (hi : DetectorCandidate C D xs i) :
    identifierFromDetector C D t xs ≤ i := by
  classical
  let h : ∃ j, DetectorCandidate C D xs j := ⟨i, hi⟩
  rw [identifierFromDetector, dif_pos h]
  exact Nat.find_min' h hi

/-- Lemma 3.2. -/
theorem lemma_3_2_detection_implies_identification
    (C : GenLimit.Generic.LanguageFamily α)
    (hHD : HallucinationDetectable C) :
    IdentifiableInLimit C := by
  classical
  obtain ⟨D, hD⟩ := hHD
  refine ⟨identifierFromDetector C D, ?_⟩
  intro z stream hP
  let hex : ∃ i, C i = C z := ⟨z, rfl⟩
  let k : ℕ := Nat.find hex
  have hk : C k = C z := Nat.find_spec hex
  have hbelow : ∀ i, i < k → C i ≠ C z := by
    intro i hi
    exact Nat.find_min hex hi
  have hpointwise : ∀ i, i < k → ∃ N, ∀ t, N ≤ t →
      ¬DetectorCandidate C D (fun r : Fin t => stream r) i := by
    intro i hi
    by_cases htargetCandidate : C z ⊆ C i
    · have hnotCandidateTarget : ¬C i ⊆ C z := by
        intro hback
        exact hbelow i hi (Set.Subset.antisymm hback htargetCandidate)
      obtain ⟨N, hN⟩ := hD z stream hP (C i)
      refine ⟨N, ?_⟩
      intro t ht hcandidate
      have hcorrect := (hN t ht).mp hcandidate.2.2
      exact hnotCandidateTarget hcorrect
    · obtain ⟨x, hxTarget, hxnotCandidate⟩ :=
        Set.not_subset.mp htargetCandidate
      obtain ⟨N, hN⟩ :=
        GenLimit.Generic.eventually_mem_sample_of_presents hP hxTarget
      refine ⟨N, ?_⟩
      intro t ht hcandidate
      have hxSample : x ∈ GenLimit.Generic.sample stream t := hN t ht
      have hxSequence :
          x ∈ GenLimit.Generic.sequenceSample
            (fun r : Fin t => stream r) := by
        simpa [GenLimit.Generic.sequenceSample_prefix] using hxSample
      exact hxnotCandidate (hcandidate.2.1 hxSequence)
  obtain ⟨Nlower, hNlower⟩ :=
    GenLimit.Angluin.eventually_all_lt hpointwise
  obtain ⟨Ntarget, hNtarget⟩ := hD z stream hP (C k)
  refine ⟨k, hk, ?_⟩
  refine ⟨max (max k Nlower) Ntarget, ?_⟩
  intro t ht
  have hkt : k ≤ t :=
    le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_left _ _) ht)
  have hlower : Nlower ≤ t :=
    le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_left _ _) ht)
  have htarget : Ntarget ≤ t := le_trans (Nat.le_max_right _ _) ht
  have hsampleTarget :
      (↑(GenLimit.Generic.sequenceSample
        (fun r : Fin t => stream r)) : Set α) ⊆ C k := by
    rw [GenLimit.Generic.sequenceSample_prefix, hk]
    intro x hx
    exact GenLimit.Generic.mem_language_of_mem_sample_of_presents hP hx
  have hdetectorTarget :
      OracleTree.eval (C k)
        (D t (fun r : Fin t => stream r)) = true := by
    apply (hNtarget t htarget).mpr
    rw [hk]
  have hkCandidate :
      DetectorCandidate C D (fun r : Fin t => stream r) k :=
    ⟨hkt, hsampleTarget, hdetectorTarget⟩
  have hexists : ∃ i,
      DetectorCandidate C D (fun r : Fin t => stream r) i :=
    ⟨k, hkCandidate⟩
  let j := identifierFromDetector C D t (fun r : Fin t => stream r)
  have hjCandidate :
      DetectorCandidate C D (fun r : Fin t => stream r) j :=
    identifierFromDetector_candidate hexists
  have hjle : j ≤ k := identifierFromDetector_le_of_candidate hkCandidate
  have hjnotlt : ¬j < k := by
    intro hjlt
    exact hNlower t hlower j hjlt hjCandidate
  exact Nat.le_antisymm hjle (Nat.not_lt.mp hjnotlt)

/-- Theorem 2.1.  A nonempty countable domain supplies the fixed enumeration
used by Algorithm 1; Algorithm 2 does not need the enumeration. -/
theorem theorem_2_1
    [Nonempty α] [Countable α]
    (C : GenLimit.Generic.LanguageFamily α) :
    HallucinationDetectable C ↔ IdentifiableInLimit C := by
  constructor
  · exact lemma_3_2_detection_implies_identification C
  · intro hID
    obtain ⟨enumerate, henumerate⟩ := exists_surjective_nat α
    exact lemma_3_1_identification_implies_detection
      C enumerate henumerate hID

end GenLimit.HallucinationDetection
