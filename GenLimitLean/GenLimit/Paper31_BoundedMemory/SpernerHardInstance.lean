import GenLimit.Paper31_BoundedMemory.ZeroDensityPartition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

/-!
# The Sperner hard instance for memoryless upper density

Source: Jon Kleinberg, Anay Mehrotra, Amin Saberi, and Grigoris Velegkas,
*On Language Generation in the Limit with Bounded Memory*,
arXiv:2605.30324v1, Fact 4.5 and Lemma 4.7.

For `n = k - 1`, the source takes all
`r = ⌊n/2⌋`-subsets of `[n]`.  There are
`N = Nat.choose n r` such signatures.  It partitions the target in
round-robin order into `N` infinite cells of exact upper density `1/N`, then
makes language `j` the union of precisely the cells whose signatures contain
`j`.

This module formalizes that literal construction.  The middle layer is
enumerated by `Finset.equivFin`; no form of Sperner's theorem is postulated.
The only combinatorial fact used in the forcing argument is proved directly:
two middle-layer signatures related by inclusion are equal.
-/

namespace GenLimit.BoundedMemory

open Filter
open scoped Topology
open GenLimit.KleinbergWei

/-! ## A uniform round-robin partition -/

/-- The canonical ordering of the countably infinite target `ℕ`. -/
def spernerTargetOrder : OrderedLanguage where
  carrier := Set.univ
  enumeration := id
  enumeration_injective := fun _ _ h => h
  range_enumeration := by
    ext x
    simp

/-- Round-robin cell `i` among `N` cells. -/
def roundRobinPiece {N : ℕ} (i : Fin N) : Set ℕ :=
  {x | x % N = i.1}

@[simp] theorem mem_roundRobinPiece_iff
    {N : ℕ} (i : Fin N) (x : ℕ) :
    x ∈ roundRobinPiece i ↔ x % N = i.1 :=
  Iff.rfl

theorem roundRobinPieces_pairwiseDisjoint (N : ℕ) :
    ∀ i j : Fin N, i ≠ j →
      Disjoint (roundRobinPiece i) (roundRobinPiece j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  apply hij
  apply Fin.ext
  exact hxi.symm.trans hxj

theorem roundRobinPieces_cover {N : ℕ} (hN : 0 < N) :
    (⋃ i : Fin N, roundRobinPiece i) = (Set.univ : Set ℕ) := by
  apply Set.eq_univ_of_forall
  intro x
  let i : Fin N := ⟨x % N, Nat.mod_lt _ hN⟩
  exact Set.mem_iUnion.mpr ⟨i, rfl⟩

theorem roundRobinPiece_infinite
    {N : ℕ} (hN : 0 < N) (i : Fin N) :
    (roundRobinPiece i).Infinite := by
  let f : ℕ → ℕ := fun q => N * q + i.1
  have hf : Function.Injective f := by
    intro q s h
    have hmul : N * q = N * s := Nat.add_right_cancel h
    exact Nat.eq_of_mul_eq_mul_left hN hmul
  apply (Set.infinite_range_of_injective hf).mono
  rintro x ⟨q, rfl⟩
  exact blockNumber_residue N q i

theorem spernerTarget_prefixCount_roundRobin_eq_filter
    {N : ℕ} (i : Fin N) (n : ℕ) :
    spernerTargetOrder.prefixCount (roundRobinPiece i) n =
      ((Finset.range n).filter fun x => x % N = i.1).card := by
  classical
  unfold OrderedLanguage.prefixCount
  apply congrArg Finset.card
  ext x
  simp [spernerTargetOrder, roundRobinPiece]

theorem prefixCount_roundRobin_lower
    {N : ℕ} (hN : 0 < N) (i : Fin N) (n : ℕ) :
    n / N ≤ spernerTargetOrder.prefixCount (roundRobinPiece i) n := by
  classical
  rw [spernerTarget_prefixCount_roundRobin_eq_filter]
  let source : Finset ℕ :=
    (Finset.range (n / N)).image fun q => N * q + i.1
  have hsourceCard : source.card = n / N := by
    dsimp [source]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro q _ s _ h
      have hmul : N * q = N * s := Nat.add_right_cancel h
      exact Nat.eq_of_mul_eq_mul_left hN hmul
  rw [← hsourceCard]
  apply Finset.card_le_card
  intro x hx
  simp only [source, Finset.mem_image] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  simp only [Finset.mem_filter, Finset.mem_range] at hq ⊢
  constructor
  · have hqN : N * (q + 1) ≤ N * (n / N) :=
      Nat.mul_le_mul_left N (Nat.succ_le_of_lt hq)
    have hdiv : N * (n / N) ≤ n := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self n N
    have hi : N * q + i.1 < N * (q + 1) := by
      nlinarith [i.2]
    exact hi.trans_le (hqN.trans hdiv)
  · exact blockNumber_residue N q i

theorem prefixCount_roundRobin_upper
    {N : ℕ} (hN : 0 < N) (i : Fin N) (n : ℕ) :
    spernerTargetOrder.prefixCount (roundRobinPiece i) n ≤ n / N + 1 := by
  classical
  rw [spernerTarget_prefixCount_roundRobin_eq_filter]
  let envelope : Finset ℕ :=
    (Finset.range (n / N + 1)).image fun q => N * q + i.1
  have henvelopeCard : envelope.card = n / N + 1 := by
    dsimp [envelope]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro q _ s _ h
      have hmul : N * q = N * s := Nat.add_right_cancel h
      exact Nat.eq_of_mul_eq_mul_left hN hmul
  rw [← henvelopeCard]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx
  simp only [envelope, Finset.mem_image, Finset.mem_range]
  refine ⟨x / N, ?_, ?_⟩
  · exact Nat.lt_succ_of_le (Nat.div_le_div_right hx.1.le)
  · have hdecomp := Nat.mod_add_div x N
    rw [hx.2] at hdecomp
    omega

theorem prefixRatio_roundRobin_bounds
    {N : ℕ} (hN : 0 < N) (i : Fin N)
    {n : ℕ} (hn : 0 < n) :
    (1 / (N : ℝ)) - 1 / n ≤
        spernerTargetOrder.prefixRatio (roundRobinPiece i) n ∧
      spernerTargetOrder.prefixRatio (roundRobinPiece i) n ≤
        (1 / (N : ℝ)) + 1 / n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  rw [OrderedLanguage.prefixRatio, if_neg hn0]
  have hcountLower :=
    prefixCount_roundRobin_lower hN i n
  have hcountUpper :=
    prefixCount_roundRobin_upper hN i n
  have hmulLower : N * (n / N) ≤ n := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self n N
  have hmod := Nat.mod_lt n hN
  have hdecomp := Nat.mod_add_div n N
  have hmulUpper : n < N * (n / N + 1) := by
    calc
      n = n % N + N * (n / N) := hdecomp.symm
      _ <
          N + N * (n / N) :=
        Nat.add_lt_add_right hmod _
      _ = N * (n / N + 1) := by
        simp [Nat.mul_add, Nat.add_comm]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · calc
      (1 / (N : ℝ)) - 1 / n ≤
          ((n / N : ℕ) : ℝ) / n := by
            rw [sub_le_iff_le_add, ← add_div,
              div_le_div_iff₀ hNR hnR]
            norm_num
            exact_mod_cast
              (by simpa [Nat.mul_comm] using hmulUpper.le)
      _ ≤
          (spernerTargetOrder.prefixCount
            (roundRobinPiece i) n : ℝ) / n :=
        div_le_div_of_nonneg_right
          (by exact_mod_cast hcountLower) hnR.le
  · calc
      (spernerTargetOrder.prefixCount
          (roundRobinPiece i) n : ℝ) / n ≤
          (((n / N : ℕ) : ℝ) + 1) / n :=
        div_le_div_of_nonneg_right
          (by exact_mod_cast hcountUpper) hnR.le
      _ = ((n / N : ℕ) : ℝ) / n + 1 / n := by
        rw [add_div]
      _ ≤ 1 / (N : ℝ) + 1 / n := by
        apply add_le_add_right
        rw [div_le_div_iff₀ hnR hNR]
        norm_num
        exact_mod_cast
          (by simpa [Nat.mul_comm] using hmulLower)

theorem tendsto_prefixRatio_roundRobin
    {N : ℕ} (hN : 0 < N) (i : Fin N) :
    Tendsto
      (spernerTargetOrder.prefixRatio (roundRobinPiece i))
      atTop (𝓝 (1 / (N : ℝ))) := by
  have hrecip :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have herror :
      Tendsto
        (fun n : ℕ =>
          spernerTargetOrder.prefixRatio (roundRobinPiece i) n -
            (1 / (N : ℝ)))
        atTop (𝓝 0) := by
    have hneg :
        Tendsto (fun n : ℕ => -((1 : ℝ) / n))
          atTop (𝓝 0) := by
      simpa using hrecip.neg
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hneg hrecip
    · filter_upwards [eventually_gt_atTop 0] with n hn
      linarith [prefixRatio_roundRobin_bounds hN i hn |>.1]
    · filter_upwards [eventually_gt_atTop 0] with n hn
      linarith [prefixRatio_roundRobin_bounds hN i hn |>.2]
  have hsum :
      Tendsto
        (fun n : ℕ =>
          (1 / (N : ℝ)) +
            (spernerTargetOrder.prefixRatio (roundRobinPiece i) n -
              (1 / (N : ℝ))))
        atTop (𝓝 ((1 / (N : ℝ)) + 0)) :=
    tendsto_const_nhds.add herror
  convert hsum using 1
  · funext n
    ring
  · simp

theorem roundRobinPiece_upperDensity
    {N : ℕ} (hN : 0 < N) (i : Fin N) :
    spernerTargetOrder.upperDensity (roundRobinPiece i) =
      1 / (N : ℝ) :=
  (tendsto_prefixRatio_roundRobin hN i).limsup_eq

/-! ## Enumerating the middle layer of the Boolean lattice -/

/-- The middle layer of the Boolean lattice on `Fin n`. -/
def middleLayer (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard (n / 2)

@[simp] theorem middleLayer_card (n : ℕ) :
    (middleLayer n).card = Nat.choose n (n / 2) := by
  simp [middleLayer, Finset.card_powersetCard]

theorem middleWidth_pos (n : ℕ) :
    0 < Nat.choose n (n / 2) :=
  Nat.choose_pos (Nat.div_le_self n 2)

/-- The source's list `S₁,...,S_N` of all middle-layer subsets. -/
noncomputable def middleSignature (n : ℕ) :
    Fin (Nat.choose n (n / 2)) → Finset (Fin n) :=
  fun i =>
    (((middleLayer n).equivFinOfCardEq (middleLayer_card n)).symm i).1

theorem middleSignature_mem (n : ℕ)
    (i : Fin (Nat.choose n (n / 2))) :
    middleSignature n i ∈ middleLayer n :=
  (((middleLayer n).equivFinOfCardEq
    (middleLayer_card n)).symm i).2

theorem middleSignature_card (n : ℕ)
    (i : Fin (Nat.choose n (n / 2))) :
    (middleSignature n i).card = n / 2 := by
  exact (Finset.mem_powersetCard.mp (middleSignature_mem n i)).2

theorem middleSignature_injective (n : ℕ) :
    Function.Injective (middleSignature n) := by
  intro i j h
  apply
    ((middleLayer n).equivFinOfCardEq
      (middleLayer_card n)).symm.injective
  exact Subtype.ext h

theorem middleSignature_surjective
    (n : ℕ) {S : Finset (Fin n)} (hS : S.card = n / 2) :
    ∃ i, middleSignature n i = S := by
  have hmem : S ∈ middleLayer n := by
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hS⟩
  let x : middleLayer n := ⟨S, hmem⟩
  let i :=
    (middleLayer n).equivFinOfCardEq (middleLayer_card n) x
  refine ⟨i, ?_⟩
  change
    (((middleLayer n).equivFinOfCardEq
      (middleLayer_card n)).symm i).1 = S
  simp [i, x]

/-- The middle layer is an antichain: inclusion between two enumerated
middle signatures forces equality of their indices. -/
theorem middleSignature_eq_of_subset
    (n : ℕ) {i j : Fin (Nat.choose n (n / 2))}
    (hsubset : middleSignature n i ⊆ middleSignature n j) :
    i = j := by
  apply middleSignature_injective n
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [middleSignature_card, middleSignature_card]

theorem exists_middleSignature_not_mem
    {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    ∃ i : Fin (Nat.choose n (n / 2)),
      j ∉ middleSignature n i := by
  have hhalf : n / 2 ≤ (Finset.univ.erase j).card := by
    simp
    omega
  obtain ⟨S, hSsub, hScard⟩ :=
    Finset.exists_subset_card_eq hhalf
  obtain ⟨i, hi⟩ :=
    middleSignature_surjective n hScard
  refine ⟨i, ?_⟩
  rw [hi]
  exact fun hj => (Finset.mem_erase.mp (hSsub hj)).1 rfl

theorem exists_middleSignature_mem_not_mem
    {n : ℕ} (hn : 2 ≤ n) {j ℓ : Fin n} (hjl : j ≠ ℓ) :
    ∃ i : Fin (Nat.choose n (n / 2)),
      j ∈ middleSignature n i ∧
        ℓ ∉ middleSignature n i := by
  let base : Finset (Fin n) := (Finset.univ.erase j).erase ℓ
  have hbaseCard : base.card = n - 2 := by
    simp [base, hjl.symm]
    omega
  have hhalfPos : 1 ≤ n / 2 := by omega
  have hchoose : n / 2 - 1 ≤ base.card := by
    rw [hbaseCard]
    omega
  obtain ⟨T, hTsub, hTcard⟩ :=
    Finset.exists_subset_card_eq hchoose
  have hjT : j ∉ T := by
    intro hj
    have := hTsub hj
    simp [base] at this
  have hℓT : ℓ ∉ T := by
    intro hℓ
    have := hTsub hℓ
    simp [base] at this
  let S := insert j T
  have hScard : S.card = n / 2 := by
    dsimp [S]
    rw [Finset.card_insert_of_notMem hjT, hTcard]
    omega
  obtain ⟨i, hi⟩ :=
    middleSignature_surjective n hScard
  refine ⟨i, ?_, ?_⟩
  · rw [hi]
    simp [S]
  · rw [hi]
    simp [S, hjl.symm, hℓT]

/-! ## The source's hard languages -/

/-- Language `L_j`: the union of round-robin cells whose middle signature
contains `j`. -/
def spernerHardLanguage (n : ℕ) (j : Fin n) : Set ℕ :=
  ⋃ i : Fin (Nat.choose n (n / 2)),
    if j ∈ middleSignature n i then roundRobinPiece i else ∅

theorem mem_spernerHardLanguage_iff
    (n : ℕ) (j : Fin n) (x : ℕ) :
    x ∈ spernerHardLanguage n j ↔
      ∃ i : Fin (Nat.choose n (n / 2)),
        x ∈ roundRobinPiece i ∧ j ∈ middleSignature n i := by
  constructor
  · intro hx
    simp only [spernerHardLanguage, Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    by_cases hji : j ∈ middleSignature n i
    · exact ⟨i, by simpa [hji] using hi, hji⟩
    · simp [hji] at hi
  · rintro ⟨i, hxi, hji⟩
    apply Set.mem_iUnion.mpr
    exact ⟨i, by simpa [hji] using hxi⟩

theorem roundRobinPiece_subset_hardLanguage
    (n : ℕ) (j : Fin n)
    (i : Fin (Nat.choose n (n / 2)))
    (hji : j ∈ middleSignature n i) :
    roundRobinPiece i ⊆ spernerHardLanguage n j := by
  intro x hx
  exact (mem_spernerHardLanguage_iff n j x).2 ⟨i, hx, hji⟩

theorem spernerHardLanguage_infinite
    {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    (spernerHardLanguage n j).Infinite := by
  let ℓ : Fin n :=
    if hj : j.1 = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
  have hjℓ : j ≠ ℓ := by
    intro h
    have hval := congrArg Fin.val h
    by_cases hj : j.1 = 0
    · have : ℓ.1 = 1 := by simp [ℓ, hj]
      omega
    · have : ℓ.1 = 0 := by simp [ℓ, hj]
      omega
  obtain ⟨i, hji, -⟩ :=
    exists_middleSignature_mem_not_mem hn hjℓ
  exact (roundRobinPiece_infinite (middleWidth_pos n) i).mono
    (roundRobinPiece_subset_hardLanguage n j i hji)

theorem spernerHardLanguage_ne_univ
    {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    spernerHardLanguage n j ≠ (Set.univ : Set ℕ) := by
  obtain ⟨i, hji⟩ := exists_middleSignature_not_mem hn j
  let x := i.1
  have hxi : x ∈ roundRobinPiece i := by
    exact Nat.mod_eq_of_lt i.2
  intro heq
  have hxL : x ∈ spernerHardLanguage n j := by simp [heq]
  obtain ⟨q, hxq, hjq⟩ :=
    (mem_spernerHardLanguage_iff n j x).1 hxL
  have hqi : q = i := by
    apply Fin.ext
    exact hxq.symm.trans hxi
  exact hji (hqi ▸ hjq)

theorem spernerHardLanguage_injective
    {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (spernerHardLanguage n) := by
  intro j ℓ heq
  by_contra hjℓ
  obtain ⟨i, hji, hℓi⟩ :=
    exists_middleSignature_mem_not_mem hn hjℓ
  let x := i.1
  have hxi : x ∈ roundRobinPiece i :=
    Nat.mod_eq_of_lt i.2
  have hxj : x ∈ spernerHardLanguage n j :=
    roundRobinPiece_subset_hardLanguage n j i hji hxi
  have hxℓ : x ∈ spernerHardLanguage n ℓ := heq ▸ hxj
  obtain ⟨q, hxq, hℓq⟩ :=
    (mem_spernerHardLanguage_iff n ℓ x).1 hxℓ
  have hqi : q = i := by
    apply Fin.ext
    exact hxq.symm.trans hxi
  exact hℓi (hqi ▸ hℓq)

/-- The `n+1`-member hard family: the target followed by `L₁,...,L_n`. -/
noncomputable def spernerHardFamily (n : ℕ) :
    Fin (n + 1) → Set ℕ :=
  Fin.cases Set.univ (spernerHardLanguage n)

@[simp] theorem spernerHardFamily_zero (n : ℕ) :
    spernerHardFamily n 0 = (Set.univ : Set ℕ) := by
  simp [spernerHardFamily]

@[simp] theorem spernerHardFamily_succ
    (n : ℕ) (j : Fin n) :
    spernerHardFamily n j.succ = spernerHardLanguage n j := by
  simp [spernerHardFamily]

theorem spernerHardFamily_injective
    {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (spernerHardFamily n) := by
  intro a
  refine Fin.cases ?_ (fun j => ?_) a
  · intro b
    refine Fin.cases (fun _ => rfl) (fun ℓ hab => ?_) b
    exfalso
    exact spernerHardLanguage_ne_univ hn ℓ
      (by simpa using hab.symm)
  · intro b
    refine Fin.cases ?_ (fun ℓ hab => ?_) b
    · intro hab
      exfalso
      exact spernerHardLanguage_ne_univ hn j
        (by simpa using hab)
    · apply congrArg Fin.succ
      apply spernerHardLanguage_injective hn
      simpa using hab

theorem spernerHardFamily_infinite
    {n : ℕ} (hn : 2 ≤ n) :
    ∀ a, (spernerHardFamily n a).Infinite := by
  intro a
  refine Fin.cases Set.infinite_univ (fun j => ?_) a
  exact spernerHardLanguage_infinite hn j

/-! ## The forcing intersection -/

theorem mem_hardLanguage_iff_signature
    {n : ℕ} (j : Fin n) (x : ℕ) :
    x ∈ spernerHardLanguage n j ↔
      j ∈ middleSignature n
        ⟨x % Nat.choose n (n / 2),
          Nat.mod_lt _ (middleWidth_pos n)⟩ := by
  let owner : Fin (Nat.choose n (n / 2)) :=
    ⟨x % Nat.choose n (n / 2),
      Nat.mod_lt _ (middleWidth_pos n)⟩
  constructor
  · intro hx
    obtain ⟨i, hxi, hji⟩ :=
      (mem_spernerHardLanguage_iff n j x).1 hx
    have hi : i = owner := by
      apply Fin.ext
      exact hxi.symm
    have : j ∈ middleSignature n owner := by
      rw [← hi]
      exact hji
    simpa [owner] using this
  · intro hj
    exact (mem_spernerHardLanguage_iff n j x).2
      ⟨owner, rfl, by simpa [owner] using hj⟩

theorem hardIntersection_subset_piece
    {n : ℕ} (i : Fin (Nat.choose n (n / 2))) :
    {x | ∀ j, j ∈ middleSignature n i →
        x ∈ spernerHardLanguage n j} ⊆
      roundRobinPiece i := by
  intro x hx
  let owner : Fin (Nat.choose n (n / 2)) :=
    ⟨x % Nat.choose n (n / 2),
      Nat.mod_lt _ (middleWidth_pos n)⟩
  have hsubset :
      middleSignature n i ⊆ middleSignature n owner := by
    intro j hji
    exact (mem_hardLanguage_iff_signature j x).1 (hx j hji)
  have hiowner : i = owner :=
    middleSignature_eq_of_subset n hsubset
  change x % Nat.choose n (n / 2) = i.1
  exact congrArg Fin.val hiowner.symm

/-! ## Eventual forcing for any successful memoryless generator -/

def spernerTotalBadInputs
    (n : ℕ) (G : MemorylessSetGenerator ℕ) : Set ℕ :=
  ⋃ a : Fin (n + 1),
    densityBadInputs G (spernerHardFamily n a)

theorem spernerTotalBadInputs_finite
    {n : ℕ} (hn : 2 ≤ n)
    (G : MemorylessSetGenerator ℕ)
    (hG : IsFinitelyRepeatingMemorylessGenerator
      G (Set.range (spernerHardFamily n))) :
    (spernerTotalBadInputs n G).Finite := by
  unfold spernerTotalBadInputs
  apply Set.finite_iUnion
  intro a
  apply densityBadInputs_finite (spernerHardFamily_infinite hn a)
  intro stream hP hInjective
  exact hG (spernerHardFamily n a) ⟨a, rfl⟩ stream hP
    (injective_finitelyRepeating hInjective)

theorem output_subset_owner_piece
    {n : ℕ} (G : MemorylessSetGenerator ℕ)
    {x : ℕ} (hx : x ∉ spernerTotalBadInputs n G) :
    G x ⊆ roundRobinPiece
      ⟨x % Nat.choose n (n / 2),
        Nat.mod_lt _ (middleWidth_pos n)⟩ := by
  let owner : Fin (Nat.choose n (n / 2)) :=
    ⟨x % Nat.choose n (n / 2),
      Nat.mod_lt _ (middleWidth_pos n)⟩
  change G x ⊆ roundRobinPiece owner
  intro y hy
  apply hardIntersection_subset_piece owner
  intro j hj
  have hxLj : x ∈ spernerHardLanguage n j :=
    (mem_hardLanguage_iff_signature j x).2
      (by simpa [owner] using hj)
  have hxNotBad :
      x ∉ densityBadInputs G (spernerHardLanguage n j) := by
    intro hbad
    apply hx
    apply Set.mem_iUnion.mpr
    exact ⟨j.succ, by simpa using hbad⟩
  have hsubset : G x ⊆ spernerHardLanguage n j := by
    by_contra hnot
    exact hxNotBad ⟨hxLj, hnot⟩
  exact hsubset hy

theorem eventually_sperner_upperDensity_bound
    {n : ℕ} (hn : 2 ≤ n)
    (G : MemorylessSetGenerator ℕ)
    (hG : IsFinitelyRepeatingMemorylessGenerator
      G (Set.range (spernerHardFamily n)))
    (stream : ℕ → ℕ)
    (_hP : GenLimit.Generic.Presents stream
      spernerTargetOrder.carrier)
    (hInjective : Function.Injective stream) :
    ∃ T, ∀ t, T ≤ t →
      spernerTargetOrder.upperDensity (G (stream t)) ≤
        1 / (Nat.choose n (n / 2) : ℝ) := by
  obtain ⟨T, hAvoid⟩ :=
    finitelyRepeating_avoids_finite_set
      (injective_finitelyRepeating hInjective)
      (spernerTotalBadInputs_finite hn G hG)
  refine ⟨T, ?_⟩
  intro t ht
  let owner : Fin (Nat.choose n (n / 2)) :=
    ⟨stream t % Nat.choose n (n / 2),
      Nat.mod_lt _ (middleWidth_pos n)⟩
  have hsubset : G (stream t) ⊆ roundRobinPiece owner :=
    output_subset_owner_piece G (by simpa [owner] using hAvoid t ht)
  exact (orderedUpperDensity_mono spernerTargetOrder hsubset).trans_eq
    (roundRobinPiece_upperDensity (middleWidth_pos n) owner)

/-! ## The `k = 2` endpoint -/

def twoHardFamily : Fin 2 → Set ℕ
  | ⟨0, _⟩ => Set.univ
  | ⟨_ + 1, _⟩ => roundRobinPiece (1 : Fin 2)

@[simp] theorem twoHardFamily_zero :
    twoHardFamily 0 = (Set.univ : Set ℕ) := rfl

@[simp] theorem twoHardFamily_one :
    twoHardFamily 1 = roundRobinPiece (1 : Fin 2) := rfl

theorem twoHardFamily_injective :
    Function.Injective twoHardFamily := by
  have hne :
      (Set.univ : Set ℕ) ≠ roundRobinPiece (1 : Fin 2) := by
    intro h
    have hzero : 0 ∈ roundRobinPiece (1 : Fin 2) := by
      rw [← h]
      trivial
    norm_num [roundRobinPiece] at hzero
  intro i j h
  fin_cases i <;> fin_cases j
  · rfl
  · exact (hne h).elim
  · exact (hne h.symm).elim
  · rfl

theorem twoHardFamily_infinite :
    ∀ i, (twoHardFamily i).Infinite := by
  intro i
  fin_cases i
  · exact Set.infinite_univ
  · exact roundRobinPiece_infinite (by omega) 1

theorem orderedUpperDensity_le_one
    (K : OrderedLanguage) (A : Set ℕ) :
    K.upperDensity A ≤ 1 :=
  K.upperDensity_le_one A

/-! ## Lemma 4.7 -/

/-- Lemma 4.7 with its literal quantifier order and upper-density value.

The family is represented by an injective `Fin k` indexing, which formally
records that the collection has exactly `k` distinct infinite languages.
Index `0` is the target. -/
theorem lemma_4_7_sperner_hard_instance
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ (K : OrderedLanguage) (langs : Fin k → Set ℕ)
        (target : Fin k),
      Function.Injective langs ∧
      (∀ i, (langs i).Infinite) ∧
      langs target = K.carrier ∧
      ∀ G : MemorylessSetGenerator ℕ,
        IsFinitelyRepeatingMemorylessGenerator G (Set.range langs) →
        ∀ stream : ℕ → ℕ,
          GenLimit.Generic.Presents stream K.carrier →
          Function.Injective stream →
          ∃ T, ∀ t, T ≤ t →
            K.upperDensity (G (stream t)) ≤
              1 / (Nat.choose (k - 1) ((k - 1) / 2) : ℝ) := by
  cases k with
  | zero => omega
  | succ n =>
      by_cases hn : n = 1
      · subst n
        refine
          ⟨spernerTargetOrder, twoHardFamily, 0,
            twoHardFamily_injective, twoHardFamily_infinite, rfl, ?_⟩
        intro G hG stream hP hInjective
        refine ⟨0, ?_⟩
        intro t ht
        simpa using orderedUpperDensity_le_one
          spernerTargetOrder (G (stream t))
      · have hn2 : 2 ≤ n := by omega
        refine
          ⟨spernerTargetOrder, spernerHardFamily n, 0,
            spernerHardFamily_injective hn2,
            spernerHardFamily_infinite hn2, rfl, ?_⟩
        intro G hG stream hP hInjective
        simpa using
          eventually_sperner_upperDensity_bound
            hn2 G hG stream hP hInjective

end GenLimit.BoundedMemory
