import GenLimit.Paper31_BoundedMemory.FinitelyRepeating
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Theorem 3.2: element- and index-output separations

Source: Kleinberg--Mehrotra--Saberi--Velegkas,
*On Language Generation in the Limit with Bounded Memory*,
arXiv:2605.30324v1, Theorem 3.2 and Section 3.3.

The constructions below retain the source's actual adversarial streams.
They are exact presentations and every point occurs only finitely often.
-/

namespace GenLimit.BoundedMemory

variable {α : Type*}

/-! ## Stream combinators -/

/-- A fixed repetition-free enumeration of an infinite subset of a
countable example space. -/
noncomputable def infiniteEnumeration [Countable α]
    (S : Set α) (hS : S.Infinite) : ℕ → α := by
  letI : Infinite S := Set.Infinite.to_subtype hS
  let e : ℕ ≃ S :=
    (@Denumerable.eqv S (Classical.choice (nonempty_denumerable S))).symm
  exact fun n => (e n).1

theorem infiniteEnumeration_mem [Countable α]
    (S : Set α) (hS : S.Infinite) (n : ℕ) :
    infiniteEnumeration S hS n ∈ S := by
  letI : Infinite S := Set.Infinite.to_subtype hS
  let e : ℕ ≃ S :=
    (@Denumerable.eqv S (Classical.choice (nonempty_denumerable S))).symm
  exact (e n).2

theorem infiniteEnumeration_injective [Countable α]
    (S : Set α) (hS : S.Infinite) :
    Function.Injective (infiniteEnumeration S hS) := by
  letI : Infinite S := Set.Infinite.to_subtype hS
  let e : ℕ ≃ S :=
    (@Denumerable.eqv S (Classical.choice (nonempty_denumerable S))).symm
  intro m n hmn
  apply e.injective
  exact Subtype.ext hmn

theorem infiniteEnumeration_presents [Countable α]
    (S : Set α) (hS : S.Infinite) :
    GenLimit.Generic.Presents (infiniteEnumeration S hS) S := by
  apply Set.Subset.antisymm
  · rintro x ⟨n, rfl⟩
    exact infiniteEnumeration_mem S hS n
  · intro x hx
    letI : Infinite S := Set.Infinite.to_subtype hS
    let e : ℕ ≃ S :=
      (@Denumerable.eqv S (Classical.choice (nonempty_denumerable S))).symm
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    simp [infiniteEnumeration, e]

theorem injective_finitelyRepeating
    {stream : ℕ → α} (hstream : Function.Injective stream) :
    FinitelyRepeating stream := by
  intro x
  have hpre :
      (stream ⁻¹' ({x} : Set α)).Finite :=
    Set.Finite.preimage hstream.injOn (Set.finite_singleton x)
  simpa only [Set.preimage_setOf_eq, Set.mem_singleton_iff] using hpre

/-- Alternate between two streams. -/
def interleave (left right : ℕ → α) (t : ℕ) : α :=
  if t % 2 = 0 then left (t / 2) else right (t / 2)

@[simp]
theorem interleave_even (left right : ℕ → α) (n : ℕ) :
    interleave left right (2 * n) = left n := by
  simp [interleave]

@[simp]
theorem interleave_odd (left right : ℕ → α) (n : ℕ) :
    interleave left right (2 * n + 1) = right n := by
  rw [interleave]
  have hmod : (2 * n + 1) % 2 ≠ 0 := by omega
  rw [if_neg hmod]
  congr 1
  omega

theorem interleave_streamIn
    {left right : ℕ → α} {K : Set α}
    (hleft : GenLimit.Generic.StreamIn left K)
    (hright : GenLimit.Generic.StreamIn right K) :
    GenLimit.Generic.StreamIn (interleave left right) K := by
  rintro x ⟨t, rfl⟩
  by_cases ht : t % 2 = 0
  · exact hleft ⟨t / 2, by simp [interleave, ht]⟩
  · exact hright ⟨t / 2, by simp [interleave, ht]⟩

theorem interleave_presents_of_right
    {left right : ℕ → α} {K : Set α}
    (hleft : GenLimit.Generic.StreamIn left K)
    (hright : GenLimit.Generic.Presents right K) :
    GenLimit.Generic.Presents (interleave left right) K := by
  apply Set.Subset.antisymm
  · exact interleave_streamIn hleft
      (GenLimit.Generic.streamIn_of_presents hright)
  · intro x hx
    rw [← hright] at hx
    obtain ⟨n, rfl⟩ := hx
    exact ⟨2 * n + 1, interleave_odd left right n⟩

theorem interleave_finitelyRepeating
    {left right : ℕ → α}
    (hleft : FinitelyRepeating left)
    (hright : FinitelyRepeating right) :
    FinitelyRepeating (interleave left right) := by
  classical
  intro x
  have hEven :
      ((fun n => 2 * n) '' {n | left n = x}).Finite :=
    (hleft x).image _
  have hOdd :
      ((fun n => 2 * n + 1) '' {n | right n = x}).Finite :=
    (hright x).image _
  apply (hEven.union hOdd).subset
  intro t ht
  by_cases heven : t % 2 = 0
  · apply Set.mem_union_left
    refine ⟨t / 2, ?_, ?_⟩
    · simpa [interleave, heven] using ht
    · change 2 * (t / 2) = t
      have hdecomp := Nat.mod_add_div t 2
      omega
  · apply Set.mem_union_right
    have hmodlt : t % 2 < 2 := Nat.mod_lt t (by omega)
    have hodd : t % 2 = 1 := by omega
    refine ⟨t / 2, ?_, ?_⟩
    · simpa [interleave, heven] using ht
    · change 2 * (t / 2) + 1 = t
      have hdecomp := Nat.mod_add_div t 2
      omega

/-- Insert one distinguished first observation. -/
def prepend (head : α) (tail : ℕ → α) : ℕ → α
  | 0 => head
  | n + 1 => tail n

@[simp]
theorem prepend_zero (head : α) (tail : ℕ → α) :
    prepend head tail 0 = head := rfl

@[simp]
theorem prepend_succ (head : α) (tail : ℕ → α) (n : ℕ) :
    prepend head tail (n + 1) = tail n := rfl

theorem prepend_presents
    {head : α} {tail : ℕ → α} {K : Set α}
    (hhead : head ∈ K)
    (htail : GenLimit.Generic.Presents tail K) :
    GenLimit.Generic.Presents (prepend head tail) K := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    cases t with
    | zero => exact hhead
    | succ n =>
        rw [← htail]
        exact ⟨n, rfl⟩
  · intro x hx
    rw [← htail] at hx
    obtain ⟨n, rfl⟩ := hx
    exact ⟨n + 1, rfl⟩

theorem prepend_finitelyRepeating
    (head : α) {tail : ℕ → α} (htail : FinitelyRepeating tail) :
    FinitelyRepeating (prepend head tail) := by
  classical
  intro x
  have hSucc :
      ((fun n => n + 1) '' {n | tail n = x}).Finite :=
    (htail x).image _
  apply ((Set.finite_singleton 0).union hSucc).subset
  intro t ht
  cases t with
  | zero => exact Set.mem_union_left _ (Set.mem_singleton 0)
  | succ n =>
      apply Set.mem_union_right
      exact ⟨n, by simpa using ht, rfl⟩

/-! ## Element-based separation -/

abbrev MemorylessElementGenerator (α : Type*) := α → α

/-- The source's element-output validity after the current observation has
been added to the sample. -/
def ElementCorrectAt
    (G : MemorylessElementGenerator α) (K : Set α)
    (stream : ℕ → α) (t : ℕ) : Prop :=
  G (stream t) ∈ K ∧
    G (stream t) ∉ GenLimit.Generic.sample stream (t + 1)

def IsFinitelyRepeatingElementGeneratorOn
    (G : MemorylessElementGenerator α) (K : Set α) : Prop :=
  ∀ stream, GenLimit.Generic.Presents stream K →
    FinitelyRepeating stream →
      ∃ T, ∀ t, T ≤ t → ElementCorrectAt G K stream t

theorem element_bad_set_infinite_obstruction
    [Countable α]
    {G : MemorylessElementGenerator α} {K B : Set α}
    (hK : K.Infinite) (hBK : B ⊆ K) (hB : B.Infinite)
    (hbad : ∀ x, x ∈ B → G x ∉ K ∨ G x = x) :
    ¬IsFinitelyRepeatingElementGeneratorOn G K := by
  intro hgen
  let left := infiniteEnumeration B hB
  let right := infiniteEnumeration K hK
  let stream := interleave left right
  have hleftIn : GenLimit.Generic.StreamIn left K := by
    rintro x ⟨n, rfl⟩
    exact hBK (infiniteEnumeration_mem B hB n)
  have hP : GenLimit.Generic.Presents stream K :=
    interleave_presents_of_right hleftIn
      (infiniteEnumeration_presents K hK)
  have hRepeat : FinitelyRepeating stream :=
    interleave_finitelyRepeating
      (injective_finitelyRepeating
        (infiniteEnumeration_injective B hB))
      (injective_finitelyRepeating
        (infiniteEnumeration_injective K hK))
  obtain ⟨T, hT⟩ := hgen stream hP hRepeat
  let t := 2 * T
  have hcurrent : stream t = left T := by
    simp [stream, t]
  have hleftB : left T ∈ B :=
    infiniteEnumeration_mem B hB T
  rcases hbad (left T) hleftB with hout | hfixed
  · have hcorrect := hT t (by omega)
    unfold ElementCorrectAt at hcorrect
    rw [hcurrent] at hcorrect
    exact hout hcorrect.1
  · have hseen :
        G (stream t) ∈ GenLimit.Generic.sample stream (t + 1) := by
      have hcurrentSeen :
          stream t ∈ GenLimit.Generic.sample stream (t + 1) :=
        GenLimit.Generic.value_mem_sample (Nat.lt_succ_self t)
      rw [hcurrent] at hcurrentSeen
      simpa [hcurrent, hfixed] using hcurrentSeen
    exact (hT t (by omega)).2 hseen

/-- The infinite fiber used in the second branch of the paper's proof. -/
def goodFiber
    (G : MemorylessElementGenerator α) (K B : Set α) (y : α) : Set α :=
  {x | x ∈ K \ B ∧ G x = y}

theorem element_infinite_fiber_obstruction
    [Countable α]
    {G : MemorylessElementGenerator α} {K B : Set α}
    (hK : K.Infinite) {y : α} (hyK : y ∈ K)
    (hFiber : (goodFiber G K B y).Infinite) :
    ¬IsFinitelyRepeatingElementGeneratorOn G K := by
  intro hgen
  let A := goodFiber G K B y
  let a := infiniteEnumeration A hFiber
  let k := infiniteEnumeration K hK
  let tail := interleave a k
  let stream := prepend y tail
  have haIn : GenLimit.Generic.StreamIn a K := by
    rintro x ⟨n, rfl⟩
    exact (infiniteEnumeration_mem A hFiber n).1.1
  have hTailP : GenLimit.Generic.Presents tail K :=
    interleave_presents_of_right haIn
      (infiniteEnumeration_presents K hK)
  have hP : GenLimit.Generic.Presents stream K :=
    prepend_presents hyK hTailP
  have hTailRepeat : FinitelyRepeating tail :=
    interleave_finitelyRepeating
      (injective_finitelyRepeating
        (infiniteEnumeration_injective A hFiber))
      (injective_finitelyRepeating
        (infiniteEnumeration_injective K hK))
  have hRepeat : FinitelyRepeating stream :=
    prepend_finitelyRepeating y hTailRepeat
  obtain ⟨T, hT⟩ := hgen stream hP hRepeat
  let t := 2 * T + 1
  have hcurrent : stream t = a T := by
    simp [stream, tail, t]
  have hGa : G (a T) = y :=
    (infiniteEnumeration_mem A hFiber T).2
  have hySeen :
      G (stream t) ∈ GenLimit.Generic.sample stream (t + 1) := by
    rw [hcurrent, hGa]
    exact GenLimit.Generic.value_mem_sample (by omega : 0 < t + 1)
  exact (hT t (by omega)).2 hySeen

/-- Image of the good part of a language under an element generator. -/
def goodImage
    (G : MemorylessElementGenerator α) (K B : Set α) : Set α :=
  G '' (K \ B)

theorem goodImage_infinite_of_finite_fibers
    {G : MemorylessElementGenerator α} {K B : Set α}
    (hD : (K \ B).Infinite)
    (hFibers : ∀ y, (goodFiber G K B y).Finite) :
    (goodImage G K B).Infinite := by
  intro hImageFinite
  have hUnionFinite :
      (⋃ y ∈ goodImage G K B, goodFiber G K B y).Finite :=
    hImageFinite.biUnion (fun y _hy => hFibers y)
  apply hD
  apply hUnionFinite.subset
  intro x hx
  apply Set.mem_iUnion₂.mpr
  refine ⟨G x, ⟨x, hx, rfl⟩, ?_⟩
  exact ⟨hx, rfl⟩

noncomputable def chosenGoodPreimage
    [Countable α]
    (G : MemorylessElementGenerator α) (K B : Set α)
    (hImage : (goodImage G K B).Infinite) (n : ℕ) : α :=
  Classical.choose
    (infiniteEnumeration_mem (goodImage G K B) hImage n)

theorem chosenGoodPreimage_mem
    [Countable α]
    (G : MemorylessElementGenerator α) (K B : Set α)
    (hImage : (goodImage G K B).Infinite) (n : ℕ) :
    chosenGoodPreimage G K B hImage n ∈ K \ B :=
  (Classical.choose_spec
    (infiniteEnumeration_mem (goodImage G K B) hImage n)).1

theorem chosenGoodPreimage_image
    [Countable α]
    (G : MemorylessElementGenerator α) (K B : Set α)
    (hImage : (goodImage G K B).Infinite) (n : ℕ) :
    G (chosenGoodPreimage G K B hImage n) =
      infiniteEnumeration (goodImage G K B) hImage n :=
  (Classical.choose_spec
    (infiniteEnumeration_mem (goodImage G K B) hImage n)).2

theorem chosenGoodPreimage_injective
    [Countable α]
    (G : MemorylessElementGenerator α) (K B : Set α)
    (hImage : (goodImage G K B).Infinite) :
    Function.Injective (chosenGoodPreimage G K B hImage) := by
  intro m n hmn
  apply (infiniteEnumeration_injective (goodImage G K B) hImage)
  rw [← chosenGoodPreimage_image G K B hImage m,
    ← chosenGoodPreimage_image G K B hImage n, hmn]

theorem element_finite_fibers_obstruction
    [Countable α]
    {G : MemorylessElementGenerator α} {K B : Set α}
    (hK : K.Infinite) (hB : B.Finite)
    (hgood : ∀ x, x ∈ K \ B → G x ∈ K ∧ G x ≠ x)
    (hFibers : ∀ y, (goodFiber G K B y).Finite) :
    ¬IsFinitelyRepeatingElementGeneratorOn G K := by
  intro hgen
  have hD : (K \ B).Infinite := hK.diff hB
  have hImage : (goodImage G K B).Infinite :=
    goodImage_infinite_of_finite_fibers hD hFibers
  let a := chosenGoodPreimage G K B hImage
  let ga : ℕ → α := fun n => G (a n)
  let pair := interleave ga a
  let k := infiniteEnumeration K hK
  let stream := interleave pair k
  have haIn : GenLimit.Generic.StreamIn a K := by
    rintro x ⟨n, rfl⟩
    exact (chosenGoodPreimage_mem G K B hImage n).1
  have hgaIn : GenLimit.Generic.StreamIn ga K := by
    rintro x ⟨n, rfl⟩
    exact (hgood (a n)
      (chosenGoodPreimage_mem G K B hImage n)).1
  have hpairIn : GenLimit.Generic.StreamIn pair K :=
    interleave_streamIn hgaIn haIn
  have hP : GenLimit.Generic.Presents stream K :=
    interleave_presents_of_right hpairIn
      (infiniteEnumeration_presents K hK)
  have haInjective : Function.Injective a :=
    chosenGoodPreimage_injective G K B hImage
  have hgaInjective : Function.Injective ga := by
    intro m n hmn
    apply (infiniteEnumeration_injective (goodImage G K B) hImage)
    simpa [ga, a, chosenGoodPreimage_image] using hmn
  have hpairRepeat : FinitelyRepeating pair :=
    interleave_finitelyRepeating
      (injective_finitelyRepeating hgaInjective)
      (injective_finitelyRepeating haInjective)
  have hRepeat : FinitelyRepeating stream :=
    interleave_finitelyRepeating hpairRepeat
      (injective_finitelyRepeating
        (infiniteEnumeration_injective K hK))
  obtain ⟨T, hT⟩ := hgen stream hP hRepeat
  let t := 4 * T + 2
  have hcurrent : stream t = a T := by
    change interleave (interleave ga a) k (4 * T + 2) = a T
    have ht : 4 * T + 2 = 2 * (2 * T + 1) := by omega
    rw [ht, interleave_even, interleave_odd]
  have hprevious : stream (4 * T) = ga T := by
    change interleave (interleave ga a) k (4 * T) = ga T
    have ht : 4 * T = 2 * (2 * T) := by omega
    rw [ht, interleave_even, interleave_even]
  have hseen :
      G (stream t) ∈ GenLimit.Generic.sample stream (t + 1) := by
    rw [hcurrent]
    have : G (a T) = stream (4 * T) := by
      rw [hprevious]
    rw [this]
    exact GenLimit.Generic.value_mem_sample (by omega)
  exact (hT t (by omega)).2 hseen

/-- Element-output half of Theorem 3.2. -/
theorem theorem_3_2_element
    [Countable α]
    (K : Set α) (hK : K.Infinite)
    (G : MemorylessElementGenerator α) :
    ¬IsFinitelyRepeatingElementGeneratorOn G K := by
  let B : Set α := {x | x ∈ K ∧ (G x ∉ K ∨ G x = x)}
  by_cases hBInfinite : B.Infinite
  · exact element_bad_set_infinite_obstruction hK
      (fun _ hx => hx.1) hBInfinite (fun _ hx => hx.2)
  · have hBFinite : B.Finite := Set.not_infinite.mp hBInfinite
    have hgood : ∀ x, x ∈ K \ B → G x ∈ K ∧ G x ≠ x := by
      intro x hx
      have hxNot : ¬(G x ∉ K ∨ G x = x) := by
        intro h
        exact hx.2 ⟨hx.1, h⟩
      exact ⟨not_not.mp (not_or.mp hxNot).1,
        (not_or.mp hxNot).2⟩
    by_cases hFiber : ∃ y, (goodFiber G K B y).Infinite
    · obtain ⟨y, hy⟩ := hFiber
      have hyK : y ∈ K := by
        obtain ⟨x, hx⟩ := hy.nonempty
        rw [← hx.2]
        exact (hgood x hx.1).1
      exact element_infinite_fiber_obstruction hK hyK hy
    · have hFibers : ∀ y, (goodFiber G K B y).Finite := by
        intro y
        exact Set.not_infinite.mp (not_exists.mp hFiber y)
      exact element_finite_fibers_obstruction hK hBFinite hgood hFibers

/-! ## Index-based separation -/

abbrev MemorylessIndexGenerator (α ι : Type*) := α → ι

def IsFinitelyRepeatingIndexGenerator
    (G : MemorylessIndexGenerator α ι)
    (langs : ι → Set α) : Prop :=
  ∀ target, ∀ stream,
    GenLimit.Generic.Presents stream (langs target) →
      FinitelyRepeating stream →
        ∃ T, ∀ t, T ≤ t → langs (G (stream t)) ⊆ langs target

def indexLanguageZero : Set ℕ :=
  {n | n % 4 = 0 ∨ n % 4 = 1}

def indexLanguageOne : Set ℕ :=
  {n | n % 4 = 0 ∨ n % 4 = 2}

def indexLanguages : Fin 2 → Set ℕ
  | ⟨0, _⟩ => indexLanguageZero
  | ⟨1, _⟩ => indexLanguageOne

def commonMultiples : Set ℕ := {n | n % 4 = 0}

theorem commonMultiples_infinite : commonMultiples.Infinite := by
  apply (Set.infinite_range_of_injective
    (f := fun n : ℕ => 4 * n)
      (fun _ _ h => Nat.eq_of_mul_eq_mul_left (by omega) h)).mono
  rintro _ ⟨n, rfl⟩
  simp [commonMultiples]

theorem commonMultiples_subset_zero :
    commonMultiples ⊆ indexLanguageZero := by
  intro n hn
  exact Or.inl hn

theorem commonMultiples_subset_one :
    commonMultiples ⊆ indexLanguageOne := by
  intro n hn
  exact Or.inl hn

theorem indexLanguages_infinite :
    ∀ i, (indexLanguages i).Infinite := by
  intro i
  apply commonMultiples_infinite.mono
  fin_cases i
  · exact commonMultiples_subset_zero
  · exact commonMultiples_subset_one

theorem indexLanguageZero_not_subset_one :
    ¬indexLanguageZero ⊆ indexLanguageOne := by
  intro h
  have := h (show 1 ∈ indexLanguageZero by simp [indexLanguageZero])
  norm_num [indexLanguageOne] at this

theorem indexLanguageOne_not_subset_zero :
    ¬indexLanguageOne ⊆ indexLanguageZero := by
  intro h
  have := h (show 2 ∈ indexLanguageOne by simp [indexLanguageOne])
  norm_num [indexLanguageZero] at this

theorem index_fiber_obstruction
    {G : MemorylessIndexGenerator ℕ (Fin 2)} {i target : Fin 2}
    {A : Set ℕ} (hA : A.Infinite)
    (hACommon : A ⊆ commonMultiples)
    (hGi : ∀ x, x ∈ A → G x = i)
    (hWrong : ¬indexLanguages i ⊆ indexLanguages target) :
    ¬IsFinitelyRepeatingIndexGenerator G indexLanguages := by
  intro hgen
  let left := infiniteEnumeration A hA
  have hTargetInfinite : (indexLanguages target).Infinite := by
    exact commonMultiples_infinite.mono
      (by
        fin_cases target
        · exact commonMultiples_subset_zero
        · exact commonMultiples_subset_one)
  let right :=
    infiniteEnumeration (indexLanguages target) hTargetInfinite
  let stream := interleave left right
  have hleftIn :
      GenLimit.Generic.StreamIn left (indexLanguages target) := by
    rintro x ⟨n, rfl⟩
    have hxCommon :=
      hACommon (infiniteEnumeration_mem A hA n)
    fin_cases target
    · exact commonMultiples_subset_zero hxCommon
    · exact commonMultiples_subset_one hxCommon
  have hP : GenLimit.Generic.Presents stream (indexLanguages target) :=
    interleave_presents_of_right hleftIn
      (infiniteEnumeration_presents _ hTargetInfinite)
  have hRepeat : FinitelyRepeating stream :=
    interleave_finitelyRepeating
      (injective_finitelyRepeating
        (infiniteEnumeration_injective A hA))
      (injective_finitelyRepeating
        (infiniteEnumeration_injective _ hTargetInfinite))
  obtain ⟨T, hT⟩ := hgen target stream hP hRepeat
  have hcurrent : stream (2 * T) = left T := by
    simp [stream]
  have hindex : G (stream (2 * T)) = i := by
    rw [hcurrent]
    exact hGi (left T) (infiniteEnumeration_mem A hA T)
  apply hWrong
  simpa [hindex] using hT (2 * T) (by omega)

/-- Index-output half of Theorem 3.2, using the paper's two modular
languages. -/
theorem theorem_3_2_index
    (G : MemorylessIndexGenerator ℕ (Fin 2)) :
    ¬IsFinitelyRepeatingIndexGenerator G indexLanguages := by
  let A0 : Set ℕ := {x | x ∈ commonMultiples ∧ G x = 0}
  let A1 : Set ℕ := {x | x ∈ commonMultiples ∧ G x = 1}
  by_cases hA0 : A0.Infinite
  · exact index_fiber_obstruction
      (i := (0 : Fin 2)) (target := (1 : Fin 2))
      hA0 (fun _ hx => hx.1) (fun _ hx => hx.2)
      (by simpa [indexLanguages] using indexLanguageZero_not_subset_one)
  · have hA0Finite : A0.Finite := Set.not_infinite.mp hA0
    have hCommonSubset : commonMultiples ⊆ A0 ∪ A1 := by
      intro x hx
      have hcases : G x = (0 : Fin 2) ∨ G x = (1 : Fin 2) := by
        have hlt := (G x).isLt
        have hval : (G x).val = 0 ∨ (G x).val = 1 := by omega
        rcases hval with hval | hval
        · left
          apply Fin.ext
          simpa using hval
        · right
          apply Fin.ext
          simpa using hval
      rcases hcases with hG | hG
      · exact Set.mem_union_left _ ⟨hx, hG⟩
      · exact Set.mem_union_right _ ⟨hx, hG⟩
    have hA1 : A1.Infinite := by
      intro hA1Finite
      exact commonMultiples_infinite
        ((hA0Finite.union hA1Finite).subset hCommonSubset)
    exact index_fiber_obstruction
      (i := (1 : Fin 2)) (target := (0 : Fin 2))
      hA1 (fun _ hx => hx.1) (fun _ hx => hx.2)
      (by simpa [indexLanguages] using indexLanguageOne_not_subset_zero)

/-- The complete semantic content of Theorem 3.2. -/
theorem theorem_3_2 :
    (∀ i, (indexLanguages i).Infinite) ∧
    (∀ (K : Set ℕ), K.Infinite →
      ∀ G : MemorylessElementGenerator ℕ,
        ¬IsFinitelyRepeatingElementGeneratorOn G K) ∧
    (∀ G : MemorylessIndexGenerator ℕ (Fin 2),
      ¬IsFinitelyRepeatingIndexGenerator G indexLanguages) :=
  ⟨indexLanguages_infinite,
    theorem_3_2_element, theorem_3_2_index⟩

end GenLimit.BoundedMemory
