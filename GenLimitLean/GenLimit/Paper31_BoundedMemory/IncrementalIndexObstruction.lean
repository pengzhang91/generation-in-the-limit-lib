import GenLimit.Paper31_BoundedMemory.ExactIdentificationObstruction
import GenLimit.Paper31_BoundedMemory.OutputSeparations
import Mathlib.Tactic.FinCases

/-!
# Appendix A: three-state obstruction to incremental index generation

This module formalizes Theorem A.1 and Proposition A.2 of
Kleinberg--Mehrotra--Saberi--Velegkas, arXiv:2605.30324v1.

The output indices are exactly the persistent states `Fin 3`: there are no
synonym indices, outside hypotheses, or hidden states.  The hard streams are
exact finitely-repeating presentations.  The result is semantic and makes no
runtime or computability claim.
-/

namespace GenLimit.BoundedMemory

universe u

section IncrementalIndexInterface

variable {α : Type u} {ι : Type*}

/-- Eventual set-validity of an incremental index-output run. -/
def IncrementalIndexGeneratesRun
    (langs : ι → Set α)
    (generator : IncrementalLearner α ι)
    (initial target : ι)
    (stream : ℕ → α) : Prop :=
  ∃ T, ∀ t, T ≤ t →
    langs (incrementalRun generator initial stream t) ⊆ langs target

/-- Incremental index generation under the paper's finitely-repeating
presentation restriction.  The index type is also the entire persistent
state type. -/
def IncrementallyIndexGenerableOnFinitelyRepeating
    (langs : ι → Set α) : Prop :=
  ∃ generator : IncrementalLearner α ι, ∃ initial,
    ∀ target stream,
      GenLimit.Generic.Presents stream (langs target) →
        FinitelyRepeating stream →
          IncrementalIndexGeneratesRun
            langs generator initial target stream

theorem incrementalIndexGeneratesRun_exact_of_antichain
    {langs : ι → Set α}
    (hanti : ∀ i j, langs i ⊆ langs j → i = j)
    {generator : IncrementalLearner α ι}
    {initial target : ι} {stream : ℕ → α}
    (hgen :
      IncrementalIndexGeneratesRun
        langs generator initial target stream) :
    ExactlyIdentifiesRun generator initial target stream := by
  obtain ⟨T, hT⟩ := hgen
  exact ⟨T, fun t ht => hanti _ _ (hT t ht)⟩

end IncrementalIndexInterface

section FinitePrefix

variable {α : Type u} {ι : Type*}

/-- Attach a finite history in front of an infinite tail. -/
def prefixStream (xs : List α) (tail : ℕ → α) : ℕ → α :=
  match xs with
  | [] => tail
  | x :: xs => prepend x (prefixStream xs tail)

/-- State reached after consuming a finite history. -/
def prefixState
    (generator : IncrementalLearner α ι) (initial : ι) :
    List α → ι
  | [] => initial
  | x :: xs => prefixState generator (generator initial x) xs

/-- Set enumerated after attaching a finite history to a tail presentation. -/
def prefixSupport : List α → Set α → Set α
  | [], tail => tail
  | x :: xs, tail => insert x (prefixSupport xs tail)

@[simp]
theorem prefixStream_nil (tail : ℕ → α) :
    prefixStream [] tail = tail :=
  rfl

@[simp]
theorem prefixStream_cons (x : α) (xs : List α) (tail : ℕ → α) :
    prefixStream (x :: xs) tail = prepend x (prefixStream xs tail) :=
  rfl

@[simp]
theorem prefixState_nil
    (generator : IncrementalLearner α ι) (initial : ι) :
    prefixState generator initial [] = initial :=
  rfl

@[simp]
theorem prefixState_cons
    (generator : IncrementalLearner α ι) (initial : ι)
    (x : α) (xs : List α) :
    prefixState generator initial (x :: xs) =
      prefixState generator (generator initial x) xs :=
  rfl

@[simp]
theorem prefixSupport_nil (tail : Set α) :
    prefixSupport [] tail = tail :=
  rfl

@[simp]
theorem prefixSupport_cons (x : α) (xs : List α) (tail : Set α) :
    prefixSupport (x :: xs) tail = insert x (prefixSupport xs tail) :=
  rfl

theorem prepend_presents_insert'
    (head : α) {tail : ℕ → α} {K : Set α}
    (htail : GenLimit.Generic.Presents tail K) :
    GenLimit.Generic.Presents (prepend head tail) (insert head K) := by
  apply Set.Subset.antisymm
  · rintro x ⟨t, rfl⟩
    cases t with
    | zero => exact Set.mem_insert head K
    | succ n =>
        apply Set.mem_insert_of_mem
        rw [← htail]
        exact ⟨n, rfl⟩
  · intro x hx
    rcases hx with rfl | hx
    · exact ⟨0, rfl⟩
    · rw [← htail] at hx
      obtain ⟨n, rfl⟩ := hx
      exact ⟨n + 1, rfl⟩

theorem prefixStream_presents
    {xs : List α} {tail : ℕ → α} {K : Set α}
    (htail : GenLimit.Generic.Presents tail K) :
    GenLimit.Generic.Presents
      (prefixStream xs tail) (prefixSupport xs K) := by
  induction xs with
  | nil => exact htail
  | cons x xs ih =>
      exact prepend_presents_insert' x ih

theorem prefixStream_finitelyRepeating
    (xs : List α) {tail : ℕ → α}
    (htail : FinitelyRepeating tail) :
    FinitelyRepeating (prefixStream xs tail) := by
  induction xs with
  | nil => exact htail
  | cons x xs ih =>
      exact prepend_finitelyRepeating x ih

theorem incrementalRun_prepend'
    (generator : IncrementalLearner α ι) (initial : ι)
    (head : α) (tail : ℕ → α) (t : ℕ) :
    incrementalRun generator initial (prepend head tail) (t + 1) =
      incrementalRun generator (generator initial head) tail t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change
        generator
            (incrementalRun generator initial (prepend head tail) (t + 1))
            (tail t) =
          generator
            (incrementalRun generator (generator initial head) tail t)
            (tail t)
      exact congrArg (fun q => generator q (tail t)) ih

theorem prefixStream_append
    (xs ys : List α) (tail : ℕ → α) :
    prefixStream (xs ++ ys) tail =
      prefixStream xs (prefixStream ys tail) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, prefixStream_cons]
      rw [ih]

theorem incrementalRun_prefixStream
    (generator : IncrementalLearner α ι) (initial : ι)
    (xs : List α) (tail : ℕ → α) (t : ℕ) :
    incrementalRun generator initial (prefixStream xs tail)
        (xs.length + t) =
      incrementalRun generator (prefixState generator initial xs) tail t := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.length_cons, prefixStream_cons, prefixState_cons]
      rw [show xs.length + 1 + t = (xs.length + t) + 1 by omega]
      rw [incrementalRun_prepend']
      exact ih (generator initial x)

end FinitePrefix

section ThreeStateCombinatorics

theorem fin3_exhaust_of_pairwise
    {A B C q : Fin 3}
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    q = A ∨ q = B ∨ q = C := by
  fin_cases A <;> fin_cases B <;> fin_cases C <;> fin_cases q <;>
    simp_all

theorem fin3_eq_first_of_ne
    {A B C q : Fin 3}
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (hqB : q ≠ B) (hqC : q ≠ C) :
    q = A := by
  rcases fin3_exhaust_of_pairwise hAB hAC hBC (q := q) with h | h | h
  · exact h
  · exact (hqB h).elim
  · exact (hqC h).elim

theorem fin3_two_permutations
    {A B C p₁ p₂ p₃ : Fin 3}
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hp₁C : p₁ ≠ C) (hp₂B : p₂ ≠ B) (hp₃A : p₃ ≠ A) :
    (p₁ = A ∧ p₂ = C ∧ p₃ = B) ∨
      (p₁ = B ∧ p₂ = A ∧ p₃ = C) := by
  rcases fin3_exhaust_of_pairwise hAB hAC hBC (q := p₁) with h₁ | h₁ | h₁ <;>
    rcases fin3_exhaust_of_pairwise hAB hAC hBC (q := p₂) with h₂ | h₂ | h₂ <;>
      rcases fin3_exhaust_of_pairwise hAB hAC hBC (q := p₃) with h₃ | h₃ | h₃ <;>
        simp_all

end ThreeStateCombinatorics

section AppendixTriangle

variable {α : Type u}

/-- The literal three-language triangle from Appendix Proposition A.2. -/
def appendixTriangleLanguages
    (T : Set α) (a b c : α) : Fin 3 → Set α
  | ⟨0, _⟩ => insert a (insert b T)
  | ⟨1, _⟩ => insert a (insert c T)
  | ⟨2, _⟩ => insert b (insert c T)

macro "solve_triangle_support" langs:ident : tactic =>
  `(tactic| (
    unfold $langs
    ext x
    simp only [List.cons_append, List.nil_append, prefixSupport,
      appendixTriangleLanguages,
      Set.mem_insert_iff] <;>
    tauto))

theorem appendixTriangleLanguages_infinite
    {T : Set α} (hT : T.Infinite) (a b c : α) :
    ∀ i, (appendixTriangleLanguages T a b c i).Infinite := by
  intro i
  apply hT.mono
  fin_cases i <;> intro x hx <;>
    simp [appendixTriangleLanguages, hx]

theorem appendixTriangleLanguages_antichain
    {T : Set α} {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haT : a ∉ T) (hbT : b ∉ T) (hcT : c ∉ T) :
    ∀ i j,
      appendixTriangleLanguages T a b c i ⊆
        appendixTriangleLanguages T a b c j →
      i = j := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try rfl
  · have h := hij (show b ∈ insert a (insert b T) by simp)
    exfalso
    simp [appendixTriangleLanguages, hab.symm, hbc, hbT] at h
  · have h := hij (show a ∈ insert a (insert b T) by simp)
    exfalso
    simp [appendixTriangleLanguages, hab, hac, haT] at h
  · have h := hij (show c ∈ insert a (insert c T) by simp)
    exfalso
    simp [appendixTriangleLanguages, hac.symm, hbc.symm, hcT] at h
  · have h := hij (show a ∈ insert a (insert c T) by simp)
    exfalso
    simp [appendixTriangleLanguages, hab, hac, haT] at h
  · have h := hij (show c ∈ insert b (insert c T) by simp)
    exfalso
    simp [appendixTriangleLanguages, hac.symm, hbc.symm, hcT] at h
  · have h := hij (show b ∈ insert b (insert c T) by simp)
    exfalso
    simp [appendixTriangleLanguages, hab.symm, hbc, hbT] at h

/- Appendix Proposition A.2, in its source-faithful representation-sensitive
form: the three language indices are exactly the generator's three persistent
states, and the adversary only uses finitely-repeating presentations. -/
set_option maxHeartbeats 750000 in
theorem proposition_A_2
    [Countable α]
    {T : Set α} (hT : T.Infinite) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haT : a ∉ T) (hbT : b ∉ T) (hcT : c ∉ T) :
    ¬IncrementallyIndexGenerableOnFinitelyRepeating
      (appendixTriangleLanguages T a b c) := by
  intro hgen
  obtain ⟨generator, initial, hgen⟩ := hgen
  let langs := appendixTriangleLanguages T a b c
  have hanti :
      ∀ i j, langs i ⊆ langs j → i = j := by
    simpa [langs] using
      appendixTriangleLanguages_antichain
        hab hac hbc haT hbT hcT
  have hExact :
      ∀ target stream,
        GenLimit.Generic.Presents stream (langs target) →
          FinitelyRepeating stream →
            ExactlyIdentifiesRun generator initial target stream := by
    intro target stream hP hR
    apply incrementalIndexGeneratesRun_exact_of_antichain hanti
    exact hgen target stream hP hR

  let R : ℕ → α := infiniteEnumeration T hT
  have hRP : GenLimit.Generic.Presents R T :=
    infiniteEnumeration_presents T hT
  have hRR : FinitelyRepeating R :=
    injective_finitelyRepeating (infiniteEnumeration_injective T hT)
  let q : List α → Fin 3 := prefixState generator initial

  have hPrefixExact :
      ∀ (xs : List α) (target : Fin 3),
        prefixSupport xs T = langs target →
          ExactlyIdentifiesRun generator initial target
            (prefixStream xs R) := by
    intro xs target hsupp
    apply hExact target
    · simpa [hsupp] using prefixStream_presents (xs := xs) hRP
    · exact prefixStream_finitelyRepeating xs hRR

  have hDistinct :
      ∀ (xs ys suffix : List α) (target₁ target₂ : Fin 3),
        prefixSupport (xs ++ suffix) T = langs target₁ →
          prefixSupport (ys ++ suffix) T = langs target₂ →
            target₁ ≠ target₂ →
              q xs ≠ q ys := by
    intro xs ys suffix target₁ target₂ hsupp₁ hsupp₂ htargets
    apply states_distinct_of_aligned_exact_runs
      (learner := generator) (initial := initial)
      (state₁ := q xs) (state₂ := q ys)
      (tail := prefixStream suffix R)
      (stream₁ := prefixStream (xs ++ suffix) R)
      (stream₂ := prefixStream (ys ++ suffix) R)
      (offset₁ := xs.length) (offset₂ := ys.length)
      (target₁ := target₁) (target₂ := target₂)
    · intro t
      rw [prefixStream_append]
      simpa [q] using
        incrementalRun_prefixStream generator initial xs
          (prefixStream suffix R) t
    · intro t
      rw [prefixStream_append]
      simpa [q] using
        incrementalRun_prefixStream generator initial ys
          (prefixStream suffix R) t
    · exact hPrefixExact (xs ++ suffix) target₁ hsupp₁
    · exact hPrefixExact (ys ++ suffix) target₂ hsupp₂
    · exact htargets

  let A := q [a]
  let B := q [b]
  let C := q [c]
  let p₁ := q [a, b]
  let p₂ := q [a, c]
  let p₃ := q [b, c]

  have hAB : A ≠ B := by
    apply hDistinct [a] [b] [c] 1 2
    · solve_triangle_support langs
    · solve_triangle_support langs
    · decide
  have hAC : A ≠ C := by
    apply hDistinct [a] [c] [b] 0 2
    · solve_triangle_support langs
    · solve_triangle_support langs
    · decide
  have hBC : B ≠ C := by
    apply hDistinct [b] [c] [a] 0 1
    · solve_triangle_support langs
    · solve_triangle_support langs
    · decide

  have hp12 : p₁ ≠ p₂ := by
    apply hDistinct [a, b] [a, c] [] 0 1
    · rfl
    · rfl
    · decide
  have hp13 : p₁ ≠ p₃ := by
    apply hDistinct [a, b] [b, c] [] 0 2
    · rfl
    · rfl
    · decide
  have hp23 : p₂ ≠ p₃ := by
    apply hDistinct [a, c] [b, c] [] 1 2
    · rfl
    · rfl
    · decide

  have completed₁ :
      ∀ xs : List α,
        prefixSupport xs T = langs 0 →
          q xs = p₁ := by
    intro xs hsupp
    apply fin3_eq_first_of_ne hp12 hp13 hp23
    · exact hDistinct xs [a, c] [] 0 1
        (by simpa using hsupp) rfl (by decide)
    · exact hDistinct xs [b, c] [] 0 2
        (by simpa using hsupp) rfl (by decide)
  have completed₂ :
      ∀ xs : List α,
        prefixSupport xs T = langs 1 →
          q xs = p₂ := by
    intro xs hsupp
    have hq1 : q xs ≠ p₁ :=
      hDistinct xs [a, b] [] 1 0
        (by simpa using hsupp) rfl (by decide)
    have hq3 : q xs ≠ p₃ :=
      hDistinct xs [b, c] [] 1 2
        (by simpa using hsupp) rfl (by decide)
    exact fin3_eq_first_of_ne hp12.symm hp23 hp13
      hq1 hq3
  have completed₃ :
      ∀ xs : List α,
        prefixSupport xs T = langs 2 →
          q xs = p₃ := by
    intro xs hsupp
    have hq1 : q xs ≠ p₁ :=
      hDistinct xs [a, b] [] 2 0
        (by simpa using hsupp) rfl (by decide)
    have hq2 : q xs ≠ p₂ :=
      hDistinct xs [a, c] [] 2 1
        (by simpa using hsupp) rfl (by decide)
    exact fin3_eq_first_of_ne hp13.symm hp23.symm hp12
      hq1 hq2

  have hba : q [b, a] = p₁ := by
    apply completed₁
    solve_triangle_support langs
  have hacA : q [c, a] = p₂ := by
    apply completed₂
    solve_triangle_support langs
  have hcb : q [c, b] = p₃ := by
    apply completed₃
    solve_triangle_support langs
  have haba : q [a, b, a] = p₁ := by
    apply completed₁
    solve_triangle_support langs
  have habb : q [a, b, b] = p₁ := by
    apply completed₁
    solve_triangle_support langs
  have haca : q [a, c, a] = p₂ := by
    apply completed₂
    solve_triangle_support langs
  have hacc : q [a, c, c] = p₂ := by
    apply completed₂
    solve_triangle_support langs
  have hbcb : q [b, c, b] = p₃ := by
    apply completed₃
    solve_triangle_support langs
  have hcbc : q [c, b, c] = p₃ := by
    apply completed₃
    solve_triangle_support langs

  have haaB : q [a, a] ≠ B := by
    apply hDistinct [a, a] [b] [c] 1 2
    · solve_triangle_support langs
    · solve_triangle_support langs
    · decide
  have haaC : q [a, a] ≠ C := by
    apply hDistinct [a, a] [c] [b] 0 2
    · solve_triangle_support langs
    · solve_triangle_support langs
    · decide
  have haa : q [a, a] = A :=
    fin3_eq_first_of_ne hAB hAC hBC haaB haaC

  have hbbA : q [b, b] ≠ A := by
    apply hDistinct [b, b] [a] [c] 2 1
    · solve_triangle_support langs
    · solve_triangle_support langs
    · decide
  have hbbC : q [b, b] ≠ C := by
    apply hDistinct [b, b] [c] [a] 0 1
    · solve_triangle_support langs
    · solve_triangle_support langs
    · decide
  have hbb : q [b, b] = B :=
    fin3_eq_first_of_ne hAB.symm hBC hAC hbbA hbbC

  have hccA : q [c, c] ≠ A := by
    apply hDistinct [c, c] [a] [b] 2 0
    · solve_triangle_support langs
    · solve_triangle_support langs
    · decide
  have hccB : q [c, c] ≠ B := by
    apply hDistinct [c, c] [b] [a] 1 0
    · solve_triangle_support langs
    · solve_triangle_support langs
    · decide
  have hcc : q [c, c] = C :=
    fin3_eq_first_of_ne hAC.symm hBC.symm hAB hccA hccB

  have hA_a : generator A a = A := by
    simpa [A, q, prefixState] using haa
  have hB_b : generator B b = B := by
    simpa [B, q, prefixState] using hbb
  have hC_c : generator C c = C := by
    simpa [C, q, prefixState] using hcc
  have hA_b : generator A b = p₁ := by
    rfl
  have hA_c : generator A c = p₂ := by
    rfl
  have hB_a : generator B a = p₁ := by
    simpa [A, B, q, p₁, prefixState] using hba
  have hB_c : generator B c = p₃ := by
    rfl
  have hC_a : generator C a = p₂ := by
    simpa [A, C, q, p₂, prefixState] using hacA
  have hC_b : generator C b = p₃ := by
    simpa [B, C, q, p₃, prefixState] using hcb
  have hp₁a : generator p₁ a = p₁ := by
    simpa [A, q, p₁, prefixState] using haba
  have hp₁b : generator p₁ b = p₁ := by
    simpa [A, q, p₁, prefixState] using habb
  have hp₂a : generator p₂ a = p₂ := by
    simpa [A, q, p₂, prefixState] using haca
  have hp₂c : generator p₂ c = p₂ := by
    simpa [A, q, p₂, prefixState] using hacc
  have hp₃b : generator p₃ b = p₃ := by
    simpa [B, q, p₃, prefixState] using hbcb
  have hp₃c : generator p₃ c = p₃ := by
    calc
      generator p₃ c = generator (q [c, b]) c := by rw [hcb]
      _ = p₃ := by simpa [q, prefixState] using hcbc

  have hp₁C : p₁ ≠ C := by
    intro heq
    have hp₂C : p₂ = C := by
      calc
        p₂ = generator C a := hC_a.symm
        _ = generator p₁ a := by rw [heq]
        _ = p₁ := hp₁a
        _ = C := heq
    have hp₃C : p₃ = C := by
      calc
        p₃ = generator C b := hC_b.symm
        _ = generator p₁ b := by rw [heq]
        _ = p₁ := hp₁b
        _ = C := heq
    exact hp23 (hp₂C.trans hp₃C.symm)
  have hp₂B : p₂ ≠ B := by
    intro heq
    have hp₁B : p₁ = B := by
      calc
        p₁ = generator B a := hB_a.symm
        _ = generator p₂ a := by rw [heq]
        _ = p₂ := hp₂a
        _ = B := heq
    have hp₃B : p₃ = B := by
      calc
        p₃ = generator B c := hB_c.symm
        _ = generator p₂ c := by rw [heq]
        _ = p₂ := hp₂c
        _ = B := heq
    exact hp13 (hp₁B.trans hp₃B.symm)
  have hp₃A : p₃ ≠ A := by
    intro heq
    have hp₁A : p₁ = A := by
      calc
        p₁ = generator A b := hA_b.symm
        _ = generator p₃ b := by rw [heq]
        _ = p₃ := hp₃b
        _ = A := heq
    have hp₂A : p₂ = A := by
      calc
        p₂ = generator A c := hA_c.symm
        _ = generator p₃ c := by rw [heq]
        _ = p₃ := hp₃c
        _ = A := heq
    exact hp12 (hp₁A.trans hp₂A.symm)

  have hpCases :=
    fin3_two_permutations hAB hAC hBC
      hp12 hp13 hp23 hp₁C hp₂B hp₃A
  have hInitial :
      initial = A ∨ initial = B ∨ initial = C :=
    fin3_exhaust_of_pairwise hAB hAC hBC
  have hinitA : generator initial a = A := by
    rfl
  have hinitB : generator initial b = B := by
    rfl
  have hinitC : generator initial c = C := by
    rfl

  rcases hpCases with ⟨hp₁A, hp₂C, hp₃B⟩ |
      ⟨hp₁B, hp₂A, hp₃C⟩
  · rcases hInitial with hi | hi | hi
    · apply hAB
      calc
        A = p₁ := hp₁A.symm
        _ = generator A b := hA_b.symm
        _ = generator initial b := by rw [hi]
        _ = B := hinitB
    · apply hBC
      calc
        B = p₃ := hp₃B.symm
        _ = generator B c := hB_c.symm
        _ = generator initial c := by rw [hi]
        _ = C := hinitC
    · apply hAC.symm
      calc
        C = p₂ := hp₂C.symm
        _ = generator C a := hC_a.symm
        _ = generator initial a := by rw [hi]
        _ = A := hinitA
  · rcases hInitial with hi | hi | hi
    · apply hAC
      calc
        A = p₂ := hp₂A.symm
        _ = generator A c := hA_c.symm
        _ = generator initial c := by rw [hi]
        _ = C := hinitC
    · apply hAB.symm
      calc
        B = p₁ := hp₁B.symm
        _ = generator B a := hB_a.symm
        _ = generator initial a := by rw [hi]
        _ = A := hinitA
    · apply hBC.symm
      calc
        C = p₃ := hp₃C.symm
        _ = generator C b := hC_b.symm
        _ = generator initial b := by rw [hi]
        _ = B := hinitB

/-- Appendix Theorem A.1 for the same displayed triangle family. -/
theorem theorem_A_1_triangle
    [Countable α]
    {T : Set α} (hT : T.Infinite) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haT : a ∉ T) (hbT : b ∉ T) (hcT : c ∉ T) :
    ¬IncrementallyExactlyIdentifiableOnFinitelyRepeating
      (appendixTriangleLanguages T a b c) := by
  intro hident
  apply proposition_A_2 hT hab hac hbc haT hbT hcT
  obtain ⟨learner, initial, hident⟩ := hident
  refine ⟨learner, initial, ?_⟩
  intro target stream hP hR
  obtain ⟨T₀, hT₀⟩ := hident target stream hP hR
  refine ⟨T₀, ?_⟩
  intro t ht
  rw [hT₀ t ht]

/-- Appendix Theorem A.1 in its literal existential form on the canonical
universe `ℕ`.  The witness contains exactly three distinct infinite
languages. -/
theorem theorem_A_1 :
    ∃ langs : Fin 3 → Set ℕ,
      Function.Injective langs ∧
        (∀ i, (langs i).Infinite) ∧
          ¬IncrementallyExactlyIdentifiableOnFinitelyRepeating langs := by
  let T : Set ℕ := Set.range fun n : ℕ => n + 3
  have hT : T.Infinite :=
    Set.infinite_range_of_injective (fun _ _ h => by omega)
  have h0T : 0 ∉ T := by simp [T]
  have h1T : 1 ∉ T := by simp [T]
  have h2T : 2 ∉ T := by simp [T]
  let langs := appendixTriangleLanguages T 0 1 2
  have hanti :
      ∀ i j, langs i ⊆ langs j → i = j := by
    simpa [langs] using
      appendixTriangleLanguages_antichain
        (a := 0) (b := 1) (c := 2)
        (by decide) (by decide) (by decide) h0T h1T h2T
  refine ⟨langs, ?_, ?_, ?_⟩
  · intro i j hij
    apply hanti i j
    rw [hij]
  · simpa [langs] using
      appendixTriangleLanguages_infinite hT 0 1 2
  · simpa [langs] using
      theorem_A_1_triangle hT
        (by decide) (by decide) (by decide) h0T h1T h2T

end AppendixTriangle

end GenLimit.BoundedMemory
