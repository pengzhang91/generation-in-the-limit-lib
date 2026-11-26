import Mathlib.Data.Finite.Card
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Fintype.Pi
import GenLimit.Paper29_MistakeBoundedLanguageGeneration.Definitions
import GenLimit.Support.HistoryChainText
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Log

/-! # Lemma 5.3: a finite class forcing floor(log₂ N) mistakes

A language along a binary ray contains all its nonempty prefixes. At depth
k the previous k prefixes have already appeared. A fresh output purporting
to be a longer prefix predicts the next bit, which the adversary reverses.
The length-m bit strings suffice for m rounds. Padding gives exactly N
infinite languages and the resulting enumeration is exact and injective.
-/
namespace GenLimit.MistakeBounded
open Support

private def words (r : ℕ → Bool) (t : ℕ) : List Bool := textPrefix r (t+1)
private theorem word_length (r : ℕ → Bool) (t : ℕ) : (words r t).length = t+1 :=
  textPrefix_length ..
private theorem words_inj (r : ℕ → Bool) : Function.Injective (words r) := by
  intro i j h
  simpa only [word_length,Nat.add_right_cancel_iff] using congrArg List.length h

private def finiteRay {m : ℕ} (b : Fin m → Bool) (i : ℕ) : Bool :=
  if hi : i < m then b ⟨i,hi⟩ else false

private def bitClass (m : ℕ) : Set (Set (List Bool)) :=
  Set.range fun b : Fin m → Bool => Set.range (words (finiteRay b))

private def nextBit (G : Generic.Generator (List Bool)) (xs : List Bool) : Bool :=
  !((G xs.length (fun i => xs.take (i.val+1)))[xs.length]?.getD false)

private def branch (G : Generic.Generator (List Bool)) : ℕ → List Bool :=
  Nat.rec [] (fun _ xs => xs ++ [nextBit G xs])

private theorem branch_length (G : Generic.Generator (List Bool)) (t : ℕ) :
    (branch G t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [branch] at ih ⊢; omega

private def branchChain (G : Generic.Generator (List Bool)) : HistoryChain Bool where
  history := branch G
  prefix_succ := fun _ => List.prefix_append ..
  le_length := fun t => (branch_length G t).ge

private theorem output_on_branch (G : Generic.Generator (List Bool)) (xs : List Bool)
    (s : ℕ → List Bool) {t : ℕ} (len : xs.length = t)
    (hist : ∀ j < t, s j = xs.take (j+1)) :
    Generic.output G s t = G xs.length (fun i => xs.take (i.val+1)) := by
  subst t
  exact congrArg (G xs.length) (funext fun i => hist i.val i.isLt)

private theorem hard_run (m : ℕ) (G : Generic.Generator (List Bool))
    (fresh : ∀ t h (i : Fin t), G t h ≠ h i) :
    ∃ K ∈ bitClass m, ∃ s, Generic.Presents s K ∧ Function.Injective s ∧
      ∀ t < m, Generic.output G s t ∉ K := by
  let chain := branchChain G
  let r := finiteRay (fun i : Fin m => chain.stream i.val)
  let s := words r
  refine ⟨Set.range s, ⟨_,rfl⟩, s,rfl,words_inj _,?_⟩
  intro t ht
  let xs := branch G t
  have len : xs.length = t := branch_length ..
  have state (i : ℕ) (hi : i < xs.length) : r i = xs[i] := by
    have him : i < m := lt_trans (hi.trans_le len.le) ht
    simpa [r,finiteRay,him] using chain.stream_eq_get t i hi
  have hist (j : ℕ) (hj : j < t) : s j = xs.take (j+1) := by
    apply List.ext_getElem
    · simp [s,words,textPrefix,len,Nat.min_eq_left (by omega : j+1 ≤ t)]
    · intro i hi _
      have h : i < j+1 := (word_length r j) ▸ hi
      simpa [s,words,textPrefix] using state i (by omega)
  let out := Generic.output G s t
  have out_eq : out = G xs.length (fun i => xs.take (i.val+1)) :=
    output_on_branch G xs s len hist
  have next : r t = nextBit G xs := by
    have h := chain.stream_eq_get (t+1) t (by change t < (branch G (t+1)).length; rw [branch_length]; omega)
    have hg : (branch G (t+1))[t]'(by rw [branch_length]; omega) = nextBit G xs := by
      change (xs ++ [nextBit G xs])[t]'(by simp [len]) = _
      rw [List.getElem_append_right (by omega)]
      simp [len]
    simpa [r,finiteRay,ht] using h.trans hg
  rintro ⟨j,hj⟩
  change s j = out at hj
  by_cases hshort : j < t
  · exact fresh t (fun i : Fin t => s i.val) ⟨j,hshort⟩ hj.symm
  · have hbit : out[t]? = some (r t) := by
      rw [← hj]
      have hi : t < (s j).length := by rw [show (s j).length = _ from word_length r j]; omega
      rw [List.getElem?_eq_getElem hi]
      simp [s,words,textPrefix]
    have hb : (G xs.length (fun i => xs.take (i.val+1)))[xs.length]? = some (r t) := by
      simpa only [← out_eq,len] using hbit
    have bad : r t = !r t := by
      simpa only [nextBit,hb,Option.getD_some] using next
    cases h : r t <;> simp [h] at bad

private theorem infinite_language_space : {K : Set (List Bool) | K.Infinite}.Infinite := by
  let K := fun n : ℕ => {xs : List Bool | n ≤ xs.length}
  have inj : Function.Injective K := by
    intro i j h
    have le (n k : ℕ) (eq : K n = K k) : k ≤ n := by
      have hx : List.replicate n false ∈ K n := by simp [K]
      simpa [K] using (eq ▸ hx : List.replicate n false ∈ K k)
    exact le_antisymm (le _ _ h.symm) (le _ _ h)
  apply (Set.infinite_range_of_injective inj).mono
  rintro _ ⟨n,rfl⟩
  apply (Set.infinite_range_of_injective (f := fun j : ℕ => List.replicate (n+j) false) ?_).mono
  · rintro _ ⟨j,rfl⟩
    simp [K]
  · intro i j h
    simpa using congrArg List.length h

/-- The finite lower bound with an exact class size, infinite languages,
a causal fresh generator, and an injective enumeration of the chosen target. -/
theorem finite_log_mistake_lower (N : ℕ) (positive : 0 < N) :
    ∃ H : Set (Set (List Bool)), H.Finite ∧ H.ncard = N ∧ (∀ K ∈ H, K.Infinite) ∧
      ∀ G : Generic.Generator (List Bool), (∀ t h (i : Fin t), G t h ≠ h i) →
        ∃ K ∈ H, ∃ s, Generic.Presents s K ∧ Function.Injective s ∧
          ∀ t < Nat.log2 N, Generic.output G s t ∉ K := by
  classical
  let m := Nat.log2 N
  have hf : (bitClass m).Finite := Set.finite_range _
  have sub : bitClass m ⊆ {K | K.Infinite} := by
    rintro _ ⟨b,rfl⟩
    exact Set.infinite_range_of_injective (words_inj _)
  have card : (bitClass m).ncard ≤ N := by
    have a : (bitClass m).ncard ≤ 2^m := by
      change Nat.card (bitClass m) ≤ 2^m
      simpa [bitClass,Nat.card_fun] using
        (Finite.card_range_le (fun b : Fin m → Bool => Set.range (words (finiteRay b))))
    exact a.trans (by simpa [m,Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 positive.ne')
  obtain ⟨H,inc,ss,heq⟩ := infinite_language_space.exists_superset_ncard_eq sub hf card
  refine ⟨H, Set.finite_of_ncard_pos (heq ▸ positive),heq,fun _ h => ss h,?_⟩
  intro G fresh
  obtain ⟨K,hK,rest⟩ := hard_run m G fresh
  exact ⟨K,inc hK,rest⟩

end GenLimit.MistakeBounded
