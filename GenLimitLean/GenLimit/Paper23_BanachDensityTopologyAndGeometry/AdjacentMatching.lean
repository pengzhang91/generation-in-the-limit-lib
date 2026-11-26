import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Matching consecutive points in a finite layer. Every interval cuts
at most two ends of the matching. Hitting one endpoint of each pair
therefore gives half the layer inside any interval, up to two points. -/
namespace GenLimit.KleinbergWei.Banach.AdjacentMatching
open Set
open scoped Classical
noncomputable section

private def partner : List ℕ → ℕ → Option ℕ
  | a::b::xs, x => if x=a then some b else if x=b then some a else partner xs x
  | _, _ => none

def mate (S : Finset ℕ) := partner (S.sort (· ≤ ·))

private theorem inside : ∀ {xs : List ℕ} {x y}, partner xs x=some y → x ∈ xs ∧ y ∈ xs
  | [], _, _, h | [_], _, _, h => by simp [partner] at h
  | a::b::xs, x, y, h => by
    simp only [partner] at h
    split at h
    · simp_all
    split at h
    · simp_all
    obtain ⟨hx,hy⟩ := inside h
    simp [hx,hy]

private theorem flip : ∀ {xs : List ℕ} {x y}, xs.Nodup → partner xs x=some y →
    x ≠ y ∧ partner xs y=some x
  | [], _, _, _, h | [_], _, _, _, h => by simp [partner] at h
  | a::b::xs, x, y, nd, h => by
    obtain ⟨ab,ax,bx,tail⟩ : a ≠ b ∧ a ∉ xs ∧ b ∉ xs ∧ xs.Nodup := by simpa [and_assoc] using nd
    simp only [partner] at h
    split at h
    · simp_all [partner,Ne.symm]
    split at h
    · simp_all [partner,Ne.symm]
    obtain ⟨ne,back⟩ := flip tail h
    obtain ⟨_,hy⟩ := inside h
    exact ⟨ne,by simp [partner,ne_of_mem_of_not_mem hy ax,ne_of_mem_of_not_mem hy bx,back]⟩

theorem mem_of_mate {S x y} (h : mate S x = some y) : x ∈ S ∧ y ∈ S := by
  obtain ⟨a,b⟩ := inside h; simpa using And.intro a b

theorem mate_spec {S x y} (h : mate S x = some y) : x ≠ y ∧ mate S y = some x :=
  flip (Finset.sort_nodup ..) h

private def Good (O : Set ℕ) : List ℕ → Prop
  | a::b::xs => (a ∈ O ∨ b ∈ O) ∧ Good O xs
  | _ => True

private theorem good {O : Set ℕ} : ∀ {xs : List ℕ}, xs.Nodup →
    (∀ x y, partner xs x=some y → x ∈ O ∨ y ∈ O) → Good O xs
  | [], _, _ | [_], _, _ => trivial
  | a::b::xs, nd, cover => by
    refine ⟨cover a b (by simp [partner]),good nd.tail.tail ?_⟩
    intro x y h
    have hx := (inside h).1
    have ax : x ≠ a := fun e => nd.notMem ((e ▸ List.mem_cons_of_mem b hx))
    have bx : x ≠ b := fun e => (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1 (e ▸ hx)
    exact cover x y (by simpa [partner,ax,bx] using h)

private def hits (O : Set ℕ) (xs : List ℕ) := (xs.filter (· ∈ O)).length

private theorem prefix_hits (O : Set ℕ) : ∀ m p : List ℕ, Good O (m++p) → m.length ≤ 2*hits O m+1
  | [], _, _ | [_], _, _ => by simp [hits]
  | a::b::xs, p, g => by
    obtain ⟨ab,tail⟩ := g
    have bound := prefix_hits O xs p tail
    by_cases ha : a ∈ O <;> by_cases hb : b ∈ O <;> simp_all [hits] <;> omega

private theorem middle_hits (O : Set ℕ) : ∀ p m q : List ℕ, Good O (p++(m++q)) →
    m.length ≤ 2*hits O m+2
  | [], m, q, h => by have := prefix_hits O m q h; omega
  | [a], [], _, _ => by simp
  | [a], b::xs, q, h => by
    obtain ⟨_,tail⟩ := h
    have bound := prefix_hits O xs q tail
    by_cases hb : b ∈ O <;> simp_all [hits]
    omega
  | a::b::xs, m, q, h => middle_hits O xs m q h.2

private theorem split_sort (S : Finset ℕ) (l u : ℕ) (le : l ≤ u) :
    S.sort (· ≤ ·) = ((S.filter (· < l)).sort (· ≤ ·)) ++
      (((S ∩ Finset.Ico l u).sort (· ≤ ·)) ++ ((S.filter (u ≤ ·)).sort (· ≤ ·))) := by
  apply (S.sort_sorted_lt).eq_of_mem_iff
  · apply List.pairwise_append.mpr
    refine ⟨Finset.sort_sorted_lt _,List.pairwise_append.mpr ⟨Finset.sort_sorted_lt _,Finset.sort_sorted_lt _,?_⟩,?_⟩
    · intro x hx y hy; simp at hx hy; omega
    · intro x hx y hy; simp at hx hy; rcases hy with ⟨_,_,_⟩ | ⟨_,_⟩ <;> omega
  · intro x; simp
    constructor
    · intro hx
      by_cases a : x < l <;> by_cases b : x < u <;> simp_all
    · tauto

/-- Quantitative interval bound for any set of outputs meeting every pair. -/
theorem interval_count (S : Finset ℕ) (O : Set ℕ) (l u : ℕ)
    (cover : ∀ x y, mate S x=some y → x ∈ O ∨ y ∈ O) :
    (S ∩ Finset.Ico l u).card ≤ 2*((S ∩ Finset.Ico l u).filter (· ∈ O)).card+2 := by
  by_cases le : l ≤ u
  · have h := good (Finset.sort_nodup (· ≤ ·) S) cover
    rw [split_sort S l u le] at h
    have bound := middle_hits O _ _ _ h
    let M := S ∩ Finset.Ico l u
    have count : hits O (M.sort (· ≤ ·)) = (M.filter (· ∈ O)).card := by
      unfold hits
      rw [←List.toFinset_card_of_nodup ((Finset.sort_nodup ..).filter _),List.toFinset_filter]
      simp
    change (M.sort (· ≤ ·)).length ≤ 2*hits O (M.sort (· ≤ ·))+2 at bound
    rw [Finset.length_sort,count] at bound; exact bound
  · simp [Finset.Ico_eq_empty (by omega : ¬l < u)]

end
end GenLimit.KleinbergWei.Banach.AdjacentMatching
