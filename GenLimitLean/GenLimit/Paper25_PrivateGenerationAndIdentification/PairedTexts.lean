import GenLimit.Support.StreamPrefixText
import Mathlib.Data.Nat.Nth
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Powerset

/-! Duplicate-free paired prefixes for the private identification obstruction.
The two infinite tails agree; one prefix can already contain additional
words from the eventual adversarial target. -/

namespace GenLimit.PrivateLimit

open Set
open scoped Classical

structure PairedText (K L : Set ℕ) where
  left : List ℕ
  right : List ℕ
  length_eq : left.length = right.length
  left_nodup : left.Nodup
  right_nodup : right.Nodup
  left_mem : ∀ x ∈ left, x ∈ K
  right_mem : ∀ x ∈ right, x ∈ L
  covers : ∀ x ∈ K \ L, x ∈ left
  overlap : ∀ x ∈ right, x ∈ K → x ∈ left

namespace PairedText

theorem initial {K L : Set ℕ} (F V : Finset ℕ) (hf : (↑F : Set ℕ) = K \ L)
    (hv : (↑V : Set ℕ) ⊆ L \ K) (hc : F.card = V.card) : Nonempty (PairedText K L) := by
  refine ⟨⟨F.toList,V.toList,by simpa using hc,F.nodup_toList,V.nodup_toList,?_,?_,?_,?_⟩⟩
  · intro x hx
    have hm : x ∈ (↑F : Set ℕ) := Finset.mem_toList.mp hx
    exact (hf ▸ hm : x ∈ K \ L).1
  · exact fun _ h => (hv (Finset.mem_toList.mp h)).1
  · intro x h; exact Finset.mem_toList.mpr (show x ∈ (↑F : Set ℕ) from hf.symm ▸ h)
  · intro x h hk; exact ((hv (Finset.mem_toList.mp h)).2 hk).elim

theorem orient {K L : Set ℕ} (hd : (K \ L).Finite) :
    Nonempty (PairedText K L) ∨ Nonempty (PairedText L K) := by
  classical
  let F := hd.toFinset
  have hf : (↑F : Set ℕ) = K \ L := hd.coe_toFinset
  rcases (L \ K).finite_or_infinite with hd' | hI
  · let V := hd'.toFinset
    have hv : (↑V : Set ℕ) = L \ K := hd'.coe_toFinset
    rcases le_total F.card V.card with h | h
    · obtain ⟨W,hw,hc⟩ := Finset.exists_subset_card_eq h
      exact Or.inl (initial F W hf (hv ▸ Finset.coe_subset.mpr hw) hc.symm)
    · obtain ⟨W,hw,hc⟩ := Finset.exists_subset_card_eq h
      exact Or.inr (initial V W hv (hf ▸ Finset.coe_subset.mpr hw) hc.symm)
  · obtain ⟨W,hw,hc⟩ := hI.exists_subset_card_eq F.card
    exact Or.inl (initial F W hf hw hc.symm)

variable {K L : Set ℕ}

/-- Force an arbitrary requested target word into the adversarial prefix,
adjusting the comparison prefix by at most one fresh symbol. -/
theorem add_requested (p : PairedText K L) (hK : K.Infinite) (n : ℕ) :
    ∃ q : PairedText K L, p.right <+: q.right ∧ (n ∈ L → n ∈ q.right) := by
  classical
  by_cases add : n ∈ L ∧ n ∉ p.right
  · obtain ⟨a,ha,hfresh⟩ := hK.exists_notMem_finset p.left.toFinset
    let b := if n ∈ K ∧ n ∉ p.left then n else a
    have hb : b ∈ K ∧ b ∉ p.left := by
      dsimp [b]; split <;> simp_all
    have leftUnique : (p.left ++ [b]).Nodup := by
      simp [List.nodup_append,p.left_nodup]; rintro _ h rfl; exact hb.2 h
    have rightUnique : (p.right ++ [n]).Nodup := by
      simp [List.nodup_append,p.right_nodup]; rintro _ h rfl; exact add.2 h
    refine ⟨⟨p.left ++ [b],p.right ++ [n],by simp [p.length_eq],leftUnique,rightUnique,?_,?_,?_,?_⟩,
      List.prefix_append .., by simp⟩
    · intro x h; rcases List.mem_append.mp h with h | h
      · exact p.left_mem x h
      · simpa only [List.mem_singleton.mp h] using hb.1
    · intro x h; rcases List.mem_append.mp h with h | h
      · exact p.right_mem x h
      · simpa only [List.mem_singleton.mp h] using add.1
    · exact fun x h => List.mem_append_left _ (p.covers x h)
    · intro x h hx
      rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ (p.overlap x h hx)
      · obtain rfl := List.mem_singleton.mp h
        by_cases hm : x ∈ p.left <;> simp [b, hx, hm]
  · exact ⟨p,List.prefix_refl _,fun h => by_contra fun h' => add ⟨h,h'⟩⟩

private def rest (p : PairedText K L) : Set ℕ := K \ (p.left.toFinset : Set ℕ)
private theorem rest_inf (p : PairedText K L) (hK : K.Infinite) : p.rest.Infinite :=
  hK.diff p.left.toFinset.finite_toSet

noncomputable def shared (p : PairedText K L) : ℕ → ℕ := Nat.nth (· ∈ p.rest)

theorem shared_inj (p : PairedText K L) (hK : K.Infinite) : Function.Injective p.shared :=
  Nat.nth_injective (p.rest_inf hK)

private theorem shared_spec (p : PairedText K L) (hK : K.Infinite) (i : ℕ) :
    p.shared i ∈ K ∧ p.shared i ∈ L ∧ p.shared i ∉ p.left ∧ p.shared i ∉ p.right := by
  have h := Nat.nth_mem_of_infinite (p.rest_inf hK) i
  change p.shared i ∈ K ∧ p.shared i ∉ (p.left.toFinset : Set ℕ) at h
  have hn : p.shared i ∉ p.left := by simpa using h.2
  exact ⟨h.1,by_contra (fun hL => hn (p.covers _ ⟨h.1,hL⟩)),hn,
    fun hr => hn (p.overlap _ hr h.1)⟩

noncomputable def leftStream (p : PairedText K L) := Support.prependStream p.left p.shared
noncomputable def rightStream (p : PairedText K L) := Support.prependStream p.right p.shared

private theorem prefix_injective {xs : List ℕ} {f : ℕ → ℕ} (hd : xs.Nodup)
    (hf : Function.Injective f) (hdis : ∀ i, f i ∉ xs) : Function.Injective (Support.prependStream xs f) := by
  intro i j he
  by_cases hi : i < xs.length <;> by_cases hj : j < xs.length
  · rw [Support.prependStream_apply_of_lt _ _ hi,Support.prependStream_apply_of_lt _ _ hj] at he
    exact congrArg Fin.val (List.nodup_iff_injective_get.mp hd he)
  · rw [Support.prependStream_apply_of_lt _ _ hi,Support.prependStream_apply_of_not_lt _ _ hj] at he
    exact (hdis _ (he ▸ List.get_mem xs ⟨i,hi⟩)).elim
  · rw [Support.prependStream_apply_of_not_lt _ _ hi,Support.prependStream_apply_of_lt _ _ hj] at he
    exact (hdis _ (he.symm ▸ List.get_mem xs ⟨j,hj⟩)).elim
  · rw [Support.prependStream_apply_of_not_lt _ _ hi,Support.prependStream_apply_of_not_lt _ _ hj] at he
    have := hf he; omega

theorem left_enumerates (p : PairedText K L) (hK : K.Infinite) :
    Function.Injective p.leftStream ∧ range p.leftStream = K := by
  refine ⟨prefix_injective p.left_nodup (p.shared_inj hK) (fun i => (p.shared_spec hK i).2.2.1),?_⟩
  have rangeTail : range p.shared = p.rest := Nat.range_nth_of_infinite (p.rest_inf hK)
  rw [leftStream, Support.range_prependStream,rangeTail]
  have hs : (p.left.toFinset : Set ℕ) ⊆ K := fun x h => p.left_mem x (List.mem_toFinset.mp h)
  exact Set.union_diff_cancel hs

theorem common_after (p : PairedText K L) (i : ℕ) (hi : p.right.length ≤ i) :
    p.rightStream i = p.leftStream i := by
  simp only [rightStream,leftStream,Support.prependStream,p.length_eq,dif_neg (Nat.not_lt.mpr hi)]

/-- Commit the same finite slice of the shared tail to each prefix. -/
theorem commit (p : PairedText K L) (hK : K.Infinite) (n : ℕ) :
    ∃ q : PairedText K L, q.right = p.right ++ textPrefix p.shared n := by
  let xs := textPrefix p.shared n
  have hx : xs.Nodup := by
    rw [List.nodup_iff_injective_get]
    intro a b he
    apply Fin.ext
    apply p.shared_inj hK
    simpa [xs,textPrefix] using he
  have hmem (x) (h : x ∈ xs) := (GenLimit.mem_textPrefix_iff.mp h)
  have spec (x) (h : x ∈ xs) : x ∈ K ∧ x ∈ L ∧ x ∉ p.left ∧ x ∉ p.right := by
    obtain ⟨i,_,rfl⟩ := hmem x h
    exact p.shared_spec hK i
  refine ⟨⟨p.left ++ xs,p.right ++ xs,by simp [p.length_eq],
    List.Nodup.append p.left_nodup hx (fun _ hl hr => (spec _ hr).2.2.1 hl),
    List.Nodup.append p.right_nodup hx (fun _ hl hr => (spec _ hr).2.2.2 hl),?_,?_,?_,?_⟩,rfl⟩
  · intro x hx; exact (List.mem_append.mp hx).elim (p.left_mem x) (fun h => (spec x h).1)
  · intro x hx; exact (List.mem_append.mp hx).elim (p.right_mem x) (fun h => (spec x h).2.1)
  · exact fun x h => List.mem_append_left _ (p.covers x h)
  · intro x hx hk
    exact List.mem_append.mpr ((List.mem_append.mp hx).imp_left fun h => p.overlap x h hk)

end PairedText
end GenLimit.PrivateLimit
