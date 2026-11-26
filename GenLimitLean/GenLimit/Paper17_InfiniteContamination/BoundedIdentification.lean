import GenLimit.Paper17_InfiniteContamination.BoundedDisplacement
import GenLimit.Paper17_InfiniteContamination.EvenDensity
import GenLimit.Core.Text

/-! # Identification with bounded displacement (Theorem 7.6)

Each finite stage postpones its first unseen number until the identifier
guesses the corresponding punctured language. Filling the hole then restores
a permutation of the full initial segment. The resulting stream stays within
one position of the admissible upper rank at every round.
-/

namespace GenLimit.InfiniteContamination
open GenLimit.KleinbergWei

private def skipWord (m t : ℕ) : ℕ := if t < m then t else t+1

private def punctured (m : ℕ) : OrderedLanguage where
  carrier := {x | x ≠ m}
  enumeration := skipWord m
  enumeration_injective := by
    intro a b h
    unfold skipWord at h
    split_ifs at h <;> omega
  range_enumeration := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      change skipWord m t ≠ m
      unfold skipWord
      split <;> omega
    · intro h
      change x ≠ m at h
      by_cases hlt : x < m
      · exact ⟨x, if_pos hlt⟩
      · exact ⟨x-1, by simp [skipWord, show ¬ x-1 < m by omega]; omega⟩

def puncturedFamilyOrders : ℕ → OrderedLanguage
  | 0 => naturalOrder
  | m+1 => punctured m

private structure Stage where
  len : ℕ
  perm : Equiv.Perm ℕ
  fixed : ∀ i ≥ len, perm i = i
  near : ∀ i, perm i ≤ i+1

private def rotateInterval (m T : ℕ) (hm : m ≤ T) : Equiv.Perm ℕ where
  toFun i := if i < m then i else if i < T then i+1 else if i = T then m else i
  invFun j := if j < m then j else if j = m then T else if j ≤ T then j-1 else j
  left_inv := by intro i; dsimp; split_ifs <;> omega
  right_inv := by intro i; dsimp; split_ifs <;> omega

private def advance (q : Stage) (T : ℕ) (hT : q.len ≤ T) : Stage where
  len := T+1
  perm := (rotateInterval q.len T hT).trans q.perm
  fixed i hi := by
    change q.perm (if i < q.len then i else if i < T then i+1 else if i = T then q.len else i) = i
    simp [show ¬ i < q.len by omega, show ¬ i < T by omega, show i ≠ T by omega, q.fixed i (by omega)]
  near i := by
    change q.perm (if i < q.len then i else if i < T then i+1 else if i = T then q.len else i) ≤ i+1
    split_ifs with h₁ h₂ h₃
    · exact q.near _
    · rw [q.fixed _ (by omega)]
    · rw [q.fixed _ le_rfl]; omega
    · exact q.near _

private def delayed (q : Stage) (t : ℕ) := q.perm (skipWord q.len t)

private theorem delayed_presents (q : Stage) :
    Generic.Presents (delayed q) (punctured q.len).carrier := by
  ext x
  constructor
  · rintro ⟨t,rfl⟩
    change q.perm (skipWord q.len t) ≠ q.len
    intro h
    have e := q.perm.injective (h.trans (q.fixed q.len le_rfl).symm)
    have hmem : skipWord q.len t ∈ (punctured q.len).carrier :=
      (punctured q.len).range_enumeration ▸ Set.mem_range_self t
    exact hmem e
  · intro hx
    have h : q.perm.symm x ≠ q.len := by
      intro h
      apply hx
      rw [← q.perm.apply_symm_apply x, h, q.fixed q.len le_rfl]
    obtain ⟨t,ht⟩ := (show q.perm.symm x ∈ Set.range (punctured q.len).enumeration from
      (punctured q.len).range_enumeration.symm ▸ h)
    exact ⟨t, (congrArg q.perm ht).trans (q.perm.apply_symm_apply x)⟩

private theorem textPrefix_congr {s r : ℕ → ℕ} {t : ℕ} (h : ∀ k < t, s k = r k) :
    textPrefix s t = textPrefix r t := by
  simp only [textPrefix_eq_ofFn]
  congr 1
  funext i
  exact h i i.isLt

/-- No finite-history identifier, even one allowed arbitrary set-valued
hypotheses, succeeds on every exact bounded presentation of this one family. -/
theorem no_bounded_identifier (M : ℝ) (hM : 1 < M) :
    ¬∃ A : List ℕ → Set ℕ, ∀ i s, Function.Injective s →
      Generic.Presents s (puncturedFamilyOrders i).carrier →
      BoundedDisplacement (puncturedFamilyOrders i) s (puncturedFamilyOrders i).carrier M →
      ∃ T, ∀ t ≥ T, A (textPrefix s t) = (puncturedFamilyOrders i).carrier := by
  classical
  rintro ⟨A,hA⟩
  have stop (q : Stage) : ∃ T, q.len ≤ T ∧ A (textPrefix (delayed q) T) = (punctured q.len).carrier := by
    have hbd : BoundedDisplacement (punctured q.len) (delayed q) (punctured q.len).carrier M := by
      refine ⟨q.len,fun t ht ↦ ?_⟩
      let K := punctured q.len
      have hd : delayed q t = K.enumeration t := by
        change q.perm (skipWord q.len t) = skipWord q.len t
        apply q.fixed
        simp [skipWord, Nat.not_lt.mpr ht]; omega
      have hm : K.enumeration t ∈ K.carrier := K.range_enumeration ▸ Set.mem_range_self t
      rw [hd, canonicalRank_carrier K hm, K.enumeration_injective (enumeration_canonicalIndex _ hm)]
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr hM.le) (show 0 ≤ (t:ℝ)+1 by positivity)]
    obtain ⟨N,hN⟩ := hA (q.len+1) (delayed q)
      (q.perm.injective.comp (punctured q.len).enumeration_injective) (delayed_presents q) hbd
    exact ⟨max q.len N,le_max_left ..,hN _ (le_max_right ..)⟩
  let wait (q : Stage) := (stop q).choose
  have hw (q : Stage) := (stop q).choose_spec
  let st : ℕ → Stage := Nat.rec ⟨0,Equiv.refl _,fun _ _ ↦ rfl,fun i ↦ by simp⟩
    (fun _ q ↦ advance q (wait q) (hw q).1)
  have ltlen (i) : (st i).len < (st (i+1)).len := Nat.lt_succ_of_le (hw (st i)).1
  have mono : StrictMono (fun i ↦ (st i).len) := strictMono_nat_of_lt_succ ltlen
  have stable (i j : ℕ) (hij : i ≤ j) (k : ℕ) (hk : k < (st i).len) :
      (st j).perm k = (st i).perm k := by
    induction j, hij using Nat.le_induction with
    | base => rfl
    | succ j hj ih =>
      have hkj : k < (st j).len := hk.trans_le (mono.monotone hj)
      change (st j).perm (if k < (st j).len then k else _) = _
      simpa [hkj] using ih
  let s := fun k ↦ (st (k+1)).perm k
  have agree (i k : ℕ) (hk : k < (st i).len) : s k = (st i).perm k := by
    have hlen : k < (st (k+1)).len := Nat.lt_of_succ_le (mono.id_le _)
    rcases le_total (k+1) i with h | h
    · exact (stable _ _ h _ hlen).symm
    · exact stable _ _ h _ hk
  have hs : Function.Injective s := by
    intro x y he
    let i := max x y + 1
    have hlen := mono.id_le i
    apply (st i).perm.injective
    exact (agree i x (by dsimp [i] at *; omega)).symm.trans
      (he.trans (agree i y (by dsimp [i] at *; omega)))
  have hp : Generic.Presents s naturalOrder.carrier := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    let q := st (x+1)
    have hx : x < q.len := Nat.lt_of_succ_le (mono.id_le _)
    let k := q.perm.symm x
    have he : q.perm k = x := q.perm.apply_symm_apply _
    have hk : k < q.len := by
      by_contra! h
      have hh := q.fixed k h
      omega
    exact ⟨k,(agree (x+1) k hk).trans he⟩
  have hb : BoundedDisplacement naturalOrder s naturalOrder.carrier M := by
    obtain ⟨N,hN⟩ := exists_nat_gt (1/(M-1))
    refine ⟨N, fun n hn ↦ ?_⟩
    have hr : canonicalIndex naturalOrder (s n) = s n :=
      enumeration_canonicalIndex naturalOrder (Set.mem_univ _)
    rw [canonicalRank_carrier _ (Set.mem_univ _), hr]
    have hle : (s n : ℝ) ≤ n+1 := by exact_mod_cast (st (n+1)).near n
    have hn' : (N:ℝ) ≤ n := by exact_mod_cast hn
    have h1 := ((div_lt_iff₀ (by linarith : 0 < M-1)).mp hN).trans_le
      (mul_le_mul_of_nonneg_right hn' (by linarith))
    push_cast
    nlinarith
  obtain ⟨N,hN⟩ := hA 0 s hs hp hb
  let q := st N
  have hstop : N ≤ wait q := (mono.id_le N).trans (hw q).1
  have hpre : textPrefix s (wait q) = textPrefix (delayed q) (wait q) := by
    apply textPrefix_congr
    intro k hk
    rw [agree (N+1) k (by exact hk.trans (Nat.lt_succ_self _))]
    change q.perm (if k < q.len then k else if k < wait q then k+1 else _) = q.perm (skipWord q.len k)
    simp [skipWord,hk]
  have he := ((hw q).2).symm.trans (hpre ▸ hN _ hstop)
  have hm : q.len ∈ (punctured q.len).carrier := he.symm ▸ Set.mem_univ _
  exact hm rfl

end GenLimit.InfiniteContamination
