import GenLimit.Support.HistoryChainText
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.List.Nodup

/-! Fair chains of duplicate-free histories. On a fixed infinite language,
a rule that is eventually correct on every exact injective presentation
has a locking extension above every legal starting history. -/
namespace GenLimit.KleinbergWei.Banach.Adversary

open Set
open scoped Classical
noncomputable section

variable {α : Type}

def Legal (K : Set α) (xs : List α) := xs.Nodup ∧ ∀ x ∈ xs, x ∈ K

private theorem insert_one (K : Set α) (inf : K.Infinite) (n : α) (xs : List α) (hx : Legal K xs) :
    ∃ ys, Legal K ys ∧ xs <+: ys ∧ xs.length < ys.length ∧ (n ∈ K → n ∈ ys) := by
  obtain ⟨a,ha,hnew⟩ := inf.exists_notMem_finset xs.toFinset
  let v := if n ∈ K ∧ n ∉ xs then n else a
  have hv : v ∈ K ∧ v ∉ xs := by dsimp [v]; split <;> simp_all
  refine ⟨xs++[v],⟨?_,?_⟩,List.prefix_append ..,by simp,?_⟩
  · apply List.nodup_append.mpr
    refine ⟨hx.1,by simp,?_⟩
    intro x h y hy eq; simp only [List.mem_singleton] at hy; exact hv.2 ((eq.trans hy) ▸ h)
  · intro x; simp only [List.mem_append,List.mem_singleton]; rintro (h | rfl)
    · exact hx.2 x h
    · exact hv.1
  · intro h; by_cases present : n ∈ xs <;> simp_all [v]

/-- Fill in the n-th word if needed before making the n-th requested
extension. The limit is an exact injective presentation. -/
theorem fair_chain [Countable α] (K : Set α) (inf : K.Infinite) (xs : List α) (hx : Legal K xs)
    (R : ℕ → List α → Prop)
    (step : ∀ n p, xs <+: p → Legal K p → ∃ q, p <+: q ∧ Legal K q ∧ R n q) :
    ∃ H : Support.HistoryChain α, H.history 0 = xs ∧ range H.stream = K ∧
      Function.Injective H.stream ∧ (∀ n, R n (H.history (n+1))) := by
  haveI : Nonempty α := ⟨inf.nonempty.choose⟩
  obtain ⟨enum,onto⟩ := exists_surjective_nat α
  let State := {p : List α // xs <+: p ∧ Legal K p}
  have advance (n : ℕ) (p : State) : ∃ q : State, p.val <+: q.val ∧ p.val.length < q.val.length ∧
      (enum n ∈ K → enum n ∈ q.val) ∧ R n q.val := by
    obtain ⟨v,legal,ext,inc,cover⟩ := insert_one K inf (enum n) p.val p.property.2
    obtain ⟨q,more,valid,good⟩ := step n v (p.property.1.trans ext) legal
    exact ⟨⟨q,(p.property.1.trans ext).trans more,valid⟩,ext.trans more,inc.trans_le more.length_le,
      fun hn => more.subset (cover hn),good⟩
  let P : ℕ → State := Nat.rec ⟨xs,List.prefix_refl _,hx⟩ (fun n p => (advance n p).choose)
  have move n := (advance n (P n)).choose_spec
  change ∀ n, _ <+: (P (n+1)).val ∧ _ < (P (n+1)).val.length ∧
    (enum n ∈ K → enum n ∈ (P (n+1)).val) ∧ R n (P (n+1)).val at move
  let H : Support.HistoryChain α := {
    history := fun n => (P n).val
    prefix_succ := fun n => (move n).1
    le_length := fun n => by induction n with
      | zero => omega
      | succ n ih => exact Nat.succ_le_of_lt (ih.trans_lt (move n).2.1) }
  refine ⟨H,rfl,?_,?_,fun n => (move n).2.2.2⟩
  · ext x; constructor
    · rintro ⟨n,rfl⟩
      rw [H.stream_eq_get (n+1) n ((Nat.lt_succ_self n).trans_le (H.le_length _))]
      exact (P (n+1)).property.2.2 _ (List.get_mem ..)
    · intro h
      obtain ⟨i,rfl⟩ := onto x
      exact H.history_toFinset_subset_stream_range (i+1) (List.mem_toFinset.mpr ((move i).2.2.1 h))
  · intro a b eq
    let n := max a b+1
    have ha : a < (H.history n).length := (by dsimp [n]; omega : a < n).trans_le (H.le_length n)
    have hb : b < (H.history n).length := (by dsimp [n]; omega : b < n).trans_le (H.le_length n)
    have inj := List.nodup_iff_injective_get.mp (P n).property.2.1
    exact congrArg Fin.val (inj ((H.stream_eq_get n a ha).symm.trans (eq.trans (H.stream_eq_get n b hb))))

/-- Every presentation eventually satisfies a property tested on its
ordered prefix. A single legal extension then enforces the property
throughout its entire tree of legal continuations within K. -/
theorem lock [Countable α] (K : Set α) (inf : K.Infinite) (test : List α → Prop)
    (valid : ∀ s : ℕ → α, range s = K → Function.Injective s →
      ∃ T, ∀ t ≥ T, test (textPrefix s t))
    (xs : List α) (hx : Legal K xs) :
    ∃ p, xs <+: p ∧ Legal K p ∧ ∀ q, p <+: q → Legal K q → test q := by
  by_contra h
  push_neg at h
  have step (n : ℕ) (p : List α) (ext : xs <+: p) (hp : Legal K p) :
      ∃ q, p <+: q ∧ Legal K q ∧ ¬test q := h p ext hp
  obtain ⟨H,_,eq,inj,fails⟩ := fair_chain K inf xs hx (fun _ q => ¬test q) step
  obtain ⟨T,ok⟩ := valid H.stream eq inj
  apply fails T
  rw [←H.textPrefix_stream (T+1)]
  exact ok _ ((Nat.le_succ T).trans (H.le_length _))

end
end GenLimit.KleinbergWei.Banach.Adversary
