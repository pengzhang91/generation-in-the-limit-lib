import GenLimit.NoRegretLanguageGeneration.SharpnessProduct

namespace PredictionToGeneration.SharpnessProduct
open Classical
open scoped BigOperators

abbrev Candidates (q K : Nat) := Fin q → Finset (Fin K)
abbrev Counts (q K : Nat) := Fin q → Fin K → Nat

def Pool {q K : Nat} (S : Candidates q K) (v : Vector q K) : Prop := ∀ l, v l ∈ S l

def Small {q K : Nat} (m : Nat) (S : Candidates q K) (c : Counts q K) (l : Fin q) : Prop :=
  ∀ i ∈ S l, c l i < m

def Resolved {q K : Nat} (m : Nat) (S : Candidates q K) (c : Counts q K) (l : Fin q) : Prop :=
  ∃ i, S l = {i} ∧ m ≤ c l i

def Invariant {q K : Nat} (m : Nat) (S : Candidates q K) (c : Counts q K)
    (τ : Trajectory (Point q K)) : Prop :=
  (∀ l, 2^m ≤ SharpnessComponent.total (S l) (c l)) ∧
  (∀ v, Pool S v → Realizes (hypothesis v) τ) ∧
  (∀ v, Pool S v → (∑ l, c l (v l)) ≤ mistakes (hypothesis v) τ) ∧
  (∀ l, Small m S c l → ∀ i, Fresh τ (.inl (l,i)) → i ∈ S l)

noncomputable def normalize {q K : Nat} (m : Nat) (S : Candidates q K) (c : Counts q K) : Candidates q K :=
  fun l => if h : ∃ i ∈ S l, m ≤ c l i then {Classical.choose h} else S l

theorem normalize_subset {q K : Nat} (m : Nat) (S : Candidates q K) (c : Counts q K) (l : Fin q) :
    normalize m S c l ⊆ S l := by
  unfold normalize
  split
  · intro i hi
    have he := Finset.mem_singleton.mp hi
    subst i
    exact (Classical.choose_spec ‹∃ i ∈ S l, m ≤ c l i›).1
  · exact Finset.Subset.refl _

theorem normalize_dichotomy {q K : Nat} (m : Nat) (S : Candidates q K) (c : Counts q K) (l : Fin q) :
    Small m (normalize m S c) c l ∨ Resolved m (normalize m S c) c l := by
  by_cases hh : ∃ i ∈ S l, m ≤ c l i
  · exact Or.inr ⟨Classical.choose hh,by simp [normalize,hh],(Classical.choose_spec hh).2⟩
  · apply Or.inl
    intro i hi
    have hi' : i∈S l := by simpa [normalize,hh] using hi
    have hn : ¬m≤c l i := fun hm => hh ⟨i,hi',hm⟩
    omega

theorem normalize_small_eq {q K : Nat} (m : Nat) (S : Candidates q K) (c : Counts q K) (l : Fin q)
    (hs : Small m (normalize m S c) c l) : normalize m S c l = S l := by
  unfold normalize
  split
  · rename_i hh
    have hm := (Classical.choose_spec hh).2
    have hc := hs (Classical.choose hh) (by simp [normalize,hh])
    omega
  · rfl

theorem normalize_invariant {q K : Nat} (m : Nat) (S : Candidates q K) (c : Counts q K)
    (τ : Trajectory (Point q K)) (ha : Invariant m S c τ) : Invariant m (normalize m S c) c τ := by
  refine ⟨?_,?_,?_,?_⟩
  · intro l
    unfold normalize
    split
    · rename_i hh
      have hc := (Classical.choose_spec hh).2
      simpa [SharpnessComponent.total] using Nat.pow_le_pow_right (by decide : 1≤2) hc
    · exact ha.1 l
  · intro v hv
    exact ha.2.1 v (fun l => normalize_subset m S c l (hv l))
  · intro v hv
    exact ha.2.2.1 v (fun l => normalize_subset m S c l (hv l))
  · intro l hs i hf
    have he := normalize_small_eq m S c l hs
    have hs' : Small m S c l := by simpa [Small,he] using hs
    rw [he]
    exact ha.2.2.2 l hs' i hf

theorem pool_nonempty {q K : Nat} (m : Nat) (S : Candidates q K) (c : Counts q K)
    (hw : ∀ l, 2^m ≤ SharpnessComponent.total (S l) (c l)) : ∃ v, Pool S v := by
  have hs : ∀ l, (S l).Nonempty := by
    intro l
    by_contra he
    have he' := Finset.not_nonempty_iff_eq_empty.mp he
    have hh := hw l
    simp [he',SharpnessComponent.total] at hh
  exact ⟨fun l => Classical.choose (hs l),fun l => Classical.choose_spec (hs l)⟩

theorem realizes_positive (h : Hypothesis X) (τ : Trajectory X) (hr : Realizes h τ) :
    ∀ x ∈ demonstrations τ, h x = true := by
  induction τ with
  | nil => simp [demonstrations]
  | cons zx τ ih =>
    intro x hx
    simp only [demonstrations,List.map_cons,List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hr.1
    · exact ih hr.2 x hx

theorem candidate_fresh {q K : Nat} (m : Nat) (S : Candidates q K) (c : Counts q K)
    (τ : Trajectory (Point q K)) (ha : Invariant m S c τ) (l : Fin q) (i : Fin K) (hi : i∈S l) :
    Fresh τ (.inl (l,i)) := by
  obtain ⟨v,hv⟩ := pool_nonempty m S c ha.1
  let w := Function.update v l i
  have hw : Pool S w := by
    intro k
    by_cases hk : k=l
    · subst k; simpa [w] using hi
    · simpa [w,hk] using hv k
  intro hm
  have hp := realizes_positive _ _ (ha.2.1 w hw) _ hm
  simp [hypothesis,w] at hp

noncomputable def available {q K : Nat} (τ : Trajectory (Point q K)) : Finset (Fin q × Fin K) :=
  Finset.univ.filter (fun p => Fresh τ (.inl p))

theorem available_step {q K : Nat} (τ : Trajectory (Point q K)) (z : Point q K) (p : Fin q × Fin K) :
    available ((z,.inl p)::τ) = (available τ).erase p := by
  ext r
  simp [available,Fresh,demonstrations]



def removeCandidate {q K : Nat} (S : Candidates q K) (l : Fin q) (j : Fin K) : Candidates q K :=
  Function.update S l ((S l).erase j)

def increaseCount {q K : Nat} (c : Counts q K) (l : Fin q) (d : Fin K → Nat) : Counts q K :=
  Function.update c l (fun i => c l i + d i)

theorem removed_pool_subset {q K : Nat} (S : Candidates q K) (l : Fin q) (j : Fin K)
    (v : Vector q K) (hv : Pool (removeCandidate S l j) v) : Pool S v := by
  intro k
  by_cases hk : k=l
  · subst k
    exact Finset.mem_of_mem_erase (by simpa [removeCandidate] using hv l)
  · simpa [removeCandidate,hk] using hv k

theorem count_sum_update {q K : Nat} (c : Counts q K) (l : Fin q) (d : Fin K → Nat) (v : Vector q K) :
    (∑ k, increaseCount c l d k (v k)) = (∑ k, c k (v k)) + d (v l) := by
  have he (k : Fin q) : increaseCount c l d k (v k) = c k (v k) + if k=l then d (v l) else 0 := by
    by_cases hk : k=l <;> simp [increaseCount,hk]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

theorem progress_invariant {q K : Nat} (m : Nat) (S : Candidates q K) (c : Counts q K)
    (τ : Trajectory (Point q K)) (ha : Invariant m S c τ) (l : Fin q) (hs : Small m S c l)
    (j : Fin K) (z : Point q K) (d : Fin K → Nat)
    (hw : 2^m ≤ SharpnessComponent.total ((S l).erase j) (fun i => c l i+d i))
    (hloss : ∀ v, Pool (removeCandidate S l j) v → d (v l) ≤ loss (hypothesis v) z) :
    Invariant m (removeCandidate S l j) (increaseCount c l d) ((z,.inl (l,j))::τ) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro k
    by_cases hk : k=l
    · subst k; simpa [removeCandidate,increaseCount] using hw
    · simpa [removeCandidate,increaseCount,hk] using ha.1 k
  · intro v hv
    have hv' := removed_pool_subset S l j v hv
    have hvj : v l ≠ j := (Finset.mem_erase.mp (by simpa [removeCandidate] using hv l)).1
    exact ⟨by simp [hypothesis,hvj],ha.2.1 v hv'⟩
  · intro v hv
    rw [count_sum_update]
    have old := ha.2.2.1 v (removed_pool_subset S l j v hv)
    have inc := hloss v hv
    simp only [mistakes]
    omega
  · intro k hsmall i hf
    have hf' : Fresh τ (.inl (k,i)) := by
      intro hm
      exact hf (by simp [demonstrations] at hm ⊢; exact Or.inr hm)
    by_cases hk : k=l
    · subst k
      have hi := ha.2.2.2 l hs i hf'
      have hij : i≠j := by
        intro he
        subst i
        exact hf (by simp [demonstrations])
      simpa [removeCandidate] using Finset.mem_erase.mpr ⟨hij,hi⟩
    · have hs' : Small m S c k := by simpa [Small,removeCandidate,increaseCount,hk] using hsmall
      simpa [removeCandidate,hk] using ha.2.2.2 k hs' i hf'

theorem copy_invariant {q K : Nat} (m : Nat) (S : Candidates q K) (c : Counts q K)
    (τ : Trajectory (Point q K)) (ha : Invariant m S c τ) (z : Point q K)
    (hp : ∀ v, Pool S v → hypothesis v z = true) : Invariant m S c ((z,z)::τ) := by
  refine ⟨ha.1,?_,?_,?_⟩
  · intro v hv
    exact ⟨hp v hv,ha.2.1 v hv⟩
  · intro v hv
    have hh := ha.2.2.1 v hv
    simp only [mistakes]
    omega
  · intro l hs i hf
    apply ha.2.2.2 l hs i
    intro hm
    exact hf (by simp [demonstrations] at hm ⊢; exact Or.inr hm)

theorem double_remove {q K : Nat} (m : Nat) (S : Candidates q K) (c : Counts q K)
    (l : Fin q) (hs : Small m S c l) (j : Fin K) (hj : j∈S l)
    (hw : 2^m ≤ SharpnessComponent.total (S l) (c l)) :
    2^m ≤ SharpnessComponent.total ((S l).erase j) (fun i => c l i+1) := by
  have hsum : SharpnessComponent.total ((S l).erase j) (c l) + 2^c l j =
      SharpnessComponent.total (S l) (c l) := Finset.sum_erase_add _ _ hj
  have hp := SharpnessComponent.power_doubling_bound m (c l j) (hs j hj)
  have he : SharpnessComponent.total ((S l).erase j) (fun i => c l i+1) =
      2 * SharpnessComponent.total ((S l).erase j) (c l) := by
    simp [SharpnessComponent.total,Nat.pow_succ,Finset.mul_sum,Nat.mul_comm]
  rw [he]
  omega




theorem adversarial_move {q K : Nat} (m : Nat) (S : Candidates q K) (c : Counts q K)
    (τ : Trajectory (Point q K)) (ha : Invariant m S c τ)
    (hnorm : ∀ l, Small m S c l ∨ Resolved m S c l)
    (a : Fin q) (hsmall : Small m S c a) (z : Point q K) (hz : Fresh τ z) :
    ∃ p S' c', Fresh τ (.inl p) ∧ Invariant m S' c' ((z,.inl p)::τ) := by
  have negative (j : Fin K) (hj : j∈S a)
      (hneg : ∀ v, Pool (removeCandidate S a j) v → hypothesis v z = false) :
      ∃ p S' c', Fresh τ (.inl p) ∧ Invariant m S' c' ((z,.inl p)::τ) := by
    refine ⟨(a,j),removeCandidate S a j,increaseCount c a (fun _=>1),
      candidate_fresh m S c τ ha a j hj,?_⟩
    apply progress_invariant m S c τ ha a hsmall j z (fun _=>1)
      (double_remove m S c a hsmall j hj (ha.1 a))
    intro v hv
    simp [loss,hneg v hv]
  obtain ⟨v0,hv0⟩ := pool_nonempty m S c ha.1
  cases z with
  | inl p =>
    by_cases hl : Small m S c p.1
    · have hi := ha.2.2.2 p.1 hl p.2 hz
      obtain ⟨j,hj,hw⟩ := SharpnessComponent.response_preserves m (S p.1) (c p.1) hl (ha.1 p.1)
        (.inl p.2) (by intro i he; cases he; exact hi)
      let d := fun i => loss (SharpnessComponent.hypothesis i) (.inl p.2)
      refine ⟨(p.1,j),removeCandidate S p.1 j,increaseCount c p.1 d,
        candidate_fresh m S c τ ha p.1 j hj,?_⟩
      apply progress_invariant m S c τ ha p.1 hl j (.inl p) d
      · exact hw
      · intro v _
        simp [d,loss,hypothesis,SharpnessComponent.hypothesis]
    · obtain ⟨i,hS,_⟩ := (hnorm p.1).resolve_left hl
      by_cases hpi : p.2=i
      · apply negative (v0 a) (hv0 a)
        intro v hv
        have hvl : v p.1 = i := by
          have hh := removed_pool_subset S a (v0 a) v hv p.1
          simpa [hS] using hh
        simp [hypothesis,hvl,hpi]
      · refine ⟨p,S,c,hz,copy_invariant m S c τ ha (.inl p) ?_⟩
        intro v hv
        have hvl : v p.1 = i := by simpa [hS] using hv p.1
        simp [hypothesis,hvl,Ne.symm hpi]
  | inr p =>
    by_cases hp : Pool S p.1
    · apply negative (p.1 a) (hp a)
      intro v hv
      have hva : v a ≠ p.1 a := (Finset.mem_erase.mp (by simpa [removeCandidate] using hv a)).1
      have hvp : v ≠ p.1 := fun he => hva (congrFun he a)
      simp [hypothesis,hvp]
    · apply negative (v0 a) (hv0 a)
      intro v hv
      have hvp : v ≠ p.1 := fun he => hp (he ▸ removed_pool_subset S a (v0 a) v hv)
      simp [hypothesis,hvp]

/-- A completed coordinate vector witnesses all the charged mistakes at once. -/
theorem resolved_witness {q K : Nat} (m : Nat) (S : Candidates q K) (c : Counts q K)
    (τ : Trajectory (Point q K)) (ha : Invariant m S c τ)
    (hres : ∀ l, Resolved m S c l) : RealizableBad (H q K) (q*m) τ := by
  let v : Vector q K := fun l => Classical.choose (hres l)
  have hv : Pool S v := by
    intro l
    have hh := (Classical.choose_spec (hres l)).1
    rw [hh]
    exact Finset.mem_singleton.mpr rfl
  have hm : q*m ≤ ∑ l, c l (v l) := by
    calc
      q*m = ∑ _l : Fin q, m := by simp
      _ ≤ ∑ l, c l (v l) := Finset.sum_le_sum (fun l _ => (Classical.choose_spec (hres l)).2)
  exact ⟨hypothesis v,⟨v,rfl⟩,ha.2.1 v hv,Nat.le_trans hm (ha.2.2.1 v hv)⟩

/-- A nonempty product pool always leaves an omitted core point available. -/
theorem available_nonempty {q K : Nat} (hq : 1≤q) (m : Nat) (S : Candidates q K) (c : Counts q K)
    (τ : Trajectory (Point q K)) (ha : Invariant m S c τ) : (available τ).Nonempty := by
  obtain ⟨v,hv⟩ := pool_nonempty m S c ha.1
  let l : Fin q := ⟨0,by omega⟩
  exact ⟨(l,v l),by simp [available,candidate_fresh m S c τ ha l (v l) (hv l)]⟩

theorem product_forces_aux {q K : Nat} (hq : 1≤q) (m n : Nat)
    (S : Candidates q K) (c : Counts q K) (τ : Trajectory (Point q K))
    (ha : Invariant m S c τ) (hcard : (available τ).card ≤ n) :
    Forces (RealizableBad (H q K) (q*m)) n τ := by
  let S' := normalize m S c
  have ha' := normalize_invariant m S c τ ha
  have hnorm := normalize_dichotomy m S c
  by_cases hactive : ∃ a, Small m S' c a
  · obtain ⟨a,hs⟩ := hactive
    cases n with
    | zero =>
      have hn := Finset.card_pos.mpr (available_nonempty hq m S' c τ ha')
      omega
    | succ n =>
      intro z hz
      obtain ⟨p,S'',c',hp,ha''⟩ := adversarial_move m S' c τ ha' hnorm a hs z hz
      refine ⟨.inl p,hp,?_⟩
      apply product_forces_aux hq m n S'' c' ((z,.inl p)::τ) ha''
      rw [available_step]
      have hp' : p ∈ available τ := by simp [available,hp]
      have hc := Finset.card_erase_add_one hp'
      omega
  · have hres : ∀ l, Resolved m S' c l := by
      intro l
      exact (hnorm l).resolve_left (fun hs => hactive ⟨l,hs⟩)
    obtain ⟨h,hh,hr,hm⟩ := resolved_witness m S' c τ ha' hres
    exact SharpnessComponent.pad_witness (H q K) (uus q K) (q*m) n τ h hh hr hm
termination_by n

/-- Product lower bound, with the exact horizon in the manuscript. -/
theorem product_forces (q m : Nat) (hq : 1≤q) (hm : 1≤m) :
    MFForces (H q (2^m)) (2*q*(2^m-1)) (q*m) := by
  let S : Candidates q (2^m) := fun _ => Finset.univ
  let c : Counts q (2^m) := fun _ _ => 0
  have ha : Invariant m S c [] := by
    refine ⟨?_,?_,?_,?_⟩
    · intro l; simp [S,c,SharpnessComponent.total]
    · intro v _; trivial
    · intro v _; simp [c,mistakes]
    · intro l _ i _; simp [S]
  apply product_forces_aux hq m (2*q*(2^m-1)) S c [] ha
  have hK : 2≤2^m := by simpa using Nat.pow_le_pow_right (by decide : 1≤2) hm
  simp only [available,Fresh,demonstrations,List.map_nil,List.not_mem_nil,not_false_eq_true,Finset.filter_True,
    Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
  have hh := Nat.mul_le_mul_left q (show 2^m ≤ 2*(2^m-1) by omega)
  simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh

theorem product_lower (q m : Nat) (hq : 1≤q) (hm : 1≤m) :
    q*m ≤ MF (H q (2^m)) (2*q*(2^m-1)) := by
  let v : Vector q (2^m) := fun _ => ⟨0,by positivity⟩
  have hne : ∃ h, H q (2^m) h := ⟨hypothesis v,v,rfl⟩
  exact (mf_spec _ (uus _ _) hne _).2 _ (product_forces q m hq hm)

end PredictionToGeneration.SharpnessProduct


