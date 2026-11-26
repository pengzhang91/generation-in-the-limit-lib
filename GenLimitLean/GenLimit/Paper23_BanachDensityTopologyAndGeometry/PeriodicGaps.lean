import GenLimit.Paper23_BanachDensityTopologyAndGeometry.PeriodicLocks
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.WindowDensity
import Mathlib.Data.List.Range

/-! Unrestricted one-dimensional Banach-density obstruction (Overview
Theorem 2.2 and Corollary 4.2). A full round of residues can be entered
in increasing order after the descending sequence of locks is prepared.
The final target is ℕ and its presentation is injective. -/
namespace GenLimit.KleinbergWei.Banach.Adversary

open Filter Set
open scoped Classical ENNReal
noncomputable section

private def block (b k : ℕ) := (List.range k).map (b+·)

private theorem in_block {x b k : ℕ} : x ∈ block b k ↔ ∃ i < k, b+i=x := by simp [block]

def Filled (A : List ℕ → Finset ℕ) (k : ℕ) (q : List ℕ) : Prop :=
  ∃ b, 0 < b ∧ ∀ i < k, b+i ∈ q ∧ ∀ t ≤ q.length, b+i ∉ A (q.take t)

private theorem make_gap (A : List ℕ → Finset ℕ) (valid : ValidOn A periodicFamily) (start : List ℕ)
    (nd : start.Nodup) {k : ℕ} (hk : 0 < k) :
    ∃ q, start <+: q ∧ q.Nodup ∧ Filled A k q := by
  obtain ⟨p,ext,ndp,locked⟩ := locks_all A valid hk start nd
  let M := max (p.toFinset.sup id) ((Finset.range (p.length+1)).sup fun t => (A (p.take t)).sup id)
  let b := k*(M+1)
  have mb : M < b := by dsimp only [b]; nlinarith [Nat.mul_le_mul_right (M+1) hk]
  have early {x} (hx : x ∈ p) : x < b := (show x ≤ p.toFinset.sup id from Finset.le_sup (f := id) (List.mem_toFinset.mpr hx)).trans_lt
    ((le_max_left ..).trans_lt mb)
  have old {t x} (ht : t ≤ p.length) (hx : x ∈ A (p.take t)) : x < b :=
    (show x ≤ (A (p.take t)).sup id from Finset.le_sup (f := id) hx).trans_lt (
    (Finset.le_sup (f := fun t => (A (p.take t)).sup id) (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))).trans_lt
      ((le_max_right ..).trans_lt mb))
  have res {i} (hi : i < k) : (b+i)%k = i := by rw [show b=k*(M+1) from rfl,Nat.mul_add_mod,Nat.mod_eq_of_lt hi]
  have distinct (j : ℕ) : (p++block b j).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨ndp,List.nodup_range.map (fun a c eq => Nat.add_left_cancel eq),?_⟩
    intro x hx y hy eq
    obtain ⟨i,_,rfl⟩ := in_block.mp hy
    have := early hx; omega
  let q := p++block b k
  refine ⟨q,ext.trans (List.prefix_append ..),distinct _,b,by omega,?_⟩
  intro i hi
  refine ⟨List.mem_append_right _ (in_block.mpr ⟨i,hi,rfl⟩),?_⟩
  intro t ht eq
  by_cases before : t ≤ p.length
  · rw [show q.take t=p.take t from List.take_append_of_le_length before] at eq
    have := old before eq; omega
  · let r := t-p.length
    have bound : r ≤ k := by simp [q,block] at ht; dsimp [r]; omega
    have positive : 0 < r := by dsimp [r]; omega
    have eqp : q.take t = p++block b r := by
      simp [q,block,List.take_append,List.take_of_length_le (show p.length ≤ t by omega),
        ←List.map_take,List.take_range,show min (t-p.length) k=r from Nat.min_eq_left bound]
    rw [eqp] at eq
    have legal : Legal (level p k (r-1)) (p++block b r) := by
      refine ⟨distinct _,?_⟩
      intro x hx
      obtain hp | hb := List.mem_append.mp hx
      · exact Or.inl hp
      · obtain ⟨j,hj,rfl⟩ := in_block.mp hb; right
        rw [res (hj.trans_le bound)]; omega
    obtain ⟨inside,fresh⟩ := locked (r-1) (by omega) (p++block b r) (List.prefix_append ..) legal (b+i) eq
    rcases inside with prior | residue
    · have := early prior; omega
    · rw [res hi] at residue
      exact fresh (List.mem_append_right _ (in_block.mpr ⟨i,by omega,rfl⟩))

/-- Every valid history-dependent generator on the same countable family
has an injective presentation of ℕ on which its output misses arbitrarily
long intervals. -/
theorem periodic_holes (A : List ℕ → Finset ℕ) (valid : ValidOn A periodicFamily) :
    ∃ s : ℕ → ℕ, Function.Injective s ∧ range s = univ ∧
      ∃ T, ∀ k ≥ T, ∃ b, 0 < b ∧
        windowCount {x | ∃ t, x ∈ A (textPrefix s (t+1))} b k = 0 := by
  have init : Legal univ ([] : List ℕ) := ⟨by simp,by simp⟩
  have step (n : ℕ) (p : List ℕ) (_ : [] <+: p) (legal : Legal univ p) :
      ∃ q, p <+: q ∧ Legal univ q ∧ Filled A (n+1) q := by
    obtain ⟨q,ext,nd,gap⟩ := make_gap A valid p legal.1 (Nat.succ_pos n)
    exact ⟨q,ext,⟨nd,fun _ _ => trivial⟩,gap⟩
  obtain ⟨H,_,all,inj,filled⟩ := fair_chain univ infinite_univ [] init (fun n => Filled A (n+1)) step
  obtain ⟨T,ok⟩ := valid univ univ_member H.stream all inj
  let outputs := {x | ∃ t, x ∈ A (textPrefix H.stream (t+1))}
  refine ⟨H.stream,inj,all,T+1,?_⟩
  intro k large
  obtain ⟨b,hb,gap⟩ := filled (k-1)
  have index : k-1+1=k := by omega
  rw [index] at gap
  have empty : windowCount outputs b k = 0 := by
    unfold windowCount
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨bound,⟨t,hit⟩⟩ := Finset.mem_filter.mp hx
    obtain ⟨le,lt⟩ := Finset.mem_Ico.mp bound
    let i := x-b
    have eq : b+i=x := by dsimp [i]; omega
    obtain ⟨seen,no⟩ := gap i (by dsimp [i]; omega)
    by_cases before : t+1 ≤ (H.history k).length
    · have prefixEq : (H.history k).take (t+1) = textPrefix H.stream (t+1) := by
        rw [←H.textPrefix_stream k]
        simp [textPrefix,←List.map_take,List.take_range,Nat.min_eq_left before]
      exact no _ before (by rw [prefixEq,eq]; exact hit)
    · have was := (textPrefix_prefix H.stream (show (H.history k).length ≤ t+1 by omega)).subset
      have contained : b+i ∈ textPrefix H.stream (H.history k).length := by rw [H.textPrefix_stream]; exact seen
      have len := H.le_length k
      exact (ok (t+1) (by omega) x hit).2 (eq ▸ was contained)
  exact ⟨b,hb,empty⟩

theorem unrestricted_obstruction (A : List ℕ → Finset ℕ) (valid : ValidOn A periodicFamily) :
    ∃ s : ℕ → ℕ, Function.Injective s ∧ range s = univ ∧
      lowerBanachDensity {x | ∃ t, x ∈ A (textPrefix s (t+1))} = 0 := by
  obtain ⟨s,inj,all,T,holes⟩ := periodic_holes A valid
  refine ⟨s,inj,all,le_antisymm ?_ bot_le⟩
  change liminf (banachMinimum _) atTop ≤ 0
  refine liminf_le_of_frequently_le ?_ (isBoundedUnder_of ⟨0,fun _ => bot_le⟩)
  apply Eventually.frequently
  filter_upwards [eventually_ge_atTop (T+1)] with k large
  obtain ⟨b,hb,empty⟩ := holes k (by omega)
  unfold banachMinimum
  exact iInf_le_of_le b (by rw [if_pos (show 1 ≤ b by omega),windowRatio,if_neg (by omega : k ≠ 0),empty]; simp)

end
end GenLimit.KleinbergWei.Banach.Adversary
