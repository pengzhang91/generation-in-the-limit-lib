import GenLimit.Paper23_BanachDensityTopologyAndGeometry.AdversarialPrefixes
import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Max

/-! A countable hard family for the unrestricted Banach-density conclusion.
At a fixed modulus k, the adversary locks a generator successively on
nested languages admitting residues below each of the k possible cutoffs.
Finite exceptions absorb the history at the time of each lock. -/
namespace GenLimit.KleinbergWei.Banach.Adversary

open Set
open scoped Classical
noncomputable section

def level (p : List ℕ) (k j : ℕ) : Set ℕ := {x | x ∈ p ∨ x%k ≤ j}

def periodicFamily : Set (Set ℕ) := range fun a : List ℕ × ℕ × ℕ => level a.1 (a.2.1+1) a.2.2

theorem periodic_countable : periodicFamily.Countable := countable_range _

theorem level_member (p : List ℕ) {k : ℕ} (hk : 0 < k) (j : ℕ) : level p k j ∈ periodicFamily :=
  ⟨(p,k-1,j),by simp [Nat.sub_add_cancel hk]⟩

theorem univ_member : (univ : Set ℕ) ∈ periodicFamily := by
  refine ⟨([],0,0),?_⟩
  ext x; simp [level,Nat.mod_one]

theorem level_infinite (p : List ℕ) {k : ℕ} (hk : 0 < k) (j : ℕ) : (level p k j).Infinite := by
  apply (infinite_range_of_injective (f := fun n : ℕ => k*n) (fun a b eq => Nat.eq_of_mul_eq_mul_left hk eq)).mono
  rintro _ ⟨n,rfl⟩
  exact Or.inr (by simp)

/-- The sole hypothesis on the generator used below is eventual
membership and avoidance of the observed inputs, on exact injective texts. -/
def ValidOn (A : List ℕ → Finset ℕ) (C : Set (Set ℕ)) :=
  ∀ K ∈ C, ∀ s : ℕ → ℕ, range s = K → Function.Injective s →
    ∃ T, ∀ t ≥ T, ∀ x ∈ A (textPrefix s t), x ∈ K ∧ x ∉ textPrefix s t

def Secured (A : List ℕ → Finset ℕ) (k : ℕ) (p : List ℕ) (j : ℕ) :=
  ∀ q, p <+: q → Legal (level p k j) q → ∀ x ∈ A q, x ∈ level p k j ∧ x ∉ q

private theorem level_eq {p v : List ℕ} (ext : p <+: v) {k i j : ℕ}
    (small : Legal (level p k i) v) (h : i ≤ j) : level v k j = level p k j := by
  ext x; constructor
  · rintro (mem | res)
    · exact (small.2 x mem).imp_right (fun le => le.trans h)
    · exact Or.inr res
  · exact fun mem => mem.imp_left (fun hx => ext.subset hx)

private theorem lock_level (A : List ℕ → Finset ℕ) (valid : ValidOn A periodicFamily) {k : ℕ} (hk : 0 < k)
    (i : ℕ) (p : List ℕ) (nd : p.Nodup) :
    ∃ v, p <+: v ∧ v.Nodup ∧ Secured A k v i ∧ ∀ j ≥ i, Secured A k p j → Secured A k v j := by
  let L := level p k i
  have base : Legal L p := ⟨nd,fun _ mem => Or.inl mem⟩
  obtain ⟨v,ext,vin,locked⟩ := lock L (level_infinite p hk i) (fun q => ∀ x ∈ A q, x ∈ L ∧ x ∉ q)
    (valid L (level_member p hk i)) p base
  refine ⟨v,ext,vin.1,?_,?_⟩
  · intro q hq legal; have same := level_eq ext vin le_rfl
    rw [same] at legal ⊢; exact locked q hq legal
  · intro j hj prev q hq legal; have same := level_eq ext vin hj
    rw [same] at legal ⊢; exact prev q (ext.trans hq) legal

private theorem locks_suffix (A : List ℕ → Finset ℕ) (valid : ValidOn A periodicFamily) {k : ℕ} (hk : 0 < k)
    (start : List ℕ) (nd : start.Nodup) (n : ℕ) (hn : n ≤ k) :
    ∃ p, start <+: p ∧ p.Nodup ∧ ∀ j, k-n ≤ j → j < k → Secured A k p j := by
  induction n with
  | zero => exact ⟨start,List.prefix_refl _,nd,fun j hj lt => by omega⟩
  | succ n ih =>
    obtain ⟨p,ext,legal,prev⟩ := ih (by omega)
    let i := k-(n+1)
    obtain ⟨v,hv,ndv,here,later⟩ := lock_level A valid hk i p legal
    refine ⟨v,ext.trans hv,ndv,?_⟩
    intro j hj lt
    by_cases h : j=i
    · simpa only [h] using here
    · exact later j hj (prev j (by dsimp [i] at h; omega) lt)

theorem locks_all (A : List ℕ → Finset ℕ) (valid : ValidOn A periodicFamily) {k : ℕ} (hk : 0 < k)
    (start : List ℕ) (nd : start.Nodup) :
    ∃ p, start <+: p ∧ p.Nodup ∧ ∀ j < k, Secured A k p j := by
  simpa using locks_suffix A valid hk start nd k le_rfl

end
end GenLimit.KleinbergWei.Banach.Adversary
