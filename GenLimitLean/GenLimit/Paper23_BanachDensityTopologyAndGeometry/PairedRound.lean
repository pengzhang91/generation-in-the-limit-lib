import Mathlib.Data.Fintype.Prod
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.AdversarialPrefixes

/-! A generator that must output unseen words can be prevented from
outputting both members of every pair in a fresh finite block. When its
current output lies in the block, present the mate immediately if possible.
The argument tracks outputs at all prefix lengths strictly below the current
length, so the fresh-output condition also covers the transition between rounds. -/
namespace GenLimit.KleinbergWei.Banach.Adversary
open Set
open scoped Classical
noncomputable section
variable {α ι : Type} [DecidableEq α]

def past (A : List α → α) (p : List α) : Finset α :=
  (Finset.range p.length).image fun t => A (p.take t)

theorem mem_past {A : List α → α} {p : List α} {x : α} :
    x ∈ past A p ↔ ∃ t < p.length, A (p.take t) = x := by simp [past]

private theorem past_push (A : List α → α) (p : List α) (x : α) :
    past A (p++[x]) = insert (A p) (past A p) := by
  ext y
  rw [mem_past, Finset.mem_insert, mem_past]
  simp only [List.length_append, List.length_singleton]
  constructor
  · rintro ⟨t,ht,h⟩
    rw [List.take_append_of_le_length (by omega : t ≤ p.length)] at h
    by_cases e : t = p.length
    · left; simpa [e] using h.symm
    · exact Or.inr ⟨t,by omega,h⟩
  · rintro (rfl | ⟨t,ht,h⟩)
    · exact ⟨p.length,by omega,by simp⟩
    · exact ⟨t,by omega,by rwa [List.take_append_of_le_length ht.le]⟩

omit [DecidableEq α] in
private theorem legal_push {K : Set α} {p : List α} {x : α}
    (hp : Legal K p) (hx : x ∈ K) (fresh : x ∉ p) : Legal K (p++[x]) := by
  refine ⟨List.nodup_append.mpr ⟨hp.1,by simp,?_⟩,?_⟩
  · intro z hz w hw e
    exact fresh ((e.trans (List.mem_singleton.mp hw)) ▸ hz)
  · intro z hz
    rcases List.mem_append.mp hz with old | added
    · exact hp.2 _ old
    · obtain rfl := List.mem_singleton.mp added; exact hx

/-- The extension enumerates the entire block, and at most one member of
each pair has been output before the end of the extension. -/
theorem paired_round [Fintype ι] (A : List α → α) (K : Set α) (p : List α)
    (hp : Legal K p) (locked : ∀ q, p <+: q → Legal K q → A q ∉ q)
    (put : Bool × ι ↪ α) (inside : ∀ bi, put bi ∈ K)
    (unused : ∀ bi, put bi ∉ past A p) :
    ∃ q, p <+: q ∧ Legal K q ∧ (∀ bi, put bi ∈ q) ∧
      ∀ i, put (false,i) ∈ past A q → put (true,i) ∉ past A q := by
  let F := Finset.univ.image put
  let missing (q : List α) := F \ q.toFinset
  have in_F (bi : Bool × ι) : put bi ∈ F := Finset.mem_image.mpr ⟨bi,Finset.mem_univ _,rfl⟩
  have fill (n : ℕ) (q : List α) (hn : (missing q).card = n)
      (ext : p <+: q) (legal : Legal K q)
      (mates : ∀ b i, put (b,i) ∈ past A q → put (!b,i) ∈ q)
      (single : ∀ i, put (false,i) ∈ past A q → put (true,i) ∉ past A q) :
      ∃ s, p <+: s ∧ Legal K s ∧ (∀ bi, put bi ∈ s) ∧
        ∀ i, put (false,i) ∈ past A s → put (true,i) ∉ past A s := by
    induction n using Nat.strong_induction_on generalizing q with
    | h n ih =>
      by_cases empty : missing q = ∅
      · refine ⟨q,ext,legal,?_,single⟩
        intro bi
        by_contra absent
        have h : put bi ∈ missing q := Finset.mem_sdiff.mpr ⟨in_F bi,by simpa using absent⟩
        simp [empty] at h
      obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr empty
      have pick : ∃ x ∈ missing q, ∀ b i, A q = put (b,i) → put (!b,i) ∈ q++[x] := by
        by_cases hit : ∃ bi, A q = put bi
        · obtain ⟨⟨b,i⟩,eq⟩ := hit
          by_cases seen : put (!b,i) ∈ q
          · refine ⟨v,hv,?_⟩
            intro c j e
            cases put.injective (eq.symm.trans e)
            exact List.mem_append_left _ seen
          · refine ⟨put (!b,i),Finset.mem_sdiff.mpr ⟨in_F _,by simpa using seen⟩,?_⟩
            intro c j e
            cases put.injective (eq.symm.trans e)
            simp
        · exact ⟨v,hv,fun b i e => (hit ⟨(b,i),e⟩).elim⟩
      obtain ⟨x,hx,respond⟩ := pick
      obtain ⟨inF,new⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨bi,_,eq⟩ := Finset.mem_image.mp inF
      have legal' := legal_push legal (eq ▸ inside bi) (by simpa using new)
      have fewer : (missing (q++[x])).card < n := by
        rw [←hn]
        apply Finset.card_lt_card
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.sdiff_subset_sdiff (Finset.Subset.refl _) ?_,?_⟩
        · intro z hz; simp_all
        · intro e
          have bad := e.symm ▸ hx
          exact (Finset.mem_sdiff.mp (show x ∈ missing (q++[x]) from bad)).2 (by simp)
      apply ih _ fewer (q++[x]) rfl (ext.trans (List.prefix_append ..)) legal'
      · intro b i hout
        rw [past_push,Finset.mem_insert] at hout
        exact hout.elim (fun e => respond b i e.symm) (fun h => List.mem_append_left _ (mates b i h))
      · intro i left right
        rw [past_push,Finset.mem_insert] at left right
        rcases left with l | l <;> rcases right with r | r
        · have impossible := congrArg Prod.fst (put.injective (l.trans r.symm))
          contradiction
        · exact locked _ ext legal (l ▸ mates true i r)
        · exact locked _ ext legal (r ▸ mates false i l)
        · exact single _ l r
  exact fill _ p rfl (List.prefix_refl _) hp
    (fun b i h => (unused (b,i) h).elim) (fun i h => (unused (false,i) h).elim)

end
end GenLimit.KleinbergWei.Banach.Adversary
