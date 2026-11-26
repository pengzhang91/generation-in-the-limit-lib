import GenLimit.Core.NaturalDensity
import GenLimit.Core.Text
import Mathlib.Data.Nat.Sqrt

/-! # The upper-density obstruction in Theorem 3.3
On ordinary turns, the adversary enumerates the first rank unused by either
player. On catch-up turn j it enumerates the first rank missing from its own
text, after every rank below j² has been used. This makes the presentation
complete, and only square-root many exceptional turns can contribute a new
output below any given rank. -/
namespace GenLimit.KleinbergWei.PartialEnumeration.Sharpness
open Filter Set
open scoped Topology Classical

private def exists_missing (S : Finset ℕ) : ∃ x, x ∉ S :=
  ⟨S.sup id + 1,fun h ↦ Nat.not_succ_le_self _ (Finset.le_sup (f := id) h)⟩

noncomputable def firstMissing (S : Finset ℕ) := Nat.find (exists_missing S)

theorem firstMissing_notMem (S : Finset ℕ) : firstMissing S ∉ S := Nat.find_spec (exists_missing S)

theorem firstMissing_le {S : Finset ℕ} {x : ℕ} (h : x ∉ S) : firstMissing S ≤ x :=
  Nat.find_min' _ h

theorem firstMissing_mono {S T : Finset ℕ} (h : S ⊆ T) : firstMissing S ≤ firstMissing T :=
  firstMissing_le (fun hm ↦ firstMissing_notMem _ (h hm))

theorem firstMissing_lt {S T : Finset ℕ} (h : S ⊆ T) (hm : firstMissing S ∈ T) :
    firstMissing S < firstMissing T :=
  lt_of_le_of_ne (firstMissing_mono h) (fun he ↦ firstMissing_notMem _ (he ▸ hm))

structure Position where
  history : List ℕ
  outputs : Finset ℕ
  catchups : ℕ

def Position.used (p : Position) := p.history.toFinset ∪ p.outputs
noncomputable def Position.frontier (p : Position) := firstMissing p.used
abbrev Position.special (p : Position) := p.catchups * p.catchups ≤ p.frontier

noncomputable def Position.play (p : Position) : ℕ :=
  if p.special then firstMissing p.history.toFinset else p.frontier

noncomputable def advance (G : List ℕ → ℕ) (p : Position) : Position :=
  let h := p.history ++ [p.play]
  ⟨h,insert (G h) p.outputs,if p.special then p.catchups+1 else p.catchups⟩

noncomputable def run (G : List ℕ → ℕ) : ℕ → Position
  | 0 => ⟨[],∅,0⟩
  | n+1 => advance G (run G n)

noncomputable def stream (G : List ℕ → ℕ) (n : ℕ) := (run G n).play
noncomputable def output (G : List ℕ → ℕ) (n : ℕ) := G ((run G (n+1)).history)

theorem history_eq (G : List ℕ → ℕ) (n : ℕ) : (run G n).history = textPrefix (stream G) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (run G n).history ++ [stream G n] = _
    rw [ih,GenLimit.textPrefix_succ]

private theorem history_step (G : List ℕ → ℕ) (p : Position) :
    (advance G p).history.toFinset = insert p.play p.history.toFinset := by
  ext; simp [advance,or_comm]

private theorem used_step (G : List ℕ → ℕ) (p : Position) : p.used ⊆ (advance G p).used := by
  rw [Position.used,Position.used,history_step]
  exact Finset.union_subset_union (Finset.subset_insert _ _) (Finset.subset_insert _ _)

private theorem play_mem (G : List ℕ → ℕ) (p : Position) : p.play ∈ (advance G p).used := by
  exact Finset.mem_union_left _ (history_step G p ▸ Finset.mem_insert_self _ _)

private theorem frontier_mono (G : List ℕ → ℕ) :
    Monotone (fun t ↦ (run G t).frontier) := monotone_nat_of_le_succ (fun n ↦
      firstMissing_mono (used_step G (run G n)))

private theorem catch_mono (G : List ℕ → ℕ) : Monotone (fun t ↦ (run G t).catchups) :=
  monotone_nat_of_le_succ (fun n ↦ by simp [run,advance]; split <;> omega)

private theorem elapsed (G : List ℕ → ℕ) (t : ℕ) :
    t ≤ (run G t).catchups + (run G t).frontier := by
  induction t with
  | zero => omega
  | succ n ih =>
    let p := run G n
    have mono : p.frontier ≤ (run G (n+1)).frontier := frontier_mono G (Nat.le_succ n)
    by_cases h : p.special
    · have hc : (run G (n+1)).catchups = p.catchups + 1 := by change (if p.special then _ else _) = _; rw [if_pos h]
      change n ≤ p.catchups + p.frontier at ih
      omega
    · have inc := firstMissing_lt (used_step G p) (show firstMissing p.used ∈ (advance G p).used by
        exact (show p.play = firstMissing p.used by unfold Position.play; rw [if_neg h]; rfl) ▸ play_mem G p)
      have hc : (run G (n+1)).catchups = p.catchups := by change (if p.special then _ else _) = _; rw [if_neg h]
      change p.frontier < (run G (n+1)).frontier at inc
      change n ≤ p.catchups + p.frontier at ih
      omega

private theorem catches_unbounded (G : List ℕ → ℕ) (m : ℕ) : ∃ t, m ≤ (run G t).catchups := by
  by_contra! bounded
  let N := m*m+m
  have special (t : ℕ) (ht : N ≤ t) : (run G t).special := by
    have h := elapsed G t
    have b := bounded t
    apply (Nat.mul_le_mul b.le b.le).trans
    dsimp [N] at ht
    omega
  have increments (i : ℕ) : i ≤ (run G (N+i)).catchups := by
    induction i with
    | zero => omega
    | succ i ih =>
      have h := special (N+i) (Nat.le_add_right _ _)
      change i+1 ≤ (if (run G (N+i)).special then _ else _)
      rw [if_pos h]
      exact Nat.succ_le_succ ih
  exact (bounded (N+m)).not_ge (increments m)

private theorem catch_le_missing (G : List ℕ → ℕ) (t : ℕ) :
    (run G t).catchups ≤ firstMissing (run G t).history.toFinset := by
  induction t with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    let p := run G n
    rw [run,history_step]
    change (if p.special then p.catchups+1 else p.catchups) ≤ firstMissing (insert p.play p.history.toFinset)
    change p.catchups ≤ _ at ih
    by_cases h : p.special
    · rw [if_pos h]
      apply Nat.succ_le_of_lt (ih.trans_lt (firstMissing_lt (Finset.subset_insert _ _) ?_))
      exact Finset.mem_insert.mpr (Or.inl (by unfold Position.play; rw [if_pos h]))
    · rw [if_neg h]
      exact ih.trans (firstMissing_mono (Finset.subset_insert _ _))

theorem presents (G : List ℕ → ℕ) : Set.range (stream G) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨t,ht⟩ := catches_unbounded G (x+1)
  have hmem : x ∈ (run G t).history.toFinset := by
    by_contra h
    have := (catch_le_missing G t).trans (firstMissing_le h)
    omega
  rw [history_eq,List.mem_toFinset] at hmem
  obtain ⟨i,_,hi⟩ := mem_textPrefix_iff.mp hmem
  exact ⟨i,hi⟩

private theorem shown_fresh (G : List ℕ → ℕ) (t : ℕ) : stream G t ∉ (run G t).history.toFinset := by
  let p := run G t
  change p.play ∉ p.history.toFinset
  unfold Position.play
  split
  · exact firstMissing_notMem _
  · exact fun h ↦ firstMissing_notMem p.used (Finset.mem_union_left _ h)

theorem stream_injective (G : List ℕ → ℕ) : Function.Injective (stream G) := by
  have h (i j : ℕ) (hl : i < j) : stream G i ≠ stream G j := by
    intro he
    apply shown_fresh G j
    rw [history_eq,List.mem_toFinset,mem_textPrefix_iff]
    exact ⟨i,hl,he⟩
  intro i j he
  rcases lt_trichotomy i j with hl | he' | hl
  · exact (h _ _ hl he).elim
  · exact he'
  · exact (h _ _ hl he.symm).elim

theorem output_mem (G : List ℕ → ℕ) (t x : ℕ) :
    x ∈ (run G t).outputs ↔ ∃ i < t, output G i = x := by
  induction t with
  | zero => simp [run]
  | succ n ih =>
    change x ∈ insert (output G n) (run G n).outputs ↔ _
    rw [Finset.mem_insert,ih]
    constructor
    · rintro (rfl | ⟨i,hi,he⟩)
      · exact ⟨n,Nat.lt_succ_self _,rfl⟩
      · exact ⟨i,hi.trans (Nat.lt_succ_self _),he⟩
    · rintro ⟨i,hi,he⟩
      rcases (Nat.lt_succ_iff.mp hi).lt_or_eq with hl | rfl
      · exact Or.inr ⟨_,hl,he⟩
      · exact Or.inl he.symm

private noncomputable def firstTime (G : List ℕ → ℕ) (x : ℕ) : ℕ := by
  classical
  exact if hx : x ∈ Set.range (output G) then Nat.find hx else 0

private theorem time_spec (G : List ℕ → ℕ) {x} (hx : x ∈ Set.range (output G)) :
    output G (firstTime G x) = x ∧ ∀ i < firstTime G x, output G i ≠ x := by
  classical
  simp only [firstTime,dif_pos hx]
  exact ⟨Nat.find_spec hx,fun _ hi ↦ Nat.find_min hx hi⟩

/-- A valid generator never returns a previously presented string after its
finite burn-in. This weaker assumption suffices for the upper bound. -/
def FreshAfter (G : List ℕ → ℕ) (T : ℕ) :=
  ∀ t ≥ T, ∀ i ≤ t, stream G i ≠ output G t

private theorem first_unused (G : List ℕ → ℕ) {T x} (hf : FreshAfter G T)
    (hx : x ∈ Set.range (output G)) (ht : T ≤ firstTime G x) :
    (run G (firstTime G x)).frontier ≤ x := by
  apply firstMissing_le
  intro hm
  rcases Finset.mem_union.mp hm with hi | ho
  · rw [history_eq,List.mem_toFinset,mem_textPrefix_iff] at hi
    obtain ⟨i,hi,he⟩ := hi
    exact hf _ ht i hi.le (he.trans (time_spec G hx).1.symm)
  · obtain ⟨i,hi,he⟩ := (output_mem ..).mp ho
    exact (time_spec G hx).2 i hi he

private theorem ordinary_complement (G : List ℕ → ℕ) {T t} (hf : FreshAfter G T) (ht : T ≤ t)
    (hn : ¬ (run G t).special) : stream G t ∉ Set.range (output G) := by
  rintro ⟨i,he⟩
  rcases lt_or_ge i t with hl | hl
  · have hm := (output_mem G t _).mpr ⟨i,hl,he⟩
    have hp : stream G t = firstMissing (run G t).used := by
      unfold stream Position.play; rw [if_neg hn]; rfl
    exact firstMissing_notMem _ (hp ▸ Finset.mem_union_right (run G t).history.toFinset hm)
  · exact hf i (ht.trans hl) t hl he.symm

theorem special_counts_injective (G : List ℕ → ℕ) :
    Set.InjOn (fun t ↦ (run G t).catchups) {t | (run G t).special} := by
  have inc {a b} (hab : a < b) (ha : (run G a).special) : (run G a).catchups < (run G b).catchups := by
    have hh : (run G (a+1)).catchups = (run G a).catchups + 1 := by
      change (if (run G a).special then _ else _) = _; rw [if_pos ha]
    have hinc : (run G a).catchups < (run G (a+1)).catchups := hh.symm ▸ Nat.lt_succ_self _
    exact hinc.trans_le (catch_mono G hab)
  intro a ha b hb he
  rcases lt_trichotomy a b with hl | h | hl
  · exact ((inc hl ha).ne he).elim
  · exact h
  · exact ((inc hl hb).ne he.symm).elim

/-- The counting estimate before taking the density limit. The ordinary
round is charged to a distinct smaller element outside the entire output
range. A special round is charged to its unique catch-up counter. -/
theorem prefix_bound (G : List ℕ → ℕ) (T : ℕ) (hf : FreshAfter G T) (n : ℕ) :
    2 * ((Finset.range n).filter (fun x ↦ x ∈ Set.range (output G))).card ≤ n + T + n.sqrt + 1 := by
  classical
  let O := Set.range (output G)
  let S := (Finset.range n).filter (fun x ↦ x ∈ O)
  let V := (Finset.range n) \ S
  let target := ((Finset.range T).disjSum (Finset.range (n.sqrt+1))).disjSum V
  let time := firstTime G
  let charge (x : ℕ) : (ℕ ⊕ ℕ) ⊕ ℕ :=
    if time x < T then .inl (.inl (time x))
    else if (run G (time x)).special then .inl (.inr (run G (time x)).catchups)
    else .inr (stream G (time x))
  have mem (x : ℕ) (hx : x ∈ S) : charge x ∈ target := by
    obtain ⟨hn,ho⟩ := Finset.mem_filter.mp hx
    have hxn := Finset.mem_range.mp hn
    change x ∈ O at ho
    by_cases he : time x < T
    · simpa [charge,he,target] using he
    have ht := Nat.le_of_not_gt he
    have small := (first_unused G hf ho ht).trans_lt hxn
    by_cases hs : (run G (time x)).special
    · have hc : (run G (time x)).catchups ≤ n.sqrt := Nat.le_sqrt.mpr (hs.trans small.le)
      simpa [charge,he,hs,target] using Nat.lt_succ_of_le hc
    · have hplay : stream G (time x) = (run G (time x)).frontier := by
        unfold stream Position.play; rw [if_neg hs]
      have hc : stream G (time x) ∈ V := Finset.mem_sdiff.mpr
        ⟨Finset.mem_range.mpr (hplay ▸ small),fun h ↦ ordinary_complement G hf ht hs (Finset.mem_filter.mp h).2⟩
      simpa [charge,he,hs,target] using hc
  have inj : Set.InjOn charge (↑S : Set ℕ) := by
    intro x hx y hy h
    have recover {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S) (ht : time x = time y) : x = y :=
      (time_spec G (Finset.mem_filter.mp hx).2).1.symm.trans
        ((congrArg (output G) ht).trans (time_spec G (Finset.mem_filter.mp hy).2).1)
    by_cases ex : time x < T <;> by_cases ey : time y < T <;>
      by_cases sx : (run G (time x)).special <;> by_cases sy : (run G (time y)).special <;>
      simp [charge,ex,ey,sx,sy] at h
    all_goals first | exact recover hx hy h | exact recover hx hy (special_counts_injective G sx sy h) |
      exact recover hx hy (stream_injective G h)
  have card := Finset.card_le_card_of_injOn charge mem inj
  have decomp : V.card + S.card = n := by
    rw [show V.card = (Finset.range n).card - S.card from Finset.card_sdiff_of_subset (Finset.filter_subset ..)]
    have le : S.card ≤ (Finset.range n).card := Finset.card_le_card (Finset.filter_subset ..)
    simp at le ⊢
    omega
  simp only [target,Finset.card_disjSum,Finset.card_range] at card
  change 2*S.card ≤ _
  omega

end GenLimit.KleinbergWei.PartialEnumeration.Sharpness
