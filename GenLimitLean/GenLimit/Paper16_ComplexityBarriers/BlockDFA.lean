import GenLimit.Paper16_ComplexityBarriers.BinaryBlocks
import Mathlib.Computability.DFA
import Mathlib.Data.List.Infix

/-! # Small deterministic binary automata for the counter languages

During an address the state stores the remaining suffix of the monitored
address, the comparison so far, and the counter. At the free bit it updates
the counter and returns to the beginning of the address. -/
namespace GenLimit.ComplexityBarriers.Blocks
open List
open scoped Classical
noncomputable section

def DFAAtMost (s : ℕ) (L : Set (List Bool)) :=
  ∃ q ≤ s, ∃ M : DFA Bool (Fin q), M.accepts = L

private def cmpBit : Bool → Bool → Ordering
  | false,true => .lt
  | true,false => .gt
  | _,_ => .eq

private def combine : Ordering → Ordering → Ordering
  | .eq,b => b
  | a,_ => a

private def comparePart (o : Ordering) : List Bool → List Bool → Ordering
  | a::as,b::bs => comparePart (combine o (cmpBit a b)) as bs
  | _,_ => o

private theorem compare_decided (x y : List Bool) (o : Ordering) (ho : o ≠ .eq) :
    comparePart o x y = o := by
  induction x generalizing y with
  | nil => rfl
  | cons a x ih => cases y with
    | nil => rfl
    | cons b y => cases o <;> simp_all [comparePart,combine]

private theorem compare_full (x y : List Bool) (h : x.length=y.length) :
    comparePart .eq x y = if x<y then .lt else if x=y then .eq else .gt := by
  induction x generalizing y with
  | nil => have := List.length_eq_zero_iff.mp h.symm; subst y; simp [comparePart]
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      have hh : x.length=y.length := by simpa using h
      cases a <;> cases b <;> simp [comparePart,combine,cmpBit,compare_decided,ih y hh,List.cons_lt_cons_iff]

private abbrev Tails (d : Address ℓ) := ↥d.val.tails.toFinset
private abbrev State (n : ℕ) (d : Address ℓ) := Option (Tails d × Ordering × Fin (n+1))

private def cursor (d : Address ℓ) (x : List Bool) (h : x <:+ d.val) : Tails d :=
  ⟨x,List.mem_toFinset.mpr ((List.mem_tails ..).mpr h)⟩

private def first (d : Address ℓ) := cursor d d.val List.suffix_rfl

private def updateCount (n : ℕ) (o : Ordering) (c : Fin (n+1)) : Option (Fin (n+1)) :=
  match o with
  | .lt => some 0
  | .eq => if h : c.val < n then some ⟨c.val+1,by omega⟩ else none
  | .gt => some c

private def fresh (d : Address ℓ) (c : Fin (n+1)) : State n d := some (first d,.eq,c)

private def advance (n : ℕ) (d : Address ℓ) : State n d → Bool → State n d
  | none,_ => none
  | some (⟨[],_⟩,o,c),_ => (updateCount n o c).bind (fresh d)
  | some (⟨b::bs,h⟩,o,c),a =>
    some (cursor d bs ((List.suffix_cons _ _).trans ((List.mem_tails ..).mp (List.mem_toFinset.mp h))),
      combine o (cmpBit a b),c)

private def machine (n : ℕ) (d : Address ℓ) : DFA Bool (State n d) where
  step := advance n d
  start := fresh d 0
  accept := {s | ∃ c, s=fresh d c}

private theorem eval_dead (n : ℕ) (d : Address ℓ) (w : List Bool) :
    (machine n d).evalFrom none w = none := by
  induction w with
  | nil => rfl
  | cons a w ih => exact ih

private theorem eval_partial (n : ℕ) (d : Address ℓ) (c : Fin (n+1))
    (u v : List Bool) (hv : v <:+ d.val) (hlen : u.length ≤ v.length) (o : Ordering) :
    (machine n d).evalFrom (some (cursor d v hv,o,c)) u =
      some (cursor d (v.drop u.length) ((List.drop_suffix ..).trans hv),comparePart o u v,c) := by
  induction u generalizing v o with
  | nil => rfl
  | cons a u ih =>
    cases v with
    | nil => simp at hlen
    | cons b v =>
      exact ih v ((List.suffix_cons _ _).trans hv) (by simpa using hlen) (combine o (cmpBit a b))

private theorem update_tick (n : ℕ) (d e : Address ℓ) (c : Fin (n+1)) :
    (updateCount n (comparePart .eq e.val d.val) c).map Fin.val = tick n d e c.val := by
  rw [compare_full _ _ (e.property.trans d.property.symm)]
  unfold tick
  have hlt : (e < d) ↔ e.val < d.val := Iff.rfl
  simp only [hlt]
  by_cases hh : e.val < d.val
  · simp [hh,updateCount]
  · by_cases he : e=d
    · subst e; simp [updateCount]
    · have hv : e.val ≠ d.val := fun h ↦ he (Subtype.ext h)
      simp [hh,he,hv,updateCount]

private theorem advance_empty (n : ℕ) (d : Address ℓ) (s : Tails d) (hs : s.val = [])
    (o : Ordering) (c : Fin (n+1)) (b : Bool) :
    advance n d (some (s,o,c)) b = (updateCount n o c).bind (fresh d) := by
  obtain ⟨_,hs'⟩ := s
  subst_vars
  rfl

private theorem eval_token (n : ℕ) (d : Address ℓ) (c : Fin (n+1)) (t : Token ℓ) :
    (machine n d).evalFrom (fresh d c) (bits t) =
      (updateCount n (comparePart .eq t.1.val d.val) c).bind (fresh d) := by
  rw [bits,DFA.evalFrom_of_append]
  change (machine n d).evalFrom ((machine n d).evalFrom (some (cursor d d.val List.suffix_rfl,.eq,c)) t.1.val) [t.2] = _
  rw [eval_partial _ _ _ _ _ _ (by simp [t.1.property,d.property])]
  apply advance_empty
  change d.val.drop t.1.val.length = []
  exact List.drop_eq_nil_of_le (Nat.le_of_eq (d.property.trans t.1.property.symm))

private theorem run_tokens (n : ℕ) (d : Address ℓ) (ts : List (Token ℓ)) (c : Fin (n+1)) :
    (machine n d).evalFrom (fresh d c) (encode ts) =
      ((run n d c.val (ts.map Prod.fst)).bind fun j ↦
        if h : j ≤ n then fresh d ⟨j,Nat.lt_succ_of_le h⟩ else none) := by
  induction ts generalizing c with
  | nil => simp [run,encode,Nat.le_of_lt_succ c.isLt]
  | cons t ts ih =>
    change (machine n d).evalFrom (fresh d c) (bits t ++ encode ts) = _
    rw [DFA.evalFrom_of_append,eval_token]
    have ht := update_tick n d t.1 c
    cases hh : updateCount n (comparePart .eq t.1.val d.val) c with
    | none =>
      simp only [hh,Option.map_none] at ht
      simp [run,←ht,eval_dead]
    | some k =>
      simp only [hh,Option.map_some] at ht
      simp [run,←ht,ih]

private theorem split_into_tokens (ℓ : ℕ) (w : List Bool) :
    ∃ ts : List (Token ℓ), ∃ u, w = encode ts ++ u ∧ u.length ≤ ℓ := by
  by_cases h : w.length ≤ ℓ
  · exact ⟨[],w,rfl,h⟩
  · have hi : ℓ < w.length := by omega
    let e : Address ℓ := ⟨w.take ℓ,by simp [Nat.le_of_lt hi]⟩
    let b := w[ℓ]
    have hh : w = bits (e,b) ++ w.drop (ℓ+1) := by
      change w = (w.take ℓ ++ [w[ℓ]]) ++ _
      rw [←List.take_succ_eq_append_getElem hi,List.take_append_drop]
    obtain ⟨ts,u,hu,hul⟩ := split_into_tokens ℓ (w.drop (ℓ+1))
    exact ⟨(e,b)::ts,u,by rw [hh,hu]; simp [encode,List.append_assoc],hul⟩
termination_by w.length
decreasing_by simp; omega

private theorem accepts_partial (n : ℕ) (d : Address ℓ) (c : Fin (n+1)) (u : List Bool) (h : u.length ≤ ℓ) :
    (machine n d).evalFrom (fresh d c) u ∈ (machine n d).accept ↔ u=[] := by
  change (∃ k, (machine n d).evalFrom (some (cursor d d.val List.suffix_rfl,.eq,c)) u = fresh d k) ↔ _
  rw [eval_partial _ _ _ _ _ _ (by simpa [d.property] using h)]
  constructor
  · rintro ⟨k,hk⟩
    have he := congrArg (fun x : Tails d × Ordering × Fin (n+1) ↦ x.1.val.length) (Option.some.inj hk)
    change (d.val.drop u.length).length = d.val.length at he
    rw [List.length_drop,d.property] at he
    exact List.length_eq_zero_iff.mp (by omega)
  · rintro rfl; exact ⟨c,rfl⟩

private theorem machine_correct (n : ℕ) (d : Address ℓ) : (machine n d).accepts = binaryLanguage n d := by
  ext w
  change (machine n d).evalFrom (fresh d 0) w ∈ (machine n d).accept ↔ _
  constructor
  · obtain ⟨ts,u,rfl,hu⟩ := split_into_tokens ℓ w
    rw [DFA.evalFrom_of_append,run_tokens]
    intro h
    cases hk : run n d 0 (ts.map Prod.fst) with
    | none =>
      simp only [Fin.val_zero,hk,Option.bind_none,eval_dead] at h
      obtain ⟨_,hh⟩ := h
      contradiction
    | some k =>
      have hle := run_le (Nat.zero_le n) _ hk
      simp only [Fin.val_zero,hk,Option.bind_some,dif_pos hle] at h
      obtain rfl := (accepts_partial _ _ _ _ hu).mp h
      exact ⟨ts,by simp,k,hk⟩
  · rintro ⟨ts,rfl,k,hk⟩
    rw [run_tokens]
    simp only [Fin.val_zero,hk,Option.bind_some,dif_pos (run_le (Nat.zero_le n) _ hk)]
    exact ⟨_,rfl⟩

theorem binary_dfa {ℓ n : ℕ} (hl : 0 < ℓ) (hn : 0 < n) (d : Address ℓ) :
    DFAAtMost (13*ℓ*n) (binaryLanguage n d) := by
  let e := Fintype.equivFin (State n d)
  refine ⟨_,?_,DFA.reindex e (machine n d),(DFA.accepts_reindex ..).trans (machine_correct ..)⟩
  have hc := d.val.tails.toFinset_card_le
  have ho : Fintype.card Ordering = 3 := by decide
  simp only [State,Tails,Fintype.card_option,Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,ho]
  rw [List.length_tails,d.property] at hc
  have hh : (ℓ+1)*(3*(n+1)) ≤ (2*ℓ)*(3*(2*n)) := by
    apply Nat.mul_le_mul (by omega); omega
  nlinarith [Nat.mul_le_mul_right (3*(n+1)) hc,Nat.mul_pos hl hn]

end
end GenLimit.ComplexityBarriers.Blocks
