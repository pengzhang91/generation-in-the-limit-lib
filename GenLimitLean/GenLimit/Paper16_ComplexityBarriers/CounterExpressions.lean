import GenLimit.Paper16_ComplexityBarriers.BinaryBlocks
import Mathlib.Computability.Language

/-! # Language equations for a reset counter

An interval between resets consists of arbitrary higher addresses with a
bounded number of equal ones. Left quotients verify this description at
each possible current counter value. -/
namespace GenLimit.ComplexityBarriers.Blocks
open List
open scoped Classical
noncomputable section

def symbolClass (P : α → Prop) : _root_.Language α := {w | ∃ a, w=[a] ∧ P a}

private def tailL (a : α) (L : _root_.Language α) : _root_.Language α := {w | a::w ∈ L}

private theorem tail_add (a : α) (L K : _root_.Language α) : tailL a (L+K) = tailL a L + tailL a K := rfl

private theorem tail_one (a : α) : tailL a (1 : _root_.Language α) = 0 := by ext w; exact iff_of_false (List.cons_ne_nil a w) id

private theorem tail_symbol (a : α) (P : α → Prop) : tailL a (symbolClass P) = if P a then 1 else 0 := by
  ext w
  by_cases h : P a
  · rw [if_pos h]
    change (∃ b, a::w = [b] ∧ P b) ↔ w=[]
    simp [List.cons.injEq,h]
  · rw [if_neg h]
    change (∃ b, a::w = [b] ∧ P b) ↔ False
    simp [List.cons.injEq,h]

private theorem nil_symbol (P : α → Prop) : [] ∉ symbolClass P := by rintro ⟨a,h,_⟩; contradiction

private theorem tail_mul (a : α) (L K : _root_.Language α) :
    tailL a (L*K) = tailL a L * K + if [] ∈ L then tailL a K else 0 := by
  ext w
  change (a::w) ∈ L*K ↔ _ ∨ _
  rw [Language.mem_mul,Language.mem_mul]
  constructor
  · rintro ⟨u,hu,v,hv,he⟩
    cases u with
    | nil =>
      right; rw [if_pos hu]; exact show a::w ∈ K from he ▸ hv
    | cons b u =>
      obtain ⟨rfl,h⟩ := List.cons.inj he
      exact Or.inl ⟨u,hu,v,hv,h⟩
  · rintro (⟨u,hu,v,hv,rfl⟩|h)
    · exact ⟨a::u,hu,v,hv,rfl⟩
    · split at h
      next hl => exact ⟨[],hl,a::w,h,rfl⟩
      next => exact h.elim

private theorem nil_star (L : _root_.Language α) : [] ∈ KStar.kstar L :=
  Language.mem_kstar.mpr ⟨[],rfl,by simp⟩

private theorem tail_star (a : α) (L : _root_.Language α) :
    tailL a (KStar.kstar L) = tailL a L * KStar.kstar L := by
  ext w
  change a::w ∈ KStar.kstar L ↔ _
  rw [Language.mem_mul]
  constructor
  · intro h
    obtain ⟨ls,he,hl⟩ := Language.mem_kstar_iff_exists_nonempty.mp h
    cases ls with
    | nil => contradiction
    | cons u us =>
      obtain ⟨hu,hne⟩ := hl u List.mem_cons_self
      cases u with
      | nil => contradiction
      | cons b u =>
        obtain ⟨rfl,hw⟩ := List.cons.inj he
        exact ⟨u,hu,us.flatten,Language.mem_kstar.mpr ⟨us,rfl,fun v hv ↦ (hl v (List.mem_cons_of_mem _ hv)).1⟩,hw.symm⟩
  · rintro ⟨u,hu,v,hv,rfl⟩
    obtain ⟨vs,rfl,hh⟩ := Language.mem_kstar.mp hv
    refine Language.mem_kstar.mpr ⟨(a::u)::vs,rfl,?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl|hp
    · exact hu
    · exact hh _ hp

abbrev Lower (d : Address ℓ) := symbolClass (fun t : Token ℓ ↦ t.1 < d)
abbrev Equal (d : Address ℓ) := symbolClass (fun t : Token ℓ ↦ t.1 = d)
abbrev Higher (d : Address ℓ) := symbolClass (fun t : Token ℓ ↦ d < t.1)

def segment (d : Address ℓ) : ℕ → _root_.Language (Token ℓ)
  | 0 => KStar.kstar (Higher d)
  | k+1 => KStar.kstar (Higher d) * (1 + Equal d * segment d k)

def cycles (n : ℕ) (d : Address ℓ) := KStar.kstar (Lower d * segment d n)

private def full (n k : ℕ) (d : Address ℓ) := segment d k * cycles n d

private theorem nil_segment (d : Address ℓ) (k : ℕ) : [] ∈ segment d k := by
  cases k with
  | zero => apply nil_star
  | succ k => exact Language.mem_mul.mpr ⟨[],nil_star _,[],Or.inl rfl,rfl⟩

private theorem tail_segment (d : Address ℓ) (t : Token ℓ) (k : ℕ) :
    tailL t (segment d k) = if d<t.1 then segment d k else
      if t.1=d then (if k=0 then 0 else segment d (k-1)) else 0 := by
  cases k with
  | zero =>
    rw [segment,tail_star,tail_symbol]
    rcases lt_trichotomy d t.1 with h|h|h
    · simp [h]
    · simp [h]
    · simp [not_lt.mpr h.le,h.ne]
  | succ k =>
    rw [segment,tail_mul,tail_star,tail_symbol,if_pos (nil_star _),
      tail_add,tail_one,tail_mul,tail_symbol,if_neg (nil_symbol _)]
    rcases lt_trichotomy d t.1 with h|h|h
    · simp [h,Ne.symm h.ne]
    · simp [h]
    · simp [not_lt.mpr h.le,h.ne]

private theorem tail_cycles (n : ℕ) (d : Address ℓ) (t : Token ℓ) :
    tailL t (cycles n d) = if t.1<d then full n n d else 0 := by
  unfold cycles
  rw [tail_star,tail_mul,tail_symbol,if_neg (nil_symbol _)]
  by_cases h : t.1<d <;> simp [h,full,cycles]

private theorem full_correct (n : ℕ) (d : Address ℓ) (ts : List (Token ℓ)) (c : ℕ) (hc : c ≤ n) :
    ts ∈ full n (n-c) d ↔ ∃ j, run n d c (ts.map Prod.fst) = some j := by
  induction ts generalizing c with
  | nil =>
    exact iff_of_true (Language.mem_mul.mpr ⟨[],nil_segment ..,[],nil_star _,rfl⟩) ⟨c,rfl⟩
  | cons t ts ih =>
    change ts ∈ tailL t (segment d (n-c) * cycles n d) ↔ _
    rw [tail_mul,tail_segment,if_pos (nil_segment ..),tail_cycles]
    rcases lt_trichotomy t.1 d with h|h|h
    · simpa [h,not_lt.mpr h.le,h.ne,run,tick] using ih 0 (Nat.zero_le n)
    · by_cases he : c=n
      · subst c; simp [h,run,tick]
      · have hh : c < n := lt_of_le_of_ne hc he
        have hd : n-c-1 = n-(c+1) := by omega
        simpa [h,hh,Nat.sub_ne_zero_of_lt hh,hd,full,run,tick] using ih (c+1) hh
    · simpa [h,not_lt.mpr h.le,Ne.symm h.ne,run,tick,full] using ih c hc

theorem counter_description (n : ℕ) (d : Address ℓ) :
    segment d n * cycles n d = {ts | Good n d (ts.map Prod.fst)} := by
  ext ts
  simpa [full] using full_correct n d ts 0 (Nat.zero_le n)

end
end GenLimit.ComplexityBarriers.Blocks
