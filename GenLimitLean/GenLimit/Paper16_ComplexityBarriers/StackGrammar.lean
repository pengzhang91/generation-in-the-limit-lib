import GenLimit.Paper16_ComplexityBarriers.Grammar

/-! # Context-free grammars for labelled stack rewrites

A transition replacing the top A by a stack u on a label e is exactly
the production A → e u. A separate starting branch generates a private
infinite language, so a sample-bound procedure must terminate on every
pair produced by the reduction. -/
namespace GenLimit.ComplexityBarriers.CFG
open List
open scoped Classical
noncomputable section

variable {N E : Type} [Fintype N] [Fintype E]

def number [Fintype α] (a : α) : ℕ := (Fintype.equivFin α a).val

theorem number_injective [Fintype α] : Function.Injective (number (α := α)) :=
  fun _ _ h ↦ (Fintype.equivFin α).injective (Fin.ext h)

inductive StackReads (δ : N → E → Option (List N)) : List N → List E → Prop
  | empty : StackReads δ [] []
  | step {x xs e u w} : δ x e = some u → StackReads δ (u++xs) w → StackReads δ (x::xs) (e::w)

def nt (x : N) : ℕ := number x + 2
def label (e : E) : ℕ := number e + 3

private def ntString (xs : List N) : List (Symbol ℕ ℕ) := xs.map (fun x ↦ .nonterminal (nt x))

private def rhs (e : E) (xs : List N) : List (ℕ ⊕ ℕ) :=
  .inl (label e) :: xs.map (fun x ↦ .inr (nt x))

def stackRules (δ : N → E → Option (List N)) : List (ℕ × List (ℕ ⊕ ℕ)) :=
  (Finset.univ : Finset (N × E)).toList.filterMap fun p ↦
    (δ p.1 p.2).map (fun xs ↦ (nt p.1,rhs p.2 xs))

private theorem mem_rules (δ : N → E → Option (List N)) (A : ℕ) (v : List (ℕ ⊕ ℕ)) :
    (A,v) ∈ stackRules δ ↔ ∃ x e xs, δ x e=some xs ∧ A=nt x ∧ v=rhs e xs := by
  simp only [stackRules,List.mem_filterMap,Finset.mem_toList,Finset.mem_univ,true_and,Prod.exists,
    Option.map_eq_some_iff,Prod.mk.injEq]
  constructor
  · rintro ⟨x,e,xs,h,h₁,h₂⟩; exact ⟨x,e,xs,h,h₁.symm,h₂.symm⟩
  · rintro ⟨x,e,xs,h,rfl,rfl⟩; exact ⟨x,e,xs,h,rfl,rfl⟩

/-- The start, padding, and simulated variables have disjoint numeric names. -/
def description (table : List (ℕ × List (ℕ ⊕ ℕ))) (pad : ℕ) (initial : List ℕ) : Description :=
  (0,(0,.inl 2 :: initial.map Sum.inr)::(0,[.inl pad,.inr 1])::
    (1,[])::(1,[.inl pad,.inr 1])::table)

def padded (pad : ℕ) (δ : N → E → Option (List N)) (initial : List N) :=
  description (stackRules δ) pad (initial.map nt)

private theorem native_step (pad : ℕ) (δ : N → E → Option (List N)) (initial : List N)
    (x : N) (xs : List N) (w : List ℕ) :
    Reads (grammar (padded pad δ initial)) (ntString (x::xs)) w ↔
    ∃ e u v, δ x e=some u ∧ w=label e::v ∧ Reads (grammar (padded pad δ initial)) (ntString (u++xs)) v := by
  rw [show ntString (x::xs) = .nonterminal (nt x)::ntString xs from rfl,expand_iff]
  have h0 : nt x ≠ 0 := by simp [nt]
  have h1 : nt x ≠ 1 := by simp [nt]
  simp only [padded,description,List.mem_cons,Prod.mk.injEq,h0,h1,false_and,false_or,mem_rules]
  constructor
  · rintro ⟨_,⟨y,e,u,hy,hn,rfl⟩,hr⟩
    obtain rfl : x=y := number_injective (Nat.add_right_cancel hn)
    obtain ⟨v,rfl,hv⟩ := (letter_iff ..).mp hr
    exact ⟨e,u,v,hy,rfl,by simpa [rhs,ntString,symbol,List.map_map,Function.comp_def] using hv⟩
  · rintro ⟨e,u,v,hu,rfl,hv⟩
    refine ⟨rhs e u,⟨x,e,u,hu,rfl,rfl⟩,.letter _ ?_⟩
    simpa [rhs,ntString,symbol,List.map_map,Function.comp_def] using hv

private theorem native_iff (pad : ℕ) (δ : N → E → Option (List N)) (initial xs : List N) (w : List ℕ) :
    Reads (grammar (padded pad δ initial)) (ntString xs) w ↔ ∃ es, StackReads δ xs es ∧ w=es.map label := by
  induction w generalizing xs with
  | nil =>
    cases xs with
    | nil => exact iff_of_true .empty ⟨[],.empty,rfl⟩
    | cons x xs =>
      rw [native_step]
      constructor
      · rintro ⟨_,_,_,_,he,_⟩; contradiction
      · rintro ⟨_,hr,he⟩; cases hr; contradiction
  | cons a w ih =>
    cases xs with
    | nil =>
      constructor
      · intro h; exact (List.cons_ne_nil a w ((empty_iff _).mp h)).elim
      · rintro ⟨_,h,he⟩; cases h; contradiction
    | cons x xs =>
      rw [native_step]
      constructor
      · rintro ⟨e,u,v,hu,he,hv⟩
        obtain ⟨rfl,rfl⟩ := List.cons.inj he
        obtain ⟨es,hes,rfl⟩ := (ih _).mp hv
        exact ⟨e::es,.step hu hes,rfl⟩
      · rintro ⟨_,hs,he⟩
        cases hs with
        | @step _ _ e u es hu hes =>
          obtain ⟨rfl,he'⟩ := List.cons.inj he
          exact ⟨e,u,w,hu,rfl,(ih _).mpr ⟨es,hes,he'⟩⟩

private theorem private_iff (pad : ℕ) (δ : N → E → Option (List N)) (initial : List N) (w : List ℕ) :
    Reads (grammar (padded pad δ initial)) [.nonterminal (1 : ℕ)] w ↔ ∃ i, w=List.replicate i pad := by
  have base (v) : (1,v) ∉ stackRules δ := by
    rw [mem_rules]; rintro ⟨x,e,u,_,he,_⟩; simp [nt] at he
  have step (v) :
      Reads (grammar (padded pad δ initial)) [.nonterminal (1 : ℕ)] v ↔
      v=[] ∨ ∃ z, v=pad::z ∧ Reads (grammar (padded pad δ initial)) [.nonterminal (1 : ℕ)] z := by
    rw [expand_iff]
    simp only [padded,description,List.mem_cons,Prod.mk.injEq,Nat.one_ne_zero,false_and,false_or,
      true_and,base,or_false,List.append_nil]
    constructor
    · rintro ⟨_,(rfl|rfl),hr⟩
      · exact Or.inl ((empty_iff _).mp hr)
      · exact Or.inr ((letter_iff ..).mp hr)
    · rintro (rfl|⟨z,rfl,hz⟩)
      · exact ⟨[],Or.inl rfl,.empty⟩
      · exact ⟨_,Or.inr rfl,.letter pad hz⟩
  induction w with
  | nil => exact ⟨fun _ ↦ ⟨0,rfl⟩,fun _ ↦ (step _).mpr (.inl rfl)⟩
  | cons a w ih =>
    rw [step]
    constructor
    · rintro (he|⟨z,he,hz⟩)
      · contradiction
      · obtain ⟨rfl,rfl⟩ := List.cons.inj he
        obtain ⟨i,rfl⟩ := ih.mp hz
        exact ⟨i+1,(List.replicate_succ ..).symm⟩
    · rintro ⟨i,hi⟩
      cases i with
      | zero => contradiction
      | succ i =>
        rw [List.replicate_succ] at hi
        obtain ⟨rfl,rfl⟩ := List.cons.inj hi
        exact Or.inr ⟨_,rfl,ih.mpr ⟨_,rfl⟩⟩

theorem padded_iff (pad : ℕ) (δ : N → E → Option (List N)) (initial : List N) (w : List ℕ) :
    w ∈ language (padded pad δ initial) ↔
      (∃ es, StackReads δ initial es ∧ w=2::es.map label) ∨ ∃ i, w=pad::List.replicate i pad := by
  rw [mem_language,expand_iff]
  have base (v) : (0,v) ∉ stackRules δ := by
    rw [mem_rules]; rintro ⟨x,e,u,_,he,_⟩; simp [nt] at he
  simp only [padded,description,List.mem_cons,Prod.mk.injEq,zero_ne_one,false_and,true_and,
    base,or_false,List.append_nil]
  constructor
  · rintro ⟨_,(rfl|rfl),h⟩
    · obtain ⟨v,rfl,hr⟩ := (letter_iff ..).mp h
      obtain ⟨es,hes,rfl⟩ := (native_iff pad δ initial initial v).mp (by simpa [ntString,List.map_map,symbol,Function.comp_def] using hr)
      exact .inl ⟨es,hes,rfl⟩
    · obtain ⟨v,rfl,hr⟩ := (letter_iff ..).mp h
      obtain ⟨i,rfl⟩ := (private_iff pad δ initial v).mp hr
      exact .inr ⟨i,rfl⟩
  · rintro (⟨es,hs,rfl⟩|⟨i,rfl⟩)
    · refine ⟨_,Or.inl rfl,.letter 2 ?_⟩
      have h := (native_iff pad δ initial initial _).mpr ⟨es,hs,rfl⟩
      simpa [ntString,List.map_map,symbol,Function.comp_def] using h
    · exact ⟨_,Or.inr rfl,.letter pad ((private_iff pad δ initial _).mpr ⟨i,rfl⟩)⟩

theorem padded_infinite (pad : ℕ) (δ : N → E → Option (List N)) (s : List N) : (language (padded pad δ s)).Infinite := by
  let f := fun i ↦ pad :: List.replicate i pad
  have hi : Function.Injective f := by intro i j he; simpa [f] using congrArg List.length he
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨i,rfl⟩
  exact (padded_iff pad δ s _).mpr (.inr ⟨i,rfl⟩)

end
end GenLimit.ComplexityBarriers.CFG
