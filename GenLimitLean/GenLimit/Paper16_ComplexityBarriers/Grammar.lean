import GenLimit.Paper16_ComplexityBarriers.Threshold
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.PartrecCode

/-! # Finite grammar descriptions and leftmost derivations

A description lists the start variable and every production. A symbol is
tagged as a terminal or a nonterminal. Natural names allow different finite
alphabets; only finitely many names occur in any one description. The
denotation uses Mathlib's ordinary context-free derivability relation. -/
namespace GenLimit.ComplexityBarriers.CFG
open List
open scoped Classical

abbrev Description := ℕ × List (ℕ × List (ℕ ⊕ ℕ))

def symbol : ℕ ⊕ ℕ → Symbol ℕ ℕ
  | .inl a => .terminal a
  | .inr A => .nonterminal A

def rule (r : ℕ × List (ℕ ⊕ ℕ)) : ContextFreeRule ℕ ℕ := ⟨r.1,r.2.map symbol⟩

noncomputable def grammar (g : Description) : ContextFreeGrammar ℕ where
  NT := ℕ
  initial := g.1
  rules := (g.2.map rule).toFinset

def language (g : Description) : Set (List ℕ) := (grammar g).language

/-- The leftmost expansion or terminal read at the top of the pending string. -/
inductive Reads (g : ContextFreeGrammar T) : List (Symbol T g.NT) → List T → Prop
  | empty : Reads g [] []
  | letter {s w} (a : T) : Reads g s w → Reads g (.terminal a :: s) (a::w)
  | expand {r : ContextFreeRule T g.NT} {s w} (hr : r ∈ g.rules) :
      Reads g (r.output ++ s) w → Reads g (.nonterminal r.input :: s) w

namespace Reads
variable {g : ContextFreeGrammar T}

theorem append {s t u v} (hs : Reads g s u) (ht : Reads g t v) :
    Reads g (s++t) (u++v) := by
  induction hs with
  | empty => exact ht
  | letter a _ ih => exact .letter a ih
  | expand hr _ ih => exact .expand hr (by simpa [List.append_assoc] using ih)

private theorem split_aux {s w} (h : Reads g s w) :
    ∀ p q, s=p++q → ∃ u v, w=u++v ∧ Reads g p u ∧ Reads g q v := by
  induction h with
  | empty =>
    rintro p q he
    obtain ⟨rfl,rfl⟩ := List.append_eq_nil_iff.mp he.symm
    exact ⟨[],[],rfl,.empty,.empty⟩
  | @letter s w a hs ih =>
    intro p q he
    cases p with
    | nil => simp only [List.nil_append] at he; subst q; exact ⟨[],_,rfl,.empty,.letter a hs⟩
    | cons b p =>
      obtain ⟨hab,hparts⟩ := List.cons.inj he
      subst b
      obtain ⟨u,v,rfl,hu,hv⟩ := ih p q hparts
      exact ⟨a::u,v,rfl,.letter a hu,hv⟩
  | @expand r s w hr hs ih =>
    intro p q he
    cases p with
    | nil => simp only [List.nil_append] at he; subst q; exact ⟨[],_,rfl,.empty,.expand hr hs⟩
    | cons b p =>
      obtain ⟨hab,hparts⟩ := List.cons.inj he
      subst b
      obtain ⟨u,v,rfl,hu,hv⟩ := ih (r.output++p) q
        ((congrArg (r.output ++ ·) hparts).trans (List.append_assoc ..).symm)
      exact ⟨u,v,rfl,.expand hr hu,hv⟩

theorem split {p q w} (h : Reads g (p++q) w) :
    ∃ u v, w=u++v ∧ Reads g p u ∧ Reads g q v := split_aux h p q rfl

private theorem backward {s t w} (h : g.Produces s t) (ht : Reads g t w) : Reads g s w := by
  obtain ⟨r,hr,hh⟩ := h
  obtain ⟨p,q,rfl,rfl⟩ := ContextFreeRule.rewrites_iff.mp hh
  rw [List.append_assoc] at ht ⊢
  obtain ⟨u,v,rfl,hu,hv⟩ := split ht
  exact hu.append (.expand hr hv)

theorem derives {s w} (h : Reads g s w) : g.Derives s (w.map Symbol.terminal) := by
  induction h with
  | empty => rfl
  | letter a _ ih => exact ih.append_left [.terminal a]
  | expand hr _ ih =>
    apply ContextFreeGrammar.Produces.trans_derives _ ih
    exact ⟨_,hr,.head _⟩

theorem of_derives {s w} (h : g.Derives s (w.map Symbol.terminal)) : Reads g s w := by
  have back {s t} (hh : g.Derives s t) : Reads g t w → Reads g s w := by
    induction hh with
    | refl => exact id
    | tail _ he ih => exact fun hv ↦ ih (backward he hv)
  apply back h
  clear h back
  induction w with
  | nil => exact .empty
  | cons a w ih => exact .letter a ih

end Reads

theorem mem_language (g : Description) (w : List ℕ) :
    w ∈ language g ↔ Reads (grammar g) [.nonterminal g.1] w :=
  ⟨Reads.of_derives,Reads.derives⟩

/-- The finite alphabet explicitly occurring on the right-hand sides of the productions. -/
def alphabet (g : Description) : Finset ℕ :=
  (g.2.flatMap (fun r ↦ r.2.filterMap (fun s ↦ s.elim some (fun _ ↦ none)))).toFinset

theorem terminals_in_alphabet (g : Description) {w : List ℕ} (h : w ∈ language g) :
    ∀ a ∈ w, a ∈ alphabet g := by
  have accepts {s : List (Symbol ℕ (grammar g).NT)} {u : List ℕ} (hr : Reads (grammar g) s u)
      (hs : ∀ a, Symbol.terminal a ∈ s → a ∈ alphabet g) : ∀ a ∈ u, a ∈ alphabet g := by
    induction hr with
    | empty => simp
    | letter b _ ih =>
      intro a ha
      rcases List.mem_cons.mp ha with rfl | htail
      · exact hs a List.mem_cons_self
      · exact ih (fun x hx ↦ hs x (List.mem_cons_of_mem _ hx)) a htail
    | @expand r s u hm _ ih =>
      apply ih
      intro a ha
      rcases List.mem_append.mp ha with hout | htail
      · change (r : ContextFreeRule ℕ ℕ) ∈ (g.2.map rule).toFinset at hm
        simp only [List.mem_toFinset,List.mem_map] at hm
        obtain ⟨⟨i,v⟩,hv,rfl⟩ := hm
        obtain ⟨sym,hmem,he⟩ := List.mem_map.mp hout
        cases sym with
        | inl b =>
          obtain rfl : b = a := Symbol.terminal.inj he
          apply List.mem_toFinset.mpr
          exact List.mem_flatMap.mpr ⟨(i,v),hv,List.mem_filterMap.mpr ⟨.inl b,hmem,rfl⟩⟩
        | inr B => contradiction
      · exact hs a (List.mem_cons_of_mem _ htail)
  exact accepts ((mem_language g w).mp h) (by simp)

theorem expand_iff (g : Description) (A : ℕ) (s : List (Symbol ℕ ℕ)) (w : List ℕ) :
    Reads (grammar g) (.nonterminal A :: s) w ↔
      ∃ rhs, (A,rhs) ∈ g.2 ∧ Reads (grammar g) (rhs.map symbol ++ s) w := by
  constructor
  · intro h
    cases h with
    | @expand r _ _ hr hw =>
      change (r : ContextFreeRule ℕ ℕ) ∈ (g.2.map rule).toFinset at hr
      simp only [List.mem_toFinset,List.mem_map] at hr
      obtain ⟨⟨i,v⟩,hi,he⟩ := hr
      subst r
      exact ⟨v,hi,hw⟩
  · rintro ⟨v,hv,hw⟩
    apply Reads.expand (g := grammar g) (r := rule (A,v)) (s := s)
    · change rule (A,v) ∈ (g.2.map rule).toFinset
      exact List.mem_toFinset.mpr (List.mem_map_of_mem hv)
    · exact hw

theorem letter_iff {g : ContextFreeGrammar T} (a : T) (s : List (Symbol T g.NT)) (w : List T) :
    Reads g (.terminal a :: s) w ↔ ∃ v, w=a::v ∧ Reads g s v := by
  constructor
  · rintro h; cases h with | letter _ h => exact ⟨_,rfl,h⟩
  · rintro ⟨_,rfl,h⟩; exact .letter a h

theorem empty_iff {g : ContextFreeGrammar T} (w : List T) : Reads g [] w ↔ w=[] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .empty

end GenLimit.ComplexityBarriers.CFG
