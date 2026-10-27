import Mathlib.Computability.Partrec

/-! # Computable finite-list folds for computable, not necessarily primitive-recursive steps -/

namespace GenLimit.Support.ComputableLists

variable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ] [Inhabited β]

theorem foldl {l : α → List β} {g : α → σ} {f : α → σ × β → σ}
    (hl : Computable l) (hg : Computable g) (hf : Computable₂ f) :
    Computable (fun a => (l a).foldl (fun s b => f a (s, b)) (g a)) := by
  have hstep : Computable₂ (fun a : α => fun r : ℕ × σ =>
      f a (r.2, ((l a)[r.1]?).getD default)) := by
    have hb : Computable (fun z : α × (ℕ × σ) => ((l z.1)[z.2.1]?).getD default) :=
      Computable.option_getD
        (Computable.list_getElem?.comp (hl.comp Computable.fst) (Computable.fst.comp Computable.snd))
        (Computable.const default)
    exact (hf.comp Computable.fst (Computable.pair (Computable.snd.comp Computable.snd) hb)).to₂
  apply (Computable.nat_rec (Computable.list_length.comp hl) hg hstep).of_eq
  intro a
  have he : ∀ n, n ≤ (l a).length →
      Nat.rec (g a) (fun k s => f a (s, ((l a)[k]?).getD default)) n =
        ((l a).take n).foldl (fun s b => f a (s, b)) (g a) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have hlt : n < (l a).length := by omega
      change f a (Nat.rec (g a) (fun k s => f a (s, ((l a)[k]?).getD default)) n,
        ((l a)[n]?).getD default) = _
      rw [ih (by omega), List.take_succ_eq_append_getElem hlt, List.foldl_append]
      simp [List.getElem?_eq_getElem hlt]
  simpa using he (l a).length le_rfl

theorem flatMap {l : α → List β} {f : α → β → List σ}
    (hl : Computable l) (hf : Computable₂ f) :
    Computable (fun a => (l a).flatMap (f a)) := by
  have hstep : Computable₂ (fun a : α => fun r : List σ × β => r.1 ++ f a r.2) :=
    (Computable.list_append.comp (Computable.fst.comp Computable.snd)
      (hf.comp Computable.fst (Computable.snd.comp Computable.snd))).to₂
  simpa only [List.flatMap_eq_foldl] using foldl hl (Computable.const []) hstep

theorem map {l : α → List β} {f : α → β → σ}
    (hl : Computable l) (hf : Computable₂ f) :
    Computable (fun a => (l a).map (f a)) := by
  have hs : Computable₂ (fun a b => [f a b]) :=
    (Computable.list_cons.comp hf (Computable.const [])).to₂
  simpa only [List.map_eq_flatMap] using flatMap hl hs

theorem all {l : α → List β} {f : α → β → Bool}
    (hl : Computable l) (hf : Computable₂ f) :
    Computable (fun a => (l a).all (f a)) := by
  have hstep : Computable₂ (fun a : α => fun r : Bool × β => r.1 && f a r.2) :=
    (Primrec.and.to_comp.comp (Computable.fst.comp Computable.snd)
      (hf.comp Computable.fst (Computable.snd.comp Computable.snd))).to₂
  have he (a : α) (xs : List β) (b : Bool) :
      xs.foldl (fun s x => s && f a x) b = (b && xs.all (f a)) := by
    induction xs generalizing b with
    | nil => simp
    | cons x xs ih => simp [List.foldl_cons, ih, Bool.and_assoc]
  exact (foldl hl (Computable.const true) hstep).of_eq (fun a => by simp [he])

theorem any {l : α → List β} {f : α → β → Bool}
    (hl : Computable l) (hf : Computable₂ f) :
    Computable (fun a => (l a).any (f a)) := by
  have hn : Computable₂ (fun a b => !(f a b)) := (Primrec.not.to_comp.comp hf).to₂
  exact (Primrec.not.to_comp.comp (all hl hn)).of_eq (fun _ => List.any_eq_not_all_not.symm)

end GenLimit.Support.ComputableLists
