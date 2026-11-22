import GenLimit.Paper00_LanguageIdentification.Effective.Names

/-! # An effective enumeration of all unary primitive recursive functions

Erase unbounded minimization from a partial recursive program by replacing
each such node by zero. Every resulting program is total, and every primitive
recursive derivation is represented. Uniform evaluation uses the universal
partial recursive interpreter and the separate totality proof.
-/

namespace GenLimit.Gold.Effective.PrimitivePrograms

open Nat.Partrec (Code)

private def eraseSearch (c : Code) : Code :=
  c.recOn .zero .succ .left .right (fun _ _ => Code.pair) (fun _ _ => Code.comp)
    (fun _ _ => Code.prec) (fun _ _ => .zero)

private theorem eraseSearch_prim : Primrec eraseSearch := by
  let Input := Code × Code × Code × Code × Code
  have a : Primrec (fun p : Input => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have b : Primrec (fun p : Input => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Code.primrec_recOn (c := id) Primrec.id (Primrec.const Code.zero) (Primrec.const Code.succ)
    (Primrec.const Code.left) (Primrec.const Code.right)
    (pr := fun _ _ _ => Code.pair) (Code.primrec₂_pair.comp a b)
    (co := fun _ _ _ => Code.comp) (Code.primrec₂_comp.comp a b)
    (pc := fun _ _ _ => Code.prec) (Code.primrec₂_prec.comp a b)
    (rf := fun _ _ _ => Code.zero) (Primrec.const _)

def value : Code → ℕ → ℕ
  | .zero => fun _ => 0
  | .succ => Nat.succ
  | .left => fun x => x.unpair.1
  | .right => fun x => x.unpair.2
  | .pair a b => fun x => Nat.pair (value a x) (value b x)
  | .comp a b => fun x => value a (value b x)
  | .prec a b => Nat.unpaired fun x n => n.rec (value a x) fun y r =>
      value b (Nat.pair x (Nat.pair y r))
  | .rfind' _ => fun _ => 0

private theorem eval_erase (c : Code) (x : ℕ) :
    (eraseSearch c).eval x = Part.some (value c x) := by
  induction c generalizing x with
  | zero | succ | left | right | rfind' => rfl
  | pair a b ha hb =>
    change (Code.pair (eraseSearch a) (eraseSearch b)).eval x = _
    simp [Code.eval, Seq.seq, ha, hb, value]
  | comp a b ha hb =>
    change ((eraseSearch b).eval x >>= (eraseSearch a).eval) = _
    simp [hb, ha, value]
  | prec a b ha hb =>
    obtain ⟨⟨x, n⟩, rfl⟩ := Nat.pairEquiv.surjective x
    change (Code.prec (eraseSearch a) (eraseSearch b)).eval (Nat.pair x n) = _
    induction n with
    | zero => simpa [value] using ha x
    | succ n ih =>
      rw [Code.eval_prec_succ, ih]
      simp [value, hb]

theorem value_computable : Computable₂ value :=
  (Code.eval_part.comp (eraseSearch_prim.to_comp.comp Computable.fst)
    Computable.snd).of_eq_tot fun p => (eval_erase p.1 p.2).symm ▸ Part.mem_some _

theorem represents {f : ℕ → ℕ} (hf : Primrec f) : ∃ c, value c = f := by
  replace hf := Primrec.nat_iff.mp hf
  induction hf with
  | zero => exact ⟨.zero, rfl⟩
  | succ => exact ⟨.succ, rfl⟩
  | left => exact ⟨.left, rfl⟩
  | right => exact ⟨.right, rfl⟩
  | pair _ _ ha hb =>
    obtain ⟨a,rfl⟩ := ha
    obtain ⟨b,rfl⟩ := hb
    exact ⟨.pair a b, rfl⟩
  | comp _ _ ha hb =>
    obtain ⟨a,rfl⟩ := ha
    obtain ⟨b,rfl⟩ := hb
    exact ⟨.comp a b, rfl⟩
  | prec _ _ ha hb =>
    obtain ⟨a,rfl⟩ := ha
    obtain ⟨b,rfl⟩ := hb
    exact ⟨.prec a b, rfl⟩

def program (i : ℕ) := eraseSearch (Denumerable.ofNat Code i)
def evaluate (i : ℕ) := value (Denumerable.ofNat Code i)

theorem program_computable : Computable program := (eraseSearch_prim.comp (Primrec.ofNat Code)).to_comp

theorem evaluate_computable : Computable₂ evaluate :=
  (value_computable.comp ((Primrec.ofNat Code).to_comp.comp Computable.fst) Computable.snd).to₂

theorem program_spec (i x : ℕ) : (program i).eval x = Part.some (evaluate i x) := eval_erase _ _

theorem exists_index {f : ℕ → ℕ} (h : Primrec f) : ∃ i, evaluate i = f := by
  obtain ⟨c, hc⟩ := represents h
  exact ⟨Encodable.encode c, by simpa [evaluate] using hc⟩

end GenLimit.Gold.Effective.PrimitivePrograms
