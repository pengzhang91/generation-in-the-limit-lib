import GenLimit.Paper16_ComplexityBarriers.StackGrammar
import GenLimit.Paper11_LearningAlgorithmsInTheLimit.RepresentationBudget

/-! # Effective bounds on finite grammar descriptions

A promised partial procedure is total on the padded grammars for every
pair of initial stacks. Taking its maximum over bounded integer codes gives
a computable bound even when the finite control uses classical numbering. -/
namespace GenLimit.ComplexityBarriers.CFG
open List
open scoped Classical
noncomputable section

abbrev Tables := List (ℕ × List (ℕ ⊕ ℕ))
abbrev BoundProcedure := Description × Description →. ℕ

def OnInfinite (A : BoundProcedure) : Prop :=
  ∀ g h : Description, (language g).Infinite → (language h).Infinite →
    ∃ m ∈ A (g,h), MGeneratable {language g,language h} m

private theorem description_infinite (T : Tables) (p : ℕ) (s : List ℕ) :
    (language (description T p s)).Infinite := by
  let g := description T p s
  have hr (n : ℕ) : Reads (grammar g) [.nonterminal (1:ℕ)] (replicate n p) := by
    induction n with
    | zero =>
      apply (expand_iff g 1 [] _).mpr
      exact ⟨[],by simp [g,description],.empty⟩
    | succ n ih =>
      apply (expand_iff g 1 [] _).mpr
      rw [List.replicate_succ]
      exact ⟨[.inl p,.inr 1],by simp [g,description],.letter _ ih⟩
  let f := fun n ↦ p::replicate n p
  have hi : Function.Injective f := by intro i j he; simpa [f] using congrArg List.length he
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨n,rfl⟩
  apply (mem_language g _).mpr
  apply (expand_iff g 0 [] _).mpr
  exact ⟨[.inl p,.inr 1],by simp [g,description],.letter p (hr n)⟩

private theorem build_prim (T : Tables) (p : ℕ) : Primrec (description T p) := by
  have hs : Primrec (fun s : List ℕ ↦ s.map (Sum.inr : ℕ → ℕ ⊕ ℕ)) :=
    Primrec.list_map Primrec.id (Primrec.sumInr.comp Primrec.snd).to₂
  exact (Primrec.const 0).pair (Primrec.list_cons.comp ((Primrec.const 0).pair
    (Primrec.list_cons.comp (Primrec.const _) hs)) (Primrec.const _))

private def boundUp (f : ℕ → ℕ) : ℕ → ℕ := Nat.rec (f 0) (fun i b ↦ max b (f (i+1)))

private theorem boundUp_comp {f : ℕ → ℕ} (hf : Computable f) : Computable (boundUp f) :=
  Computable.nat_rec Computable.id (Computable.const _) ((Primrec.nat_max.to_comp.comp
    (Computable.snd.comp Computable.snd) (hf.comp (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd)))).to₂)

private theorem le_boundUp (f : ℕ → ℕ) {i k : ℕ} (hk : i ≤ k) : f i ≤ boundUp f k := by
  induction k with
  | zero => obtain rfl := Nat.le_zero.mp hk; rfl
  | succ k ih =>
    rcases Nat.le_succ_iff.mp hk with h|rfl
    · exact (ih h).trans (le_max_left ..)
    · exact le_max_right ..

theorem effective_majorant (A : BoundProcedure) (hA : Partrec A) (hon : OnInfinite A)
    (T U : Tables) : ∃ f : ℕ → ℕ, Computable f ∧ ∀ l r k,
    Encodable.encode (l,r) ≤ k →
    ∃ m ≤ f k, MGeneratable {language (description T 0 l),language (description U 1 r)} m := by
  let raw := fun n : ℕ ↦ (Encodable.decode (α := List ℕ × List ℕ) n).getD ([],[])
  have hraw : Computable raw := Computable.option_getD Computable.decode (Computable.const _)
  let grammars := fun n ↦ (description T 0 (raw n).1,description U 1 (raw n).2)
  have hc : Computable grammars := ((build_prim T 0).to_comp.comp (Computable.fst.comp hraw)).pair
    ((build_prim U 1).to_comp.comp (Computable.snd.comp hraw))
  have hs (n : ℕ) := hon (grammars n).1 (grammars n).2
    (description_infinite T 0 (raw n).1) (description_infinite U 1 (raw n).2)
  choose m hm hg using hs
  have hcomp : Computable m := (hA.comp hc).of_eq (fun n ↦ Part.eq_some_iff.mpr (hm n))
  refine ⟨boundUp m,boundUp_comp hcomp,fun l r k hk ↦ ⟨m (Encodable.encode (l,r)),le_boundUp m hk,?_⟩⟩
  simpa [grammars,raw] using hg (Encodable.encode (l,r))

private def tower (m : ℕ) : ℕ → ℕ := Nat.rec 0 (fun _ k ↦ (Nat.pair m k).succ)

private theorem tower_prim : Primrec₂ tower :=
  Primrec.nat_rec (Primrec.const 0) ((Primrec.succ.comp
    (Primrec₂.natPair.comp Primrec.fst (Primrec.snd.comp Primrec.snd))).to₂)

private theorem tower_mono (m : ℕ) : Monotone (tower m) :=
  monotone_nat_of_le_succ (fun n ↦ (Nat.right_le_pair m (tower m n)).trans (Nat.le_succ _))

private theorem list_bound (m : ℕ) (xs : List ℕ) (h : ∀ x ∈ xs, x ≤ m) : Encodable.encode xs ≤ tower m xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    exact Nat.succ_le_succ (GenLimit.LearningAlgorithmsLimit.NativeTape.pair_mono (h x List.mem_cons_self)
      (ih (fun y hy ↦ h y (List.mem_cons_of_mem _ hy))))

def inputBound (m width x : ℕ) : ℕ :=
  let b := tower m (width*(x+1)+2)
  Nat.pair b b

theorem inputBound_comp (m width : ℕ) : Computable (inputBound m width) := by
  have hb := tower_prim.comp (Primrec.const m) (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const width) Primrec.succ) (Primrec.const 2))
  exact (Primrec₂.natPair.comp hb hb).to_comp

theorem le_inputBound (m width x : ℕ) (l r : List ℕ)
    (hl : ∀ i ∈ l, i ≤ m) (hr : ∀ i ∈ r, i ≤ m)
    (hs : l.length ≤ width*(x+1)+2) (ht : r.length ≤ width*(x+1)+2) :
    Encodable.encode (l,r) ≤ inputBound m width x :=
  GenLimit.LearningAlgorithmsLimit.NativeTape.pair_mono
    ((list_bound _ _ hl).trans (tower_mono m hs)) ((list_bound _ _ hr).trans (tower_mono m ht))

end
end GenLimit.ComplexityBarriers.CFG
