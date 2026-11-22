import GenLimit.Paper00_LanguageIdentification.Effective.RejectionClock
import GenLimit.Paper00_LanguageIdentification.Effective.RecursiveObstructions

/-! # Primitive recursive adversarial text for tester identification (I.9) -/

namespace GenLimit.Gold.Effective
namespace PrimitiveDiagonal

open Nat.Partrec (Code)

abbrev State := ℕ × List ℕ

def advance (m : Code) (v : ℕ → ℕ) (n : ℕ) (q : State) :=
  decide (v q.1 ∈ q.2) ||
    (decide (q.1 ≤ n.unpair.1) && RejectionClock.rejects m n q.2 (v q.1))

def symbol (m : Code) (v : ℕ → ℕ) (n : ℕ) (q : State) :=
  bif advance m v n q then v q.1 else v 0

def step (m : Code) (v : ℕ → ℕ) (n : ℕ) (q : State) : State :=
  ((bif advance m v n q then q.1 + 1 else q.1), q.2 ++ [symbol m v n q])

def state (m : Code) (v : ℕ → ℕ) : ℕ → State := Nat.rec (0, []) (step m v)
def stream (m : Code) (v : ℕ → ℕ) (n : ℕ) := symbol m v n (state m v n)

theorem stream_prim (m : Code) {v : ℕ → ℕ} (hv : Primrec v) : Primrec (stream m v) := by
  have idx : Primrec (fun z : ℕ × State => z.2.1) := Primrec.fst.comp Primrec.snd
  have hist : Primrec (fun z : ℕ × State => z.2.2) := Primrec.snd.comp Primrec.snd
  have word := hv.comp idx
  have inside : Primrec (fun z : ℕ × State => decide (v z.2.1 ∈ z.2.2)) :=
    (Primrec.nat_lt.comp (Primrec.list_idxOf.comp word hist) (Primrec.list_length.comp hist)).decide.of_eq
      fun z => by simp [List.idxOf_lt_length_iff]
  have go : Primrec₂ (advance m v) :=
    (Primrec.or.comp inside (Primrec.and.comp
      (Primrec.nat_le.comp idx (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))).decide
      (RejectionClock.rejects_prim m Primrec.fst hist word))).to₂
  have out : Primrec₂ (symbol m v) := (go.cond word (Primrec.const (v 0))).to₂
  have stepP : Primrec₂ (step m v) := ((go.cond (Primrec.succ.comp idx) idx).pair
    (Primrec.list_append.comp hist (Primrec.list_cons.comp out (Primrec.const [])))).to₂
  exact out.comp Primrec.id (Primrec.nat_rec₁ (0, []) stepP)

theorem history (m : Code) (v : ℕ → ℕ) (n : ℕ) :
    (state m v n).2 = textPrefix (stream m v) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [textPrefix_succ, ← ih]
    rfl

private theorem finite_if_eventually_old {s : ℕ → ℕ} (N x : ℕ)
    (old : ∀ n ≥ N, s n ∈ textPrefix s n ∨ s n = x) : (Set.range s).Finite := by
  apply (Finset.finite_toSet (insert x (textPrefix s N).toFinset)).subset
  rintro _ ⟨n,rfl⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < N
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (mem_textPrefix_iff.mpr ⟨n,hn,rfl⟩))
    · rcases old n (Nat.le_of_not_lt hn) with hs | hs
      · obtain ⟨j,hj,he⟩ := mem_textPrefix_iff.mp hs
        exact he ▸ ih j hj
      · simp [hs]

/-- Every infinite language with a primitive recursive presentation obstructs
effective tester learning of any class also containing the finite languages. -/
theorem obstruction {C : Set Language} (finite : Text.finiteLanguages ⊆ C)
    {L : Language} (hl : L ∈ C) (hinf : L.Infinite)
    {v : ℕ → ℕ} (hv : Primrec v) (hp : Presents v L) :
    ¬ Identifiable Tester primitiveRecursiveText C := by
  classical
  rintro ⟨M, hc, learns⟩
  obtain ⟨m, impl⟩ := RejectionClock.code_for hc
  let s := stream m v
  let j (n : ℕ) := (state m v n).1
  let go (n : ℕ) := advance m v n (state m v n)
  have phase (n : ℕ) : j (n+1) = (bif go n then j n + 1 else j n) := rfl
  have emit (n : ℕ) : s n = (bif go n then v (j n) else v 0) := rfl
  have guard (n : ℕ) : go n = true ↔ v (j n) ∈ textPrefix s n ∨
      j n ≤ n.unpair.1 ∧ RejectionClock.rejects m n (textPrefix s n) (v (j n)) = true := by
    simp [go, advance, history, s, j]
  have mono : Monotone j := monotone_nat_of_le_succ fun n => by
    rw [phase]
    cases go n <;> simp
  have prim : Primrec s := stream_prim m hv
  have reach (i : ℕ) : ∃ N, j N = i := by
    induction i with
    | zero => exact ⟨0, rfl⟩
    | succ i ih =>
      obtain ⟨N,hN⟩ := ih
      by_contra! miss
      have stop (n : ℕ) (hn : j n = i) : go n = false := by
        cases hg : go n
        · rfl
        · exact False.elim (miss (n+1) (by simp [phase, hg, hn]))
      have fixed (n : ℕ) (hn : N ≤ n) : j n = i := by
        induction n, hn using Nat.le_induction with
        | base => exact hN
        | succ n _ ih => simp [phase, stop n ih, ih]
      have hfin := finite_if_eventually_old (s := s) N (v 0) fun n hn =>
        Or.inr (by simp [emit n, stop n (fixed n hn)])
      obtain ⟨c, test, T, hT⟩ := learns _ (finite hfin) s ⟨prim, rfl⟩
      have absent : v i ∉ Set.range s := by
        rintro ⟨u,hu⟩
        let n := max N (u+1)
        have hfix := fixed n (le_max_left ..)
        have hseen : v (j n) ∈ textPrefix s n := mem_textPrefix_iff.mpr
          ⟨u, lt_of_lt_of_le (Nat.lt_succ_self u) (le_max_right ..), hu.trans (congrArg v hfix).symm⟩
        exact Bool.noConfusion ((stop n hfix).symm.trans ((guard n).mpr (Or.inl hseen)))
      let k := max T i
      have rejects : 0 ∈ (M (textPrefix s k)).eval (v i) := by
        rw [hT k (le_max_left ..), (test _).2 absent]
        exact Part.mem_some _
      obtain ⟨n, hn, hk, detected⟩ := RejectionClock.complete impl s rejects N
      have hfix := fixed n hn
      apply Bool.noConfusion ((stop n hfix).symm.trans ((guard n).mpr (Or.inr ?_)))
      simpa only [hfix, hk] using And.intro (le_max_right T i) detected
  have visited (n : ℕ) : ∀ i < j n, v i ∈ Set.range s := by
    induction n with
    | zero => exact fun i hi => False.elim (Nat.not_lt_zero i hi)
    | succ n ih =>
      intro i hi
      rw [phase] at hi
      cases hg : go n <;> simp [hg] at hi
      · exact ih _ hi
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
        · exact ih _ h
        · exact ⟨n, by simp [emit n, hg]⟩
  have pres : Presents s L := by
    rw [Presents, ← hp]
    apply Set.Subset.antisymm
    · rintro _ ⟨n,rfl⟩
      rw [emit n]
      cases go n <;> exact Set.mem_range_self _
    · rintro _ ⟨i,rfl⟩
      obtain ⟨n, hn⟩ := reach (i+1)
      exact visited n i (hn ▸ Nat.lt_succ_self i)
  obtain ⟨c, test, T, stable⟩ := learns L hl s ⟨prim, pres⟩
  obtain ⟨N,hN⟩ := reach T
  have fin := finite_if_eventually_old (s := s) N (v 0) (fun n hn => by
    rw [emit n]
    cases hg : go n with
    | false => exact Or.inr rfl
    | true =>
      simp only [Bool.cond_true]
      rcases (guard n).mp hg with old | ⟨hk, rejected⟩
      · exact Or.inl old
      · have negative := RejectionClock.sound impl rejected
        have hTn : T ≤ j n := hN ▸ mono hn
        have positive := (test (v (j n))).1 (hp ▸ Set.mem_range_self _)
        rw [stable _ (hTn.trans hk), positive] at negative
        simp at negative)
  exact hinf (pres ▸ fin)

end PrimitiveDiagonal
end GenLimit.Gold.Effective
