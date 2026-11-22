import GenLimit.Paper00_LanguageIdentification.Effective.FunctionLearning
import GenLimit.Support.HistoryChain

/-! # Effective construction of a stream forcing unbounded changes of guess -/

namespace GenLimit.Gold.Effective

open GenLimit.Support

/-- Least-witness search for a decidable test known to succeed on each input. -/
theorem computable_choice_nat {A : Type*} [Primcodable A] {p : A → ℕ → Bool}
    (hp : Computable₂ p) (ex : ∀ a, ∃ n, p a n = true) :
    ∃ f : A → ℕ, Computable f ∧ ∀ a, p a (f a) = true := by
  classical
  have dom (a : A) : (Nat.rfind (fun i => Part.some (p a i))).Dom := by
    obtain ⟨i, hi⟩ := ex a
    obtain ⟨j, hj, _⟩ := Nat.rfind_min' hi
    exact Part.dom_iff_mem.mpr ⟨j, hj⟩
  let f a := (Nat.rfind (fun i => Part.some (p a i))).get (dom a)
  have mem (a : A) : f a ∈ Nat.rfind (fun i => Part.some (p a i)) := Part.get_mem _
  refine ⟨f, (Partrec.rfind (p := fun a i => Part.some (p a i)) hp.partrec).of_eq_tot mem, ?_⟩
  intro a
  exact (Part.mem_some_iff.mp (Nat.rfind_spec (mem a))).symm

private def extendConstant (h : List ℕ) (x t : ℕ) := h ++ List.replicate t x

theorem replicate_computable : Computable₂ (List.replicate (α := ℕ)) := by
  have hm := @ComputableLists.map (ℕ × ℕ) ℕ ℕ _ _ _ _
    (fun p => List.range p.1) (fun p _ => p.2) (Primrec.list_range.to_comp.comp Computable.fst)
    (Computable.snd.comp Computable.fst).to₂
  exact hm.of_eq fun p => by simp

/-- Each stage inserts a prescribed datum and then searches for a finite
constant extension on which the learner changes its guess. Every inserted
datum belongs to the supplied range. -/
theorem mind_change_stream {N : Type*} [Primcodable N]
    (M : List ℕ → N) (hc : Computable M) (v : ℕ → ℕ) (hv : Computable v)
    (change : ∀ h : List ℕ, ∃ a t, M (h ++ List.replicate t (v a)) ≠ M h) :
    ∃ s : ℕ → ℕ, Computable s ∧ Set.range s = Set.range v ∧
      ∀ T, ∃ u ≥ T, ∃ w ≥ T, M (textPrefix s u) ≠ M (textPrefix s w) := by
  classical
  let ext (h : List ℕ) (j : ℕ) := extendConstant h (v j.unpair.1) j.unpair.2
  have he : Computable₂ ext :=
    (Computable.list_append.comp Computable.fst (replicate_computable.comp
      (Computable.snd.comp (Computable.unpair.comp Computable.snd))
      (hv.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))))).to₂
  let p (h : List ℕ) (j : ℕ) := decide (M (ext h j) ≠ M h)
  have hcP : Computable₂ p := by
    apply (Primrec.not.to_comp.comp (Primrec.beq.to_comp.comp (hc.comp he) (hc.comp Computable.fst))).of_eq
    intro z
    apply Bool.eq_iff_iff.mpr
    simp [p]
  obtain ⟨q, hq, hqP⟩ := computable_choice_nat hcP (fun h => by
    obtain ⟨a, t, good⟩ := change h
    exact ⟨Nat.pair a t, by simpa [p, ext, extendConstant] using good⟩)
  let seed (n : ℕ) (h : List ℕ) := h ++ [v n]
  let next (n : ℕ) (h : List ℕ) := ext (seed n h) (q (seed n h))
  have seed_comp : Computable₂ seed :=
    (Computable.list_append.comp Computable.snd (Computable.list_cons.comp (hv.comp Computable.fst)
      (Computable.const []))).to₂
  have next_comp : Computable₂ next := (he.comp seed_comp (hq.comp seed_comp)).to₂
  let H : ℕ → List ℕ := Nat.rec ([] : List ℕ) next
  have hH : Computable H :=
    Computable.nat_rec Computable.id (Computable.const []) (next_comp.comp (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)).to₂
  let chain : HistoryChain ℕ := {
    history := H
    prefix_succ := fun n => by
      change H n <+: ((H n ++ [v n]) ++ _)
      exact (List.prefix_append ..).trans (List.prefix_append ..)
    le_length := fun n => by
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
        change n + 1 ≤ ((H n ++ [v n]) ++ List.replicate _ _).length
        simp only [List.length_append, List.length_replicate, List.length_singleton]
        omega }
  have atBoundary (s : ℕ) (h : List ℕ) (hp : h <+: H s) :
      textPrefix chain.stream h.length = h := by
    apply List.ext_getElem
    · simp
    · intro x hx hy
      have hz := (List.prefix_iff_getElem.mp hp).1
      have hpos : x < (H s).length := lt_of_lt_of_le hy hz
      simpa [textPrefix, hy] using (chain.stream_eq_get s x hpos).trans
        ((List.prefix_iff_getElem.mp hp).2 x hy).symm
  have inside (n : ℕ) : ∀ x ∈ H n, x ∈ Set.range v := by
    induction n with
    | zero => simp [H]
    | succ n ih =>
      intro x hx
      change x ∈ (H n ++ [v n]) ++ List.replicate _ _ at hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with (h | rfl) | h
      · exact ih _ h
      · exact Set.mem_range_self _
      · exact List.eq_of_mem_replicate h ▸ Set.mem_range_self _
  refine ⟨chain.stream, ?_, Set.Subset.antisymm ?_ ?_, fun T => ?_⟩
  · apply (Computable.option_getD (Computable.list_getElem?.comp
      (hH.comp Primrec.succ.to_comp) Computable.id) (Computable.const 0)).of_eq
    intro k
    have hl := chain.le_length (k+1)
    change k+1 ≤ (H (k+1)).length at hl
    simp [HistoryChain.stream, chain, List.getElem?_eq_getElem (Nat.lt_of_succ_le hl)]
  · rintro x ⟨k, rfl⟩
    apply inside (k+1)
    exact List.get_mem ..
  · rintro x ⟨k,rfl⟩
    apply chain.history_toFinset_subset_stream_range (k+1)
    change v k ∈ ((H k ++ [v k]) ++ List.replicate _ _).toFinset
    simp
  · let b := seed T (H T)
    have hb : b <+: H (T+1) := List.prefix_append ..
    have hu := chain.le_length T
    change T ≤ (H T).length at hu
    refine ⟨(H (T+1)).length, (Nat.le_succ _).trans (chain.le_length _),
      b.length, by simpa [b, seed] using hu.step, ?_⟩
    rw [atBoundary (T+1) _ (List.prefix_refl _), atBoundary (T+1) _ hb]
    exact of_decide_eq_true (hqP b)

end GenLimit.Gold.Effective
