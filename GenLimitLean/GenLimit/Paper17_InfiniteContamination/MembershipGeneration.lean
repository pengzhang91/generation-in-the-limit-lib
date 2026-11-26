import GenLimit.Paper03_HallucinationAndModeCollapse.OracleGeneration
import GenLimit.Paper17_InfiniteContamination.FiniteExpansionTransfer
import GenLimit.Support.ComputableLists
import GenLimit.Core.Text

/-! # Membership-query generation under finite contamination

One fixed oracle search asks membership queries for a finite expansion of
the original family. Each round starts above the previous output. The state
can be reconstructed from the finite input history alone.
-/

namespace GenLimit.InfiniteContamination
open Support HallucinationModeCollapse

private def stripBound (data : GenerationTable) : GenerationTable :=
  ((data.1.1.tail, data.1.2), data.2)

private theorem stripBound_primrec : Primrec stripBound :=
  (((Primrec.list_tail.comp (Primrec.fst.comp Primrec.fst)).pair
    (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)

private def boundedPost (data : GenerationTable) : Option ℕ :=
  let bound := data.1.1.headI
  let y := data.1.2.unpair.1 - 1
  if generationHasConsistent (stripBound data) then
    if generationAccept (stripBound data) ∧ bound < y then some y else none
  else some (bound + 1)

private theorem boundedPost_computable : Computable boundedPost := by
  have hb : Primrec (fun data : GenerationTable ↦ data.1.1.headI) :=
    Primrec.list_headI.comp (Primrec.fst.comp Primrec.fst)
  have hy : Primrec (fun data : GenerationTable ↦ data.1.2.unpair.1 - 1) :=
    Primrec.pred.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))
  exact (Primrec.ite (generationHasConsistent_primrec.comp stripBound_primrec)
    (Primrec.ite ((generationAccept_primrec.comp stripBound_primrec).and (Primrec.nat_lt.comp hb hy))
      (Primrec.option_some.comp hy) (Primrec.const none))
    (Primrec.option_some.comp (Primrec.succ.comp hb))).to_comp

/-- Input consists of the previous output followed by the ordered sample. -/
def boundedMembershipProgram : OracleSearchProgram where
  queries := fun p ↦ generationQueries (p.1.tail, p.2)
  queries_primrec := generationQueries_primrec.comp ((Primrec.list_tail.comp Primrec.fst).pair Primrec.snd)
  output := boundedPost
  output_computable := boundedPost_computable

private theorem stage_eq (O : OracleFamily) (input : List ℕ) (q : ℕ) :
    boundedMembershipProgram.stage (generationOracle O) input q =
      if generationHasConsistent (generationData O input.tail q) then
        if generationAccept (generationData O input.tail q) ∧ input.headI < q.unpair.1-1
        then some (q.unpair.1-1) else none
      else some (input.headI+1) := rfl

theorem boundedMembershipProgram_terminates (O : OracleFamily) :
    boundedMembershipProgram.Terminates (generationOracle O) := by
  intro input
  by_cases h : O.HasConsistent (listStream input.tail) input.tail.length
  · obtain ⟨q, ha, hb⟩ := exists_generationAccept_above O input.tail input.headI h
    exact ⟨q, _, by rw [stage_eq, if_pos ((generationHasConsistent_correct ..).mpr h),
      if_pos ⟨ha, hb⟩]⟩
  · exact ⟨0, _, by rw [stage_eq, if_neg (fun hh ↦ h ((generationHasConsistent_correct ..).mp hh))]⟩

private def runRound (O : OracleFamily) :=
  boundedMembershipProgram.run (generationOracle O) (boundedMembershipProgram_terminates O)

private theorem runRound_spec (O : OracleFamily) (xs : List ℕ) (b : ℕ) :
    b < runRound O (b :: xs) ∧
      ∀ z < xs.length, Critical O.language (listStream xs) xs.length z →
        runRound O (b :: xs) ∈ O.language z ∧ runRound O (b :: xs) ∉ xs := by
  obtain ⟨q, hq⟩ := boundedMembershipProgram.run_stage (generationOracle O)
    (boundedMembershipProgram_terminates O) (b :: xs)
  change _ = some (runRound O (b :: xs)) at hq
  rw [stage_eq] at hq
  simp only [List.tail_cons, List.headI] at hq
  split at hq
  · split at hq
    · rename_i ha
      rw [← Option.some.inj hq]
      exact ⟨ha.2, fun z hz hc ↦ generationAccept_correct O xs q z hc hz ha.1⟩
    · contradiction
  · rename_i hno
    refine ⟨(Option.some.inj hq) ▸ Nat.lt_succ_self b, ?_⟩
    intro z hz hc
    exact False.elim (hno ((generationHasConsistent_correct ..).mpr
      ⟨z, O.mem_consistentCandidates.mpr ⟨hz, O.consistentAt_iff.mpr hc.1⟩⟩))

private def replayStep (run : List ℕ → ℕ) (state : List ℕ × ℕ) (x : ℕ) : List ℕ × ℕ :=
  let xs := state.1 ++ [x]
  (xs, run (state.2 :: xs))

private def replayState (run : List ℕ → ℕ) (xs : List ℕ) : List ℕ × ℕ :=
  xs.foldl (replayStep run) ([], 0)

private theorem replayState_history (run : List ℕ → ℕ) (xs : List ℕ) :
    (replayState run xs).1 = xs := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih => simp [replayState, List.foldl_append, replayStep] at ih ⊢; exact ih

/-- The fixed finite-history controller calls the round machine once per observation. -/
def membershipReplay (run : List ℕ → ℕ) (xs : List ℕ) : ℕ := (replayState run xs).2

private theorem replay_succ (run : List ℕ → ℕ) (s : Generic.Stream ℕ) (t : ℕ) :
    membershipReplay run (textPrefix s (t+1)) =
      run (membershipReplay run (textPrefix s t) :: textPrefix s (t+1)) := by
  rw [textPrefix_succ]
  simp only [membershipReplay, replayState, List.foldl_append, List.foldl_cons, List.foldl_nil, replayStep]
  rw [show ((textPrefix s t).foldl (replayStep run) ([],0)).1 = _ from replayState_history run _]

theorem membershipReplay_computable {run : List ℕ → ℕ} (hr : Computable run) :
    Computable (membershipReplay run) := by
  have hxs : Computable (fun p : (List ℕ × ℕ) × ℕ ↦ p.1.1 ++ [p.2]) :=
    Computable.list_append.comp (Computable.fst.comp Computable.fst)
      (Computable.list_cons.comp Computable.snd (Computable.const []))
  have hstep : Computable₂ (replayStep run) :=
    (hxs.pair (hr.comp (Computable.list_cons.comp (Computable.snd.comp Computable.fst) hxs))).to₂
  exact Computable.snd.comp (ComputableLists.foldl Computable.id (Computable.const ([],0))
    (hstep.comp (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)).to₂)

def replayGenerator (run : List ℕ → ℕ) : Generic.Generator ℕ :=
  fun _ xs ↦ membershipReplay run (List.ofFn xs)

private theorem replay_output (run : List ℕ → ℕ) (s : Generic.Stream ℕ) (t : ℕ) :
    Generic.output (replayGenerator run) s t = membershipReplay run (textPrefix s t) := by
  rw [textPrefix_eq_ofFn]; rfl

/-- Exact presentation for any oracle family, with freshness relative to all earlier outputs. -/
theorem replay_generates (O : OracleFamily) (z : ℕ) (s : Generic.Stream ℕ)
    (hs : Generic.Presents s (O.language z)) :
    GeneratesElementInLimitOn (replayGenerator (runRound O)) (O.language z) s := by
  let run := runRound O
  have mono : StrictMono (fun t ↦ membershipReplay run (textPrefix s t)) := by
    apply strictMono_nat_of_lt_succ
    intro t
    rw [replay_succ]
    exact (runRound_spec ..).1
  obtain ⟨T,hT,hcrit⟩ := exists_KM_witness O.language z
  obtain ⟨n,hn⟩ := Generic.finset_eventually_subset_sample hs T hT
  refine ⟨max n z + 1, ?_⟩
  intro t ht
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t ≠ 0 by omega)
  let xs := textPrefix s (r+1)
  have crit : Critical O.language (listStream xs) xs.length z := by
    apply hcrit
    · intro x hx
      rw [← hs]
      obtain ⟨k,_,rfl⟩ := mem_textPrefix_iff.mp hx
      exact Set.mem_range_self _
    · intro x hx
      exact mem_textPrefix_iff.mpr (Generic.mem_sample_iff.mp (Generic.sample_mono (by omega : n ≤ r+1) (hn hx)))
  have hzt : z < xs.length := by simp [xs]; omega
  have hgood := (runRound_spec O xs (membershipReplay run (textPrefix s r))).2 z hzt crit
  change FreshElementCorrectAt (replayGenerator run) _ _ _
  unfold FreshElementCorrectAt
  rw [replay_output, replay_succ]
  refine ⟨hgood.1, fun hx ↦ hgood.2 (mem_textPrefix_iff.mpr (Generic.mem_sample_iff.mp hx)), ?_⟩
  rintro hx
  obtain ⟨k,hk,he⟩ := mem_generatedBefore_iff.mp hx
  rw [replay_output, ← replay_succ run s r] at he
  exact (mono hk).ne he

/-- A finite expansion is indexed by a base index and two finite edit lists. -/
def expansionEdits (j : ℕ) : ℕ × List ℕ × List ℕ :=
  (Encodable.decode j).getD (0, [], [])

def membershipExpansion (O : OracleFamily) : OracleFamily where
  language j := finiteExpansion (O.language (expansionEdits j).1)
    {x | x ∈ (expansionEdits j).2.1} {x | x ∈ (expansionEdits j).2.2}
  infinite' j := ((O.infinite' _).mono Set.subset_union_left).diff (List.finite_toSet _)
  query j x := (O.query (expansionEdits j).1 x || listContains (expansionEdits j).2.1 x)
    && !listContains (expansionEdits j).2.2 x
  query_spec j x := by simp [finiteExpansion, listContains, O.query_spec]

theorem membershipExpansion_computable (O : OracleFamily) (ho : Computable₂ O.query) :
    Computable₂ (membershipExpansion O).query := by
  have hd : Computable expansionEdits := Computable.option_getD Computable.decode (Computable.const _)
  have hc := hd.comp (Computable.fst (α := ℕ) (β := ℕ))
  have hb := ho.comp (Computable.fst.comp hc) Computable.snd
  have ha := listContains_computable.comp (Computable.fst.comp (Computable.snd.comp hc)) Computable.snd
  have hr := listContains_computable.comp (Computable.snd.comp (Computable.snd.comp hc)) Computable.snd
  exact (Primrec.and.to_comp.comp (Primrec.or.to_comp.comp hb ha) (Primrec.not.to_comp.comp hr)).to₂

theorem membershipExpansion_presents (O : OracleFamily) (z : ℕ) (s : Generic.Stream ℕ)
    (h : FiniteNoiseFiniteOmissionEnumeration s (O.language z)) :
    ∃ j, Generic.Presents s ((membershipExpansion O).language j) := by
  classical
  let e := finiteContamination_expansionWitness h
  let a := e.add_finite.toFinset
  let r := e.remove_finite.toFinset
  let j := Encodable.encode (z, a.toList, r.toList)
  have hj : expansionEdits j = (z, a.toList, r.toList) := by simp [expansionEdits, j]
  refine ⟨j, ?_⟩
  change Set.range s = finiteExpansion (O.language (expansionEdits j).1) _ _
  rw [hj]
  simpa [a, r] using e.expansion_eq.symm

/-- Algorithm 2 and Lemma 4.3 on one indexed expanded family, simultaneously
for element generation, set generation and infinite-set generation. -/
theorem algorithmTwo_transfer (O : OracleFamily) (z : ℕ) (s : Generic.Stream ℕ)
    (h : FiniteNoiseFiniteOmissionEnumeration s (O.language z)) :
    ∃ j, Generic.Presents s ((membershipExpansion O).language j) ∧
      (∀ g, GeneratesElementInLimitOn g ((membershipExpansion O).language j) s →
        GeneratesElementInLimitOn g (O.language z) s) ∧
      (∀ g, GeneratesSetInLimitOn g ((membershipExpansion O).language j) s →
        GeneratesSetInLimitOn g (O.language z) s) ∧
      (∀ g, GeneratesInfiniteSetInLimitOn g ((membershipExpansion O).language j) s →
        GeneratesInfiniteSetInLimitOn g (O.language z) s) := by
  obtain ⟨j,hj⟩ := membershipExpansion_presents O z s h
  refine ⟨j,hj,?_,?_,?_⟩ <;> rw [← show Set.range s = _ from hj]
  · exact fun _ ↦ lemma_4_3_element_finiteExpansion_transfer h
  · exact fun _ ↦ lemma_4_3_set_finiteExpansion_transfer h
  · exact fun _ ↦ lemma_4_3_infiniteSet_finiteExpansion_transfer h

/-- Corollaries 1.2 / 4.5. The same total finite-query machine and replay
controller work on all families. Each expanded membership query uses one
underlying membership query and decidable finite list edits. -/
theorem finiteContamination_membership_machine (O : OracleFamily) :
    ∃ h : boundedMembershipProgram.Terminates (generationOracle (membershipExpansion O)),
      let run := boundedMembershipProgram.run (generationOracle (membershipExpansion O)) h
      (∀ z s, FiniteNoiseFiniteOmissionEnumeration s (O.language z) →
        GeneratesElementInLimitOn (replayGenerator run) (O.language z) s) ∧
      (Computable₂ O.query → Computable (membershipReplay run)) := by
  refine ⟨boundedMembershipProgram_terminates _, ?_, ?_⟩
  · intro z s hs
    obtain ⟨j,hj,he,_,_⟩ := algorithmTwo_transfer O z s hs
    exact he _ (replay_generates _ j s hj)
  · intro ho
    apply membershipReplay_computable
    apply OracleSearchProgram.run_computable
    have hq := membershipExpansion_computable O ho
    exact (Computable.cond (hq.comp (Primrec.fst.comp Primrec.unpair).to_comp
      (Primrec.snd.comp Primrec.unpair).to_comp) (Computable.const 1) (Computable.const 0)).of_eq
      (fun c ↦ by dsimp [generationOracle]; cases (membershipExpansion O).query c.unpair.1 c.unpair.2 <;> simp)

end GenLimit.InfiniteContamination
