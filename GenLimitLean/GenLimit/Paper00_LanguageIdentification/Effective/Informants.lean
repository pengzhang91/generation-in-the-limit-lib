import GenLimit.Paper00_LanguageIdentification.Effective.FunctionLearning
import GenLimit.Paper00_LanguageIdentification.Informant.Enumeration

/-! # Arbitrary, methodical and request informants (Appendix I.3) -/

namespace GenLimit.Gold.Effective

open Informant GenLimit.Support

def arbitraryInformant : Method InformantDatum := fun L => {s | IsInformantFor s L}

/-- Answers to an adaptive, computable query rule. Previous answers suffice
to reconstruct the words requested on all preceding rounds. -/
noncomputable def transcript (q : List ℕ → ℕ) (L : Language) : ℕ → List ℕ :=
  Nat.rec [] (fun _ h => h ++ [bit L (q h)])

def RequestIdentifiable {N : Type*} [Primcodable N] (names : NameRelation N) (C : Set Language) :=
  ∃ q : List ℕ → ℕ, ∃ M : List ℕ → N, Computable q ∧ Computable M ∧
    ∀ L ∈ C, ∃ a, names a L ∧ ∃ T, ∀ t ≥ T, M (transcript q L t) = a

private def annotate (h : List ℕ) := (List.range h.length).map fun i => (i, h[i]? == some 1)

private theorem annotate_comp : Computable annotate := by
  apply (ComputableLists.map (Primrec.list_range.to_comp.comp Computable.list_length)
    (Computable.snd.pair (Primrec.beq.to_comp.comp Computable.list_getElem? (Computable.const (some 1)))).to₂).of_eq
  intro h
  apply List.map_congr_left
  intro x _
  apply Prod.ext
  · rfl
  · apply Bool.eq_iff_iff.mpr
    simp

theorem methodical_of_arbitrary {N : Type*} [Primcodable N] {names : NameRelation N} {C}
    (h : Identifiable names arbitraryInformant C) : Identifiable names methodical C := by
  classical
  obtain ⟨M,hc,hm⟩ := h
  refine ⟨M ∘ annotate,hc.comp annotate_comp,fun L hL s hs => ?_⟩
  obtain rfl : s = bit L := hs
  let info (i : ℕ) : InformantDatum := (i, decide (i ∈ L))
  have valid : IsInformantFor info L := ⟨fun t => by simp [info], fun x => ⟨x,rfl⟩⟩
  obtain ⟨a,ha,T,hT⟩ := hm L hL info valid
  refine ⟨a,ha,T,fun t ht => ?_⟩
  have eq : annotate (textPrefix (bit L) t) = textPrefix info t := by
    unfold annotate
    rw [textPrefix_length]
    apply List.map_congr_left
    intro i hi
    have hlt := List.mem_range.mp hi
    by_cases hin : i ∈ L <;> simp [textPrefix, bit, info, hlt, hin]
  exact (congrArg M eq).trans (hT t ht)

theorem request_of_methodical {N : Type*} [Primcodable N] {names : NameRelation N} {C}
    (h : Identifiable names methodical C) : RequestIdentifiable names C := by
  obtain ⟨M,hc,hm⟩ := h
  refine ⟨List.length,M,Computable.list_length,hc,fun L hL => ?_⟩
  obtain ⟨a,ha,T,stable⟩ := hm L hL (bit L) rfl
  have eq (t : ℕ) : transcript List.length L t = textPrefix (bit L) t := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [textPrefix_succ]
      change transcript List.length L t ++ [bit L (transcript List.length L t).length] = _
      rw [ih, textPrefix_length]
  exact ⟨a,ha,T,fun t ht => (congrArg M (eq t)).trans (stable t ht)⟩

private def replayStep (q : List ℕ → ℕ) (h : List InformantDatum) (ans : List ℕ) :=
  match h.lookup (q ans) with
  | none => ans
  | some b => ans ++ [b.toNat]

private def replay (q : List ℕ → ℕ) (h : List InformantDatum) : ℕ → List ℕ :=
  Nat.rec [] fun _ => replayStep q h

private theorem replay_succ (q h u) :
    replay q h (u+1) = replayStep q h (replay q h u) := rfl

private theorem replay_comp {q : List ℕ → ℕ} (hq : Computable q) :
    Computable (fun h : List InformantDatum => replay q h h.length) := by
  apply Computable.nat_rec (h := fun h z => replayStep q h z.2) Computable.list_length (Computable.const [])
  have ans : Computable (fun p : List InformantDatum × (ℕ × List ℕ) => p.2.2) :=
    Computable.snd.comp Computable.snd
  have get := Primrec.listLookup.to_comp.comp (hq.comp ans) Computable.fst
  have add := Computable.list_append.comp (ans.comp Computable.fst)
    (Computable.list_cons.comp ((Primrec.dom_bool Bool.toNat).to_comp.comp Computable.snd) (Computable.const []))
  apply (Computable.option_casesOn get ans add.to₂).of_eq
  intro p
  unfold replayStep
  dsimp only
  cases p.1.lookup (q p.2.2) <;> rfl

private theorem cache_sound {s : InformantStream} {L : Language} (hs : IsInformantFor s L)
    {n x b} (found : (textPrefix s n).lookup x = some b) : b.toNat = bit L x := by
  classical
  obtain ⟨l,r,eq,_⟩ := List.lookup_eq_some_iff.mp found
  have mem : (x,b) ∈ textPrefix s n := by simp [eq]
  obtain ⟨t,_,ht⟩ := mem_textPrefix_iff.mp mem
  have h := hs.correct t
  rw [ht] at h
  cases b <;> simp_all [bit]

private theorem cache_eventually {s : InformantStream} {L} (hs : IsInformantFor s L) (x : ℕ) :
    ∃ T, ∀ t ≥ T, ∃ b, (textPrefix s t).lookup x = some b := by
  obtain ⟨i,hi⟩ := hs.complete x
  refine ⟨i+1,fun t ht => Option.ne_none_iff_exists'.mp (fun h => ?_)⟩
  have hm := mem_textPrefix_iff.mpr (show ∃ j < t, s j = s i from ⟨i, by omega, rfl⟩)
  have bad := List.lookup_eq_none_iff.mp h (s i) hm
  simp [hi] at bad

/-- An arbitrary informant can simulate a request learner even when an
answer was supplied only once, before the learner first asked for it. -/
theorem arbitrary_of_request {N : Type*} [Primcodable N] {names : NameRelation N} {C}
    (h : RequestIdentifiable names C) : Identifiable names arbitraryInformant C := by
  obtain ⟨q,M,hq,hc,learns⟩ := h
  refine ⟨fun h => M (replay q h h.length),hc.comp (replay_comp hq),fun L hL s hs => ?_⟩
  obtain ⟨a,ha,T,stable⟩ := learns L hL
  obtain ⟨S,hS⟩ := eventually_forall_lt (n := T) fun i _ =>
    cache_eventually hs (q (transcript q L i))
  refine ⟨a,ha,max S T,fun t ht => ?_⟩
  let data := textPrefix s t
  have sim (u : ℕ) : ∃ i, min T u ≤ i ∧ replay q data u = transcript q L i := by
    induction u with
    | zero => exact ⟨0,by simp,rfl⟩
    | succ u ih =>
      obtain ⟨i,hi,he⟩ := ih
      cases hget : data.lookup (q (transcript q L i)) with
      | none =>
        have hti : T ≤ i := by
          by_contra! h
          obtain ⟨b,hb⟩ := hS t ((le_max_left ..).trans ht) i h
          rw [hget] at hb
          contradiction
        exact ⟨i, (min_le_left ..).trans hti, by rw [replay_succ, he]; simp [replayStep, hget]⟩
      | some b =>
        have hb := cache_sound hs hget
        refine ⟨i+1, by omega, ?_⟩
        rw [replay_succ, he]
        change replayStep _ _ _ = transcript q L i ++ [_]
        simp [replayStep, hget, hb]
        rfl
  obtain ⟨i,hi,he⟩ := sim t
  change M (replay q data (textPrefix s t).length) = a
  rw [textPrefix_length, he]
  exact stable i (by have := (le_max_right S T).trans ht; omega)

theorem informants_equivalent {N : Type*} [Primcodable N] (names : NameRelation N) (C : Set Language) :
    (Identifiable names arbitraryInformant C ↔ Identifiable names methodical C) ∧
    (Identifiable names methodical C ↔ RequestIdentifiable names C) :=
  ⟨⟨methodical_of_arbitrary, fun h => arbitrary_of_request (request_of_methodical h)⟩,
    ⟨request_of_methodical, fun h => methodical_of_arbitrary (arbitrary_of_request h)⟩⟩

/-- §8: a countable class with arbitrary chosen names can be learned
semantically from its complete informants. -/
theorem countable_arbitrary_informant {N : Type*} [Nonempty N] (names : NameRelation N)
    (C : Set Language) (hc : C.Countable) (hn : ∀ L ∈ C, ∃ n, names n L) :
    ∃ M, Learns M names arbitraryInformant C := by
  classical
  by_cases he : C.Nonempty
  · letI : Nonempty C := he.to_subtype
    letI : Countable C := hc.to_subtype
    obtain ⟨e, onto⟩ := exists_surjective_nat C
    let E (i : ℕ) : Language := (e i).val
    let pick (i : ℕ) := (hn (E i) (e i).property).choose
    refine ⟨pick ∘ informantEnumerationLearner E,fun L hL s hs => ?_⟩
    obtain ⟨i,hi⟩ := onto ⟨L,hL⟩
    have eq : E i = L := congrArg Subtype.val hi
    obtain ⟨j,hj,T,stable⟩ := informantEnumerationLearner_identifiesFamily E i s (eq.symm ▸ hs)
    have hlj : E j = L := hj.trans eq
    exact ⟨pick j, hlj ▸ (hn (E j) (e j).property).choose_spec, T,fun t ht => congrArg pick (stable t ht)⟩
  · exact ⟨fun _ => Classical.arbitrary N,fun L hL => (he ⟨L,hL⟩).elim⟩

end GenLimit.Gold.Effective
