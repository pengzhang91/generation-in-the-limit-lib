import GenLimit.Paper22_LanguageGenerationWithReplay.ProperDiagonalStage
import GenLimit.Support.HistoryChainText

/-! A computable diagonal family for Theorem 7.1. Each selected transcript
forces a nonzero output on an increasing prefix of the even words. Row zero
contains exactly those words. Each other row receives a private odd word
beyond every membership query made before its marker was committed. -/

namespace GenLimit.Replay.ProperDiagonal

open Encodable
open Support.AdaptiveMembershipDialogue

private def trial (A : ProperMembershipAlgorithm) (s : State) (n : ℕ) : Option Candidate :=
  let c := (decode (α := Candidate) n).getD default
  cond (accepts A s c) (some c) none

private theorem search_dom {A : ProperMembershipAlgorithm} (hu : UniversalProperMembershipGenerator A)
    (s : State) : (Nat.rfindOpt (trial A s)).Dom := by
  obtain ⟨c, hc⟩ := accepted_exists hu s
  exact Nat.rfindOpt_dom.mpr ⟨encode c, c, by simp [trial, encodek, hc]⟩

private def pick {A : ProperMembershipAlgorithm} (hu : UniversalProperMembershipGenerator A)
    (s : State) : Candidate := (Nat.rfindOpt (trial A s)).get (search_dom hu s)

private theorem pick_comp {A : ProperMembershipAlgorithm} (hu : UniversalProperMembershipGenerator A) :
    Computable (pick hu) := by
  have cand : Computable (fun z : State × ℕ => (decode (α := Candidate) z.2).getD default) :=
    Computable.option_getD (Computable.decode.comp Computable.snd) (Computable.const default)
  have h : Computable₂ (trial A) := (Computable.cond ((accepts_comp hu.1).comp Computable.fst cand)
    (Computable.option_some.comp cand) (Computable.const none)).to₂
  exact (Partrec.rfindOpt h).of_eq_tot fun s => Part.get_mem (search_dom hu s)

private theorem pick_valid {A : ProperMembershipAlgorithm} (hu : UniversalProperMembershipGenerator A)
    (s : State) : accepts A s (pick hu s) = true := by
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec (Part.get_mem (search_dom hu s))
  change trial A s n = some (pick hu s) at hn
  let c := (decode (α := Candidate) n).getD default
  change cond (accepts A s c) (some c) none = some (pick hu s) at hn
  cases hc : accepts A s c <;> simp [hc] at hn
  exact hn ▸ hc

private def newMarker (s : State) (c : Candidate) := encode s.1 + encode (roundList c) + 1

private def step {A : ProperMembershipAlgorithm} (hu : UniversalProperMembershipGenerator A) (s : State) : State :=
  let c := pick hu s
  (s.1 ++ [newMarker s c], digits s c)

private def stage {A : ProperMembershipAlgorithm} (hu : UniversalProperMembershipGenerator A) : ℕ → State :=
  Nat.rec ([],[]) (fun _ s => step hu s)

private theorem stage_comp {A : ProperMembershipAlgorithm} (hu : UniversalProperMembershipGenerator A) :
    Computable (stage hu) := by
  have marker : Computable (fun s : State => newMarker s (pick hu s)) :=
    Computable.succ.comp (Primrec.nat_add.to_comp.comp (Computable.encode.comp Computable.fst)
      (Computable.encode.comp (rounds_comp (pick_comp hu))))
  have hs : Computable (step hu) := (Computable.list_concat.comp Computable.fst marker).pair
    (digits_comp Computable.id (pick_comp hu))
  exact Computable.nat_rec Computable.id (Computable.const ([],[]))
    (hs.comp (Computable.snd.comp Computable.snd)).to₂

variable {A : ProperMembershipAlgorithm} (hu : UniversalProperMembershipGenerator A)

private abbrev cuts (n : ℕ) := (stage hu n).1
private abbrev history (n : ℕ) := (stage hu n).2
private abbrev chosen (n : ℕ) := pick hu (stage hu n)
private abbrev marker (n : ℕ) := newMarker (stage hu n) (chosen hu n)

private theorem cuts_succ (n : ℕ) : cuts hu (n+1) = cuts hu n ++ [marker hu n] := rfl

private theorem cuts_length (n : ℕ) : (cuts hu n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [cuts_succ, ih]

private theorem history_succ (n : ℕ) :
    history hu (n+1) = history hu n ++ [n] ++ (chosen hu n).1 := by
  change ((stage hu n).2 ++ [(cuts hu n).length]) ++ _ = _
  rw [cuts_length]
  rfl

private theorem nth_cut {n k : ℕ} (hk : k < n) : (cuts hu n)[k]? = some (marker hu k) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [cuts_succ]
    by_cases h : k < n
    · rw [List.getElem?_append_left (by simpa [cuts_length] using h)]
      exact ih h
    · have he : k = n := by omega
      subst k
      simp [cuts_length]

private theorem marker_mono : StrictMono (marker hu) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have mem : marker hu n ∈ cuts hu (n+1) := by simp [cuts_succ]
  have bound := coordinate_le_code mem
  change marker hu n ≤ encode (cuts hu (n+1)) at bound
  change marker hu n < encode (cuts hu (n+1)) + _ + 1
  omega

private def finalQuery (i x : ℕ) := answer (some (marker hu i.pred)) i x

private theorem final_recursive : IsRecursiveUUSFamily (rows (finalQuery hu)) := by
  have hm : Computable (marker hu) := Computable.succ.comp (Primrec.nat_add.to_comp.comp
    (Computable.encode.comp (Computable.fst.comp (stage_comp hu)))
    (Computable.encode.comp (rounds_comp ((pick_comp hu).comp (stage_comp hu)))))
  exact ⟨⟨finalQuery hu,Iff.rfl⟩, (answer_comp
    (Computable.option_some.comp (hm.comp (Computable.pred.comp Computable.fst)))
    Computable.fst Computable.snd).to₂, row_infinite _⟩

private theorem agrees (n i x : ℕ) (hx : x ≤ encode (roundList (chosen hu n))) :
    finalQuery hu i x = temporary (cuts hu n) i x := by
  cases i with
  | zero => simp [finalQuery, temporary, answer]
  | succ k =>
    by_cases h : k < n
    · simp [finalQuery, temporary, nth_cut hu h]
    · have hm := (marker_mono hu).monotone (Nat.le_of_not_gt h)
      have hb : x < marker hu n := by unfold marker newMarker; omega
      have hd : x.div2 < marker hu k := by
        have := Nat.div_le_self x 2
        rw [Nat.div2_val]
        omega
      have hn : (cuts hu n)[k]? = none := List.getElem?_eq_none (by simp [cuts_length]; omega)
      simp [finalQuery, temporary, answer, hn, Nat.ne_of_gt hd]

private theorem fst_bound {α β} [Encodable α] [Encodable β] (p : α × β) :
    encode p.1 ≤ encode p := Nat.left_le_pair ..

private theorem snd_bound {α β} [Encodable α] [Encodable β] (p : α × β) :
    encode p.2 ≤ encode p := Nat.right_le_pair ..

private theorem transfer (n : ℕ) (rs : List ProperMembershipRound) (hr : rs = roundList (chosen hu n))
    (xs : List ℕ) (he : ProperMembershipExecutionValid A (rows (temporary (cuts hu n))) xs rs) :
    ProperMembershipExecutionValid A (rows (finalQuery hu)) xs rs := by
  refine ⟨he.1, fun k hki hkr => ?_⟩
  obtain ⟨hi, trace, out⟩ := he.2 k hki hkr
  refine ⟨hi, fun j hj => ?_, out⟩
  obtain ⟨ask, ans⟩ := trace j hj
  refine ⟨ask, ?_⟩
  let r := rs[k]
  let qa := r.2.1[j]
  have bound : qa.1.2 ≤ encode rs :=
    (snd_bound qa.1).trans ((fst_bound qa).trans ((coordinate_le_code
      (List.getElem_mem (l := r.2.1) hj)).trans ((fst_bound r.2).trans
        ((snd_bound r).trans (coordinate_le_code (List.getElem_mem hkr))))))
  change qa.2 = true ↔ finalQuery hu qa.1.1 qa.1.2 = true
  rw [agrees hu n _ _ (hr ▸ bound)]
  exact ans

private def chain : Support.HistoryChain ℕ where
  history := history hu
  prefix_succ n := by rw [history_succ, List.append_assoc]; exact List.prefix_append ..
  le_length n := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => simp only [history_succ, List.length_append, List.length_singleton]; omega

private theorem presents : Generic.Presents (fun t => evenWord ((chain hu).stream t))
    (rows (finalQuery hu) 0) := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact (answer_even ..).2 (Or.inl rfl)
  · intro h
    have he : x.bodd = false := by
      change answer _ 0 x = true at h
      cases hb : x.bodd <;> simp_all [answer]
    have mem : x.div2 ∈ (chain hu).history (x.div2+1) := by
      change _ ∈ history hu _
      simp [history_succ]
    obtain ⟨t, ht⟩ := (chain hu).history_toFinset_subset_stream_range _ (List.mem_toFinset.mpr mem)
    refine ⟨t, ?_⟩
    change evenWord ((chain hu).stream t) = x
    rw [ht]
    simpa [evenWord, he] using Nat.bit_bodd_div2 x

theorem impossibility : Theorem71Statement := by
  rintro ⟨A, hu⟩
  let stream := fun t => evenWord ((chain hu).stream t)
  obtain ⟨_,n,hcorrect⟩ := hu.2 _ (final_recursive hu) 0 stream (presents hu)
  let c := chosen hu n
  have hv := pick_valid hu (stage hu n)
  change accepts A (stage hu n) c = true at hv
  simp only [accepts, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hv
  obtain ⟨⟨checked, inputs⟩, nonzero⟩ := hv
  have run := transfer hu n (roundList c) rfl _ ((checkRun_spec ..).1 checked)
  change (roundList c).map Prod.fst = (history hu (n+1)).map evenWord at inputs
  have len : c.2.1.length + 1 = (history hu (n+1)).length := by
    simpa [roundList] using congrArg List.length inputs
  have hprefix : inputPrefix stream (c.2.1.length+1) = (roundList c).map Prod.fst := by
    rw [inputs, len]
    have he := congrArg (List.map evenWord) ((chain hu).textPrefix_stream (n+1))
    simpa only [inputPrefix, stream, textPrefix_eq_ofFn, List.map_ofFn, chain] using he
  have houtput : ProperMembershipExecutionOutputsAt A (rows (finalQuery hu)) stream c.2.1.length c.2.2.2.2 := by
    refine ⟨roundList c, hprefix ▸ run, by simp [roundList], ?_⟩
    simp [roundList]
  have enough := (chain hu).le_length (n+1)
  change n+1 ≤ (history hu (n+1)).length at enough
  have sub := hcorrect c.2.1.length (by omega) _ houtput
  let i := c.2.2.2.2
  let x := Nat.bit true (marker hu i.pred)
  have hx : x ∈ rows (finalQuery hu) i := by
    change answer _ i x = true
    simp [i,x, answer, Nat.bodd_bit, Nat.div2_bit, nonzero]
  have bad := sub hx
  change answer _ 0 x = true at bad
  simp [x, answer, Nat.bodd_bit] at bad

end GenLimit.Replay.ProperDiagonal
