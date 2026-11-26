import GenLimit.Paper22_LanguageGenerationWithReplay.ProperDialogueCheck
import GenLimit.Support.StreamPrefixText

/-! Each finite stage searches for a completed, nonzero output on a temporary
recursive family. The target used to justify termination omits one fresh even
word. The final family will preserve all answers in the selected transcript. -/

namespace GenLimit.Replay.ProperDiagonal

open Encodable
open Support.AdaptiveMembershipDialogue

abbrev State := List ℕ × List ℕ  -- odd marker coordinates, input coordinates
abbrev Candidate := List ℕ × (List ProperMembershipRound × ProperMembershipRound)

def evenWord := Nat.bit false

theorem evenWord_comp : Computable evenWord :=
  (Primrec.nat_add.to_comp.comp Computable.id Computable.id).of_eq fun _ => by simp [evenWord, Nat.bit, two_mul]

theorem coordinate_le_code {α : Type*} [Encodable α] {x : α} {xs : List α}
    (hm : x ∈ xs) : encode x ≤ encode xs := by
  induction xs with
  | nil => simp at hm
  | cons a xs ih =>
    simp only [Encodable.encode_list_cons]
    rcases List.mem_cons.mp hm with rfl | h
    · exact (Nat.left_le_pair ..).trans (Nat.le_succ _)
    · exact (ih h).trans ((Nat.right_le_pair ..).trans (Nat.le_succ _))

def answer (mark : Option ℕ) (i x : ℕ) : Bool :=
  cond x.bodd ((!decide (i = 0)) && decide (mark = some x.div2))
    (decide (i = 0) || (!decide (i = x.div2)))

def temporary (cuts : List ℕ) (i x : ℕ) : Bool := answer cuts[i.pred]? i x

theorem answer_comp {σ : Type*} [Primcodable σ] {m : σ → Option ℕ} {i x : σ → ℕ}
    (hm : Computable m) (hi : Computable i) (hx : Computable x) :
    Computable (fun s => answer (m s) (i s) (x s)) := by
  have hz := Primrec.eq.decide.to_comp.comp hi (Computable.const 0)
  have hd := Computable.nat_div2.comp hx
  apply Computable.cond (Computable.nat_bodd.comp hx)
  · exact Primrec.and.to_comp.comp (Primrec.not.to_comp.comp hz)
      (Primrec.eq.decide.to_comp.comp hm (Computable.option_some.comp hd))
  · exact Primrec.or.to_comp.comp hz (Primrec.not.to_comp.comp (Primrec.eq.decide.to_comp.comp hi hd))

theorem temporary_comp {σ : Type*} [Primcodable σ] {cuts : σ → List ℕ} {i x : σ → ℕ}
    (hc : Computable cuts) (hi : Computable i) (hx : Computable x) :
    Computable (fun s => temporary (cuts s) (i s) (x s)) :=
  answer_comp (Computable.list_getElem?.comp hc (Computable.pred.comp hi)) hi hx

@[simp] theorem answer_even (m : Option ℕ) (i k : ℕ) :
    answer m i (evenWord k) = true ↔ i = 0 ∨ i ≠ k := by
  simp [answer, evenWord, Nat.div2_bit, Nat.bodd_bit]

theorem row_infinite (marker : ℕ → Option ℕ) (i : ℕ) :
    (rows (fun j x => answer (marker j) j x) i).Infinite := by
  have inj : Function.Injective (fun n : ℕ => evenWord (i+n+1)) := by
    intro a b h
    have he := congrArg Nat.div2 h
    simp only [evenWord, Nat.div2_bit] at he
    omega
  apply (Set.infinite_range_of_injective inj).mono
  rintro _ ⟨n,rfl⟩
  apply (answer_even ..).2 (Or.inr (by omega))

def roundList (c : Candidate) := c.2.1 ++ [c.2.2]
def base (s : State) := s.2 ++ [s.1.length]
def digits (s : State) (c : Candidate) := base s ++ c.1

def accepts (A : ProperMembershipAlgorithm) (s : State) (c : Candidate) : Bool :=
  checkRun A (temporary s.1) (roundList c) &&
  decide ((roundList c).map Prod.fst = (digits s c).map evenWord) &&
  (!decide (c.2.2.2.2 = 0))

theorem rounds_comp {σ : Type*} [Primcodable σ] {c : σ → Candidate} (hc : Computable c) :
    Computable (fun s => roundList (c s)) :=
  Computable.list_concat.comp (Computable.fst.comp (Computable.snd.comp hc))
    (Computable.snd.comp (Computable.snd.comp hc))

theorem digits_comp {σ : Type*} [Primcodable σ] {s : σ → State} {c : σ → Candidate}
    (hs : Computable s) (hc : Computable c) : Computable (fun z => digits (s z) (c z)) :=
  Computable.list_append.comp (Computable.list_concat.comp (Computable.snd.comp hs)
    (Computable.list_length.comp (Computable.fst.comp hs))) (Computable.fst.comp hc)

theorem accepts_comp {A : ProperMembershipAlgorithm} (hA : Computable A) :
    Computable₂ (accepts A) := by
  let D := State × Candidate
  have rs : Computable (fun z : D => roundList z.2) := rounds_comp Computable.snd
  have a := checkRun_comp (q := fun (z : D) xy => temporary z.1.1 xy.1 xy.2) hA (temporary_comp ((Computable.fst.comp Computable.fst).comp Computable.fst)
    (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)).to₂ rs
  have b := Support.ComputableLists.map (f := fun (_ : D) (rr : ProperMembershipRound) => rr.1) rs (Computable.fst.comp Computable.snd).to₂
  have d := Support.ComputableLists.map (f := fun (_ : D) k => evenWord k) (digits_comp (σ := D) Computable.fst Computable.snd)
    (evenWord_comp.comp Computable.snd).to₂
  have oi : Computable (fun z : D => z.2.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  exact (Primrec.and.to_comp.comp (Primrec.and.to_comp.comp a (Primrec.eq.decide.to_comp.comp b d))
    (Primrec.not.to_comp.comp (Primrec.eq.decide.to_comp.comp oi (Computable.const 0)))).to₂

theorem accepted_exists {A : ProperMembershipAlgorithm} (hu : UniversalProperMembershipGenerator A)
    (s : State) : ∃ c, accepts A s c = true := by
  let r := s.1.length + encode (base s) + 1
  let tail := fun k : ℕ => if k = r then r+1 else k
  let stream := Support.prependStream (base s) tail
  have hr : 0 < r := by dsimp [r]; omega
  have hcut : s.1[r.pred]? = none := by
    apply List.getElem?_eq_none
    dsimp [r]; omega
  have good : ∀ k, stream k ≠ r := by
    intro k
    by_cases h : k < (base s).length
    · rw [show stream k = (base s)[k] from Support.prependStream_apply_of_lt (base s) tail h]
      have he := coordinate_le_code (List.getElem_mem h)
      change (base s)[k] ≤ encode (base s) at he
      dsimp [r]; omega
    · change Support.prependStream (base s) tail k ≠ r
      rw [Support.prependStream_apply_of_not_lt _ _ h]
      dsimp [tail]; split <;> omega
  have pres : Generic.Presents (fun k => evenWord (stream k)) (rows (temporary s.1) r) := by
    ext x
    constructor
    · rintro ⟨k,rfl⟩
      exact (answer_even ..).2 (Or.inr (Ne.symm (good k)))
    · intro hx
      change answer s.1[r.pred]? r x = true at hx
      have he : x.bodd = false := by
        cases hb : x.bodd <;> simp_all [answer]
      have hd : x.div2 ≠ r := by
        simpa [answer, he, Nat.ne_of_gt hr, ne_comm] using hx
      refine ⟨(base s).length + x.div2, ?_⟩
      simp only [stream, Support.prependStream_add, tail, if_neg hd]
      simpa [evenWord, he] using Nat.bit_bodd_div2 x
  have recFam : IsRecursiveUUSFamily (rows (temporary s.1)) :=
    ⟨⟨temporary s.1, Iff.rfl⟩,
      (temporary_comp (Computable.const s.1) Computable.fst Computable.snd).to₂,
      row_infinite (fun i => s.1[i.pred]?)⟩
  obtain ⟨halts, T, correct⟩ := hu.2 _ recFam r _ pres
  let t := max T (base s).length
  obtain ⟨out, hrun⟩ := halts t
  have nonzero : out ≠ 0 := by
    intro hz
    have sub := correct t (le_max_left ..) out hrun
    rw [hz] at sub
    exact ((answer_even ..).1 (sub ((answer_even ..).2 (Or.inl rfl) :
      evenWord r ∈ rows (temporary s.1) 0))).elim (Nat.ne_of_gt hr) (fun h => h rfl)
  obtain ⟨rs, exec, ht, hout⟩ := hrun
  have len : rs.length = t+1 := by simpa [inputPrefix] using exec.1
  have split : rs.take t ++ [rs[t]] = rs := by
    rw [← List.take_succ_eq_append_getElem ht, ← len, List.take_length]
  have inputEq : rs.map Prod.fst = inputPrefix (fun k => evenWord (stream k)) (t+1) := by
    apply List.ext_getElem
    · simpa using exec.1
    · intro k hk hl
      simpa using (exec.2 k hl (by simpa using hk)).1
  let n := t + 1 - (base s).length
  have hn : (base s).length + n = t+1 := by
    have := le_max_right T (base s).length
    dsimp [n,t]; omega
  refine ⟨(textPrefix tail n, rs.take t, rs[t]), ?_⟩
  have hinput : inputPrefix (fun k => evenWord (stream k)) (t+1) =
      (base s ++ textPrefix tail n).map evenWord := by
    rw [← Support.textPrefix_prependStream]
    change List.ofFn _ = (textPrefix stream ((base s).length+n)).map evenWord
    rw [hn, textPrefix_eq_ofFn, List.map_ofFn]
    rfl
  simp only [accepts, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, roundList, digits, split]
  refine ⟨⟨(checkRun_spec ..).2 (inputEq.symm ▸ exec), inputEq.trans hinput⟩, ?_⟩
  exact fun h => nonzero (hout.symm.trans h)

end GenLimit.Replay.ProperDiagonal
