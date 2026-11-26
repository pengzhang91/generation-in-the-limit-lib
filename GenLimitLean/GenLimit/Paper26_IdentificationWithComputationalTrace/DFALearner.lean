import GenLimit.Paper26_IdentificationWithComputationalTrace.DFA
import GenLimit.Paper26_IdentificationWithComputationalTrace.VersionSpace
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Fintype.Prod

namespace GenLimit.ComputationalTrace
open List

private def trim (M : BinaryDFA ℕ) (qs : List ℕ) : BinaryDFA (Option (Fin qs.length)) :=
  ⟨locateState qs M.initial, fun i a => i.bind fun j => locateState qs (M.step (qs.get j) a),
    fun i => i.any fun j => M.final (qs.get j)⟩

private theorem trim_sink (M : BinaryDFA ℕ) (qs : List ℕ) (w : List Bool) :
    (trim M qs).run none w = none := by
  induction w with
  | nil => rfl
  | cons a xs ih => exact ih

private theorem trim_accept (M : BinaryDFA ℕ) (qs : List ℕ) (q : ℕ) (w : List Bool) :
    (trim M qs).final ((trim M qs).run (locateState qs q) w) = true ↔
      M.final (M.run q w) = true ∧ ∀ r ∈ M.trace q w, r ∈ qs := by
  induction w generalizing q with
  | nil =>
    by_cases h : q ∈ qs <;> simp [BinaryDFA.run, BinaryDFA.trace, trim, locateState,h,
      List.get_eq_getElem, List.getElem_idxOf]
  | cons a w ih =>
    by_cases h : q ∈ qs
    · change (trim M qs).final ((trim M qs).run ((trim M qs).step (locateState qs q) a) w) = true ↔ _
      have hstep : (trim M qs).step (locateState qs q) a = locateState qs (M.step q a) := by
        simp [trim,locateState,h,List.get_eq_getElem,List.getElem_idxOf]
      rw [hstep,ih]
      simp [BinaryDFA.trace, BinaryDFA.run, h]
    · have hstep : (trim M qs).step (locateState qs q) a = none := by simp [locateState,h,trim]
      change (trim M qs).final ((trim M qs).run ((trim M qs).step (locateState qs q) a) w) = true ↔ _
      rw [hstep,trim_sink]
      simp [trim,BinaryDFA.trace,h]

abbrev DFACode (k : ℕ) :=
  let σ := Option (Fin k)
  σ × (σ → Bool → σ) × (σ → Bool)

def decodeDFA {k : ℕ} (c : DFACode k) : BinaryDFA (Option (Fin k)) :=
  ⟨c.1,c.2.1,c.2.2⟩

private theorem small_code {M : BinaryDFA ℕ} {rate : ℝ} {cutoff d : ℕ}
    {s : ℕ → DFAExample} (hs : DFAPresentation M rate cutoff s)
    (hd : 1 ≤ (d : ℝ) * (1 - rate)) (S : Finset ℕ)
    (ho : ∀ n q, q ∈ (s n).2 → q ∈ S) :
    ∃ c : DFACode (wordsUpTo (cutoff + d * (2 * S.card))).length,
      (decodeDFA c).language = M.language := by
  let words := wordsUpTo (cutoff + d * (2 * S.card))
  let qs := words.map (M.run M.initial)
  let A := trim M qs
  have eq : A.language = M.language := by
    ext w
    change (trim M qs).final ((trim M qs).run (locateState qs M.initial) w) = true ↔ _
    rw [trim_accept]
    refine and_iff_left_of_imp ?_
    intro hw q hq
    obtain ⟨u,v,h,hu,_⟩ := M.visit hq
    obtain ⟨p,hp,hl⟩ := short_dfa_access hs hd S ho (h ▸ hw : u ++ v ∈ M.language)
    exact List.mem_map.mpr ⟨p,(mem_wordsUpTo _ _).mpr hl,hp.trans hu⟩
  have witness : ∃ c : DFACode qs.length, (decodeDFA c).language = M.language :=
    ⟨⟨A.initial,A.step,A.final⟩,eq⟩
  let existsCode (k : ℕ) := ∃ c : DFACode k, (decodeDFA c).language = M.language
  exact Eq.mp (congrArg existsCode (List.length_map (f := M.run M.initial) (as := words))) witness

/-- The output is the product DFA over the surviving tables. This implements
finite-class identification without an inclusion test or a tie-breaking oracle. -/
structure DFAHypothesis where
  size : ℕ
  tables : Finset (DFACode size)

def DFAHypothesis.product (H : DFAHypothesis) : BinaryDFA (H.tables → Option (Fin H.size)) :=
  ⟨fun c => c.val.1, fun qs a c => c.val.2.1 (qs c) a,
    fun qs => decide (∀ c : H.tables, c.val.2.2 (qs c) = true)⟩

private theorem product_run (H : DFAHypothesis) (qs) (w : List Bool) (c : H.tables) :
    (H.product.run qs w) c = (decodeDFA c.val).run (qs c) w := by
  induction w generalizing qs with
  | nil => rfl
  | cons a xs ih => exact ih (H.product.step qs a)

theorem DFAHypothesis.mem_product (H : DFAHypothesis) (w : List Bool) :
    w ∈ H.product.language ↔ ∀ c ∈ H.tables, w ∈ (decodeDFA c).language := by
  change decide _ = true ↔ _
  rw [decide_eq_true_eq]
  simp only [product_run]
  exact Subtype.forall

private def dfaAllows {k : ℕ} (c : DFACode k) (e : DFAExample) : Bool :=
  (decodeDFA c).final ((decodeDFA c).run (decodeDFA c).initial e.1)

private def fromSize (k : ℕ) (xs : List DFAExample) : DFAHypothesis :=
  ⟨k, versionSpace Finset.univ (@dfaAllows k) xs⟩

def dfaLearner (cutoff d : ℕ) (xs : List DFAExample) : DFAHypothesis :=
  fromSize (wordsUpTo (cutoff + d * (2 * (observed Prod.snd xs).card))).length xs

theorem identifies_dfa (rate : ℝ) (hr : rate < 1) (cutoff : ℕ) :
    ∃ d : ℕ, ∀ (M : BinaryDFA ℕ) (s : ℕ → DFAExample),
      DFAPresentation M rate cutoff s →
      ∃ H : DFAHypothesis, H.product.language = M.language ∧
        ∃ T, ∀ t ≥ T, dfaLearner cutoff d (textPrefix s t) = H := by
  have hr' : 0 < 1 - rate := sub_pos.mpr hr
  obtain ⟨d,hd⟩ := exists_nat_ge (1 / (1 - rate))
  have hd' := (div_le_iff₀ hr').mp hd
  refine ⟨d, fun M s hs => ?_⟩
  obtain ⟨Q,_,_,hQ⟩ := hs.finiteStates
  obtain ⟨S,hS,T₀,hT₀⟩ := finite_observations_stabilize _ Q hQ
  have hobs : ∀ t ≥ T₀, observed Prod.snd (textPrefix s t) = S :=
    fun t ht => (observed_prefix _ _ _).trans (hT₀ t ht)
  let k := (wordsUpTo (cutoff + d * (2 * S.card))).length
  obtain ⟨c,hc⟩ := small_code hs hd' S (fun n q h => (hS q).mpr ⟨n,List.mem_toFinset.mpr h⟩)
  obtain ⟨V,hV,T₁,hT₁⟩ := versionSpace_stabilizes Finset.univ (@dfaAllows k) s
  let H : DFAHypothesis := ⟨k,V⟩
  refine ⟨H, ?_, max T₀ T₁, fun t ht => ?_⟩
  · ext x
    rw [DFAHypothesis.mem_product]
    have cov (n : ℕ) : (s n).1 ∈ M.language := hs.covers ▸ ⟨n,rfl⟩
    constructor
    · intro h
      have hm : c ∈ V := (hV c).mpr ⟨Finset.mem_univ _, fun n =>
        (show (s n).1 ∈ (decodeDFA c).language from hc.symm ▸ cov n)⟩
      exact hc ▸ h c hm
    · intro hx a ha
      obtain ⟨n,rfl⟩ := hs.covers.symm ▸ hx
      exact ((hV a).mp ha).2 n
  · unfold dfaLearner
    rw [hobs t (le_trans (le_max_left T₀ T₁) ht)]
    exact congrArg (DFAHypothesis.mk k) (hT₁ t (le_trans (le_max_right ..) ht))

end GenLimit.ComputationalTrace
