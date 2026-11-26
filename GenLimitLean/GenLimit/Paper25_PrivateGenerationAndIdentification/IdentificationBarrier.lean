import GenLimit.Paper25_PrivateGenerationAndIdentification.PairedTexts
import GenLimit.Support.DifferentialPrivacy
import GenLimit.Support.HistoryChainText

/-! The private online identification barrier of Mehrotra, Velegkas, Yu,
and Zhou (Theorem 1.5). Each diagonal stage uses a full comparison text
which differs in finitely many places from a partial target text. Pure
privacy transfers almost-sure stabilization between them. Causality fixes
a late marginal with the wrong majority before the next stage. -/

namespace GenLimit.PrivateLimit

open Set MeasureTheory Privacy
open scoped ENNReal Classical

/-- Identification stabilizes at a single correct index almost surely, on
every duplicate-free adversarial enumeration. -/
def IdentifiesOnline (M : ContinualRelease ℕ ℕ) (C : LanguageFamily) : Prop :=
  ∀ z s, Function.Injective s → range s = C z →
    ∀ᵐ y ∂M.law s, ∃ j, C j = C z ∧ ∃ T, ∀ t ≥ T, y t = j

private def outputEvent (C : LanguageFamily) (K : Set ℕ) (t : ℕ) :=
  {y : ℕ → ℕ | C (y t) = K}

private theorem output_measurable (C : LanguageFamily) (K : Set ℕ) (t : ℕ) :
    MeasurableSet (outputEvent C K t) := by
  change MeasurableSet ((fun y : ℕ → ℕ => y t) ⁻¹' {j | C j = K})
  exact (measurable_pi_apply t) (Set.to_countable _).measurableSet

private theorem eventually_correct {M C} (h : IdentifiesOnline M C) {s z}
    (hi : Function.Injective s) (hp : range s = C z) :
    ∀ᵐ y ∂M.law s, ∃ T, ∀ t ≥ T, y t ∈ {j | C j = C z} := by
  filter_upwards [h z s hi hp] with y hy
  obtain ⟨j,hj,T,hT⟩ := hy
  exact ⟨T,fun t h => (congrArg C (hT t h)).trans hj⟩

private def MajorityAtPrefix (M : ContinualRelease ℕ ℕ) (C : LanguageFamily)
    (K : Set ℕ) (xs : List ℕ) : Prop :=
  ∀ s, textPrefix s xs.length = xs →
    1/2 < (M.law s).real (outputEvent C K (xs.length-1))

private theorem extend_stage {M : ContinualRelease ℕ ℕ} {C : LanguageFamily} {ε : ℝ}
    (dp : DifferentiallyPrivate ε 0 M.law) (ok : IdentifiesOnline M C)
    {i j} (inf : (C i).Infinite) (p : PairedText (C i) (C j)) (n : ℕ) :
    ∃ q : PairedText (C i) (C j), p.right <+: q.right ∧ n < q.right.length ∧
      (n ∈ C j → n ∈ q.right) ∧ MajorityAtPrefix M C (C i) q.right := by
  obtain ⟨b,hprefix,hcontains⟩ := p.add_requested inf n
  obtain ⟨inj,rangeEq⟩ := b.left_enumerates inf
  have hb : MeasurableSet {z | C z = C i} := (Set.to_countable _).measurableSet
  have right := M.transfer_eventually dp (Finset.range b.right.length)
    (fun k hk => b.common_after k (Nat.le_of_not_gt (fun h => hk (Finset.mem_range.mpr h))))
    hb (eventually_correct ok inj rangeEq)
  obtain ⟨T,hT⟩ := M.eventual_majority b.rightStream hb right
  let t := max n (max T b.right.length)
  have hn : n ≤ t := le_max_left ..
  have ht : T ≤ t := (le_max_left ..).trans (le_max_right ..)
  have hl : b.right.length ≤ t := (le_max_right ..).trans (le_max_right ..)
  let m := t+1-b.right.length
  have hm : b.right.length+m = t+1 := by dsimp [m]; omega
  obtain ⟨q,hq⟩ := b.commit inf m
  have len : q.right.length = t+1 := by rw [hq,List.length_append,textPrefix_length,hm]
  have he : textPrefix b.rightStream (t+1) = q.right := by
    rw [← hm, PairedText.rightStream,Support.textPrefix_prependStream,hq]
  have prefixB : b.right <+: q.right := hq ▸ List.prefix_append ..
  refine ⟨q,hprefix.trans prefixB,by omega,fun h => prefixB.subset (hcontains h),?_⟩
  intro s hs
  rw [len] at hs ⊢
  have agree (k) (hk : k ≤ t) : s k = b.rightStream k := by
    have eq := congrArg (fun xs : List ℕ => xs[k]?) (hs.trans he.symm)
    have hkr : k < (List.range (t+1)).length := by simpa using Nat.lt_succ_of_le hk
    simpa [textPrefix,List.getElem?_map,List.getElem?_eq_getElem hkr] using eq
  have eq := congrArg ENNReal.toReal (M.marginal_congr t agree hb)
  change (M.law s).real (outputEvent C (C i) t) = (M.law b.rightStream).real (outputEvent C (C i) t) at eq
  simpa [eq] using hT t ht

private theorem oriented_barrier {M : ContinualRelease ℕ ℕ} {C : LanguageFamily} {ε : ℝ}
    (dp : DifferentiallyPrivate ε 0 M.law) (ok : IdentifiesOnline M C)
    {i j} (inf : (C i).Infinite) (dist : C i ≠ C j) (init : PairedText (C i) (C j)) : False := by
  classical
  let next := fun n (p : PairedText (C i) (C j)) => (extend_stage dp ok inf p n).choose
  let P : ℕ → PairedText (C i) (C j) := Nat.rec init next
  have advance (n) := (extend_stage dp ok inf (P n) n).choose_spec
  change ∀ n, (P n).right <+: (P (n+1)).right ∧ n < (P (n+1)).right.length ∧
      (n ∈ C j → n ∈ (P (n+1)).right) ∧ MajorityAtPrefix M C (C i) (P (n+1)).right at advance
  let H : Support.HistoryChain ℕ := {
    history := fun n => (P n).right
    prefix_succ := fun n => (advance n).1
    le_length := fun n => by cases n with
      | zero => exact Nat.zero_le _
      | succ n => exact (advance n).2.1 }
  have rangeH : range H.stream = C j := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      have bound : t < (H.history (t+1)).length := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) (H.le_length _)
      rw [H.stream_eq_get (t+1) t bound]
      exact (P (t+1)).right_mem _ (List.get_mem _ _)
    · intro hx
      exact H.history_toFinset_subset_stream_range (x+1) (List.mem_toFinset.mpr ((advance x).2.2.1 hx))
  have injH : Function.Injective H.stream := by
    intro a b eq
    let k := max a b + 1
    have la : a < (H.history k).length := (Nat.lt_succ_of_le (le_max_left ..)).trans_le (H.le_length k)
    have lb : b < (H.history k).length := (Nat.lt_succ_of_le (le_max_right ..)).trans_le (H.le_length k)
    rw [H.stream_eq_get k a la, H.stream_eq_get k b lb] at eq
    exact congrArg Fin.val (List.nodup_iff_injective_get.mp (P k).right_nodup eq)
  obtain ⟨n,good⟩ := M.eventual_majority H.stream (Set.to_countable {z | C z = C j}).measurableSet
    (eventually_correct ok injH rangeH)
  let t := (P (n+1)).right.length-1
  have hn : n ≤ t := by have := (advance n).2.1; dsimp [t]; omega
  have wrong := (advance n).2.2.2 H.stream (H.textPrefix_stream (n+1))
  change 1/2 < (M.law H.stream).real (outputEvent C (C i) t) at wrong
  have right := good t hn
  change 1/2 < (M.law H.stream).real (outputEvent C (C j) t) at right
  letI := M.probability H.stream
  have dis : Disjoint (outputEvent C (C i) t) (outputEvent C (C j) t) :=
    Set.disjoint_left.mpr (fun _ h1 h2 => dist (h1.symm.trans h2))
  have sum := measureReal_mono (μ := M.law H.stream)
    (Set.subset_univ ((outputEvent C (C i) t) ∪ (outputEvent C (C j) t)))
  rw [measureReal_union dis (output_measurable ..),measureReal_univ_eq_one] at sum
  linarith

/-- Even one finite one-sided difference forbids private identification when
the distinct targets have infinite overlap. The orientation of the two
languages is chosen so the fixed prefix has enough replacement positions. -/
theorem identification_barrier {C : LanguageFamily} {i j : ℕ}
    (dist : C i ≠ C j) (inter : (C i ∩ C j).Infinite) (diff : (C i \ C j).Finite)
    {ε : ℝ} (M : ContinualRelease ℕ ℕ) (dp : DifferentiallyPrivate ε 0 M.law) :
    ¬IdentifiesOnline M C := by
  intro ok
  rcases PairedText.orient diff with init | init
  · exact oriented_barrier dp ok (inter.mono inter_subset_left) dist (Classical.choice init)
  · exact oriented_barrier dp ok (inter.mono inter_subset_right) dist.symm (Classical.choice init)

end GenLimit.PrivateLimit
