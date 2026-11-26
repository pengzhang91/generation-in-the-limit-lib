import GenLimit.Paper23_BanachDensityTopologyAndGeometry.PairedRound
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.RectangleInterpolation
import Mathlib.Data.ENNReal.Inv

/-! The rectangular lower Banach density of Definition 1.1 and Theorem 2.4.
For every size threshold the adversary completes a fresh pair of translated
point sets. Coloring a point by whether its first copy was generated selects
a rectangle missed in one of the two copies. All its words are already in
the input, so the rectangle remains missed along every later locked prefix. -/
namespace GenLimit.KleinbergWei.Banach.Rectangles
open Adversary Stages Set
open scoped Classical ENNReal
noncomputable section

/-- The supremum over thresholds of the infimum of all rectangular
fractions having at least that many target words (Definition 1.1). -/
def lowerDensity {d : ℕ} (O K : Set (Lattice d)) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨅ r : {r : Lattice d × Lattice d // n ≤ (box K r.1 r.2).card},
    ((box (O ∩ K) r.val.1 r.val.2).card : ℝ≥0∞) / (box K r.val.1 r.val.2).card

private def Missed {d : ℕ} (A : List (Lattice (d+2)) → Lattice (d+2)) (n : ℕ)
    (p : List (Lattice (d+2))) : Prop :=
  ∃ l u, n ≤ (box (language d) l u).card ∧ ∀ x ∈ box (language d) l u, x ∈ p ∧ x ∉ past A p

private theorem round {d : ℕ} (A : List (Lattice (d+2)) → Lattice (d+2))
    (n : ℕ) (p : List (Lattice (d+2))) (hp : Legal (language d) p)
    (locked : ∀ q, p <+: q → Legal (language d) q → A q ∉ q) :
    ∃ q, p <+: q ∧ Legal (language d) q ∧ Missed A n q := by
  obtain ⟨j,large,unused⟩ := outside (past A p) n
  obtain ⟨q,ext,legal,seen,single⟩ := paired_round A _ p hp locked (put d j) (contains d j) unused
  let color (v : Point) := decide (place d j false v ∈ past A q)
  obtain ⟨lo,hi,c,size,mono⟩ := force j color
  obtain ⟨l,u,iso⟩ := isolate d j c lo hi
  refine ⟨q,ext,legal,l,u,?_,?_⟩
  · rw [iso,image_card]; omega
  · intro x hx
    rw [iso] at hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    let i : sample j := ⟨v,(mem_trace.mp hv).1⟩
    refine ⟨seen (c,i),?_⟩
    have h := mono v hv
    cases c
    · simpa [color] using h
    · exact single i (by simpa [color,i,put] using h)

private theorem zero_of_holes {d} {O K : Set (Lattice d)}
    (holes : ∀ n, ∃ l u, n ≤ (box K l u).card ∧ ∀ x ∈ box K l u, x ∉ O) :
    lowerDensity O K = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro n
  obtain ⟨l,u,cap,none⟩ := holes n
  have empt : box (O ∩ K) l u = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr; intro x hx
    obtain ⟨bounds,hO,hK⟩ := mem_box.mp hx
    exact none x (mem_box.mpr ⟨bounds,hK⟩) hO
  exact (iInf_le _ (⟨(l,u),cap⟩ : {r : Lattice d × Lattice d // n ≤ (box K r.1 r.2).card})).trans
    (by simp [empt])

/-- A known singleton target in every dimension ≥ 2 with a bad exact
injective presentation for each generator eventually fresh on that target. -/
private theorem empty_rectangles (d : ℕ) (A : List (Lattice (d+2)) → Lattice (d+2))
    (valid : ∀ s : ℕ → Lattice (d+2), range s = language d → Function.Injective s →
      ∃ T, ∀ t ≥ T, A (textPrefix s t) ∉ textPrefix s t) :
    ∃ s : ℕ → Lattice (d+2), range s = language d ∧ Function.Injective s ∧
      ∀ n, ∃ l u, n ≤ (box (language d) l u).card ∧
        ∀ x ∈ box (language d) l u, x ∉ range (cubePlay A s) := by
  obtain ⟨p,_,hp,locked⟩ := lock _ (infinite d) (fun q => A q ∉ q) valid [] (by simp [Legal])
  obtain ⟨H,initial,allK,inj,missed⟩ := fair_chain _ (infinite d) p hp (Missed A) (fun n q eq hq =>
    round A n q hq (fun r ext => locked r (eq.trans ext)))
  refine ⟨H.stream,allK,inj,?_⟩
  intro n
  let q := H.history (n+1)
  obtain ⟨l,u,size,none⟩ := missed n
  refine ⟨l,u,size,?_⟩
  intro x hx
  obtain ⟨seen,miss⟩ := none x hx
  rintro ⟨i,rfl⟩
  have at_end : textPrefix H.stream q.length = q := H.textPrefix_stream _
  by_cases early : i+1 < q.length
  · apply miss
    apply mem_past.mpr
    refine ⟨i+1,early,?_⟩
    have eq := List.prefix_iff_eq_take.mp (textPrefix_prefix H.stream early.le)
    rw [textPrefix_length,at_end] at eq
    exact congrArg A eq.symm
  · have pre : q <+: textPrefix H.stream (i+1) :=
      at_end ▸ textPrefix_prefix H.stream (by omega : q.length ≤ i+1)
    have start : p <+: q := initial ▸ H.prefix_of_le (Nat.zero_le _)
    have legal : Legal (language d) (textPrefix H.stream (i+1)) := by
      refine ⟨List.nodup_range.map inj,?_⟩
      intro v hv
      obtain ⟨t,_,rfl⟩ := mem_textPrefix_iff.mp hv
      exact allK ▸ mem_range_self t
    exact locked _ (start.trans pre) legal (pre.subset seen)

/-- One presentation witnesses both the overview and detailed limits. -/
theorem obstruction (d : ℕ) (A : List (Lattice (d+2)) → Lattice (d+2))
    (valid : ∀ s : ℕ → Lattice (d+2), range s = language d → Function.Injective s →
      ∃ T, ∀ t ≥ T, A (textPrefix s t) ∈ language d ∧ A (textPrefix s t) ∉ textPrefix s t) :
    ∃ s : ℕ → Lattice (d+2), range s = language d ∧ Function.Injective s ∧
      lowerDensity (range (cubePlay A s)) (language d) = 0 ∧
      outputThresholdDensity (range (cubePlay A s)) (language d) = 0 := by
  have fresh (s : ℕ → Lattice (d+2)) (all : range s = language d) (inj : Function.Injective s) :
      ∃ T, ∀ t ≥ T, A (textPrefix s t) ∉ textPrefix s t := by
    obtain ⟨T,hT⟩ := valid s all inj
    exact ⟨T,fun t ht => (hT t ht).2⟩
  obtain ⟨s,all,inj,holes⟩ := empty_rectangles d A fresh
  obtain ⟨T,ok⟩ := valid s all inj
  have inf : (range (cubePlay A s) ∩ language d).Infinite := by
    intro finite
    obtain ⟨N,seen⟩ := Support.finite_eventually_subset_sample (show Generic.Presents s _ from all)
      finite.toFinset (by simp)
    let t := max N T
    have late : T ≤ t+1 := (le_max_right ..).trans (Nat.le_succ t)
    obtain ⟨inK,freshWord⟩ := ok (t+1) late
    have generated : cubePlay A s t ∈ finite.toFinset := finite.mem_toFinset.mpr ⟨mem_range_self _,inK⟩
    have inSample := seen (t+1) ((le_max_left ..).trans (Nat.le_succ t)) generated
    exact freshWord (mem_textPrefix_iff.mpr (Generic.mem_sample_iff.mp inSample))
  exact ⟨s,all,inj,zero_of_holes holes,interpolate _ _ inf thin holes⟩

end
end GenLimit.KleinbergWei.Banach.Rectangles
