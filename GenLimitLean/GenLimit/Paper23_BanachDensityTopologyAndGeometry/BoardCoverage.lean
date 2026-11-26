import GenLimit.Paper23_BanachDensityTopologyAndGeometry.BoardController
import GenLimit.Paper23_BanachDensityTopologyAndGeometry.LocalReplies

/-! Transfer a finite board's guaranteed replies to a generator on the
whole universe, allowing arbitrary visits to other boards between moves. -/
namespace GenLimit.KleinbergWei.Banach.FiniteGame
open Finset Set Real
open scoped Classical
noncomputable section
variable {I V : Type*} [Fintype I] [DecidableEq V] [Inhabited V]

omit [DecidableEq V] [Inhabited V] in
private theorem prefix_split {s : ℕ → V} {t : ℕ} {before after : List V} {x : V}
    (eq : textPrefix s t = before++[x]++after) :
    before = textPrefix s before.length ∧ x=s before.length := by
  have lt : before.length < t := by have := congrArg List.length eq; simp at this; omega
  have first := congrArg (List.take before.length) eq
  have part : (textPrefix s t).take before.length = textPrefix s before.length := by
    simp [textPrefix,←List.map_take,List.take_range,Nat.min_eq_left lt.le]
  rw [part] at first
  have pre : textPrefix s before.length = before := by simpa [List.append_assoc] using first
  have through := congrArg (List.take (before.length+1)) eq
  have part' : (textPrefix s t).take (before.length+1) = textPrefix s (before.length+1) := by
    simp [textPrefix,←List.map_take,List.take_range,Nat.min_eq_left lt]
  rw [part',textPrefix_succ,pre] at through
  have len : before.length+1 = (before++[x]).length := by simp
  rw [len,List.take_left] at through
  exact ⟨pre.symm,by simpa using through.symm⟩

omit [Inhabited V] in
theorem prefix_covers {s : ℕ → V} {D : Finset V} (covered : ∀ x ∈ D, x ∈ range s) :
    ∃ t, D ⊆ (textPrefix s t).toFinset := by
  let first (x : V) := if h : x ∈ range s then Nat.find h else 0
  refine ⟨D.sup first+1,fun x mem => List.mem_toFinset.mpr (mem_textPrefix_iff.mpr ?_)⟩
  have h := covered x mem
  exact ⟨first x,Nat.lt_succ_of_le (Finset.le_sup (f:=first) mem),by dsimp only [first]; rw [dif_pos h]; exact Nat.find_spec h⟩

/-- Local count in the actual output set. Only routing of nonempty
recommendations is required on a board covered by the real stream. -/
theorem realized_bound (E : I → Finset V) (w : I → ℝ) (wp : ∀ i, 0 < w i)
    {q : ℝ} (hq : 0 < q) (h1 : q ≤ 1/2) (D : Finset V) (s : ℕ → V)
    (covered : ∀ x ∈ D, x ∈ range s)
    (plan : List V → V → Option V) (backup : List V → Set V) (inf : ∀ h, (backup h).Infinite)
    (routes : ∀ t y, recommend E w q (run E w q D (textPrefix s t)) (s t) = some y →
      plan (textPrefix s t) (s t) = some y) (i : I) :
    (1/2-q)*((D ∩ E i).card:ℝ) - log ((1+q)*(∑ j, w j)/w i)/(2*q) ≤
      ((D ∩ E i).filter (· ∈ range (LocalReplies.play plan backup inf s))).card := by
  obtain ⟨t,cover⟩ := prefix_covers covered
  have bound := covering_bound E w q wp hq h1 (textPrefix s t) cover i
  let p := run E w q D (textPrefix s t)
  have sub : p.outputs.toFinset ∩ E i ⊆
      (D ∩ E i).filter (· ∈ range (LocalReplies.play plan backup inf s)) := by
    intro y hy
    obtain ⟨inP,inE⟩ := Finset.mem_inter.mp hy
    obtain ⟨before,x,after,split,rec⟩ := output_source E w q (List.mem_toFinset.mp inP)
    obtain ⟨pre,atX⟩ := prefix_split split
    have fresh := recommendation_fresh E w q rec
    have localHit : recommend E w q (run E w q D (textPrefix s before.length)) (s before.length) = some y := by
      rwa [←pre,←atX]
    exact Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨fresh.1,inE⟩,
      LocalReplies.credited plan backup inf (routes _ _ localHit)
        (by rw [textPrefix_succ,←pre,←atX]; simp [fresh.2.1,fresh.2.2])⟩
  exact bound.trans (by exact_mod_cast Finset.card_le_card sub)

end
end GenLimit.KleinbergWei.Banach.FiniteGame
