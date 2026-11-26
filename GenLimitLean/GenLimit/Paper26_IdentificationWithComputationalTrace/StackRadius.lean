import GenLimit.Paper26_IdentificationWithComputationalTrace.StackRun
import GenLimit.Paper26_IdentificationWithComputationalTrace.ControlBound
import Mathlib.Tactic.Positivity

namespace GenLimit.ComputationalTrace.PDA
open Control List

def factor (S : Finset ℕ) := Tree.treeFactor (palette S).card

def rateIndex (S : Finset ℕ) := 4 * factor S + 2

def radius (S : Finset ℕ) (minLength : ℕ) := 2 * factor S * (minLength + 1) + 1

private theorem integral_rate {α : Type} {k d : ℕ} {xs : List α}
    (h : (k : ℝ) ≤ (1 / ((d : ℝ)+2)) * xs.length) : k*(d+2) ≤ xs.length := by
  rw [one_div_mul_eq_div] at h
  have he := (le_div_iff₀ (by positivity)).mp h
  exact_mod_cast he

private theorem sample_error {P : Program ℕ} {s : ℕ → Sample Memory} {cut : ℕ → ℕ}
    (hs : Presentation device P.machine (DiminishingBound cut) s) (S : Finset ℕ)
    (ho : ∀ n e, e ∈ (s n).2 → e.1 ∈ S) (n d : ℕ) (hl : cut d ≤ (s n).1.length)
    {ds} (hf : Finish device P.machine (P.initial,device.load (s n).1) ds) :
    ∃ k, k*(d+2) ≤ ds.length+1 ∧ hidden S (P.initial :: ds.map Prod.fst) ≤ k ∧
      ds.length + 1 ≤ (s n).2.length + k := by
  obtain ⟨ds',hp,he⟩ := hs.traces n
  obtain rfl := hf.unique _ _ hp
  obtain ⟨k,ed,hk⟩ := he d hl
  refine ⟨k,integral_rate hk,?_,ed.length_bounds.1⟩
  have hh := ed.hidden_le (fun c => decide (c.1 ∈ S)) (by simpa using ho n)
  change hidden S (((P.initial,device.load (s n).1) :: ds).map Prod.fst) ≤ k
  unfold hidden
  rw [List.filter_map]
  simpa [Function.comp_def] using hh

theorem time_bound {P : Program ℕ} {s : ℕ → Sample Memory} {cut : ℕ → ℕ}
    (hs : Presentation device P.machine (DiminishingBound cut) s) (S : Finset ℕ)
    (ho : ∀ n e, e ∈ (s n).2 → e.1 ∈ S) (n d : ℕ) (hl : cut d ≤ (s n).1.length)
    {ds} (hf : Finish device P.machine (P.initial,device.load (s n).1) ds) :
    ds.length ≤ 2*(s n).2.length := by
  obtain ⟨k,hk,_,hlen⟩ := sample_error hs S ho n d hl hf
  have hh := Nat.mul_le_mul_left k (show 2 ≤ d+2 by omega)
  omega

private theorem hidden_sub {S : Finset ℕ} {xs ys : List ℕ} (h : xs <+ ys) :
    hidden S xs ≤ hidden S ys := (h.filter _).length_le

/-- Every control state on any long accepting run is in a computably bounded
neighborhood. The shorter accepting run preserves every hidden transition
and enough consumed input symbols to invoke the same known rate bound. -/
theorem cover_diminishing {P : Program ℕ} {s : ℕ → Sample Memory} {cut : ℕ → ℕ}
    (hs : Presentation device P.machine (DiminishingBound cut) s) (S : Finset ℕ)
    (ho : ∀ n e, e ∈ (s n).2 → e.1 ∈ S) {w ds}
    (hl : cut (rateIndex S) ≤ w.length) (hf : Finish device P.machine (P.initial,device.load w) ds) :
    ∀ e ∈ (P.initial,device.load w) :: ds, e.1 ∈ ball P.machine
      (Finset.univ : Finset Observation).toList (P.initial :: S.toList) (radius S (cut (rateIndex S))) := by
  let L := cut (rateIndex S)
  obtain ⟨t,z,pt,hz,_,hs₁,hn⟩ := parse_input hf L
  obtain ⟨u,pu,preserved,cost⟩ := compress pt S
  obtain ⟨rs,run,steps,hs₂,ha₂⟩ := run_input pu hz rfl
  have selected : (u.items.filter Label.selected).length = L := by
    have he := congrArg (List.filter Label.selected) preserved
    rw [selected_of_protected,selected_of_protected] at he
    rw [he,hn,min_eq_left hl]
  have long : L ≤ (letters u.items).length := selected ▸ selected_le_input pu
  have accepted : letters u.items ∈ language device P.machine := ⟨rs,run⟩
  obtain ⟨n,eq⟩ := hs.covers.symm ▸ accepted
  change (s n).1 = letters u.items at eq
  obtain ⟨k,hk,hh,_⟩ := sample_error hs S ho n (rateIndex S) (eq.symm ▸ long) (eq.symm ▸ run)
  have hb : beforeStates u.items <+ P.initial :: rs.map Prod.fst := hs₂ ▸ List.sublist_append_left ..
  have ha : afterStates u.items <+ P.initial :: rs.map Prod.fst := ha₂ ▸ (List.Sublist.refl _).cons _
  have cm : u.marks (protect S) ≤ L + 2*k := by
    have est := marked_count S u.items
    rw [selected] at est
    have h₁ := (hidden_sub (S := S) hb).trans hh
    have h₂ := (hidden_sub (S := S) ha).trans hh
    exact le_trans est (by omega)
  have short : rs.length ≤ radius S L := by
    rw [steps] at hk ⊢
    change k*(4*factor S+2+2) ≤ u.size+1 at hk
    change u.size ≤ factor S*(u.marks (protect S)+1) at cost
    have hm := Nat.mul_le_mul_left (factor S) (Nat.add_le_add_right cm 1)
    unfold radius
    nlinarith
  have ball' := cover_short_run (S := S) device P.machine run short
  intro e he
  by_cases hseen : e.1 ∈ S
  · exact seed_ball P.machine S _ hseen
  · have hbefore : e.1 ∈ beforeStates t.items ++ [z.state] := by
      rw [hs₁]
      exact List.mem_map_of_mem (f := Prod.fst) he
    have hafter : e.1 ∈ beforeStates u.items ++ [z.state] := by
      rcases List.mem_append.mp hbefore with ha | heq
      · obtain ⟨a,hmem,hstate⟩ := List.mem_map.mp ha
        have hm : protect S a = true := by simp [protect,hstate,hseen]
        have hprot : a ∈ u.items.filter (protect S) := preserved ▸ List.mem_filter.mpr ⟨hmem,hm⟩
        exact List.mem_append_left _ (List.mem_map.mpr ⟨a,(List.mem_filter.mp hprot).1,hstate⟩)
      · exact List.mem_append_right _ heq
    rw [hs₂] at hafter
    change e.1 ∈ (((P.initial,device.load (letters u.items)) :: rs).map Prod.fst) at hafter
    obtain ⟨e',he',heq⟩ := List.mem_map.mp hafter
    exact heq ▸ ball' e' he'

end GenLimit.ComputationalTrace.PDA
