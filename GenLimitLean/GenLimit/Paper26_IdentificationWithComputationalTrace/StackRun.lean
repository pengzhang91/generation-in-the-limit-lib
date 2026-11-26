import GenLimit.Paper26_IdentificationWithComputationalTrace.StackCompression

namespace GenLimit.ComputationalTrace.PDA
open Control

def beforeStates (as : List Label) := as.map fun a => a.start.state
def afterStates (as : List Label) := as.map fun a => a.next.state

theorem parse_input {P : Program ℕ} {w ds} (h : Finish device P.machine (P.initial,device.load w) ds)
    (L : ℕ) : ∃ t z, Parse P t ⟨P.initial,w.head?⟩ false z ∧ z.look = none ∧
      letters t.items = w ∧ beforeStates t.items ++ [z.state] = P.initial :: ds.map Prod.fst ∧
      (t.items.filter Label.selected).length = min L w.length := by
  obtain ⟨z,fs,hz,hp,hw,hs,ht⟩ := parse_finish h L
  change Forest P fs ⟨P.initial,w.head?⟩ [false] z at hp
  cases hp with
  | cons one rest =>
    cases rest
    exact ⟨_,_,one,hz,by simpa [tokens] using hw,by simpa [tokens,beforeStates] using hs,
      by simpa [tokens] using ht⟩

theorem run_input {P : Program ℕ} {t p z} (h : Parse P t p false z)
    (hz : z.look = none) (hi : p.state = P.initial) :
    ∃ ds, Finish device P.machine (P.initial,device.load (letters t.items)) ds ∧
      ds.length = t.size ∧ beforeStates t.items ++ [z.state] = P.initial :: ds.map Prod.fst ∧
      afterStates t.items = ds.map Prod.fst := by
  obtain ⟨_,cs,hcs,hp⟩ := h.execute [] [] hz.symm
  simp only [List.append_nil,hi] at hp
  obtain ⟨ds,he,hf⟩ := hp.finish (ds := []) (.halt (by simp))
  refine ⟨ds,hf,?_,?_,?_⟩
  · have hc := congrArg List.length hcs
    have hh := congrArg List.length he
    simp only [List.length_map,List.length_cons,List.length_append,List.length_nil] at hc hh
    change ds.length = t.items.length
    omega
  · have hh := congrArg (List.map Prod.fst) he
    simpa [beforeStates,hcs] using hh.symm
  · have hh := congrArg (List.map Prod.fst) he
    have hc := congrArg (List.map Vertex.state) h.chain
    simp only [List.map_cons,List.map_append,List.map_nil,List.map_map, Function.comp_def,hi] at hc hh
    rw [hcs] at hh
    exact List.cons.inj (hc.symm.trans hh.symm) |>.2

theorem Parse.allLegal {P : Program ℕ} {t p b z} (h : Parse P t p b z) :
    ∀ a ∈ t.items, a.Legal P := by
  induction h <;> simp_all [Tree.items]
  grind

theorem selected_le_input {P : Program ℕ} {t p b z} (pt : Parse P t p b z) :
    (t.items.filter Label.selected).length ≤ (letters t.items).length := by
  have h := pt.allLegal
  generalize t.items = xs at h ⊢
  induction xs with
  | nil => simp [letters]
  | cons a xs ih =>
    have hl := h a (by simp)
    specialize ih (fun x hx => h x (by simp [hx]))
    cases hs : a.selected
    · simp [letters,hs] at ih ⊢; omega
    · have hc := hl.2.2 hs
      have ha : a.start.look.isSome = true := by simpa [hc] using hl.2.1
      cases he : a.start.look <;> simp_all [letters,Label.word]

theorem selected_of_protected {S : Finset ℕ} (xs : List Label) :
    (xs.filter (protect S)).filter Label.selected = xs.filter Label.selected := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases hs : a.selected <;> cases hm : protect S a <;> simp_all [protect]

def hidden (S : Finset ℕ) (xs : List ℕ) := (xs.filter (fun x => decide (x ∉ S))).length

theorem marked_count (S : Finset ℕ) (xs : List Label) :
    (xs.filter (protect S)).length ≤ (xs.filter Label.selected).length +
      hidden S (beforeStates xs) + hidden S (afterStates xs) := by
  induction xs with
  | nil => simp [beforeStates,afterStates,hidden]
  | cons a xs ih =>
    cases hs : a.selected <;> by_cases hp : a.start.state ∈ S <;> by_cases hq : a.next.state ∈ S <;>
      simp [protect,hidden,beforeStates,afterStates,hs,hp,hq] at ih ⊢ <;> omega

end GenLimit.ComputationalTrace.PDA
