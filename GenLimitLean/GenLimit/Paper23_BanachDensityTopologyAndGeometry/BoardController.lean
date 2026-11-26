import GenLimit.Paper23_BanachDensityTopologyAndGeometry.FiniteRectangleGame

/-! A finite local game driven by a stream that can repeat words, visit
other boards, or reveal an earlier reply. Only fresh local inputs advance
the game. Its recommended replies all precede their first observation. -/
namespace GenLimit.KleinbergWei.Banach.FiniteGame
open Finset Real
open scoped Classical
noncomputable section
variable {I V : Type*} [Fintype I] [DecidableEq V]

structure Position (V : Type*) where
  inputs : List V
  outputs : List V
  free : Finset V

def initial (board : Finset V) : Position V := ⟨[],[],board⟩

variable (E : I → Finset V) (w : I → ℝ) (q : ℝ)

def recommend (p : Position V) (x : V) : Option V :=
  if x ∈ p.free then
    if h : (p.free.erase x).Nonempty then
      some (reply E (weight E w q (x::p.inputs) p.outputs) (p.free.erase x) h)
    else none
  else none

def step (p : Position V) (x : V) : Position V :=
  if x ∈ p.free then
    match recommend E w q p x with
    | some y => ⟨x::p.inputs, y::p.outputs, (p.free.erase x).erase y⟩
    | none => ⟨x::p.inputs,p.outputs,p.free.erase x⟩
  else p

def run (board : Finset V) (xs : List V) :=
  xs.foldl (step E w q) (initial board)

theorem run_append (board : Finset V) (xs : List V) (x : V) :
    run E w q board (xs++[x]) = step E w q (run E w q board xs) x := by simp [run]

private theorem recommended {p : Position V} {x y : V} (h : recommend E w q p x = some y) :
    y ∈ p.free.erase x := by
  unfold recommend at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h; apply reply_mem

/-- Positions after each local response, including a final input with no
available response. The intermediate input states are the weighted game. -/
private inductive Ready (board : Finset V) : Position V → Prop
  | start : Ready board (initial board)
  | last {a g} (h : AfterInput E w q board a g ∅) : Ready board ⟨a,g,∅⟩
  | answered {a g F} (h : AfterInput E w q board a g F) (hf : F.Nonempty) :
      Ready board ⟨a,reply E (weight E w q a g) F hf::g,F.erase (reply E (weight E w q a g) F hf)⟩

private theorem next_input {board : Finset V} {p : Position V} (pr : Ready E w q board p)
    {x} (hx : x ∈ p.free) :
    AfterInput E w q board (x::p.inputs) p.outputs (p.free.erase x) := by
  cases pr with
  | start => exact .first x hx
  | last _ => exact False.elim ((Finset.notMem_empty x) hx)
  | answered h hf => exact .next h hf x hx

private theorem run_ready (board : Finset V) (xs : List V) : Ready E w q board (run E w q board xs) := by
  induction xs using List.reverseRecOn with
  | nil => exact .start
  | append_singleton l x ih =>
    rw [run_append]
    generalize hp : run E w q board l = p at *
    by_cases hx : x ∈ p.free
    · have after := next_input E w q ih hx
      by_cases h : (p.free.erase x).Nonempty
      · simpa [step,recommend,hx,h] using Ready.answered after h
      · have empty := Finset.not_nonempty_iff_eq_empty.mp h
        rw [empty] at after
        simpa [step,recommend,hx,empty] using Ready.last after
    · simpa [step,hx] using ih

private theorem step_free (p : Position V) (x : V) :
    (step E w q p x).free ⊆ p.free.erase x := by
  by_cases h : x ∈ p.free
  · simp only [step,if_pos h]; split <;> first | exact Finset.erase_subset _ _ | exact Finset.Subset.rfl
  · simp [step,h]

theorem free_subset (board : Finset V) (xs : List V) :
    (run E w q board xs).free ⊆ board \ xs.toFinset := by
  induction xs using List.reverseRecOn with
  | nil => simp [run,initial]
  | append_singleton l x ih =>
    rw [run_append]
    intro y hy
    obtain ⟨ne,old⟩ := mem_erase.mp (step_free E w q _ _ hy)
    obtain ⟨hb,no⟩ := mem_sdiff.mp (ih old)
    exact mem_sdiff.mpr ⟨hb,by simp [ne,no]⟩

theorem active_input {board : Finset V} {xs : List V} {x y : V}
    (h : recommend E w q (run E w q board xs) x = some y) : x ∈ board := by
  by_contra outside
  have absent : x ∉ (run E w q board xs).free := fun hx =>
    outside (Finset.mem_sdiff.mp (free_subset E w q board xs hx)).1
  simp [recommend,absent] at h

theorem recommendation_fresh {board : Finset V} {xs : List V} {x y : V}
    (h : recommend E w q (run E w q board xs) x = some y) :
    y ∈ board ∧ y ∉ xs ∧ y ≠ x := by
  obtain ⟨ne,old⟩ := mem_erase.mp (recommended E w q h)
  obtain ⟨hb,no⟩ := mem_sdiff.mp (free_subset E w q board xs old)
  simpa using And.intro hb (And.intro no ne)

private theorem free_partition (board : Finset V) (xs : List V) :
    let p := run E w q board xs
    p.inputs.Nodup ∧ p.outputs.Nodup ∧ Disjoint p.inputs.toFinset p.outputs.toFinset ∧
      Disjoint p.free (p.inputs.toFinset ∪ p.outputs.toFinset) ∧
      p.free ∪ (p.inputs.toFinset ∪ p.outputs.toFinset) = board := by
  induction xs using List.reverseRecOn with
  | nil => simp [run,initial]
  | append_singleton l x ih =>
    rw [run_append]
    generalize hp : run E w q board l = p at *
    obtain ⟨ha,hg,dis,free,all⟩ := ih
    by_cases hx : x ∈ p.free
    · have nx := Finset.disjoint_left.mp free hx
      simp only [Finset.mem_union,List.mem_toFinset,not_or] at nx
      simp only [step,if_pos hx]
      cases rec : recommend E w q p x with
      | none =>
        simp only [List.nodup_cons,List.toFinset_cons]
        refine ⟨⟨nx.1,ha⟩,hg,?_,?_,?_⟩
        · rw [Finset.disjoint_insert_left]; exact ⟨by simpa using nx.2,dis⟩
        · rw [Finset.disjoint_left]; intro v hv
          obtain ⟨ne,hv⟩ := Finset.mem_erase.mp hv
          simpa [ne] using Finset.disjoint_left.mp free hv
        · rw [←all]; ext v; by_cases e : v=x <;> simp [e,hx]
      | some y =>
        obtain ⟨ne,hy⟩ := Finset.mem_erase.mp (recommended E w q rec)
        have ny := Finset.disjoint_left.mp free hy
        simp only [Finset.mem_union,List.mem_toFinset,not_or] at ny
        simp only [List.nodup_cons,List.toFinset_cons]
        refine ⟨⟨nx.1,ha⟩,⟨ny.2,hg⟩,?_,?_,?_⟩
        · rw [Finset.disjoint_insert_left,Finset.disjoint_insert_right]
          simp [ne.symm,nx.2,ny.1,dis]
        · rw [Finset.disjoint_left]; intro v hv
          obtain ⟨vy,old⟩ := Finset.mem_erase.mp hv
          obtain ⟨vx,old⟩ := Finset.mem_erase.mp old
          simpa [vx,vy] using Finset.disjoint_left.mp free old
        · rw [←all]; ext v
          by_cases ex : v=x <;> by_cases ey : v=y <;> simp [ex,ey,hx,hy]
    · simpa [step,hx] using And.intro ha (And.intro hg (And.intro dis (And.intro free all)))

/-- Every reply stored after a history was recommended at a definite
earlier prefix ending just before its corresponding input. -/
theorem output_source {board : Finset V} {xs : List V} {y : V}
    (hy : y ∈ (run E w q board xs).outputs) :
    ∃ before x after, xs = before ++ [x] ++ after ∧
      recommend E w q (run E w q board before) x = some y := by
  induction xs using List.reverseRecOn with
  | nil => simp [run,initial] at hy
  | append_singleton l x ih =>
    rw [run_append] at hy
    by_cases old : y ∈ (run E w q board l).outputs
    · obtain ⟨a,b,c,eq,hit⟩ := ih old
      exact ⟨a,b,c++[x],by rw [eq]; simp,hit⟩
    · refine ⟨l,x,[],by simp,?_⟩
      generalize hp : run E w q board l = p at *
      by_cases hx : x ∈ p.free
      · simp only [step,if_pos hx] at hy
        split at hy
        next z rec =>
          have eq := (List.mem_cons.mp hy).resolve_right old
          simpa [eq] using rec
        next => contradiction
      · simp [step,hx,old] at hy

/-- On any covering input history the replies attain the discrepancy bound
in each test, counted as distinct words on the original board. -/
theorem covering_bound {board : Finset V} (wp : ∀ i, 0 < w i)
    (hq : 0 < q) (h1 : q ≤ 1/2) (xs : List V) (cover : board ⊆ xs.toFinset) (i : I) :
    let p := run E w q board xs
    (1/2-q)*((board ∩ E i).card:ℝ) - log ((1+q)*(∑ j, w j)/w i)/(2*q)
      ≤ (p.outputs.toFinset ∩ E i).card := by
  let p := run E w q board xs
  have empty : p.free = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun x hx => by
    obtain ⟨b,no⟩ := Finset.mem_sdiff.mp (free_subset E w q board xs hx)
    exact no (cover b)
  have count (a : List V) (nd : a.Nodup) :
      a.countP (fun x => decide (x ∈ E i)) = (a.toFinset ∩ E i).card := by
    rw [List.countP_eq_length_filter,←List.toFinset_card_of_nodup (nd.filter _)]
    congr 1; ext; simp
  obtain ⟨ha,hg,dis,_,all⟩ := free_partition E w q board xs
  change p.free ∪ (p.inputs.toFinset ∪ p.outputs.toFinset) = board at all
  rw [empty,Finset.empty_union] at all
  have mass : (board ∩ E i).card = (p.inputs.toFinset ∩ E i).card + (p.outputs.toFinset ∩ E i).card := by
    rw [←all,Finset.union_inter_distrib_right,Finset.card_union_of_disjoint]
    exact dis.mono (Finset.inter_subset_left) (Finset.inter_subset_left)
  have pr := run_ready E w q board xs
  change Ready E w q board p at pr
  have disc (p : Position V) (pr : Ready E w q board p) : (1/2-q)*((p.inputs.countP (fun x => decide (x ∈ E i)):ℝ)+
      (p.outputs.countP (fun x => decide (x ∈ E i)):ℝ)) -
      log ((1+q)*(∑ j, w j)/w i)/(2*q) ≤ p.outputs.countP (fun x => decide (x ∈ E i)) := by
    cases pr with
    | start => simp [initial]; have := Finset.single_le_sum (fun j _ => (wp j).le) (Finset.mem_univ i)
               have logpos : 0 ≤ log ((1+q)*(∑ j, w j)/w i) := by
                 apply Real.log_nonneg; apply (le_div_iff₀ (wp i)).2
                 nlinarith [mul_nonneg hq.le ((wp i).le.trans this)]
               positivity
    | last played =>
      have h := discrepancy E wp hq h1 played i
      dsimp only at h ⊢
      field_simp [hq.ne'] at h ⊢
      linarith
    | answered played hf =>
      have h := discrepancy E wp hq h1 played i
      dsimp only at h ⊢
      simp only [List.countP_cons]
      split <;> push_cast <;> field_simp [hq.ne'] at h ⊢ <;> nlinarith
  have hdisc := disc p pr
  rw [count _ ha,count _ hg,←Nat.cast_add,←mass] at hdisc
  exact hdisc

end
end GenLimit.KleinbergWei.Banach.FiniteGame
