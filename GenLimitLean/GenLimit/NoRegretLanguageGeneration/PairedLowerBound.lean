import GenLimit.NoRegretLanguageGeneration.PairedPoints
import GenLimit.NoRegretLanguageGeneration.SparseGraph

namespace PredictionToGeneration.PairedPoints

def baseIndex : Point → Nat
  | .base i => i
  | .pair _ _ _ _ => 0

def demoIndices (τ : Trajectory Point) : List Nat := τ.map (fun r => baseIndex r.2)

def BaseDemonstrations (τ : Trajectory Point) : Prop :=
  ∀ z x, (z,x) ∈ τ → ∃ i, x = .base i

def NoBaseOutput (τ : Trajectory Point) : Prop :=
  ∀ i x, (.base i,x) ∈ τ → i ∉ demoIndices τ

def demoSet (τ : Trajectory Point) : Finset Nat := (demoIndices τ).toFinset

def outputEdge : Point → Option SparseGraph.Edge
  | .base _ => none
  | .pair i j _ _ => some (i,j)

def graphEdges (τ : Trajectory Point) : Finset SparseGraph.Edge :=
  ((τ.filterMap (fun r => outputEdge r.1)).toFinset).filter
    (fun e => e.1 ∈ demoSet τ ∧ e.2 ∈ demoSet τ)

theorem graph_valid (τ : Trajectory Point) : SparseGraph.Valid (demoSet τ) (graphEdges τ) := by
  intro e he
  obtain ⟨he,h1,h2⟩ := Finset.mem_filter.mp he
  obtain ⟨⟨z,x⟩,_,hz⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp he)
  cases z with
  | base i => simp [outputEdge] at hz
  | pair i j k hij =>
    simp only [outputEdge,Option.some.injEq] at hz
    subst e
    exact ⟨h1,h2,hij⟩

theorem graph_card_le (τ : Trajectory Point) : (graphEdges τ).card ≤ τ.length := by
  apply Nat.le_trans (Finset.card_filter_le _ _)
  apply Nat.le_trans (List.toFinset_card_le _)
  exact List.length_filterMap_le _ _

theorem pair_edge_mem (τ : Trajectory Point) (i j k : Nat) (hij : i < j) (x : Point)
    (hp : (.pair i j k hij,x) ∈ τ) (hi : i ∈ demoSet τ) (hj : j ∈ demoSet τ) :
    (i,j) ∈ graphEdges τ := by
  apply Finset.mem_filter.mpr
  refine ⟨List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨(.pair i j k hij,x),hp,rfl⟩),hi,hj⟩

def excludedFor (τ : Trajectory Point) (I : Finset Nat) : List Nat :=
  (τ.flatMap (fun r => indices r.1)).filter (fun i => decide (i ∉ I))

@[simp] theorem mem_excludedFor (τ : Trajectory Point) (I : Finset Nat) (i : Nat) :
    i ∈ excludedFor τ I ↔ (∃ z x, (z,x) ∈ τ ∧ i ∈ indices z) ∧ i ∉ I := by
  simp [excludedFor,List.mem_flatMap,Prod.exists]

theorem outputs_invalid (τ : Trajectory Point) (hn : NoBaseOutput τ) (I : Finset Nat)
    (his : I ⊆ demoSet τ) (hind : SparseGraph.Independent (graphEdges τ) I) :
    ∀ z x, (z,x) ∈ τ → hypothesis (excludedFor τ I) z = false := by
  intro z x hm
  have neg (i : Nat) (hi : i ∈ indices z) (hni : i ∉ I) : i ∈ excludedFor τ I :=
    (mem_excludedFor τ I i).mpr ⟨⟨z,x,hm,hi⟩,hni⟩
  cases z with
  | base i =>
    have hni : i ∉ I := fun hi => hn i x hm (List.mem_toFinset.mp (his hi))
    have he := neg i (by simp [indices]) hni
    simp [hypothesis,indices,he]
  | pair i j k hij =>
    have hnij : ¬ (i ∈ I ∧ j ∈ I) := by
      intro hh
      exact hind (i,j) (pair_edge_mem τ i j k hij x hm (his hh.1) (his hh.2)) hh
    by_cases hi : i ∈ I
    · have hj : j ∉ I := fun hj => hnij ⟨hi,hj⟩
      have he := neg j (by simp [indices]) hj
      simp [hypothesis,indices,he]
    · have he := neg i (by simp [indices]) hi
      simp [hypothesis,indices,he]

theorem mistakes_all (h : Hypothesis Point) (τ : Trajectory Point)
    (hn : ∀ z x, (z,x) ∈ τ → h z = false) : mistakes h τ = τ.length := by
  induction τ with
  | nil => rfl
  | cons zx τ ih =>
    have ht := ih (fun z x hm => hn z x (List.mem_cons_of_mem _ hm))
    simp [mistakes,loss,hn zx.1 zx.2 (by simp),ht,Nat.add_comm]

theorem demonstrationLoss_count (e : List Nat) (τ : Trajectory Point)
    (hb : BaseDemonstrations τ) :
    demonstrationLoss (hypothesis e) τ = ((demoIndices τ).filter e.contains).length := by
  induction τ with
  | nil => rfl
  | cons zx τ ih =>
    obtain ⟨i,hi⟩ := hb zx.1 zx.2 (by simp)
    have ht := ih (fun z x hm => hb z x (List.mem_cons_of_mem _ hm))
    simp only [demonstrationLoss,demoIndices,List.map_cons,hi,baseIndex,List.filter_cons]
    rw [ht]
    by_cases he : i ∈ e <;> simp [hypothesis,indices,loss,he,demoIndices,baseIndex,Nat.add_comm]

theorem comparator_regret (τ : Trajectory Point) (hb : BaseDemonstrations τ)
    (hn : NoBaseOutput τ) (hnd : (demoIndices τ).Nodup) :
    ∃ h, H h ∧ (τ.length : Int) ≤ 3 * regret h τ := by
  have hcard : (demoSet τ).card = τ.length := by
    simpa [demoSet,demoIndices] using List.toFinset_card_of_nodup hnd
  obtain ⟨I,his,hind,hbound⟩ := SparseGraph.independent_bound (demoSet τ) (graphEdges τ) (graph_valid τ)
  have hE := graph_card_le τ
  have hI : τ.length ≤ 3*I.card := by omega
  let e := excludedFor τ I
  have hm : mistakes (hypothesis e) τ = τ.length :=
    mistakes_all _ _ (outputs_invalid τ hn I his hind)
  let B := (demoSet τ).filter (fun i => i ∈ e)
  have hB : B.card = demonstrationLoss (hypothesis e) τ := by
    rw [demonstrationLoss_count e τ hb]
    have heq : B = ((demoIndices τ).filter e.contains).toFinset := by
      simp [B,demoSet,List.toFinset_filter]
    rw [heq]
    exact List.toFinset_card_of_nodup (hnd.filter _)
  have hd : Disjoint B I := by
    apply Finset.disjoint_left.mpr
    intro i hiB hiI
    have he := (Finset.mem_filter.mp hiB).2
    exact ((mem_excludedFor τ I i).mp he).2 hiI
  have hs : B ∪ I ⊆ demoSet τ := Finset.union_subset (Finset.filter_subset _ _) his
  have hBI := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hd,hcard,hB] at hBI
  refine ⟨hypothesis e,⟨e,rfl⟩,?_⟩
  unfold regret
  rw [hm]
  omega




theorem base_mem_of_index (τ : Trajectory Point) (hb : BaseDemonstrations τ) (i : Nat)
    (hi : i ∈ demoIndices τ) : Point.base i ∈ demonstrations τ := by
  obtain ⟨⟨z,x⟩,hx,he⟩ := List.mem_map.mp hi
  obtain ⟨j,rfl⟩ := hb z x hx
  change j = i at he
  subst j
  exact List.mem_map.mpr ⟨(z,.base i),hx,rfl⟩

def AdversarialInvariant (τ : Trajectory Point) : Prop :=
  BaseDemonstrations τ ∧ NoBaseOutput τ ∧ (demoIndices τ).Nodup

theorem adversarial_step (τ : Trajectory Point) (ha : AdversarialInvariant τ)
    (z : Point) (hz : Fresh τ z) :
    ∃ x, Fresh τ x ∧ AdversarialInvariant ((z,x)::τ) := by
  let i := Cofinite.freshAbove (demoIndices τ ++ indices z ++ τ.flatMap (fun r => indices r.1))
  have hi := Cofinite.freshAbove_not_mem (demoIndices τ ++ indices z ++ τ.flatMap (fun r => indices r.1))
  change i ∉ demoIndices τ ++ indices z ++ τ.flatMap (fun r => indices r.1) at hi
  simp only [List.mem_append,not_or] at hi
  have hif : Fresh τ (.base i) := by
    intro hm
    obtain ⟨⟨w,x⟩,hx,he⟩ := List.mem_map.mp hm
    have him : i ∈ demoIndices τ := by
      apply List.mem_map.mpr
      exact ⟨(w,x),hx,by change x = .base i at he; simp [he,baseIndex]⟩
    exact hi.1.1 him
  refine ⟨.base i,hif,?_,?_,?_⟩
  · intro w x hm
    rcases List.mem_cons.mp hm with he | he
    · cases he
      exact ⟨i,rfl⟩
    · exact ha.1 w x he
  · intro j x hm
    simp only [demoIndices,List.map_cons,baseIndex,List.mem_cons,not_or]
    rcases List.mem_cons.mp hm with he | he
    · have hzj : z = .base j := (congrArg Prod.fst he).symm
      have hji : j ≠ i := by
        intro hji
        apply hi.1.2
        simp [hzj,indices,hji]
      exact ⟨hji,fun hj => hz (hzj ▸ base_mem_of_index τ ha.1 j hj)⟩
    · have hji : j ≠ i := by
        intro hji
        apply hi.2
        apply List.mem_flatMap.mpr
        exact ⟨(.base j,x),he,by simp [indices,hji]⟩
      exact ⟨hji,ha.2.1 j x he⟩
  · exact List.nodup_cons.mpr ⟨hi.1.1,ha.2.2⟩

theorem signed_forces_aux (n : Nat) (τ : Trajectory Point) (ha : AdversarialInvariant τ) :
    Forces (fun leaf => ∃ h, H h ∧ ((τ.length+n : Nat) : Int) ≤ 3 * regret h leaf) n τ := by
  induction n generalizing τ with
  | zero => simpa using comparator_regret τ ha.1 ha.2.1 ha.2.2
  | succ n ih =>
    intro z hz
    obtain ⟨x,hx,ha'⟩ := adversarial_step τ ha z hz
    refine ⟨x,hx,?_⟩
    have hh := ih ((z,x)::τ) ha'
    simpa [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Exact integer form of the manuscript's signed lower bound T/3. -/
theorem smf_forces_third (T : Nat) : SMFForces H T (((T+2)/3 : Nat) : Int) := by
  have ha : AdversarialInvariant [] := by
    simp [AdversarialInvariant,BaseDemonstrations,NoBaseOutput,demoIndices]
  have hf := signed_forces_aux T [] ha
  apply forces_mono (n := T) (τ := []) (hf := hf)
  intro τ ⟨h,hh,hr⟩
  refine ⟨h,hh,?_⟩
  simp only [List.length_nil,Nat.zero_add] at hr
  omega

/-- The paired class has a uniform realizable bound but linear signed dimension. -/
theorem paired_separation (T : Nat) : MF H T ≤ 2 ∧ T ≤ 3 * SMF H T := by
  have hne : ∃ h, H h := ⟨hypothesis [],[],rfl⟩
  have hs := (smf_spec H uus hne T).2 _ (smf_forces_third T)
  exact ⟨mf_le_two T,by omega⟩

theorem every_strategy_signed_third (T : Nat) (s : Strategy Point T []) :
    ∃ τ h, Outcome s τ ∧ Legal τ ∧ τ.length = T ∧ H h ∧
      (T : Int) ≤ 3 * regret h τ := by
  obtain ⟨τ,h,ho,hl,ht,hh,hr⟩ := agnostic_lower_bound H T _ (smf_forces_third T) s
  exact ⟨τ,h,ho,hl,ht,hh,by omega⟩

end PredictionToGeneration.PairedPoints

