import GenLimit.Paper23_BanachDensityTopologyAndGeometry.BoardPermutations

/-! The finite alternating game of Kleinberg and Wei, arXiv:2611.14887v1,
Lemma 8.1. Black must claim a free point. White may pass or claim one
remaining point. A terminal condition sees precisely the set claimed by White. -/
namespace GenLimit.KleinbergWei.Banach.ClaimGame
open BoardPermutations Finset
open scoped Classical
noncomputable section

def Free (D : Finset ℕ) (move : Move) (h : List ℕ) (x : ℕ) : Prop :=
  x ∈ D ∧ x ∉ h ∧ x ∉ earned move h

/-- The history records Black's choices. White's strategy reconstructs its replies. -/
inductive Play (D : Finset ℕ) (move : Move) : List ℕ → Prop
  | start : Play D move []
  | claim {h x} (earlier : Play D move h) (free : Free D move h x) :
      Play D move (h ++ [x])

def Safe (D : Finset ℕ) (move : Move) : Prop :=
  ∀ h, Play D move h → ∀ x, Free D move h x → ∀ y, move h x = some y →
    Free D move h y ∧ y ≠ x

def CanForce (D : Finset ℕ) (quota : Set ℕ → Prop) : Prop :=
  ∃ move : Move, Safe D move ∧ ∀ h, Play D move h → (∀ x, ¬ Free D move h x) →
    quota (earned move h)

private def projectStep (D : Finset ℕ) (move : Move) (p : List ℕ) (x : ℕ) :=
  if Free D move p x then p ++ [x] else p

private def project (D : Finset ℕ) (move : Move) (h : List ℕ) :=
  h.foldl (projectStep D move) []

private theorem project_push (D : Finset ℕ) (move : Move) (h : List ℕ) (x : ℕ) :
    project D move (h ++ [x]) = projectStep D move (project D move h) x := by simp [project]

private theorem project_play (D : Finset ℕ) (move : Move) (h : List ℕ) :
    Play D move (project D move h) := by
  induction h using List.reverseRecOn with
  | nil => exact .start
  | append_singleton h x ih =>
    rw [project_push,projectStep]
    split
    next free => exact .claim ih free
    next => exact ih

private theorem seen {D : Finset ℕ} {move : Move} {h : List ℕ} {y : ℕ}
    (onBoard : y ∈ D) (input : y ∈ h) : ¬ Free D move (project D move h) y := by
  induction h using List.reverseRecOn with
  | nil => simp at input
  | append_singleton h x ih =>
    rw [project_push,projectStep]
    split
    next free =>
      intro later
      obtain ⟨_,absent,unearned⟩ := later
      simp only [List.mem_append,List.mem_singleton,not_or] at absent
      have old : y ∈ h := by simpa [absent.2] using input
      exact ih old ⟨onBoard,absent.1,fun m => unearned (earned_push.mpr (.inl m))⟩
    next spent =>
      by_cases eq : y = x
      · simpa [eq] using spent
      · exact ih (by simpa [eq] using input)

private def liftMove (D : Finset ℕ) (move : Move) (h : List ℕ) (x : ℕ) :=
  if Free D move (project D move h) x then move (project D move h) x else none

private theorem lift_legal {D move} (safe : Safe D move) : Legal D (liftMove D move) := by
  intro h x y hit
  unfold liftMove at hit
  split at hit
  next free =>
    obtain ⟨fy,ne⟩ := safe _ (project_play ..) x free y hit
    refine ⟨free.1,fy.1,?_⟩
    simp only [List.mem_append,List.mem_singleton,not_or]
    exact ⟨fun input => seen fy.1 input fy,ne⟩
  next => contradiction

private theorem lift_earned (D : Finset ℕ) (move : Move) (h : List ℕ) :
    earned (liftMove D move) h = earned move (project D move h) := by
  induction h using List.reverseRecOn with
  | nil => ext y; simp [project,earned]
  | append_singleton h x ih =>
    ext y
    rw [project_push,projectStep,earned_push,ih]
    split
    next free => simp only [liftMove,if_pos free,earned_push]
    next spent => simp [liftMove,spent]

private def uniqueMove (move : Move) (h : List ℕ) (x : ℕ) : Option ℕ :=
  (move h x).filter (fun y => decide (y ∉ earned move h))

private theorem unique_hit {move : Move} {h x y} :
    uniqueMove move h x = some y ↔ move h x = some y ∧ y ∉ earned move h := by
  cases hit : move h x with
  | none => simp [uniqueMove,hit]
  | some z =>
    by_cases e : z = y
    · subst y; by_cases mem : z ∈ earned move h <;> simp [uniqueMove,hit,mem]
    · simp [uniqueMove,hit,e]

private theorem unique_earned (move : Move) (h : List ℕ) :
    earned (uniqueMove move) h = earned move h := by
  induction h using List.reverseRecOn with
  | nil => ext y; simp [earned]
  | append_singleton h x ih =>
    ext y
    simp only [earned_push,ih,unique_hit]
    tauto

private theorem play_inputs {D move h} (p : Play D move h) : h.Nodup ∧ h.toFinset ⊆ D := by
  induction p with
  | start => simp
  | @claim h x _ free ih =>
    obtain ⟨nd,inside⟩ := ih
    refine ⟨List.nodup_append.mpr ⟨nd,by simp,?_⟩,
      by simpa [Finset.insert_subset_iff] using And.intro free.1 inside⟩
    rintro a ha b hb rfl
    exact free.2.1 ((List.mem_singleton.mp hb) ▸ ha)

private theorem terminal_earned {D move h} (legal : Legal D move)
    (exhausted : ∀ x, ¬ Free D (uniqueMove move) h x) (tail : List ℕ) :
    earned move (h ++ tail) = earned move h := by
  induction tail using List.reverseRecOn with
  | nil => simp
  | append_singleton tail x ih =>
    rw [← List.append_assoc]
    ext y
    rw [earned_push,ih]
    refine or_iff_left_of_imp fun hit => ?_
    obtain ⟨_,onBoard,fresh⟩ := legal hit
    by_contra missing
    apply exhausted y
    exact ⟨onBoard,fun mem => fresh (by simp [mem]),by rwa [unique_earned]⟩

/-- With any terminal condition, a strategy against all full permutations
exists exactly when White can enforce the same condition against every
legal sequence of Black claims. No monotonicity of the condition is needed. -/
theorem canForce_iff (D : Finset ℕ) (quota : Set ℕ → Prop) :
    CanForce D quota ↔ ∃ move : Move, Legal D move ∧
      ∀ h : List ℕ, h.Nodup → h.toFinset = D → quota (earned move h) := by
  constructor
  · rintro ⟨move,safe,win⟩
    refine ⟨liftMove D move,lift_legal safe,fun h _ full => ?_⟩
    rw [lift_earned]
    apply win _ (project_play ..)
    intro x free
    have mem : x ∈ h.toFinset := full.symm ▸ free.1
    exact seen free.1 (List.mem_toFinset.mp mem) free
  · rintro ⟨move,legal,win⟩
    refine ⟨uniqueMove move,?_,?_⟩
    · intro h _ x _ y hit
      obtain ⟨actual,new⟩ := unique_hit.mp hit
      obtain ⟨_,onBoard,fresh⟩ := legal actual
      simp only [List.mem_append,List.mem_singleton,not_or] at fresh
      exact ⟨⟨onBoard,fresh.1,by rwa [unique_earned]⟩,fresh.2⟩
    · intro h play exhausted
      obtain ⟨distinct,inside⟩ := play_inputs play
      let rest := D \ h.toFinset
      have dis : h.Disjoint rest.toList := by
        intro x input rem
        exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp rem)).2 (List.mem_toFinset.mpr input)
      have nd : (h ++ rest.toList).Nodup := List.nodup_append.mpr
        ⟨distinct,rest.nodup_toList,fun a ha b hb eq => dis ha (eq.symm ▸ hb)⟩
      have full : (h ++ rest.toList).toFinset = D := by
        ext x
        simp only [List.toFinset_append,Finset.toList_toFinset,mem_union,rest,mem_sdiff]
        constructor
        · rintro (i | ⟨i,_⟩)
          · exact inside i
          · exact i
        · intro i; by_cases old : x ∈ h.toFinset <;> tauto
      simpa only [unique_earned,terminal_earned legal exhausted] using win _ nd full

/-- A strategy can ignore repeats, earlier White claims, and inputs outside
its board, while enforcing exactly the same terminal condition. -/
theorem canForce_iff_covering (D : Finset ℕ) (quota : Set ℕ → Prop) :
    CanForce D quota ↔ ∃ move : Move, Legal D move ∧
      ∀ h : List ℕ, D ⊆ h.toFinset → quota (earned move h) := by
  constructor
  · rintro ⟨move,safe,win⟩
    refine ⟨liftMove D move,lift_legal safe,fun h covered => ?_⟩
    rw [lift_earned]
    exact win _ (project_play ..) fun x free =>
      seen free.1 (List.mem_toFinset.mp (covered free.1)) free
  · rintro ⟨move,safe,win⟩
    exact (canForce_iff ..).mpr ⟨move,safe,fun h _ full => win h full.ge⟩

/-- Play any collection of games on disjoint parts of a board. Each move
serves the part containing Black's input. Local requirements see exactly
the outputs in their part, even for terminal predicates that depend on the
absence of particular outputs. -/
theorem canForce_partition {ι : Type*} (D : Finset ℕ) (part : ℕ → ι)
    (quota : ι → Set ℕ → Prop)
    (games : ∀ i, CanForce (D.filter (fun x => part x = i)) (quota i)) :
    CanForce D (fun W => ∀ i, quota i (W ∩ {x | part x = i})) := by
  choose move safe win using fun i => (canForce_iff_covering ..).mp (games i)
  let play (h : List ℕ) (x : ℕ) := move (part x) h x
  apply (canForce_iff_covering ..).mpr
  refine ⟨play,?_,fun h cover i => ?_⟩
  · intro h x y hit
    obtain ⟨hx,hy,fresh⟩ := safe (part x) hit
    exact ⟨(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hy).1,fresh⟩
  · have same : earned play h ∩ {x | part x = i} = earned (move i) h := by
      ext y
      constructor
      · rintro ⟨⟨p,x,hp,hit⟩,group⟩
        have loc := (Finset.mem_filter.mp (safe (part x) hit).2.1).2
        change part y = i at group
        change move (part x) p x = some y at hit
        exact ⟨p,x,hp,loc.symm.trans group ▸ hit⟩
      · rintro ⟨p,x,hp,hit⟩
        obtain ⟨hx,hy,_⟩ := safe i hit
        exact ⟨⟨p,x,hp,by simpa [play,(Finset.mem_filter.mp hx).2] using hit⟩,
          (Finset.mem_filter.mp hy).2⟩
    rw [same]
    exact win i h ((Finset.filter_subset _ D).trans cover)

end
end GenLimit.KleinbergWei.Banach.ClaimGame
