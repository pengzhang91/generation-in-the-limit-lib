import GenLimit.NoRegretLanguageGeneration.VCCounterexample

namespace PredictionToGeneration.Cofinite

/-- A computable bound strictly above every member of a finite list. -/
def freshAbove : List Nat → Nat
  | [] => 1
  | x :: xs => max x (freshAbove xs) + 1

theorem lt_freshAbove (xs : List Nat) (x : Nat) (hx : x ∈ xs) : x < freshAbove xs := by
  induction xs with
  | nil => simp at hx
  | cons y xs ih =>
    simp only [List.mem_cons] at hx
    simp only [freshAbove]
    rcases hx with rfl | hx
    · have := Nat.le_max_left x (freshAbove xs); omega
    · have := ih hx
      have := Nat.le_max_right y (freshAbove xs); omega

theorem freshAbove_not_mem (xs : List Nat) : freshAbove xs ∉ xs := by
  intro h
  have := lt_freshAbove xs _ h
  omega

def hypothesis (excluded : List Nat) : Hypothesis Nat := fun x => !excluded.contains x

def H : HypothesisClass Nat := fun h => ∃ excluded, h = hypothesis excluded

@[simp] theorem hypothesis_positive (excluded : List Nat) (x : Nat) :
    hypothesis excluded x = true ↔ x ∉ excluded := by simp [hypothesis]

@[simp] theorem hypothesis_negative (excluded : List Nat) (x : Nat) :
    hypothesis excluded x = false ↔ x ∈ excluded := by simp [hypothesis]

theorem uus : UUS H := by
  intro h ⟨e,he⟩ seen
  subst h
  let x := freshAbove (e++seen)
  have hn := freshAbove_not_mem (e++seen)
  simp only [List.mem_append,not_or] at hn
  exact ⟨x,hn.2,(hypothesis_positive e x).mpr hn.1⟩

/-- A horizon-independent generator whose outputs eventually exceed each exclusion set. -/
def generator : Generator Nat where
  output xs := max xs.length (freshAbove xs)
  fresh xs := by
    intro hm
    have := lt_freshAbove xs _ hm
    have := Nat.le_max_right xs.length (freshAbove xs)
    omega

/-- For each target, all outputs after a target-dependent round are valid,
even on arbitrary demonstration histories. -/
theorem nonuniform_generation (h : Hypothesis Nat) (hh : H h) :
    ∃ B : Nat, ∀ xs : List Nat, B ≤ xs.length → h (generator.output xs) = true := by
  obtain ⟨e,rfl⟩ := hh
  refine ⟨freshAbove e,?_⟩
  intro xs hb
  apply (hypothesis_positive e _).mpr
  intro hm
  have hlt := lt_freshAbove e _ hm
  have := Nat.le_max_left xs.length (freshAbove xs)
  change max xs.length (freshAbove xs) < freshAbove e at hlt
  omega

/-- Every past demonstration is distinct from every past output. -/
def DisjointHistory (τ : Trajectory Nat) : Prop :=
  ∀ x ∈ demonstrations τ, ∀ z ∈ τ.map Prod.fst, x ≠ z

theorem disjoint_terminal {τ : Trajectory Nat} (hd : DisjointHistory τ) :
    RealizableBad H τ.length τ := by
  let e := τ.map Prod.fst
  have hp : ∀ x ∈ demonstrations τ, hypothesis e x = true := by
    intro x hx
    apply (hypothesis_positive e x).mpr
    intro he
    exact hd x hx x he rfl
  have hn : ∀ z x, (z,x) ∈ τ → hypothesis e z = false := by
    intro z x hx
    apply (hypothesis_negative e z).mpr
    exact List.mem_map.mpr ⟨(z,x),hx,rfl⟩
  have both : Realizes (hypothesis e) τ ∧ mistakes (hypothesis e) τ = τ.length := by
    clear hd
    clear_value e
    induction τ with
    | nil => exact ⟨trivial,rfl⟩
    | cons zx τ ih =>
      have ip := fun x (hx : x ∈ demonstrations τ) => hp x (by simp [demonstrations] at hx ⊢; exact Or.inr hx)
      have ine := fun z x (hx : (z,x) ∈ τ) => hn z x (List.mem_cons_of_mem _ hx)
      obtain ⟨hr,hm⟩ := ih ip ine
      exact ⟨⟨hp zx.2 (by simp [demonstrations]),hr⟩,
        by simp [mistakes,loss,hn zx.1 zx.2 (by simp),hm,Nat.add_comm]⟩
  exact ⟨hypothesis e,⟨e,rfl⟩,both.1,by omega⟩

theorem forces_all_aux (n : Nat) (τ : Trajectory Nat) (hd : DisjointHistory τ) :
    Forces (RealizableBad H (τ.length+n)) n τ := by
  induction n generalizing τ with
  | zero => simpa using disjoint_terminal hd
  | succ n ih =>
    intro z hz
    let x := freshAbove (z :: demonstrations τ ++ τ.map Prod.fst)
    have hx := freshAbove_not_mem (z :: demonstrations τ ++ τ.map Prod.fst)
    change x ∉ z :: demonstrations τ ++ τ.map Prod.fst at hx
    simp only [List.mem_cons,List.mem_append,not_or] at hx
    refine ⟨x,hx.1.2,?_⟩
    have hd' : DisjointHistory ((z,x)::τ) := by
      intro y hy w hw
      simp only [demonstrations,List.map_cons,List.mem_cons] at hy hw
      rcases hy with rfl | hy <;> rcases hw with rfl | hw
      · exact hx.1.1
      · intro he; exact hx.2 (he ▸ hw)
      · intro he; exact hz (he ▸ hy)
      · exact hd y hy w hw
    have hh := ih ((z,x)::τ) hd'
    simpa [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem mf_forces_horizon (T : Nat) : MFForces H T T := by
  have hd : DisjointHistory [] := by simp [DisjointHistory,demonstrations]
  simpa using forces_all_aux T [] hd

theorem smf_forces_horizon (T : Nat) : SMFForces H T (T : Int) :=
  realizable_forcing_implies_signed H T T (mf_forces_horizon T)

theorem every_strategy_linear (T : Nat) (s : Strategy Nat T []) :
    ∃ τ h, Outcome s τ ∧ Legal τ ∧ τ.length = T ∧ H h ∧
      Realizes h τ ∧ mistakes h τ = T ∧ regret h τ = (T : Int) := by
  obtain ⟨τ,h,ho,hl,ht,hh,hr,hm⟩ := realizable_lower_bound H T T (mf_forces_horizon T) s
  have hb := mistakes_le_length h τ
  have he : mistakes h τ = T := by omega
  exact ⟨τ,h,ho,hl,ht,hh,hr,he,by rw [regret_eq_mistakes h τ hr,he]⟩




/-- Finite characteristic word for an exclusion set. -/
def mask (e : List Nat) : List Bool :=
  List.ofFn (fun i : Fin (freshAbove e) => e.contains i.val)

theorem mask_determines_hypothesis (e f : List Nat) (he : mask e = mask f) :
    hypothesis e = hypothesis f := by
  have hlen : freshAbove e = freshAbove f := by
    have := congrArg List.length he
    simpa [mask] using this
  funext x
  by_cases hx : x < freshAbove e
  · have hxe : x < (mask e).length := by simpa [mask] using hx
    have hxf : x < (mask f).length := by simpa [mask,← hlen] using hx
    have hh : (mask e)[x] = (mask f)[x] := by congr 1
    have hc : e.contains x = f.contains x := by simpa [mask] using hh
    exact congrArg Bool.not hc
  · have hne : x ∉ e := fun hm => hx (lt_freshAbove e x hm)
    have hnf : x ∉ f := by
      intro hm
      have := lt_freshAbove f x hm
      omega
    have he' := (hypothesis_positive e x).mpr hne
    have hf' := (hypothesis_positive f x).mpr hnf
    rw [he',hf']

/-- Countability expressed as an injection of the class into the naturals. -/
theorem countable_class : ∃ code : {h : Hypothesis Nat // H h} → Nat,
    ∀ a b, code a = code b → a = b := by
  classical
  let code : {h : Hypothesis Nat // H h} → Nat :=
    fun a => VCCounterexample.wordCode (mask (Classical.choose a.property))
  refine ⟨code, ?_⟩
  intro a b he
  have hw := VCCounterexample.wordCode_injective _ _ he
  apply Subtype.eq
  calc
    a.val = hypothesis (Classical.choose a.property) := Classical.choose_spec a.property
    _ = hypothesis (Classical.choose b.property) := mask_determines_hypothesis _ _ hw
    _ = b.val := (Classical.choose_spec b.property).symm

theorem dimensions_eq_horizon (T : Nat) : MF H T = T ∧ SMF H T = T := by
  have hne : ∃ h, H h := ⟨hypothesis [],[],rfl⟩
  have hm := (mf_spec H uus hne T).2 T (mf_forces_horizon T)
  have hs := (smf_spec H uus hne T).2 T (smf_forces_horizon T)
  have hmu := mf_le_horizon H T
  have hsu := smf_le_horizon H T
  omega

end PredictionToGeneration.Cofinite

