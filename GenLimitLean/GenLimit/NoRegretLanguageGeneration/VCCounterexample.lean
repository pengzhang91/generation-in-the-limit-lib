import GenLimit.NoRegretLanguageGeneration.FiniteMinimax

namespace PredictionToGeneration.VCCounterexample

/-- The manuscript's nonempty finite binary strings. -/
abbrev String := {p : List Bool // p ≠ []}

/-- Prefix membership in the infinite path obtained by appending zeros. -/
def OnPath (p : List Bool) (x : String) : Prop :=
  ∃ k, x.val <+: p ++ List.replicate k false

noncomputable def path (p : List Bool) : Hypothesis String :=
  by
  classical
  exact fun x => if OnPath p x then true else false

def H : HypothesisClass String := fun h => ∃ p, h = path p

@[simp] theorem path_positive {p : List Bool} {x : String} :
    path p x = true ↔ OnPath p x := by
  classical
  simp [path]

/-- Every member is specified by a finite binary word followed by zeros. -/
theorem finite_word_parametrization (h : Hypothesis String) :
    H h ↔ ∃ p : List Bool, h = path p := Iff.rfl

theorem onPath_chain {p : List Bool} {x y : String}
    (hx : OnPath p x) (hy : OnPath p y) : x.val <+: y.val ∨ y.val <+: x.val := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨l, hl⟩ := hy
  have rep (a b : Nat) : List.replicate a false <+: List.replicate (a+b) false := by
    rw [← List.replicate_append_replicate]
    exact List.prefix_append _ _
  have hpk : p ++ List.replicate k false <+: p ++ List.replicate (k+l) false := by
    exact (List.prefix_append_right_inj p).mpr (rep k l)
  have hpl : p ++ List.replicate l false <+: p ++ List.replicate (k+l) false := by
    rw [Nat.add_comm k l]
    exact (List.prefix_append_right_inj p).mpr (rep l k)
  exact List.prefix_or_prefix_of_prefix (hk.trans hpk) (hl.trans hpl)

theorem onPath_downward {p : List Bool} {x y : String}
    (hxy : x.val <+: y.val) (hy : OnPath p y) : OnPath p x := by
  obtain ⟨k, hk⟩ := hy
  exact ⟨k, hxy.trans hk⟩

/-- VC dimension one, expressed by its singleton and pair shattering tests. -/
def VCOne (C : HypothesisClass String) : Prop :=
  (∃ x, (∃ h, C h ∧ h x = true) ∧ (∃ h, C h ∧ h x = false)) ∧
  ∀ x y, x ≠ y → ¬ (∀ a b : Bool, ∃ h, C h ∧ h x = a ∧ h y = b)

theorem vc_one : VCOne H := by
  classical
  constructor
  · let x : String := ⟨[false], by simp⟩
    refine ⟨x, ⟨path [], ⟨[], rfl⟩, ?_⟩, ⟨path [true], ⟨[true], rfl⟩, ?_⟩⟩
    · apply path_positive.mpr
      exact ⟨1, List.prefix_rfl⟩
    · simp only [path]
      have hn : ¬ OnPath [true] x := by
        rintro ⟨k, hk⟩
        have := List.cons_prefix_cons.mp hk
        cases this.1
      simp [hn]
  · intro x y _ hs
    obtain ⟨h, ⟨p, rfl⟩, hx, hy⟩ := hs true true
    rcases onPath_chain (path_positive.mp hx) (path_positive.mp hy) with hxy | hyx
    · obtain ⟨h, ⟨q, rfl⟩, hx, hy⟩ := hs false true
      have := path_positive.mpr (onPath_downward hxy (path_positive.mp hy))
      simp [hx] at this
    · obtain ⟨h, ⟨q, rfl⟩, hx, hy⟩ := hs true false
      have := path_positive.mpr (onPath_downward hyx (path_positive.mp hx))
      simp [hy] at this

/-- Every path support avoids every finite set of examples. -/
theorem uus : UUS H := by
  intro h ⟨p, hp⟩ seen
  subst h
  let n := (seen.map (fun x => x.val.length)).foldl Nat.max 0 + 1
  have bound : ∀ x ∈ seen, x.val.length < n := by
    have aux : ∀ (ls : List Nat) (a : Nat), ∀ k ∈ ls, k ≤ ls.foldl Nat.max a := by
      intro ls
      induction ls with
      | nil => simp
      | cons b ls ih =>
        intro a k hk
        simp only [List.mem_cons] at hk
        rcases hk with rfl | hk
        · have lower : ∀ (ts : List Nat) (v : Nat), v ≤ ts.foldl Nat.max v := by
            intro ts
            induction ts with
            | nil => intro v; exact Nat.le_refl _
            | cons c ts iht => intro v; exact Nat.le_trans (Nat.le_max_left _ _) (iht _)
          exact Nat.le_trans (Nat.le_max_right a k) (lower ls _)
        · exact ih _ _ hk
    intro x hx
    have := aux (seen.map (fun x => x.val.length)) 0 x.val.length (List.mem_map.mpr ⟨x,hx,rfl⟩)
    dsimp [n]
    omega
  let x : String := ⟨p ++ List.replicate n false, by
    intro he
    have := congrArg List.length he
    simp at this
    dsimp [n] at this
    omega⟩
  refine ⟨x, ?_, path_positive.mpr ⟨n, List.prefix_rfl⟩⟩
  intro hx
  have hb := bound x hx
  have hl : x.val.length = p.length + n := by simp [x]
  omega





/-- Two strings that cannot lie on one path. -/
def Incompatible (u v : List Bool) : Prop := ¬ u <+: v ∧ ¬ v <+: u

theorem incompatible_extend {u p q : List Bool} (hi : Incompatible u p)
    (hpq : p <+: q) : Incompatible u q := by
  constructor
  · intro huq
    rcases List.prefix_or_prefix_of_prefix huq hpq with hup | hpu
    · exact hi.1 hup
    · exact hi.2 hpu
  · intro hqu
    exact hi.2 (hpq.trans hqu)

/-- A fresh output can be excluded by the next bit of the path. -/
theorem choose_bit (p z : List Bool) (hz : ¬ z <+: p) :
    ∃ b : Bool, Incompatible z (p ++ [b]) := by
  classical
  have child : ∃ b : Bool, ¬ p ++ [b] <+: z := by
    by_cases hp : p <+: z
    · obtain ⟨r, rfl⟩ := hp
      cases r with
      | nil => exact False.elim (hz (by simp))
      | cons a r =>
        refine ⟨!a, ?_⟩
        intro h
        have hh := (List.prefix_append_right_inj p).mp h
        have hh' := (List.cons_prefix_cons.mp hh).1
        cases a <;> simp at hh'
    · exact ⟨false, fun h => hp ((List.prefix_append _ _).trans h)⟩
  obtain ⟨b, hb⟩ := child
  refine ⟨b, ?_, hb⟩
  intro hz'
  rcases List.prefix_concat_iff.mp hz' with he | he
  · exact hb (he ▸ List.prefix_rfl)
  · exact hz he

/-- All nonempty prefixes have been demonstrated and every output is excluded. -/
def Invariant (p : List Bool) (τ : Trajectory String) : Prop :=
  (∀ x : String, x ∈ demonstrations τ ↔ x.val <+: p) ∧
  (∀ z x, (z,x) ∈ τ → Incompatible z.val p)

theorem invariant_step {p : List Bool} {τ : Trajectory String}
    (hi : Invariant p τ) (z : String) (hz : Fresh τ z) :
    ∃ (b : Bool) (x : String), x.val = p ++ [b] ∧ Fresh τ x ∧
      Invariant (p ++ [b]) ((z,x)::τ) := by
  have hzp : ¬ z.val <+: p := fun h => hz ((hi.1 z).mpr h)
  obtain ⟨b, hb⟩ := choose_bit p z.val hzp
  let x : String := ⟨p ++ [b], by simp⟩
  have hxf : Fresh τ x := by
    intro h
    have hh := ((hi.1 x).mp h).length_le
    simp [x] at hh
    omega
  refine ⟨b,x,rfl,hxf,?_,?_⟩
  · intro y
    simp only [demonstrations, List.map_cons, List.mem_cons]
    rw [show y = x ↔ y.val = p ++ [b] from ⟨fun h => congrArg Subtype.val h,
      fun h => Subtype.eq h⟩]
    change (y.val = p ++ [b] ∨ y ∈ demonstrations τ) ↔ y.val <+: p ++ [b]
    rw [hi.1 y, List.prefix_concat_iff]
  · intro w y hm
    simp only [List.mem_cons] at hm
    rcases hm with he | he
    · cases he
      exact hb
    · exact incompatible_extend (hi.2 w y he) (List.prefix_append _ _)

theorem invariant_terminal {p : List Bool} {τ : Trajectory String}
    (hi : Invariant p τ) : Realizes (path p) τ ∧ mistakes (path p) τ = τ.length := by
  have positive : ∀ x ∈ demonstrations τ, path p x = true := by
    intro x hx
    apply path_positive.mpr
    exact ⟨0, by simpa using (hi.1 x).mp hx⟩
  have negative : ∀ z x, (z,x) ∈ τ → path p z = false := by
    intro z x hm
    have hn : ¬ OnPath p z := by
      rintro ⟨k,hk⟩
      rcases List.prefix_or_prefix_of_prefix hk (List.prefix_append p _) with hp | hp
      · exact (hi.2 z x hm).1 hp
      · exact (hi.2 z x hm).2 hp
    classical
    simp [path, hn]
  clear hi
  induction τ with
  | nil => exact ⟨trivial,rfl⟩
  | cons zx τ ih =>
    have ip := fun x (hx : x ∈ demonstrations τ) => positive x (by simp [demonstrations] at hx ⊢; exact Or.inr hx)
    have ine := fun z x (hx : (z,x) ∈ τ) => negative z x (List.mem_cons_of_mem _ hx)
    obtain ⟨hr,hm⟩ := ih ip ine
    refine ⟨⟨positive zx.2 (by simp [demonstrations]),hr⟩,?_⟩
    simp [mistakes,loss,negative zx.1 zx.2 (by simp),hm,Nat.add_comm]

/-- One eventually-zero comparator invalidates every output at every horizon. -/
theorem forces_all_aux (n : Nat) (p : List Bool) (τ : Trajectory String)
    (hi : Invariant p τ) : Forces (RealizableBad H (τ.length+n)) n τ := by
  induction n generalizing p τ with
  | zero =>
    obtain ⟨hr,hm⟩ := invariant_terminal hi
    exact ⟨path p,⟨p,rfl⟩,hr,by omega⟩
  | succ n ih =>
    intro z hz
    obtain ⟨b,x,_,hx,hi'⟩ := invariant_step hi z hz
    refine ⟨x,hx,?_⟩
    have hh := ih (p++[b]) ((z,x)::τ) hi'
    simpa [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem mf_forces_horizon (T : Nat) : MFForces H T T := by
  have hi : Invariant [] [] := by
    constructor
    · intro x
      simp only [demonstrations,List.map_nil,List.not_mem_nil,false_iff,List.prefix_nil]
      exact x.property
    · simp
  simpa using forces_all_aux T [] [] hi

theorem smf_forces_horizon (T : Nat) : SMFForces H T (T : Int) :=
  realizable_forcing_implies_signed H T T (mf_forces_horizon T)

/-- Explicit legal terminal witness against every deterministic finite strategy. -/
theorem every_strategy_linear (T : Nat) (s : Strategy String T []) :
    ∃ τ h, Outcome s τ ∧ Legal τ ∧ τ.length = T ∧ H h ∧
      Realizes h τ ∧ mistakes h τ = T ∧ regret h τ = (T : Int) := by
  obtain ⟨τ,h,ho,hl,ht,hh,hr,hm⟩ := realizable_lower_bound H T T (mf_forces_horizon T) s
  have hb := mistakes_le_length h τ
  have he : mistakes h τ = T := by omega
  exact ⟨τ,h,ho,hl,ht,hh,hr,he,by rw [regret_eq_mistakes h τ hr,he]⟩




/-- A binary coding of finite words, with the empty word assigned zero. -/
def wordCode : List Bool → Nat
  | [] => 0
  | b :: p => 2 * wordCode p + if b then 2 else 1

theorem wordCode_injective (p q : List Bool) (he : wordCode p = wordCode q) : p = q := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => rfl
    | cons b q => cases b <;> simp [wordCode] at he <;> omega
  | cons a p ih =>
    cases q with
    | nil => cases a <;> simp [wordCode] at he <;> omega
    | cons b q =>
      cases a <;> cases b <;> simp only [wordCode,Bool.false_eq_true,if_false,if_true] at he
      · have hh : wordCode p = wordCode q := by omega
        exact congrArg (List.cons false) (ih q hh)
      · omega
      · omega
      · have hh : wordCode p = wordCode q := by omega
        exact congrArg (List.cons true) (ih q hh)

/-- Countability in its literal injection-into-the-naturals formulation. -/
theorem countable_class : ∃ code : {h : Hypothesis String // H h} → Nat,
    ∀ a b, code a = code b → a = b := by
  classical
  let code : {h : Hypothesis String // H h} → Nat :=
    fun a => wordCode (Classical.choose a.property)
  refine ⟨code, ?_⟩
  intro a b he
  have hw := wordCode_injective _ _ he
  apply Subtype.eq
  calc
    a.val = path (Classical.choose a.property) := Classical.choose_spec a.property
    _ = path (Classical.choose b.property) := congrArg path hw
    _ = b.val := (Classical.choose_spec b.property).symm

/-- The complete lower bound also applies to each history-based generator. -/
theorem every_generator_linear (T : Nat) (G : Generator String) :
    ∃ xs h, xs.length = T ∧ H h ∧ Legal (G.play xs) ∧
      Realizes h (G.play xs) ∧ mistakes h (G.play xs) = T ∧
      regret h (G.play xs) = (T : Int) := by
  obtain ⟨τ,h,ho,hl,ht,hh,hr,hm,hreg⟩ := every_strategy_linear T (G.strategy T [])
  have hc := G.strategy_consistent T [] rfl τ ho
  refine ⟨demonstrations τ,h,?_,hh,?_,?_,?_,?_⟩
  · simpa [demonstrations] using ht
  all_goals rw [hc]; assumption



/-- The numerical dimensions attain the maximal possible value. -/
theorem dimensions_eq_horizon (T : Nat) : MF H T = T ∧ SMF H T = T := by
  have hne : ∃ h, H h := ⟨path [],[],rfl⟩
  have hm := (mf_spec H uus hne T).2 T (mf_forces_horizon T)
  have hs := (smf_spec H uus hne T).2 T (smf_forces_horizon T)
  have hmu := mf_le_horizon H T
  have hsu := smf_le_horizon H T
  omega

end PredictionToGeneration.VCCounterexample
