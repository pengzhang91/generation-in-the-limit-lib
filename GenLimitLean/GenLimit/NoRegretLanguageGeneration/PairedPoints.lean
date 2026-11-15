import GenLimit.NoRegretLanguageGeneration.Cofinite
import GenLimit.NoRegretLanguageGeneration.Uniform

namespace PredictionToGeneration.PairedPoints

/-- Base points and infinitely many points for each unordered pair. -/
inductive Point where
  | base (i : Nat)
  | pair (i j k : Nat) (ordered : i < j)
  deriving DecidableEq

def indices : Point → List Nat
  | .base i => [i]
  | .pair i j _ _ => [i,j]

def serial : Point → Nat
  | .base _ => 0
  | .pair _ _ k _ => k

def hypothesis (e : List Nat) : Hypothesis Point :=
  fun x => (indices x).all (fun i => !e.contains i)

def H : HypothesisClass Point := fun h => ∃ e, h = hypothesis e

@[simp] theorem positive_iff (e : List Nat) (x : Point) :
    hypothesis e x = true ↔ ∀ i ∈ indices x, i ∉ e := by simp [hypothesis]

def mentions (xs : List Point) : List Nat := xs.flatMap indices

def KnownPair (xs : List Point) (i j : Nat) : Prop :=
  i < j ∧ i ∈ mentions xs ∧ j ∈ mentions xs

theorem two_points_reveal_pair (x y : Point) (hne : x ≠ y) :
    ∃ i j, KnownPair [x,y] i j := by
  cases x with
  | pair i j k hij => exact ⟨i,j,hij,by simp [mentions,indices],by simp [mentions,indices]⟩
  | base i =>
    cases y with
    | pair a b k hab => exact ⟨a,b,hab,by simp [mentions,indices],by simp [mentions,indices]⟩
    | base j =>
      have hij : i ≠ j := fun he => hne (congrArg Point.base he)
      by_cases hlt : i < j
      · exact ⟨i,j,hlt,by simp [mentions,indices],by simp [mentions,indices]⟩
      · exact ⟨j,i,by omega,by simp [mentions,indices],by simp [mentions,indices]⟩

theorem knownPair_of_history (xs : List Point) (hn : xs.Nodup) (hl : 2 ≤ xs.length) :
    ∃ i j, KnownPair xs i j := by
  cases xs with
  | nil => simp at hl
  | cons x xs =>
    cases xs with
    | nil => simp at hl
    | cons y ys =>
      have hxy : x ≠ y := by
        intro he
        exact (List.nodup_cons.mp hn).1 (by simp [he])
      obtain ⟨i,j,hij,hi,hj⟩ := two_points_reveal_pair x y hxy
      refine ⟨i,j,hij,?_,?_⟩
      · simp [mentions] at hi ⊢
        rcases hi with hi | hi
        · exact Or.inl hi
        · exact Or.inr (Or.inl hi)
      · simp [mentions] at hj ⊢
        rcases hj with hj | hj
        · exact Or.inl hj
        · exact Or.inr (Or.inl hj)

/-- Choose a fresh serial number independently of validity labels. -/
def pairOutput (xs : List Point) (i j : Nat) (hij : i < j) : Point :=
  .pair i j (Cofinite.freshAbove (xs.map serial)) hij

theorem pairOutput_fresh (xs : List Point) (i j : Nat) (hij : i < j) :
    pairOutput xs i j hij ∉ xs := by
  intro hm
  have hh : serial (pairOutput xs i j hij) ∈ xs.map serial := List.mem_map.mpr ⟨pairOutput xs i j hij,hm,rfl⟩
  exact Cofinite.freshAbove_not_mem (xs.map serial) hh

noncomputable def generator : Generator Point := by
  classical
  exact {
    output := fun xs => if hp : ∃ i j, KnownPair xs i j then
      pairOutput xs (Classical.choose hp) (Classical.choose (Classical.choose_spec hp))
        (Classical.choose_spec (Classical.choose_spec hp)).1
      else .base (Cofinite.freshAbove (mentions xs))
    fresh := by
      intro xs
      split
      · exact pairOutput_fresh _ _ _ _
      · intro hm
        have hi : Cofinite.freshAbove (mentions xs) ∈ mentions xs := by
          apply List.mem_flatMap.mpr
          exact ⟨_,hm,by simp [indices]⟩
        exact Cofinite.freshAbove_not_mem (mentions xs) hi }

theorem generator_positive (e : List Nat) (xs : List Point)
    (hn : xs.Nodup) (hl : 2 ≤ xs.length)
    (hp : ∀ x ∈ xs, hypothesis e x = true) : hypothesis e (generator.output xs) = true := by
  have hk := knownPair_of_history xs hn hl
  have hi : ∀ i ∈ mentions xs, i ∉ e := by
    intro i hm
    obtain ⟨x,hx,hi⟩ := List.mem_flatMap.mp hm
    exact (positive_iff e x).mp (hp x hx) i hi
  classical
  simp only [generator,dif_pos hk]
  apply (positive_iff e _).mpr
  intro a ha
  simp only [pairOutput,indices,List.mem_cons,List.not_mem_nil,or_false] at ha
  have hp' := Classical.choose_spec (Classical.choose_spec hk)
  rcases ha with rfl | rfl
  · exact hi _ hp'.2.1
  · exact hi _ hp'.2.2

theorem realizes_play_positive (e : List Nat) (xs : List Point)
    (hr : Realizes (hypothesis e) (generator.play xs)) :
    ∀ y ∈ xs, hypothesis e y = true := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro y hy
    obtain ⟨hx,ht⟩ := hr
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hx
    · exact ih ht y hy
/-- The single anytime generator makes at most two mistakes on every realizable play. -/
theorem realizable_two_mistakes (e : List Nat) (xs : List Point) (hn : xs.Nodup)
    (hr : Realizes (hypothesis e) (generator.play xs)) :
    mistakes (hypothesis e) (generator.play xs) ≤ 2 := by
  induction xs with
  | nil => simp [Generator.play,mistakes]
  | cons x xs ih =>
    obtain ⟨_,hn'⟩ := List.nodup_cons.mp hn
    obtain ⟨_,hr'⟩ := hr
    by_cases hl : 2 ≤ xs.length
    · have hp := realizes_play_positive e xs hr'
      have ho := generator_positive e xs hn' hl hp
      simpa [Generator.play,mistakes,loss,ho] using ih hn' hr'
    · have hb := mistakes_le_length (hypothesis e) (generator.play (x::xs))
      have len : ∀ ys : List Point, (generator.play ys).length = ys.length := by
        intro ys
        induction ys with
        | nil => rfl
        | cons _ ys ih => simp [Generator.play,ih]
      rw [len] at hb
      simp only [List.length_cons] at hb
      omega






theorem uus : UUS H := by
  intro h ⟨e,he⟩ seen
  subst h
  let i := Cofinite.freshAbove (e ++ mentions seen)
  have hi := Cofinite.freshAbove_not_mem (e ++ mentions seen)
  change i ∉ e ++ mentions seen at hi
  simp only [List.mem_append,not_or] at hi
  refine ⟨.base i,?_,?_⟩
  · intro hm
    exact hi.2 (List.mem_flatMap.mpr ⟨.base i,hm,by simp [indices]⟩)
  · simpa [positive_iff,indices] using hi.1

theorem mask_determines_hypothesis (e f : List Nat) (he : Cofinite.mask e = Cofinite.mask f) :
    hypothesis e = hypothesis f := by
  have hh := Cofinite.mask_determines_hypothesis e f he
  funext x
  cases x with
  | base i =>
    have hi := congrFun hh i
    simpa [hypothesis,indices,Cofinite.hypothesis] using hi
  | pair i j k hij =>
    have hi := congrFun hh i
    have hj := congrFun hh j
    change (!e.contains i) = (!f.contains i) at hi
    change (!e.contains j) = (!f.contains j) at hj
    change ((!e.contains i) && ((!e.contains j) && true)) =
      ((!f.contains i) && ((!f.contains j) && true))
    rw [hi,hj]

theorem countable_class : ∃ code : {h : Hypothesis Point // H h} → Nat,
    ∀ a b, code a = code b → a = b := by
  classical
  let code : {h : Hypothesis Point // H h} → Nat :=
    fun a => VCCounterexample.wordCode (Cofinite.mask (Classical.choose a.property))
  refine ⟨code, ?_⟩
  intro a b he
  have hw := VCCounterexample.wordCode_injective _ _ he
  apply Subtype.eq
  calc
    a.val = hypothesis (Classical.choose a.property) := Classical.choose_spec a.property
    _ = hypothesis (Classical.choose b.property) := mask_determines_hypothesis _ _ hw
    _ = b.val := (Classical.choose_spec b.property).symm



theorem uniform_two_mistakes : UniformMistakeBound generator H 2 := by
  intro xs hn h ⟨e,he⟩ hr
  subst h
  exact realizable_two_mistakes e xs hn hr

/-- No well-founded realizable forcing tree can force three mistakes. -/
theorem no_uniform_three_forcing : ¬ WellFoundedForces (RealizableBad H 3) [] := by
  have hne : ∃ h, H h := ⟨hypothesis [],[],rfl⟩
  exact (realizable_uniform_characterization H uus hne 2).mpr ⟨generator,uniform_two_mistakes⟩



theorem mf_le_two (T : Nat) : MF H T ≤ 2 := by
  have hne : ∃ h, H h := ⟨hypothesis [],[],rfl⟩
  have hf := (mf_spec H uus hne T).1
  apply Classical.byContradiction
  intro hb
  have hf3 : MFForces H T 3 := by
    apply forces_mono (n := T) (τ := []) (hf := hf)
    intro τ ⟨h,hh,hr,hm⟩
    exact ⟨h,hh,hr,by omega⟩
  exact no_uniform_three_forcing (finite_forces_wellFounded _ T [] hf3)

end PredictionToGeneration.PairedPoints

