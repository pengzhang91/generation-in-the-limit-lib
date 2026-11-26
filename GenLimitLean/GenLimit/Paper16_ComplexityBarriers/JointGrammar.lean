import GenLimit.Paper16_ComplexityBarriers.StackGrammar

/-! # Two grammars check the same deterministic computation

A label records the two top stack symbols and a freely chosen bit. Each
grammar checks its own top and performs its own half of the joint rewrite.
The two private infinite branches have different initial terminals. -/
namespace GenLimit.ComplexityBarriers.CFG
open List
open scoped Classical
noncomputable section

abbrev Joint (A B : Type) := A → B → Option (List A × List B)
abbrev Event (A B : Type) := (A × B) × Bool

inductive Run (J : Joint A B) : List A → List B → List (A × B) → Prop
  | done : Run J [] [] []
  | step {x y l r u v tr} : J x y = some (u,v) →
      Run J (u++l) (v++r) tr → Run J (x::l) (y::r) ((x,y)::tr)

def leftStep (J : Joint A B) (x : A) (e : Event A B) : Option (List A) :=
  if x=e.1.1 then (J e.1.1 e.1.2).map Prod.fst else none

def rightStep (J : Joint A B) (y : B) (e : Event A B) : Option (List B) :=
  if y=e.1.2 then (J e.1.1 e.1.2).map Prod.snd else none

private theorem stack_iff (J : Joint A B) (x : A) (l : List A) (e : Event A B) (w : List (Event A B)) :
    StackReads (leftStep J) (x::l) (e::w) ↔ ∃ u, leftStep J x e=some u ∧ StackReads (leftStep J) (u++l) w := by
  constructor
  · intro h; cases h with | step hh hs => exact ⟨_,hh,hs⟩
  · rintro ⟨u,hu,hs⟩; exact .step hu hs

private theorem runs_iff {J : Joint A B} {l r tr} (h : Run J l r tr) (es : List (Event A B)) :
    StackReads (leftStep J) l es ∧ StackReads (rightStep J) r es ↔ es.map Prod.fst = tr := by
  induction h generalizing es with
  | done =>
    constructor
    · rintro ⟨hl,_⟩; cases hl; rfl
    · intro he; obtain rfl := List.map_eq_nil_iff.mp he; exact ⟨.empty,.empty⟩
  | @step x y l r u v tr hj hr ih =>
    cases es with
    | nil =>
      constructor
      · rintro ⟨hl,_⟩; cases hl
      · rintro ⟨⟩
    | cons e es =>
      constructor
      · rintro ⟨hl,hr⟩
        obtain ⟨u',hu,hl⟩ := (stack_iff ..).mp hl
        cases hr with
        | @step _ _ _ v' _ hv hr =>
          obtain ⟨⟨i,j⟩,b⟩ := e
          have hxy : x=i ∧ y=j := by
            constructor
            · by_contra hh; simp [leftStep,hh] at hu
            · by_contra hh; simp [rightStep,hh] at hv
          obtain ⟨rfl,rfl⟩ := hxy
          simp [leftStep,hj] at hu
          simp [rightStep,hj] at hv
          subst u'; subst v'
          exact congrArg ((x,y) :: ·) ((ih es).mp ⟨hl,hr⟩)
      · intro hh
        obtain ⟨he,ht⟩ := List.cons.inj hh
        obtain ⟨p,b⟩ := e
        change p = (x,y) at he
        subst p
        obtain ⟨hl,hr⟩ := (ih es).mpr ht
        exact ⟨.step (by simp [leftStep,hj]) hl,.step (by simp [rightStep,hj]) hr⟩

variable [Fintype A] [Fintype B]

private theorem inter_iff {J : Joint A B} {l r tr} (h : Run J l r tr) (w : List ℕ) :
    w ∈ language (padded 0 (leftStep J) l) ∩ language (padded 1 (rightStep J) r) ↔
    ∃ es : List (Event A B), es.map Prod.fst=tr ∧ w=2::es.map label := by
  change (_ ∧ _) ↔ _
  rw [padded_iff,padded_iff]
  constructor
  · rintro ⟨(⟨a,ha,rfl⟩|⟨i,rfl⟩),(⟨b,hb,he⟩|⟨j,he⟩)⟩
    · have hi : Function.Injective (label (E := Event A B)) :=
        fun _ _ hh ↦ number_injective (Nat.add_right_cancel hh)
      obtain rfl := List.map_injective_iff.mpr hi (List.cons.inj he).2
      exact ⟨a,(runs_iff h a).mp ⟨ha,hb⟩,rfl⟩
    all_goals simp at he
  · rintro ⟨es,hh,rfl⟩
    obtain ⟨hl,hr⟩ := (runs_iff h es).mpr hh
    exact ⟨.inl ⟨es,hl,rfl⟩,.inl ⟨es,hr,rfl⟩⟩

theorem sample_obstruction {J : Joint A B} {l r tr} (h : Run J l r tr) :
    ∀ m ≤ tr.length, ¬ MGeneratable {language (padded 0 (leftStep J) l),language (padded 1 (rightStep J) r)} m := by
  let F := language (padded 0 (leftStep J) l) ∩ language (padded 1 (rightStep J) r)
  have hf : F.Finite := by
    apply (((shortWords (Event A B) (tr.length+1)).finite_toSet).image (fun es ↦ 2::es.map label)).subset
    intro w hw
    obtain ⟨es,he,rfl⟩ := (inter_iff h w).mp hw
    have hl : es.length = tr.length := by simpa using congrArg List.length he
    exact ⟨es,(mem_shortWords ..).mpr (by omega),rfl⟩
  let events := fun b : Fin tr.length → Bool ↦ List.ofFn (fun i ↦ (tr.get i,b i))
  let f := fun b ↦ 2::(events b).map label
  have hi : Function.Injective f := by
    intro b c hh
    have hil : Function.Injective (label (E := Event A B)) :=
      fun _ _ h ↦ number_injective (Nat.add_right_cancel h)
    have he := List.map_injective_iff.mpr hil (List.cons.inj hh).2
    have hs := congrArg (List.map Prod.snd) he
    exact List.ofFn_injective (by simpa [events,List.map_ofFn,Function.comp_def] using hs)
  have hsub : Set.range f ⊆ F := by
    rintro _ ⟨b,rfl⟩
    exact (inter_iff h _).mpr ⟨events b,by simp [events,List.map_ofFn,Function.comp_def],rfl⟩
  have hc := Set.ncard_le_ncard hsub hf
  rw [Set.ncard_range_of_injective hi,Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hc
  intro m hm
  exact pair_obstruction hf ((hm.trans (Nat.le_of_lt Nat.lt_two_pow_self)).trans hc)

end
end GenLimit.ComplexityBarriers.CFG
