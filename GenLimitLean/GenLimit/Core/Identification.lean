import GenLimit.Core.Text
import Mathlib.Data.List.OfFn

/-!
# Identification in the limit

These definitions isolate the paper-independent logical shape of strong
identification in the limit.  A learner consumes a finite ordered information
history and must eventually stabilize to one fixed name denoting the target.
No computability assumption is imposed on learners or denotation maps.
-/

namespace GenLimit

universe uInfo uName uObject

/-- A learner maps a finite ordered information history to a name. -/
abbrev Learner (Info : Type uInfo) (Name : Type uName) :=
  List Info → Name

/-- Adapt a learner written against a length-indexed finite tuple to the
shared ordered-list history interface. -/
def learnerOfFiniteHistory
    (learner : ∀ t : ℕ, (Fin t → Info) → Name) : Learner Info Name :=
  fun history => learner history.length history.get

@[simp] theorem learnerOfFiniteHistory_ofFn
    (learner : ∀ t : ℕ, (Fin t → Info) → Name)
    {t : ℕ} (xs : Fin t → Info) :
    learnerOfFiniteHistory learner (List.ofFn xs) = learner t xs := by
  change learner (List.ofFn xs).length (List.ofFn xs).get = learner t xs
  have htuple :
      (⟨(List.ofFn xs).length, (List.ofFn xs).get⟩ :
        Σ n, Fin n → Info) = ⟨t, xs⟩ := by
    exact List.equivSigmaTuple.apply_symm_apply ⟨t, xs⟩
  exact congrArg (fun h : Σ n, Fin n → Info => learner h.1 h.2) htuple

theorem learnerOfFiniteHistory_textPrefix
    (learner : ∀ t : ℕ, (Fin t → Info) → Name)
    (stream : ℕ → Info) (t : ℕ) :
    learnerOfFiniteHistory learner (textPrefix stream t) =
      learner t (fun i => stream i) := by
  rw [textPrefix_eq_ofFn]
  exact learnerOfFiniteHistory_ofFn learner _

/-- A sequence of guesses eventually becomes the fixed name `name`. -/
def StabilizesTo {Name : Type uName}
    (guess : ℕ → Name) (name : Name) : Prop :=
  ∃ T, ∀ t, T ≤ t → guess t = name

/-- Strong identification on one information stream: the learner eventually
uses one fixed name whose denotation is the target object. -/
def IdentifiesInLimit
    {Info : Type uInfo} {Name : Type uName} {Object : Type uObject}
    (denote : Name → Object) (learner : Learner Info Name)
    (stream : ℕ → Info) (target : Object) : Prop :=
  ∃ name, denote name = target ∧
    StabilizesTo (fun t => learner (textPrefix stream t)) name

end GenLimit
