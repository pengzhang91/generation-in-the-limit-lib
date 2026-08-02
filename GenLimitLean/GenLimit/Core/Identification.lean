import GenLimit.Core.Text

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
