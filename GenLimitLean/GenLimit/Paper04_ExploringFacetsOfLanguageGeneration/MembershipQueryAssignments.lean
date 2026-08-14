import GenLimit.Paper04_ExploringFacetsOfLanguageGeneration.MembershipQueryShadow

/-!
# Finite assignments for the membership-query diagonal

Small local utilities for extending finite partial two-language oracles.
They remain paper-owned: Core does not need this operational vocabulary.
-/

namespace GenLimit.CharikarPabbaraju

/-- `later` preserves every membership decision made by `earlier`. -/
def AssignmentExtends
    (earlier later : PartialTwoLanguageAssignment) : Prop :=
  ∀ x bits, earlier x = some bits → later x = some bits

@[refl] theorem AssignmentExtends.refl
    (assignment : PartialTwoLanguageAssignment) :
    AssignmentExtends assignment assignment := by
  intro x bits hbits
  exact hbits

@[trans] theorem AssignmentExtends.trans
    {a b c : PartialTwoLanguageAssignment}
    (hab : AssignmentExtends a b) (hbc : AssignmentExtends b c) :
    AssignmentExtends a c := by
  intro x bits hbits
  exact hbc x bits (hab x bits hbits)

/-- Assign `bits` at `x` only if `x` was previously undecided. -/
def assignIfUnset
    (assignment : PartialTwoLanguageAssignment)
    (x : ℕ) (bits : Bool × Bool) : PartialTwoLanguageAssignment :=
  fun y ↦ if y = x then
    match assignment y with
    | some old => some old
    | none => some bits
  else assignment y

theorem assignmentExtends_assignIfUnset
    (assignment : PartialTwoLanguageAssignment)
    (x : ℕ) (bits : Bool × Bool) :
    AssignmentExtends assignment (assignIfUnset assignment x bits) := by
  intro y old hold
  by_cases hy : y = x
  · subst y
    simp [assignIfUnset, hold]
  · simp [assignIfUnset, hy, hold]

/-- Insert a fresh common positive example into both languages. -/
def assignCommon
    (assignment : PartialTwoLanguageAssignment) (x : ℕ) :
    PartialTwoLanguageAssignment :=
  assignIfUnset assignment x (true, true)

/-- A one-sided membership decision, used for a newly seen output. -/
def sideBits (side : Bool) : Bool × Bool :=
  if side then (false, true) else (true, false)

@[simp] theorem sideBits_not_common (side : Bool) :
    sideBits side ≠ (true, true) := by
  cases side <;> simp [sideBits]

end GenLimit.CharikarPabbaraju
