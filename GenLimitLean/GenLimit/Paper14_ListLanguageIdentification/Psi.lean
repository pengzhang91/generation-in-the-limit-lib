import GenLimit.Paper14_ListLanguageIdentification.Definitions

/-!
# The recursive predicate `Ψ`

Equations (4)--(6) of Charikar--Pabbaraju--Tewari,
*A Characterization of List Language Identification in the Limit*,
arXiv:2511.04103v1.

The paper writes `Ψ₀(L_i) = 0` and, recursively, asks for a finite set
`T_i ⊆ L_i` such that every strict sublanguage containing `T_i` has positive
predicate value one level lower.  We represent predicate value one by a
proposition.  Thus the equation `Ψ₀ = 0` becomes `False`.
-/

namespace GenLimit.ListIdentification

/-- The recursive predicate from equations (4) and (5).

At level zero it is false.  At level `k + 1`, it asks for a finite witness
inside `F i` such that every strict sublanguage in the indexed family which
contains the witness satisfies the level-`k` predicate. -/
def Psi (F : GenLimit.Generic.LanguageFamily α) (i : ℕ) : ℕ → Prop
  | 0 => False
  | k + 1 =>
      ∃ T : Finset α,
        (↑T : Set α) ⊆ F i ∧
          ∀ j, (↑T : Set α) ⊆ F j → F j ⊂ F i → Psi F j k

/-- A finite set satisfying the successor clause of `Psi`. -/
def IsPsiWitness
    (F : GenLimit.Generic.LanguageFamily α)
    (i k : ℕ) (T : Finset α) : Prop :=
  (↑T : Set α) ⊆ F i ∧
    ∀ j, (↑T : Set α) ⊆ F j → F j ⊂ F i → Psi F j k

/-- Equation (6): the indexed family satisfies the `k`-Angluin condition
when every indexed language has positive level-`k` predicate value. -/
def KAngluinCondition
    (F : GenLimit.Generic.LanguageFamily α) (k : ℕ) : Prop :=
  ∀ i, Psi F i k

@[simp]
theorem psi_zero
    (F : GenLimit.Generic.LanguageFamily α) (i : ℕ) :
    ¬Psi F i 0 := by
  simp [Psi]

theorem psi_succ_iff
    (F : GenLimit.Generic.LanguageFamily α) (i k : ℕ) :
    Psi F i (k + 1) ↔ ∃ T : Finset α, IsPsiWitness F i k T := by
  rfl

/-! ## Depth one is Angluin's tell-tale condition -/

/-- At depth one, the recursive predicate is exactly existence of an
Angluin tell-tale. -/
theorem psi_one_iff_exists_isTellTale
    (F : GenLimit.Generic.LanguageFamily α) (i : ℕ) :
    Psi F i 1 ↔
      ∃ T : Finset α, GenLimit.Angluin.IsTellTale F i T := by
  constructor
  · rintro ⟨T, hTi, hdescend⟩
    refine ⟨T, hTi, ?_⟩
    intro j hTj hji
    by_contra hnot
    have hstrict : F j ⊂ F i := ⟨hji, hnot⟩
    have : Psi F j 0 := hdescend j hTj hstrict
    exact (psi_zero F j) this
  · rintro ⟨T, hT⟩
    refine ⟨T, hT.1, ?_⟩
    intro j hTj hstrict
    have hij : F i ⊆ F j := hT.2 j hTj hstrict.1
    exact (hstrict.2 hij).elim

/-- Equation (6) at `k = 1` is precisely Angluin's Condition 2. -/
theorem kAngluin_one_iff_conditionTwo
    (F : GenLimit.Generic.LanguageFamily α) :
    KAngluinCondition F 1 ↔ GenLimit.Angluin.ConditionTwo F := by
  constructor
  · intro h i
    exact (psi_one_iff_exists_isTellTale F i).mp (h i)
  · intro h i
    exact (psi_one_iff_exists_isTellTale F i).mpr (h i)

/-! ## Monotonicity in the depth parameter -/

/-- A positive level remains positive after increasing the depth by one.
This is the local monotonicity observation following equation (6). -/
theorem psi_succ_mono
    {F : GenLimit.Generic.LanguageFamily α} {i k : ℕ}
    (h : Psi F i k) :
    Psi F i (k + 1) := by
  induction k generalizing i with
  | zero =>
      exact (psi_zero F i h).elim
  | succ k ih =>
      obtain ⟨T, hTi, hdescend⟩ := h
      refine ⟨T, hTi, ?_⟩
      intro j hTj hji
      exact ih (hdescend j hTj hji)

/-- Monotonicity of `Psi`: once true at depth `k`, it is true at every
larger depth. -/
theorem psi_mono
    {F : GenLimit.Generic.LanguageFamily α} {i k l : ℕ}
    (hkl : k ≤ l) (h : Psi F i k) :
    Psi F i l := by
  induction l, hkl using Nat.le_induction with
  | base =>
      exact h
  | succ l hkl ih =>
      exact psi_succ_mono ih

/-- The `k`-Angluin conditions are monotone in `k`. -/
theorem kAngluin_mono
    {F : GenLimit.Generic.LanguageFamily α} {k l : ℕ}
    (hkl : k ≤ l) (h : KAngluinCondition F k) :
    KAngluinCondition F l := by
  intro i
  exact psi_mono hkl (h i)

/-! ## A canonical semantic witness -/

/-- Choose one finite witness for a positive successor-level predicate.
This is the noncomputable semantic counterpart of the witness chosen by
Algorithm 1. -/
noncomputable def psiTellTale
    (F : GenLimit.Generic.LanguageFamily α) (i k : ℕ) : Finset α :=
  by
    classical
    exact
      if h : Psi F i (k + 1) then
        Classical.choose ((psi_succ_iff F i k).mp h)
      else
        ∅

theorem psiTellTale_spec
    {F : GenLimit.Generic.LanguageFamily α} {i k : ℕ}
    (h : Psi F i (k + 1)) :
    IsPsiWitness F i k (psiTellTale F i k) := by
  classical
  rw [psiTellTale, dif_pos h]
  exact Classical.choose_spec ((psi_succ_iff F i k).mp h)

end GenLimit.ListIdentification
