import GenLimit.Support.KleinbergWei.TowerTopology

/-!
# Finite Cantor--Bendixson hierarchy

Shared finite-rank infrastructure for the Kleinberg--Wei density papers.
-/

namespace GenLimit.KleinbergWei.TowerTopology

/-- A point of Y that is non-isolated relative to Y. -/
def RelativeLimitPoint
    {X : Set Language} (Y : Set (Point X)) (K : Point X) : Prop :=
  K ∈ Y ∧
    ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ K.1 →
      ∃ L : Point X,
        L ∈ Y ∧ L ≠ K ∧ L ∈ basicNeighborhood X K F

/-- One decreasing Cantor--Bendixson derivative. -/
def derivative
    {X : Set Language} (Y : Set (Point X)) : Set (Point X) :=
  {K | RelativeLimitPoint Y K}

theorem derivative_subset
    {X : Set Language} (Y : Set (Point X)) :
    derivative Y ⊆ Y := by
  intro K hK
  exact hK.1

theorem derivative_mono
    {X : Set Language} {Y Z : Set (Point X)}
    (hYZ : Y ⊆ Z) :
    derivative Y ⊆ derivative Z := by
  intro K hK
  refine ⟨hYZ hK.1, ?_⟩
  intro F hFK
  obtain ⟨L, hLY, hne, hLF⟩ := hK.2 F hFK
  exact ⟨L, hYZ hLY, hne, hLF⟩

/-- Finite derivative sequence; Paper #23 uses this in Section 3.3,
Definition 3.7. -/
def cbDerivative (X : Set Language) : ℕ → Set (Point X)
  | 0 => Set.univ
  | n + 1 => derivative (cbDerivative X n)

@[simp] theorem cbDerivative_zero (X : Set Language) :
    cbDerivative X 0 = Set.univ :=
  rfl

@[simp] theorem cbDerivative_succ (X : Set Language) (n : ℕ) :
    cbDerivative X (n + 1) = derivative (cbDerivative X n) :=
  rfl

theorem cbDerivative_succ_subset
    (X : Set Language) (n : ℕ) :
    cbDerivative X (n + 1) ⊆ cbDerivative X n := by
  simpa only [cbDerivative_succ] using derivative_subset (cbDerivative X n)

theorem cbDerivative_antitone (X : Set Language) :
    Antitone (cbDerivative X) := by
  apply antitone_nat_of_succ_le
  exact cbDerivative_succ_subset X

/-- Points removed at finite level n. -/
def cbLevel (X : Set Language) (n : ℕ) : Set (Point X) :=
  cbDerivative X n \ cbDerivative X (n + 1)

theorem cbLevel_subset_derivative
    (X : Set Language) (n : ℕ) :
    cbLevel X n ⊆ cbDerivative X n := by
  intro K hK
  exact hK.1

theorem cbLevel_disjoint_of_lt
    {X : Set Language} {i j : ℕ} (hij : i < j) :
    Disjoint (cbLevel X i) (cbLevel X j) := by
  rw [Set.disjoint_left]
  intro K hKi hKj
  have hjSucc : i + 1 ≤ j := by omega
  have hsub : cbDerivative X j ⊆ cbDerivative X (i + 1) :=
    cbDerivative_antitone X hjSucc
  exact hKi.2 (hsub hKj.1)

/-- Empty-perfect-kernel finite-rank predicate. -/
def FiniteRankAtMost (X : Set Language) (r : ℕ) : Prop :=
  cbDerivative X r = ∅

theorem finiteRankAtMost_mono
    {X : Set Language} {r s : ℕ}
    (hrs : r ≤ s) (hr : FiniteRankAtMost X r) :
    FiniteRankAtMost X s := by
  unfold FiniteRankAtMost at hr ⊢
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro K hKs
  have hKr := cbDerivative_antitone X hrs hKs
  rw [hr] at hKr
  exact hKr

end GenLimit.KleinbergWei.TowerTopology
