import GenLimit.Core.Basic
import Mathlib.Topology.Defs.Basic

/-!
# #15 Full-enumeration topology and tell-tales

Section 4.1 topology with basic opens U_F = {L in X | F is a subset of L}.
The file proves the topological core of Theorem 4.9 and Corollary 4.11.
-/

namespace GenLimit.KleinbergWei.PartialEnumeration.FullTopology

abbrev Point (X : Set Language) := {L : Language // L ∈ X}

def basicOpen (X : Set Language) (F : Finset ℕ) : Set (Point X) :=
  {L | (↑F : Set ℕ) ⊆ L.1}

@[simp] theorem mem_basicOpen
    {X : Set Language} {F : Finset ℕ} {L : Point X} :
    L ∈ basicOpen X F ↔ (↑F : Set ℕ) ⊆ L.1 :=
  Iff.rfl

def FullOpen (X : Set Language) (O : Set (Point X)) : Prop :=
  ∀ K, K ∈ O →
    ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ K.1 ∧ basicOpen X F ⊆ O

theorem fullOpen_univ (X : Set Language) : FullOpen X Set.univ := by
  intro K _
  exact ⟨∅, by simp, by simp⟩

theorem fullOpen_inter
    {X : Set Language} {U V : Set (Point X)}
    (hU : FullOpen X U) (hV : FullOpen X V) :
    FullOpen X (U ∩ V) := by
  intro K hK
  obtain ⟨F, hFK, hFU⟩ := hU K hK.1
  obtain ⟨G, hGK, hGV⟩ := hV K hK.2
  refine ⟨F ∪ G, ?_, ?_⟩
  · intro u hu
    simp only [Finset.mem_coe, Finset.mem_union] at hu
    exact hu.elim (fun h => hFK h) (fun h => hGK h)
  · intro L hL
    exact
      ⟨hFU (fun u hu => hL (by simp [hu])),
        hGV (fun u hu => hL (by simp [hu]))⟩

theorem fullOpen_sUnion
    {X : Set Language} {S : Set (Set (Point X))}
    (hS : ∀ O ∈ S, FullOpen X O) :
    FullOpen X (⋃₀ S) := by
  intro K hK
  obtain ⟨O, hOS, hKO⟩ := Set.mem_sUnion.mp hK
  obtain ⟨F, hFK, hFO⟩ := hS O hOS K hKO
  exact ⟨F, hFK, fun L hL => Set.mem_sUnion.mpr ⟨O, hOS, hFO hL⟩⟩

def topology (X : Set Language) : TopologicalSpace (Point X) where
  IsOpen := FullOpen X
  isOpen_univ := fullOpen_univ X
  isOpen_inter := fun _ _ => fullOpen_inter
  isOpen_sUnion := fun _ => fullOpen_sUnion

theorem basicOpen_isOpen
    (X : Set Language) (F : Finset ℕ) :
    FullOpen X (basicOpen X F) := by
  intro K hK
  exact ⟨F, hK, Set.Subset.rfl⟩

/-- Specialization preorder oriented as in the source. -/
def Specializes {X : Set Language} (K L : Point X) : Prop :=
  ∀ O : Set (Point X), FullOpen X O → K ∈ O → L ∈ O

theorem specializes_iff_subset
    {X : Set Language} {K L : Point X} :
    Specializes K L ↔ K.1 ⊆ L.1 := by
  constructor
  · intro h u hu
    let F : Finset ℕ := {u}
    have hK : K ∈ basicOpen X F := by
      intro v hv
      simp only [F, Finset.mem_coe, Finset.mem_singleton] at hv
      subst v
      exact hu
    have hL := h (basicOpen X F) (basicOpen_isOpen X F) hK
    exact hL (by simp [F])
  · intro hKL O hO hKO
    obtain ⟨F, hFK, hFO⟩ := hO K hKO
    exact hFO (hFK.trans hKL)

/-- Finite Angluin tell-tale for a point of a set-valued class. This is the
intended strict-sublanguage reading of the malformed self-referential display
in arXiv v1, Theorem 4.8. -/
def IsTellTale
    {X : Set Language} (K : Point X) (F : Finset ℕ) : Prop :=
  (↑F : Set ℕ) ⊆ K.1 ∧
    ∀ L : Point X,
      (↑F : Set ℕ) ⊆ L.1 → L.1 ⊆ K.1 → L = K

/-- Local-closedness at one point. -/
def TDPoint {X : Set Language} (K : Point X) : Prop :=
  ∃ O : Set (Point X),
    FullOpen X O ∧ K ∈ O ∧
      ∀ L : Point X, L ∈ O → L.1 ⊆ K.1 → L = K

theorem tellTale_iff_tdPoint
    {X : Set Language} {K : Point X} :
    (∃ F : Finset ℕ, IsTellTale K F) ↔ TDPoint K := by
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨basicOpen X F, basicOpen_isOpen X F, hF.1,
      fun L hLF hLK => hF.2 L hLF hLK⟩
  · rintro ⟨O, hO, hKO, hsep⟩
    obtain ⟨F, hFK, hFO⟩ := hO K hKO
    exact ⟨F, hFK, fun L hFL hLK => hsep L (hFO hFL) hLK⟩

def TDSpace (X : Set Language) : Prop :=
  ∀ K : Point X, TDPoint K

/-- The topological/tell-tale core of Theorem 4.9. -/
theorem theorem_4_9_topological_core (X : Set Language) :
    (∀ K : Point X, ∃ F : Finset ℕ, IsTellTale K F) ↔ TDSpace X := by
  constructor
  · intro h K
    exact tellTale_iff_tdPoint.mp (h K)
  · intro h K
    exact tellTale_iff_tdPoint.mpr (h K)

def TOneSpace (X : Set Language) : Prop :=
  ∀ K L : Point X, Specializes K L → K = L

def InclusionAntichain (X : Set Language) : Prop :=
  ∀ K L : Point X, K.1 ⊆ L.1 → K = L

theorem tOneSpace_iff_inclusionAntichain (X : Set Language) :
    TOneSpace X ↔ InclusionAntichain X := by
  constructor
  · intro h K L hKL
    exact h K L (specializes_iff_subset.mpr hKL)
  · intro h K L hspec
    exact h K L (specializes_iff_subset.mp hspec)

/-- Order-theoretic/topological core of Corollary 4.11. -/
theorem corollary_4_11_topological_core (X : Set Language) :
    TOneSpace X ↔
      ∀ K L : Point X, K.1 ⊆ L.1 → K = L :=
  tOneSpace_iff_inclusionAntichain X

end GenLimit.KleinbergWei.PartialEnumeration.FullTopology
