import GenLimit.Paper23_BanachDensityTopologyAndGeometry.Topology

/-!
# Finite Cantor--Bendixson ranks of convergent language sequences

This file formalizes Claim 4.11 of Kleinberg--Wei,
*Validity, Sparse Holes, and Breadth in Language Generation: Banach Density,
Topology, and Geometry* (arXiv:2604.02385v2).

The paper's claim is finite even though Definition 3.7 is stated
transfinitely: if a proper sequence converges to a language of finite
Cantor--Bendixson rank `r`, then the sequence eventually consists of
languages of rank strictly below `r`.  We work directly with the finite
derivative hierarchy already used by the positive finite-rank theorem.

`BasisConverges` is the exact sequential convergence condition for the
containment-refined finite-evidence basis.  The final theorem assumes a
finite global rank so that every language in the sequence has a unique
finite point rank.
-/

namespace GenLimit
namespace KleinbergWei
namespace Banach

open TowerTopology

/-- A language has finite Cantor--Bendixson rank `r` when it lies in the
`r`-th derivative but not in the next derivative. -/
def HasFiniteCBRank
    (X : Set Language) (K : Point X) (r : ℕ) : Prop :=
  K ∈ TowerTopology.cbLevel X r

/-- Sequential convergence for the containment-refined finite-evidence
basis: every finite subset of the terminal language is eventually contained,
and every sufficiently late language is a sublanguage of the terminal.
-/
def BasisConverges
    {X : Set Language} (sequence : ℕ → Point X) (terminal : Point X) : Prop :=
  ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ terminal.1 →
    ∃ N, ∀ n, N ≤ n →
      sequence n ∈ basicNeighborhood X terminal F

/-- The convergence core extracted from a perfect tower satisfies the exact
basis convergence predicate used in Claim 4.11. -/
theorem basisConverges_of_convergentProperTower
    {X : Set Language} {sequence : ℕ → Point X} {terminal : Point X}
    (h : ConvergentProperTower X sequence terminal) :
    BasisConverges sequence terminal := by
  intro F hF
  obtain ⟨N, hN⟩ := finite_eventually_contained h F hF
  refine ⟨N, ?_⟩
  intro n hn
  exact ⟨hN n hn, (h.proper n).le⟩

/-- Finite point ranks are unique. -/
theorem hasFiniteCBRank_unique
    {X : Set Language} {K : Point X} {r s : ℕ}
    (hr : HasFiniteCBRank X K r)
    (hs : HasFiniteCBRank X K s) :
    r = s := by
  rcases lt_trichotomy r s with hrs | hrs | hrs
  · have hdisjoint :
        Disjoint (TowerTopology.cbLevel X r)
          (TowerTopology.cbLevel X s) :=
      TowerTopology.cbLevel_disjoint_of_lt hrs
    exact False.elim (Set.disjoint_left.1 hdisjoint hr hs)
  · exact hrs
  · have hdisjoint :
        Disjoint (TowerTopology.cbLevel X s)
          (TowerTopology.cbLevel X r) :=
      TowerTopology.cbLevel_disjoint_of_lt hrs
    exact False.elim (Set.disjoint_left.1 hdisjoint hs hr)

/-- If the `R`-th derivative is empty, every language has a finite point rank
strictly below `R`. -/
theorem exists_hasFiniteCBRank_of_finiteRankAtMost
    {X : Set Language} {K : Point X} {R : ℕ}
    (hR : FiniteRankAtMost X R) :
    ∃ r, r < R ∧ HasFiniteCBRank X K r := by
  classical
  have hexit :
      ∃ n, K ∉ TowerTopology.cbDerivative X n := by
    refine ⟨R, ?_⟩
    rw [hR]
    simp
  let firstExit : ℕ := Nat.find hexit
  have hfirstExit :
      K ∉ TowerTopology.cbDerivative X firstExit :=
    Nat.find_spec hexit
  have hfirstExit_pos : 0 < firstExit := by
    by_contra h
    have hzero : firstExit = 0 := Nat.eq_zero_of_not_pos h
    apply hfirstExit
    rw [hzero, TowerTopology.cbDerivative_zero]
    exact Set.mem_univ K
  let r := firstExit - 1
  have hr_succ : r + 1 = firstExit := by
    simp only [r]
    omega
  have hr_mem :
      K ∈ TowerTopology.cbDerivative X r := by
    by_contra hr
    have hminimal : firstExit ≤ r :=
      Nat.find_min' hexit hr
    omega
  have hfirst_le_R : firstExit ≤ R :=
    Nat.find_min' hexit (by
      rw [hR]
      simp)
  refine ⟨r, ?_, ?_⟩
  · omega
  · exact ⟨hr_mem, by simpa [hr_succ] using hfirstExit⟩

/-- Once a language has left derivative `r`, any finite point rank it has is
strictly below `r`. -/
theorem hasFiniteCBRank_lt_of_not_mem_derivative
    {X : Set Language} {K : Point X} {q r : ℕ}
    (hq : HasFiniteCBRank X K q)
    (hnot : K ∉ TowerTopology.cbDerivative X r) :
    q < r := by
  by_contra hqr
  have hrq : r ≤ q := Nat.le_of_not_gt hqr
  have hsub :
      TowerTopology.cbDerivative X q ⊆
        TowerTopology.cbDerivative X r :=
    TowerTopology.cbDerivative_antitone X hrq
  exact hnot (hsub hq.1)

/-- Core of Claim 4.11: a proper sequence converging to a rank-`r` language
eventually leaves the `r`-th derivative.

This is precisely the source proof.  If arbitrarily late sequence elements
remained in the `r`-th derivative, basis convergence would make the terminal
language a relative limit point of that derivative, placing it in derivative
`r+1` and contradicting its rank.
-/
theorem claim_4_11_derivative_exit
    {X : Set Language} {sequence : ℕ → Point X}
    {terminal : Point X} {r : ℕ}
    (hterminal : HasFiniteCBRank X terminal r)
    (hconverges : BasisConverges sequence terminal)
    (hproper : ∀ n, sequence n ≠ terminal) :
    ∃ N, ∀ n, N ≤ n →
      sequence n ∉ TowerTopology.cbDerivative X r := by
  classical
  by_contra hnotEventually
  have hlate :
      ∀ N, ∃ n, N ≤ n ∧
        sequence n ∈ TowerTopology.cbDerivative X r := by
    intro N
    by_contra hnone
    apply hnotEventually
    refine ⟨N, ?_⟩
    intro n hn hnDerivative
    exact hnone ⟨n, hn, hnDerivative⟩
  apply hterminal.2
  rw [TowerTopology.cbDerivative_succ]
  refine ⟨hterminal.1, ?_⟩
  intro F hF
  obtain ⟨N, hN⟩ := hconverges F hF
  obtain ⟨n, hnN, hnDerivative⟩ := hlate N
  exact ⟨sequence n, hnDerivative, hproper n, hN n hnN⟩

/-- Claim 4.11 in the paper's rank language.  Under a finite global
Cantor--Bendixson bound, every sufficiently late member of a proper
convergent sequence has a (unique) rank strictly smaller than that of the
terminal language.
-/
theorem claim_4_11
    {X : Set Language} {sequence : ℕ → Point X}
    {terminal : Point X} {R r : ℕ}
    (hglobal : FiniteRankAtMost X R)
    (hterminal : HasFiniteCBRank X terminal r)
    (hconverges : BasisConverges sequence terminal)
    (hproper : ∀ n, sequence n ≠ terminal) :
    ∃ N, ∀ n, N ≤ n →
      ∃ q, q < r ∧ HasFiniteCBRank X (sequence n) q := by
  obtain ⟨N, hN⟩ :=
    claim_4_11_derivative_exit hterminal hconverges hproper
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨q, _hqR, hq⟩ :=
    exists_hasFiniteCBRank_of_finiteRankAtMost
      (K := sequence n) hglobal
  exact
    ⟨q, hasFiniteCBRank_lt_of_not_mem_derivative hq (hN n hn), hq⟩

/-- Perfect-tower convergence is the main source-facing special case of
Claim 4.11. -/
theorem claim_4_11_of_convergentProperTower
    {X : Set Language} {sequence : ℕ → Point X}
    {terminal : Point X} {R r : ℕ}
    (hglobal : FiniteRankAtMost X R)
    (hterminal : HasFiniteCBRank X terminal r)
    (htower : ConvergentProperTower X sequence terminal) :
    ∃ N, ∀ n, N ≤ n →
      ∃ q, q < r ∧ HasFiniteCBRank X (sequence n) q :=
  claim_4_11 hglobal hterminal
    (basisConverges_of_convergentProperTower htower)
    (fun n hEq => (htower.proper n).ne (congrArg Subtype.val hEq))

end Banach
end KleinbergWei
end GenLimit
